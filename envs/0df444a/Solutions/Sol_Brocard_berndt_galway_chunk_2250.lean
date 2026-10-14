-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2250
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:07:43.460019+00:00
-- url     : https://prove2.me/submissions/a5589a2f-c1a7-4793-b38b-2fb0ab016853

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 404496402 ≤ n < 404676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 404497652 1250 404496402 404496481
    0x606140328020a021609020c07030209041e0303020a03050901050f060f0409050601060903020a0e0903041202030307050703050d020c040902060d020c030d020a05040501030c03181205311d 82
    0x3422910000d85c110001c0b018000034880954005450110000c606002840c0003056507102d150000134040c0c4c07461b40c00710301441140c4030440a102d074010800c144a92280c50000e0103900504a0700780803a040201040302c00300306008141c070a40012030607142c5a951407003000540c22070380700700941003a90b07600d040300882c800740001b5019000c0c580f220919103203944144025007800c1c0c0e0045c10050321820071b009003e50040115800c0b5080001400308141450000a05511440340000c2c8103124803840002001004184440701e40001d40135200340300035040512068801c2d000d0002c1d0301420800105800004940c054500030b1410740869043c118005000012a1f2249081001080c400b0400b00000e60b07142c000c5412005031482c0a004800a415034100411094140280441403815010904a00c0303101070352180e41072103652485140c20b40600515948010110701d10030940d18801080c12681012605001c80880d049000c0c1551211889031701002c00e0310070200d203c1242c850080c4c0c07410303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 404498902 1250 404497652 404497657
    0x1c0509040204170618070e0411030102030403081f030809060d061502060402030d0e0102061902090d0f1a0c031f0509070210060501020708030702010309050c0d0f06060614032802 78
    0x21155903c46001c811900305904d8010004c01c000540e007408400c0c1409483c020a14200310f0306004191031080e215468407501104140f820183c0540c404020041030540c0319861500400d6040100200100e50130360b4000d45003203030f000141640108014168150500d10010311040c8903403000080e84545850000d0350160b1040d181c08016809042880f084d0328043c4240210305a01c0c0c10141c02030102200040c0d21680c00900040c4c000440003040d0b101039003250116000b11100070140503140c040c514000300740c0d400303410064800400b034076500e1041200080c251070085200180040c210754591010113014541e076698081c00c070803120341c00100c90b01c641c3d00310381c012080d580207400514802100c05089800301c0d4401c50465100c1070080040101c04002c4858590302883c0c0030a500c419070038600c0c640000c9a884c00c1d002203400350808280408590ba895000b485041c050010703540d1420304544942d00511098030006080001c01d800da420001509000d0380c80040d840086903908a1803402ca8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 404500152 1250 404498902 404498909
    0x8070501081e0f150a030f0f0201021f1a0d0807140c060a0f0807021203070c050c0d06021902061b030901140c0405010e01110604110d0c06030b01201c0509040204 71
    0x641034403041c00304036a18a089130040300001da40302c00200c2c0c40c584480303455040ca00030242250060650b48405d40e403090102814912000390b804002e8120541518001c0105025800050042c1c1c2060380300e80c0381c00030303a8407110f5030405d0b001070030541f154071511000c0c1d10b40c00a440d220721440c450001a030710340d00301a00c110740b280e44602000c440d030180003501241d0000d08003003c540200c6010207001c400e05082d030f0f41042261408540040300c61416910341071001098a13405107008141d4400c11030320341c0003002120002c1554000301010300000b40d03030300d40f819107603040245100b100080c1c036101004080c5512038001800421004040c12410b084490700741d90460103800001000c0c4003950300710420040f0100d080c80c0040310801016031507511000c000e04000d1120001001c3d00c8641d6a9a0f1014018244c010760200e900355a21032002d0014111480741d80d012034040303100d40602e280c241a10b9004220050080c0c00c40892800e5104110f841c85486001841014462407085449500c00341029 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 404501402 1250 404500152 404500171
    0x3032206140a05010506070201020a030f110712060606022a0d0206070309030b060d0803150a051207060f0f021038030708010506010c06090c1a030f010f08070501081e 73
    0x5007022a0402c00f5034105070059802607004001250050340d0004503049515003500d04480d1503243d0707200803143c40d440d0b520071f11150702c2035080c0030501c0d03e1210340f038180c004d1168204100c080d40ea140160b0321562030100703903031070002c40c410b0b150725a860b01c0c4180f0007000d0006046103900b58059001880c40c0d0000d0105800041442400348104034030041172a4110b07134111103102d00e004442e5a030b0b41b520310000b84044480410151907950907103c6106040180000a042e05040e501c0c000802c3c2c3c1d1200701c4c0c400c1f84c0002d4401a00b5000d5275004000d200740c408041c1e40070f000c42070701c02044403001e0405910800c164584001d514402e01003610340741c09035240074041252850b2010f408146c540101c94002144030b074035103414450b441ea00300c003940c0c1d6450350003070700403410100905201000c0c0c90a0350126403251400c0d600784225048007001544101c103c000003842503600e87c02c2c1c2d0b600311200c3c0d024011301c9a100d08402d00096005a418503884880c0390a20540b12072200c03040e800801050b2844101c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 404502652 1250 404501402 404501441
    0x610090b0307141612020f03041e03020d0308041a0705031612020c010f061d040f0501090b072c130b04060914040312020304020a18150e090c030102040803032206 71
    0x8028170254000600205032004201c409a080d031900d403030f4420343c400c404024944051851140b1481c0d00554001c5030010000890b4080f642000b510581c8112400c44100c14900789051001c000c071505180240d0140d83c8050850790340c0180c0a60511080d03845009000740d000704004104054001420740c00e8a150000c036070815140c050105841c103580200160800c140080034141800f210f0b0241d1198100540390315569090030481e0051140c580060300040307003c41000121034010b900b00900e6181071a0181d20070100c0c0300b8640c0c01140300c2003540d6028042d0745820340011a00d4024010880c0c0040c000100690381d40314030011689505913045551915104002c01c1c950048810a203030b0114170000c0d491441d040c0d000075412030190040c2c418182c400c043e070031861400c540c0141c1c0e4a90140d0007407039220b600c0b12020a51170b9403c440942d4217100e1605044140e05040c0203640440c0c0f050070013182580c507000d61040008091a01007030302c4042c12100307100411070b20300030003290584000d032102 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 404503902 1250 404502652 404502697
    0x50c0a1103091c02060d0203011202150a020d081f0306090b090a0c05040f110714010e0f07050d031106010b0405030105070309050a0308061f030506090610090b030714 73
    0x618406514060030180c1c1c0090054088a484807400f8141c000038480c901410a50a8400109140500784001507190701c003000200700810f00994562155008230380200c5200c0c1200b00c104141c1c41221050401600721044a40762140641c18440d0001a60310002000c0d1000700c0c00c0000c1c11140758419221681c80d01d2180080c03028144106411052480142c000b007007094440c11a44080c600c80c55020f240d43c2c52034003e51415546c4a400f9811382c02011954039406410880000d4000a0007000c1d075501e80900c40c651a03200007035a4003d00384000240c1111807400041103611503840800350306108000130501440d49050000f03501904582c1d0106d5101c030b04280515003100e01c020010010305141c2080d10b80401c9001a504040c00da16140a050690740e03000441d111118800380c0d000c24480c0c0c0b8050140700c0c0d40507000280720b5034040c2d5800c00d0351313542c441c10016440c81001c00000401c01d600c0c0244160540200115404407450a04609000c100d1030050120792009038025816854640e006 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 404505152 1250 404503902 404503907
    0x3070f06060801090201230d0203041a01080706090909110402030f011401050a05030103061a03011a090a0b06040605030c090a12050c01110715020109050703050115090c08040209060d06050c0a 84
    0x405800b44800800282c1400d0740040c1c0706985a0b0540c0105c25421400010903514403401ca50300015400000d41d00e07070500746480140a44031245007a80407a0740b0001180101c00000c1ca9030840b40540d41d0210f515103040342d00c00081a488400381c03041c01c030301070b0451207079215400258055540000c08855661404131000c08101c01c5c01c00060400908003c20304510303511030203403819a6044480041c1a40c00c4280d4001141d000e800c0d140d03019400c00e0031041100c1a01413110107015000d42d0100c80a51700c1103142d008460380c800c4695801074040c4014840d040c480d5004e1035018101408051a00003080001003072040e1503440101068450110794007005414414002040303000e0074640c0c07500390105034694890805000b2505560308000180034158403d400900f03100390404185c070b6440d6140c0c1030aa010700a401101c03042c0344000c1600003020301c950b210f8249a181c45542d40080c640304c075030800003011009054240d001580c10b0200d004102c440c425107001da550040c40701c1d542c18078207002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 404506402 1250 404505152 404505161
    0x4031103060a060305030906090d121e08060307031214070507030c09021801080603102f04210f05030c1c0314130c03331a04051803070f06 61
    0xb1940b8982006001c10025000100f640e4522004580d060786549402c000300c2c00c0c00090100242501e840101c4000d81c0580250003603400c403c1c110b4600724152240041642c403440700361103040e01075003d0f213010000301d2503541e150241242c05140c1185c2c0342c0701004094a058006600c2524a46c20a1100700100680742d8400300040160510650910369841c00c0d505c000341c0d071004043d060040d12000a15256828480b8500f0070702603075070400c140d0540c1d804209104070351450891086001c002c3c042500c004800559084441028010f1584904004107490221200c602110700f03229000b030410000b5424005842601e2a6800612029203903403c0c8014130002c40014030189442c20b0807503a016031031601d080d90301c0820410000c83e0094140f41c0030b02031003007076440908800b40c1e00c8201140c2c0101c208811408003444582032014414111303c03641101c520300c81060700c800b04205a60110305103a04a01c0c3d000461103101c92300c43c003105c440581980e200301c2e03041740e02c40321030003140b02001064440c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 404507652 1250 404506402 404506411
    0xa0606080f0402060d0e0c100801050a0602070510231b0d0914010818070e0117010c080a0e10020d060501030e060705070803040507050a0308071a0c2d0403110306 71
    0x30240c100e04060f000300f503892040c0c0401101d0315444004c410410a002c1118800c00507010708080d0400351103550040200f00280181032040b9024000011814800130f050740664000502d0407505040c0000b050ba1184480421284a24188241184100c2020300604100100320b5265072140e03034083c42d440c0c01e107c0581490410302c00050002c0c400381c1c0420398003207402c0710b0a007080303a040c0e154030095510000303906074000400e114589000c58a01d0303964000604882940d091070628110447c1701078280c48116281800049100c00041c06248554125140c1102076405540c0c51150102c0b4140036a4040480c0109460719440c0400c00c65a240c03140b80e6901042e40081c0403242486540180b82d0300c00c2e4040034081d00b0002c00460207010301402404000d020040114450b65030302e02d0205903c1e08025420b4030b0312850400c24a80c03030401e401140b03114680c103524507132810031500000c0d000c0f0740e0440850488000c008006000b2005410b00800240d8028540b8000904a04042500e070000051 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 404508902 1250 404507652 404507671
    0x1203070c0c0303050307022b05070503040e09160806040f06050408070f230705030706030b0109080f0109140f060712020c06090a17160305030417031305061005030a060e0111030a060608 81
    0x90075010348d0417008040c20303102200c515145a0f55103150a00790310314091a007040a03448410400c0c480c00c101d0000f44840400150142003003000d83d030b4201d6603200e0100322005440ca0202c210464000b80680d8043d50784184110022400c201254445845810006104403030b10300c00107a4240004284280380710010000d5401000340600b00408a9180c101310710403042856260740c12203110781e0040e03000c2d6010b81411021141c3c12220215254040d0001150942e00c0410301103002c05a110301103011040c5e800c0d078078000e10b103d4076602d10888803031149210041100e80e00788200380001509000307941c000e0071004002e02c1c2014203070800c203081210342d00c03040928900400c50b48140054451031008081e0305418000d80b60382c0e80341099100491482c0c5812102d8000008010071441c12031013035164107000350b003110165a10021400e501c4d807071a00410394140c0c008440c0b04c0020740e250f007141c88021204000898840c07042c41064406400c2238030f4145000341c40348424030401f0f9229619603030112081 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 404510152 1250 404508902 404508943
    0x190807030506060c0a140a14030a030c03020f0702010809120a080f060405010e0f0712020f030f060613090e010e0d020706020d02070e13020a0b030106030218040b031203070c0c030305030702 83
    0x20306950743c5d5182c04c40c0300030700c0600c0409411200c2001800010500c1b074000c507000c200d560201e2400c603200d600861180d008030340381c0403640c4001840317407007540c03980c64410810f20b1814070ba44e0015030b079420004181c8031443c0300b410a070722814802c2c01c0107051180380c240c5900300f070381c04d09403009510600c009250a001e103103040010000d071207044808540000b01203111008545030413408132100281d200503d0015400042d00060103109000158820042042c2801c407540300e0b0720412601e4810012080c400005860b01486049140c0c1d1101e000c011160300000761000c0c00c401024208004004100090781050b2001c114064041c01f070503036000700520103000780ea81480080d407107002d4007411050504008807144001c41d00c9845100c005480c403007085986a60b07403004024040c0d40820b0740d441212958075206856428140200c01c021700c4020040c10903441c03807030391004181c0c1004103400b00b0404844803102c00304018411250145019540781c43e41c83c9840d9401903d02801d03619400342c0003a04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 404511402 1250 404510152 404510167
    0x2a0d14070504060f1403070806120109121805030724110d11010f1407110a05070515271f142b0f05090613080f19080703050606 56
    0x1908a030b05031100740c03d05501c2c0c00980241101c0e89040803204c0884003100000780040a5000300030507108910481c2d50740702d1a1070380b01c10142600c40611000709050031246031001514010213098074084186000040f24941d1540001d24000907a0300880080300c2c00400300d4000c100285507000c50302500d051405040b903058440c0341ea9106034003494410440d84207410990040e081d00300542c402c507807110510000c0c452245044418100740c8ac0180469051560b41c14051404140802c1c2680c2060241c045a8a081e043c030110144c01c5031010800002044408a40744025504055494034240c0300d00c041c024400600000614807501c03a003209440f100b6510a01d58032034119401010312090032901c9240c0f048400304a5904052940045140507240003040001e9501200c640c02c040c80d014861a1205c17900d540d2181c2d805e483c03d03c03071207444480890108080e030009000000c0404606031070b04a40d0081152208001c03043c001c00140a07405001072194140103698002604403080c500c0d0500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 404512652 1250 404511402 404511407
    0x80d0606050310270c0908071e05040207050111070f06050606091f0306120b0f07170a0b0303040f061107060806010e0f0d080f040f060c1101082a0d1407 67
    0x702d100c0e0400b100c81c248241001307044030103024500e101d0b089a00b4048082d0800e00500049840d000e8940244900381001508143c203919011040809000754952142000b09001c00381d44102c805032040c1d0340b94003e600c5000760f01d2008100507401801c90380140348013032800e00d0a80d24090070340c80c030480040c0012030103941c5a2040050050030040505000354451805901a00703250f8001110009061a00c1c014000c03070a000c1442400344514001d40f547d00d00000f40c0301c155401041440c50002c220005d058100749601c85040c002d03004040700d0415940c1c9100c1c080c090102e0f0460000103804038022180c131340c02040a14040c2c03101c1d08203d2510310704030000074030104103041c1003841681d200980300a039071240b2104400141d04482d19690700c2a151441030a0340e8000d20403e40550807241001030150300c54139243c0d19240c0d0101182e1403030000d4200460b9007a6003d0864080c0ca03032801c00d1024150710803e00c0f0141490441e408540b24898040324108483c80f551010440304403100c20800304c5603 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 404513902 1250 404512652 404512681
    0x60c0a1506060f05090f0a03020310090312020a02210d06060c03030b031b04020d090602041403100c02100504051006140a0b090a09020309070e0907051c0507140f0d080d06060503 78
    0x810548446c03103050f11050020303480702c1180c0c0c406501400b801c02004400d5000b42c101ca03003000c1c003c1d12001e540e880b228020808038480c1442180050304170400c50b000401100d404007200185000c1c2c518240212458078034121400365002e0b2000c50540c1c20440c1c1015014040c01c81122000c80c0a41a004d021010007800059140d040e03070300c2107900150b400084c484907801288400e030400011511340d03841e0800e0844a44460009510a01c40c0e03075044090b0580034007428030001602e030f01802c80320410600c0d640203010003410071a068040c06403084003000d0380380300c0c1c9802041d8019620700c043c1040380034004420f5844e000641005020401084680c4400a1480c1140c02d11900140d6a07510a03440d41d080c080c054200d006e24400c1002408404000001c0690666a0490340c54680758075802c2030010788607079100b004010341c1291004010000c5201f040c50311689010304043e24902c60900012441c034100c0b00e0840b14240041045010141e491003070714007501d00b41c145289541401a01c2c4102d80 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 404515152 1250 404513902 404513917
    0x1507021e010231091505010908060705070605040206040e0708060901090c0903080f04120305070b061210050901060f0608011a2d16050109030809030a170402060c0a1506060f05 77
    0x9511603640741c03c1c5100c00d00154802420352140400c2100c40c0d40480213a89843ea104070b50008007c00d00c007090000c2c001c1807842c0260829240c440c50a199035440502424004105a81c0103405020014500a4400e405445869985c1d038140079440c2130b50802000050680000403805e10740101c1e44144c6810114210549401c01d07001501c4c4d40406281e0035051280342c10091560072403507686c04c105070300300b00a800701c030f44203a01d01d0342240c7d40c580920071980000c8024600650040504541418441d4042c580007001d40c0004291340da290b2103800d00b1046070b50304c81000244040010400703002c8451004500119044e205441c0c50a070111031103000644501014400041d00066462081341c0c43c2180e581405814070700c982000c450a04900034400c00c8000d5000c40c1c59000016000c3c0ca001c0222120a0019151a04c0c041000740c802d96120000800403608041d0802040f42856010000c2400c401e101e121400c440c003640c2d0aa560940f903042d80100300b40283c81e00b20050194018060300c609 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 404516402 1250 404515152 404515207
    0x60901061215110f0a0e01170c030a0b090c09030705030a0b070518031c020f2109030a020301150302010f05092202220609060914090403021507021e0102 67
    0x900b903465100000305403c554601480030001000c80f58100c4a00c00350a044d0303403131b4070b8541c8001c1281c001521400e01c1030181861070801b03100080c800200e05809140c01a20340200022150a5480414070f4070200fa20401c401280100d20340c40c0c03e180030000e2001400041e800780030031002941e280e2000c108041c001e902404008508220110000c6003130341100e650040c202c40544210303614605038034000e810001c0050052090b40c80c4200e5000810a1802600c40740c0f03009040a0700f44880c1c6030b0f80002c0c3e00315a00d8081c801400d070150341d00340108208002d070141110b0240d841e504c0003604c02c10040200c00184a000e01407200d541e6500e003162505501842c80d500d0758a103100c40d1843c020b110701c07100ca072404900c080090100c03032000040f00080d030740c45880f04403019480d003030700707850441c0a40324200017031101411101c014145141c105401c01c1c031a004444441c0b01d602c0e00c040c2456012908500140e021b61b084100303900342044000030101314600214a013211820002c9032050104450126 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 404517652 1250 404516402 404516423
    0x18120819021009080406030608030a020a06020a0e030114150d053a08090f01020c030403080f070f11012a02040b010e03070314010c050a050a0e0d02040f020a020609010612 75
    0x99041c000c0c40201002d1407000703000c01954034907160120103500b09000d8203000920f098004542070320004111400c1d00001c2d00181070003402075550101950080300c0000801000258a00d101e403400d004403c1090340c103041d06196450f14000008810140a000c030f1702c104a074458200200e20041501ea61200310640051045503c52810713004204c40c8045503180c4844404540075042c0e03100700158018140b1500392200821652111400d13401101131002080d04100420400688030700010687c1c0b01003242d106003007203210f44801204508010042c1d510403114121840191381c0140d40140803003804840000c0c0c2c062500d0750071022440b05500038000e980e201c03a0302007682c0c00703204e2115036405d001f0121880c6c1902c030328041c4419427001b40701d100e0355800c00c41c07500705035802031054402114840c0c1c6e415040003500c4404680c900401c05c9c0043e00020a40e18803400751712980148541450ba4880c0582d481da17855100074034180380100316a4041e4900403003800342c030700e0943c0742c000302940140c0b8201 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 404518902 1250 404517652 404517697
    0x30c0204020f1b010609200c0f0102040609080c100518011e09030308090604050d050307180e150a080304060c0203100f05061002031e03041a0403181208 67
    0x100240709021110001c054040380c410001c160583c605140142803100038081c60f6915160902038914191120240140c0e401420815008800240c00e200c280e800880d0042842002e9003401c82c1d00c60740104c00000c1c1c110030244082d00d01000064210702c0140d4486c40d140341d07020001000c81c040c2c2a404500f91036581a203800d141c0c8120100c42a400084002148003c2003c0000c0c2610149100032804680c440d000140010000f00710039204079048005000c2c4844202c20840d101c0e84020000014001d644244050159400c1c4054020b0082c00d040300625042543d00040c0144060056502c0307a81c0ad42818001d0002c00300666040b40e0580c2803454201c5a00d10000781403840c41000b44411a182100c0c0c1c4d0300384007461b0091401307610140d9541c3c0e059090784a0490f280c0c4904c5640c44100c0048650b0000380007181d500a6a0140c054580b111440c4c00b0941f00914180041d901900010030381c1080d03c2c1820022406034008001c1c118400c60821349503035030440c0303c5c0600310b00003683c03c1d2600440b1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 404520152 1250 404518902 404518909
    0x4140d0204090506011e062c03070806010803030f01080606010c0602090a0506072009160c030c050d18060e0108060d0305090315071205150d020105040f0803072904030c02 75
    0x314602e80c018113541040d80c4440b2244a240720b803142000f201ca0480b440054040d02520003510300010f0081d86034009201000c001180003035103820b00e5054031070010b00040b0319200344141400707464554082c580e00c0c14698148200e181045e000b41615400100c24080364cea00054010000e59125101580320148840041c1d01210f4a40c0b0080d0011400a0108200031580c07008618040424030400203410707010081c8031659000711002c00c0e6440385400c5c0e0824440c014010650502d1003854003044444142d42c3d05428210000c034458080b5150b001d400700365008144a80010b080b062030321140148116000a0450f40c02801d01c0707015aa2840380d5009040c407542c2180e440410280c01c44000e00f2102c20b4064415030201c03442d40000342c00a8001d0704041150203042c0c010110f150070200864080303401c0000c5414001c0c0101d0500104102c0060fa00d60008100310003020248081e41e1a07014906040d90310300d620b00c1c49a42c000042c554000d80e01100414269080780d050719044e50007410307a1011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 404521402 1250 404520152 404520161
    0x5010f0e0411160602041802070213200f0331080c1c05040e0f1009020d0f0e010b1201150e100816061b0305040501030c05070b01030b06100504140d0204 67
    0x21500f52003581c401801d120310341e0000c008454024072410521294006640101c6c0070301c0100a5002c25004075403a2142900c1c1c0288420000404140c11501c034003060540095010b5612409074100c02300c10001e8079502502e044040c40c51011500e80c250740e01a807454030840200f0401000540041458940138508000d14130340c401c001086061a14180389028000341c20900c9038a04400301c00e80000c4500c1c1c80a010329008018450403194503c0c10700410102035081500c001e91801d940ea4000b005403c10741c080c0a0519024100004007140321030240003500800842880041c2e0400e01c1da846864180c8284204590031440d0400171b6072030f80c840300d505030280b6920a038594442c0254140403110320008070401c0b0355558442802c1703001031050055211842c0307403001d008203030305200c2004254041e0f007100c40c400e40702c0d18250340350402603500c60180c100281c1054500441c10410800f003800c0c01c83d40d038060f62841d41040c40c2814a010b00c40000e1070040c820305401500101602021034489800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 404522652 1250 404521402 404521417
    0x504062303150c0c150a1b09180c0e130e0d0203070506220c0603021b0c010804030f050405090a0902032512020117131b1404050c0c070b0904050105010f0e0411 70
    0x100390b1602d0070601c003010094140c000648283c492070b01ca0700104103001d42007041c00c48027400c2e5a101c0b6444500a244020a18610200d003802801456164643c0d1f54123400c1c12800140a0000365881c0c400341020300d040344a0002d06c055520802c40303980890800034030681e00c0000000d641d503a00031a6600c81c192051100030040c1104603d41e00805e0130b80e01900076000c0014451986403060710003012140d0703600c540030502404503200c0300c00b040c04644070b448424628907050401c603280582d01c07800705d182030740704a0300d128405950b0310700001149001c1c08610440300d4494410380c0d07900c000f03100702c0b01c400340039105264000010052030011a405407810b0750301c0b031074012040328480c41c16042c030b15010841c00030100c2d01d00f03818100e0002110420011502070f140c14651003074034440c01e1014080100b0340074090b0100c0d1207040c450030501322130802102c0c016000d4411055110702d180707018041990010b03040701d410b0000400c507141080d03900c070034a440c40315021100400c4490303080121038001d02c541071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 404523902 1250 404522652 404522683
    0x12020d051207060912090b0304030e040e0f100f09050303010e04170304030e240409020d0b03030c1605040212070c060e0f0304080f010507050307050c070504062303150c0c 75
    0x242c2200f400b103a90301155543d40666502e000700381e58104211124072a901485a15080901c0842c021900c1201803406c4084042c10020341460701c0080a46800000c20b00c0313400680c44241c2e41c640159140c09404909004210144001081071f694151030380414018000c00328110000602401003480c90445403180c1d849025540341400e00300241158101c5189a0041c010f4401102640016882069241c51a1084a42090308040c0c50f280690300c05640c100440d9101c102d5102b0351b5405200400721001004010403040200c4800f02120380d08545c0300d40d1141e88107200d4014a0094030003003a601070420329003030092003050b14200340144520201c0c03040910440c1c0070030f0840701c00000148241c5217913808070792100346034006181c244c0388202c1e22a000500d0a1002c140e17041e024030007034a80107943d00203a44015454101040803200c1940c03000c40c0343d03010f52441e11100c0c020b03a540003607214401c2d005400f00140c160851102c103074020708503211000b400120550204001d0291780d42020006 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 404525152 1250 404523902 404523907
    0x18040908040602011a0307090b1f020d11121812010c050a03110c1b0d05010c03020d180f0b06040209120c0913050c1314180606040612020d0512 63
    0xe040c04980398105000e078801543c82d00100740c0c00c20500101c083c10080d4010000c0a40a00301b9001d0009414540c141640080310340d6000902c0c000b1400700301c515036007598001c00c00001404802001100a60120581c603004003038145c90a00348103003100d4111444d051900c074016585008901000000c103601c911f15482c0400d10160181c0c090003c2c500f012866034140070503062920400b03858480c041c0391071015440004210705075240301100500040d00100042101203154444c242590b84400c48140000e038005020030b00c4152502c282c69007400100b40311403201c6525500c00400414242001d0261240c00c000101070f540c498044030440700e4040c1c4038407101d9007912200d0365140c0c09131442c1841040c2140000d21004080c803035111030301d40c02c1001005100111024081071924018101000a455079225801c441c14507092030b004a45000800304041c010b00c4015040c41c90151480380304a051000802c00328145500548021350115540301e500001d42c41c1c00b078036003d24a4404126840c02 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 404526402 1250 404525152 404525171
    0xf091c021209010c080c10110414040b010302092e090819060e1f060b0f041e09090f15020901020d03020919060c110105120a1a13022101031101051804 66
    0x704200340c580c51040d20900008241d0714100203140114003400ca102000380c848ac10071860250091581035406040042c6840c0254001c03c2d900400510340d190400420400192040742441003a45d11030301510b020314100d03040100c003540b0b5040d00226405922040108103040c015940d10000c4040507110807540748038880b60764205054803140484500c03e00c1c01c800010411051011690190280e85146103060300340038201110304018440822100010400458070040702d1252416540c0074143e00da0341d4505c58078207101c02040414010003601c0c0180f041400c035076000139240000100c11305025031100003410110303c012103200d41b8040da0320204500003d2494003c990005403c5c0902281c03111210b145005507158810756154241c4020060300180c8000e490f980603240c02c02840704044540500765000600071680d058070609426400207004100e0b441326068509070801e54940010258034503241d017101c10122071421814440d0000e032070720300f500480703103c100e00580c014000c000f035566 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 404527652 1250 404526402 404526427
    0xd15051803041706010503010606050304031407080310030b070906093c1706011a1b120310090603020303030429160e040921090e0f091c021209010c08 66
    0x84030040c0003403134003804c800420141418062102580c078a52965855615181d41c1102c05a041811254040c02c042c04100c000400c48001075006580d0030380d0b07000f0250b0444c00c040c0c014030f0001d040d000c11b11065600070000783d42c0080c202c80448181032002c2e0061001c00740703042c0710072224008149010012405a0048482040b181000e581100907241d05811513010110381c2c80e01d00717000340b051130104084009080702645000b049082002c0103d2030030703441c42200700341c90000040c00ea40e4103600301004003e14000b210400034014002107105000b040e00e90380100ea01c0b03100151020705450782d80605030000f0085502406c01c88030b420001c100d981e15107001e04140920034442808009040310600d10801e19040c043c8200303250300f211941c81c49480007010b03444280200c420b20814090002000183c0441050300903116000f01a20106c50345800d203801820300300b098000303101c001c99800d008002150f001071009586646031454a5891800a0058406d0440000020300c044c0c8000340100c540310 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 404528902 1250 404527652 404527679
    0xc020c0a030605100e1b090114030702010603031b02180a090b010b13090624030b060f1801050705060c070f020907030c021b060f03060d0b1e01050d1505180304 70
    0x1a10310f13a0441c0c11030716140000d9040030300f80e401c00740500203c0c905a00598940e030050016a1050501c5903040194140000c82900212075410160350344031b00400038503130004103003409802d1085e4408103071100c40c3d00160800b401d40d00e4103007030365002500040c1d0100665000020b1a500080150599a950484840c2542c040c50701142071012100d000501c0514a0060b01c040d1041803015070b40880c000f003071409440c070001030745204040c0c86a4040c4100c1d00c4940040c010860030a09a60340c07110324802c5140c0401141340c480e410480c0c01c01400c1c012074070204200d41c00c4040d00c000d450f5203100d14100b03850a040c2c40310300a9402525003003403220a5070194004c00c0381c0841d1f5020b80341e0301c10080003d00009040e00f1107030754001000f00803001c0d41d2000f4070001d42d40550300074204250b244494682d680300c1942299103650844001c2c94007296100049486070042c5000c841e00b0200c090340f9614403c0c101480041c25510b191503c012030b00307440c0e0b00b03515030415090190480c0e8903142e50f400c1c4140400d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 404530152 1250 404528902 404528911
    0x1005040204080f010c1d09040302120d020904110c07030212070801180501050a060b030703090804090207030f0215060a140303070203010c021606080915071407061b170a0c020c0a030605 81
    0x540c80d01803500317801e034021500307800c5190b400d1201c00000080c140500256813001807041701180143c0d44a943e0b1030b0710401c060032802e03030401070068994024009000840700750300a215486074051018155070743c40080c0740ca0a40b44d040c0d590004201d0300d008918901040740d0400002d5500f081846401d0f4001c0d2140d4844440c0904004c0c411500d510b64244100c2c1c40500444407402000c1000440c0c641c002c0c0c0142c42d00600c81c000c41890300da03a44810101720303001501e0807800201071506000141d03604010218503c40e030220395036070324107010b0002840e140041c8150340e003050080b00001903641e420701c140d070300958024009020b120b020748802502c80d00d00441601c0e42c1c03d2154404111035200f281901d1240d40c800009000e0400e2040900c078003044018201020080c180b1042907080207610003900d00d0324820f1078080b6045e10300d00a19288008841c101e041041040d012a030f0094000325071031130704103601000000d13500c020070508a080241f50b140190b0032889000c400001c0001c20340c41203105 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 404531402 1250 404530152 404530183
    0x902031f0c090506090931080301060908150103030f0908031201030507120209060603040c03020a08151b071103070f080c030d0813240f1d070609090203100504020408 73
    0x2e09440e5810000c0c1c1d030288103952600464114001450526a4041031084a00009154a031a1400904909110104002190002004030040100c41d4010104201420a14024014081002c110b00001da041480082c0070001000a140100ea0107501841c003e00710f84004c2e04c0c1e44011039041418415828031003120700380714042c40010010343e02040c11610765070060040c42140c8a840c04c000e55a0006001601e20000d01c80001006a481c42500c6000b070092101030014400c001c0200344c02e000c4c0040100c5812a09901004070300c28580c02203801785684124000081040324021a2a01d8655002182d01107062080072a10443c0000c1040442c05c08900f203951012048504030b42501003034031181c5400e4086500900003c244a10500d20343c0070101181806a01c4000468103403034180c00749001e900c1c3d80758460f0500765203c0318444103460302c403401808920300d400c90092503085c851080c1030b001c99011011035022107035109544002d09000b801907480d10340790036007e0340795500a2203001c0c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 404532652 1250 404531402 404531417
    0xa030903090e1501120605032506080720010b041e050115080c0c03090301090303020c01230a0b040b0303070803220b070c02031903020d020c01020601180902031f0c 72
    0x182e10300c101580038440c0d02c402030ba4003a0300b41d0f010010340b46007550702c03012074030303103480d406c0100c0c0e40d403030030000e50001d0100501d49501580385440a0051080541c000c02c040041d5101080240c0e60010001190720f20b2551141441142102d440c5006041c0885407580c0182040399003225550302c20303004503040f100582c00300140d0740d0764410340100500309040100452545030000f054104814080c02c44a82d480054a2400c811440044c0c00c592069400f100440c0c0e000c131703500729448824030801d0703501c040300502d03414240c0f4844508a00b0381f00c0140004409030303da6013814965184d40d0810040b451010b01103903201c030283d140c0280705400449a5020a000c05103001085419213640c05000b01d4010038054a543c40c2c480c1c040341c0c4580b0f50f400a98062040f90304403a0305c4003c041030214068002d83c040d00b030b00c1c0001c2e100242806140c0c598641150b1088005000d4142d11840225500c0c52409000455004600c042030411082d0010b050801d400b0350001011034441d40c0001d02844256601d0302c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 404533902 1250 404532652 404532659
    0x70509181b030f0112290a050105010512040b09121216180b0702150d0606030b04090209131e26160b040c080a11030c100f0f05040b0a03090309 63
    0xa5950100711108002191110010017070307003991071a132420703860203042d46840c080e09420190010011007050f02d4200b142500030000047c1e2244103040c09000b003481c1c003e261030161401c0c0c17070280130040d101426100b0003a0105407105c85c1005000301c8100340c041c4443d100d502c1c144510000c02c1d0100e8280040140440303440010318803440015101030703502610458054100040b841c002e800011040340c00c20303800c411030307d81e2800ca48050304441c80d102d440443c45904064006059840010145020394100486a00140d554071401c40c1c2c00101c440700151149550f041c11141c4404190b041d81345200213001c5d01042c04510309800d64944c190540c0110307840480c82009405225103d25550301032710294001000070700180c411600280201e044107030031500c0d000401d0038402c504a00715409030310240d021020b41400d000b4000150000c49207030050407103052000e00490780c1a144001000003a01101d0343c1c09000344103a42c05007441e0b055464031403040b11405002403502034810340210b01c4500001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 404535152 1250 404533902 404533951
    0x80f0a111203070f050106091a030f0705060909220302030301060206060a0b070b0a060b04060c02041a0a05010809191103100903210f020a02151f0e07050918 69
    0x300d00646140010b5262800940700c42c1100806210102d42c030703540b00c050002d80d1640900480500c01d052000d82c0000c1e10800007018589102d500710081960030004040006603a002c050b40d50102d01070f1024643c964030401c04841c80c04010381071426182031318000409055000024505a40d03c0390211a500d403131b00b004020898840340b0504a0320402004104001400c40d84d141b6044a800500440d01c1c5c0e8444080b0202d0341c02513000800001c1240b0b42c201c0035403a040c001c0b1540240e08a108100607003c010104070050390718003481d13050086000c0403c4516008005660012000c2110500340c0300c1c9906c0c04a481003044441e062291043c6007440c001e4000a200b020f1402c0d500d80c07101035410382c035445001a000d0100303031006455070756094a403200144070300003001052074980c040d11075031580908440480901900c2150580da48810380c00141842a5482068a03101e106c540511380c1e0b05201180d2500ca00185140c110241a00709140480c034000e003d0300503c4c05901414490340c040c1d014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 404536402 1250 404535152 404535169
    0x4030606050907021c0509010c1a15041b0e0319111f170705130b0301050307120b04020618031605030f01022104020d0c060905011205040b0f10080f0a11 67
    0x780c078491005c0480006141e000d88000c15041406040001781c2011035200d10003145822100c00b00180c104004002103403a4401c0108402c00302100c08002010000300203d02c2d4904215294040c8a414800b495181e9400c100c0181c10040d03c00810215611918000511480161500d40119511620306001403060540c0c50018005580d840c0c00c0900090903140d040500649a50240102000b01e0b4500f0f0340c90030340d1807001d4019400090b989514000a05141040540c03081c0000a0001000000106036000c4580c2003901100c1c85500e68521a20b404846a9101c00301030340345c03041d07441c611003900c0201810b400300c42e070850541c0c11048003000303000c0c01d034810b400e80062301000c2c01129001042d0b80c4608640c001d4000750640c50641410b58880d29001c0c2c0726000710012460b1003408022542e8002031090740d41060750801c0c08182001d81d0342030000b8202500d089042e528000006090032a98040301004080e20710440d581000403c4c1d0098413080c2001c1300f0344140707201d018966605c0c20310049 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 404537652 1250 404536402 404536423
    0xe060108040615090c050403020a0503060105060f182e030515012102071b09020a090b28030f05010b0c03071b0905040b061206060901090c030f020403060605090702 72
    0x1144416641e4075a1101c006001c1c010691142010510001c9400262480ba243c20b074625511419900d80c11401000700c0440b02d41d1207244a507006100600154584000b41c1d4405070b0700d01e54490326010903840710750303895521503032030303a00860b03645240c807141c0070006080d02602d400300070820540e0524900403001c1e20011280108880301402107040c555105282d03021003030401c00440b0101940e1140c3e41c80990380104d5055503440c054000315180309031000c0c4014010401e00303200310300e80051540007a122008170b1050220114001c19408600e00c40300320003016004512804100410f074003030000c0e004040226400fa00f82d0b14107400410b01c5d602c00c100301c2c1d0164000c40011400c01403a566550f0100100e0182d40b506105a2480065601a1801054001c912400102c1000e1030314100344440e602c424200c00c08182c1c06102032081a803180361035141503a4500c0e50100d02160303806d40c150080c04816212040d00e604c00600001030054940c001000d85604668901454881400403641c1d60001034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 404538902 1250 404537652 404537657
    0x5031212180c0d0302030904050f0610020609070302120319030501090c033303060c1e08040f080a0c050601080f070e011512060504050403020c011e021911031b010206010e0601 77
    0x8401c0301c903915240d80940c000e20300c20305c100d0745088900300205040d12010f450711041c0c2150f01080c05150f10f44515441c40307803510791008114906d401d101e082e070f6803501848040d01440c0b02141d03103241c4007014021959080065107448100d17244000000307004150910802d42064606a483d60751203101c3d015002c2008100d00ca2081e8034840121003001e050804140c1100103403140c2000000120340d40510f042c00641c6844648200d00c01c0c6960710039414270001c00e80c00b003000c131004001c0060130f510200117009411041282d01e8500c44041034400810620018020740320345000041c031035070000345c80c00c00040204250351200da80c0f0413a03104800801c1c06403c494402000d07070078205510450413940c2000e900640442c0a990302c4c00481e01b294003e99003a401030300280c2d040c0c4002d50308400d401c00380d4401c15014201d1030843d510000d4039111070340140b41010240250f003400380601c0c980c425030103c03001019240015a12448141d000c1c0d00d000f4002e002d03011754000083c00c04500c01145210f1401038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 404540152 1250 404538902 404538913
    0x10090e0c01090621020a09180b040501050109051e1c050a021005030c031306020423090906010602070311031e0601091422032102091201091a0a060503121218 69
    0x2a101c03c044c1d04400c5400082140c115000210504002081c448007000104001804009c0200b0b000503110141c00c03c0b03051183c030301000c00c45601c4007040e0030603401c03103000444500e1003d4000900000041c000d410030070408800000c003403010114281424a108035510107468030326030801d07510381c01b0132500c0c00c1004105100080d03440001300312904017580319500052800e5118981c0b2040c00c1c0c5905814680c0e20441c184240c89810080030304c41e0400c5d4000e005064640c5440d50082d6994002e02000300a01c160030100e00b2584c81c2003066080b420300120500b4050906044556900d020920480191740d0802428401c08803500f40098001d04c00c20418040c1d040303c0000880460f60012412010460444e0015010150300c80c01e44c0a14514101c01580d143d00200c03c10204401e004d01e200d120787d142c4405640050840b152100000a400e04181038a5454200450091030103900840c0c050180740010380720380000000030010300c0b80161a603050340d00c03804444403c00340b00c40b0031800c041c2e101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 404541402 1250 404540152 404540207
    0x3030f0e030901080f06031e0c030a060f0f090b0a0b040b040513051209090726070809100203090c010309080d0906050402121c14040b0415030c0c0b0f10090e0c010906 73
    0x8402c8c840d10131180800440c2c0c0c84854280c0420b1800030b05c0b2078251040d90380e8000182407003003103025100c0498014030007403101a41c0c980391040000c0d40a06030020f501c0e9102c440ca01d160b201d0b50131820074400c00400400c82031411071018188440070f11f101311400e00588071420031200982c0152000200c4c0608010741c203540b0114152805d06543c80404413001046000c2440c0020135111a4403501032a51401e145040035031a0351b103800c02000744200d2160040c020410781240011300712101000900e8041498180740c14a0940380c03058400162240303041c40000000d10101e40c108a000301c0c400e40e4011810503091001e55210910783e510790000780d4060100000351071152070001000942c0c0c80b500ca141c9560f5035000e09243d400f581c0030f11007003614205800c451036003511400a03640564201000c40c034400f0343c0d4280c40ca0030010141826042804003182001411a00050141500c10350411401c2c01070002560349104001c003090000d10009000b02e00b85200d040c125074106916616007881c501e5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 404542652 1250 404541402 404541433
    0x2a21030b0d0804050d0809061602030c060c150c090a08010507081b03070c061512050601061107090f0213140a050406080a06020304021225051f05030403030f0e030901080f0603 77
    0x1220041a500108280104a49907541000521a082e5201c03100c03e0b60b049c20340f0515003050900b840061007100c050081507104a0301140807059080070503030800b2255951500d071041c80c000e500d20260808440b13400814030400550083d40100c071151a2070030300f03654111400c080c0d10240203c100c48402c0610200e201c8a000300700b0505003d1280f207000c59482410514500a8190342e404000030501d480400004d002090185902511080c80c0c004010400c8401c0603a450078184600b16482c1d60342c1001c0e04041416034103031951301c086d101003d040d03541c0e5401403802071942c40713859501ca031f0010040000e19203058031440c4201c6030400e01070400f0131807580f00c81c402500010803c0ea040340884012034100c56043c4030207180c1c0707480324a410041040d20341e4203040341c0260381c02c442d005104c00b50980152149400c1010f0b1903002328904280e490303940d458120003401e030300d420310300c4004c0c100300444149070008000341210f00420382e11a809a910303060615a640d07015144c01d40c060700450044601c404 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 404543902 1250 404542652 404542669
    0xd05130f03022b120509010e0612040f080c10060302031005010f0911070209090a0b0f040c0504020a02010b0307060302040503010e070b1920070504050601020d2a21030b0d080405 78
    0x40a02c83c02e89050009440d610311035001280c1c1038001070130020320043c2a45e0003074058544000e098403030600f00007803000c1504407034001500281854a03408021400c010341d82048401c007080b694140d0f01d090303804002c1c01016042d9030100324820300480340c41c8003504885105060484880c604401c0038075142098520040611980002e02850b0400c910b6000d40c41d0308003514090700e210801400702011500b05503003804800340c000c402c05401c034014400420110b01d000780680e0b500325030050f600c4050040607801041c02d80412500b40c020944001440c5c0e4144d40904102c8a0aa00a01403e55880da6258450b41103009522907400144a0301e04032141c540c1e610000c0d03800d10708009000325a903001502a075600c0c41491411a03100141c18403427801c0900419400c80303008e000038046c0340c1500b43c0c0644114405100d4072110320548200e0403000f20050480c1e18415005042600300d074990340c0030403001c00d117500c148102090410664003490304210032900b80e040d40001e5803e041a084c0002c120015 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 404545152 1250 404543902 404543959
    0x40c050906041112010e0f0108121308060f07020615010912030e03070308070c060f080f0a11040b040801060e0705070605040302070902043302030a110307050d05130f0302 75
    0x6a514000c3c4008012140c004110f08441c1204840e0150700d04039851104e484020203510241c50002d00412505900181e240c1003910b4440b096610355803001031210780b14026600c4580c6a00c07400d818403562031402142c00e0300500c0c183c0d0940340e25035507074074800d07011400e251059400140e0202040041024070005d2a582c5d921919210142d10000000a07240c030f074140d08140e903010400601c103030411030f4103401c5030700420150500c00d0010102c680060301c1800e00a04014100c52010001040c4101a42c49000c1142406a01e661104c1d00c480c06840d040e0440e0092105a43c40e010700821240002c4c2216449480350740d0711240307801c000f40e403203001410020f8411800d501c20828045800c03c49400580050466030302c00c6801009170b1400d000403241030340000d60102010100314500c07a940402110203200207030410160344258110b807c1c0c80d41c421340b1400703001e5024032040c0c045016488001011080e032684001c3e00465100e80058126012520002f503210304142e6000007100360b1f007240320b10034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 404546402 1250 404545152 404545159
    0x70f0f110a05010203090f0c0312090103021803010c052a0304030f1e11130c09140310020c0705100f0504092c0c130b130b060f070c0e0609040c050906 66
    0x1c02140e542c6503070980c1c10503202d0002c9508079050a54107040100000c1c1e03000c1c0300417402081254501802c500307403485440b9400d410150002a2030220100000d03600c03020f2200540200b00c1e101c001a401850b507007000d00720300d145000c601c031240402c06007070760b410424440140c00365160600e5559842c1e840c1144680450300321586514001820070b00c0f5018506050042c036410340b990000a0070040b605240d6201602024601004202d074540c0c003140c060700b52405122004400c51010000a107800c10fa03100240e21240000784114031004040b4905003100c0f025a100000806a110207943c1c06410a41020021b8001d1008129040f22600038012240e010440320000c4040e5540100304140030052003030950740231090050150410010321011060039080400c941606d080c0015200b411441e22042d51a0320341400c852580c2e107080c11110301c0601034070200e50768216171034603d404a07040d1050007210b2040c000080c42c00d05080c034016200715407160780041203e043c038003080685c2c000074110a81 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 404547652 1250 404546402 404546413
    0x3190b03060a2a09061e0c031202091c02040b010206011202040207230d121808130506040806040302010507140a03090c0506070b0603070b0406051e090603130b070f0f11 74
    0x15100524004142c40001c1ca80e076821043d07043c94009449104148106203200d02500d98124406600c8640681c860f0b5061034645180c271560340300d0402a000d01d030032499002c070001088085e083d61f50703070f901001c03c0c1c402c1c0d8050000814100041e601e8000911803034039001810000f020041c6403ea0007005818130a03501104519042061641c0c400601001e1081c5a4080880300360005c0d08840381d6800d02c480341409004400148403c000c1808440784018441000480d10703000312262004a1030160001600607901c581e034480400d542d80700305840940c055480c101c04104810b2081c00000004041084410b1410210b00e000b20010904044d054807c02d100d0701010949070340c2c107402085214002d406907489420481c003010300b04011030303000007640e1100300020058203030800b040ea20790f0502030101200b5070003e0074199010740b0881c140349510080c00404c10080007024402c2088140c020b4008072502d50791308070140c6590003004000008900648400305000784920401c814034005182581c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 404548902 1250 404547652 404547701
    0x30c0503041b03060e0c0f1f2111190206151908030c01022101060206010b0a0c0f0c15090b030115050c07120209070f1205060d0b04060203190b03060a 66
    0x300d441700d01c6504001d800c4001403609524000c0d500d074020303d0003161700f88040700389144d1501c0c0c00c00c003050600081c0440c600040b900c3c0c0324401b40c00c1181449014050052081c2c61040c9003150307200301e030030660346000c80c40503411481c4005003841c0700e00044545646024014010402005000381e10080b84400141c4082846c51040c80603001146502001584a2034000144000302256040c500030400c08040104850780c1e0020380d890440304a079001642e2519071034001c907451503d480010300042224007842c2e0400420000e100c0c04c5070302d038000800301c80000340d00c12103000381c3c04c1c441d141410409200600c2220b10b44803403e00c2e58002410100c0c94940d44204090409210b40e0000200c6460803110500754101001001c0d804080c0d40b611002d1816080009003218000b00b6030100c48a5544c000140300f0349500070040c010503000106c542c0310340b51034500400039500842e601e01c504566041c86d0100c03400c641c0110b00880c480200500300e03075540c510b000300c02042034121b04c0d191000030040391f6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 404550152 1250 404548902 404548913
    0xd0e040b0409060f0c2f1606051c020a0c030f0309060f150b030705180d051b040e030f030103020411090a03051b0a030b0402010f030e0d050712030c0503041b03 70
    0x8442c0310310940703011840d28100c800980440e0507181c0580b0500071076201b1040700300790281612905840528254403c5003030b08000780c0c50654142d45070059049200c101203001c07608440a0242071303401100c00c10210303000c890600203034040c0c00c070514045204082030100090090100f0f41c40003603640f0300021100c41079182c910580b220702100d81d02c815030703503805503140c0c01044038400058125500c68500e9401d04400c01001351007101c0904612091400c48140349691f04944020b00c59008012286294a6032440207880c0110090309480f603850604d02804402021095a407149481d555040c210b038615002d00c40505000070284140403010000424156505900380b005540128010079440e00c038105205081090010303103510030000e2240c20000907018228603a44280e0a10305014202c1352400250040c0c1402c01240c002e170b0051025a440c0380394010b02034507080d400340508800002000f80103408480b070705e1030680d00050b4208000780c00700710120340600421000d00031451049983c0d03181d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 404551402 1250 404550152 404550161
    0xb0d0b18030c0a06090b10050a0314152508091506041d0703060501090912030207030c06061401020606180106111203010e04060f0e03180f03070f0602120405030d0e040b04 75
    0x48507220390305d800c1c49051061400540d030740082510b518491080c00c040004400300c06c0e51100030b004600c40152051030030020300400c0e14101d4403c0403078600382000e80f1901c070f8902623030140f0320915603050b44030712805201d4010341c0d005000c094007070f120b4101c080e141207044c2d180041003d500f1544a42500a68601221400070324210714005001040d0440c94444142e50701a4442d030010303414450800040f48000d00d280455102d24180142c1d1b07260645001d40e90008102d5003d4040380c07500900240b00300c0090010034030b803502603080c0c0b000c0b640e8503820404400480c104064076070522600500c8802d0040143c800e103d640e64040360340040b01c0958608050f84241c2241e10700b0070580c03003400200601da00a00e4260180c100e800e01100340340c40d00e01d590341e000b0708441d48080d0040714440c01240c1c0742c1074040b0058420180c155083d003925542e50581a42c070500c11400140f1030420360600311000d140540b03040e40c0e40140913054100f1581022100a01c100803550b5000350341d03100c0203285607141e105 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 404552652 1250 404551402 404551423
    0x15030501020c06090c01020c01050a26011a250c090203042f0f09060a080712031821080c0f071403010b061c0621060b0d0b18030c 57
    0x150756401c0e1001010b00f80b8a001e8121129a07206100040aa03038000c15001c01002003880e1094840000d01d0045803200c00101c2020b0742c030448860008002414a08500d050703c002c0d440c09602030110f4440c41c20385220322135079103458000d00c1c1e11100481801448000030705000d03035002042c035030b2034590150032644203641c00c680038590400c15030a0094840c046a0000c03603255041130f000049400414030404110460902c128000c200180c5030b9500d01440d007000d031000310102c680c00e50b1550086075800303200146c20340c04544180001c0c401c51800d524118155000e09480006100400b040301ca070311280b260040b50103000901001910a10030056444040359507402030410500c2c00440d065400d0759102e82501a0741800c0207419913840e00d0007241c403080f0308540c440b00b480e0580d1840c100200010341024039a07142e0100e007602e00c035984403042c212840c05081c1c100300f003007003000410445d021441c1d0000c010011070000161a58500341c000140308e208902605d28100e11408503c0c1031601809 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 404553902 1250 404552652 404552663
    0x1090e0a0515150703230708031509100b090102150f07110105010f0b09060c0319030e2107020102072c0f101e03020406090e010f0c0806010e041503 65
    0x41c01c2084450700d054003048920010f480720192110f425201c040d10348140711001d014400c040001511009814000e246000c01c5540d403140c0380d04851425010f1075109850340b010134284204006a60301d81100704a0003205088054041c0e246480404441604588503240c15402444110b20b2651080c82c6540e01c00c420800380c0c11410700c0d15060182c44890b1181d2460394580c5400010f024030380d1189000e0b0190303000ca100303854990180303200142403482001c030314540318000441c0c02c50304148d0f1a01140d01c00c0d101384d14140700804d070121000d40c2e01d407180305127000e640603d410840307001c601c0100200007050043c03042e030f012152900721414009442141140440d0543c0d003003508030030807086800e600021390b20780040090330321440300509685507000b08000c820380c603401c224030040e1540c0001c004650150083c08401d0f9220f00250040c04640950180d6500340030003e05038480502c49d8100505442d00d5600e0991155001118046a1280d08a420542c0d55190600350100da000700d100451046 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 404555152 1250 404553902 404553911
    0x62408101a0903010e1b2103040b1201170a02040b060910050c010e070f05010f02030421060e06091b060d18030e0909070b0f090d0c060f0c0b0c030601090e0a 69
    0x18410f150858102000760800303a0001c03070300700c244c410710900300088010040714418080e5051a1840d40030100641070900244000a80082c074598150040c015060360301e9070010072aaa01c14002c0c012410940d03581860780c1065407003500514099103c2002c652014101d503040003a914013007014044100c1c10480415408510303465180c01c02d0144040303101004e400b41c00ca19242c544004258401c600600c0e06201c144414504231602c208166001004000304814601e20200c5402c0d084c400d001809807020350030b08100f4040483c000412501804e0100010f00f10100b9480c01700c00c0d0100410b18140c4d110781c003000081c0b00149180100c4c030340142c6021100319050a40d1030b01414140c0c5040340d903070160f1200010030443d00c0d80030030fa4004031407000c150b050752101003208120192103104015940281c0b503d400f60240840c4460361001d44820f51034101c00c3d03184060040d00c0552000c00020301c004590030004501240950266801181c10f0501d1401c554454000790600607048442e12ba546588 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 404556402 1250 404555152 404555167
    0xa020d0e010504121107030b0703140a090c06141b0304081005060f151813140702070b090f010513030804171b09060f150307050d062408101a 62
    0x440b94140c1139245a08000c660b90300010307156910b0b2a402c0c400030b08030311410300c005890b10b40290080404208044d02c100154a0008991001010160b80544008178046c0b004501d03180581000400360b84001052030800d95004034a03640b8010b44060200a80418800000c0e920f50030408250013101c2d807100480d031441d02e0814862004281440700b40300388210824400d40000510445200b03c40074a040c021500814002c640340d0010856403002c014a000c01e50b031640e1081040c154000d00243c4c0c213588406130b0720104000d00340104205507511000c0b8220350421507000320001c041442c81410f50311405942d03601c4203e000c3d00f0a40c0030351030f404188010320703001d00c0d0188440c010040d8040d4026010801400c08a00c1040008000b1402400c581c520740754103070380b080056103d04144c1c8411954a1402d184020600d411a04207008441d007030260104024024aa98854070304040002845d41481780c40100c80c190301c040c000d804400c465400208030480103c090000c0740a44010640e41c0300030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 404557652 1250 404556402 404556413
    0x12007140a05061e1308090105071703070c0b0f06010e130e15010f0f03030807080405011503030302090a0509060619050c160f120b0105040e0c030115030210050f070b0a020d0e010504 80
    0x10700420172003510307018090407000140da0006480e9000d00a107001511100c1e585842803001341c18124000c094031006c800c01004c00c0e44043c450950921a208c0c144491b01e40850080d68408155200c1e0b002c101c0c15070103a85d0b1400c0c5040b03100c1e1440100800032503020443c3c022507007040700d2101d0b9445291269001401015503159041c0c0007442d020312105001c0346540c80051014801403d0181003000d0705010505009003500101c0e41499494142c080d855a286030140003580600358640c01900480c500142501d84079002c548143e001420040c03a03e01c2468200660305591011482804000d000249034000d04100344c00034030303408541c442040c074142110b80c00f00c0c5980c1e07401212040f40307421200b000521070501c0141110801c0d100404c07441c0302081854100300148036003e070950300e441c104800070b0003441100b07412240240c61094552901d03040455061144036a0400f9110003084480005107a1400b02275100700702020040c10001c0c0051008280c1d4082c1000d50400da4407207007408144030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 404558902 1250 404557652 404557711
    0x51306020c0a210e0108040606031406040308180303310f0611191103040513060312020307031d030715020d02010b01111f0603020604030f05012007140a0506 69
    0x400c1103000e1074040c461000f000b010400621045410408a04045410011640c005001442e40700304510070505203580c805696407000c0b80c0503000039604002044c48094031f0005100b04e003462402840c41c50f03880f480d205a880741c410880241c800c2e00e0524140840b080c00300c0c0e010480b40305031580341850109061510583c1e40702e41c0518001d01c0c041141000e40b5520169a101040301810002068488440d6090940c040c070360003941c21964204c01c0c600d180e0080c0d807181050b00d2041d0140110038843d40c1d0700b01d07506c1c09080c8004010440142007012011540400324210480082c1120940f980312003a582c4110b64075a030f10b00240c0d014040504003140c080c001c040c40100300f031130880400e41540c4011540d500e01240045446000300b58041c030304280039004080a141c0181229035034a41d40e02e44140843c030280c40580e020351030070b000c1480d171443d52100e0070501038840311400c1c28100551600c4034a5496000c8a2805100740c03e49078000031001c0c0b00144c403508a0341d503025001603803064a5504031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 404560152 1250 404558902 404558933
    0x204060312080717070c02040609052e0302061b0f01060308090310051b2508071b05090105090903120a150e0f0c0a0c14060402270a051306020c0a 64
    0x290613650404400000e580d40d10032401d10b000202d581290000c5070082c01e95070005003e05061908021621141042a00783c010b040c80c5060484010544040b10078106400000d501034010413401502540080078511b402d18140700750703050480014038003402c555465004442d03155001c14003aa4500d800c1c06040c419500380307402402030b440c22104050314085ea0505032140380801081c0f00802d08001010f1291000c00018250541030f0039044c0f80c1019008805c04031503603802003505c4810a28055400300442e04060214036850342041c0170060720480007030007122035200501c10354011000c00181240541030504000560482907a4040d1011030960007143d40660b10314140303d010130800303290769800126405202d0f1a2540b4a01c22958100c00b654058034103007034803101022862020030124000d5200701c440d800505200000709440c1e40c422040003d20805460024544185d0703900f155500070300700d1245503e488600c1d40c2c0c403012600490902c401c29880a4007030f008200c910040700010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 404561402 1250 404560152 404560157
    0x3031f08150a0e0307021207090e030a08160c0501020a0315050f1302090f0303040605040e010e090a0f031223090c0d030309240b010206160210050402060702040603120807 75
    0x20400380503188112490701400700400541d841481000094040c401c0c0c828003580184212140761003064415a04d210071b002c1d402c081e5140424009c20f0034400801c854200c0403c2c0c482100654901485000c2c00c4d0800c1e03849410f0001d03480e68500050007e02c028010300005441c000750b1921b011000760302c81c0d5155007146002d4084410403500c255a03224201d2844c2c3e10724400565220701c0b040c041142289400c0c1c0c5a5054840483d01240150700030000d4000d48a4034658a440c0e41c4e626804800d82e10829501400245c00c02410703040460302c411801c0b14031500a080409800f25101007480c1120f800a158009224007050440401d82d06409a80c0d007184d0310740020820300c840c3ca000505200c2044d0340086c149552030701058108aa0454000250344030103200f482511500b6415402400d00030a0490060282e14000b0302451020344004824030990303401440c40603444490000104001707082030b40e0041041c080e203001a500d50007040069031096400036600301140c82c0c05446018007424038000e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 404562652 1250 404561402 404561413
    0x703140106050403080304021807020a140a0210030507020717070608060303030c25020d0c1706040c06110106090f1e021204021c0b160212070506060f060c03031f08 72
    0x41c0d41d00100351401e0300c1d000f64840c0d40e0798489100250341d08000100156074a13540004010100c0d40208a013582d80c0d00441c40540402808400543c65000741107001b540f002c8c00303034081c0315458440c0e480f06030b00242500440f5074961f03c0f50045020080b20b084004100d034485030b014001e00350702c40d403101e030010019001182941403640e5224118040c158500d0440ea2060400d000d2034180b042154002c03a4003d06058909802420198214105401090b850850009c1c080651040001e10288200c1e009101c4d89810740c1080011034007101c03607650006881d900c40002007000f485500c1601d4103150301070b900007503a00246d031071082001203105030380c0724403881400700b05c03100d409807580e4a42c490390442e081001c0034122250803000c888102d501134007568847c010000c4100303005001c0482c03883c0a8089580c80b900b0041e0401491103a0345005100e41c128001180340f5050002070010300081c002d29071420600129012841c41d041110340240643e0313180d5480c600141440840c20151468202420 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 404563902 1250 404562652 404562659
    0x80d02121c02070312050406020909060d0201020a020118030c090f0b01051912180b04020f030c0f120a1b090501060c0807020127060908010f060617062707031401 71
    0x107044240c86440e203045650001444002c00d4840c10030b801315040b000d1810042401c141c200200250002c031b400a00400000340031840500c0c00903070140d41c0d0360341640142003103440340d0f004450079003009060981000205002000058403480158042c0110040001e000f0034581c0620b01958158601141070103000c108c004542402c4001c0748503d0203690900c085101d1940200d4801800180c1d410313000061481c40e480d040210201d0164000c0c1c0c02114040b140d15000380805441c1d00000e800c181d4000d01c090002040750038003192611110503024180d031101060b6407140000f00788070203c4040141d06449041c44444854450980900000d1400e026211020f1740da091031071003020701c003a0522800704580000300c0c03441e203203400c41c24000c0c0c41c250840135550070020b000d6495038045c40da215402c04403104196622442000b003290603960354030041d54880054012510009840d03240c200307400a405070718011030b45502d00008001d5108040851400300b40c0202100d500f0307e94844c10100850042 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 404565152 1250 404563902 404563927
    0x304110a12060e06100f060302210403050d0506010e0d110a050612040302012004142d040b090c07080318010501060f17040506060f03030c010f02130b0a08010b07030216080d0212 78
    0x35070a07111f071401c0043e6550102595141c054801018814080192104200c02c040c0c2c01009084400010b409c02e0103a81c4500006540c060701c12402990020074410901011035114403a06c86040006403c0c0103030140c8900c0410318603484031004000c8a03100e4000e10040503424030601141e8112500b40d00c140c0c84031442c904280b44070744c0c0301e50000c118040c4901d015654031098025008080f070300002e0011a40c035802d2402c4000010b0350350b88103903c0c000d900d4846081c80411603200f01a160480b618001143d607407651a0340000d0011142d21210f004000d0b44860244540c0380130701469215a41d0420a00c14002e1a40e4519180030b44440136071414000001c0c40044c4c0307940c1002c0101da100c80c4602c0031030003281c030714058640c6070b100300e42c04c00c00040151003440e4024411444101c001d40c15444d150034242c2c0c3c00c0d209810f080c40014600d240100304000c400005400c401c1c2c400c0c810380750740e0480391075030a143c44071076005004c858001c03031042055940c0402200980362000135030b0320b00b0003c01c000c0741e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 404566402 1250 404565152 404565179
    0xc07080604082a1507020f01020f041e030803010b18181605070f1202070f27060302060309010506010f0f021903020a05030408060108120403080304110a12060e0610 72
    0x8242c4910344801a01d00302084811808000034603400458049104d07104d02498921401d45044016006004075100c2c80c02060084800103015043d0892a251a044e5007110000103803a6101a1001034071700803000812090041d8004e021074036000743c95407461400201045038004440d1700c500c011001e0f1446141e001c1103040e501c90008401c51006025058059885104819006144e04603100f407000400004024818942103298215480b481e2a0341e02c0da50445802d00031101041a44a1030050045038903181c9088295840004103409650303a0110b0300d19082501d250318a40d448004000565a019a40449546a41c6040c00014101950203034172a000e010114051006900c42c440925008011548056030310004a988d615640c0051541b594000c0c041e6050a02584d0f0107103034046003440a4401f0f40b5085a0708510750340312340d51040c400d480380d0003031250850000d040001c1c030441c820400c160034901500380811282c092590305801c00200800012001581031821300208016112 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 404567652 1250 404566402 404566417
    0x4050d06090206091207091b23070606090c0f031104030623041a0105060403080301061b05060702031b0109230a060614030d141603050f040b0c0708060408 68
    0x340001d0120880c00401c071103204400e20903810040004500d05045000a803e60031185045020845500c60107034403004020034204003070011303c3e04080340100ca4030344180000d030b10072020010b501e0520103903215415900598001035042e075680c0d800342141c9400498001110040b46000c1060708205000c0703d2081c081c90001919043d5141d510241180b13003024046074603180706c20707001064541498207025007600a5034802c12622420000956410328a00356415694003122240c110303805d1910868070f03480c410381d1070b21590f001e00040a01240042c02841d00502c180c0e0702441c2d0f500d1991030807010a0741441d0303151603140c7c54440b4880200b0080424009011840203200341c0c0d22942c44040703486c0543c0c02c40c001d46014540078002402c1100d500c460b4180c0c070000d40607903040c282d01120588607003140c0e41c0200c481060800014800702c11030985440c11921070300740b00c3d0510444511808880e00641c0000c0d2080b10001044e101203403040100a0007000800c2c0104840c3c5466a100c0700140140c42 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 404568902 1250 404567652 404567663
    0x40312090c090b01022802012007230409030906031d06010603051f0f0501111504080318010f05041e030e09040c05090a0b0108150d08030903090307080d1404050d 71
    0x24000440e172007403103512404200c1030b80c181403001025000d05500c1d0100d2808901203500d4025104447d89100481d030241c209000c0178044141c50810350565000c17105200401d801401140e80403161b4941c4901034520b402075440c608014101000a011220800d107201400380d00c81130760700041500015880d0660302c080c0b42c0450306448034401c250307440389020741c01e8500c0c500c2c107100800e0540e8100c04810450308241d9880054a1041000170380302c0c501691032002c000040f400203008680440029504041c1183c01259140c01c0e1850702c40c00c4a2034822542e240c2500c1e9002d000522495141c0d4070403220000c0c25024a00304641d50140c144031f41c40d229a80610110301c000360074444043d007480300a0101a1007200380385842e40480c1c00070210f50858030b011400f00400b15070504c440b203004440b0180b010304500d041400c1c680300c08100d604014a030b0a400c0c07104001c07c0304192014011240284200d400900540300760410240c03110403807500d0890840b100780001c02240d690380108078256504030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 404570152 1250 404568902 404568911
    0x9131a09011113030809030f0a060219140702010e13090f022404150e060309010917040b0a050c0f0a0302060a0c0201020a0e04180c0b040509010e04050c12150708040312090c09 77
    0x1a01023401c00e00c902846c00a18000d20700d0000c2403003084d400400b5085110410310300890900401604c918526501040d2031507024440e0000550059040c0d1118000060400124000e02d0200f03d082d503608600c129005000340300804218100510010000300c42c00c03140c1d905250413110703015500e00803841881a5190001a0320708681c0c0620170a07090650b000d0038266503464003408d01c5028101400c2d0450b00407207110300c8e81e00e48076004020344050b5005600c086107480b0325039500f1100c681041c6889038490144030011a6490010810b2441c07040c401d401521251a2058240c4100c40b0882d08110959004118210403143d10a1200c0b00980040740d0000e004500410b81c5105043c508000600c5400800004203a0103d840e014008451007103a0f9004940e0721018102e9650209513802006644500c10b4158a4984500081c3c6444040c5088400c0020b204051440c0b03040260f400714040707520403090005140e4090301ca0602a9425881800b03510706995611041c18104d02c14540c1040d40d4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 404571402 1250 404570152 404570167
    0x5030f0307031e3b0a0b040501030903140a08010501020d1704081c05090303190e0a03080603101b12200c030f0310051807090509131a090111130308 65
    0x1130700c05040c00d24850500c402224840300100c0540c000360000c000d85a21402440c91051070141c105c4410355030200d4400d41407614100054002e004c90450031000d00c1200015101203030345110241540c01016600d08000d545003500180c140007106c1d452004010040c0c03040b42c62907074042c6046421035804031580c0c2e03890451108220720b1a802c0e8402c22015400e14060006425000000e94040c140d4440b01d4a00c0e82c003a84039000440350100c2100750160406510034020900406410764481c001500742e48200800c0b03801c1e80101e502c1416894208094850500d104603408004442d00701c0341c0701400c2100440c41c104a41030030480003031050306860009030440000c00706100307807011303034020000d841c0e1a4240a0104d00c1e9207500c500a1078007035146d01d41e16980440482d420b440c0a10b59075103520b00b2180c01d04060100c0035000900e4811207248282540c070029141c40003026407061004049803007030030031050190941e0f00f200e000e210300503403c0c00040c0c1c15100501c10300040320303400b9074801da85001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 404572652 1250 404571402 404571407
    0x4030f021216060801050d030e0f060702090703290d1106040801060807030b0901021207030b0a0509071d0f0f040213050d0b011a0a092c01090605030f0307031e 70
    0x4091005840c0500e40505a02e02600e402e80c03820b80b1100d884000240c1e0f2542d003413040056801e103010700003a400385881e481c40c0c10060307a01480c242018011714508038054000c208685016075210b80000d5681d00da118010a000303500528188808040c1e003034a0140c8000200f20301c0f8500302c09081c050013203051842c190356144c2160b0081403a40003d12000c0c5d0b643c2031161300c90403144402d95684441000003004840c041c400c556030303c2900c56460b01543c03900f410480083c21240c0010360409400c2c0c1002c992580e907125210312855440c1c0e184409421330035130112200039600d082c64018001a104000303196218454040145420780b80140c9910307010314050050340c03140e406181c0208e0f481d03802e001841608407180c1c2c160303080469800c999207074143e000e40305407180040081c0003c00300c41080c802c00500040100404428840403034085103c1c207144402c5400030703030000e1110340e81c0380303403c000a0505211441c043c10914004d10b050440f40c0c1c6000d01035156049282c401e480600499491660 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 404573902 1250 404572652 404572669
    0xc0e06010306030606082a0901030f170f0322050619201201060206090601050d031808010b0a05010206040b06090c0403051b120a031709070503100c2304030f02 70
    0x541080b41404211b0340c403089a03490746110922510302d200b1200050071810108101c132a4041d0016000310741c103030f01e0354032480e1307a1384800901290804500c4650100364032000c0007608880441c01100f036941e050000d0500f401e0040d4040d01d00c22440140c400b1404120301040c0356a01042442589000300c1403501540c0003020710f56162a0080c0d000301609540420321800382c801644032604c8000300c1c1e62211420303641c41c0c10442e1141d22640c003903c0140301c1d901f003040010101502c641050212885189a0141c10320095007003180c040e1b55500d24400c080c904194003400906007800078104070b00703141d114240301240c0107160600038080300c00400d0500312110100c60055401c50182e6a0101070340741c0c6100e0014181c0001031180d03000400c090311188c404140c00d803403240e058641000c551640030341c0300710008000780308a00d64003030684002400d441c107001e8002003048940c00040ca00002e2080a084a0891584058010001d6000400e000b945008440690740c10007001c000c1010f4603c0001e1048 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 404575152 1250 404573902 404573909
    0x304080a05010f14090d1209020909060703061a0f18061b0607030c0512220c0305100605031005090a06061203030509010b0a0923041208010609030c0e06010306 70
    0x51041458100a1081c1903002290030398540707409100c0c55040c800200c05514054a124889401c00b10b260b05a4500445c00000207a0b0310400200d0b40c015076400254218501701e03902c0302590002020400c150740d2512400001e85041da1115942040c103005030000c0c0e02401c2ca080d0081c6d0b40000b03201401c010360340e40a11403080018901c640d40d2146062005002d03540b041400e01c507114490109415600a0103000e101c450150789a40c1090382e114584030319910060070082d003a2800d144d0440500311003102c141174440c003d2000c0c060040c950718000303140030b40003220700c9029840c0402c107000aa80110708104005120390010075152294501c20341040d61210004040398903003400002e55005010203811014004d4030104050b40e1010701c014203a621418005601c4480420284800b1401e5806500201e0201548a04480c120b1102148c14001074405450f030706c4110151080c12a4006513640c050030b030342d1511711826842d5503074001d8400b43c0ca000d90344d00056210f000400d181d10940c01180117 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 404576402 1250 404575152 404575169
    0x90a0f06060906080d12020307120b040608010203091b0f210f011a040b04050408030612010b03101407022a040e071e060503060a050d08070605070f09080d02070501030e0304 76
    0x26030350380c13010785550b075035100008000305040048408202d105842030b28441c0c005a2200044a0780451400008214060440745d110b942e40c080403a41c1c01c824405544100078040081070301341408900e8200500548010a01c130307440002c26608075469110409000d00d890294444041803c01d242508024800c0a0b42110350300c0c00d4081340030702c500e1700004809001c058408104d90740c5500148416100200c80c043c081c1c40d010008100c490400251140324842c1800c0001400503800300082e04049942c1100403000352110b020f80c81e1800030210045c1c00107101c0c0000c103103800c5144026054083c080e070400c20301c100c5501c401d814949481e00030405840c02c0382d041c0c407103c81d203900a481d0740c22000c1c0755003400c1e005c0040c03011441c240200c00712401504001c00c1141e401d4a0402084031900e0584012103400074203212190001d036840c02031500581d429290382960342803950000300581e95a600050199004114102006801041040950704203182c04100b440c5030b141400d19510031a8043c2d880d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 404577652 1250 404576402 404576411
    0x12120a03020c10050f16031404080d06030b04080403020907080103050c0d0f02031609050c0a020a11221a0f0612040c050d050102030105040b180a09031b11030f0303090a0f060609 78
    0x442031400c1c60b640e07201d880c050041446006e12207104404442241c2e401848201020021034003082c00701c0060184166030704e1000c6805030300d0742c1d0b030402d903c442518202c5d4014404641401145007682d042d0f0380c040c0041c90111074940c03444c1c40311030b03881d80800140e43c024501800f5071428442d0b54840700b0a0980c0107021a20000343da4001401504218400c0c420760900d400d0210300c9407a0681c00310381c20840c07a90300400065941d51a003029056218803450382c080161505200054442805001e00c481c9401000034940c8048000d41801804807500c0c0d40b1904c1d10205081003135a1740010f464100c041c0b0203ca2101d03039101e190a010070030f9140c001c00c0c3c1c85494215040200070054006606a403001d46041c003840e00d260003440b00c90a42c0004407c5585180c00c0007074035405895010b402070324020b2824a8035079080c001d00042d140a006026a1200c0340c5545c03002940c14100303d00011001010029443d42c9016041280c036115114401882d20300540540c100703008041d0816000f60028240802 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 404578902 1250 404577652 404577661
    0x16060804020a0501030b01020a02062116090503070f0b160b0c0405040b0603040c1a13060804110a08030f071b0608090d02030403080307050c1507090512120a03020c1005 74
    0x4141000454049104034a803500200f4194400d0068198554040e002000c41581c10740c20082c02c1c0d04407050741c0c4501001d240c503000028071104922805520700000301100320703082c2c410081c154000d5400c000d000e43d002034010051400c001880341d04840c2d40400040d101c0d00c1242041c2e055401e07105001d00074481c5481804801c0301041c0c002c4c802c07503e08460402100c0f40c42424800300340402c070b030f002e0000340b400d903c10488038190b090580700d002d05d8101d1017407500d40025000c076021b01c2227400240001c0d001404001c2000000189001640021101d1074512482c1c401c13203e03903d2050003296034210002050355420012000c0f102c501d004a0000d07680b091a8031090028482c038001c98141c0e040384515908a40740900110483c0c0c02d41380c0005c2c0c1e6501d15662194150341581c0102c00c14011803051400b0303030f8056040c40706614010540f0365521040c00385800b007080116450b507103042e440f41c2c1214040301c88420032242115401c4085080150300c40500f03041903170030403410002d98071981c5d04040811 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 404580152 1250 404578902 404578907
    0x30e0312040807050f060d0203040201020a0b0a140702010504231203090a11100215340201060605090a09180c080709050c04051804051c030f0605011b141606 69
    0x704240c42c91001250001940c0314100014420360407007a540040c020007035a41c2e116010f4008581c0680180101c861580f200c1c0d90300350108800710b4680000c40e0f940c005002507a21361640303d6800010920007404203003015150785251070604c0ba80c0c20340e08521810708d180d031403609006448441c62194440d40e141d151140d4103a4030799442e402d040398440449149864245448600c1b0549038070203030b0081c056186810840700c6684e801418880720320586000c040d000f1119a890440d000c1c06d00e0407204041c21989002a0070f403411a00881c0074000c0c180302070780c01c61b210360302200304413000c14501240c0c1e0031080f41500401100484082c20018580b017010030703003000c00a4030100b2600010410000d035918034245070083d0145008041d4080d07810741d020700c510a0401030a980042c0550142c0340c85400b0714042c590007014120341070300407030340b40e104178440e2400c0751050f18001c207020b003080038001c001c2a4070640011150b0700000c102c0b00c1703201200c0c000010100000e0203c240260b0f80e90504a4035808007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 404581402 1250 404580152 404580157
    0xb0a0203040f05040908030109021c020f0a020d1b0b1b0f120f01030f062406090812040e0c0a0915050d050a0902090c0f07050105070504060207141c030e0312 69
    0x2040b648012000c030028440c1094441d180b0103a4000c0c0803103003942d00344049480694418621440c083c1110010529099030605c000c0c40e00d6019654559130b00c4100007030203410600c00808280601290807a000340190300003441901c8650b101000c1030f51946e0f05010720f10300e041d00401c880d00d06c0078003041d60114501604000c1581075403025141c0829521801214000719007400b000b01103407514084403000a8150308142e074003490345840b041c03410400202128900d80964000000220f400504109914041c072542c06040310340392400389064207114074446000030103406242c41680004480c44264816000e220145c06240b10400701e000d10001c0050250304100142c00070702e45800b0106030100b200384101c25a10340c2c05082c3e80c031a551800841115a0403058042d41c26820400c09000047e10a00c12141300350300740d4840b139803220b0a1180c000d2525a41c0d8001407017109950049900540d07409000b11206070f040c4d0050014a200307494212048081189040e030548207903d11461008a400b02 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 404582652 1250 404581402 404581409
    0x7030b010c15050f01080615091306052406090d2409030e010f0203070f15020715050a0b100c0b06210a020f010207181d12210906060d05070b0a020304 66
    0x11a16405c1c0d0b04c840c4156103070102074820101e80c04081d0210065410060981c60b0304c0010500701032130315241038a6803800d540c0111003994042208540600c1c0003101381c807200216640c1500c0240c00c03c0422030100d07600c42c00d40d0381c0203001c2c901480d5082d00c0c408549210001302042c6c0c0201440342c2e9440b0326003c2c0c140d86549108a001c9580d188a0300740c807034400010b82d07491580244c09503ca000194030b40748a00c010301c402e18084540c080014101040b40c40034845401d031184580010503140001050b0102e0b10404000ca00c41e00c188806d40038006e45c05000a24010341110f0910710548a80d4006001c0c2c42401c4001d5090b0041601300c445201004554040030074000c1e545451020b03150300049845400038000c02c0c0d600140e100303521600c2c0d10941d01905d10203810b0380900c03942c0c0301c03101d40c03551601d08a1010b034480c950000800c820100d0140c80c41c00790600f61024410102d061400ca442d4070b400c402413010303002e507a003154039405100041100c84000e050041c0c8180d558102c60f00001d440303500900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 404583902 1250 404582652 404582671
    0x2010207051816020111070f120c20060d0f1505041e09050a020301020c0d1403010303080f100312181a040506130302030615100905060307030b010c1505 67
    0x1840091103060911001030070000e1600c441080b5a03035040d80c6510590001803d100310365071119030b8000b00c0c082c0001054a80d00410b071541b240944d901c0c0808542c0d4882c0c81d03100811100b1803550b80015000e0305411042181103140c00c0d541404000421803a000f001861200c09003400e03012a40804280e1290a0071040c485503c04100c0d10b510601c025a240b40b00d02c0d000074050741104100c030000342c0e4000000a84200c09948903804581c00080c2079800c0309840e4811604512100d4021070b4100c0c1e04190a031380c00c00d41043c00c43d0314545015000c41e100805449441082d90006034841252604007009581e208510030150740284c3c100400c1314030010041000e002ea407917804140c03904a880210b5211105141840c5010700b00b030240211904080c0b0007142c10042c030364000c401650b080c40510722a01007100201d84014500080056030100300407010b0034818034a070240065101c0380102c030751103441d034200403038114a07400c012079031582142409010322512a124156144150304114021080381 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 404585152 1250 404583902 404583913
    0x91011030610030c02060a150b18011101060305030d0c12060b0c0c0d020904030e0102070e0108030304060f0b130b0d050f01241d0411091e010b0403110f1c0b04020102 73
    0x2c0055003101c40100540000d6031018001651906181c0c1260783d10342501c0c540000758554400300942280c0003072100c1c0a184401d0f000d202c190707585c40b0030a9168a1488d0300280101444c54071840e4584c1700b59a40c0640b010741b6040b00138902030040316010104228904100b1440303950304001c4945400c1a0b14009103402001c161000314500700910010540c0c00914608062b11542d40c156000c4804003072460650003229000211010b189454900174015800615503038902450940d003120041c0d200310f0050381c40c0c01a1a45c039512560402100c80b0390144001810901c00390000d4914800490004d140d84110602d0b640760300300641000c1240d201009050100b845458101c01c1c2800b540c0c0a52510b0701501c000340180c03180580074007a0400c0c01000b20303086594041000c40d29041c000c81d00722403864541300d05110450511000316005284101003641440c2c1141e43e01091000e02990041c4506070711071304840c040d601c1c042d1480c2c03d43c840c00480059500d03035203048048030800320780a9026002e0f1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 404586402 1250 404585152 404585179
    0x30e060601210f0b030f010504031205070f0c06110f2124010e090103030807090609180e1002070c1e03080d0f06030c08030403060b06070305120910110306 68
    0x903544050084450381d0140d1080200c0b80d00190050008800c4040307040c1d100c1c440c0120940b03050084000181040c000802e9901c1d040c140640003140b01400b104810b03240504104a0590010008030600a0b6140c0034042c90601e0804401403c00c0b40c0c0010f44910f000550300c11240103a20007401c80c00303c4804411380076190400a0701000004a602c403412074200c8607084550310003842c286541d0001410940101c400a10106420071000d80044011506000c00d0101298000a0a0000b804240b800070201410001143c4d2020401c0700c4030712071607458010b49840c6550901a141c1c0c00d54480f0002c54885c0e050342881390500800c0d2060662000e01032001990340804035401a090301d0704034910918024001110100425400405040e8550b480d04003200094500302c9000040a01000440d1130ba400c40c04c01e2011906000e02c0c06108036402c205140020350480140c501c40100010201019603c0c02d0b8003e0801e035445101111251801c510042d000c811000514001c03001582c114000c06034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 404587652 1250 404586402 404586407
    0x20c03070305060f0a0e07030f03020c040b0a060c05030c010c09051509010f0804051905100c090f0b1b03040b04140f0d06050604020715020c01051003200a0302030d030e060601 77
    0x9060002802c42c1d004000015000c1c2c0300c224469410041480c0000b400501000401c1d0505c0c14540040b100d040c0c02c07615100506074100200785c18100116420031000c4031f200c00249481d9842d1060740244401c00800006000c0144181c94089100b000240460748420100030907810130350003113501c18080920021108401001514101141030315942c0004004010581e2960001031080f5054840d60400d461048044d10090541600c14030043c0701841c010200380060ba40800e041004102d40070508000c80718111600c0c0c0300300c40c01242016550544000c000030060715044885149200000300000c03a00c0d40341c00140308841c01512401c88901260701013044900282c03100c0e95101c030911460401190300380d44001e40004000700b0045c9004c5c0e0303541e509a103841e20100c03040c03642c80d404650414603d50a008640e8002e0a01400e00d00944c20b55448410241c2000e41001322030b0a1880b4400ba151511050b200145070000c0848501c201c00c2d2100402600503940308100e18001e0348041001c550 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 404588902 1250 404587652 404587663
    0x70b030702030f030606091c20090a0b030102040e01060c06060b120601031e09030e19150809010603020d08030a0c0e010918153003081f08010e0d020c03 67
    0x910380e4051440d082034a5040a16500043c0071241d1080007008240000d50702c0448a1023045124000071501d41d046017001e50703c01400300020b00001c1c00042c1705081554814a405500245480001401660b0080400d009014079004611413419080004c1760381034010101982d81ea10403c01840016114445003060340140c84d1034034400c2010074041110b0f50301980281d620300702c020550082005019040b5002d40c1c5003c84203a0204071845403c210900f44140c224100c807138108080f03040300d4039240704074500c000c15145020402c001d14000c902210002e402850040d074005094004280007410511003a0303006803802e00c1660320f404402c1c40340600038403804505100507140c010015151180703d1215205039480307012400da030f5811809907030980c05a4400074200364800491002c445e00014014540f024010086802c40c2001c85400079a0201c1e1055000c2e400d69542c1a0001234200c0d44111200e10b0340140d0440d50900070783c2480c0001c0020000340b0107180794210b50721400a10300703250f02c03035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 404590152 1250 404588902 404588911
    0x21b010c09051008040f050105070507060605030c030a030809120a111e0d050c01060e0a091205070f02220507020d0f050301180b13020a170a0216020f0d05030d05040203070b03 77
    0x3d00c3d621500c443c41c000c41c1819802800f0f100c0c00110b0010603915a400c4450072552a004a80082044400d02c0303c070344109000307030500703034000c01142420070b0004e99500f00340d0900404020304100001c407444020701407009981ca81140c8162251500d620151840160f495128146d01c600250a0307091201030704412080e00480003d405012036030641155580d0024085036010740d00e8140000360700600035540391095072891070003e2084942d1400010400c840f2144008000e02032140d5004204041c0200c001d465044821036108510300c10b01c1210510440a003401462800b420000c06e82d40209000c034244485a4440302412800c14058485000a024a800c0382103c12000c0800354480c0d0b00c001105035000304404e0a46124451400582c0d0000c00c208002655866095182d03200e4200881c1d081405c100c1c0c05c0d0306110034030800c142503810707880b0081d02ca1000041444542c1e12111448500710b81c00034182c2c2d03640c0d42c0c2e40d40d03480d001d48420b0f01e003280a032103207000000d440b101364800e0300d016 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 404591402 1250 404590152 404590159
    0x3030b090f041a27060f0133030603240f11160303110a0c06050a050408071709130b0a06020f062a1b060a15030b0c040801021b010c0905 60
    0x3c40140c0c115024a9840041001d40d400301c6599000c1080840928940c200030812001054a494000c250040085041c0d010354404002010b40c0c14040b2034a04000d82001c1c01c1080088820030f0508007207014044070742c0301400e80301c4040036400e2a00901059402e540764041018801d0400401c2c06900716403402c0b1080715900810700005c45181c40068044103150f005c0c1c030b000715513144a00700f00705290340030064081c08501036401c2e15040081d140100707644010501401c12407441c140d00c1da03d03520b1043c82c0006140710384501d02203010780c0c10141510f10358000034000507450032846954034001c0c48102a03092148020310700010360644006800460b41c529040540f5480d180e0001e441c00c60400c0031001030384098803c00c011449840100504014060307120380f01349007101400802e0410170b01a045020701401c0c407444495449094020703204480c0e200300c20803003d03520101070f00094060b5420526895000140241c2030001a14034540c17581003800c000c005d22064610305544c20b072511b00c5190b03003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 404592652 1250 404591402 404591423
    0xb0c2d090d05030910081e040305030708100e0a02041701090309030206030903040317040303110f033708040302160e0703050402010509030703050601080c0a14060306030a0501020703030b090f04 85
    0x5103081141c107004070395100b0400c903410301c401e07000040d400c25201002c0200081003202000350440c412000c81541c0d14060742c01d6000d03401c1980b0b005041303100003019007041c42194808504001c0c40c04959500170100003400e0316140c201101d030b14001c2e5010384600a17201d01c100704401c150740300612546001980c161600042c041c503590a00c002504020030030039040c0000d010001c04548403407000421101494442e85c0e0391070a51030060562a891015444958810312030a0320441e000000c41d00350300c03600700342ca0b2082c40e580400c11146ea0b81440700010021003200424072440d810034a8140a140b0907000c1d554644e50b00701c045003c641c15407049030500801c01000c55030b428003a070701c0f0541260061421615141e0f00401080c40d1410715442208d640d4803a02c01000441710034413200840351811101046110314201000c00214103c8040382c1c856400000402d0003581e080100100090f0b11400943d21000c1c10300700600141781d114141401000850001846150604c0303010744201d9026481d0070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 404593902 1250 404592652 404592667
    0x5040e0105220903030603140f060c09040b120102040f0b0a1d011407050f0c0102010207050c040c0203090d0c0f05010504050102150705090d0c080c09160e0d0b0c2d 72
    0x20845002c102c14802420648144940e6075495000f0101c40502039100815a03d1640c40c000381d160460542d9803074035401c880c0755014000004521a07030480c0d000050136032200c140e07400040040a145001b943d0103000282003114401042d00a00700b101d0280101c0d184840c3e460742c0384000f9200301003100d00065941802030541d00358802c150f441034001072400c11510009a140701c43e4550200c1c50540f000d511180b0704810858080042000410080c4000d40c1004200ea6800d540d4840f140034652141d5180c484000031517108005171215000b0040900442007001d0402c00d4240c582401a01c0d240101e0b8a400325855000c1c504607012680c0690003004405085000103004440152810003085401c0040c1c3d06d2a82d21038001c600038a008650441c02c0d1880c05021924001ca23545d01280135418920400000d6203600c8081500c004140c140040d00740050f1340054a04094508001c01c15458901032111481100c8040c100181c0603107800041c8034030038501030715500c03080707294103015041c00c01480 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 404595152 1250 404593902 404593909
    0x40b0a140109050403090f03030e1009140d0f020603070f0f020c0114090409080406030c20030313050109020303040e06090a09170c033a050106020a020120250605040e0105 75
    0x1a44030b4003a1620840c0c0315160405101607d0f000d620950000302842da1345403540c500f44091507084440b504000807000d1605000b45c210340f000507081c5200c2c1900d40071080c03d218201e840b207680701d540140034598a24044c1070280c407070000c003108040090b4005085143c81c9000180385841c241050312203420702c803100461012664030054003548c12986550050340010440d201400c051305440c0c4000c03540e0500b2045c010000c0050310280f0b00c03179600923051844541408800c490b0010049130032103580300d5060910f039025100d0090300a400d8440090002150340b0241130300d41c01140103c418a1054032074000304070580300c00280250000d070b4903884c00584e03c0303c148000c00c01082c0040940e810701d0584e020f0351000845c100d0083ea082c1e08503140301d0b000c1c0018058040311020f41640100074550602d04001e69a9004800013814840000f1040520f11800d220000b2201c251000f1900d8401034404500d034522040c819042e04214814070115205019009880c1501c2020080030310607860310040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 404596402 1250 404595152 404595161
    0x3030a231c0c110708070815060a121e050105010906120c14010903020901031127040f020609040c0905011b0f0b0a0e060c0c2118030309030d0206040b0a140109 70
    0x282c2c082c843c1c002066003480105020f0f400040a02a01420200d032504180718204075201d40d4400020a5000030030805a40300300d8407034143d40f0203a01424001c4158036018440c003082c2020708241c076540c02100000c000c015003001781a06e0703a400c01030044603994a43d04000c404102801840810705a005000d45a9051040f0700c0c2d8100525254040030350b03e4000c100480d40030307041036640c2c04001d4182030361030601c4400e840400008110382c010081c0700c11f10028001c10040c0c0010910343c40f810b110001d5585000960b8425900108204110f0781c46501c0a4140d020512840f8086414034208228a41c40110600035054100100207403002c05503650500142004000002c459910003031882844410440c05210b025140310040d5035122044401d460812101e00b000a021102000440c0080b9124250380842c5000d0004060420203040024194041d0000c41505440b81126030390740f071030380000c2d014003e0340511392180540c3c0391061154280d03031490544542c4942e44038010851181954030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 404597652 1250 404596402 404596421
    0x9120c0a0509190e010605130e070509040203030a110307141501051e040902190f060806030d120207050f371a04030c020306042405011a090f03030a231c 67
    0x81c90031f4490000a125202c00700801c60021364640342604410803c0013140c1c090042107800c03414901d890340c0042d60300e2007648408810820301c9020f070481d00308100b041d5041d040c1d120420502c6030f400c0c121029a1546400500c2d2120380e00072000262606041c51501e11744000300111640040d144020710000d0800110102e07002002d044004003c280ba2001040280024000c062103c3c0e00e844401413003c140a00b841e031003030308540d1080301d0322034000710f8005056021200158590304142040c90a0103181080c090441c080e21504199440c0c1d107116078403078100c02020012500c088400c1100c9074010120b0004e00f06001c1d8120344d2540d010340603040d80e0092081c074000c070501e1401d50210741400801d890480c0d0408031101c443c400c80c02c00342104407000058850811080d03142031445c00040c100003a1100ca41075000407038040700e03290b4020145401314007030100c07a0782c0c08002e8001410005689281100e6280030b014060202100c034044580c98000900c0303403000e801d0644152401081c0241 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 404598902 1250 404597652 404597681
    0x501180b010513080f10050613050624040611011a010c020d05030c0307020f0103180b070504080303130210080f0106052a0604050105060307050904120509120c0a050919 74
    0x41815856a000c140490107000000c0160444203442c0754114a0041415980c240d0305047c101088282c0c1c488a00c50000061008404100c944620010401c0415800122105501065121031313003a14500c004004450365903807a640e600b0310079000d0b1800c03549481c40c0340f425880310f802d141100e98411301100501a0004042e4207900601e44c0d40d00d8a141d001c400c1011075a0000700d151000c1d46046030804001c140c2c00c0c00c0611205c810b05000c49006e8442c2c010041c800501c500100e500188501c0a80d4051301024044941e24200000d0300d035003d03003410310308038419002001c216140d00c5c41200408d025241011510740030ba402e03c04c05580b0f23074002d0300303100910309507420262400c1c0c25107800f0082031400f00006031800f42094204542552030051003036000b035002620421a41d11441003e42d4000c0e009044462407008020742143d051098005142e030000c0b60f5207801d58605800301e0a40c40c0e400049808404460341c0d4018488440804c4500d25075005c0300b40d00e9081840000c0d001215060101d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 404600152 1250 404598902 404598907
    0x30b0603241501110c0d111c1e080d0e0a0c030602070209011a040303050c070306050106020d030e07120f02030c1012050117030702061e120412030501180b0105 70
    0x282440640000086421580107100c040c8440c60780c1d07088000906220070f1800d5400c400302103107019917a4000040396070060030449166030030300c549010a400c071554010036807010806034500c0b182c9585980c1805403150b086031108282e8001591003820110b5601c1004503040034008903032079000341503503d043d444c030340070b46d0313448000150070403059038007035840f072a00143c5510040c0140008260142c100c13a940c40c609840c01d04070046a402542c2c1102da0501d00191b444000c600503504110840c0d0000b4155402c1400206650b078007c074444880346040e640810840058106a50760b071912882040702010b207202c01c86000c1a624022012420f0001e0100c07450a4480710100b40d02c0e804001c03201c0e0004002d68000b03054904903020352401070002004100d40c45e005000099242d12468074024855440012039510100c204410107545000120b6100e403500144401c03a65104012a0304846048c1c1e04e0101c580c40301d0280c420241651420f80c000407110310044000c0e801003034405406030500106 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 404601402 1250 404600152 404600173
    0x308040302070e01031a130b0109020f090411120a0515010c02180c04090b0a05090c1b0f100b030d0906030c030e07080d02010e03071a1003050a0b090d18030b0603 71
    0x54030780b18002d40c0701b440b41da6903204030b4018981500d90007800c2040c0c0d1208801c0500701007106050684e05440c43c403030b0b0040c2c2d1001200100c043d02c4c401c05010710780050130308048224941132140a020002a03014440c101682c912aa00303048076001c803000c001d4100d000075000d00f103500c0b494000146903c003070300c40c0c460503003e00a001c0c91904125010060110005800e0110344000c1c081d85400c4041901e80744052420003002903074001c0001e1216000c0702002c1111903040724a00d452801c030480e1442130f00d0494005507002502e50082d07101c8164058140015600a4200021498450744465a81d80c261b58280001203000e0b150f42800d02e0205529411700404281c1d050210100510945009055000280c6006405d40d1003a00341682141c01c02e00c164008a610020000900b40030303030303403005802c0d0f407a0060b800098020780c02c01b030000d00c5000c1c45002000356085900d40200d00300802c070344059560071011980c181141901000e985441902000090009000d03d6003001000301a50030b10342d030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 404602652 1250 404601402 404601419
    0xa08030d021c292e0c020a030b0f010b090607110406080114060411040503070308160b01030f060e0706020309130603120207060f032003090c091e010b0a0804030804030207 75
    0x140f0300c014942c6160f10b03601c410701c3c010f403814640c007800640f549298203410720452070f041101c3c071100400c510100060b81c0140c0b031194426107180395005000f804095106c1c141141d81007011190010081002c100105d500d90790941503d600e41801810a031401000e85e45036408405441002e54000741c40705070204142d0320078080c02e6640c00c1120021083e9203400c00030003040c1c0e425504a041c420808000510554a02040c070400782c03900801e4280d5101c00d220b094003154011044043c081d03500b000004000c001440c00148c0440340150b0041c4103442502c404540c88541c2131003040d000d80d004000c003182d00e0505000d40c0a03242c1140c0d60025007a07980c2d8403000c907080c1c6c00b10000c00041c0c004010600c41d20741c01038086031441c0024a0104104003d00503500c1c01c07001c0060040c10640c03c0800001d103c0d00081010302d9180c80701808000c4607051411300381c03000818201225100300c1001e00042400350700340c025540550042e82d10011292030343c1d2800c0c0e442100141c001d0702140143c40c8080b44510 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 404603902 1250 404602652 404602661
    0xa080d0207020a031e02090c040501140a211a030601080c01031a060301030638011202090406081b0402071e08280e060306100522080c0109050a08030d021c 68
    0x69980b8170104440c04d10303204221480d440140740c0c070b8100c0014041072020f030340d000a0444c8010910711040f5601c3d440c445003034814040002d2110f440b01c01542d031019a50300c03981c0101a04c601199000300c40440c0080815441326030034051510b00b0b0740114549085513110340c000b0b10074003c1c0f1a11044110351000023044255000b44c006a6455498200420f0300c0c24100700085a941c075041100010200340d20101041c41c2c0c610604a410410182c00c0542c2c101c07511740c1120380b141402481044915a58103116449100d0403c030301c400c07003003020b40e1040c8038182030007143d807460b0340031070031004842044035a110200b40298080d910044180000003642000328400741c001c5240758507150034144049002042c1440031168a4003036001807052110544400d1642400d40c505424040e0322500500452400910300c0c03001c0c022408224000014003010104580c030b80100280d03110b80344540c446c0140400340d019440303080c10540c0b0030808054030044d03a80c0504052103180d000d071042400705c8200401500c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 404605152 1250 404603902 404603933
    0x3071e050f0f2101080c040f06091506030e0304050306181c1706151c0e190c0e0613090201030908030c0910140d05181e06090a080d0207020a03 63
    0x1c4200142080d00f1203031654803a0940003426042c0c0e0803e43c10030401c1501d034501011414022600c50200d40c144442c0d6401401c0680b038060300821404205800000f0044106d00c10340d03020901d481420748050001000b15029a00080d00501c2c40341c4684800c9040c0744d00c47c0100340b140313010f04d41e05141012885450612103048135551154040c8000690880402002c1d0516114235132454440a0b5900742c841558213204c2d94003e0380000c041000003110242c001d1583d03400150041c002d0005020f15101c0380821854082c2c60303031360000d5880c0c044841603000f041e0380d240c2c0e11130b01206040310080c800d6007180700c07031030b1040c90b0100349000c4a54400031190001da60320320488501048150040c14075203000ca0041c0000d107011140c0c0b40c081d0030980210300c0341800d0203102c203441d0f80001d80c803e6030011060780e840b5941030840e0380121080b030440c400700c415002290043c0c010074021030a200710001c0c04003555500b102c91503107071540400c2420000c0d44941d00407030b0007100b00d500000110f1020f9940c81c201 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 404606402 1250 404605152 404605177
    0x301306050c010c0207030c061107031509030e0f28050406030317130816020d05030315100e060322050d0203090301060501210504170324040203071e050f 67
    0x1140c45464805007903c0c0c10a1000003103620000c401c00c081015502c40b001125400d00f0714680c8071011100c128241200e03034001810f100c0c40041c00b011400256031040e00140d0181c0e075901c411b403120000f04402c44c0d500c50802c80d401203d1b0160225007005c51680e61408021010b003172400303199244040303030039100b04e580705501281c014000c048040e00905025588180303250720f0600ca1250903a14244e090003a24100c400c125011180c0c00215182e00200110300390f000b104503034031703850107104030b0000c0c904048116000f90640748a10010a010701221345009200405075801c41d070701c00340348402015540d01c00748038056140380294081130051007001d4010400d60302459951a45400b07150035030740c1681c005810000c0c2030601803545940340da01411203890820000c903036a211820896503000710500004070544001052205d28003641960028a960820070313410348102130070070081280021940040070031001c0341e5203001d51801c4100d007002c21005050007801e02c011013030b00002d10380040040151 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 404607652 1250 404606402 404606407
    0x7061d072606091f0906110d060602120a030507140316030605031605042d0c02010f0506091602100e0606090105040606020a060506011e0e040e30130605 67
    0xe5a6030710501880e0a40e0000014451410619403440c1d40b25001d40500c1d02090010a04101c1120550015005190000c03018441ea08841c10b405400742c0c083c51a00c01741c145030120001e4001c0c004188070b06112010415035091001c010801d60207054002c0181c01042048142d488060401c54080c500803424030118240104001d2405002c80c0d540d030304014400e03400401384048070500040000c06840060750081000d10078210780640e228100741d010b03080d12501031420480300441e5840390045252540c000d0092315074605694040720b0080e1422901305d10000001041c0800684c60850746620381e00c111000d0510307455040c000c88810b0039005069810140c00d0180134a005140300d070140c1030442d000c00c007003490200c0c003950300c64094000030a1541ca0354000f807916030180d501080d0601041003034000304260601c00900025481600a2181c0c1c60440d128401c81000901c9074100d130182d2103409040c3da982450090341051850751420051010892712011542400020b401042e06491301038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 404608902 1250 404607652 404607689
    0x406051008060a0807350712031407021c170c160b030603030a120603170a030f0b210307050a05060402010f020109120c0f21030e070b07061d07 63
    0x181c1081030f54000c10060348085002d12509043c4a44660031606d4070401110344880308010502d004107a04100030140600c0c0e01c0003e403004c5002c218001c2034443d075229040c24040c0909104035000341d03400603412100d8800303900a44c000c5e2840154015006001488070820802100d401e5680904940001c6170001840c404040c800021030101034404201140c0c21031406402103566401a40300881c1044500704c000c111078a401d5004801454022612603d038000108202900707911021103000001e1a08042c041184918851110014130040c51460351707503080f04031b401188807940050085800108a4040064020000c89a800d40300d01d000c0c0c40c0620301400090851310441c40400151390400c0640800940d5642d0001c1c00d100d450b08086882003064209143c82c0b0b045800000d0100c4100e040b8101c034004402150003000322141d8082c40b00c155050442c079120040783c032503510b9240c014049100003034219040700310321140d0b8a860342030302d2303940003e40d40c5010b40340e5002d480051181c040c00d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 404610152 1250 404608902 404608909
    0x17010603061802160b041b060c0b0c07050c011206260c03060f040303090309051e03010c050a0c0b0414070b0406260f06031609020d06090c1706040605100806 69
    0x5214201d1040c000710300b00303514144c040c007103144040c0c0000c02c100c610400240c2081141041c5011a040c079140d1940280e46500e0301500315607604401f5a40000c80e0400900007100340e100300ca500961000c003900e0040305100055414810030b80800d20350f01d407205000300c4c0001119120700030180c900840400041101130782c2d54100044403c18900a030040e03801c100400d00c0e01200d03907410960615000070342c0704182c282110209900c0e00100d40c404020a40c190303455403400300309980b00c0700c00c41c001c104101e0300480aa40c00d100302880f1001180d0040480e101003040384c02215400380c020882241c4a11440b027800c1d0900c03645400c1071210321001300d02444040c0c1e0140300480c1d030303400e5107440d03080640741c1c2000d0400b018001401a074456040e20300040032074500740b01c00e003d440010a400c0c0c1000f40c58503d810080d4000b010414506450200006048041802019072990907078031006003200c00c00f2134005802d50300800c42900152507100014060300c030100581040460341e81c075424942010703404c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 404611402 1250 404610152 404610179
    0x20a020a06050a0503040f0303090f061514010c031202070c0b0a020601090504081204061113080c090f1306090218060f03060c0f0a11010908070203060109020f07080a1701060306 78
    0x100200034041c003c058943d6041800c4a400c00e8000070b0000d140007182c58102c0283c510b441006240c0821042c40804102041e00442c0c41c0070503040040c129113031208504000e9441042120b400114100e1040300803d002d400b40c0740c1d10a1442d10701514100d40e940300c041c0307d41e10541c403012003041e0000ea45110540c7c144161030250520203c1409141850344804c84140510f103286540180c041c00460100b005650141c0940381c41d80340059110300014058000d0040c643c4689000c600840c802c030803143c9001030040c2e210f841d031164034032241e0700c80b00030302c1c0c0c850051248201c61090b5520901005a0707183c03440308a011490f520410380d02e20307004040c407841c11040070740a03000b44e02c01c01c01d00c038912a0308010703180c3d1030b15a141015140d00c00c0139011120b6141d40d01c4e9030301c155464900002c081c44510f40c000e14031980207504944060366511ba04504a01c201102c504040d07906000400c000b5030000010000d40300180362001d981c00304400e51208100c8280d2000c00800c0c1d41d4102044405a950324 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 404612652 1250 404611402 404611409
    0x7111c0c05160602030d0c030b150309010c080606030109050c07050a0b071b1101031e06090209040e0a0314090103020d05070c0309050118050f0607140105040b0f04110d0602040503010c020a020a 85
    0x440d40c0b00b180740000c040d40c0d80c01001d9001d58850f4440c01441440e5110368044031750b2100c018159981d00305080341c90b40c02c03503005845691155090000389280d1030b008140c0c690060b0005810301e89142e10300000034008210103400e00001510400c10840820710030090005028011840e0590505100c134015040d2250102c451229255008044000c948500c1041400610a00303020915821a20300240801c502189000606140000101d0041c1c4280c1c094a010002500c0410041403080c002c00e0b44d0356103180e80200010822401c10a420281c600942200d1806044c054100409581d0400c06d503102290540001001c1a4460b002e2546c00140704000f4102803d02d264a0440d0b0f5907407840c83d15450088900a44506561107100d071107040403a245c07280c000820344074500d480d08400c0d01900c0e041e50155000b4000d140070407020696000e03543d0023141d000729084085440c000602080341c80900040e40c80e03039401d110006161310203020341d007038100141d400360030741c04030a10402c11800141d42 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 404613902 1250 404612652 404612683
    0x50609090d03050907090e0c040f0501080601092d05060108010b0a090e19050907030309080d0516050708120c100605011b0f1a090d021507111c0c05 65
    0x14280004190041007103910000e00e440d000c100382e0740d2040c64602e40071695001e200042d19220240255a40114440380c03444004c440c188000802d0384070b15030a8540a004081e29030300080e0040044d90324941c00244801c0111301194405540f04400c21120420051180c07000e83c3c980007084059a4020200c40c00b600e0903501c031700e040424554000b804c1e0700060040b80350580c10280402ca200701000d4154a0700060a80140000c1c40c04800b010303100c0030103100031004139201f080e0100b800c600204024407000c0c0156200350a1100c1d0414001c0c00344007001c810740301c6004078280400e1a490600c0b0720703801c12135010f00803030303030784040c0d181d13543c42d000d91038802541c810308c0c101d41840310303030703846010180c20311031060300d03820104179a040c11105000ca11034010b054504600004002019221204d48640001c00540300784a4000300103a8070340d0f400c2254903040500302000541003a000d95000e940a02c0c14a04541c1e0f1070b240c04100440d071000341348180c800b0030400340f000b000b08a000c005c41d841c00d20195 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 404615152 1250 404613902 404613919
    0x1f09060b0102061510020c0a0801060e280c11061815090604141005010609140907020c121e0c100f090302061e130603150308030103080304050c06070303020a030506 72
    0x4c1d0660b140d590144a902d00c12020603030104200351080058490f006c00040581c40700d6650b0340340c5030f8000c100d0b81c8195500040300f080001c1e440201d442e10340540010410110003031500c1c800e51071b0010207068000c02c061000f010000010782004000192003001050883d001a0300080b162520700800003c048848901c4281040a5404007090850308180e0000510f0040542c0c445490305210350317180d08002c03052810b00001401940441e83c441110708059441c002068050244940d41034100d88040141e8414810489181000d43c590a05c0d0044d03501035840c0b07000f020800c030304154000c641d0b05440d42d2040005489c1441c24610401c101080303428208140c003009103019015101038403010b407040c070010480d072109819583c2816440107641050316600c020306c15401618030f20501401001910300400100c000025000c408240da810902407805c1d60b1a55450500c158402403040b10039008001034041d8989481c0c02500301c031403003601d0242c1c0307405c81400000c08844006102c5403141484 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 404616402 1250 404615152 404615161
    0x105010906140612070e030604060902090a0e0303060d02040f0f02040f050d031205040c0909050d080f01050d15020f042907080a032004060f0305361f09060b010206 72
    0x4420803207902685680302400c842d65100d20071303035206d6081030610790140140c40410040282c2c0340e015041c0c061084401030201c0e120701880d0401c171121964147e0a603442003001c1012032820346242c0103d64801400440c043d21008121803c4d0344800282407803058010405228690590205401500c010355072a00080140d440080c180c0001d4034800480030381d80c101050a00650040400c0501440c2c0d10034484810300c1c0c5042035132038050301c03280d5000900c0c44000c52420f40c2400c805504a070380040581c90700655a8541e10040c2e144000a02030070340c3d00300144111110b82402900091894104e0341c615100b6034691400844540d030103603804003a0400500c80001c3c0c0c8002a1007a240d10b40c90000f40880780c04103218402d08c80e944c02000040ac02180c002401507200c12900c4548445540912454031260718900c81c52007001111b2008045401d0790340000755440c1d90444034042d1600840b94840c1c40c40d282070903401007036800742000300d0715030300401305001c191701519984000c20f02c01051503182 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 404617652 1250 404616402 404616409
    0xb041505090a090611072a14180106020303090d05030402011d040b1503100f030210050a05041203090501090806040320031e0403110d080315060c0f010501090614 71
    0x42402128820545400410b0440556910a1800e194441420003c13120040211012504400e40403a030300d80701c10841d000100402c4a00d10b03e1600941a803158160030244611800e0045046040c1c0083c502080702201030a0011094004c00e400d802443d0340f4200424614100030000100c03409003e0308005000050340d02010446040f068038940c83c00080e40800005d01030701c4840c0702d281d80710168461042403070171100001c5005012445a00c0c512a5840c1c55004800a45110281d482211083c41c504010300401c01400004901e2500da0700c0c154449141d0701803924080025400560000000c0c0315a58000081601914050006088510742607400500c2500041c0f00d80b003245240c40d0580c082282c00304251500248460880200d1000c11020700b1210b40051009890204206000354074500b4204460a50240c018a41502d10380c0d41784180001c040c00e09803403a030003000410400302580c405000b400c10004c1900c001281c21b5140c14440429100302d508004000c2100320802040b50342c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 404618902 1250 404617652 404617691
    0x3050601050105180910050306071d03011107020f0414070f0f030e06071d060a080a0f050c0a051809010612150b1c020405060c0303070f05071e050a0c17010b04 70
    0x11000c17203507550182e444160304070a6101540c00960144220014040ca00d0340001c0702e001c0d08019000d582001d0044241003600342c41c150030303c0c1d00ca14401000a000541440103248441d480064030202e5000f005070f011980b180320407200e401c0003652010503000940e900280c00002c101041c5402d002108030b0040954807a14050403110901c460b03c2c95403c0c952403543d039640e0384514003c26540d116103c04401138595102290f003084440d14203441103102041510809010f9480c80c14060304000711808141c0d80d41d07004140d074484050303140b940300c0d065559030350071540601020f94400b00b40f407054101140580f1071100d1f0150700140c0c500b1050002d20891401d8900c484001043c01a6507040382603c44000c1c82287c211540003d0b001400300c404483c0000158003401c0789540d82c145445d0300000c1214036000d07071103005003130703841c401c11803102604144088900540520140c0d5081480d40d5200c049401c440d074040c0e8400242400401c2013900c2c00e00c225043c05200781c0e020301031a0b0300200f0281c51030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 404620152 1250 404618902 404618947
    0x302010e010f03110c0d021608070509041e0f02030105070905130f0e030301031103070b07080412060b210111030105030d20010f050103060c0e031c05120a0603050601050105 76
    0x408060070500d103e11a4000740f076620800703022180c2d01c5009040c0d890f218628500300201511070100c9505003508621000d8044034140c1014001090901080107800040584251209100800c058100f020045030007626503100340701200c00c00650348145804e44200510703c000340550244100010740360548141e6500400007800120b01440783d4258005040000602c0c0386448044004010440313200a2013001c0141281122903150361005031442912507400004e1201c482444100300d41e00d54103000b414040d1183c5d401003901241a008509548070b0340c01c1205c00d4041c0760413030858082080c400e214004000c002103a14542c10f00c0042030b41c816001d050760007040714401d0412107402c0103245240f45504400c009100e80c4403600c80c0302018010070302060b60014030707104104042038018031a1000c419005005410801c000080c14040078122101000c1408001c101d0501404125a00795105058034100020b0b20350131030800903c2c1c86416007019040c03003010031544d0400f85050b00380e4034a6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 404621402 1250 404620152 404620157
    0x9100902031e0906040b1f030611070b0112051c0507060b0d02180a0b0a030528020a0608010305150108190c0b1201090506031203150a091103180c0a0306050a090803130b070305010302010e01 83
    0x103080080001020f2f8880e04602604e41080c0e140086a072600303140080030268004d0f400c452059207980840d903020360a84c0c2824000c203030304200040c0003885a8000c4424100d0007085104034001a801089500300c0034420100c00c505607200f00b00c00120203100d06c0960300323820380b504c100a50559079115600e082003c1c0000c0900c9442c45046007596110318038600096000e0720195820303a4421001c2d041c00402e0000300c9241c022410220600d442e442074240c100c407070007801400740e05207004020f80041402c10041d0760b0203002007804100090410014000600800c1d108603e0390f26101c52581250b001401b03a0707110350044014014047d0020b01a40e0300990000c9182a10010210000b1221071141c3d03c800c101d64181a0200c94003d24003000d148550b2013080500c0010802540e213644541c04440c481c1d5015a42e642c0c1070001c510240d02942c0e000860200c00940300500c0e44400031160811600725204400b00340041c020400c065000c04e400045604062106505650020f410030000200c805d04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 404622652 1250 404621402 404621411
    0x80d05100603110714011d0f010c023c010e0703150203060d02060a020a06090c05030f0607021b0d0c171209030c0418060c0306080c09100902031e0906040b1f0306 71
    0x307410702980001c603d8004803602c04801f020442015480d0301c611103040c3c44035440d140880e12000d0002c6190f40c00100340320300340c500d52400381000c00076041460b000c43c2e0940c9284121160600004d21850340d2100e541c4004020329880e42c45c1601c2d101d209207a044003040e00502c03e1081e240c60f1015a2182c080d0304584c42d580b1248034110407480c280500c1c47c081c0020342003e03110018000300300144d1007550720540c150b034880d000c203044040c0e840406545c0e603401a440075a40305103141400004140d0058000c01410384080a5190402000080d41001c0148006010440501c003810082680d00d011000262401e110700f440c00030742c481c0c400f034140d00d0146881d010742c02d0100c0e00e04081ca054045d400131041183c004040f01c002d0050003140205903092041c40c048002c1031a0110503140b06010380322901200c00e04080c001006500b016100001e41c0041444120003200f000d215588541c0c00e0100501051510f4108070f01650005000c407003000901c1c040c0021400c1c0d0b448902c00c1501d800c0000400e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 404623902 1250 404622652 404622683
    0x903090a1e0b07020102190303050609060414060f030a0507080d0f0810120215070f05060a0b06042d0902031f060e241c0b01030e0a0b0403030207080d051006031107 72
    0x1f828041204030b15408080b44042200415400d90305c02c0c0d001d41e000303071a8542165983e0003801304030703880f6004d188000c0ca042d800180680c0b80c016031600ca203240c05001c0e940150700380e41c0d83c00d10b00009900601c02c40e401030f00103d142594071142c2c0034212210384c6406185400c003004900117010f40e6006080004104c00c01350700554441310079014003501400c904039a20415801c0c440c00c10201e448080ba1075000301c0c6e021501a107440d00445074401c00040c42e03e0300e491b103000380b8402d90800c6406020500c504115281098407400302c103d0f402415258005645c1b40741040c41d25281c80b1a6450308024159211400c0c000300b640300030070a01e0640309503502d000e0030181c0d000070f0950f0013040400300c1d0004400a9548111940d0414502d001d80604a0070320000700c2c1c40c0010b40c140c030040009800c140d40032545800204041030b03e43c540042c081c1c01e0040c9049156141c01807180c0c0710400030a034084e01d0f2000d200e07c120100541c0c90080aa900e001c00100d0150340074041d85210324100036103007905180008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 404625152 1250 404623902 404623907
    0x4030203040f0816140a0e151f08100f15020703020a0603090201021504050604080721030c1b03140d0f020408010606080a021207080703020c060903090a1e0b070201 72
    0xa80107025415401d88810f0b655110f2203a850800410b9010800191038001803a07040600c0740407010a8028a030050720b506040c03403000100c0000304041440c0902004800c16502d03a42d901048451001007400306040c05288042d00440c00500b880c2c0c10f12408100400504904101142c00d44950460260407c0d5002001324a024560f0b04040e5001102c1d04000602a805600c42c0b2801c40c070070b070269203012040300325506040c2c00c12a8098555040743c00000c0014030802c0040100d14890012001c000d114500600305012140402c000030a64a1079100306a941144940500f400340c1200804100e9640d0340090188000c901e44010015020540021141ca01c1e04945001c50440b07c0440d10740741c1d01c88419010341494400c90002c42d100002145590005001315200e011600100c1d120f0b0380c80740345003210400e80c018900c008166090125200359041407040e036004820141c021920b03250071400300400003441d40d2012040c650364011704180518894904821218080c50f41a240c0d0b0301030005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 404626402 1250 404625152 404625157
    0x4440307020a02120105150f031c021002160b25080c091f080106050403050304030326070309060c050408060c030709031a04030f0f05070605100815090c0d081204030203 74
    0x1e6004e004800c881880d007030154056882114046413003241c400b054424002c82c0030444000c1901a0400042c88040000600e80c1d071841c50901c0c411641030302180d1251108903041595929607504203003411384d083c03101c2c888010b80c10521319a500241080001d910900d1480119070303860501c020800002c0c001640700065442404020b48240c1d141e180c00121049000c2000d500070002c01c03000b400105425200e10207640540364042e00035031030582580c03400c0c1c0c0c24000503402c5480c1201a1583c0300720390941090280d00507141c50b2004545000c491819909880f00c4d08030690030090140000c01501400141c895000240200382d665030352201e0004650714403060700060004d44240c284d0b141e07010048086944a140250348410080d03a003894100c03030a184800b00070001400c00e02509011070400d91290350045080301c3c020000941d01d141440c01c083c442000c00144112140400008603824483c2c01e14081c1e0844040c0814600d55852924500546015080c3c4900103000241010b008104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 404627652 1250 404626402 404626423
    0xf100204180b01051c060e090a080409110706090302010b03120c0307021201020c1617010516050d1407020d0306050d050a0f0c030615080d020f0309011101020702090444030702 77
    0x1004680a60740e9040c176010b45420b00c0313200b8075488032030001024a000410005050307070b0700c00c600717900d42031401c0d64110203481d2600d035000030050200f00c03000008200d0700c5042c040901c45d170008603849148000701810031a08100303404281d80c0421124000300c40210440f904a941100d0f0300d10341c40036003006140280540d4000341c045124643c2c00d0410071840921640c01c9482900d01044100c4080b8071890a807281959800300b0a10800106c0c5007250146000c0c1003105042040014020310340b8201201e650416545c550150b00711280b803030482907150103618040c01081d96884080e140981e94190303110b010441c0500614070201d03119080051044240c4c0055400c02c0003400b0219241b410400321344d41c00e02c149441481000d8000d8100d034000b00e80c601c60101c1800145041c40c0c0b80c800103503200c041d0007144981a550800c00300c40140da80c1030220b40034500440b000301070769458031170b2006021040840108840780a08178442000c1c100007218040c1d1410310300d21900c07074442c48010ba142851202 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 404628902 1250 404627652 404627677
    0x3020d0204031109070c0309090e0f070e0a1116030e01050c12030106120b010e100c060f05040210020a051009021804050f010506010c0309050415050904050f100204180b0105 76
    0x41c00014400c4030b4890a0309600c003102c000c04203807549a000d440c450f00300b003801808036020580802030300d0b020b40d02c00b44203842c00707800342c0d04444040464541492001e40241c00709003561014041009050701c150902244000b451514150011035032445120a0800080070001591484803059100b0000d17144225585030031179030b584103060003103902034000b40103501c00a040b20102c1214a24207000e011880001a1560603030b101609050007820105501c400007881003141c0d40c1c44c0003034910302c143c80c040703000460001214140b900c1005510540c000c80d0703108540c4483d0b070744408501c01207690120010650800202c2c0140340c408514642601c0d40d580c6062401001003100f03001002c514101810a41c000030803640e65460700648031079201280103000034011840601c45070520343d122043d009180a074503140d00d6035410005048800444003100d5a0b0040d401c60220604100a030222215032030000354145400c150208004c60b0500c00026880c0b9282c0c501384e94240d005004032104c001005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 404630152 1250 404628902 404628907
    0x61202160c0311010806040227030c181501091a0705070f080a15020301081e0709090309080601060e09070f030917040302030c04020f0304080705160320030c0f1003020d02 75
    0xd052a82030700c3c000394501c501164041c000103100d443c05200311229981c0590a0703258140c000c201480089840640480d010704c00d0050010043c3d50710100b07241c9900340715548ad0b41a240c44924000c00a1514580505112214006104508400f420119046003186000303495100390b0400c0e074542200d6501c100001e1070751107008a0400400715003c803a4a006002c1c3c0c0e02d000303161100c04001c9101c240308070b400607000f0240c131282940b180300b003912407805608100c40d40140c07a00c100e8001c40b90004011404506084810001c0240c02e1008074010101c0d4103010408030310700c80110344818802403c4804004e4036194040c81c0300e0183e4020007c150300030b140020006040c940425403640a408168824403401e11844228501070003191807840c1e020b030032a42561030309e5694a081d5003101c04100c4160241e1810104c60806810720700c40118000d00d00803c1d03031b54451543c00000700a0402d1103020b0b0b00041d41e001e40c1344e11016003400084900340c40c01d0440d0030001d0402c80081c01034003d14403009000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 404631402 1250 404630152 404630159
    0x1407090f0b01020c010c0b2d010602060105090906060102150a0e0d03020903010b0f13020c031903020d0606020d020a08031b0316110d17040602040302040c0306031209061202160c 78
    0x141e200340c504a50030303000c56155084110054443c44840322000780240701d14400078403464904500b00c0c1455503030b8000c4a030b4009500d0310b0309101d05002d030410381c010707413100b0010071903480c2030b540458004203544090581800c1c4a00000e4a9030104013802802110041c0861000d1605911044801441400f42e50015442d4a8020060f500c1514002e01c20340c00c0101d4000c43e8940351400074004039006295076040e00c814142c1e000030750445140d081042c003050001e00320034040862010350704075081d0307001a43c8103001080002243d01a030003100c1154065040143c20940018041d03c280741c000d0982c0c0c0c0ca0f80e4401e02c05040701c0d410a0186c5100c05004001d200441c1082072044c01410030b140ca0700152107910400d50340c0d03600703035804001c400500d061a0440a100c100c44043c1c0e0480e005000241c07410303480c2e402080c1950154198100080d81c0d4030010000d00c4114004081800240d103020f0700e41c0c0b8a050802801010940303103412041e0f80c0041c0c001070200032000b80740c00c1540d00458150b58582e4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 404632652 1250 404631402 404631431
    0x10e150d05010b010207080f1902010302040f030b0103030305010e13020f040f14100b0316050d020904091104060503070614030a09170705011104030314090307050a08030913090305030103140709 85
    0x103070400b98054480c030381010981f00ba0104a40707003880142c0004182d40240c0c0d0308440446200d07004141c3c181907080002081112618280c0c00180d40200a07140c003035451460020b00301e03401648424134108a0038184044040c0013000001c07407076011030700b100d00104644002401005215031120202c0e1515640c2c4d210b4841e486500c41c0b240400e000100706217a0b50340c02c420792920040f10b11141244100d481e61030101e009a0181c0545800d240005080c40c480390b01040840314010004e40c0d04000c0c000000e051807502e401410090081a070240032102c1c0b5151000e410205008039010a2003004800103408402d01d034001c0513215006551440d10410128007200d055001017001e480a5007484504481200300340212b80440387c2c550384100344202d92280c08041d941007c00e11319410b01548100080d0780e80c4006485002e0041040515659503185003007115a0b111000b601c140c140c105060b44010030340103002d41c0c1c1100d800c40b030f01d0040420340c5961a030130504140c00009545d4030b0200c10301c03500003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 404633902 1250 404632652 404632661
    0x314070306093c0225060b0406060f110f0a110a090b0102060109090303021e0c1b0607060b06041205030a0e06070f110d05031902070518010e150d0501 66
    0x24003641e010002044034443c0d08080b02124600000c01040030b0398503640080111a0195001500c02801802c20f10707412040345c6120110015031822945506a040a01034548070301c90340c4c004119001c0052516012010300b00d00320074603241003400300002513180451014089200b1211b445e10a403000c115080c94141000001b5103000c0d0f008401101c00420740310b802c1c0c890816010310580040c0040c0c0e01e00b03144c0001400150344101d08058081c4200e4107603020340280c92040c54018881e5503115240003072003030310b40b403104282c0d0b4229840e00c4088070311540316002280c0011303070080300c04108541d01c01d011034100d00c690380c4003090710565000340c14103010012005e0082100c040e51115258018002008803500400f00301800300c60100013001c0008907015140c03082c2c80c401400000b41b21406454103815030f0004c00d6403c6428002210070b04120380d0500201010381001c41e6110500158006170b2081400140a503280101c481d00100da10602c1d0450f0901800500820398243c4d078405240107030191 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 404635152 1250 404633902 404633909
    0xb0703020606150c0f1b0306070e36010806070513170f0321010f14010e0301111b060601030504050307120203040f0b120a0b031b120f0d1d060702090402010314070306 73
    0x74031100c01001c0d11f14012416a00942c1280e0780c81c42e503480310004028890b840140e0403c0741075500307031010a28200c0241600514445c08102c020f50b9890200b403181445001030891080040030440b211041c5207407d01c40c801c0e9403c2440e1040300c0301c644a541807502902051106071848085052044090030320401158142c801c42d03506900d0b41d9400d00b031014419140507616039100180515803542d4400c490321100c0d040002c001088003401c05144c40c1c001e510000007490b030b04507551108605218100000c0d50083d40c02c0c0b900304031618007074851f20b4580c041e08600030038108141120650061080017070b14003420590800b02c031140d65030510100c0c65403100f110ba99200b085c02002440080c894810440401006000790914100d80752a0350001400404001d42c04904000c0300c0b050824200140c0c44580703040401821500c0c0d40200c084c0c441c49100640941e0400140343c1200c4c0c0e5112101521440f44e07040d10b4403101a255480140d0241807400c41103c1001401c0040085082c0d2680007a003c070b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 404636402 1250 404635152 404635183
    0x1303030f03021905070c170f0f1c1103041e03150614060901091a070201090f031208060f0d1b0e040c14060d0221010b0703020606150c0f 60
    0x46034800c101036003603000f050038070071000c041c030741081c5001030080004040f4144101c0d015580c407606e0310590450b11158400c030029039401010010040d0f40b0408c100440b4000c448014205001d0412030a104d41e0a004440c00810000780851500400c04005030f8016014103032039802c42008102520610310701c240300c2503480341c2039409240c00708403a40c400c8200703503550540a0300c028031641b001d014071035000800080c10005011400100000e600e0a140400c102e480340c89651100719000042c0351040710380040d4900b03c2a02d8040001030b03180c13005070240556a080050080d620342d000640321170208036149802c4507041030301400b08207800d01c0c552807041d412800c0712a01a1180b1038015003800c01c540090590084134420700025120308070006288400400c5130740740c107081c40401c5d0b05030f070051550031a126070b202e40c0c040090001d5100c451701500d400040a4108080ba3303e00943c0e03101d020b44800d0080340141c1c0d039200fa106402003110382441c100011a844242081559607442c105071000000c0e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 404637652 1250 404636402 404636417
    0x70c0e01080604150510090b22090215030108060604050703061d04052802041505060d050f0a0b030a030c08130b0c0f0106030c0e070c02090c0a08150d1104020c03130303 74
    0x400190170300c81d1310b000304075910310550300c6410050351030001c1171269040c550080d1221012000100704106a501500110b00049444466881488400380d100407402d96803110074070040c0040403001421981c003441c11503010078180c40f006003d030000e01d82d80e08a9240c2c1e90084040720540f019503524640510312520484100f81110150040e8200860503040500000c2c41c0c2d00750301602c2e164101d6a0199840e03014084119030307903000103045500206d0305c0324082c0d07151420056090000c2c4401d44e845040800240a003400f248000313525000d10f800024180500f1107205424000307141c0030781c0d070714544100b00c4842d841e40b02c500d02025a0820341c40d103045031107400b200445c01d0381d042c0184012a80d21000310b0941d641000110841010024a01001c0002484c11a0096a64884181d00400006071410ba40f1284200001c00410009001742004038149042e1450343d10ba200156945a401600c01c45802d1521700018029125051403071030350f44004101e9000141e02c204031007048030f1007070300c41c0107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 404638902 1250 404637652 404637683
    0xd02030913090b0f0a021606050f0603070803091509100903060b1e0925110f03130b0a0c060617061807060f0c060e070e1608070f0c05060a0c1d0f0105070c0e01080604 73
    0x40d0381d171140c0d000700300094100780465000c40c144540a12410300300c14103036a042038460710100300360016100c03413d00041da12840030814403140d80b180d440050000e603415420000078030380201012803d510801d019950001c00a110031030f04800140700070142502c4520525140d20004000c00364640c111003003801442c01c0361740c51407230000c03ca4401c4d0341c1c0d041d0810161403405010f402c440d007181c007589060000c510902030001d503440c0302d5600039003c81859650300000c4050410718041d8003c1c548900107102200c1900310340400221002190014501300208018184044807400c4140400921490800d020411544400300794401136a40400c2a800965189405848424403625400000c076001d0408111703800e101d070720003c030180b40e103050891141c850f03556280c1c98035108440e01143c5541d20512001c100340c0c020f15500100d000081c21b40d0840380d019001803e4415500c00b114180040098003904026611600c0c000270f219407203032040990b0395074080d5510b40d03d01311000c80300d0044505020f0f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 404640152 1250 404638902 404638909
    0x120303040b0604020304030c05060c1206030133030c0e07140a09051e0d030e01020f030a1b060b09040302030c0c06070308060108180d02030913090b0f0a021606050f06 73
    0x8a00c61078200c584016603484400a000c000c0d40054000d4082000c02d00c00031380030850412520380652900401d80e517541c0106c41c24403010001c007800b8039100340d040484900c116071030604030b8054102c1e10010310880c0c0401c810041000d039010751001302001c02e088400101030f2182004c040c41038401c0e45030044462041c02004003c1d100d999540008640c0c0b100b0309008506010ba01c1c05100c0c20703414643e0a141c0c0103540091074480c02c0030f4003140011a080071054555a0500c20061100c13810720056003004583c0340c024180740785402010180c03c0f54000c040040c002690058581d0a80c082e003040507a09060800a440703500c490300c2c1a400d449202500078407030400704210781d881501075035101540d0300d4501c01152007140c094059200110003214140040406024241014000d0f4005560300c402c958140400d103900c40e2034003142c1a160403d0800420107228006510141c01880c0711300d00c0e0703294810714001340a8a401191042010744246003085800c1d40500c2c0640711900c400c2c1000d94400d001c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 404641402 1250 404640152 404640157
    0x41d10090f110a0308160c05090106020a110f040e0d0e0a0509180f011506080f0c0f070813140405090c030712030207081507080a110a0c2109051203 65
    0x1c200054070005200482e0111207160703806a0b000f0580424150399072143c89090b00a102d185030404d000c00d4482e0300304510000c8200051405490b486001e624141e00607440da240b1030b2010f4011301e0307950444642c564401c014844c40c070900800070800b4007929a904c503514210340b2181c1010441c101d004c3c000d94503000c0e1003501162001081c01ca042d030f03100602d203407000c00d001c2261a464891010604800202801114140342003070514904140c07800200400c41100581070310401d6039a14240910f00e00d10030300722105d4180d54001207a031041c03c0e03d0174800902c50b00700d1000040343c0c11a00810740c0c6d05250a030b100102d0f0103c4040c45203071540c01c10395440d03140f250420307540750f0300040080203001c07507008803000018064010358600c2990381c0d50940c02c021504050044058041041140702604034540e5508480030010030000e02c90810307500b001c0d6102d03040c05c29040c00401c404003410052a410190b034109410301100074022581040505000194028640f290600d0340c2c500b5a4100300206 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 404642652 1250 404641402 404641421
    0x1506050310210204020708090a0803091c1e0203030408010609050604050702011803030b0a031514090a0c0b030a060801152102060d02030402060c030f071a0c0d050a0b041d10 76
    0x80352a010459036081100a46c030048084494000070b0012480a0303444541c40c00081034150091680d91280d03000b00898036a150303034850740c0303858040f1802d00860542408242a03402064401d82102070b51700000346140100e612a00c0990f0912a0104020900f0b400c49409410281e07000d110b151030304e08050342070b87c1080c03150800300c07082030a40e0f1010074401d400601c2c400c48041c0c81c0e004520740780d0b01c81810400c041d0003105041c0c0c0d00c48050b40d08041000408a502140304000b41c1700d1900d156035200aa01a60f1080c90380710b1401002042241d01c42d640038500500031a03000300320700c5000c1c0748182103100c0a031060042c480815480d880c40070308000743d41c2010036070003400c503461300d9420300380c0c403009400140040e60000380900160403100b00403c001c04410f060055019121005840c000b200e581c0140301101e1803070074032001c0c000d20250000079109600740448011941d80c0d00c4000010003000032503505640b10382031528088074442c850700700d0006004400260303040c442d6059444810341d07540c0704 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 404643902 1250 404642652 404642699
    0x1020a02070501050c033a0e070618060302091c0f0203060901020307050d091704030f2f120a02220f0b0a030201050708040806040b010e07020714040c02011506050310 73
    0x41000314000300050a42244040001100041109210391050084a030011840942d0323a600403038100c1602009090010041d9290840c0d02c603207003008802e100050741c0700d89824150041040000c1d40d0754003c01484000241d4000e0300841d0503820301d50070541c03851509901070b0113500302054a0399411b008a07403007014142c490500e0000d40241090042840480a40d40c107805554040e42601c4900c004000850145044035041081030508810180200501385083c1411030b0425150b203140c0030501007544004c0318440d00d500400b02c0c8003401c189000c0c1000350b001e0000382610300d0216120488502003030078004104074540c030240e003803400c907419921882d6005001c04402c00c0103600c1103008106151041c00386130b050a9a0310070039803400340241d900300c2d0480c0c240001031000301540b46040c2da00610510013404410b10f000c00441000b001148001c2c0940c0c0c0320311a052400e0b0003500140b00c001510042c00580d980d03503110080c09a08140d03407100b02d402545000107454410b0b80c150195254408 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 404645152 1250 404643902 404643907
    0x170909180316080c0a0501020a020601170a0305160204090320210a0903080409060501031b082d010b0a03050601021b04090c0506031512150115020c060c01020a02070501050c03 77
    0x1c1d450a82c107a4055104840c0000200b1400c54403680c14010300120511500016845510340c0d54040c0c107041d016082025602120b041c030407800e0340000b568880300754040c00c3c00743da148034200c504a00807a400c10043e41260034203944104055000c40c0454500c03204819014003641100d040c0783d2501260010107151401d0710710a039000f0481c80b0002c180104c0c00b400c141c044030f641c9507500541600b0542c020404696103100070400b81d6054007420241d43d4503121140c600944075030010300440400f8102202142c80d1a03126001814510022541181c11402c2c81d80c10f5a901c0d4070007101684210f03407070000030b420b00c6c010403003d5000041d414000800320029104000b4841e060100502c2d20311030603200c6108000c40019a074031844001c5000321400100044520080400d00c40e0300002ca8102c85616405a40d681400c02d01c0d002c086819a000860800b5000e60104001c0303252103404010aa40408000b6a92801050541c020000401d0503020b8403665035079032006445034001d400f400080c94004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 404646402 1250 404645152 404645167
    0x15021b07050a0b130302092715010b07080a030509010209032a1f030506010905090112051c0e060c0c0a0f09060902120a020306210a031b0c150302071709091803 70
    0x1c0d1410030740c45014407207074180179006080403000b460321130045149a03800c52780e0701e01c421100d030010807405400665605840c00340c007507550b000c4512840e4400e81c1015511404210301e0344082d0100c40c01110003c3c1240e20107580802d8600c0180b50304000381d4190626540e041b0805e00f4206400ca080c48001494040c40805120081e806020b009010b24100404100041001d5444202d0903019010029400314006034619003207103002030030306100d04515298000a03042175800b00c0049843d0b813044d1881a1260807920745540b034155000d0845034003441c0d1140c0894000f43c5074190404561443c50203000541c1d403060420200d205043e001c240c54207a59002541051440e0010750b000070010b0070202c980c2281e010120a0300c01c482c00e80203001d8022017407420a0613440205089802116054502c0000b0240c0d130f111900d10840c0b2030308262400e44005060018041e80c1524040c94100309400d6094801c0080454194080c5d400302e4413449c0329401082049495a0a071442c3d010b0503001980f07001072 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 404647652 1250 404646402 404646409
    0xd0b031b060a030b040203360645100207150504051509010209012616090b030108010b1002060f180304090f0605090f07020a15021b07050a0b130302 65
    0x540309509068444d10460748039120b40c4002c5100d007100302c08801c2080005c611480598081d691500c18500c01000d05003041c11011495541004001c0b0802c01102081d15078260780c5041d9801150074646846242241e03000b0020701c0b05012400c407020b443e284a5413195105c124041c6001c003600e01145000d11807045040c9921980d04180180100c40c8002c604070014004400c0482e43c901c143d0350045210395040d42c0111b070b414103400049141640790303640c0c50111049003400524a406215a40100c2c610301802050984050b2003038150483c6c0d00e40e140c00ca014081c140f6025080c5c06074099003659043c0c0d510204465000c0c3e0100040382103140c940ba07180112000e1124884902e50000308000112004280324503c02d01c4042c140109540e840d0200b005540c9500400e80c040410710700701044401e0750f011440840c420344c07104400c03203aa001c07580054000d0044000f451a058030441520824900004480302113070000c442c603a554503240c0b820108030b401030b5a000c40c41184082014401442c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 404648902 1250 404647652 404647657
    0x8010b0310050904150b060703080c031012120909052202030c27060906130f060f180e0705030c04022d07031b02130b03210d0b031b06 59
    0x161050030000c07460340c40d9030001d054641c1c240e608552012407809049084d80d014061072003c08012504035051000a407000392620b0303001032031242e80d02d000100042c15107141410680141095481c40c0c2d03200229881d144e03050b42000c020130408030302d03a2800012100383d00e000303907442036180c4481540e8842e15850544000024a00100d80c1030140c241c18801d5030f12003d060504041e05580301032250304d104080b070b60b02d540010707000d140240c80d0038041118136181d440c948680000d0044000a00006508142c4000c20310b980280040e200d1501000032a2640d0f01c03c840d1100c00b40341020004820a1001c495484d43c84e0701c81d0a816420040c00000d26141582c0548044012061b1611000000c4818800300c101c040703460001107880400c1c0310b801d056000351464103074000215058443c100d19000501500c220000e03a04000f074546040880301d8600f4007002095840645409800b00241d400f21840c5421070400c1450451510034440c0c2e961a00040040700141440b0010300400060000e0040301e030b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 404650152 1250 404648902 404648911
    0x1090510020f0105150f0d0302060705160606030f0317010509060105130f0303050705070605030106050708160609050601150e09010b03100b0a080103150e07180905010207060c0e1008010b03 83
    0x180202c075400c0010040c02c0c000e0134815004a070121103040b401c03c0410444800560201e801403828454030000a500001c0d920b4110407282000c0ba15441c0c6c01c2c80c0d244950300340d02c030000c056a0500e1400010007405820381c200b0203100703445a155404400105154401b0244150740d4072403604000304419501940040c40410f110203041e034602600d0b86600324216009901c102d0008000248a509016080c04040042e180030302c0c00a1540d45840e0008045001d44d0310003425010000800d2050150381001490b03995034401c01c20f0115200608103a0b40351a402d1084542114500c0c3e0480041886240309e8903e107100107114119990802c000100360707400050110f02c48404107440400d80f0031845000e015140160380e0303071035041d606515080070380711105400304070014204205108112000701c1c7e060142d460303588101010103100702440380070300060f00014016510001d210418084107030491141014552915099404110180f00540c000380d00082d001546400052050040200045802 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 404651402 1250 404650152 404650157
    0xa090b0d030e041805160803030f0a110903062a0403210309050a05010504050106050922020102100e070306050114090f04050c0a0e06030c1203090d08070f290601090510 74
    0x441902c51003540302c401340a07000396070990103841402100d880304066907000e0120700014500307504003420003550754240a010700c820300f52a20500080c00100e14266000d0003030044c104c69242c1071025840c3c0062080c0d4100090403441c044006200780b4002040b94200d0b40e1115245101e10000d860702c0504403034800c010005c058a07030b070044002c83c0c010007030b11181038010b2000107030504051500c2801c6480651001c1c1c016803000080105007225480c880d85400b08400201c0d03824111440101d0030640c2e1803601240d218074200b0f03100c08800000801400352440f4010400960340c98100107204a0762100010780d01400701000240511000307002c40e50814892011201d07000d25000018182d00d11540000322800e03100c00420285203010080026440c40c1a100c04940c180256011502c038801c1806480c02030951480002c02c002c03401c012034a800782c0104040ca82c08503140341114480c0c00420020600031004410300301200401540107001d60030503103030b0b500e06c1440c1c1001e01010b00c540345106000e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 404652652 1250 404651402 404651411
    0x1106040b040303020609071508060613050603010b07050c06070f120314070806030105070c120e01090306020f030405061e011a070f1128120c0f140a090b0d030e04 71
    0x4011030504080c0000d50b100743c010346180e00d80440b081e8500285640040c2048403600210034071190000303442500450b0589003148c0e41c0208100503002d0b42560b50119421900000001590300c600c0c0d400303825901c0c812001e0b81c4110007080b0420241d4040c4100250503040c07581010400200d42d40600082c0380d006040c0411301c5100701560b036603142011545000400c40007000c02010380340a2040a41c040c816041006c46040340d070322000907924a1100c0c02c81030240811066560b0f83c028802d4030000c56201e00c0c15560703074054001000c841d81080c1c900711514428000404c0d46100c0e00044c0504504480008002582c6001c210a0480d140601c40c0602408100311620119502601a07006207001d03c0c0c902c0b41e000840800e000c580fa0000c0701100c1903009106080c512511242c10107411101619496000c0380c2640c1011f03d03a51100742e2000151907804440080c00b507510170724042c8226001c071801e42c4080c0c1c6e40d07002070003501e034000680d40d481141e41d20306100181c0201982400e00034050710025 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 404653902 1250 404652652 404652659
    0x90a18050a06090b090f0c040c09180f140106020a020607030e040f0504030e2d1c05071503090b0a050403110109080d1521080d05010b03041506080a110604 68
    0x2410480d4100742501e10300e85400420060100e005800391300098144010840c2003c01c42049071030700c00090080741300e04d8541001a2107a07200320703075001c0901013103c622024000d01c91500c0005000c2001101243c80c14164010b6085038240650b6049650a8018041841c0e140d820040342d40c1c4110000c034203000320549803100b1519030380300e00b100115264900203054203082c203019000004040c40c03144a0f00c424901b40d150305020400072400c031811140500e6000b8030007400103a07420070070001c0c1d40001c00544c83c2e9800344040001d19004680340c3c1c180841d9000b400d03402c00c0f0141d6101200c041c149840503030200301e01c2400c03a4803856000d4082e16003500721a40d19001d01d42540d01320403050762190008920900c03002213511a9908445100d032081c400b00b40303828048006140e40c0005600b82c000e0b114031060a01082004a442c1006004010026581c5510480780b80350002d80c0e06032204d0003036610031021075101c2c0c850380c1c0a4401101c02001f09044541e240d00d2200d108280e00b9822410501c40003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 404655152 1250 404653902 404653913
    0x5010f271e05041802042708030f06011b030e1f02010608100e06060d11040c0f0e010c05030301140f040e0309090a020a09090c030b030607210b090a18 66
    0x40007070800400320107000401c600aa41006245800c514415450883e14022034101030300c072404480d90560780420040000d441e40340481030b14406035181c00410100090401107003000031441110045a0303103103aa151800111448000c0b0101e0f150b5682034407140c100070034081e003801910210002d004400740500705504107541e0140048560160391034180a02400c241440785228800300c0c00707005c004082800050039510031010f4401800f91403805000c00500c110300403009109070014105210f0090001c3c0001c1c0711109641c1d074000000d040d561608180d41c405d0420528550304040154250b03401c1010180ea07501406012035880256001500641d445900400618590700c00103192122416014410011802003007009590320402240c03c40b40d4200f5511826501101c9000038442103843d0250014001040c0059040c80761b2001c210a15910103600b07010300c84180054030380d00e4800901c0005450505020603400b500441c0041e0ad61403070b5522205442c050340c900000400300b41e4030342 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 404656402 1250 404655152 404655227
    0x60a0b09070c052d0c01020a0503040308160803161e0207090c050c010905010506090c0a08010e040c1d060102010c03021204080702241908070e0f060f040b0702030f0705010f 76
    0x1100c000140b0f26954510384134080c01040b01001080c000b4022036131896075401c4e1a44501e00000b00026804a41244944141d00380300f0794040c0e1040c101562800d01001e03c2201c000240d0b50303400001c42210304125a651200c28244100010f900144409803c000b07150000d055102250f200704081404441d040d003009000303444c03d507402003000140070305044051000303102c00180400d40008080100c1080594081113190460740c0007145403100791603901d41040a540c181d44451002c3c9800c00510503260384400846020b81c000360000c000340d040d4a84c0039404e9020381c40e001d1100b445020001008192004020081c09100503d01400c0d05e030f440e481031000c145903a00c2030150034408168921f425001e945480e01a11680c100a00c441c9401c8100410840718900c50754040c00301003408040c80c0e280c640c182c401841050419a4a81e611140408050741108405a20a100f443d00905024001003011010b40d10181e40e41e11445040c0030003500c07a40d00c002610a402c140c52541c1c40081040d0864 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 404657652 1250 404656402 404656453
    0x3330612061f110f03090a0320060d0c08010906050d0303020705120714070e19020c010f0e03091503011d0c0d09151424060409110408060a0b09070c05 66
    0x10743d00a0007000c1540d0501d00000741c089103140b075104010043c2c40b80c2d1044440c5045a92085a00c00808156a80b40c201c40d44910360240d00704102140303111800c00c96030440c191101880d43c5009049c0e98880c105019a540ca201300c0f82c2052030a0030800110340700790000c080300c900920844540650306400c6080f00c2c4d1001400365400c0044000a980849050145400400900500b000f19040c40c00b0072142e941418203031411590350010f104c0e64102c0081d0044448140300e10410059490003014607030712603001140392840780c13510707090311004c515044058a050f148400e080040101c0c1c00001c9901c4050042c1410440b00d005100300304280900e4001d096500b8450308208407142000038007202614108403500740d6034183d1004001c4808402d06420840400391000201001404404108140b0440d04002d0500741041452003100c003005c8001c204032000c1104692146d620032003c42c086803c18005103034000e4499020810b210300c516403031030b01c080c02441914002c201c656860240d0307080f081c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 404658902 1250 404657652 404657657
    0x4020a090e0a0207052e090f050106060816030608060604050709031707110105070f080918100f05010f02031c0615080703150b030105060a110303330612061f 69
    0x381302d020400d0a20202c403590204510070074100000080191b400c5895621034410a0b680310442000c0c000403600c10340e60550000000c000300c6031202001010ba02c4101e074858401d102010703501c1800c1e88244100030445100c1005400035440300342c1008042e0001401c03080800000150210100f22200111910080d118840c25a00e4502c2d00d00380c0d80750340b036009003281403200601022010418940305042850381c4059001d5880310500009003400c6000200c00443c035071964100a4450501c06000d003d6604042655041a41d10030044030110300713000343c100c0185c201348520540314540c0b003c0658003d0f0b0080340800c00c81d40b251700c40a504c4a20341000d10001e440c50052040f4190140300f00030301d0741c144036405c24138582403802240c21888103110386070185038005001524a031240525034041c0e41c148058036a6030a103a03443c62a0380d44030b90700e480c41541421500b0619842c2d0400d01035007d02d00544080d00b441561a0841e0000c003004100c00e401c88455590542c0c0955840e42c40e0b1a24001c80c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 404660152 1250 404658902 404658907
    0x8090f0315060112020412110301020d240902041d07020109060c02062a120c0409090b160302040621150b04080601080105040b04021212030103150c020a03090504020a090e0a02 77
    0xb04001003100b88408500409640704000c28040c441c04001080c3d4842d400c41ca10709094000580801e00a12454074603800003850411000400c130b01039916200820010101102215104c01c8007004910842c41022440c1588444c00d0804284250026900856900000800d00c01c6ea0711400b0544401000000c010381110041228882c0b50b90114100c00070000701078801d050b0400481a25071140c8612903c072001c80e20300080310709450404039005407c03002002d02c0903030380d07030b152040c030700e03182903880d079200c2240300702c0381200d49220341f09481c120f440c03a5607141d4030340075100004101c40c10b901085110310390301da041c582111401c0c1b0350305a0081c00d00b06052541e81d0701c2c14030f50f1800d00030180c0081d0540d9041c4428031000c5102e6480194005804a84410940e020062110701c1c180b45103080c85000c005c044000024002d0009020070082d078021400d119460000c0c0c4102d8507410306080080c003290106a040c171a42c101a4050098103025007080b80b0f41039202c0c000340e8400c01e4110b17820440240c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 404661402 1250 404660152 404660161
    0x8040c051e01120e0712060204030c03050c090708040302060c09060c1510050103020c0a0212070e01060c0209010806160f0e04020705030a0306081204091a0607030201050402041d060408090f0315 85
    0x8a0484140c0303a0340e0150400c2100c62600704240c50344117500c1400b10714210040d41d18140704040e81218002c1da4090f01142d0b070760b5070b24038040d61160043c2d5040b41c4101341c0038002a104038043c0780100e10890313056010301810303039401c0784070252500702000454100c81c00f40691071002108210140c561003000c52191024500350b40e58030546001500024101801400540503130a0001104400c0c0741e81240d022501001500110b40362451a5000e5a045030903074000145d210f400028880719103000351040040c42c0c0e04c1e281c9940c1d40300419910241000f050242010301507104444d907030082419494180c0154100000050a980141900b030710703a60000100307100602d4140c401c100080a420340548110241c0d03034a034000500682c401da004a90b200d0840403090081880d503852407402c000c0186440300c2c01801c0090080004840c100d0241e07282c844c40d0051b09210290101140314610010121a5544d44e41d2803403e40004524941012100300310f0001a40c00340605134110401e06000d80291a0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 404662652 1250 404661402 404661407
    0xa0906050711071205060c18060a03150b0403050613060f0606020c040e010c2703020406030f020f060c0d110c0306070c03020d080408070f0c03060e010605030708010e0a0308040c051e01 81
    0x3016070003020320101034154000040c20101e006c0d60312208210150f62603008110340441c0f04c0300c45c6031603d5440f6800088a5600e280c0642c421004614040710f00e4440c6a02c1e047d51460ba4031650202422540c04000001d081c0612506414200303031103000d01140080170190107c040d80c0f042d030441405a041251011007e0405129100702441d0001c000c2c4003114401c880a04014001c030810042c50441580514200b080c1202560040d580980200091603503030400700401c0d24203140c224401c540101c81d2003210b19225007910580003008000e0400081214030130340780242942c0b68481729020324600c500c8995418000305120743c1541c0c44880c28a4014a0000d01702000c140c07285003031001c950144004100c5c20300c142c40b2980d52051003225140107900308800d0343c0d084c0380e00c0201100d0404200484420064000c2001c03540280c0c1120010364850391080e09a54051200140540c0640c20b40404a84a2011542c110b03005071500780315240c8520114a60030240c0044403210071178444003139820f5a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 404663902 1250 404662652 404662663
    0xc0102090916140309030408120a031812050904060b040303050703020f0114040308090f0d0e010e180610050c010e01020304110f150c010605060d06080d0c050a03080a0906050711 78
    0x102c4151240c1c1d401d241e800e0050030703101038000c400c01c0c04200880082e1304803000b00201c50142201004841c000c00100b05014401d40c0300e0340e62000024240403c4018480803100004519903210030302000440c00000c3c100d407a90084400180d00948944001a5010b403900081c4061350103a039660755924170300c3c1800703032411190710030401e02c60f8035000c50018200c000e4440150481d50500d003200031610340041e01032900c20090300e2401c55000300000303480c1440e04045850035022007030b00c5104048004608202030203c1016800003070003003000000b41c003481e03c0d002e00c0f03458056074100181030400440c541800c4400074030121416030350010621050110132000d4200071034044541c1ba60f480070712004034a0702d00f140c4840741076041020490300b551850a40010014050140109072220340342d2400c0000303814039101b001350500600c0c3d00a60306500c5035184401c056000b20017400005403c2da8125440c002c0100b40040c0e05503501c4a82000a040b0f0148501034162940c5025100c03522400103070512 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 404665152 1250 404663902 404663911
    0x70813080f0304020604091d2416020f072c07020a03080403020c030d030603061401051e0402040b030c03060a06111b061e0319020a080112020103090203030c01020909 73
    0x48600441000191120301100c0030030050840a944940340c500c08264180030315000304003814207040080107030359446555002d0121140302295800d558814200305030310440b50044580703140001c00240564104076209a14840c940b044540e075483c00c0309042d08040e000d802c41c0501c01d0440781d141001c010311500703560704202007402c81981c41c00c0140b0080c1d40c4207200c0030b004052111510010b1309050090110402e04480902951100850094000c005207820700080381e0b000d00d04080e030402100d540d6000d905031a0090040f140481c0c0e5120364203074545110700410381c0581c0802000c2821750f2140301840c01103e1850160ba10703070428000f04600c2054076005842001204291390980340d4002030008500201030000601104034000440d040c0c3c41144200001c0300034904d2058003074410700300150b1048102e03419014003044008a00016881900385c10700002c3e4503000140048000c01a8040c0c080f4414100001d44c007801e0f81c04681180c20004010302d03107941c080f50143d207600300110741d02e510 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 404666402 1250 404665152 404665171
    0xf050a05062412010602100e1612060e071202040f0c090b1c090c090b0306060108161101150e07080705030a0c051c060f0506392e140105040e01140f0708 67
    0x4001a00000c9d80c00c3c8148a40806510030840c04024000c0b180d024816800000094418803900c65544081c1180c485204901030f43c640304096030a034285100e403c1d0303100785031764a00c01411702d072540b042c0458100980200602423800c1510b0102102403003811152486112040784052a251001c81100c0003030383c8070750080d044503041001d03903a804070b401644828004110340f2542c0c1300b03800072580e8981c1481801e04940c40c020703042011000361800c00003251124968142c0039036a00c00100d4498034180c0f500e2010650610100300d9540140d041380d06155012714041342082044412070602038594414940c0c0315946800601000810300005c002170300094030101e140c45020180011502c0780154180c00090032000c4005a03080810503141070b00401d28100c800c0100c110909080101e80c43d420141e03040b0304644ca080000900340196074506504a0880d21180c1c079240c14400034194502e10340090755a01d0300d200d0721070050403d9041c041c07554803080e10b030380b0b03c1c0090000d0000ca6019001054 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 404667652 1250 404666402 404666413
    0xf07030f020414070921081b060606070302030d09021810060206100f1802070c09050604050105011707030e0708070803040f060e1f0e10030f050a05062412010602100e 73
    0x49064001c080c02c170440c0e103095140e0461000000300003003490307a601d00092040d100003a01d0b141034450201484040048101070b91a0b036250081006602c1c0b003941001000758209101d072645c000800d610110609001400c0c00f00308085036201500480030031500700c0d5044c0002c0f68188409641044042d520446400960070b40074101141c50a56900302e119002903046880c0c4d40748400ca200e038054440c1d29500158094046440d0704010004d800b0468296000c0c92800c0700010f42c1c3d40c483c1e00889282d54a20004403102d07260341804501a0207100c200380224464501c00042840041010100510060001d140c03502d007007990b929403100c06940030000f00b242440d058400b81d0740355a00d041d4003c3e40501c6000400b10011801e40d00680041c080c0c55001800c240700900194043e0004842e45116202c10807107541e4922401088610076074800b5000200300310721150780103407580e40c2c1c00c15003030040301c00f410a00080203000c0400c9090300083c0040e00405290005540c0c10300825815640a5000c0d14 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 404668902 1250 404667652 404667661
    0x31b070501110c060a1d0c090c16080705011104030804170a0503030c040f0e010501050a051b03040e09010c0c150c0302070501020711030607050c15061c0b071b170306030f07030f020414 81
    0x2651f90046c10180782c410503010000c80d130800a000c0868800f401044000000d050890600f046d25030840c26040c0d619500305000989000c480c00200c40075242d014001d2401c150612441107610b80d4004503602d03481c401c0a81d880c01150080028600c0b43c19000c50704c0360345030b0030070aa003058140c0a50055801c280035000501003680c0000594031322005d14581030f0380f80c001500000301e50b07500b5409800c2680c0130006000c117104445078103107842815200003e0204c003042840841d24603400300405081505020785c01041d081294000d0400e00101e0714025050050303d4448508992052804503000c41c1100d00700d0302c80e400d0500c2490360161060800b942448500d040310750312070b45507002c01c031070880300c1000140b45507841e510450681689401c414458203814604540100003d84146001c99200b00180250040c0e03a4410012aa03103c86407a01100c2550074040c51030304054440d42d45405900c3c041c01108004100940040d80512400c260720b030040d0050004540382411402a241c1d030780b50810 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 404670152 1250 404668902 404668961
    0xa050103050103050c060c15270604120f2006040c080318040507110a0309060e12100c030603080721030b18040201030e01110301031205031b070501110c060a 69
    0x50751758400d50304030741da030072666481c2400d00e405519002402c00c100400d10244440c1c0340d1041c503408111120400718240b1058403a543c450080700d00611206450754003800552068030035101003030300d90800e15504c11440d8400d0000742c01d42d401b032000c0303580181c2c108814422001001e06c0107040300c0780510325045108050501c0461211400c60140d45c94101050802c2d1052544007a98000d90081da40100072625009041c5841413080d03d001600d13039107003124103241409000566a981074010825000c54483c95005000800d05460600d5034031702c000000305031400014181c440c45850b01041810410039100718150345423000408040c50840714140c00e4903070101c81400000072885980881c5c1c1e4034401207010f411104050400355003450380c8034940b200750b10040d5068070b1084050000403041c1740c808849a010445100d40c03501d11100e0100d04a00e200c5004040c42d80c00f42001151030440000400c500742e00c50205d50303001b82d10110030085000042d101c2c3e01c0d03500c030f41d11011202008108401c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 404671402 1250 404670152 404670163
    0xc05090f0a0b15030406020a110d09090e0f190308011d07031a0319140a080f0d060e0f04021e01021c03060e100e07090b18030a200a05010305010305 65
    0x240118565141a4103034a07544812160f022404841141503032881c09183c054069001b100710303a000718004014074440404007040c189030344d1403a5030720801c0d01071400c2820005405448402c40c000c1c010a074101d11200c2e002c3c003140d00008103400a072001403200d450020541c44051b0300500c4c04880741e0001d0041065680d00c1d65030001040e2802048120214100d41401d8505504c40c0346c2c0b44c4211070030105401010810002c00900449400c1c44d07400061052903203405d00308000402281c0f0410201c402140c03100068020700c48007410003c0c510740c855080300545007040e80c40b85c1d00840c05d0b204000031890201078501c011101e045140030003c82000010350b441c05a80300110401c400421000911403003507200d04010031514a41c011541803c60042c1040b2086006426200480b61b0000300304900441503002182c010000a5280c482c004128895101403c01c0943d458000c04800c240440d410140d6000c04480c0d0400002034a1518020046980761700d038803c2e4103141c1001b00410116401084 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 404672652 1250 404671402 404671411
    0xb07080601050a1d130c0306080a0b06010f091d10060512040b1506070f0303110a080114040e0f0c0f0d03020606040b0301061a0702040605040501140120030f070c05090f 74
    0x14403c0c000c2004d0f810088032865034041036904101e00c0c48138802140070740d030000d209014080d20100400c540b111384280d10b4140030403028016010394004681c4a500c01c41601c2e05001d001d140c000e61207902d4828086141800a9941d614045041700748110140100b10241c0242020b0800c1c0e8600043d0b41844542444014000341a0340140b02c002440c01c4074080e0940f603a400000c0c00507039500900d1403d030755204450341302500081d00d001824090344800100f121006034207500c5083c2d50340e213080c540b0207100ba1850005034002e5158806004081810050500c0d01554032024000103075508040c0314a0302408039156114901d00d03414100400d401150298100303e007541e012403899400404240500916400751003415007040041d030107032171410040d050946c03003140c00344500740c3c0c2c072400c0209a450a000740c0c0c44400b82200340188640c0502a041985985485000c43c5c07508101c803000d08640003e504844126800900e04041106201c2c1034400750504583c00010740c20001680400c0000081 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 404673902 1250 404672652 404672657
    0x70c1d04030c1103102a09081e011b0305090d02031e03100305240f0403140901170c070201121104120606082d0106050312160512070b07080601050a 65
    0xf56001c83c50b201400000f0a120412905203c2415200b01c4c002400e0015509686807582e80d0411440d2603200c1d4111000711120b40004207154a130780301400b403610018441440e181d40d81c07502c2c0740c900b424005180041440d2107890004043c60080c591504200c20301401404542003000b00281101106072080d04983c1c0300041c05490340e590455452071048103802c003900c144544905e4a042000211107912100142070145601782c40c0c501c40d039a0b074610b040e1380c000c01280c07548107083c0004403880b01800480c2c01c145842001810312880a03148c804c000da4400041046c0015140195604121080c2d04074410b06000c00052180d140301d244d00d40258000d9154600c1d60500100610500e034100324094074070001620340b0100024884e0380700c003d940b407154010314250107010950000602c2848125200a4050038010a100742c0610240d03021160f580481d0348549100b5010400402000c1c664581030104103030345881c40e00700301a05c0d010041100040046503800c0000507648031081c0ca004901c0760 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 404675152 1250 404673902 404673923
    0x102100e071202060d050f061c11270106053006010c0c0305010c05040501030c020118030806130908030f091903140f0c01060e07030213050f06040308070c1d04030c 72
    0x902c006086481a0b17040000320700d0500040c4041c0c65840d4407003d001e40d104031203490b20100e44520114079403425640c0500203030b250724a980943e0030015142503610300c5032800350048400d100d600d03a000120a07001900000c00c00708202203000c010b8404030841d07503442d92010482d1080c440201e201002c004110b1410800c03804081000c104101c50740002440d440002401006d00b4250020280c0e04240300b0940002d00f0180f1280c01c050040c420311070580d400c034070507810b1201c55490070b80d0304550123054290000b00c004061a1049610320440da00640706d0350071140e880c01e00300b0120b10303e004050041002c5400c4080d4040c074215141000d41d450703907810709203200b0302012000994800c3c0594072040d8580c031400904a40c0507038041d0701500580b58019100c0c5626150284203c00302c3c015405039403004581e43c00103101c00d1501d500c4400b284c0c0401006140b900d41c40f0356401b007864000704d10444001076000c41c01c2c410100400c4c00410045002120802d00c1d1810741c600403d81015904040c0203031024 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 404676258 1106 404675152 404675189
    0x111030d090b07030203160c020f03070902040e0f0903040e070201020706050c1e040503030a0302070f05120d0b040b090403030237020c040507020304032d0f020102100e07 75
    0xe1402000741a60f1f42d013900c2c01800302d2803d1341d2154011034120250b6408015001c0030b04100900540c44918015680383c10020140c0003004082c0500200a074504001043e1402c075202141842c445442c1d107641a0300910030803038041c244a090008100030b014060004150150100c175600d8400d82501d042d02140707003d9400351943c141c2081061050fa544242c02034204680a0b40e2914014640c5954a601c1c005003031007403004a850200350b01103042c100d03101d0401c0341da1081c5d80500960024500180d40408010402010f060b40071401c21194104411200900944403c8164a04104a405220400c5004107600040c4074600549840b03007014012507018140ca40c008509103401d43d070350040c1842c4d00070341504036a00010a043c8030f07085c0c11913482e520715000302000100414140002410031880c4051041980d04000001317403011000a43d920440781c0101980f01d003000c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 404496402 404676258 := by
  have h0 := BRFrame.cov_init 404496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 404496402 ≤ n) (h2 : n < 404676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
