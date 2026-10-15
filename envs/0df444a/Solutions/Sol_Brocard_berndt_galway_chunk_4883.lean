-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4883
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:02:41.584782+00:00
-- url     : https://prove2.me/submissions/e238436d-0d5f-4b7f-86fd-ab57c42c1337

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 878057553 ≤ n < 878237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 878058803 1250 878057553 878057561
    0xe060f1b03040503070b130b0309011d0c040c0e03060601030c3c021c030b0a08010f02031f030309090c11012c0c030316020a080a030306050a0e0c03070e0103 69
    0x40c480301254408052084060044000d0007900c8094055844858560082c0c0c00301c0c0c40390740141d00c0e42c0103070720204120540c82a40650340059840e40081740000e003c12402174603035a0603034252001c1c0c2140848003080e00e4980300d800c07a100c10a007072840e0f4a1003001c1c002911003800606090502d6140d0046ca03141d50320400e8544210089040c103000147d081c48510712031410060240030701c12224010566896000184000e000d1030118605983c403420340e40c2c00c070060900d1410850300002c890f940800c01d83e8007030068010b25695054016102d1602c00c020444085840c519200640401001070003c80d42c411008005d40c1e43e48600070401ba02c1c03c10044402c90a848036100207546058204c0b41d401c8407134814001900d207000c21496042c040e4001141c0c403840d0703821a0941c5940100240342401c0c0c410440303203610700c2c00280485403840e076403681c980c2050051241180041d6071080d0a100501d00091008068501e0002c48012854400510021031001038600310610a000b00a12416803007900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 878060053 1250 878058803 878058817
    0x5040e010306091505160e031204032d02010c030e01050d051303080a06060e0f0a1a070c0b040e0a0b030a2a091a010f02120307050c01051005010e060f 66
    0x4152a260340e5242011802000c50550840e0b10301c221150060841d280d60255502640300c2c04441140440d100344281c412030500940550507024001005c2400e0301e03100c01410007180a94101a402490b01446c42114800c00480e81030b418941d03078483d00980d0307101400c4201c05501d410941e40700c00c8560700603240da0080240c043d0b0707214105401c010814018070203800c904c1c0d1081c1c03100c0704075441d50440c4206860b01d6024400000743e1a0444080c5850400c4414054650180054840503190b940141c45048e1103039040143d008000fa000c0200144044030f4001403651440d9282060700f80710300344842500140040300c48075200e01400b10560f07030901c845030085910044501c0700310003108600d040700c540c5819850802200c0e5200080650080c0180c8400d41000c41c60280172030308180c0191045070b003039000d075030443c410003855120069250004500810050315404c0c1c80742c4a840040e820350f4001400b048a00c80b04640800842c1d8006030750f09118981103c0300d40e12901c8101c015101409089 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 878061303 1250 878060053 878060069
    0xd06080c12031e0d06120203160e0c0d090f0c0e010801020c06010e0a0b030a0606061709030409091a010f050901170715030908040311151603051e120108010b010c03050f03070504 78
    0x20300015001240031b002d113920a100b6025655810b07a6070051104281d02c500c54031a918003d400003541403414440200411407117440b001421765031644440824079580c01044484031101c0f4001e200400e000b50900d40101400d40c001e516041d9144080ea071a0181071080905413400c940101d4030400c0349801100900801070202ca074003560508184010700100c1c0700c1c000105940c204401c020f080100d0b1814410b1344032200651402c2e291060700d100074510b41c1826145030240050f65803848800800351402400e4030700c4222684ea003041c1c10803800100603405241e001c1c3d0b55600c0c0794a0180045840c90448026090912a800b071f0305d030f0f00b580070701580640181050070000d0b01004010801c51050502c100a4441d000200020804c05206100f0035044032100d1903040c1c19000000d00c01ca00401d02010003104003000e61660b90103402e41c682161003070024211002c001400407840c240f10f134400710720b001d00c1c002005401702c3c2c5020b03103c3d10589000c500c522500000180c8050302400445005003000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 878062553 1250 878061303 878061311
    0x15090414100507030f0c14030703110429120721020a0c0c0906030203120c03040b1c0f05070c0f0611030106230322060905030d06080c12031e0d 63
    0x1d441402000200e5410b000320b460003111500d108040d1003981076a40c1c0d81d444407000005204071580c4150801400b03081059182e6134844031503d00725014000405026903410b01c004000c150b0071149500350619202017044c11304c1885000f00c0a03040d0f0030380191480c20100c81070000340701c1356014600801d801c248200e00000d01d5030415540f015041c05158041da050203003241d203d1840100b503a8143c84003a40c980d00c5a4100c4d030041d003e84005000240c4000c0c210703482c0ca9074900a1a560742c008070b502220040c10780c1c40c080c1c5105424010100d00540c108400c1140d4901418041d001041021015113103820f50001001000095030140003060b42c0d8184494032980c0d103801c01089000308004000680d8500b503c0503c9480d126421b607401504040501501c07003049005580d0028000d080039111b80342c80c3d40f0b000000c214103200a000c0d12408580200d542401d0800c51032804c1640f4180034000d8941002e0302030324034408010b4421107000382020140c40010907511440ca8000c0c10b000300b407010703c0c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 878063803 1250 878062553 878062573
    0x303090212160b03071e120507091e031509050a0209270705010e010e06120a0605180603030d020702150d05040605010504200c0307060908031e15090414 67
    0x410310034004031107005181c0503440b141c0d01e041602085c0c510601144000e43c0b2651000d62848107070005040c10314140000c000d070b040b000710a40380107a44110200e8402030301880300c07017240c424149a0003401d00c1c11102c0b0900d1941c40d0648114940c4c220000c203680c0d100007104010040c000d01c912240c009041c290b05081036180d84015026841c41d40300b101c1a10400c080044c1401315503002107420503103401003280c3c01e01d0015206100c0c150210340d440041045052280d500d103a040c28010300c5000000a42941040d041c442c2041b0200111001551503100f0400941d40004c201c8460442071140076807100600d102080d1440e505c0d40c10030810b0349001c25003a000002e59440f00c0d100d00e00645c400d11a5903a42d8003031000f02c0300e10740060740142c1c040328410307010351106100428190103550f00f00c9240000340d803100811200400c0c0205c48518000003804441c410780e20a900000309010341e120003905004001c441c0354500c6005075400380e0655000281406aa4541548401d408034251090340c02 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 878065053 1250 878063803 878063839
    0x10815040e030c1509060708040c0305030c0d020c1503040f0203120c0a110108040210080403020f0d030e0706090f1401050f1c06061110020d020706020a0c060b091501080403030902 79
    0x81003c52401030311684c3c404807079003840041051302540106015010a4807030100446c0c0d1030100800070348110b808254000009141000200030800c09071000d404428080d00b4000e050160f03040c08140328070588500f00c1144400d1000700c1e0303041341e0312004030001060740b4400b19082c020300281c4800c0c010400700341210f408101240c4040d0b00c80c4554010f92203403030208015070301c481e004d0ba8041d4000e4149050880320070b008109403a003083c024011035030102c0b03010300c00c681780c0707061040b540002984440940394034060800034640034110178108a04d2050801540305d80a1240d44505180e030403100840200f940d000f035007244c0740042150242035551148501110541d02c00301000385030189040f0340007419034801d807c584d038609555805000300d00b00002a2101a400c298001149a6420851500050410310041c5180016600c810804a0660502402700c41010203540d0107001900100b05803200e802ea280034800300c090919042640310340c101207009002a480007904a1410b041e80f9144107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 878066303 1250 878065053 878065057
    0x106030803040c0608010f030309141f0c03110d0c080f1e09030d0c03021207060b1009060912050a0213140a02250b0112030c0501051e011e05010815040e03 68
    0x3c0c2c615101c0e11802d1f41e0b58110022044d080d8403015001a9080e0fa00f8000305100485900444000524944086a8291100c400d080e0a40405c03c0410720390008d003c109500309900310b00761a502c0002e0901008801d8020b01a0b40b0038a4000f802c400c03000803681c102d0b13000c1005403030300ca00420154800498001002d10101c4c1d21202d00c0034440d104074000511642d11640d80c0344845685a070240815450280c100900b50b00720880403103101d600c44020500d00c3d203031210b44000384400b5a540d28821450a82c002d4400003294100c849060781d0a005500858000a407144000340d0688010303104d03a41d00b5611300020701c00d6285c80d5001c0e070030001c10301c15501c4080d000360441c42c00171460034400d4400705221003840209100e000301030801c0b54004016840300001c4042c2a103000f0304115901c5180760351080d00b11441240c01c0b2550998140704007800c01a603584030b17400340c40c64444400302500052128100f88000d4452a41003040c09030014500c42d41e07000b09085030b103002400500517007414101890b04c039 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 878067553 1250 878066303 878066309
    0x1020a0506010f061d010e060318030c0d09050d050a02370302040b01020d0c0602160813060807050a05180102030c07080615010e0d1502090d0605060a0504020406090608090106030803040c 82
    0x404603045c80e24228140300c102400180161580041403e09001b40071068000514035409010a581e4604940f80b05000070803560409402600005820280c0600383c046150411400f03545d40c41d495800280001a101400d541c0444036281c07030309013880c080e612650043d03918082c81062100c1c04540c0c2030301846400243d901c03c40d01030010403441c0b401281d0369503d2003031103400550103046000200744158014003e01c00d0521680119503450745400125501400a000109030841c02c1004000d61110740c558002c0201d24042e4584425180300410034060b8039000f4807543c0b076100d140e61240e03000f00201c03004850b6610550312565516007402e80c41c1e030000c966044024004640f40d0380301798840c401c0321a468000610200c40c80009881d50515076a104585d4000349034200f02071082a0354040c01d0000320b911503d0b01090620f002030502224607190341c421400307240140424060160020042d00a4900e185000385403941c907400014050700b0039a1016000c01c00000a0000f0b00294841c1c2c0070503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 878068803 1250 878067553 878067557
    0x204060b0720030a06180503030718060806150a11120d062c04030c0816060c030b130e030f031008160f0513020d0e010f0b0a14060901020a0506010f06 66
    0x10b159000001448019842a0030a5064100d000d184000510701c1e885034003950200318200d0741e4800c0e80d0707880c246180d02c00e440172000708581c91441e08005913480c2c0003201511040c58450030500745035000c1590403018400303041d003254010032004c40d0184034a0100c005480b8078001c0b240e24100700070f00313600183d00001c81040201d06113040480c5603041c00143c8030000c049100400310340f80b1440001c40303401c6000b420440402501500c06004240d152000d448064444540509680103a1a0900460b017007000c1c24014141041d6001c0460358500c0442d248280022a02080d40780006143c00e05500c40e440c040a901da0f00442031020031405250280e05a65940c01103c504501891440d01c80d1107440c0f0030141c8801e4201024001c44c14141c0c1600c0440f594241c015040510340300021058030080c036018012a950303003529108a500034007595403140c00542d00754201031300b04100303001440d200030705040c001c10b0001640e5072213034801c100301d0134040e4211040e1440e5507141d02101c02203400c04d2140c02c1c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 878070053 1250 878068803 878068823
    0x40c050c19082a07060201060611010506220603020603040b0403080c0319111b1605040e030f280206060a1505090f061c050618010b0403030e0d0204060b07 68
    0x55215981c0e1074001c2904840400d003840c0c802640603260003100d00c5105250450b180318800324090800c481005840c00d9000418003502340000140400011071903da051381c10103081c41010746980000000c0280d9600d8408103800394108418042d1000c2c1d48000e410410000420007030003038001452307014a21a0341e44000b10380f2990310030803a0b4001a110b41d40d01d03100d505290b82d2000002d41c000401082c1000b11503051092104c035601c0d10071001122200c098008144240102c615102e0100160000b110f080001d0054418601d9403030140e804c0c1948108400240010008200340203000021904020301b0790b6400764400081d2258825149140154040000401c0c4000310980328540008a41e40d01806c00f4075860401c6510700e00c151016401a02c10041c8684070b03144100800031881c542000401d80f42003200900000c0300031f04080c138400003007203c01402042070b140c044030103c98240c604102e03100b40c00300c00a4410311011070005d50091400380001280840b58000e4250349006404000e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 878071303 1250 878070053 878070073
    0xc1504090c020703050615031203040302031308010501060e09060a091508010621060c200c1c02091911070311100c0e060a02010f0c09030203070909081206060702040c050c 75
    0xb03662078040d404010a13940100c0000780142c0304013171910390001001021107218034800d49010322168006d5406400680000540400d000180044800104403000080145603d0310300d0090045902d844900c0c843d0301c425021412641d82d41d14510068800140c040003c08840c0001d854208020f201ba13030010b5080090004001e2040c801100c000b000308000c1e030302c2e40780d129651704c4001c16580000c1e10601149103101c945c461503002018141e0203942c4000e008540d511400c10011a02031018400d4540700000d0b810300503114481020707007004040d40c2d03864a1010700752113040906024031120740120404203c3c841810341c804140c40001c1489400d942c0c000310340c0c122840550764206c120780d0206823154200310142c2002002814080420720000400190b2448000705460f5203045c5403000815100042c0290300d07003400a540240301e100f0b004c200801c050741e14400940956402109055420380024000b52102c3d01115001da0703000780100500d0508a0024120703400c290b02880c90741c4a141000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 878072553 1250 878071303 878071307
    0xf0204030b280c110f101a060d110705010c02061014090c091302030a0603020102060708161d0d0303061802090609120708060403080402011e200c1504090c 68
    0x104203118000d030390361041480440442c0080c1c200e43c02c001c400c100006031000c070504802c1c0894021054070070080e04c2c400030060360407401d0329241c0c20200b5500e4961801110503a5071181103940c0c205403514007042c800010382500019000340701c00070f000b03035080c451070064141c0c2c0840d410384140b882d001d42c003004540b500002242e030301c824400c440d04062a075011440f0300c1280d402130101b00400800348124041086002d005070b0b0003c1e1116100a51a0030003841150780501c81613038001c803280340464042ca4204401a00b4502c95107101c01401310b41d000908065420b20b081049013880500403000c00440c61500034000c1400b446034019400740240123285001d905d000f140d045000c000d00c8a810030703034828100641105184d19107011486510000101d42d403041c002d140c4124000c2d2503054003031500d0700001d000c0d503440400c40354032842100803c1c0091074100d6501aa00f81d502c90b080b07040c3c003000c810305500c2c064550408030b500100703184910300030058920041c003c1e1003800200f400009068401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 878073803 1250 878072553 878072581
    0x2708040e1501121a040e1c08070207030f03021204030510150f0b030a0603020a03080a030e01180b040f0c09091406010308040501050309033609070e040e010f0f0204030b 74
    0x801c038001240030030a050381144507000350105031107001a0701c43d01001840010101c5800c5418400290001954000358400441e00c08414010a090042c1c05107080c4100945884050000a118260b0f42805406042c420070032404603c1c07449080300c2c2c0d50380c0c8905101d0345d0390314100c410354005400c004d1055818045104d95200b00e4407072442d420b1542c0d0811500080a4000800304007400c2e668820010250740ca540d500d40046001b00c0c0c1aaa82e081d0010004041e201220300b038011716814100c680c0206000124072140e117541000c0249070079200d6141c0020480700d0400080c010112502020680584560240070307214450070b07038440c00005038823025488200900c00a001000144010841940038600650744040e086040e646018000307401000c16881c035026102901d256401000b640042c1b003907040040701c00480f410002894845002440060f4450ae5503010f180c8921511040c40025008401d2505501c01c0500522a0081070b03000250060300c001d99085401d2808551004040d002d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 878075053 1250 878073803 878073841
    0x60501050f011404153606050421080705010509060712060f140619080a0506031b01030209011101180501050f010e041e080d1e0209010507062708040e 66
    0x640f060406140c400300880300d400b005101002d001c0f110300102d0f00c01500a079402c003d01010b10700f0380304012850034910b28903c005d030405418008100418811217a548042501d1a00c412110200810840ca40303078003180901c1100800660070581844614800401c140384502050360303c0000c3c01028854007001d541a40c0309500c66403609100500030100c1c1900c01c0c00180c000584010f14141c0306000e80c4141e16084103141c40001e4000b003e12003004c58502030283c00402c1140186500c1c51100c5202d6100034401100c0b41c1895800140044183d020b00d0070401c004c80c101d0020484c0304012241030003170070b1000302c045502e54a09400240703401c54000040781660490024402940d603180d5407c40c0c241c0c40c21100c040308442ced0503165400240010010214940318500c00709843c404400a074a800c41c0b0030314014240350051000307900c0c40c0d9104060710000ca401100124030048089255118581d64043c0c070b002841c001440740c000e120f01c90b80100300704c4040208002e102c5d5500c4000b00c501c415803c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 878076303 1250 878075053 878075087
    0x9180f03070f170702060f090a050d0209070c26040905060a290d0c03020705010f06290705010516110d1b0302011d100e030708030103020607050a0f060501050f01 71
    0x1440c40085000e4440c00304140c80c00d607229601e481300315000100b45030022100f061440b003000407081503d00b0304103046c5008007005c0d612034500303010503400120f0304070000300444200005446031809100c41040388291003180312540303d000303080800b088040344d405030064a0116092001051440c100310001004039840ca002ea6480703403501e94940d50340180000400e0385c0800007440001c00d800070600c0341095800b09903c00694600c200d00d411800c1d500b840701240000da143c45410401c1101c5c00e166110121501c1079a9290108041401400d03800b41d00d401074030030762900e4200030a407912240e513164403d8698484001d15424442610b55030b0046282d10400612640001e812202d242050081c2030b9200b4000801c03400858443c0703280b0810113041e0307001c480d4822664040340d91003511608510b11306c008083c0d450013802e6210000c42c0d00c41840000d000301d1001400c4001d0002c148140456079500c0000240e51ba2150b00307108014140a000b2503120b034204901301c44540d809040c00910301c00d141 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 878077553 1250 878076303 878076323
    0x90e0307020915092802040f080d1107050d020105040e040609020a270b010c06151a0c0c0d1704090b09011202030a021c0c080115050a030c05040f0b09180f0307 70
    0x70850014415604450030031045c81d41020700140000c14009440900541059000210300d400003043c0307488042d4007540140f00c2c451014444541000c1610000c0d548d042c1c403680513240036840101c41d00e04c940c1c2d11411501034148144010403c01c1d81003ca40c10f40219817050300d07252079800d4441c0d44503041351040c881c0c0c0104411602c07150226001501449414104005180031584034101540c038081080386181c04515028403a084c07aa001c00c6842103207080031319091000d1055a6640e8507002d8500c144120608001d20f010007000701c840070140c600044186440b0795945003070740e02408444901c54030030191034001080124514920034021a0020b004003c5990700d9002d222048441d030310040700f0030508030300e80b0b00402e1102a2080003442040000214181c00c1d00700401c50707400c1074029602c1140d890104101145d2291a40030030b4a0044400040386131007100960010b021400546400524032002c2000e942002e01181c55030307001c4d42c0300791841211035440290303c0b84030f0ba020041085a503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 878078803 1250 878077553 878077561
    0x10b01110d120e0303130506090f070506090312040f061704030e010e03010b0d15050108010c0f08101a0a030605041811060904110309010b0f010c031206090e030702091509 75
    0x820701d01c0c140d4182c400240003d08241654140c0c2c210741c411140b001489000054034001c0280810500d94000303512405002c010911140840d00d400b07242c0300c0c840c45420013081d51880c903901404415185030b040c00e00d00f0380d45c540e18920000c1003a02407060501103203294203414582c0c00c19207251413060f0b82c907568442c046025030b40151200143c1c0501540c140d0368034903038038003143ca94145070b0421500a00e0511208001d1582c294141c85058000000c40d9040070000e03c4503d8001e040900803600506004074147e650851610703000f81c055201a0319810b01910780d810b401c0400f401800c5111441e9000d010f1542c4a40038003090721424801920081c20020540c80480c0070800102542076004040c14034001402e00000c01b03455000d540c10709818000030034070030008000d202d0080d0700e4509840c801711209200c0c001070159180c4400180c144a029101c010110f26641d0003c4060300c015501000319209480740c6560b60307003021b00203e000c2d400324404038010b540e409a0301d1251601c01400d2014581e6 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 878080053 1250 878078803 878078807
    0x6060c030a08010815041e030c1e0b06030d020307080f16080417062809020a240804030807030b010e0904030810080303151903080301080c010f030c080109150506180102010b01110d 79
    0xc28488242c04200124040c0000503507082d101120302b180f0100e58100000d07560815451142d0060f2800e4800e900025504c001c80e50080260396142d500021841e49401ca515011891031041c00c2d43c5c24890320300d089105042102e020302800540c0d8440203d12126030703104000035030b43d10094586180b60440000600c83c951841120f40c92040000ba10114030480d4950100e51600e040342c2050007103021841c0c5668070384049907103680400c01d103441c01d0013590605031005007041c90080d1030b030010075071106070301e0000741d0050022417100e1038082c2c103440d103034038160900426141054405013118204a0f00006903000c0c000140e0b80158064002c51201000e4102001034030f1582c02e081c480d04131040f03100080444c04040c003641c02006440c0142c582808900d00041640c0ca1b18860071007490320300144e405070964040b00f45415074282d140002a1440048138290f01c068150703003c80d5000031f00045071f01900c2c4100380c5c3c40c040c0c00070a80081c4030070720719440159100b4040108240c0c090340085420b10142d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 878081303 1250 878080053 878080103
    0x360301020901140310030b16020d090617130807110112060f5414060f040b040c02210708121f030308042f040506060c030a0801081504 59
    0x1001100b1700c8151641ca54542c06400022a062440c0e9582c0c110841d80075038045c4642d0402ea4034600d00b6004840c00c01c58040d100d9440c0d00c0c0e1501c0c10103c8000000c1160008014448070103820a1015450342450314140c001d0300f414a049038001801103aa2010000d0540901810b039025000c40e0225141001480c40c000c20103824022000241001d0400080f1507003616101800c88402010107041c1500c13001c1c1c000a0144d66104400c0d41c58400c50030b020252025020390071a408564a200d2556100c0000d00a400c5c00390800303a0091411450100a82e000034070600e9006c030302d00a134a1500b0303070321069000a000d0b1100c05040101c080201c5154002c8240c056580004284420358250803180c035a0b83c801009500100c0100340143c00340014090306440c3c075440440c40d80038945d103444403c0d443e0504e5030002101c0500550700c60001c00c1c1c0541d6564141c074416202078007200e888030440760004000c89820311401501e0f0160500d140943e40303071241990300c1503030821800c070400e52004007600e2400c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 878082553 1250 878081303 878081311
    0x60b0f090f120a30110105010e13020609030c040501061701170d3002070311060601093804030c0e10030b040f0f03020f01060b070b010605070201053603010209011403 73
    0x101a8043c024281813603d880032650a190769a5a0f4141c81741c103c1240e4215a0f06812244106c80e800040001052410704a041d00a605982c4207848600340d0012914000780c404000c3e51003401c03c8008100d0b1036005c1034002c20215488401d60071a66100c0114032500001d07011100650000b04081090501403541c9002d00383d002c0070003072407480240756940901a0010b1490060580024001080c154004d45004c2d11006000c0644154241030b40083d0080f00e484c469800c6124002144001030840400e200c00c0c9403080101805044100b484840c0c20b681c03060000b01e504030310742c400c00310300d10b040c1c0c920443c071441c894440b00e800282580c5420781da0b0703c0010411200c1071140c1c0b880e400098a101a102e118911a0300204039114031840e20314251035441d04088030620050014902094151803500e0454203e4108503654181c2400120380030700c2102088100251003056a0300c4000300b05540016203c2548042900b04c1400d40400d801d074890310500c1c80c00200c2d0040c4601c0d131190404019504 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 878083803 1250 878082553 878082593
    0x507030b0402130603081c2309010609050907290d020f09060c0106030b01080c0310180c0f030c060801080307140c0301140906010608010810020d060b0f090f120a 71
    0xf104a48201010a131041a0000c0b10340d0b50f0701040d07480010112100205418210a5042c002c080b100e4401c03c9111661403945120740e60280042140e01d0030a501100103850b002e60140294a000481c503a81c40300a4441c0d1030360211102d400c1440300905411040000c00c482c80c00601d08030002c002d2902942014202414554041010101c82c1d80e840c001061400c0310480086002465800c141c224440c050744003000c2a00200440d0780540c0d800b003180d140c0360000000009031500c40b40462281c0804210b001040079441e6003020400c07114061218045a11926040c9044d5445820032a01e4140038070548843d035100703002c54400240750807a440003187d0405c04550f0355a03a4800007a007513444024511803c0324400c0180045840c0034090507014008030308001099503d403449c8195110140381c54802400d9010030350584121041c2c00c000001c0981038201515802c00102c0c625041d4450128640b04060090441d0841d04284460b400040c5003030015025510003911412a01d521805001074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 878085053 1250 878083803 878083819
    0x140f060f1b22090c2c06090402160212030421030f03051306062705071b1a010617060a050303030c0a05040f0e0106020f070e060f0112050106051903090507030b0402 72
    0xd14540310f8410344405281c0c568078103617240e11600841110402480082c03141441c00c01150b01c41d602d80804451080d08161001651844072400d00181c400805070003d510219046000c1945000000134105880c561504914600700054001400707581680e00200803a0840112282c0306000c0da00213039019105928040f948402543c2c0d8400304c17941c075040007aa0f448802050640107540c80c00c8078140c07088400007001141040c070400380c8100000b6601e0040750150a07036036070030070160108280d40c902c95003540c99055615950068036889000d113a000080f890840040d6031407078074a06400840e88040e001e5842e42d107495100081b0303030384078540e4001404810400090010701c034141e001c00a2501e82284402035061040081c00d2000e001d16240440c0e10030300c82444004248100c0d10703005001285e03413241700400798005076000480f0010036200503242400006400c1e800000400c00a00ca4403082c000680d4500d800fa400c0362900c48000e8802d900814003407000503207000d840c0f0740060000301120 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 878086303 1250 878085053 878085059
    0x3050a031d190602010b04140103081e030f0403030e031306050f0c120a14130e07030b0d0309170703030e040c030207200a0b07110d140f060f1b22 64
    0x2040c0a900b503060b250301c12101042080707407031390a1003800035084084a0511a890032942c03074400d42c07541800041c140f50030000341901e000b40c1240104922000c0c55104546924005801c210390100480f0140c0c0440d08110720290520349c04422503000d40300c0f1a1000341e4030b80c1400b0086445400c6001e440c000f6400812465022100422801c204e510a001c4a5641c030043d000d00206600051032100410300d00174400c80300700d60100c2125100352048200c115034a6551003a04901620070000180c2d081303000b410144041c154041c94001c11b40308000c0d011a07117001c5662401e555042244406000220400d140f00c0c184c2c80c03d83c01c5540d01d030f20180703809410403441f074031041c2c01d002c800c2c00c50b1107043c0145503c0c002c41d8100b1000100062418409560030107540f62a11200007a00c2c801c0144102000c0040c10200400d0020010070030000c00100c031980ca91144085075982c00554690b591350754a0b4000480910b0b51f52518049103590000d5241444111030440c60003005d00ca00000d1419401c003008 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 878087553 1250 878086303 878086309
    0x3071d030106170604140f03040b070602160f11030c010e01081302060f040611190b0403140d0f050c070c170f0d08071b0b0612120a0806030d080103050a031d 69
    0x84080324129400713081d9908191400000302c91021940d01125003020b10721080c2040044162030484441c07204041e50780d01c8500d0842c1c0203215009010075891540e015050070b02c5035519404628920424407402da4440315401c00d655400b80c0251580020707042954154694450101c0c0350f007003154480c60b04940000381c0d0002d04d40340c1040c0c8031810310180100d01049100d501c5094004512030341c03c00781c104003c0e03a50132003c0041201402030610100c14001c101003610802e420078440e00c13030400054841000d800b039980035207501e03031030050402c0c03d000209031030345a654110f42e1499800a0407004035031400c1d654510b0752a517220b54924a000d01c50304141e0240091000a00741c1045980e010b0191800040150002d0209014203088060b40d4450a00084000c6115600503804940c84c20011041c1003200385014115030b0040500c03840464120141900310760f046000381c0d4120b007a40c3d94401202c00484000b031003403001070031070b41c004691140401c1c003800342100301c000034003440c09001142e0b03404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 878088803 1250 878087553 878087579
    0xf0409050f0309031623210106140f0a05012601151103070b0106110a061a0108011a070206071a070c0605012909010c05150a050a0203071d030106 64
    0x708494a800008403210503213400d1000c81c130460b4103100d005580c01c1c100043c00001c61884201d04051a10040c2014441d9451011040a0402d4440b1f140c0e0384842c46510a0702903c2c072440341d285c018080300311800062030705c00410140c1101c00340c01d07110480d14001c011502110b580009525401e544c02c2c1c01c13000004a00c0c031190103050f042a402551014110000303002c00c00c3c003c0749900c590002d1000e100020f15a500e4607044078018601016048502c1280c01e01b85491100300408183c5800244840b0030459504407032074070000d0302c03501c0c601d82ea640721349051900031000042c0000c004020a40c0146020360203465601d00400c040030f00e071b00c02f07000c2000d868402994103074040303000da000700c4c42008914043d950251450320b0380300391150703442550304100003683c12403c400030001060070304035a441400494a080e0b00f0504507018100036074060711030302c1c000742e0b0801031060425001414018560086900401c8142c2e1008201c200f00036504880d1160007001d10380c955244c11001071038813a2410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 878090053 1250 878088803 878088823
    0xc150c0f0d020403050c040506030a110307151d0301020901050a0f0905120f2a130f1107120302092d03010f0209030114060f091b1305011701140f040905 67
    0x150041c3e030b480c110f04201e07140c101482c59041c400d80c140405c00055071800301d154541e030b96000d5008420780f60f0410004e81010030b00d030420346124016803000320003a83c2c0310100b490103030008030f01c4000c075200a80a0500380d03c02c0400c102c0c0421002c0203000040b81c456980c0003c20013242c030b0404203107a05c410009860101d0b042000c126070b4000c1c0034000c0358950500145581c0c41020351040c030002e03c203c458002c40b81c0c0c581f4409210344402041c02c24088590740140d6000350300302c0700407c9100c513900003469141d0440c00c400d40d54440d02d4020040c0440c021720846408040003455008041d5000848000c910112390040d5095103860b4007800f8980c80c24010500c0c0c6800c0c00d2005038a500800051608450080c80c0303000e4680440400d210341c0361284407400c9003c40e81500c0f200e500c1e54604c110050445400118045400c80014202c05803c92004102c03090312026641c1d0f81c60380300b424601961a940031701400d804c8800140d4201d415240104c0f080000303c501038004103202242da02e800d41880c0c1030311 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 878091303 1250 878090053 878090077
    0xb0f181204060224010b0a200f0d020d0813030c020411030a15150807020708060f04060c0807080a0b01110a08040e01080a12030b04060e13060c02030c150c0f 69
    0x8503090000580512035a114000c070002c49043d0a840524039044600062250b442006c1d400903810320124410711800311803403022031440d11102030351034110340d0781c0c43e8800d10100a40202d440c5014041e1012a0020080c05940c0e0b80c40316945945090341911200d20308100c0a04c80e15103803200040e29039005603a560b5160a01060300c5c0d1602c0100c280507119666050b80b1426880d680c00d0010314080c4103048407001503031916a0700b950f940c030400e91600c1e12035000303254030380714000c00c10082403628000640b00d41d106035400d000d03d134120401941d5980b03095602d080800d0b0a000000e9405080380e001c0a0780036414034040703007100084036450f400e2560204094541101c0001c0034401d40d9900744030140140794101c001e0944949c0c0351549054486910790b40070405842d441c001c502c5507903640112001d0030a14004000d40d0500c10702000790340d402c018017241c82c14104409403d11500200c261241c00d0010000740c00380c4801278200c5940c600000304410000703c01408645000b003000000b50820304004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 878092553 1250 878091303 878091307
    0x1a0d11040b040209011202070c0b07060911040203010806060d032003090f0307080a0b04021306090903030c0f020c060f0c0a1407080109020f092e1406070b0f1812 71
    0x1a410300003540d00c11014280101d00410114101d40d80c06030800c18201000c10005840d004c2d2480d00c0040780c09070b640010710400d008241d6500380111a400a04100e103c0c01030091040e42380700c20310007a80000d00c00c4400d40e80201c00000c01604013a03810592180c8a07142030b00d5a09400d459202e101c1c3d40030700710081b8580c004a2508050709006020100844c41180200b445a1600c0c10072680c030729080305e0080c031540e80f0300007050854030781e8001140003503013084050140a880c1d04170701000307020041d01600003e0500c1e0051014070f001d581c4c0c000c2031000b40e40c09894420f51041c10f2010540c00b80101c07105030380741005a04615041030000001d503900c251040c11107001e00e11246850180642c0003181c40d6451705082000603a5603030501007402e2400e0302c81c150781d03946070210000801c8001d16214000c0f0741d0814007908071a40180524262020380c280410305195070020b120a03401034450040420304503401107031a14209045450b4000c0d8244d41c02480d101d0718004c15414405c04200b0301340d2410300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 878093803 1250 878092553 878092583
    0x30a030f06360f14130507060f0507061a19080615030705190509011403030406110a1a09011817160c152015061503011502120712031a0d 60
    0x14010013143c00c500000e100010503081c42e1030b0151500c40600c00d040134000f800c014101507500410540b0b0a042c0c0044040101014502213524040c400349411480b8045600d4001a0f40005070807aa043c0c4610324000c0519a0b51784000e0b040e94600d0500460b0f140c8181200003070651348840c00100000080b0040c03140107071629080c070440210680040301010701540c20090a0348000003500c08071040d9103006084e40841d40b46e003604020110314050f10755141996030034008804855550b00400c2418001c110000080c405011b10b0b0400310402000c0e042c00d1100b0741d082d109004060020a12617032841ca112402d42d030b0710700400d81001d90000082030b5966440070342468001241903000503107c0c03032440360801e0060b20305440714030007454945600c8150000c07882644500d40c40e240c1410290607034503906d5071070340302c1c11848507802d0405e400184600940c4040d88803000082e528169404002c0e080722000324a0b055006e40703103114445011800383c401100407647c40d040c000c44d886008036030215000207 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 878095053 1250 878093803 878093831
    0x60c0a0905030307080414091509061807090807150806190f060c030201050106030c02030d090611040311040b030d08011a0702041107060b060f2506060305030a030f06360f 75
    0xf41020603845101d0050400c440e0781000d245520001c9c10803100320509644080005031200c0a40700c0c60b8504486010401c0003d6030026081402d8800880c11941255130340c4504500c015110004140080c0307810b070100701c90b400c01e41c04180c1024224500c0489154464002d803454038210751150700054031070000d50040c59020300c1900d015159514040c45a40b203017020107544e0f40309000030703440250f5031856008148520342c0c0c4035040705580c0e15105070344c030b6540b42002452845000e041038811440d00303003141e141d0311f0300280e01c524285c8185c540c800d903070303207410400710303c0c2041000310917000c40d820081680140c0c2c03280726040d65500701d40001d0303031240c1c40b904105003251400c4e440710b80143d2007044118030030300003007041d81c08a0210028142803581a81c01c1d400c2ca40e0f54154005101d0341c01c00c1e030007004201010000e4049142659020010b03c82030390070341d40940b5518452800400d001103c2c02e110820711030510b1003c011984040705402d0030000b0503078125411348480b1351309a070f070343c20315940310103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 878096303 1250 878095053 878095079
    0x50d050d141602060c010914030406110106151d04020d091407240c0b1806090304060c1118040606060e011e0e0310020d1a12060c0a09050303070804 65
    0x604114110350038050900b40081c849032810002074407a01004c00d5020200c0ba0035040301d03c1c001c0d48104c070340796200b019900060350307600b1900845020503e00264028080350512030281164003000c5104281e04140310181d60f0303000d0018024030a0107a10800c4c604c2501c4a0000340302c80c20090400213a640c0e41c40c2880742c2004200f1842150075000711070300b08211308002c181500343d582c00810740503203110310601c1030b95443c102c0c20004003030b224440f042020192800070001042c0c4cc040c0b040e1178843c0c3e01d002a250b03c91040703024460105039080a540e01061100c00307849462900a400d0050f07203000f80e104d0b140f645c00300703c40c1107030f046485000921080758400010034070210b007802c0c032600c440e0b003148100d4001741480303d0801c00c102c03400009491940c0c04001c20900040c200408660340d901849a0102074809014926071320014400000120b00740303482d440010140100203404170fa02d440714116030a81c00006860104004010045940e079814401014000e200d002c84954561621132200d001c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 878097553 1250 878096303 878096327
    0x304080a060e1c05161a09012012040804081b011b0f080915030a09030f0905030607140c071205010605010309150e15280501080c12010204050d050d 65
    0x50f420080030342c012400c040401070044040350034019110004041d8648110750341050140044054030602e554540302c01881d140103100140003400302c100445500e10300210154540c580720031040042541588020355159001482840c449140c030340d4540000d0f190441c141c000c492001314611040d001582c000011600c2101ca12500341c0c03120340b075915a480c9031515110080c004540004270841a50f0340e281e020741183c800b0107586612030416004403c01408641011000300303016400c80a040c0e401541010122200200200015039a100d41100c90f00080142810810000e00194040240501c00d140c058207031110b40c0744034881c590030000d0a540442e071042e4189448c2c1403540d800f10781011409c80303090b2072450000c40da140c1c18400c0103180c09a4403030200342c10160042400780c164116181d9889400e241c443e007820017060343c0f900400f110401e03c16511a0740c4800c0c00642d20f401d000000d0610401c03400c000505055980c404240c000708e021030300702c440390407504141c03521a030886445209 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 878098803 1250 878097553 878097581
    0x280b04121d011b0c0801020412060c0302040e13020d121106010b040302010e12071d09010e0f071e030609030806120703120302220602030c0c090f0402150c0304080a06 73
    0x40c070159400068210540031a0342c00791580c1c0c042a5005203d1509402001404484000c41d40c45550b03092031400700c01103003001c55855041140294040f0702c64026101510042401300c0040e8880c40d01411182001c00350407a08051a0008100440c1442004c00c29031000c5803200c0100501100189092801c160004015464144024000750368001d03d003149502c002da0b914a10086040030562601180d944039000b00c00e41349106540d442c07160b40e00d16000d200d070140240400b03442118203c4d03d68101c080c901d903981d48011800c101d500e035080c51904400c103182d081032502c0e0340c0340d483d11020398003070f144142c01196001d01441207034107118940d0710408540c440900f50b00c6086681c2c0074a5590350322004020140c0100303500031000c103004210000c454600622904159a41c50040d45a40044044007a980590f0402d828035044c201c0903280314135083d03803102d0b141d03580e5a800c007c05075001c039001540b00c0005020000308454200000e1000d4400b060081088400350b140440c1030b03410054041e44 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 878100053 1250 878098803 878098847
    0xb07050c04020918011419080a08030702030d090309060e030a0b0c031b1204052b0e01260105011b0f0803040812040302150c07050309150d0204120c05040e280b0412 72
    0x1208d42c60209002181a62203403200e0313070381e4589001c00c902d0750180511004406241503486010103420585000403204507840301e9441c2c4420508040c0c846a042e0070180c05180c81d40001501502000008c40c5d208080e642011155088082c0d8030307500d5003109068108905030701043c031003444002c002000051001810203101024120880482d50556000000030710194a86801c120f81c080c0a4902540e80b03061240e40c40686404032401d5044000e100f4140850792180414003413504480504101ca43c01c0002c1101420b480e940e100880d074401002580d032000203208949100884000e403c0c0918001e40c0100b0b01e41100100d160304100340540a02c00b6000c0c1000a41d000590201c1504e1112104940c40b256900050440d2402c0f40f00c0c3c030100f030070300718400500401d10490941034600c40b240510b058020041e240c83c180b02c03c4442c0b60b4401d69880e40204403000508401c800d020070050002c941c82d0325980e646030b131868072503501078800b290003045440b50041070650100703081d0380d000c80381d04c1444 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 878101303 1250 878100053 878100059
    0x427050105040e100b0a050d0503071a010b0a0c0821010807080115140f0405100f080304031a04110a12060c020120070f12080603070b07050c04020918011419 69
    0x1e80d0300e00a41c10300320213040d00c40c0f20801580d981c6083c0100102000380002d000e28000c0d152075034595101e000110340c0005402003800c4400c0742c0240390b5050f0b0704150783c1c1d40e16240d1031210541da14110a0400c070b4000400b0051941400350052003a824500c0042741e07900f803541403e00107410400d032504032182c103a01d400b515003804050509000203d80801c2104510011a032001c2192220707045010707a00305090000703102508007a030705040300702c0780c801c0c03040c10f0b10586480e490348d1217108510001e44103510300c0042e205071240c281403298005204000145c2d4803110400800d0252090b9440000d501028881802c284402802480d910194610081101c148071800d00310078108611809501c18402280e94010014658011104507802c8001950b07141c065a100621001003141c126020740030b00c100000e580009601510308072a44440034184806000b001d0000a4110000c065481613804600480c8044a218030602038260142c41e030001c11410010302046d9104030a030b0701c1019a11031020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 878102553 1250 878101303 878101331
    0x1812020d020a08040306180614160e09150307090c03060509010603050f0103060527010e0f06010608072102070f170a0504050d1a010608010602070605090f15042705010504 75
    0x88065a600a1b400104c0402c01000000b031241d024030000d0031540b81c07603a800400b44191040380d105142000070140d40b4041440308442c0d0b480e4000003203401c034000c0d801291458600e10b41039140144c0140448211558450418098414940f01e000100ea070702c0e0014042c5080ca12243c0c1d01404c5107003070900440c2840003c3c6621440144005040d181e5920045460416650411661000d4a1803d2010500c00c41d01c0c0a00a145101480601e845580041c2c41180d101064031412a00b85468904440e59440c806030303078281a030b1840c01208150001b00c00c1c00511144060319100d800b45c0642100311013603140000c400020301d104c5080001c403e00c100c160341c07a03020b82120b080e01e005075a11002628949004a04c02024030600503000140d0000402d43d6540004d580d8100ca03a6582158002d40c3e8400c8107850a01c110314009401511540c009480760a00140540707035010003880c2a03140603500d4a084280c922005140880d0b800c0c00c0c0742212582c1c4040c025107015200c121800c01c000a080a21 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 878103803 1250 878102553 878102557
    0x90d030903021e0102041805012103050703110309040501080606120c03070b07060216030c0314030609073006052704140a06230f01050609040f1812020d020a08 70
    0x2d586003424840030464184102174040c0c4004007a10501d110021109440c1c0e10041c100c00d0081da00344c0c50100300040419007c070060302404ca41c250300c0e22854112aa1001c542460500e108a500340c84104406c45283d00d035407103814000c0040070058a4241003103020030028103202c9001d080705522841a0b05c4031944c000c10791900300c5400000071980c91201d031914801a0141c0d001145440121580390002d00d60414401c24400d4801c1c2c0e10095035014030b40d040c100600080c2c4980b50004103035000140c2250003980c0345500c2950040391813001100c0f40340da83e60003805101c2c29026042d10b5010801c0a82000d0001000e2103112414480100328032112016000d10000c2c000351100e0301c190303c0309404440034016000d40039004034091200311001c03114000b80c02c03440c1c80d0400d844000d550004141c0d502c1c0404040c107a6100800141c0707410212010080604402044444544d58900b081c070f112003031400c2d810a50a114126000e01c0081040003c1e04200d500c1c8400010754001800f4040000c8035803003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 878105053 1250 878103803 878103823
    0x1c08010b180301110903071a1c091b0f06020102071101030c050d0c0914090f04021306081f110310031b03081809090f0a06051b0a08090d03090302 64
    0x1081e4035000081c807800d014075100c40c0705036090b501c0d051580010314000802042021401d80403604929503416604452000010300a10441c505001e00e1310704141c0c0e40401a180404101c0205140c0d410b44c94140d0f00761100c11108080c245060400c0000130068100ca10052085000840c201002901c82000b03c03001018041e04050341e56080c604220300031800c0d9a01c04100c1e600421070380592000c090900d441078000c114000c03810481a84003841c01d140b4091261180032030700441c5441c2d9a00f4404101440b0044507a401c3d140c58000c01d031050200310013003283c032010307880a404414291501e03044030f030092514400c42800b00200040400e1122400b400c40350f009000716160120722040c401c0c26031003500001d01600e00003a10744641544010386101c2050202d40307600c07082c0c81d660700d001d035038000100c010300c0141c01261032400401c600d50302030360703101c088456400c40c1100c405a8000043d4404142040800c4c014800d0040f451000c010070340306511103060421240c451074030040e40e50b00c5401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 878106303 1250 878105053 878105069
    0x90314070e0c12010e0c131401020c040c050d0b010908030c010b1c051b0301020f031504060e0907030b0408040504140703060f030f080706062103120b090c03040602070510020703021c0801 82
    0x400420f1249446c0c03822034403000341d0290342020b400e07101c011040c2c141500c070b15420b0051040c2c1c4910b407120b1130a40b04400c0e600340103440b01460140e0400d107000103410308070703180d9050081021002a074000107000911984029800000d80b600d007000400810305503059141031141009a8040300050000860401310041c0024805c030000411700000d0191060001120034203c0c0401031000c0f10026120200e45a60215001e014180d101c042070b690903082125121010741c00051304101150500041c96080b50240c000c0340d141c03a40351030200301038500d510040700c52000784108001425600d80301e10005840714030307800b511803071441d11043d81c1d1110580d0007520b01840002c4000030003d0650000d4010010390412140011503410445424484c0c810154081550942100bd0324400f6205840c000d00005140140d1a1103d04110001d80c1000704120762407a400c014030340229504010075400000310036005a0380f603400d440e0090405c40344011003070346508258040f5094a07040f901c0c00341560888 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 878107553 1250 878106303 878106329
    0x15020f01063f0804030b040209090a11011206030615061d01021f0e070b09040c020601081b0d170d1109090f060415180608030a05041203090314070e0c1201 68
    0x71582e80b50071122445401440f102000500004000107512024841d034001c84006260341d580484194485081d680010440c0b443c99003124075a40c0642142070b000c0d4440000014040e46964400c021151070501d41207422406120401100b580402c032080c0380c1c43e00c0c2070000b65218180b00040d40e0303281d10060400580d113550801001840c8554001c0400b078940b50111082c05030b4510660526611032030017180101e0400b40c0d0425081d0000505a040314004001050040e041c078035620303900b00c40c3e243c5840d80080d20180600c0807801901c00000104412240d40d647c0d010320020f024200e880200d5518802c001c10700607115240d130707420f500503407082d0403842c103072000d940360b80c0043c00404012070000071b600e105010108403004004880d216201490710304100c0103480d1018a40d490180e12600c400184040000b48004101400c0707070b901c0c1078401e040c03200b001a03e80ccd40b085e5840c0310034481e0b21480d80c0901c4042115100004102c0d4100880d81003841c40d01000d0341d0281c09120050140680a100d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 878108803 1250 878107553 878107649
    0x1112011a090d080c011e0e030705061803120c04090606140a032d0207152705070f080f0c04230606070b1305210a1815020f0106 56
    0x700f07080b03440343c41001c002003201400018100c1d441000c40c0016803c040e1425540001c02240041110500c3e50800000c0c6543d59880342141c0c80059200c40ca0b045600090050088400500100328080c800c1e040744c80d03407130f941008101d00440304268410340070010111042171b080340200d07007110b14800e002d1034081002c00c075170032184084c00154510a21074200c1c0710300310700440ba11a405030449034407a0a4140b14840035400b1581680d408002010b0040340c01c40580d00c0350100c044102420511480964640503592665241c00c1e21007a400a1140d030446242c135180380e401031041c009040c03422101006241009400c181e8009404004404074a941402041456449000b51841d06512411802c620310340186c044040940e20b1001321b84031300c2101003503402c0b00202c402d4444c20b1805418114101102d9040407540c00f02c40c80206005241c0c1c0d406c0101c0c0181560740e404c0c4462150742c00403c0228521a901400c60304a580120200d1030070742d218001801207078030032055980e1800e184460340c0300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 878110053 1250 878108803 878108813
    0x9020702030f0601121b080607110c0a0b031602120306010e0a210b0a0605010f0815030a0b241c03021905010506011b0c030b1003061112011a090d 64
    0x200050b00c5045209603800003038035503541010101154425103042c0041d80c01c21a6482d02c900031402a040143c2080001801030741c81820841d0b400a0703101d0880702c0020400c2c011071081886500103048000d03002040000b031f200065070940c242542407005003688002c000300c8100a00000c0c00103810020b291205410a030b4940c070034103010b804140701c5014035920304c00b440041a61245011100008040c0005020034694880d400071510103840b8000c0b00550f2a0044454075001031070740610040300001384100d038500b08000c4030110701c0b0710300a00443c00d20781c2c81040003150342051a205c6800e20201c401090721001450032801c01a4840d480c0c4510300d030710b0305a003003001c2c1106001d03485010600240c20702105401040c003d400a8031181e0812160b0980e4901c415146540580541030810040000451a001d00c43c0d0002502d034080f21200e0b2680c0c0c485054071514804200e08800c0402d81c20300003204800494010003000c0301c642005584004020741034054510030034418580008510b080c44 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 878111303 1250 878110053 878110063
    0xc070e070215100314070b120604020c0615031b010909020a020114190f052205030c030f0d05090307030c08030c1c02030717060a030b040501111b060a11040902070203 73
    0x2a8106880040514001803400c03c2012180b2042e00c1503504822031220030032012440304140d07080c41401c0713440e00140c0c1c440700800c100060091031b0003a900304122511307030f8410700c03880d0700a030321950202c42b0b550340000826141c41041e0344000b0756004001c000407040c2c1e070815610802c0718900c0e0005a00d858080b5801d0f801815010782d6444143c1c1804100881c0a99030031100326001e60341c107001c11040400780f8104040302c904545644024504034404000d40f100e03008030604452156046a28012801c6015030642e04043e0780d88440c0300000c6400c05c802512402203a030720040340e100840c11703c0090f0b1002060607640c000f016000d40e00000c0810030700910b038802c86a45c2550710412051400150f43d074440290b004880c040006000548000240356104802d01c0c098280200300750704190451311201d84918018104480ca0b640e10141311070006104400380c11f04000740c9003032040204100c42c2507801c01130000c01711582589010300b491485100c60b0305480c19154500001030301e6010b9403000c28600 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 878112553 1250 878111303 878111323
    0xe01110c121c020c0a050607060b030706030b0f030f0d0c2901061106042303090904050718360c2301030207210c1208060909030c070e0702 61
    0x590180c50403201850700085140c0744002000c1034181040000d0340c204c1c1c441c2e43d240e000c3c42c1c3c0700d0012601041140f0745a0090001079000f1fa03000141188403000191402400e5805000841d4a515075000b01e45403862450442c4041034020341150038114042544035030407100072000f0b020a11a0381414031503003882c45100d207886c03484a40003545410042d031007001c00c240300704000102a074a4001d4850008129035010303035404110f6440503035402d02c0801c1c1403840401000c00b203120600240c1c2460b540d50244a0049000b0340250402d1411320800c1c0d510103040840c080800c030700706441034042c44c3c1d20811302c048000030142c3d030308a00b44014501c070000b00307010340c0c01034001103030608045410040403295058000000c00749440e04038650b0015801e074020310a020b412010540740d072001111022100c0480800d032483c0003400000b071543d03881c84105e450700070400003c20356420000f15040000017036400400460055003400041c1b16038a07911810360040b0000d071030902e00842c03460b078001c0210500b8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 878113803 1250 878112553 878112559
    0x403140c070b0d050901090b0403080c0c0106090c020d0503010b07081e070c06020606010e0310020a0504080a0302010b100c20040b03152d070309020f060a0314090304060e01110c 78
    0x69595914211040d503001803c802050b90b10f0800401c1c00000d05200301034030726501c40c84d41d207010394032074800b5661400c00400400340d07441e00300080852121b0130311443c0c024010a4000060791400c0380802490b140c0044030180600c0300030401403010000000540e55841e5026000c584d540c40300024030b04d01c0d889075803038501241030b002ca1000e080100d03030044c0c08242e5003254220741407981e640f00111ba07030700c11425003c3d8158119070401e0815070055002446c2003807141c1411403615541c3c0d5401c13850310642140560060355500242c1c18145801c2d1181d10074104545000d0350040c5042d280c100e00394010594060b1420780b913500c0d00315191125000303010044002425a441d060011b60101c1340c1402c2140d9902400e010000c0c142e40600f910024502d25581c400710007588c40e0703903003c42500200844641aa4007d011103c05c1285642e0301c5e00802e03001e035581e54081f079003c12003080200f440c00b002c0c02030080c41c2c0091006001044d4445001e0381580401d03c0c0006403065420ac03441c0c14500d00342c6503150 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 878115053 1250 878113803 878113813
    0x80706120e1c05072d021e060703020304062d050a1404080d12091109070c05030406050d1821050d020301150206100501080f0601050c1006210b0403140c 67
    0x2a01c2c64004015184050180d100900c20090056180700790f91036078800700341400519021140503080480744c50750b00c80c00c81444400c190f0450400991030b80c00c14902100143c4c40010180b010f151700c0460b0342400e1801008000030146140481c0c00c202c3d014030510003c200011910960300ce1080c401100d1000351070750030300d65aa440c0e01c400d070307140ca02c04c110040206d640c0e00000010022548500c4c1c8466030424501c0140e050300000700506c3ca84042e10341002c000025094001007442400144001d105586595a8880c2800390050a1380c422340c0302907011010002614011070300c407401c040c0c25011800e407071400317001d4480c0341900d1601807080d5802c03040c0d101000200c9d080024020203c0b004682e502118002e546c1c0c004150610a0325000c4e01d80084d0002003c0761480301d1480b0304c0394001d08141805400c11080c2152f051a00911090303090700140c0710035041000340b500205d030600f884001d8562898101d003c1e201e166400c8030150004081002004c40c1c00030610041d003d9a8028a6150540e2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 878116303 1250 878115053 878115103
    0x70513060509030d080c0f03131a0402040606020c01080a0203060423040614010f050d1712010e13200d02120105010e0f0601020d0f050d0e0304030606080706120e 71
    0x140303076810035801c460107407088840100c1c9450044041d0f6204103074000700c65103015140b0741c00701203d03000580590741c5184100580d50014a04103000380c4240403402c0515003926050042009aa005900c400e0954200740343c40e18850340e1045034160711441440026a0ba521403038041401444109000c0700c610001042000898010101d000d009a000c1c0b4002c0c050641104084500342d0020712802c031002501d0b900130040c80c14013002c44100b4074040d0001071240852144124800ea2284c441c0075111201000103000944c0c03038544d1a0b41082e00352035400c03950a40c0b681c40c0e0450217002da031444d0341810010308098180c0c0e1048a81c0a40980c00b13040c03d00c040c000044054042d050030b010322200e0118000000d5602d03a118084940324800507070007051440390002c400c0e00c050030802c4422040140c10051000d8040d01409030b5210181e9010081da1303950f16500307203c000c80d03e0035001091141c10401c4104010f6500000380500e00e402c0034000034107074090024461518903265004482030401074685 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 878117553 1250 878116303 878116307
    0xc0b060915130f2a18030606080309011e09051c24050601030207030e130605060a090501020f1914070e27160909080f030c03100f0503070e07051306 65
    0x480050b01c010803052042e000700015081402100380e41c001ca00e446501082800244912940400303105c0f01998030010740d850361500c1040d1042034228144e0b9a00001d1842c085507030004400c83c80d00d07002140107145400c40c1000428190061240510819032051000c40d4407800c681c00d030b42480c0d8030110342c41907000f0403070b0440c1030740c006602e041200c140b034030340044c107954002e00861746c0f03841c0e15548010b42c10856000300100501821081010588c1c0d900340802c1d0758076408000c0003401c07100d4031401d008900d0040020714000240303c03c401e4a030080000c0e00d00300c5000c80c982c8000580d00c109000032a0701061003007850500e01da40f2a0180c1d440080c180043e1901411440da151400201c6004c042000c01c1102a664820401c005d4072032000740c5020004151590f02081a4910a0060318605803c1c454580b44036003055036280004800001444036018100c00b07120300528120100050862070300000a8031200c0c40d00c01d1040901e003040018403102c1c414000c58240710758880c03699080584403100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 878118803 1250 878117553 878117561
    0x3160e1003230c07060c02010e0a0b1f0e0105060f31051f050d0216060b01031d0703120c120801050102121c0c09050a0905160c0b06091513 61
    0x1880805060350262000541c801d045548500c0403500c55915044d11640c51900602c0721a540800315565080c202150050501c0031450300390080c0260442410041201540b030032001300b03001d1420b804044100941807128903c1411904200d8620351500401920003200e0720542d4201051400000564401c010305229101100146a48115503164842d0180f110311178444070390aa2480840250640f1035104030014010300d910441d0150800340401400c07031540101134011a0b00586610058a45507418403800000c0118404011000d444210445031203c2441c0000390030b600b2a03a4500619500941c12842c01c19840080e032492481a180c00600da80310070300a490040c02180f0207082c1c541501d000b55600b90880380d03038010b40814540141c0300208001c0c60040280500301c0400211a40c0780d5615500402801c200400c09140c42c403600104480c1c00c0c00004e05204441e41d100c40820300c411400c50707102d041518004003d841d5800400c10b140b80c800d001d0740c0e201c881c0d01c80340304030941c560300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 878120053 1250 878118803 878118821
    0x40905150a1401091107060b0f0d0302030903190305030c1608040e04050d02010b011d0d14060a0c080403050a0503090c03071d01080f0d080a020d0f060312080c03160e1003 75
    0x22110201c0e600c1c0d40b2034001360317028410041d82480301400750b440420b41c107500807045503c00400c0041d681d1481c1010540c542200c00059015030008140705000e4282409094031825180a0707681c07284c0340a42c0c001d40b15020192503040051004900c1c034900c0c419a106e40c10149400100350b07a16180d50f008200002c180446040b00d480c0076002680d40b005005000c3d103003ca600585a0303c03102c84c6000c000d54181014141c0745c9601c10041001c000c0407a0f20501e50b05071540042c0044c0c2540e161080140302078070f4038514840d0421075010100300101c0ea0100c04c1c0c4213050706901e0120340d261120000d031494810144d00030741c1d16004072200010200d10a42c0145041c5412640360009030703070f8603e010303500e898110882e030107a80c20000003a0600351281c90280c1d488040e0603401810400098500703003c403050700780c4221445680d0541801440803603000d0642c4020030b85070080d8545890400404980000f0b846c1c0304000c48180750050036603000d014400c01292001e44441e10a0113107203401005841d2442c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 878121303 1250 878120053 878120081
    0x708070f140a030c060c06090b040b0601090e010e0c0901030219090f080105040c0308090d0c0f181b03110f03041a0601111f090f0f050601091a040905150a 68
    0x101c081034242560084120f0b900000340c0c00c00300d45481415542240e402c0d4086132810b0792041a40c0009000c00440d0380543d00441124800d880c0802c005001c500207600f099440b01c051000400c04600008081d652000b1014609615880c0400051740680100070345199898101d85408088a41c001c0f5508111380303144071050360b9940d840c80100c2c22250180c0e8040c2c440f02c44075605001003519480149810300002d403034082810f407280c50380804980310ba04008000c1e10383c0030081292514180b070152440400c21b20400c14608c0e110110045101003112036424181c0381c802101200101d10240c5810010041c100303907a1b4034141c81c0810540e0510340302d00380f4109030f030340103c0c100394424110120300301c00c900003c1c00c901c2c3d28055020a141c8562010700c45064844000d8000248500180010a403045107524258040343c0f8001381002016000903607660314014030386040034000d031403d0b44640c0b41980e001644661600300380f0f0070410354a14410307800500700240440061340da48404003040ca00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 878122553 1250 878121303 878121329
    0x2061620060f04120201111212060a0815040501020d0213030212010506030303071823010806120a1704170f150606030c18030111120112230708070f 65
    0x4000300030700e80c040d00c445110310700381c284400d0014800500b480e0140c0740c0141003100d5070f8251202c0e0300b841c01640d00811035100b200421100405e01c50545030300c1d0028421034001a0b03442c00c3c085070702d03035500100080014611800f00401c050107000c4d4100d07414404420f50070356661039240d141c2596a40705100c2203019944a04c1545140c00044c403c141c09100e004000c0c52850b141d40604940d42e103003e4000c0505074103803000001e0340b60104410310b425482810b06102d41c0c541080009014850000c0c45140100421110201d907803102081000c11194000115a190012400c00381d1082c0102c2d00008140e00091160072074201001800e040c1080710402100d40d924504800507107100f070140c8100b50460001c1c40464403071340c0500302a05c0c0c442004011520710300300050003c4d0a40b51500c44a0001e5400000e480860209515225000d4542e2402c2a68100c501c0d40c4c0b8009081040c402d004000600940c00c030051007000d00c800001000c03c903080b07402d210345850409003030054500c11014101e00f0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 878123803 1250 878122553 878122613
    0x602010e060603010903050306060705010605060d140f01080c12070e10170304080303040f0f05060f09010b0f0f0607020a0b0c060a0606080601090b131d010f0e22020616 74
    0xf050181190040e03240e50380303e0840c0c5480086c04480d8120f00000c840765500e610300440c490b1070b2140985100007021002068001050f25400001c50014007a60400116000180b002004c002151482180d0a0300c00207003c0c1420120a41400c0d9035400903510108007806000081e48407140060546007110002001c4a004020b40c96032481a13100700c0c4083e030010300019001c24491030800c1c0300300f0b0040f04411003c20b0303141d80340d500b060001c031407280b003560700030702401201d240c24450b00802c07420640c0c00f44102400320001a00700500c1a0740341e4403445002a0390021503c4e0b000c540c0340100548800c89484521409500b030700c0300720072a207040285141140008500c2e00c100040303030103820182c5401f10098204400d091140d07020b01d0b10030340c0c01c40403490001551042c225401004010b84840203000d54103004100c0c0d4070180c00d5204010007102002400002c5540f054074014a03a28040112001030942c0b01141040c002e42441486004081018000f80440070952220000b88044401d441403c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 878125053 1250 878123803 878123809
    0x5190b06130302130212070207080c01020d0c0f050c090a0b0102191509030311040305010207060f060e01120c050907050d050c1303033213120206030613150602010e0606 74
    0x5548041500c8501e00300d0100098203201c4109070a140003030704050714101c8009030f04012007100baa0480c005a01101c4104070408013441070b001010003d1001e080104030700c410080c40c10104140103405450001403001c1004000c010400305a840030389100c0c03007842c011401d10000c2004004035800750107000c03004000c032004129402101c951004a08000800901b00700c2c0c01000500c0c1c044044c550788001024400780480043d0000314800e0340007598403450f92500005440e500300184100c1810501c00707004401103201d005064401003030000c40603600070b0034401000710343c50f80015007103000b10050200d500c3d8868014003054a00c1c1c0f4091050351100e07120003a26110b00740000820300884041840004d119405242042c00751001c1c181d000b0020741901003071051505010000380000280004606c20b00c6104000109075114a4200b2105070b80c0204002d484004c280520510303032084040c4080308154062178010801c20600100c1341d850b1003012f4000c0000030324000c2580b01e444001a00c42c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 878126303 1250 878125053 878125057
    0x506010e060a0509040b1801060b091504050904081305130501290d0f0b060a0207080d0c020d020402030a090c03050304051e03030703030c0512040b0f0105010513061d030105190b06 79
    0x141d8084c0c801c143c1961652901060010050b02002400b5040c000450010009009210181612040c0780c0e5480801404103c0009000c00c000807000d00c09100400c0660f582c08441b96001e5080030800350340c0d602c406403440c170341d5142d03401180e40580300b8150442423005560185042c1d844c14150404290450500e07644c10501c050040b514030340701040480c441c0126074010a40c01c6042103c0818451690700005050740c126040c15401a0b00c014010810740a040091950104045c2452400e102054001c00c0d4403005c03000000e40581c0c4c0000105020360031a42c4003103035540c0c2000c6407034812900c903e8400e850b80d0151003001e110319001c1455030244d906510041c01d044e03500500030741c07904449a034160090481d550303543c3c040c0907003401000c1e801c41c4d4401c0d01c83c0c810b92140f030009034a40f506c1003540c84601010380296041007030a100300010740410030010f000b510228108813041c001c680703802c0c400c2219003a9001d90554240010301c0b03800b101c05040c000d043c00d00107a05001c081d410005004441c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 878127553 1250 878126303 878126309
    0x160c09050a060630020f0301140f0111060105150d020304050a05120f0714190501020c01150b03190b03191211031912020307020c0a0902040b040e09190506010e060a 72
    0x20134103800c0c4180d9016001859041c0580c0400b40036003041100548080c141d0800d80c4074021840440c40600b109250180d1140c26605090810440c1c90344c84540c02d640d6002c2c1409081d010700c1d4410300e0b00142000041c240c81ea070342403e000940d5079180914015459030824001241d140c810003040c401c41118032419207050b6484007a03082e041010781d441e106007100e0040b09880b00d500428000d40114001402c00b0f20005020f04005a55450140c68240c21900c210060000a01000e20140043c1309070b02c040fa900303c101214500c80291840040354000c140c01e00032941c3c03511620260407400643c20b07107000d4600740101c09002c0d250342003890030b85e050a000160010300f9041000741c101d01d04404585004141c0c4145010b41c1c144840300310007400c90340107540304005070b40084541e031003e2405044d201c000c1c06100c0e8082d800d051801d0226180382c0154010355000c010f0410000c0c90481c01004419a408082036241000c0c00880c100350f602c030b4200b07008441411740c0100000d009401e02485990407 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 878128803 1250 878127553 878127587
    0xa031e1a131b09020a18060305010b0711010201110c0120030103030c02100e090a090b1506090103200d021306090e04031b020406030501050601020115080d05160c09050a0606 76
    0x159110b9440407010905039a10070003000b079125000c1070700900351000d031110810300d0b200c1340d000480d624000503089049030700c00810541050f00610400c1428015120340740d41c0300c1c001c89070325985100140e0251a04924200d0340c4000814010055401500311606600f516010103c12006c048900326142c4000d0102601044602c03c98500505041c080350004054078079180003850350b00c1000890003d0240d031940d00198642c1d8180b0f05110f02d5410303644c0c00c0800e140d554216510540040b9000b4000d16100c981415075581048248000300d510f01c00310030400d03c0140da0344030b400c0801100250009004c4508048011101054082c019001113041d01c50340d450007561541c0b5550115048419240c0c462020398041c0e501c000183c44900070304029520800c004209407800000080c211910302072440026024a5002c006201c0003280d85141c1611601d80b06646880c80c0d85a5100400160b800030000305031044000b84800341d030760040d40104200d000a10001d075459800300c0e211201170706460b41c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 878130053 1250 878128803 878128831
    0x151b0905150a110303130201090905061509040f09050703140a08190e040e0718180b09030c0a051f1a040f0b040f0b040f110a0507020a031e1a 62
    0x1010381d0058015228202951614101144802c141103046410540c0ca00861500894400d0110b41e040341140300a006524401c01c15460500000394245400c43c091804466001a00d03403a02d880d20b400c850502034100c6000c0c4082202c900d00303160b4514240c401550049030801c0d444600c40d601080621146801c41081411301040c6140344200700343c04140d100c1400298146800c00d51541d02500351040d5112000d000e095150040c403d40400c501c40031052400d14054403d80001c00c00d4150b81d600d580c100e04046031695600c9032651842c80362450a402510900e6500810000000b8001224980707002d0200d00142c0c00341e07070300415540041e501c1d1046402e402c04000e917900301a448503100b100782100109081e202c0c8030209007161034031001a02c0303194031546001ca00c0e05080c05454a003413080340041200406070302c4071120354003a5041c441d0810400060900942d0b494082010182d9002490124800008802c030300060088810458040800f56a450211300e4501d00452144510310b0705c0c07203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 878131303 1250 878130053 878130079
    0xd0c1b08060403180312050d060609050310020918010305031801081915031416050f060313080c060106090603050916170106170102090a0f030528151b0905 68
    0x1a40000c0404071500e48991075580001c04200700504105078007106495941d23448030702d00003410a40f010b6421a1007448541a0204040c0d00c002621102102c002c02005840755507000008080b07941c01600c400498060000100030b10070040000d002c0d014a00c40d220365583c0240005441c800b4003110400191114200e44e4100240c1c690071901003180468010544a03840759190741c030504184a4018541e48210307018291240440f0140d40038150407074000901201c1500040d041d848000d0000368080060300401c81000107050981d109440c445080c0d5026684030500100340101c00d2007450300090601c0082104440302180c100c01d2255942c0100c0c0490f420300014000600090003500595941d6103000140c00300321000084840b404c5038009aa25039000040020901003038025141020f01c4203410000580000781280e4012440031103624104032200e100d41c80d4000200024044801c8202e0f601380d2308516078400c5d440c00c443c41e488164100d01d0007000311003031415030140310f80000740c221600c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 878132553 1250 878131303 878131307
    0x3020c060a06062001020903101508060c070323070b0717100e0c090a0806010302090f0702060708040204092415060503010e0414120903012703200d0c1b08060403 71
    0xb4003078055130000050700c0c06c142c84000c01d2620001440c4d081c0c24a0fa10f10342e240d550500310011a0090200900402d40742c03c14003107403000d80c0b24800c002001d0000e03032441c08401001d002150145900301c502016107038011030805410f43c2904844102c00200b48450700c807042440010903901440710100704100d1141041c0c0c080d400d42e0780c040c142000040061104e201c2503520400688040e00b4450050f1102e545140705000c0e52900c003501d160a82d40d102400c10078143d80c00500e441d8401c4075880c258940e0b0f122400460000d010200d4040d11807000c5101145d07003114100c1138103600701c43e2104c00b04620078004288074060713507a0b070090400040703007000104400000c1e0280d043d081401503040340c15501d50f01c4203051804000039880203401402290040440c40c2c20303c40e0079000e20485007124500c3c0c000c030850b881240c106403001020700214400c08140b540ca0160049003180500c002c03201310600d91170010305901c412980850742000c28046482080608007040700480d10202c00030100c03506c1e03d940c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 878133803 1250 878132553 878132597
    0xd140c09190f1e0608070210150b2b0209030c01080a0605040e0601061b0b0711010f0617070f0f031e050d031a030606060307030f140703020c060a0606 66
    0x3520840100d000700225403410242e10baa0000c0490309010524200e840300070110010040e444074060000078020000301daa000700e110104d0b401c1c0808001010030703410a0400d01400d99030481c40131154003013214801c4881c020303800f1008003101d01d002900142004244026442001e03c0b0740e40640186a580c4910b501905010b900f1094482020541c030392682c010030704681a0004a40d00e40e8400c5004000590300210045600d40d4001c11000307421000c3e0311560003d01c4060714400070010718104081c80c00e542981301c902c0e252521801480103580c1c4a405800e001d0075180c00c440c817400344c0350000a440036500c821100710350794000350680d02d5145496055050240e41c6191032070b4000e40311940006034051050b90351305500b5880008003016183c000a805440d501100c2c0d020f9441507090110035900c810589901500500d8007068642c0d48030300c0003000d002d40203c1085001c4101040c450707115050703005001c024450204841c880e90340d450680c0180c4081d4850701021030032070181400d01c0109403035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 878135053 1250 878133803 878133829
    0x81b010207090903030204051801080c0607062a0e0406080d05031e07020604140a030917010603020301090507330e06090919060b04030201050f03040f080705030d140c09 74
    0x15074074815039403003920b016910f1014048002950014040c0401d01e450000010464101c1c4903104d00c0e581044111983c4665200c0c000d03100d02d8002c54010708004946d04404005400c0c1e4400c00c00c6100c00c42d001381072913119408001e0200d0000038015884d41000d00c1032070225074000c002003180498009042c5c1d411380c405030050184c03400001001c0f0154405070340303050107080d02c0d0340245458907280c14000c18881d0000e64452407900601401008654842c0075401628200304002c004600100300250040415600c000e4165091200c104140a00440d00104a03031400020f0488441e880c0408035244408846d00c040e40c0b490703420481540c41c030500010141e074401a20b043e21706441000019034440c4221029000c585040002c02030f00d031442c5c003480700200307090200c007400c140c2142d002901c0e9028540002d000c2c0c440c0480040c06222900c1d0b07001102c10b170003540440c0d5400c0c1d03c0c20f20907140c3d0700103021440010301308100b51030107002541e295485084000903090038051060104030905888003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 878136303 1250 878135053 878135057
    0x90c0a120c05031c0f05192f06090c1002120c072402010c03111b01060b0f03040c05030c1503070e0405092b080f040305040306020d05010e0f01081b01 66
    0x41002c00c2035101007200d01c140c482189820101c0e8510350300018103081c3e00c540f010080001c01d000c20403206440708441042007405e07013001543d40003030004000800001c1600c4554078180d034040b0000013000801d40034021a504c00503540000d080c9000d001d46407280c180140300581c8246105d00000f201100034103032040c812015502002c0d03a89024400d01c00d003204069003d080003992104005130241f2549041105500702840700300c802411842090040352804100120102413222002c0429444400075001c1010542c2d1a401001d50a01d00c5820840f0110b845080203d404119491b00140011010900503d869509440c400038450305401c080e20507030604c5001c0c0307460716036560b9501a01c1d100e07100c07000041444010602d4070303058040c8140941d800345440f10030700c2480d580d4050071240d0b1009043c40c0640c01c0d43c4a038502161144940d5002a009510104840d1901e1080360000e9040310200c9038008003580311300b03011840c207030428800c410705980000384506003102c68544d03c0712400014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 878137553 1250 878136303 878136323
    0x9060504060b0c06071b0f06050f0901060308091306030209131e0507060318060c0f0f0e130b061c06031202010e1f06032405011e091a060d0b09090c0a12 67
    0x560759091100b514050103c038004d84270420403500201400c1100d0740407070008000d100103440c5448100031072040d500c1c1e15000e100c8100e200c0700000c8a541142c401541e010300102c486150003103401480c1c21203410b049400d152610700c000c0c14640080c4640141d01d070130201030410240f400101781c00601a0322802ea685590003018000401c13030340d106941984c000d40e11040b07582158050010300607164407002c00140049280401d91546a1144550070303149540c0300041d00c0114500010308901a0400344000b070900d40c00c101512124903008981124410700c1d012400a200c1d82040e400d1301c400b12045801a0300c400c0c2040b0f0f5643c121652030640102403200000c0c0c0d180c590322090003400c40352a40d10701d400c48400181c0280c44062040f00d0041402c0811403081504c0e0040c605020320492040c2585141c4035603102c08404614660b02017103007801400c41d965204104002d40103481e1351194940b04000c07a80c00034590340004246107000c100000e11401025080c2006603614070380c0341034152046202 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 878138803 1250 878137553 878137607
    0x3030117120f0304140d27080601050d02030a050d0504140603010e1504180614091c03050901020d061413180807080906070c030c050a030c03110310020409060504060b0c0607 76
    0x1400007260131b000c035075260110002101070700c01c003181d002c46200c002c2030b8115400f04095200032640c00c0c1540c03003c413640c02d080705640c00000d1901c0d0703001101400d40c1c01441651a000d42e0842c00800c11074a420300300d172805035200001c010050000344075580c150a1218002280b40101681d40805004010300010300c0c105500300c0143c007900303284021101941e0319420a00d40303c0c0040c080d00d0b40300030100000c081981841810301c2ea0f005000c4190410305450b2004221075400070b406840440da6690000c1084658401441020314500041c09000f20050300103202e014030703140603880d01410031084840b4213070f4482d07072407841540c0102410303621110203101402d402d50313400004111007030003450864041c42c03c41c1487e40300650310350f21141c4520300c0f88000b00001481a080507080341d40040a20000181c4070340840c0c240144408a25542440054081200c07a141d03480030302a580266810005107865a0030f0301d107641b0882140c0b9907654803403000206000d21420044540c030342078500b5403d103440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 878140053 1250 878138803 878138843
    0xc0d180b0a02040905090f0c150702091302040f110a260f0f0108061303080a181218030c1518030b180303040209010504110c06040503030117120f0304 66
    0x2100761140301c1800d400260800c1103403110f00403550082020030280404424640d011a80d6007240303a00b43c0c0c000d90b94249844000445003082c0ca0b082a0098184192490401d1a5600f64101288224420341c5803441841414409200f0780d102e654101c142c0600e40400b0b0f040c1550103440784014034a0124200f5072192004807030102e428042c0c101c2212000c19800d06e0107420940820580001c00140e1004040200c411402202003081907014204269252110f10035440540082c004803a588504c0783c0b150000c00c0030601c007022a40d0b000c0d954241e28041c5001748145030519905c030162462010b5041032090000000110105800c0350030040391380c0c2a071034a009000c2d41e0591003a200540c4140820600c99036040356103d03e1072130000590310350728041e40022005801809814015070346c2c0d260724240390085904484a805489044556a28003407408983d03d500c24010035000c010401744c02004400c001076488041103036280b02a081101044c0368100d140c10060065903c0001c10000308071040c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 878141303 1250 878140053 878140073
    0x60c0f0f030309010e0a03052a0d0c0203010b04090f062406090519060503180f0a050a02100206270309041a040606210e12030f01060f02060c0d18 64
    0x88503480165480740b500c0d040150848280c0b001800880d04038091034030000e58080d00b100d9030100881c807102c1700e00b40c4c207405580003c021011203203c00e10410210002080e0003c0d003442401d4401c42c021f00c1819000d10501003941c51b100c2c40200341e00c0d800d1000c0c2d400100c035504044058001c41c4038500300c0d010b04000080710340080b0340c80303070700800d0b4485070600c054100f07141401803a103d0300340c16010040c94058024002e00c0700405c210004422000300c890000300500611420300e41400441c2c081d11120300384152111454034040f072140b803145540c0c0d1041400828071038800c48203a18061711100c0440d442102c0c4040000c1d201c5020300003040a07071032030f40d075a208017400ca5041c2614120150301010601040b1190707500903909200c014803640602d401e041032074501040d0b00c924003107541da00386d14095140400c610031485418001004002000b10710224060403642030355175141c8a00c44000d0140d03100e03581035619003000e80040091000c00d0b4581c0d0440e6030075124020704000144d184d80c8032000c1d01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 878142553 1250 878141303 878141323
    0xf220b2a03010608101202120a05030d0f15060c0209090f06010f081005060604140307030b01090203041709030628090302010b0a05040b0d1b0e040825030e060c0f 71
    0x384030201c014000c0c02c1d0b00914180d40070071800704443c1d40c181080c4c0302c6200b012840100034440c44020004c03109044042c011000f1050b0300c030040725200c160420701c000180030311703010004405142141c810399801040540804858458503410100601030f02800003c25004100390001c3c862142240342c1e50408008040c02005450f10140080703040c00402424502d121044880941c201424850a40e0b540e0b8111400c40d2030010354142e0180c2440c0201c4d007001ca01d80e00c0a0199a40c0400020f84401d031a0001d41c49a40324807000300f1440d14180520f01d0078010030380d80c15055480400040c103034081c04e205080310001301e40da040311401c00410790001a02c1c1a10412401070751a203420300305034109083e185004c0d0008035410b020b02030b481d001103100307058a0200581341c54280d07543d4042411042c01050701070182d4800a4620745000c2c1003080c0c6030b9101c04802c01c8074001e501e0744070304c8640c6401003803110302d0340c5907039902d01410340d041c100203090b00000103804840c0140740c0300c2084e0b050100310758400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 878143803 1250 878142553 878142631
    0xc07020d0822120b0115030b0306040c030204200f030a020c06070210200711190306140c0306030307150b0a120203160602070b03040c09090602030f220b 67
    0xc0c003000355081c01c2261800ea4070003c008a410901480010140c2074541d041d566018010112603000e02800c4000e0802c5902e59909405540d082c0030501c022602c912054034001e135400e020304081080e10701000d00c1a0381030518034035400c3c01000e60f01d142450055401c03025038800582005210042c2c98102103003079031480c0141c4d0282403452081382041c0644c0030400040824900d14516803010225076100d0100000c04c2c0d01c2040d148451140e4400103900000d401c1c202c445c2a800707859140100040000b030003050400f018040010740420400b904580c81048003a02941c106000e694422040780e102540c241e0003240c03103040e070380200e07201d0355045001070440b0f040007102031005005141c20000c903815018111400120144061a0002030400880d1128011960f8030707550703070502551488039034020103001130030807061406014041c0c01450041412901d940c00340c2c1c4950703c509121030030408030489a4490346000001007680f4045099003d0040c041203000030000c1c03849241806103119106070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 878145053 1250 878143803 878143837
    0xb030402030606011b0b090106151106010902090604050d0c030209150112020703050324060301090b100e030d0309060b03030301170d0207120236061201140c07020d08 73
    0x419481e00304160740e0800700a080c540d00140f000500c0280f14081040094401b4410700d000c24024003096001c203008007003101201000002e101c1000701b504036031000c0f1602c980320380c0c0c0000c206006244200c07102a44003c0525181c14034000901892001e204004e0700c600d0b40380240000561207642e0814859640f054400480c005100000343c40400b04112600016105014080010780c0000803241c029204120003044001c094040c140100e183d442895005480807000051a207503940190256031412290000f15404c2c4810860f0a251240141c030360540c0407a9103000d00741d002c0c2d401019894092240070489914181c040303441e6500a03485281307084c41d1901c40c000c3c2c2440c10b1088914241840c400b50540a00e408110200e855007100064480c6078101c0c851417403031035100c241600490340b80712421032a040e00600542c035003000b00d503100c0c040c1c1d00a00f5600c90a0406100c0e15034401143c154a9205840e80281c11045400680080340c120001000c0c0102184000028004403460b190b5482 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 878146303 1250 878145053 878145061
    0xa0303050415050403020a0504090224070606081c0503090f0102040b040503010b1e060a051207020f06130c090f0207080c0a060615080a0509070f030516140102120d020d060b03 77
    0x18807018a21400b110810100748424001a5140b1070890211481182c0c08941c2034440d0000822a0707034a0421002a5102a80f0343c101d22200b079400703009118040c400421806955040068032981070808005148200c1c407130750804103001e40050754005141508582410b04214403540c00ca90017508844000c0c040440c3c10400c1740740900405d10103107819203080040100b80101201106502c0400c680b00703800208901c1c5240d440750b415203120031510440c13846070b4103114501a4803134101c011500c81e1402a0300c0000d501c0d4106003011182140e111855410342c51030310f01e00c180101203096640c0c8060340c0070002c1c08040b52030140580120300404c0082c1c4441440c0b803a200b002c8980d641d001c030140030642e400b04e8403510340041129901c444044c3c001700340d503a104012281045000e07001800c00300d07000030020081c410001807907040a110021608007251325a4100c5050700000c0305040d0041c1d000c0c003540b640301400e2001811784a007070000c016007090070440700d000c1540c08682148900701c401200304 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 878147553 1250 878146303 878146319
    0x60309060612070b120f0603030c0d0e060d051303030f0203100e04020d08071203061d0606031017100b1225031a1614040911041a0714010b060702100e0a03030504 71
    0xc11f402602c110000e501c0d0202100a158951071301011860500054401003000c039100d440446200000d0341c0401c03c081d05d081c50b1000c100c2586610260002860000c00d96a2001e0038400c0f64010442107903c00390140c0b804400c484850030082080343c2152880f001074001955213030150400d02d12881048a0100e0000c1d002001c480c0d8684c0f040c000f01402e20f00ca0304241000d035000640240090301c1e0a5901e42c0c50140038003810301039070310180c00046c07030380a045a95180480e810314484000c070001d2041007400300070030418001c151b18503581900f00d090402a040c5000122285400b0340144c0c0c24100c940c1e03034450080e04142100188211010b4100f04000c1d01180c0c1c4041d030b04000e6a0401011920400890500c40c4c011801048141c40d0746240ca8003525035500252001403d00c0030340e0f40f10030189108000240d41010314115107141c0905148040c807032041c0a0644191301c0035141e02e05140454003040a003002c80d15504013401180000b40400b0340715102d078040075601a40b1021380d118605068 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 878148803 1250 878147553 878147581
    0x806151b07051801030210270303020304080705060909280207050601051309031403090c1315170a080a03060306050906012619060b10120605060309060612070b12 71
    0x4401c0070307040f40c00188016900c4091083c0b20006c0d914101001c1c10080416401c40c1b01c0388210f4030303186408402c00004050307001004006461509007030311036859507442440558003c816202c0d81c840360b00c03400640f50000302c580c0414850030007007140c1c0c2440307003060400c41243d200c0d00c01070f01c0d150800b900501c00d43c00c028044030b00c0401107030400c11102000307850081c0421017200c10040c242100001040c988401000940d1520300d00034081c80c0c202e802140790354000c1c080d400e41c0d11081c180030100000c24041c03481c040401c200c0f032200a032007030383d200d5078038a03040d039009112600a00d0792342c55001c40414841d00c20300b4130890610006102c2941003600c40c0768580c10020341c8203280c03000402c80012104001c600b11060708119141c4080c1011985840005480190300c0d8580040310010040d10030359001c1c079183c40741607550404106c841c4d181c40c1400601d100c02c449046060f84004d0206e00340d41409500e14045004d4002580c10458569024050700c0c0c0c0606a1243e00c2081341c01440108108113038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 878150053 1250 878148803 878148829
    0x3020f0d0201020a030c03110d030506031c0801030f030315060309050c090709030809060d020a0c120206221104050a090203250e15040f0c02010507020d0806151b0705 73
    0x16030300881005a40003e540b001d010200034208000c1ea0020070805000d42a13004409084006444400c0d01c540401002000100d0f450341c40391164140b058800000c440300c030818000c0b10740e02c90b10b003a82161210100c1c00300c004030840416681d09218880c4120803100500504040c0d940490a00710780d080151a00901451080c41000074805005609401081030400c0340c2d40030340030940b03c0e8002e5000030007900441501c007908600002d6a0403003981e02400c040d000d144100091490692901000c9940e00e804603401e1140f8001d14402080d4541e400201a165a10075071a2000401d10080414107445080d9022503006031181018011880d040c8180d0208903e81d02c005005800a94100c00b001d50041c071404a080991402260800c00107409100b60000058014882c0c903c07100e000300000c04000446000651a00e4041000075101080c514007140a84d5200103e076250081001042010303801c210341301803020003850f001d004004112441e0603207100003401e82c0301e00c1e00d824441c00580e200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 878151303 1250 878150053 878150059
    0x1b02150108030901030c0e033a05030601030905160b0d0f1b030902210303010501120213182004090c02031e0901030b03030c010501300809061c0603020f 67
    0x400601c0070342000030a80742119801d1074089584d0a809034107599141c09540784a8040c000d515880c1021105c00c8a0301c0c40301800e0309042c20324a01059a050002110103c446000620400120300342d0743c465003181421502410603208a82001095400c0a643d2640151141540030904041e04421442034140740c50042009021310040c10000040090941d409a010b0542d10010601551200d0417441d201282d41001d5140058080480319540d4009104450010300010041c00352180c2030b00030344050b280c40080c44080c5c0c50800350010308404894070ba45410980d505000c46407200b0303159288820380c1c0c500302040d554074102002a0140c8006004500a55104001180310f009030b0240000d03200901420481d00c4012603801200948841081c050b414400032a2500c0940410742c8400d0484e0801c450a03000c9210f014111119481620300000e44e5164480100c408540014000c0c0080c400c0101064548044003603184a502c81048000d41c40d180c1e02c907801d0045040541070002440421 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 878152553 1250 878151303 878151343
    0x60106030c170a15030809130c0f200d05070c090915020d140106081006020c010c031107050a03050a0614100506130b0c0307020312040302010203041502030405041b02 73
    0xa01000c0c14001810b490342039800075580000c3c4104605034044540981070448180c025075403424009050741020850520900c070700c5040c06e0850743d96214150380c1c07401a88842c40d5500074000b05403585211815a2140c641c0319080d2001011070904ca01403445100c0d840e426114402410160100c08403a00b1181c0110310b002c0121000c1a408100c0080d40c044815004d65180405d400d4a4050107801e00c03040d21016060b00082040d94000a450b4800c061072400100340ca0303501d800480e0348004800641d40816842000540443e00c565079400c116541e07030084900035030b0799402040e0030000f0b41d4010340e860382140d64128100304003400b07200e1154035801c030015039a0410301041910301095103c4c241c800c0c080060096001016407203040b00034028030b1080c81d110002100007a45a81c00700104900c07a001c0c1c0c041262003003074014262404c9c0e0350185d00450605062001c1218004005500039007507100912000502e030359540582400c0c41c20800d01e02403916071000000c1e02d007122880c0748280006074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 878153803 1250 878152553 878152571
    0x1c06050c160602210a0e120307021906020408100207020906150f0d0608060405160803120a09021306030c05040f0917090a0f090f0c0815060906280e010503040c03020103110d02070c0806010603 84
    0x2002454bd15010201014040981001e24003200248200d0780300002c180115100e9502d2000d80e030340a0007a4030300903079480b20555200301c1048000c0e100b1384c85404068100b4804039a100d070b8820003405180c002c01000040c416147c0c15142e283c820200d5040761254040c6440c2a0400c00c181c00079030062424400a5090218410b203200c5c0c413081c0140266032555943e03030201c055507510185c6a02180d440c502c01c0100359101d0034440e41480444c001c0301e00480c2440b449803603a54491003201c20154006950418841d88807110800c10380c42018001c1d8004010400840c1504003100003800814808900050310801c0e0002442a038081c01d0341c100512070040304100d26840d6500c520f00700c0040407a8469540c05501000a42c0c80c022482072442072a00d0f0303240d182581507180141d0540241540f102480b00f8a14401110035210443d002404c40181002c00c00040d4000d4200802840390006441d040a8501e1002000c03070b0031012060740c0c1d00c0c6c2c81c02803c01440c04207104171409424246002e101d00d1305c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 878155053 1250 878153803 878153807
    0x30c1f12090b1b1e030703230601030b060c1b24090a0f0620120f0d06050d03050414040b120d080702030910080603010b1c06050c160602210a0e120307 66
    0x201a40c04c0706a8450020005929a100b6440b04d80f02c201820342d603980404850031000b103504411240c80b8013081c03420200c40100d1030064266008036100d5070007410031140940d00c0f01410034054071120340040d08071681c1c9c00401c8501091080001c51045c000d502e075100303a0104030b1900e07207640c80140c01600484052080c0c0e0740c001c0301c0b1040b00d0100d40751184203148640d002c40c5032079500a13a0a903428004950080015001320082c4507402501d0340501c0f16030348aa08118240b40c00c1080200030840c10881000305021750a4a038803d100e0081c40011910183c501140c690610300a03044a950440350603014100c0c1c200025036000807c5100844c18104120042100c41c13011400c0700d001c0c80b005030700040341694250004d00001d100a00104c3c4040400f154400754103e00d0041103d5880c180000601c01c0366141c000e030348440d501644142018042070716400001e501404041404001068541000c8260b01211601031803040000141c2410240201800c09075603d1409443c41c104000b03101c005030b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 878156303 1250 878155053 878155087
    0x32a1531020103051005150d111626120916151805060c0601152604080d1416020105160e030a0b09010c0e030c1f12090b1b 54
    0x164282800501611000700102e4110f400303074401540324007070300c101000d0461440050420540802812702902d040c8000c4240a402074000915040c0304007a8190b000c9141044000060004040d40e003540114140c80080b10b80d0028000c0305445640005228412808221140280f031352510902c030380c1800c003600d6207128980b840b9540208819148205195074007078017040b000f003000030b250b00d0365a4a2540a50349a441c24130440d0b03001e030448001125040d0050080c1581003d001d08030181140100b038036a128140c015206440300d040a0007402c1400489101c0c503144820b2a2079010060f280030600030b0390b00328007151104d046904100c2404020b0b604041c8038101c02d14103090540244c1c040202180c902485214040c16446851b028001c01200652101c40c1c42605542c5111004407140c09055a07881d484c201260000d04e204074140540590b02c500f00c0c9028410b1410b4052012007201c00300c02c1d0fa450342070580700d2020100601c25a82c400c608658404080629124100345001485e02c06038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 878157553 1250 878156303 878156401
    0x10e1b040b131a030a0b0703140915100522050c0403030e1e100e040605010804031d030f01020c03120a0506180408070f11030d11032a15 60
    0x1858944140c40215054a80016100d69011302114032a8202e0705210a50301010340c0d282011902e0009880102c80a01c0e0029108056980040041425030800d104d80240b0003008032059900146021425503030f4004a941c00058150b048021007200501000807641c014080c00c0800c1410002000003e80010001c00e40391400c4a254a03070558003003c076150320310402080350b8400071904140407121f4000440909004040d10100583d5413641e0040d6041c550640c0c0282c041801c1c0358003170140808640702043e50300300250580300100c00361040b06003a60040f4589c440c0a401c081100c00c4d4541050210350350140209000340b110f403c107180820350300502020880300302c0d104c103c00101446080c03021070395020b0348608007480c1c9400e64103080300f0102e04496014444e00488a00c210442c1c0b050800000003903602d8059031510008072100780c0460303091000d80010b84540d20100c40c45200a01004005000214241c64507181014400000da042c4601c40e14244108641e003514156800381400c202c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 878158803 1250 878157553 878157589
    0x100905010e1e180118050c120915010f06080f130b0a06120c090b010804200a03050d030c021243110103110903120f0408010e1b040b 58
    0x1005030992030380381c00b018001544a401100542203800c035409003d00c0c2c94103d42090f80200d480b150010710100a44030266894820001c00740500c00c01ca4101d012080c1e0003442d080112500d002c40851503000340402680402240725521804103c155005111154000000705489015140102080701a054886005001002d25400103030360f420480d4815800b400c401e0540c106802601d18100141c40000d0041c00092401c1c041a104c4a50041aaa034000e55000202c07103880c08460354071401c5224030f490340c40d0b449404624000301050040c44082007001641d07401245000c44410702a2410540c2452004101e02c1003180304c40c0c0007218008511169004024400381c1c85600500d080306885a0650708010103484103090104055140381192190080c2c03818801d00380c2005030404103006000029070140c0003032040b151441042c40040c1041c0e00f21444503401c01c3c1d10303495800c2c21a104646200e00e66480403442c00b05c0030f004050b00032180002102d00b80000283d04d400702d000407080105070a0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 878160053 1250 878158803 878158819
    0x2070312051b01050903071509020f0f04140405030304030305061c0308060402070812040b0105010905030c06301e15040c090b0d0203010e1602070e091c0509100905010e 74
    0x8440410503441c0e410840b55800240900d090070260242c0300e0b41b003044126240300c45103000c03260041080c0501251070307400a00340d40c68140c140e02400740c44041c84001990044d994001464500000d80310940554003e000541d103030300c0c10f80f5010b0111000601402d100f44441d00204200524082c1e06008266051410700d60646804000c900680256580113143c2080072982e0003480d41c03ca00d1262059004400381c04036a44e880005440c038403498084d0907056005076007086401d08100300240311210808ac106a5230340e24a2134241c52a010303d000c840d4441644000748409000504400d1040301d0060900e04818240411409468069400100d010f541c84682007890a40a484014010f000c20550f082d5244080c901d100c009500074015040181520404200c2c00340d58681912442642a00103103896400c00407100380010b4020072611861065042c0402d6410038541020760b04c0b000c03621802c2d00c07143d0302c03003c102042c20350095450810203090720070020360f07031312503a1429606000d0b20051 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 878161303 1250 878160053 878160067
    0xf080d050c0a0b0103060212180d0e1c0b1803090a14031005070f080c09030a02130f020a05191106060d0501091b030c0914191b0f09060207031205 64
    0x1802d081e903945001d800f40000b04000014400540c000306007140505d070044440755240c0304840c40c03540351300c5180e08459000c401001c1565000d201d41130380b180d80051441440511310b40c1242081440508111a00004072048c4042c83c41e055559100003280c58000e1410126004041241c020340c91062802900445007203405c1134030248883c1e020707160042c009002e24a40301070080d1420340046200c4000824920010b200d40c1c4003003059800109005015000601440c5c0802106080100c00701142ca640e40b25407000d8166944020409070685c4e807105510707264200c403001004521000100305001444106070000340f000b1801ea64040001c80d502c500448aa060882c014080f4050003003000c01101140d02a140850f030441c1300f00d80c8154040d0f9801034451800e80141ca6000a50400d80a00000416075820341300c4482e29030300200910000d40d207840010040501c020002d00d090200b05200520041c031940000d03d01c024100c280014041d081c9182c0e04c5482d00f1690301da00404001c000720f11b01c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 878162553 1250 878161303 878161327
    0xd0222050c0c190c0317040b040e01090605010e0a211a1503120307050306061c0603020f0303040305030d1a2206060305060105030610030e0109080705070f080d05 71
    0x1411254048200030005494411004900703a401102030780e8142c0301c0ca641072101c04448844407500f07203500402c6050910324581d80ca52036000c050707004071036041d014040400c05002e61070141006005440480c0e242d9450405a6011604070780c000d54100812840492801c1d124580307210300b10f0b5800250a01009104007813440d2010303a03800700801080407290900901881010032030302400d5a46400c0354030303940b81d804065a4101c4418000024802400080c002c036000701e020f19448200174040f189048940c20340c030041504541c01c500707503843d035652003481035003004411401c5000003074000314542811510b59035030340d01510481c281c440341c654000f0b02d6489403107403410a5030000580a5248040500c0004c5052312581035800c241c2890180f00184440c824042e1310700070401038585038510b841da0420b0048030014a1742d90300030f140d148d40b0001034070042481041310503406800c0b180e854403902d1602c00c0c1003100c40d074004805201000010710150101080700743c00000303075007030060f0344000080c40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 878163803 1250 878162553 878162599
    0x150a060e0114090627060a17070507060905060f0610050f030a06030b01080f0f03070b0402090907031e11090106170a0e0109032d080c18060f0c07090603020d02 70
    0xf01a040003001ca8407610100801d4000e80070500082610800f403168041441b905000700c043d003030000348140c4130000c1d00401241220390010210301e005441e0881c01d0711900d040c1d800d0480100c803507070300c01420802100004030540d600721004680c00803a90281c410020924013410103482003a10340040842c0c003041540d0b002c02c008681c00000d03c001907079100700154440743c043c0205d03102805140c100a40c010804003c560210380d11050320440c54850342c0038013900d540001c04180c0103100ba0007000c800300300c1c441c60150212249a01100b428640340c9040d02c0c0c4800000200d07401030500800502105422003501c0542c4442c81d1032081481ea0340c082c40e20041c2c00700340007078403146d46001944402d0603880000340301180b02209000c3c1c0141032100110110000c0301c4548800504000c02040300303400c42d0801092040003000341c155400e2034190004140d907000410118110000003803020081d00148881001400010390800c005850340e00410300c01100f906009114506c50340800410003aa448 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 878165053 1250 878163803 878163817
    0x10603021302030f0c04051c020d050601080c01020f0133031b1d060a03150f060b090a060f140a2604020f030c030a08070f0515150a060e0114 62
    0x8420320740040c01d06030600941c4151454403000c3c03103002c00100005c1e10601102d04496000d460641c070386661403071464a8043e04c860499100000191540116804005150181c003001d005410007d49000019180c001c00303442901c51a418410b045103d03074400c40540e00c1d00c8095030840d1101c41a054030729080298560401400120520341d051214000d040d07410090310750707034040c002d1071030181c0051070201102140c0c001d0b0f0240b2040024400110511081c02d504c0440c0d24020402107416401c21080e112140c1140c1c80617000401c01200900d03041c0c900d46c00804007410082c0e246001400000c0514030f441c06c0c140c10140340094401180c51040061444907801d00c10310b20101402e58000240070201903905910030300b10140080c0d41890003280d941c0900500400030040310072503540b0b4404540240e0400c4d80c1082114030140003150302803003842c49818071a680032a04d4a0210f8501b806402c0e81d540e12400740c1c0440c0003d100c825080a40d40b0b402080034240074030a0503000d803082e241c40c41094 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 878166303 1250 878165053 878165059
    0x2190305040f0603050f0a0b1c031e080906070e0109030b0403120606022104061b1106040806071b02010c2a120b0c0a080118061a04080f07060203190201060302 70
    0xc2c00040d41ea54154049801051004c43c456600e03110441940241d07000b01c400e0341e60083e000e0110f011400440c0c45012010340c824282000200b02d24000100218818194040491014030400c04d501d038051007101da105101d0b05140087d11040700c0001c0a60b0810700005009200180118041c90300481e000c2207952410f250a00c046074444078001e44038030031200d00240300100e10220040500801c000c1c1c034181d8890360b45041383d0ba1480703440140343ca0010103007924100740c41007140000d074450b00c0061020305004402032102c1d0400050082288002c81070860b240030258009400503a402182c0c00c010b070b9004604195004007000482c1e10310b50070458401c0307080c9040318001808116904080c0b00b25030049011904542d04c0c00c0040c07070a0302c965040c0c400051088001030041002074841001c09485000000500c0c44e01c441d40e1104004201a200040c0c3c070001c202000152030030000090003a11250162500c1458288042c1d0b44e0b00403588041480d4516014240c1414803d50046000b5a001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 878167553 1250 878166303 878166329
    0x1030c060507030e060d0b12061506090a05030a030201060513050702030306040207020f0d23210f0403080f34080313080d0c170702070e1003080c1005070e010219030504 74
    0x103020040050811721f40c40e5000311100c1250071441030b0702260311071150040f103a47d540c000d800d420400c0404e901c078000c010751003260401d0104290300c4c100180d03200c4902c65000020058284002c212089400025402c90113040004100080b41d012003601d800c05002d80700542c07030720742610002d8401003181d0181d641221143d0302c04014400400700341c1e038292480c5c003c411480d2000600302c036112250144901c1c0703101c2c504541d00c607003441c45100070a6850740a0040344e090079125581ca4100d9803048200a9a810300400c0009100b0b001c4038800c6001c40c4294507840f8601251200e1030b8001d1490030010302000d8010000844860288100f00703c40340d4040510340e07607000318000a00c000c1452035007640006188490340d2900d03003041013070107000308503540040602600c0d110602c0c01004000b041070456241e101d20020000304410040c140503005480031b0808122580c80f2601114402040c4108110301400008450b90f00800d08803800c0892107681001000641000d0b03c0134811503205240503a26 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 878168803 1250 878167553 878167567
    0x150a1b1e1b050a050f03030c030a021006350f01020f13050405091c1403010914151302030901090803070503040605010509190f150602010b09010b0301030c060507030e06 74
    0x1481004500040c8140405440380400304001c0860040e14050503801c00360b01002806a441d24182000c500800242202e00c1c100b04264600c1c1180c12030300e403640140e4841480c0c120780d440c4500030300340035001821031102400000c5100c0140c0b07c0383d41c0103144400c000348040c040405400d014054440c61914001d655070700410410111640c8a242541c40840342c40e040803e01d0301c0c16001d10390040007108010f21000165611004403034100140800034015140810302006041c11302546c02440c0078280080d4044410b030915203020801008090300c04103c61034000d8680e5901010a0a0f2041c5900161241d07944a45940100803064018000c90004030811181c2580b00b401548220300c070342800d0200b640c1e02d03028800360f11016982104818424416182d021019034044414444503c3d004102900f80105411080603540c01240c0180d450702c40a003010b0405114550050400316162480d40d8555120009010102c2c01510100900011040245403113100c90342c1100100070811f9544041c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 878170053 1250 878168803 878168843
    0xa0213080607091406040501090b0f040f3209161101050c071202030307020a080d2c0d0507170f04210b060d21210203070e150a1b 57
    0x1503e100715132040e0300b41c0380008a03038108407042e06c1c1200d2040c1c44146803103003414240840764200040e01949038409000000b5201d10642c00600240a11407249a05000b0300003101c4510003044903182c0d88850b00740b41030816444032004164802540c6038246289002c2d044c085071000c031694043c0d103056003440240300c0543e031038400800c02c851140c1105007049804081c240c0e02c03800304032840f001603004000303100e02080c2007a0052480820041000403002c1c0762049400b80e0f104007403c5c000c0b260385c5a02070b8480d030f00c80811415512580c18107284d81040220780e1588840356100782c1911841d040030407140c45640501017600c01410399202d948525240d0408607403074160100009903044070100c00810810f04000c1d1889080c03541001c5a03038140c01003001c00d440c880810f40140d00401454402d4420341d905003180c298aa030070483d202603a03a00701603074004e005031000301d4910710880c411007503280b010719a041180c1100781e640c00e00304442d1150300004c00c50100d1000c0b001c1c1295443c150f1b1100024 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 878171303 1250 878170053 878170067
    0x1050408100b120d082809031d030703080d0e01060807060f030b0a0b090409050c030a0b1f0e0714070c031103012d020c100204030309180903080a0213080607 69
    0x801903c4092410000000700d0780e5480e805152840824442c0003c02c0d854003040a10406964089841c01011200f40500708100c48081100380c002800821418904d02425000f41441c42822002800d0701400c6450340000781c40f91880c031440740e40d40c99000c1c10b241a0300b034000760f006150f070038140c54403641d441c54050b0444002d83ca121001900d4a4280865840c1078000c14064905640105060480c83c50074031004200c100c0082d0b401d4481c0c4503e40175595800c0000c0020907126501d028120b040c40c02150561081c6555079910000b40c0303400c144545a1058401548030406103090003202e00d0b041110b0009101e403803c007403c034900889011041c80394400c07403128020b0080d4001c00c00b03607544070800860250460200040300c0300e8030f102099061b9458028100740c1c540882512034603e8085408c4080740d000d40d108401044501c501001200c071080080000348001c0407050084024a6800511605004040c0111650301150b440710303112000c038800f00a01210021282c031410f06d82d5010b8440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 878172553 1250 878171303 878171321
    0xc01150305070f0e071e142a0105040b040201080703090b13050c0a05060d020c031b01090c1403280c2418050603040f0501020f030402120607020c0f0105040810 70
    0xc58038868001521350388240c001407241506949500c1e803101c1c100281c000001070200303000c00300200345402c401c402e54030400403c0d2040c0000b641c0345607103400d0005112625203001d070303026842e4500000c100c08603104d40b01e43c03984030f030742440c107a42d4039a03503030000364010300713644d900a800300005104000541d4000c0482200301400744080b0740c3da510001040001c4002e00c1d001e800d4014006120210720054280c0140c548001441c003601d007440089a500c1c050325a81030601c0c1507903074441208009000384804210040c006141c1c004589802c0d00000c00e0341e400005082c00001806180c102e007855521005030342045500900c0e1154559948026451000710344000680540100f504504a140501a04007117450071051a0407514903100070030180b41c00007481520004900400500012070a00c020001c03228116042a10717800d01c4d00601c113050500c4030030102a64420b60038014490740000312844c1e40c61044481c816034410b004012030382806298400e030282d120300851107000000c00e8002c1040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 878173803 1250 878172553 878172569
    0x1020703200a170c010207110f060708030f191401150c0c0e100f031202061e0a0504021201091118070f11010b09070203030717070f050c0115030507 65
    0x35814518031114032180d5200403409442e8484100400010341440c295242da403100142c850900103244920340c00c1e03130701c5088100c500c15400e040515044c5040c0c40e0701c400c1e00005841d028100801a5076450403444050460300c00466040c00141c160300c87d05c91844c800b000260414020b040044540702c5400e08213004080c20300c5c0705540c0700002e241c80381d1899440320b40c0101100c0b0525113030001080c10180094480c0501580d161008290101c010701001d0045d48200a02504001035001c001e040c400f0203008191406101200800e501103940041d941181010b800090035807224400640b0501c0c4441001c3c000307501b41203c080501030362500c0621007150036100300403064020800d03c14800802c80d06c02010807841024040140c2c800c0b54840030034800031000064002c007400000d000958215140e10059000100f041400c40c0d01c0b601074030301c0c141015081c61160511682c003030009600012071400b0005c003c982c03c5c60010003500a200400004400700c0b11070307522800c200d0749840e5035004202e9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 878175053 1250 878173803 878173817
    0x4140a030f0609260901120e12040812090d02040c1205090f010b1503011a04030c0f080c030f071202010e040c050a0f05070f03080a0f050c091005041211180901020703 73
    0x50724100c0d00410000f02e03500502132454100030000555911450100d410340c903d50b0b50100110300710301081862400d6503000c04060f100c5c3d10380800e26127407182c0d030725420140e2503091020f00b0154607400c2d5000c01072035046038045480d40c41d180d81290343c64510301002c0c5607175041800303100c041500401c00b88488030702500280411300a4000b4030254004030f04c0594101c1604100401c488944c000c0010f40d8200a513a20900d4a6a6a10b50440402042e00b042c100e0035491901003000305000c0040329850b41064028044103c000c26170252515401c1c0300303510404110a5495003168400c0c10f40e1340245400603c100a080d21040000303150b900720164180200d1540d0307002c900c80d41d01a41c160303519240d01c141008116491030740d0407502403c0141410040719221484811034000500034144100868000075441c0d4216004000300c0d006c0186064003800410002800400c481415049401e50026000d00550142001081d560341201409040b204074240611a41c100190024241c940c02503640380 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 878176303 1250 878175053 878175083
    0x30e0a150306141f0c051507030c0c05100b0307030212031909120303270516060c081210031e0b10230f0a0303080f0a0c0504140a030f0609 61
    0x90200e0388803040050740400020310502400c4c01d80401a1201c1440d868103820b054055520756282106100c00f400f030841010307003044100c1da894420b0300306400d1546030036210101035803a09925403810130400441162103950392002510100951001540c1c040e0141150300c1840c90929142e4000b03440a005928503140d4521b255440b17465600d00f41c1d285800346021404441d41c06500a008503001794603080002201c040e100c509a20045686034019400b030641d08400e102e580b0f10340c00882c0c0081007400301402c003580124141c5001c0d220305201000a64029403140010b2040d0500d113a8401005911507280b03103200249030401d4400c0c0c0d10f200300d0304e25407141c0310f403858442c05039a14000c541a440c00e000d00018030300000c0710300301620700014040503035249282c4080740c4900020b030000e50228981030107010601c8e542c0c0c1e62090703010810007000c001c00050368400400500c01d42c883d8101c920440c01c03800341c1c95505c041c031150045500904400403c111440d200019208014042e10b844000100794 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 878177553 1250 878176303 878176319
    0x303080435090d081909170d110c0a0f0801052d13021e1315030b1803040e041101030c0e13060b0f27030705010c030e0a150306 56
    0x1121007500403041a081d50a03810488001da0004212258054a80840300c07010540001c01401e007a00c0300c2e0346090414000c0c1740080c03c26021a4400755010b078101c80d12008910703011401010520040c540300350824840e2442e00d1034132001502c1240d211540f0107000070700c01c041e06010400c0b1420180203000a039a030b4000084a80320280b2400e0801d1441c3c0301c004001403131340c403005a03c545030300c0000c046803100b60003048031460700b004001120001410200c40340c0c980ba010311696903446c0041400500e0010040007002c0126100007084c4140113408104001e1040400c040e00b040024112519156507142c5441d00d0b030400c3c0c1d019114400009221100b6500c03c0c0552207540c806900c0704003905c1c0c0544207112022110402221080350340c2c600214054200074020403000d010800e10350348400d0000e40380020b80950410f903004402c03d00e011040b454401243c1b04c0c0807140c2c03d08101c0c0000000e4101a01d4290301d404c0c0c510f900c103e251034086080d01342e40007007800700c414030f0380c007045020744800300c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 878178803 1250 878177553 878177603
    0x30f0806010215072c03070504020403050307020d021c0c060f020a050c060a050f0d0c110303071b15090f1203060e0408070804030f03030603050c0607080a032403030804 74
    0x3841c010381000807205410000600f01c40d80009081c41d000c41e4520030b10280300d1205402801c2402400c0d403d20300f002540c82c080100c030300500800c0740d04610300362440d03030b84603924420350000900626510390104155038850a245ca04030749914400c8040d954107141070441840d41e40101c4000c2012084000c5255100045042649030f214004100c008800c030700b08440c541128074150100b040401002c80346a4444014040f44941000081500b03015101c0c050010149508031803070b107520900411818a034811007200000345602e0901c058a1414240a09904603030340c0da0440c4a82480820010010041c0105020794014011b80091580b4280c00b103040c0c0d0b149200f000e00302098000404c0225003900f00800341c0e01d2161a40300e01c0d081e03036503450003c000000501a40481d989040c02c00034048240070181071490101c800c2c920744031056440780c002d070040408030030805940e080401c01d040000b0850050101e1500c02d8450b17030030703580c0c54024813a42e0120b4080360000d05001d10706141000c00c0c84 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 878180053 1250 878178803 878178811
    0xf2d03040b07080907090e0c0915060a0e15070503192f0a050607020a0c0b030402010504270203090c030f0601080a0b0a060e0406020d050609060109150504080607080103030f08 77
    0x811428035140c2e2001151031003005402444c00b4003d0390000640320071144129103d42503440060302444513400108002024010000000c41124660403092a5241402c1310145170039824001c4102c207141001c40c4490000c1081c0405031140000d841c4140580000a45003800f4041c0011488c40516041241d006201400c11400c3c3d201e0029a044800703415941410b00440c01802c4071022117a907141d0610300300c01030316001c02580003a550780d014001000c072180068161221403034507600b401d42c0000c110344200d1040b4a00d512064440b0041154000840d52010310031000554480c00c1c5654442d4450100040162080c072a0500d5001010341c04280c2a0403103c006001c0c00402c40c0e507440d200524070700106810030307881c0e640b0400308071042559141c500450150000580720880c44540e43c086404c040c10305442111614100001c5a03404101c490a503001d07803441d482c41d441084001c0d40c080c0659002003103640100e030b0403c05181e0744008428100c900030740c0c4640307940e900e518040c0c8001c43c06071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 878181303 1250 878180053 878180063
    0xe040f02070203101b0e180f06090133110f16140906060307021005010305060f07110a08090418110a060804050a02010f0e091306060b04050d02090a020f2d0304 70
    0x26240c10f02031802442d0841c01240b000e0500d542010002c0c5075201050000c07201c1c0700e00d8234500b00070b104180c241134540314003418510450700c02a0b5a9010080610011490a5000c061204004600252003080301100c103202520072030700703a5204103074a1900c2d41048212800c0110040c00001110f842c84d20818800324400ba01c01c203001e40302c840c1845043ea000815580951190b10b000d0700782081e162240c1030003140144081c1c80d8034108003501100c020b00141c5000d08001e05031005024081011940440c441d0b070004071265a880c0c500c002c40d0103010f484821607044051001071100740511001c820744034076001c5603109581c0f612044280d40e90764050310050700507842190481c00550080d404945c140030142040d04850310018000303240e50308201c45192401310100b50240422815000d80b1300a400c0c0c482215013024104000700e180b1181f83c3c20042d02c6600f85801041719a8825812515200c00f162646030f61454020103510109001022856031201d4803440b039890000c0d50f43c144d9001c0e56103d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 878182553 1250 878181303 878181341
    0x7032012010b130e131101030c1e021006140310020313080c0709110d06061e051e030403090e09010b010e1909020d1d0d02030a0f0e040f0207020310 65
    0x1a4142c40b0a07040074881c481c00c000070b02008502d880b64150214419850b440400c0442c06052400e10000390591000724141800c02031101865600b1510b03a040820411210182c8c0e544040c0f400ca142403d9a0520b00d40c440c41d12202181303107003882100240b100303001e804468009181000d24030403440202c6140d104141d000f644180014440781c024000764500100b120002512980c220080b141c0311440702486100005001c03035518840d000e140001c1c08203050503e06049548100141405035885840c100040000e1000d240d210019220380c2c2030507640e100700e40f40d00c2c3c0341c64081c0c80c803002805045e503944258030018820000500581031040411ba40d401040c490f40c10901404000601c2080800200740101103024046840500702d1510400d4004c55850b840c50070003003070041c2004248100d0b400c903034a480380303003034001046860710b038101d00d40300000d001c02c1d43c000c441e8410041102a44141003800000309694940c01811100c0c0c001c0f015183c40000181462044586001d02d200c520250 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 878183803 1250 878182553 878182559
    0x80f060f0408032202090f01052d15070c1202130203070c15180c090b0f100c140607081e06030d0806030c06030c032707091509050703201201 62
    0x7074001d4140c419661281e0b105051300d4a603001502d00741081b1520440300f003041004112620300b081040e05900c1d04840000344280315403002d01030001d03e00c1c2260340a078411010700c130b121300401c400719600c05400034014000151200c4075481d03d80e1130020180d100c0c2106032403518210001c0d00c00c49019491544503603ea0201560b0745000042851050b0104140c4d51038085e0b00e50110000240c507298403540d850790f07000f41000050302c11500303405006da000340c914000401440d00c9502800100e00da0030706003aa01604585042680610050445009030045c60148601980c0080b01c1901500f108240500f15040404e40c1050326401101c01642c07503488807040904203805090107a800c040085c040e0343d20101404003090b040d610944294a03601400070802071100c0ba81c8000703034031a41c40c040844000984c80c19129a89039041c3c001c0b0b002d00381d611420b100c14904141201802000e0b07100c2d05001d940740080014001780082084007146074800300500034070b02c0c240422160b02d8550317040503040e031340d01b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 878185053 1250 878183803 878183821
    0x510020313121410090201020d030207020114030a150914130203061f1e030b01050d02090a0c170411190602101a330f0703050d09020604080f060f040803 67
    0x1105070700c150f425078522081520103c106114800303204903460400305d8a00d03c203100083c580b905c03109000003094418461000140c5c0d00c0300d00e0224144070b9101d103130f440703440b0b004050005009140c006076120040000008214140d90000c40180351007056444c040d0352805080c030007803440040b00a40c140c102800064a1031602240081600500c9150002c1d00c0c2d102c07580b6801c248490501d0740c0100003414010001c005503d80c2880c0902816152201300d9034440c3d006c50703110b03800905001c9036a40c40c0c03907110402e42d10851103074082005d0a4050482402d140c02c0c110560440c691640d03001e020010803100b00403400151100485401d58010210403070100c1004004015061100040c801d40c080c5400c1940d0b1071030024045000c0c48824208101c1e00012a124503001c0300302844400401881070380b000202410980d0f0340281c050815550368100c4400c1d2400070302d149407009610400100740490038090008075086246a004102c8013140c44506941000762412600109170075401c10000340201c6c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 878186303 1250 878185053 878185079
    0x40b06100903060c05090a08010e0a0816020307120b060301090803070f0c02090a02040e01090b0109031104200903012304120c0b0403050306040f0c080f10080106030c0510020313 78
    0x1501500e001d4030348540383d0b6151001e4a080304890000940b000c00c0701180c42c50404505001094520002c0110040c1c00c581c0030f03201c0e040f003000031345201400329503140c0d01090204502c541680c014196148241c0340c0c0341d502c0303c400c00190b0a68003083c0c940006481410144901050190841900e42c215503540c2c200315415200180004d04110b4111580070040c0c40b204103e60198403019000341c4c4a5041580912a041050b40032404080c140348041103503981000303022003580c2d040840d00404c10348860220780039101c000c0d0a0914205500000440581e00402070504110304a00034410f1500300c80075100102244240401d89907041c4c000314bc0000c1c0c000e00700e603001d05020708000c2d0f04060785881e03407050100d0484060b40442c03c00030401000e40b429104649041c1c01c24441001440d244103401801041c0c01407502d11a034081d1000304040d61400d00204008018000003801401c0d100e10706401c1c02e00a92140c2d601440c1d8021400d0340c0310740080145c3da00d0b01d0201200521092034806403400c49 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 878187553 1250 878186303 878186329
    0xd060510260a0209090106050d060506180106051225020c010e04060f090f0e0604050a03030507090303020d030b030c04090f290c07320c01030c0f0e13020a090603050609040b06 77
    0x6e40d6141000a1103441e40640c045045004560001e0185072040a10180900380126400c1c0d0040c42001408a90b80190584885070640071007082d050b6900d104000039240d9100080b488603508140792032400e40d0005420011340001c3c0e03a003800d502c4c00c4906010588186020351480b0315010102448419616032041c6100300e00020003085010611404e54200001a03d040d1402d4000840322000d0581602a03250400440d242c485230312031564600944519240b0170382c1081644405603290203540401c00703c01e124000500070030900000785003000d641504104203e485590303840d05003140b005e250201d800c3c00d0041d920804031568800aa081c1d4503408400c0845043e040c42c5810b0103602e119844141205908800c481640600d007441e45103000c1c22100e680d81054280104d0f8450582d100c81780302044061418540860101d160008028140c1308103901c24448c070228a0400c01c0341e100756190304607140f0344c9042165856400500101c1041110003610502a0001044031414501101e403a0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 878188803 1250 878187553 878187571
    0x12150c050f0c1014040506010b03010b1213021c0b060409050729040b120a0c121107050a03020c1c080412080904050903190c0f110d060510260a0209 65
    0x29011200f041400ca9110104d80d0b2880700b6030ba02000704100041002d54050102c01201a0856261201c111503a02c07a48108181c1098500085041e102049600c5221a0360003003100181444490714a040340321083c3d401e8170b00c030303031070780c01040550601f40f140780401c0d030300031018280c1c5504210101c003c41654807a440b00c0c00003111401e0070250900030240c0080e180751390565544c6c0400c1a00744500745c0000e0a15502d06184c020003108550f0840c1c1c0c1c5503031a5094003008990b98200c0350389010703103001d042000f9004c0d01949203031a0425a010440001c0410100c0f140716401070058413810460600220003450b0f5501084140801c4000d200b5401c040c40c40785521a150900d5500031400717548065545481130b904c0892210345000d07846d00c0e420802015486e103a10b18030329075210300c4a0407074008000342c4440356040380020180c941130942c0e40b44640148042c0054200b00c640e585c41581903114100c6941c0c075041007d500e441240725200d07a490410002001d00c40c00740d800300702c0d410901800d8111 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 878190053 1250 878188803 878188813
    0xa0c0c0b010623030703060f0501020c0a090506010c060504060209010206091f0b04180c0609050402121605070209040f051608030a08062d041b02060c0a051312150c050f0c 75
    0xf000c0c00190000c5100b075261341d80204105182c041448204541c0d0740201d810f5400c840e95442031078541d9095035080303980c801e001040c15117810005907602030004101902044c144020003091028036001000082401e030300301c1d03200e9500c0301100761b1280171040701402c03040c4581c866074802c0a02600003000710344e4001c100007a00503416884500102c1072040c21100c442c00764004002850f00300f66660004c04c0261810342c40c04440640038180120002c000340040054500903a003e10710a509075203149074050228065420913050070b60385030311500000c484500c19410342609640c6004100812142c201e030056082085a16007034541000040c81180c0040c0c2c0b10107001d040681025001c15403616500c003103100703c80d12a0500c81503504008440d032041c1032201241440507400506141d106681d12000d0751074040300641140d0500c00d0b0084800034502015010604c881c7c24244420f081307100e0550424502400c04c0ca000582c1d0403d030040c00821810301040164456a00c020007c2029082c1030320 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 878191303 1250 878190053 878190107
    0x150615050d15060215070503010f030230100b0328030e030102031009060503010605060405100903080f30070c081e0a0906030203061311090411030a0c0c0b0106 70
    0x60402e416582c802801644030461550340213004800654001d907403482c1c9980b56606080c441e20030702c2c90300d2000030700609042c4100d24040f40c0050401c3c4d1002141814039520100c03101005076070740d4202c00c03408000740c500307403c0481070310700002e42d9810030620760039807800303001da80b4800f100d1400e211100b0707800c3c08060300e01d070a010354007840190301c14989240b10b503202c10705100c0554112449a00054000ea02d040340c188801d40d00c0c80c090710100d440468190f1007007108843c0441c0c0200045d40002d2a258000c54850004a80b400c0070b480c540e00c0c2420b0361581d2469041105600100f6038421902c042e81c1100421400c911a080c004802c1e0300540003103141848030368201d41142c0e4020350000c129240441c0c6c1d4074100381d0280029000f081a03240560071414075000082110b180146100903059171101c1c50305e58070781c02400769603a4420003003040154261100404c1110751080f02d00c06051450704444d80e40741c1c6d0081289100e12600000c11095607070800000780c1d0b0858a90540e40310704201c9c20540d07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 878192553 1250 878191303 878191331
    0x2041a0f120102042301090e04020934120e0c0d061107080a091802030f010506160c0e04020f060f0306060702040b0910051c0f0b061c030c210c150e0706050304150615050d 75
    0x480150917a2414410214103103030740115410700408009680013f104803405a4444c107940d82000c0d0018400183e41104258033540f52040e00002056034001040d0f03042c12a0b00084100100d69944183c00d0005c0300c2406100124401118094400640320006026905126010f4408460002c0c008021340f0302c13030307222403955143c03680c440303013201c241c000c208801c40c00c02246410f039000c4141d40c21401c1000501c900700c400d000080515008407804078150096640d6500900071030140a845a0400d09001566205038582c501a040c040c81c15403e11050420181c24070b1004689c00402c124106a03480d500e810088a0140c0031541c0500d0380b0362a501d01501810700f6010302440307a201c0341486240c0340340011482d440710b11f18841c0b0541100d540f651194004c54074105403031340808460440d61042c10b00c503001b44080c450f41806440380e5203001c00c2c1c04d03800c2402940698060928280e81d02c000720b0030317030701950b019004401c690340d407109031a1342a901a1000e02844180d43d940840c40c0400400c003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 878193803 1250 878192553 878192641
    0x622240b10020322170f120306091302150d050604061a09040b150a050403140c01140c0708060108010906110f091512040303050402041a0f120102042301090e040209 72
    0xd00c215004a0b40004010306e003000b980d04490304846060b403c41c0703402c074002070010a00402d521142d14030402d001c02190340e0500345200e0a0221202c483d21846042000030080004841c0d0320300035880c008010502803440b100d682025908100300074135006805003800040d000e11b40c0310365042050030705810551031850020f002a02a1660b0f40390b142ca1460504d03039880c120000b460340240c1c002181031035079643d112490f0003052503ca0601d030713500c0c00a00310161401406500504007070064800109507041c040d0032080b05d403030203038030180560840020308802a20a0311300c003d41e4040200a90380d114107002c888800c144c1211810346041031100701c4e10320720041e411a01100000c0d9584200030851500b0b104400312132030707000f0044040d50311030000f16a030000103003030302e5220f208a2100304034408000d4045030041d0000d0455142803611800e036441c3c0c1c1c1d40c002c1c0c0c10140454860031011170082955a000382c4610b030002d0141c451510f0700040c0451035490010724101c903030292900810074400c2919 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 878195053 1250 878193803 878193839
    0xc16120206221505041103060906010f1a180a080604081312150f060f03050a020a06050a02060a0f111b010b0a080622240b10020322 58
    0x750096241030100307440c2c09003046507924190b200084820000c1908451011180c1d12035420005842d1074509120b2034207032807018070543c18030404040011000e008a80c09041f41d00310544132884503211480c403441d1200c804e807800f0000009028041409010200000b4240000360075040c4e01f03500d602c0032a0801004030303000c4c2c03003515001405014000f0110400b900600d11b44400002c654216681c002c1415000e070009800103032103a940000c18416580410000c01c90745d00e045884656901e00b007a29600c045c01d06a2040001d80c90002c1c41c8da010b2400c49200880550281406e9680c04003941c004040f10004643c91076a00c103c000c540c0307040308000b0510880b0b24542c80340c40c040318220f601d0960700034809d040c0c0034901590082001c010000380c1c41e900007104006462034190030704089022902401c0f005400a00050362141d81503111404094641c05803600c00e001000000060000d401e88029500300103a1081180d000241d0318213a880d43e5500440311407190070f640d1880380c2544224803207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 878196303 1250 878195053 878195057
    0xa020d1109150906060a1b11032d01051b030432010f11090904260d0c1d010804050c0907020c0306090106050a0e09070b0304030c1103060f0c1612 64
    0x8185110a2401d0107080d9404101200c5d59071601c2000e18005040645001c0002c041043e00265101008016110640304150103007c03101900c19943c01c0c1d01c8000c081c81d6107807800c5003d206014040100600a00d442a810030490903499030003101080d68a90004105513020034610079210f03104407151a00c20b0220413040c28940303140039000c0902c0c1c01c40e08080401e02915140c41052940d520485090b130344044400c581800c09681c0300d080881d40080740e01c081d4003001011501c1001039240100292003a12110346e8204207588200300281c4800410601010b1070314200f8042c0c000a611400355194080d02c944140c500d4403c05030086882c008054074a040035801011215000e4102000074660203120740b402402030601c1d20010403010000c50052020300d4813150000740d0a0301d020043c1034005c2c0b031440c40310340e540d02d001c1c10020b1589904080860f0701c040742007441551898002190340c044c1039100b00115080d150b003180030310558407820a2001c0c2c000201004c40c04611805542e503040300041e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 878197553 1250 878196303 878196331
    0xc21040b061305070207060507060f020301090c081501020316060b1203030610020c1e030307050d1706040506092a07120e09040c0303181e0e180a020d1109 68
    0xe481005100c440e1407040078021490101044021340e400507520046617502d04060b03941e440b580c03c0043c00381c5071808001c483c26000100014520000c2e07800710b44449800d999075803040c0c85a110444c240d4030940d040c3c5006a01c1030110044401102c56291700692050b000040e8035607114002c01c01c501c0c2d003800040d9003900b0205c00c000301801c02c0100c0420b144224070241122102060020b03130402e0200701480c80d1280c2d460422021528200103c6203116081400ca50030802c0700c1500509010200c010280c1528030840824a581014011030380030b0f0100501c541c1c1c66540d041d94040445202044542d04211010034000051084200400c00c4070300451281c1ca1490114901400e109074003101b2038001e0840c0001c002c0856907595000081c3c0361b02d0300c0d0508403031143d0814a400ba03200c0b84c00c052107400649002d1042407074a03e00e400207d034200e003d4800b0968541801914000c0c4201010f40a40c0010880d0303070040ca04550b2000000b0f04c2080504a000f10b04804203410080446115111440f0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 878198803 1250 878197553 878197561
    0x603150902131512050f030d0b03010c0804031b02040612080d150803120a0b060d0c03050a020a0905040f0906090c03050f1204170f16030204050f06090c21040b 70
    0x1d1248042402c0b1454000d1080400c0c10940111440d254451907052100d0020300724204001400049244d03010307441125141c040341c4020030018060810030900c40d6181c0a070346a102030060703684a03c00ca4041d101c0002c001841d40c4105604e0704641303012a402540c4400110b071003207030741010021250003998569111003d902c0300e02d00710b0f10300c0d03407880c07000a040d90010840c403d0000115400e000520030080c2c41901e4081071903000e095100380a5501800104400e01403102d10750184241000c1c1c0d03a414402504c030b500c005800ca11540e030300c0c440011030703010307003403202d4100b41e080403550003c00c000000b049203181d110101218009201180c4520000c0d40030130a01904114611540e40701d032002e08816006100111124401c030b2180100c00c1440b00c08042c440d42c400c1c00880203480c01e10b0240c5018025601d10b1404c18405c1e40400c030710591410020803601841c0d541c1d02c0d8410b02c009800d0610545401100c5411600704140c0348039911210322040e030001031440704242c000c51042d0441c220b1410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 878200053 1250 878198803 878198809
    0x20a0f0f1e0501050a0201020c01050f04050115060e01030b150403061409120a110c131b0804080708030c0403060e0a020108160815060f0f1801050703020d0806040603150902 76
    0x641d911404460050903103203a03510382a95101c1e001c035042400c00c03a50311480c840b0705a000e40a81c50208a19500e07040400401d802d440218601c5244a01c2c02000700c0d0600188100030b032401c40c010b4000289111044a090354065030040e11003400050201c08040341c040794660542d802a0412105940c9403009422450b03c08020140c04c20076800140c081c00f9494086400d5600840c4050350400480202628080406200707038800701c0d5000c0c00380b07410b024a0410141c06000c1d10840849000d510150050f0714174070840300280600c0c0e108481d01e2405506071582802e603000542001011902084004005841482035280c5107041001505080501e800090079018000380400302026281c03401c004415408009258414410810307020070076070b0a00412164010380384260100c3e40300180310043c400611000e040003102c2c0030b10791140342150a0044915000c0d001006002d83d011101c000005030103400e903030f40d10890140c070000d4840d949840b6007120002110801614aa4030707040001981 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 878201303 1250 878200053 878200079
    0x317041502071404050408040305030c0109030f03060602030d0e01151e090c0e04050702030c0d0801080d05120a0f0b040c03332d1e09050f010e1003020a0f 68
    0x8500d400903101c00d61600ca062401c85103020b050b00c0c81945d94900150401c01104191405990800126a10751030300d24140380c0200b00c200c10680200750902c2c0d405204901c44d000303407010b33240c6071b43c060750410180340c90171030107000074400d0720485549a20303000c4814811075121500070041903010305054070000c2003c2c0c0c50148107802000c039050400c0c0f00a290160805004888034100b500d0000d119a0340000403070550141d0346000115000e8078050900b001da00100b014141e4048005880001030342c10030540d40780c4a00448821000200400500c8980003540600101c03500f03440081680d11410002504582041541d840403d6490006c040744420f00d126098090203c201c403081c101081000014281c1c031140b1401c0103640c00e00d0f00c3d5500807280081403e80ca42c0d03501c03401e5880b80381c4071500b0108000b040c081d001244088640c00254804084c014580603010080b00306501e80d003484001c404120005002280b00d0007003800010040c2c80e4041d14100604030341050091240c01c1c00d0a8070745032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 878202553 1250 878201303 878201339
    0x24270d0b040c0f1511072c010503010b0d0803040311150f130309170c040f2708071e2001030609020f0306190e0c07021503091f06031704 60
    0xf00b103100c200740089002a140c60114020600740b01c0e000303448a80a00f491310074280c218055079868010003120102540c0040345a034400041d10005070303070700e0328103141c200c1e00c4111402d0ba000b0020003565021888000c01181c205009182807074403080d010b04060714081c0420480d40720354441604101da02e40b1071000883d0016002e90029186040f2914010081c5680307002e00242c910750152201c0d680041000740b00c010102c007410078000400502d002c5802000c02d500450a0681d500c90010030b01c0710b00705115406a0741c00008c250801e10345031100546c6800c0c55280c20b400c8030319003144201240d81191810b8070095280302c181c0c51001400001816600300c1d602c4030804c01c3c0148a68849000707401c007038079480b95041e5a108081c0c50b014102059050a41e4003400e1401a50014003201030310080081a100c1c0c0266030441400c004409000c0140c402203032907244642180e08049142182802d800c0e4580054100101d5420749940314040703222440a0710910103900050304112540c6004811021 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 878203803 1250 878202553 878202569
    0x63501260706120e0609060f070504050a180b060403170304060b120106080f0703020102120d091401060302041a0d030f020f190506011212050a02030d06060e24270d0b040c 75
    0x1411b280442c150343e5407010301a1a9121810320016042c0380c440c205403402044001c0401d5405507a1300b50803c180c00c10103c0c2542c88a06040b810313291401d0110481e0102c1c4e0340400741004103445040c2003903d98001601c01c0b14505c0c0c8035915055665120b04894500890704000040c0382850140042d28110741c041611585400a0008002507078001c03404000030320840010303c0e51030b9511a915801003880300e4000f00300e000c0503064040700d00c81c15444441074a201b581c0800690b9114030441c2d0454414842c0c050f4407504108502001a01c201da000855284074012100360301c0e020a41c0c203040038003032511040103528610205051180420506004040344c1402c125902d0040d1140030388080c2d8196000103001001400c1580702e8401c104692644688038000c00145031a00001040e03498041ca2843c0310b141d010707103803c11483c250b180c803221140341d9505151a00c0000312004a4000c0b402c804100c1d03846e8400380341c22031074840200c00b0200130700c16078000e0060304d420b141a004040301504030920f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 878205053 1250 878203803 878203813
    0x320030706050a05070606050d030c0b060306150111010b120a02011d01020d2610140406080318061209010b0112021e03090115063501260706120e 64
    0x150300305049556008083c84e04560f0340c112420000c0107420664000c1c0e401101d4103e5510034554084040000b29204204160f1a034803070380c00b05070344d826090780d6021a52131a00f814a00c4c41d80501080c402d0310030f07410000700314410440300184200d0300b94000720711301d900710001c014215a48116a202d40b03805e2503119841080007840002c3d51760b804480800148100c200a50300800c070303070588407140c0c10201d5210149a00d0034031403c0c140c0c00c00d2841f821074617401c8020300410710314260142106070389950001354100440b0b229184034442c00110001c1d0402000c00c203000f808202220101e02c2065920004205900c540380010f0458540550801c000c4e441402420b0070301b0704407884a00e5421540c0e412540381d03156401c01500402019038031003541000400700085468011000341c282c3c20704100003940c0808000c01904012942d0400001d45202507030044c440c81545e817102110359422100e403000d101c1c224a10041c50100d25070014404180c0c640e02e08003800a03140252594200f403000900 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 878206303 1250 878205053 878205059
    0xd1e080a020d03050c0301090510150519111b13020d05040506010e13080a0e0303030a06030506100b1905040806040303021c0c0509010c020103180803090d0e03121c020403200307 78
    0x106010600034180c0230342e2610040303288400820245009840325440e1160f41c100c1c01364001d81980c0c440e501d5100d000c61000300d0008080d000b80400d01075000350784082c002c1c1e894041040c0300b00c008081c20b05a408404101d103080e2184842c0301034201141c003030000142d6030800d424118500b420507409490343c09801410040400003041c0360b401c0541c0d010f03c0307064803001079000036200c0f501c4080c01c03a50544004003c0003801c070f4198000d041181d005234280d0f4540e460b420031155001c030b0070703000b1002c40304002c1010803181c004090422000c810245001030810762101c01503420724030705440a40000750003180b1701c40340755690552a100d41041220070800f141c00254003030000d0080100c0141449060800c140945e406a0440c20030b1403030600c0e000d58084800e10701000e841e04181c0300305540c0e201d1120361408840c020551145c0e0064003d008003520300550311103c0d0a540a0740c0c0742e4480b20fa445003500728140c0701d400540082c41c4112801110010092401040030742d543d8016403095005800070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 878207553 1250 878206303 878206321
    0xb0612030a050309070b03040b060a06020c010e090c04051012240605090a0506030106030c030b120c22020f07050f16210210020115090903020c0d1e080a020d0305 71
    0x195840c40d41d6040c01da44a959004600e800c0c15030940c000319030301d8000405c1004000c000e100c071511499045a5900e800c40e00c0e648100d950b0f20404051034041140a4240b044070f181585800398400c0b003807410303245403d0721400170500000c41c00d0710300c0d0045010380bc1c00c1080301541e80101810045258928428090441c414004048140c4691018030200180c07064071512661480805020007030300e80d80c0c0d03a5070f5400d4018001d000e0081410000b0385020720303000b070300c0c50814030f5400d0f0005110002c0c104903c1540821000c240f0302188000d07482d60a00d054a4075800701c1c00600081c1c800d44c5107060b10748040382003141c1001140c01254172140c000407001c13080111040900c400b50f4495400042c0c5502d01118440300d49030f0340c1300c0007a5222220528810365154150848100091500d09640d0340c250789070311200c15109508001001f507005800701a113903007000450f070081d0901070701840151b1542b005031500d4401517004160345130400080da14081c50340411000c0c4e0200014a000c00c00c034500302a01c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 878208803 1250 878207553 878207557
    0x1f081e060a0b1b12040510080412030e16080a11010f0815061c05100e040b06010f052505120408061807030b0c070b221101021c020a0b061203 62
    0x50007000e01c8040b40c400070107180e50200c42d021420380d600b19138000c00300880e030040c150841d100305489445981500c1100d544241c070854000d981c03258080b942248511420b401a2100140c0c664041c0314902282c070b2203c1088081000610b000005043d0186c02070612180040001c6400c80c1031102e28140c184020f64010388280d0301c4000c00381d0b12109002480001000351040b04156466071228903c0b041d910115a88614051240350040c0c80c0e00c00e136511078220301800c4c04c6401400b10748504c000140c40c0c0d401441c0c5803081c0440c0b882c246143c12454002c2101e485012a1100b0b140280403d05004108041207040000441e0400e070314101490080d40583e12a801001c1c0d0b003a4004600880b0106141044200301031a840a0710b501140780450414100360000e51080c0e807592088008510607100c59440380b60344044850003003103404a04e444080004000106040c1184900b4000600200544c041c050482c010707940940f41041c2c0504080d001041d01400252043c126415404a21200041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 878210053 1250 878208803 878208809
    0xb090f04150b060913020d0506010906080f040807060203180f01062304060803040b1c1503111203030c07051006060203040312120f1d07030308151f081e060a 69
    0x4002c25203030200c00c0800c000303016090086800000720308840c403962100d0b402a10040494007010000c558a480044404129038840d00c03001c58444004510103840184400354841e00451041d031030201540c1d10402241c0c02110f900011300441808040e1488041c00740c1c030304c2e00d0810300007805064140040703801207400249030048020004c103400341f400e46854000000034450311023581e440c1d56650b0081ca146a020202c10310000788141c0c03210030714001c1c1d4440c50041c501021891603486c3d09640c0c0d4640c9280541001c01e5102190303000c20a074400d805c00003188901001030a058840c403039450f02600c1c00c0c0d44403580f0394880d0708101c401e01611303500105480840f0342181004400080c0c0000659200e012051945007036800c0c03940351b00700c41802d80c10024156038244031044252414484c4181c646269002c0200000c4002c00801c0311a51801c0b065400204010184840c3c03941c1d00d00d034940d482d441c240607140400e03404002c118403d2031b4812144490b0390002d0741c0550320310308100000c03400f5490b80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 878211303 1250 878210053 878210093
    0x306180108030d2406030605010210051018020c0a050d03270308060d0b040305040312050c070b1309140105040b0117040618080a0c050c0a061e020a0c090b090f04 71
    0x310144c800d16103020142d8070312000004400151a420014040d080502441c0c4c094801c009001e1180c251920a5038802e0842004003282c250514030f005902c080a2086c8421b80c0e5002e00c00484000d0041c00f841c00706501c41c40040a0320303100341c000501070301c0780054080750030b00480c80c0006445146040980741c00303500d494001e12940c0c0d500300003800340a103020042c290701c04000030013080542110050050302e0091499046048071240e0456082c445d0004000d041e800c0742c00d04000b01e10055001d08035924620f80101035440d01c40840a045130045006464103e90361001000282450f1240d0000d10800380b13004050007031030f00c07030108074403201078001840103540b400504500c0420003844000c9c07992144101d960303030088180007031890b0750f00442030303981c1c1c0103400002c6954503041101c40b04484203503d1b0b942444005603128004c1d111503204500c29801000c010300001801500c2e0f1002924610f80009200c001d450148104424024000a00d09107030200380004a16011a0461050402 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 878212553 1250 878211303 878211311
    0x30e16030b01120f170c0c061602090a11130306060b07023a150506041a040e100e1b010c0305070212010f0f1a0a0e240d080306180108030d 61
    0x1500e84404280ca0040016104c40a1905c0320010541140c2c003d04c070071742e51201250140e02c55036003003044501c03e420004000e4503800c0c0c1d1020041c00d0180c5015400800c080f000103003481212101d150a503c00700c045000c000c40b0200c1403003002003510558020307061283c00141080103d07404240032001c0801180a04603030300200d4102840144070b004500d807034007a502c040880071881d14105001402c20400d0390541800006551030509103e68648203844140c070304070021904060000400b00f041d0000c90324021a034450b407c08440d8058040c0c0803e02100a0a0004946c0e6451002c403503d0100343d410041800c480401007a441000c0e90407982e01141c2000d00c41e0f003c403500314010410014000030a508000700340314880115400f00d256012041007042602004004210b45c1c0e40031401002c481c441714101040344240c10501180045e000c5040101289204d1030004104155100d030841d0300044c000108520303818400b0004045a1502e50309860300d50512070b400d6102d0241c0e0b8490000240e035 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 878213803 1250 878212553 878212589
    0x1c0503130807021818120a05070302100603081b0d05340c18060302060f03100b0c071503090507090b0a0e09030c0601062a020a090c030e16030b01 64
    0x3060403548603a50080000440d19140c013201c0c1d003041804c07030320520718020540810700e1814002c40d00c94500c10b098101d06162110243c0180c4a54102101c01d43c00c40c810b041c00d1000c20181c5100741d00c0a107004519140c0ca85e0600c9102c01d2030100ca0328208402e030307008500c210060075041403c0c0c40207814200d045042c45003a0344203140e400c42d905400d804092106164200a0042c6a06c51074161400518468030500d0aa100340051740c0e56840000c1d0041020410180241d0700000a0f641180b035400e01d007a1134135610300c0001d513190080d0450400702d0700300c000c08100c00003201c0f401021558182c00c0a000080c8543c031401e8032503606104c0c40f2010340d100c1039410318513501c0c0100e0314090b00740030700941c415081c2125030b1a40c80d0040391403d0b005101f07042c008202540a003c0e5144e516500c0d6118048081540303040082c49101003c003280c203c000b1102c089916801070040f082c2d1024285d900180d80c24a4140c50ba14100c00c0c800681e40041c0d5000b01800440c014115141c156416140d20100d1010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 878215053 1250 878213803 878213813
    0x120f0703020715060305070605090603010b0304060605090411010e01031107201c0c050103090804030f020301020d02030f06041505012304080a0818011701030209040203160906081c050313 82
    0x82414801014403e034900300740441903a0f03038070890951b4010012100443e45034103054646106046a041d44a002030004102c00720305107000710351041c440c00c004110305544d1004103019140550f41240c07001d006111885041d60302c4402e001511400b46028002d018102030313444a40c0c41222009408030b080000000c0308560b90b107001130a0600007400c00e5401c0409458040351310b96410000b114000454000000c0540c403900603100d4240c0c2002800d490b2502e0340c0e582c00e40c160a071070012070301135409000302c403800c074410310156202e4042c03403820040c9441c0030000c02c0200c41443d46039078481444840103010381e0340c0c0280f10300401901c880241d0031405003103c0b0080c0d9401182d0200946100d040b5501041091003000b608090124036040c50781c50022034010350f40d128030000d00d00c8030a0811001000903280a9030300b60b41003400541610000b0001c452051003e2403180c00145485444500402c112042085000d00200619165580749040050000e00512010f00300189500c4c00103001001c0c02 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 878216303 1250 878215053 878215057
    0x91109010c0f2604090510060905060c07080d0c120c0b060402071416030c080f100203070c170406090603020f1219050f011802090f100c0204020d06030b0c120f070302 73
    0x42495803014509103e403810042d0a600c14011901000c0c2481d0200382409000840e41c01501c20030b07110109001d040909206082c0c020014007007441c032802e01e0008100005100200340b04070f403980c80752210503107030400c44ca00e9144038601008000c0d00702c41203004201c59000080c0c1229041342c01603960811410302615841054034805204c5c003511014080720507004904004482c0300750781c00c0c00c00070760780c1b80c86c0c43c0c8503040d600c2e40d440f05411503c01500008465802035030700500d941480d40c0c2901054a0348124a0100780c0c004a000c440000d06002268002000000030155481c09524108a940c003c0d01c47e40203120404caa5041941c000c10032140015010000800710988200001e150461402118800030301c0350649030709554103440301144e07c50085984001015283c1461040110140f040c4000076190f08000c02c40a007040344010b83e00c1d8001043ea0110802c800b16611703085051105862784058103658241008106014440c58031110300e0b035100540d0041d1178050f44d1401401d4010b8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 878217553 1250 878216303 878216333
    0xf0a0611030904050f04051c0c020112180c050306130c050405101205030a030c0f0f1116090e01060b1614240906060102120904090204020919091109010c0f 68
    0x6044c003041000b803141070704445126600920480e06094421120310904102d14140343c00054045448a000365019804140580158420009001640c900301600c241c201030021900c40081c1c040400440c541000915000305500180c1c00c8410106d44d18001101003501c13940f0700442d00d42c0001540d006c210500a8014100341c2041b11080b0304620b00b140d2030354851950880401d00c0c1141c603500c2c883c880c6d0002100ca0341191900003400703103254403c2d13540c8900241041164800c68030b04840000841810b80000c1c0805040824000c0d1580401401c0d5500da4000c3c0282400c240301030f900c03a0141200c06a085500030b0000d03600c00d00400b0045017480c0c0c114070400289042c84159020f000780007035201c0d10031196401651030549580004a8031408100701f0104070f22410301107012603142c00e51150320018070081c0014075006801020a0042c658980d2075208010605030800c03801c0102e001d2042da111300c50030228500610400007800a44020345c2c09014060b00340303412020030006031040d510f6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 878218803 1250 878217553 878217559
    0xc0e090316140607080a060609050f130b0303210c0702060a111018030f02060f1b22170f1005040305091f0f02010203040f120504090608010504110f0a06110309 70
    0x844c544a03401400e5038074251240741c6414034280340040c05074440c1c0e6110040d610002c7c80030080d400329000704801c5450f10740000c980d055988090144995042008140d901200516080d584a071811311016540c00200303801200e2800f0041007005a690604880080085003801010003000c12502da00d4911804e00784d111040c07401800910710390a041540c181c0d2440703035681c01c1090401c02d00c100d0700ca00c0140d40e01c014840000c1c001c82d00e0b0000e1400300042401481c19201d041001003803940d440caa0104500303852881d65000240250031540d5441c43e8440402001084c1c4240040002d99582100c0e00166044950700c1d0045030070144500211104940700078602c910a45400d0404480c40e00325032400b202041c3d00a00203941203006000340c0748207540000307035003140307411a880d45005140040700c44400c0102c1040003203401904c41c851080548110070000032a4502450080c0020349004511441101e08e0800c080082c5e4410780a002641e190b032400c0101283c41c2000c2c0351071401146600b40d8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 878220053 1250 878218803 878218813
    0xc09040c110604050c090109290402071a010608160c0b06040906020a0305060a0501230702010c050a0302070f171e0c040623060406051b0a02090c070c0e09031614 71
    0xc280100005c0110708524115005a026642c5a007100c040324960390702c1420140c035048080e801c1c503413060300c03140303002d82d000d00b02501d0000565940c60250240e0b45d00000c0c0d9030100001805034550001900e03901006000c8034140300072400401805040c440c01c0018003245096002030007549841d00704a132040d5109c0c10554031001d55941c0a405072a04503510b6002c1c2c001c0700c000081f40d6104500c08400c45110590000120b5040444041d03035610450003641800392081410b0001042003190813601c501a9001e030130464206000130f20f101060764042c00e408400103180401041c0041000c4802e000e65840c0d43c001651007480140c100072400400d00d61051078424000b503800090540c1158988200b100c4000180219003000300783d005038003038403000038804c0c02002a00003c4003088044c00b0070540c100c90b142d500c10303400500004400c44201c0150140407901c00300300035090404d03401030001d4059850080c580031610307036900d014a60f0704201501e0407041d41400e014039440c60425966000054407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 878221303 1250 878220053 878220061
    0x20702190801050f091618090c0807080105090102091f0903020a0602010b01090503070b03040f08130303031a010e1e0d21110d020c0f03030c0d1d03060c09040c1106 72
    0x42c02460b0407551400760714050000030315001c4001c11b03040710f06030200e900440d00504000031b80e840d04e041d00c2060a04155140310301400f0070305400d4003500401d8800f0080080134100207801d0b00b59103010f44460600e070b00510180e101d564840e14200348800c90702100c0c64422004500c1282c017102070341d00194024040d28004101d0b140d0641010601e00d0b0281c80700c0c038145680d4000c1c1651100a4840d414041c08103001041c0090604410060002c1c064100c007400d0103641c203003038100c0e101180d104501203540c3e00c5d114121210280c0c03050031744402c24204081340f58201d00114110048046542420601d550075041955880c188680e01b0305030002c80034089640c1d5150b210030603c1c0c021212074046440c11161044e96840050100e28440c41d035806450301c292104148285038003080c6003c0e0f0302d4003003841464a030b03140410942c0c410340c00c15500c0240700802e602c1c01001c6022245820b038025042041048400000702040f80c08035607050304e0004400c00803c004590420000c820210140580c02c140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 878222553 1250 878221303 878221319
    0x1a16121710060315080703081e0c03070b1806190f1b020c03071401051308060720071a0c030415080a110c06150303040801090f15050c070602070219 65
    0x10100361661a1410000c4190031203a404c0d200b801841803040f5a40203c60600c0001d040b0030140c8404841010ba00044014410a851064020407080400c5500108050040c804071241090700446160400300c0354480d4112081d46403500100b1004111601c05070040d017440c090340c4502d01280ca800820071020111910724050062170b503c0150040c890100c201c0303081c1c41c000c41e48404480d140307038034203e83c40c400700c005507141d40000044400f480083c40f400203524805021291003486151f0362244540d402042c8002000c003c40c8200000e6030100000380021858020480d615201c0690980c1c0c481c41815401443c501ca2500042c0c0000f4132080c0840c1c5c2c6c81d8001480a001c0c611081091185100e4541b650441e409040086216a40100041054080e0305410141840805410b803450320391140b04160940303844010803646524010180780a101c1d03030380c40120703003014403001c10b000c64200058141c2c2ea500400e50701401d000d0340020240c0c115503030050321119518144800e025500c1e41c0c1c880c9 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 878223803 1250 878222553 878222581
    0xc050f040b19030507080f070504170c0a090e0304060e04060f06110d0c1101051c181b030c0e2805090c0f0303030c130b03010308041a161217 62
    0x1604407140910b5075a100030501034020240b0035800c581d04d600341680c0ea40c510307400b00b14024200005122003008041035201c00e0b4151003036506003501c014202082c6c9041441001441d962251905a20740a040a0010004000c4400f20ba0311403515849000e240700c000380c0103104a83c40071007084c92940c0002a0300da001028544000000d0741614000f03a610722043d41c00a1303d003a4028007425000d20000c51b60741c007401c00341204030f4140c40003049001c070003031080003201c1c0100300b07030500c2e404440c0c1d54404200c200240c0c450204e82403400541c0851543c0d55084030f51480f0f00461b100003d816000a008408070744405500b840c02144c170000c92145000840010003081c0e41340105030040301002030f66030a00501414070550301900840c034566540710190b03004d41240402080d40c0341c07080c0d000980c5001d11000744d8040c50040d105207a540b441c00c0c1ca6041e036020000256000d90b581804404404c110450201a18541011030700550f04c00c0c114084565600000c1017010b141885030510014447c2c0e590 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 878225053 1250 878223803 878223817
    0xb0105041e03050d0302070809061b010903080627180a080403031805060712030f09050a080a031b050301060e0607020904060618060305030d180206040303032007150c050f040b 77
    0x16130380b140242440440c2a413052107000b60072840100708507820b03410600c004060004122007640182c1030720300380060a448660005800240ca038809004140c900183c2d550a400485050080b901302500c4052206d00802040c2a00a140340c01010151010030301c0003400455004010981c8c42c1d80340d24003d0810300050a00c10010410041c002c121802c0400445810701d802010bc894072844154084001c0c00c880f845502030f95171611030200000d4020021075000031b02c204c074411b440700400d11b8000c04503161071344054101e0300a41100d820180d0072008990550ba16403034004400d050500226400d0710138004005e421141003001c06c01440000c0d4400c200781c2c0e0070030404040c130400e024488801e44400b40030161542e041000301601074411540403c0e00c21800c9449200101003680000d03000750030591081d00800e842d490310740542c080011640303950821500d405810242c4070307251031100700fa9001016801c43d0b138401c4134610190281c0103603140303482038085165a464980c00c0d100c082e600540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 878226303 1250 878225053 878225063
    0x312050a0806010f02061515040803030f06090609180102070b070302030a0c0e0102031204050f25080106030b010b130503060c0409060e131b0302030d08040209070e060d0b0105041e03 80
    0x1001141c00c81d807007425240f00e030035141d85c01000c540c0c6422017411243c150b100281980048210324401003404010080c00041c0f201001541d100c1ca010304001c400c1c80c1e00140b01e5442500984d04012060351800b0f01e158000c0300d024040285c01000c070348a5030080c031a50201400c21480c082c01c11103050740c580c0085102d400f8803501405080d81d4607506507080c0c80140412030150300700748540d030010100c003a681540f190081040343c1c3c1e500d8a400005080c2000e103107a1070409290980b03550340e00004110380300018120340c4000c000f00e5140d9161040007100601500c41a0140015a0161f810600c82e61401414004058803070030304001010305416441f0b0300c40c0440c3c0a0426500240346081d80d2030052091141035622600c030000b55440805804020002601a000160b00403001d83c600700a00011003015440388800ca080a00401c0718006e0b0080c000410880d00c0941f04031251201000d0722520740701582c02061280b00c4c0700050700e00307010700d4103e04440186102444009021450354000701e90040e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 878227553 1250 878226303 878226317
    0x150b010e0a0b0301140613141219080a05130e0a1401050f15040f0308250f0b06030a0212100c0203040812130e040f02031b010e15040312050a 62
    0x500148048040e40b8811004640310600c0104205031043d0303000300410200600c1030b80f07411004100b0440e07000c995000074543d98012030290356141080d444001081b404840240045000d800514241c0d0031560b10041039080040b0342540710034001e800347c41480a0b251440403a50780c9030b04600741500300454044019509024204020030201c000141c1a40c40150500e08003052070f0041c010303508001c46401200039010400000c3c022494420700c80690b01c00c150141d95034440c440006003542c0c0e20350300580c0f0004100007220005104107003424800394080240d141642e130342e800007030071702c1c1050401942041d18500c40f10410340011800d0b080011100c0c001f00000102d24104a90b039002c0c070f00030304907903502c12007095240b100c4450150202000b00e421050f0540d48031130b520b40102005690841d21101003240c8001189818896510419410005203d90141c600c0008010300c1c4c02da101c6600881010f44400c4d154540e80707040b00e0141d41c0210200e0103012119070010a2a8003902181002410f0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 878228803 1250 878227553 878227577
    0x712021b0103090c0b03130b07050a1e0e010e030c06160b0f041505091023282c0303150a0b12090f0d030b33070f150b01 53
    0xa12640e05265040460180318a04114200305c10781e00181c40821500c240c9145400010141060f8900c0f03142070f550b4054481002c8907006d801c2c0300d1601c03002124000180e5a030103059600008610764034000340b078100c840302180c8000c00e08200842d01d5060f006080028144c2c2124005034002a0300c611035100c062899850480c030314922a0296002415548040000d403800f0042d41c004580010b010020350b003a08c64888014400c98000603044460700501850b0101070b500d1462040d0f0b40b05116115914096001035080844030b42c0e03120401620990391049035401003126000c83c444021005283c100740d8405030202c81c0d4a800489851001c1040700010800e00d040000d0003a0840e0407440e9103d00b040071140050b26800305c0144950708034400d4070700d615900701c801c01c07581c14004090348002809000c504184039080300c00e8111118220445030b0502c0003481103950350b54421300c994401c140c0356040780c80c1402c1612400e540c09400c0504e1010042c204010b581d10100d510082602d5015000c0c01c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 878230053 1250 878228803 878228807
    0x170a1118010909021908040804080703140d02060f13080d0908091306060e04020706150605030a0c030504020f0d0c12050102031602060402032805250503031213080712021b01 76
    0x104904550050504100602c45d9490044150641141c0300d611b07a20f007070580f55110245406c401790320503031742124510160720000314140400300d8000842c2c406000c031440c00202288030050080c0c500034a03098511088006c6c40707a000e05035151010181824488042e0034181400c454000c14001445034054409424108545215041c11101c02c2e0b2280e8155080c203c0400000790481d03c8246c9038070b5158203081c0008601521044040e0a8a0301d030240c4908007521110201c03000289070505051900080c170000d60b880c01d0180c00c480600b151030072400102da2400702d0b0003001030380c00340842c455004000c404100040d005140306001091480321f900911b000c2c01c03a5245c50036a400781d0580c10094070300c10035211303009503982c005440065207100b00b03800da90745500c0c00c0d0700a106103262014410120007058200280e11009160840c0190700300044201c141ca100c0001030b01c1c15010381d41c0c410800040080900c10b60f40e40c60b4020b07105042c1500108000b0307441e004040e036504800c0c500c1843c1030f00158 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 878231303 1250 878230053 878230057
    0x403140705010f201e0f041502300708130e040326011410090b070f06060506040503030a050d09351809181c14040303170a111801090902 60
    0x40c0b804000403009170086031221200e511024103000420343c200320100e1500900344560740d400010b0360080c40522041030205008801d01400030560010300c00c045200d00f0748450075100000d41280c80d5955070000c2111004c41c6a410b540000590414401003209054004480444001555181d80b0303d04c1d0340c092046013041c109008086148a4540899840d4288050340b0f0403040c1c10360500f0985c036500d4040504943e04000d1003210780050030399a0303c080000c2401000002d080940301c0034209824040040e4490181c0d078000810800c011580007941081c0b5000045c03403d42040681c58040805030301705c5102c0d910341054115213201e80e131101822507150f01c2210307882081101c03030005c0c841d4000d003009490800a84140d04440a42801c500810300a014101c00302c1c4003260f1002c006403981d500075000c0d980070990018141e805000802c040303904401c24030703040051009007400c06da51320303440b0000078030400b00100c0d008600420407140c00c029078070584440b0a0240c9901c400c0541c0c55413400181c0c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 878232553 1250 878231303 878231317
    0x308091c141002040e01090207020f061b070e06030307022803082d0405270a050103051203090703140a050105091b030c0d0308060607080d0207030e0301140403140705010f20 76
    0x2064034170b401002000040e6002d000f00314402481c909540d0060000141c80c0d07009243c03c8a40b480f800c41100d03410307140800c0a003004024440300c0b024503242c800700194032409107000107401084501d40c00441d04000da40c0c82c220070005e6000b13580800d0385908141c07940390000c0ca551038066610208a015003030b21241404504020074145502e0181080e0501441500500760b840130101c148990242001c141c0310070500c0f54110312000600745d80740d4100985046148208074418440c1041409400c4001207200700540c1e81120140c0324134010310050310719111404601030059481c10707062140c456004500f041000c804a00300085200c00f002c00c041d2502e90965445500080003190500024021a01c8591010004200d98102611a00c46841951205007031044666000401030109170f00f082614040c01070a800070810740d03200303080088680e58044c0c00a410f03c85440d62907024440300504850007154404020320100d03801407084800b900c8511107250500d01400309407400040554240e500d2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 878233803 1250 878232553 878232569
    0x6010f0201090b01090218120313050d261b0706090b27040204030206430221160807080a050601090513020d0302031e0906040308091c14100204 63
    0x20740d180190a90095119503889030585820f07c00354241c5a480c4860f400307107400b81d8005035a846d030503d10760b88485070b0982c0000d407180c4601e0520101240c0720300c820081030100d00c608105208885a0700d52024042e0f0308a40c050740495420305000b144000c0f5104044818035202d4403111038840c6c0ca00c000d540512170720007101a07882e41415040c444060001880000040c00061415460342c0209900d80d008031700704403810b00e0401d907020120001d52181801801540115406400204600b41039001e50010280c414440c2c500401c80400b01c1d10040001c954502c2c0c11940012080c03030365141c4409040c455807049024080c00010f091750041448003045901c4005460541c1c20041c6030001032130041c060520b0341720520000750058950031680600103000f90000c0d030311081d072081407001403520209110070314034084c003460b00179445100c103030340a40b5800540346464003a02c2012812035403400c0c2511810115004e06081401801c0d104200c4441a05003640c1141eaa4030107140b0a91140b031190410b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 878235053 1250 878233803 878233823
    0x1020f031215090106090e060616020405093f09090412110a0c2603030c16052b0903020a03080a05210105120c092e030b06010f020109 59
    0x44141c105074610394461541d02d0b10300d940595500119221040907088400851080f89080c04880000d5046a6100e4000c031010b0f0314143c01c1c200c00c0d002031a004000207002d96200c40c08610448000e201914610085c1c45d52a21450354a4402c1400c3c008504600662500038003603001c8070204103000ca1307040c24005019410543c036965981e140030444c610320042009001c10b00d54501e40024080041100c1c090014024100c2c20071501c580019034058000322104014140190300010100c01d590740082880307000c2e0384501c004080807582c0580140018902d0141410040ca54882203240d1080b00c0007000c03e11910030301a07030041d16501d189010107907001c540d01c3e00070400038030a41d0050107520450f1500c03e040c0150744a0388400550030202200c1384c40034081c0140081d080c2504611028540c0500501020452078003044500300d01410400d0310b45418102030410341829400c2d800040242e01c400b002040e542e04000780c0c0d010b02a605240051161490f40a18034414040c41803510f4220503018 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 878236303 1250 878235053 878235067
    0xf090c050a090221040203030705030c0307020f090f041b0302060408010c0f080c030408030a020913140a1a101b110103050c120f040201030e011e060b0a050406030209031c1d01020f03 80
    0x180c407500001700700702c0e894030081045000081c1e00340f000d020b2481550008540310a04e42c4100719090042c4e030340c01406169a54100400e1401200703170b443d0440d401000c401d50010f403410b1035444861803500065000300c000a400500c0e00015402044800b2042d5034100c03142c64106022603c0c940295100303c1d0a031828070100b80410107240003540c00043c200c50044c030700000d8030041a0030002c034400000c0c00c40c0d0b031341c0ea560702042e41002d6070581c005044401048583d28000c501010031001440c3d807801400414420040c5c10b02642c1440100940c1e00840c90100d44549442250456181152070000b030416021a5502e072610068600d8420b00d001000760560390f0380c00019041c28001c009904050302e45c000440d07007040030301c11740c001502800c80034038000d440000c003c02910304a81c00740000381d1b01009820f034606e6100042e2030079a035407440c000d03a40b41c24045c002842d002c0200125031840460b400000300c8690042d4980c004009194500c10300301b541b200c01a0384401554100f0000364000708101 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 878237410 1107 878236303 878236357
    0x50409080711010e1309020a05030609071a180d170c03040302030105061002060711030c120304060c0c0305030604020c420601051c0f090c050a0902 65
    0x4c0d850301214000400c2d24241300781c000d20381040d07590840408544d15840020b000b071400608880081c03e205815503103032a414415140f818410303c82800214000d13900f42c1e181c0702d81c0040048801d1204200380585445010707003c0301c5090702c214860300c082040c0c1d005004041d507140002d5813541e0030f510506007180e4000c1c01d110300c0342c0c8901c84000301032540000d41a40c0806a45010306080108038140c618500602100d401d140c01900f0400403030701501d8001d940708500805060000d00305114007955a910107410140004404000003546814140c008042d850b01102c21103007005426448610342030719130f0442000e0710b0f9400010108a2010240103a43c140c05002d80e441c0703a007170500002e03000e032040250b0107115041142d00343c00030130040d900c00d03404105922407d002182e00ca00d0070040c525a43e00407036100d141c0314600428880c080f4405d42d1045145541049107034468035a007 = true := by decide +kernel

theorem cover : BRFrame.Cov 878057553 878237410 := by
  have h0 := BRFrame.cov_init 878057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 878057553 ≤ n) (h2 : n < 878237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
