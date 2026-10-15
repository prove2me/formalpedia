-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4327
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:16:02.213445+00:00
-- url     : https://prove2.me/submissions/a913e694-adfe-43b5-bfa8-dee485e430bb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 778057553 ≤ n < 778237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 778058803 1250 778057553 778057573
    0x20a0b0f041d090f06090618010207020d0c0503010f02120103141c0c1719050903010902180406110a0912030e0d031106090c0a0b0a02070b0d0605030705090f181908040305 75
    0xc0414046d11401061001c3c1003990744602003c140c10900c4107520714590f42c05e0091000613142c5c420b1001c4054081c4c030b030410250349420f0405003500e806204030600c450051001e109941c0060700500d0540354002c84036a1041c40240c505442e00c41825411010b0f0001c0c031003500882608100700311085405260841814210b40c0000042c5110303a0080b22078441c0040da03840d41c003510130005810070b041c4c02400801c82000c0e03500010300000c0c07802c600ca445c29810100384420400a445820030148041606c2d5040c40310080c0068001601403080364905000b240407101054400c0c550b480d41d469004208400c0d81d11107046c010280c2da40b8601c404100d01c1658003141d108030340001c007070008100052214088908044008903d50040c29101042d0300c1001008101d000e44c50707000c0d003d00c01c074003400041c0e900c0c506001c00d49400e00d19803007103024411040600407841c0c81308890b194018039480c1d84c203c4014990f640c06160069030704030070450540340d410b954100070082008004603405030044601c550a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 778060053 1250 778058803 778058833
    0xc020604090605030d1103030a050c0c0f100c0306030807081303020a060c1106090d0f0204060e07050a0e010309080a030e0a0503030720010e150406180f060c0804020a0b0f041d09 78
    0x180342e03002d00047c2e00c2403001440d1802c0d01d8100940c031004070007801c0d05054120002c589040b962940500003a040100c0781b040001d543d204001411060340b80c00c0c010b0700d2640d201c1031414484c48d42d01410110000500c00c0c54016007a01600c0290382c080c2480c0421b030340e078840081040d16144811100014100301c800d02c24a4020705a0f8881d4100801c2580e25032802d603101000100071520403600117450340342c001021007100e69118866951030f200c25a50380042c810040020f051143c94505044c45c00c220303040882c5004098807501002c4e41400600302c01010091803400000e40700081242c030000040114956209107203420019407a50714050440740d800740cc0d404d96010b500d040c4400d62040c05a1442d52302c140c100c450300580181c000180b0780c3e101ca0000c4060181480301038030b1036102ca480660411072144250944407106207403000381401c01d03500040329442c2d244503041841d0004240c845070840c0560444000b840384401a4800c11785600b400f0766194800c45901c54035010311400c03034482003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 778061303 1250 778060053 778060067
    0xe010914040221010b040c0e13050714160203010f0b040e0303130822030c0501110309010c0305090604050a09090b0705070506190603080a03060305060a0e0a0605070c020604090605030d 81
    0x42d40c010103820b0018000010f05040c10308000582c800c6640b54110110320351550b11508000180c55918060031005030014400c606c004058074195840c900410007407100e61083c0414110015904000e50716640c940f00c0700e1280c20202000780d415480c10580100c41001d60307118008030700c81520148020384030030036903e03128001205c3d0701c501d03144610700d800001483c42c0001c0460312800750040c110318072216001d03a02c180603034008480b101d5290500384959178000301d40c0310305103411100541c80c0144e05000206400e040c100002c01b0300c840031419403500e40d1800240c030064400906100e001d142d0728039440001d0b114984050b102c01c0c14040200e03000912500403200b80d690010000c0c00d0a0f26032401c0240900f03c003a1440e2003042d503e41c0d0200000d8003100c01084810030a036400700e000c9096041c40d6040403000fa01e800c0388207192024904040d840407a04941d4160422000261660340141c05e847c440300c498402980000c0000e000b1607007518650141d801c0e100150200d403000301e48204203441c03034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 778062553 1250 778061303 778061311
    0x908360a080604120c0c06050c060c040324020f0a030618110304030518060708120907060c150204330e06090f010905370f031205130e010914 62
    0x2074005100080210741c44d1190140300c2025450890114060307074a8075601d41c01e9036001040000c200081580b24503801704642504a416407000381e2a0500e16601ca16000c480001b403e0f590b500c00000b40754503810071750306603940c0d0f003c000c1c002c0d45c5d2000c12803801002402d0501a90880a6001c1090341d40051984905415807990b503040500c1c580307464030240c41580041822060420600c581c5202d1500c45030f000d0000e4a108030025905c41441d1400c1e0100392100800e070450940c0318110401100b584854820200c1e602b0481c1d8405102406074014043e1040303402254409050b6842031020000c002e0f4844128a02e00110081c081e0881d40d0440d403003066090031650104050044000c21720f0a1486e15100324014100384281a035118046001d1f849250f207500100d1441041443c01d040c45000c849400110910780b00084030704140200104000c1804003030308500d0f04101c80c07000c21340960b04441000000f2445005a1a0796000c003036140b00d400d0040103015070034100200c0c03221918030065809 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 778063803 1250 778062553 778062569
    0x9020a090c0e06031506070b04021c0203030a050708040e07020705090f0105060301061b0f20040b3a05011b020c0a0e0703020d05180601050d030e040908360a 69
    0x10b07035086102086890b0f00060007840c00300c000000381042036580c04004000c1c0c01d2180c85260721030724190040100500285501c0241f131403814030004010390b004011543c1ca41311a00b415521007585042ca42c00078055038114110001c3c5c144e050128540e000100041102e4045a0800b250354407013290f95090002840b40f2600700700107100500400c0c1c021000d0750644480400c80403d021000d4442c4d0b0007440b0481001d0344c10542c3d2106600ca09840c90903692929030707040e2420721044d40204007081c003c1a464041050840314860ba015002005540e2001c80d00e40807030007945041558280070f4028807a000340035040c0710003512850305d50b5001141e2004c2d049401007584105a152014000281200400f00c030300301a42044204480c2d14584180c40c082d02200031114030303044000011034504207060f0416840b07508032311003210000343c0c81200d5035062102500d0102e02c42110b494650600d010303621141030b440ca18164030344c407180d0300e406d2404409e89103040f86095202601d018810b03120014012065 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 778065053 1250 778063803 778063817
    0xf06041d0601030f0f05040201030b06070506041e170a02060a050f0406090c090204030303091401110409090809120d020114060604172407030f02210a090c060309020a090c 75
    0x1080312034030034040340d00c5070042c100841c040c421110900f088612006680c0c0d400d5564400b44170079541c0c548110140b40c6010340e140b91801ca81c0f074843e2990fa40c00180300408403060301c41da070441b000003e100c24070000d03030140c4281c8060810300c024465507001203d81d031005215480015520b035540d40141d0340100e8400d02d0201080d02c864175120064081c85400f44e4080c48206400190030040b880100000d600964001030490500d00c1c0c820705c17002141413001e02d10303810206000c50401d91541200c0440380d8001001401d9030552800c0c0403580650030f012540441484c911600e108800700e40d038003910860b0350003040040600f01c00d0310016030701903c0032500444280800d001540498208003500e000a9044440720718950410008080c09100050752036601003050004507601402000c82c5240054003c0d82801443d52003a4102c0700a440d2484118402c170002c44c1018005500081045800c03011503c4503a0b00c404010313001e42070a640890094810f44800101c0e001540301c1c41c0095001a902c0d10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 778066303 1250 778065053 778065089
    0x170406170603010921080f010e07110a05100203010e060a151803020d05011e060b190c0f120e011b0b180a0c170a030207210c0e060f0604 60
    0x240c50310002009280c140d980e0b0b20b00b803404202c002086050010b10308500000051842000400c131400103040c05041140d01001402540351400341070b9800034880c64442006a201d05d4454074150203680d001c0c003680243d0b5802c00d900c0c1103540045060f20a806c20912041e00c1c2e0400340403c0104500c100301e060040410422040c51203100d0120316054255500c0b2a11501c940000b03901500005086426a55885511062141da41241c807441280072404020345071824a694000d442078a8101c80179080c11547c4260850084085040040e0024400ea003885180c0c036154900040d0302c800310340442e40c101c1030501d1540c4117811031070004401d51041e051402040d56115592800501072490255462110703166101c0704005111001d40030701c5034070003540c3c6400c44c2a03410356024048401241c0010f101d03031000c2070300001c0e1407040301c0c6490044000d8550164104050020745d0900030f058040c2c40c0400141c1c0001001c0f0750307000710021100c0c17941c0c0100307130020400280b00b98800c3d890b07090307050a00e074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 778067553 1250 778066303 778066337
    0x91721090106081e07060c112b0321021606020f0f0a03140c040b0a0e010201060b040e06100905180601360b040b1b03070c080604170406 60
    0x12640195080001040b125150b1030480d04008606100f084000c40595800103001c00401c0440020203203414441c90192040d220303c803144d510f10054602800608164090140320848000000101d00660600b0b481151a004000c181d0490b41c0580e4110300d00741d41e1031a0100c034030071500491201c01100c45050f4041d40d403071019404c16001038441c400240200c80c00d4448200c010301380483d4698000855015030b141e0890081390143c180c0c10984002e100c103100808115049594500e814140300300c1c1d018844004030b025100541041d40419400300e00000c02e01d5034440018080c420071190030100c00c42c0400211405141449180ea10044400a4048070030321f410713809800c4801071400e40d1444459030701c540d02c240500d00506035018504581400140710380700300940503003034100c15180b40030302c0e001c0030028038042d16a242c421103440c2103c1c010110b13000c00c1102c0c1e502d136201e180c01007410ba81c0c10310355450304011207050f1941129000c424076039140c5001200e0595899458900ca503440c100e0344 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 778068803 1250 778067553 778067617
    0x180605250203100603260306012f03040b040602070b0c07030b0705160804090f05060604140a08012a020a0b0f220501020a0e01031a0d1502040602010917 67
    0x166090b028111441c5100403050150720f014600591a450003000c5040c98101050001c8940c450a40c80c18008e0203c00d070b81c80501c1050003200e40b481a141c051030318031000d400300010050050507100000d80080e040040502a20449503d502a00d030326a9840344803841c00d200320b41d40c074002030f04403110500004a92600c044c5d0040001e1406606241044484651540312068180c40d0800045030420803e880d50150b000102b1882100380050f050010200c0c800f07004900517141c0c01a4809140140d17520f80104000013012550000d01240c01c4085d00b00e5400031005160f106000c140c54a5040d241d0300000d40d80100543c030444030020340d500c3c501d541e1103c8501500815003000302000591601c03980d2041c030b0a85500480c00180d480030960000b41003606a1400a410305080010a01e64070100c1004c54002030003d8500649000141c40c111090010380701200510a00c0800e01080040e415405062100d00c41c0c501c003000c0c80342482c1d0041c868041d41c4219841400113140c00c00d1104d215181d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 778070053 1250 778068803 778068877
    0xb0409051c02070b1314010203120a0f0f0504080301031b08030a0f0e03010f0f050117060a0b1203030403080402090f0405030d0f1b050d0501050f100503130c06180605 73
    0x4180c3c0c0340c107a15228102e0459212142c00050100300000501c040c0e113109a100d0358480090004510703122500c4051010040000c1c00a094241c1d40c101d241c2403a149900200300b400f00404d000c000078034240c90052042e80084c081514018440020405591400a4403806440d2004011070a101c1840421908c103007a000880040022000c10900c094070240650480e0000d072800108a00c88007000c1c410840d039050b84240f44e2100321a48030103080c1804169180c0101300d80074042980d00e044000b04a292402e030315000c2a9210000800061660020b0f1260007944200c5003850b80d0b44580501210029064601400c10b400420643c90034880e20b80c031400004541e4039021030703c2c07c0c1007194019040580180c1d9400b10302e00046681c00070181c0d10400f80034003001c492000c248140c11b030100d03200010841e510414010b0000203c0d20301d00c682c003403080f4181d0b8454000c194180d15200001c141801c144448495a425400c021400300c1c0180c0c15217280080b948031818100c580d5240030f15100003508 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 778071303 1250 778070053 778070057
    0x4092c011107060e0c0603070c060b31060e040b070206010503060609070804030c05100b094b0106030b01020d030903020d050d0608030a02012301052d0d03120b0409051c 74
    0x1810403400c0d5140c2a02070f41c881e0062751102c841c940118100001aa0010258203220710310380c014100d150080d64034840d802d6142c216003143c02440030b003007000c000c02094124100f40340001040008214100314450710480d065404d0320700c140da0301d100341170340e0764020b540d00c40e480080c0200203a5000d10070140158007a010340741101d0300301c0c56520b07410b04254200d9100d1085075180c3e11a420309042200510f41c0000e403030a03401c50b420103400104001264404c0300007400844080d1020300c80c1518690045841361850030f1814196598a0003070000c3c00c5016009015001d11450074542601a224401d030301a05900503124130b843d003010855840c0d00946400040a503940c138003003044c040400c040c00408145400000d01c0301d54007410850004030341044950218140d03001030044d0340314040841c2c402205110788090a5a030720080c0707011489102559900240010124428107500008100e0b80e42c100c001f040024041403400e0006503502c21402618540c016011002c101c0c5446c4c6440004030824 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 778072553 1250 778071303 778071313
    0x913020a1211121f050607020307060305190614090721020c030c060108010c0207230904030302250605010b07080711030c0a030308070216140d050304092c011107060e 73
    0x714140c610b075803041c0c8040c1080a88546035641121304030b0b080c0c0016203001c40d103481c1408030583c00031b90b454600303000360800c150b11400071800504004445a08650f0181014001d640e15030007519000703042821860b00c0b4020310340c003040e03085000301550010003881031072070b10800b03003583e0000380079511441c800030b01c0744401c0200c4640d0075424400c05000c1e00d0400004207085643c270070000c0c548039183d08100d0541038221104660b900b02c220002c1c44a404c251110201c070354a40c1000d07002030290098003103880343c010b440e1304c455280c940140220140714910400490741c94500d81c039804d021301c150003002607200308015404a00c0003040d42d030060600800710b441298410022400042c40380d40b0441c0804c1e9100140b200720b64040c041451082179002c1280c8400d03150880b000c0f0700703003807040200c1d000300c221105070000d0001c1441218040c0150b80d101b440340103215603004804090280720540000d00500b9041c00321071042c0540c040100724205100c2c240000f07619508010403080703801e180f43d4450 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 778073803 1250 778072553 778072567
    0xe240f060d15060201020f03070c0309030803092b1d0a0f0e010e0609040209041e0c1e12030206061306091e0b01090b1911030f0913020a1211 62
    0x388000528840c985404042141800504008800c04458021005690060204004a401200a80b540403caa1400f0340d40502d00f403e081c2c3c0c214440c0c0d000905900f40000c1044a0350500003503c501c0707444c04000b205a418444010003001c01442e520000008400f00d40e000600c0c00d502c003841c0100e01000300a22022580e41044404103165540050403402060004202c120300809506c2d82c1b2000c151690394180c541079000440301b00c8000c0006004140e8080800c003a401800704802d0740310342c00491100c203141c5550854130152285401c0800c2188400c00c0401c80d00b03403541e01600c0e000d034145c00808103a1500420403d0b400e180003004064655500720014180d80a40501c1006c16100100c048112000c001101e06036240d010180781488045003042103807818220440c1d0300400200c100440e080042803088030704118200d08840c2520001c00c600b842c0100d000000d10b5800c8044840c0b003020f80748028144140d0082010b13280100e008011007000100080c0c225414003010700c540d1514200d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 778075053 1250 778073803 778073809
    0xd0e0f090c310306050f1b0306060c010f06060e0a06030917090d0c061701051806010f0504090501080601091d030f1818090d09051f030608100f05010e240f 68
    0x2841e0300554984c3e45840511801300d0000e54a16007104800d4076541c0718134207401a40f003080c4800b8000e2802040c00040c0701c030500000b0340c421000070503542c0042c05141e41e01c600042441c2c94460740c2506c00c1c10f1134000080e885000e07215036500d80307500a40ca84040d403100305030110113803c007516140d0814000044500012200c5d55600c015000d1078035111080720340c10202082d0008160070550080840752000b1010310700590402d58451000d1034903030742114125004560074095540070007851810480003242403000800c03614181d42c1c0140c02040441c251804400207441c080607141d0305c03a0000c102040746054400700800e1003100007140c0b846608a40b0000c200000b6803140074803411006031040c030100302d8050148808584e00c524060a4241c10040045c002441d0f40a14241038400c01043c0d29a2034040c0d0061030041c100310050341c500c401d00c80900409071500c0103034800340f1490140081440c866440445016540822a002041c81c9456500760b400f88a500d145074000108076041c0815a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 778076303 1250 778075053 778075147
    0x90604150f0611060a1e09230705030d05090a0b0a180b0715020f0d0209040e0f0f060609160c06110d09020114030c07150e0d0e0f090c 59
    0x104580d0b42d03a00401c4030f00380007810554090305102405042090916210000015a40107201c000c40c0c0003401c80c2503498504410a06486d511028244035140c00c100c07800c01283c00001c485050303094582a111000085440b4880c000a0640c018180e20041c010700d0390010190507807007520f08100b03420303408013140701180701420b50181c8000d2600007555010801d04452040c0c0103845408290306104a0300702d03050490007654140440303240d010030000a941d4407034000c28039960740345051318507400e403c8020b0340d11081281184c40a502c92000424214241171011a125004e090b03210101c02c49a101e041340d24a14203201070f80d042c0c0e290040032802d915490020841c6184044002943d4a510300c00074000e40342400d01968159000d004000103c02408100c0b803150354001814030218004001e01b0005120b801001ca43c90311490000c00c17201a0880ca0b03482d050241182c071070200c0c0c6414401c0000200d0100d49e002858401400030000c8410b40d01b00c010022548a81141c00c0c60b422092801442 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 778077553 1250 778076303 778076309
    0x31b01180f0210030c120c0c0f0b0402011701030302190f020a083702060703020f0102070605041401020c0d0e0307030203060c0714030a052704020c0d0906050702090604150f 76
    0x6800142110070861900c0500c1d90816041820b050011481c500400360102c0c5c20b800b11290714036252040c1700403491050751086440341d403010810021102e54184044050790480307003240031412131100c00a028450301c01150490783e06600401210180c0b1520103a050500b00b000c84044907400c1803040103a855a040c030b0042d005d0310000700281100d051821241855010a803d14810506070544128880d61004040b060701030b21456aa00c1c0c00e031034124941074804240c001203500c045102402c004032900102e010300d000310741c01400c1c880c444541608078070449001c09400d5109240301c281d02802610390101c01c20b40101550802c5903203401003401d00c1c10440310001440b43c00035081c0b0800820091540c1c1d880850f10045040c040c40c030708060158450341314900080c14032401d40d4a501081943c5000c2200000792041d92140d40c102e5400760350f0900254290041416501c0c0070412070300c41d2040d10005078000f0320032095921030600340f00040c02040b8800702d40d0402d222000c80e400144205120003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 778078803 1250 778077553 778077563
    0x6091b01050d1b020a050d0f080606220b0307020c0103060e070c021507031701080c1503090715020d1d060f280c06050c090603041101030f060f0504060b030603031b0118 74
    0x401000761800787d00b003c112803880024811001400c220140d4000e000d107910500030b40e07040e6610140390680b0001b0503c9840c0c28910042c141c500800c070003101c10060742c0200c00540885170b124100000540654042c0c0c0200910346018034000b600141c811950b0f6100980041d1540d4141c03c07040900c00b902d54812102500410f04c1000b0f4000030701980c84c807035401040c00c00050040c140d01c64001a24001d502040000c196030040042004840280071410007882569940141c488509801944800c103112000000c00c0220041c4424865135042d44070b02888000c0290f031610103d8075000902d03412031480244013000c07042c2071046c0c4030b08801250407440d4017603d96803003042d00b80c9800c4041c0c0d82c0080092000b048140041d401940756038041d640c001d540004075110a09041e40100d000301508082070082d01d0418400184401031080d4038010344400b907409022132900d41710707004480d2000366540c98055104020404420152110b401d8911121038004240c400307450800d072400c510300c0001992 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 778080053 1250 778078803 778078813
    0x130212070e0105060405100c05010b0a03030c02030d030605060415050c0a060506120309010f030e16270218040504032105060a060c050d030e1f050906091b01050d1b02 73
    0x911418480d11401800c0c01c0707504da03203440d042101048094010000d40c4052040c401e50b40400c0110a4001c10012a0040e0000100a0740c0e410010584130401c0e1003a8081d01680c03a0344109184a0b01401007a248041e1049180c5450010701c3d00d000e0103c07072005810010700b48003c0303514940501102060301d0080e040802e107030520303a0412900c1c0d0782d91103800360070380e1080001c002d46981100440b6502002ca0400068111841c81e1075800c00a041d580711403411104c8001181c84940344050301e4a04500703c9111740b0412250040c64102d20550b4410b44503c1540354100f089441c042d08440d42c490310900e030865501d004e05007a0603803020b16400001e0255256410000340e0304100d55100001c2c40f03a0301e030455a10300551100394550a002150504054942180e001401b0040048803000201c2d03620601d0240c40003070500b401090b042d42c128066000d5000403502220000490104551b000483c0600e07006160006450307070b50041d445580d01549454a41c441120742008541c003103042600501 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 778081303 1250 778080053 778080059
    0x1f14090304080706050705070b18030a0302060703050105030a02090103150e0307030c3c0302190b040605130210210f050f010b0f07020609040b04020c070608010b0a0503060913021207 80
    0x1d400c1c058244c00a00402c00d0601568012030800030f041401c41d00e09082c200c0c0c1d20004581c91014040405400b280c051140641240070968000340c2d082c41104a0341d010807403644c8070130400d42c03100c0c40a007010358081d0900c0018004140300c1149980891340348180081d01680c40e0f407000d030464200d1b01082d000310300041c00071381c00c0c0300d0341078007890101c03c064091054161030807425859050959200c080114200640b039810140200803902800f9601c0e4072015180316986840041c401044604030b031000c0c2000042050411a148400c54040e402045141a103003601400c45101c2e41031000051000383d440301d4140109094400c000350650091408105890011010840746c0c00c180c2c05680b040c8000c002801c071800401007600c0702c4641c1110255036030594900003c01600842508982c0f080c400250440f0105000501d40300300c0d04c0303503112086907a0341c03660b40e5600b502910f181d84010074010400203102d8500024002da020000c0780c200301c03800342203401090001c8900c0f49480fa60b640549424 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 778082553 1250 778081303 778081319
    0x6140f1b0f010e0102031303051b19050114011229070306030605070f0e1e06040803030103030f02030f090f1201090501021c150909020a0812030a18051f14090304 71
    0x19410050f0b031040203525500700b00d18401082121000054200103011031520481c010402c1c80c04c508a45000444803520115201442440e03001581100d441d8646403805090b541e00103c1301c0c2c100c400000c40980d000945844140740f080c25000729001c11b4a1404c50310380b854009840c81d90245500d5035001441d1811460702104544010b0300000921040481c1c0400d1164050104140d00b00d042d1156040440100c43c0307480b00c41c0610040b258000404280420040400130145040340d000307655030ac0207980071803410b036201d115545003102c650b00d080001039541d003440c0507001042d8002404c0d040410001c00025402c6541c5500112903503500024030091050801ea0711105200300040204540e10503504e002c0d618081600c9150789881c2c513000c01307509543d14103082c0d8001b031981c6400e44118000100b90085030b50b00466040000500c5c21204004841d01241000fa00e150b100004248013030501d00c14850280464560101d42c9450300b4501001c41c24514506002e1541c4a00860b2a80d0400c845 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 778083803 1250 778082553 778082561
    0x6080606090402010f020102161202070e0f13020f0d03030f0b03030a08180c0a0305100501140f130216060b0a3003020c1507020a0f06140f1b0f01 64
    0x101096208500380320303466031a100300c030750032980c2402c00e01c030301e0304c2019420b9019010b1a1241101410701200e908280803070961242d604441d0b640c01c1d00c0e074258603489c4600d040501a180354070342044030343c006207480c00000e0b107407408a4001403c61464810000c00610a0070400b030044000a4407540c114100c4a01da0103504801e5400f10050750074038038610b0000b0701da003800802071580c1900705400d011090805115a13403034081e001e8481c203502072700c0c0e05040d03070381d00d481c610314030101c46c507100001491440500d0402c51141005091411000d807a108100c6110f0903901003c0c89036500b00502840c61035180000c00c0310702d1042c0000b0031a6039040b010000c0024030703580901300500640c010520001d01d03056a00400e030130f402444440c0c14030740b802c0480c034122460541c07071b402180840c84250b481c1c1c040b00181c181d640c800c883e0225440c1e00c400307e04491070f115208000119a000c9110340322102924003030822500d0050345941450100200319842c0c2e13048587d048200d4010380b48801050300d003805 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 778085053 1250 778083803 778083809
    0x4061a13060806030c060313020a0609080f06040305180a2606010512031e090a031103010f0e030a0c0807020306010605040e2a0d020c151503120d0e0a170d06 69
    0x1800301c2c0742e140400c0400e440350b0b24488124414140080051392250407070407503135000b94003c0e00144d040c5846200c040e2800c0b269004072800e40c4600234929140e0180000d02c00e1185503d5038909003841c1e400308104520294410320113900c800900300100794004144c1e00300d00d03e02c8c040500100c8440c41d9510a50400308107030031941c041d500300014950245c00020468a001300340c5c0108440c80c01c00307200b6003d02d0b4041d15840704e51000c060f0b00004180140c2050851800e00210003c206c1c4882c030080e0340f0120f03280340242002c160414400c0d023940704c0c0120720024219010311001d5180040560000c2d041410981144010420100301401078000ca01d00c45c035408503c50b480401800403141c1d2100a500404104210407440001c09149400d0280c0694000f80d401d02c0481d40c0d190030102603d401550101c440800c1c2000c0b00d48045001e10300000e61001d11000c5003101c0d85040320b200781c464090b100060480220340302e819803100c000743d10804404c520401d14821561220f03c3c0c040c1c62029201154 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 778086303 1250 778085053 778085057
    0x10f0203090d03031a06160209090a0524060f10080912071a0f0f01030609021c121e080105040f1b030603031b02010f0806030f0106060206040c0603140a090204061a1306 74
    0x1c0f14800907c46a030030b05484058048600d0301b0030395038220b040c610b82416194002c00314001d0440c048045000c050100d800440081003918584d5203850038080500404480b0592020219060011043c081d217a19034000f4640b900391048640c402c10100d200da07110b40c204a132088251a6590b844080081c070b0ba9401000e200e0107041141402c80c1d8418030780006000c00f510f61543e82a060007195540414000080b4412541c18800350072410207005c002501e600c00c0c0007007041c80007500c00510510b2a6840c900400c0e45400344142d007808203100081031981c0d4504c50712540d9a0a1103220000f10750702d401c081d8103c1e40c012640c2c0b401c6140090461030701900134485411042400b0300181e0300a401c44c41e40c54014070341740549544100001c0c2ca4240e40400c0d0014951a185006c80e20a03030200d60584201d0294403481c08059072240c003141100c1c3c20364040758070b4010020100f260303108284c0001800600050001c10140d49406800002410ba41004200303400001412001000d180000c0b1009015038 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 778087553 1250 778086303 778086307
    0x5010303020d1202090a0b1c02031e04080c030c100e0c0a0504180c08030717090a0308070804150f1b030e040209062a0708011a010f0203090d03031a06 66
    0x9030354003075900c012048400301448810004002020b4040d41035610b8104000c148408542d55a540480958803440f51020f05a50385d016965151344a40200c0c0d009269603040407646901d040426400c080700a001216107100801c850030100c2c5c4100080c0c04c451074040702405081828801440440d580c106000121f90088102000e103690380c0e400280c00c803482540c010070240d140148101802c031031400001c142c1c00c442c90000ca9403100020203065920b105454080c40e20000d084440d00310b0040c50925030348200442d2051000401041c054000c12348070300c16180c20541c070780000002c445a070004103c0000e460001e45204c1c5607000040780e529036414004c4a00c1e0399000c2d01c0082c007c25420f08028019500050307603082a40b1602d046401c0d524261180d42c00c038880c50a40c0c540c1910140b007000c0a18440d2101c04035840c1410301c00d1103a000c500314100c003407241c151801510102c01c24040b1100354002800304403540e40342c070142202c40511990b40021100846540d103010100070205a501503401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 778088803 1250 778087553 778087559
    0x408030708011a07082a01050916050d1205120f250206010506030612030d1418030d15050301090b0126190627050c2b0201031508060114040501 63
    0x600c04035040c0f1a006601c0558821030030100c0c1080c0300b805d60310301b042d00341e0a403030340c013194003041d40881c2c05446040d007501c0111a0449990708950034500801e1351002449580200040740b8520420114406080c2a81041000001c240190400300d45225140d240c040c200a0044082000454001c120b2001a8069549000b000f07694000500500d405201300202094141c1d0f103080030b9280ca0100d11007107a90b41d89400300100c0240c0700001400000b0890703c40070821880c070390a2902c69008142c4025403c1c0074090b4400303000340c5541003154a42c942e030f0010124082d2001e0007003d8145026083c08103d65142c08a600301c0c2c41503159400c0581440e50002020201003c50400b80f08405102c11540402050900200034010404900c9400500c0109200b0b866980d00a80ca01c2601a1050789d40c0b6556600c10300860024880840c0f500d080848214132002900c070268107015801850000380300450850000e01e0110b6540014006511075001040044120080460f0811080d54103001c40c0d45 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 778090053 1250 778088803 778088849
    0x605040b0907020a0b0702070810020d0509030c0a0f03051605030315030309010906230c0f070b030c030c0705070f120b0a09020603011701290f01020c0906041e0203040803070801 78
    0x1c2844c0300100600b4421021925040c4200144c01c040d08001e01551800c00c81c0c03142d008002e6004403c0c562549007000d0000c1c14104010064030728900da46000740c550215560f40381000700003050400c606110302403242518504002105000280c440c400456603400d001e640980310307030602416188685c2c010072138141c0fa039a20200b888115901030030040c1c41f0205c400401d1002c1c01250018441000002c120000000030009400c80300405550507900c00c0e9071510301b6924548400c0340d2484101008001060541034580001c1c10000e01a10a841c13007540c07120f0443e4103000c43c50740404180300c0185041070500064188690300155100410442001c842c1e0108429002c140318941c04038910201c60082c2c03c400b900900e162510545008240c000450340045034403d01000c028050341500420f02501c1d400060402490381c0000e10b2407525030348000030040500346120462565408010341d50170f4401460000c2c5015074450000f1a46a01c5c0001006000d00b0b816070060044080d449090b100140c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 778091303 1250 778090053 778090063
    0x40312020613050d0e030c0d0b06121219261e0108071a0c0d020a03090e0f1b09040f06030227040f11090a0906051f0b1e0d0605040b090702 61
    0x9655410724491719600300000a007820058104a90001206400300d0104402e4000c82031103014119107038610407a41550081c0d0390818080b102d1441d82080000288180e00c0e807400303185188885c6002d113500368940009410480e5101008900045208103103c1c28600c1240b00c601c58a40710f880c0d4580d658941811207a03103016903c202901d00803002540c000e90340c1351004407407040240c1021100c040300500301c000c3d5201e5014006400041da040c0000c2030052041400e6030060100c50b03c2d80080d038880b06040d160011640b40c0ba00c140e00c1c0c00304051401900c9a000d1000060007100c4000341052031801440000c0c08104241d8a0000d0801140140c10a441680b250000d81000e85030401007020320700000d81074400302d030640d0b00030105820013505001e03036041054031a100f62010302860b240d0030502e94043c2184140503180715500d00381441092a410054484000090400c820710000f03621070405960004481000f4940c0761181800a81014020f690000006071907100d600d15150100a483d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 778092553 1250 778091303 778091323
    0x303070210090815010303021c0f080720032503021902040b041d0d020d14070c0504112508090f011215031e0803010b0f0705010204031202061305 64
    0x103907142040801d80c0078840c01d20394020749941c1d000c4800407042007500d020001e80920003100180700c2d038074400d0b1052008a04020002c14261105420030103501e100769081c45e0018000c0040008094103002810314031030107400301e104144003a640d00c0010b03240c2003203510880308081100b07107400380c000d00000c0d0380014217180651035a08518200b598501c0040e000d805407498280d0303c103051660100c2d04014506088003080c0c051000c0300c0000c0e40f40031042c1e8a90345070000e0f080220703240c5007940c00218103140c001c00303005103d070044140c05521a800035080315100682800102c00101d0014501d0080300756400348415440100030755580180d40d4000340384244000180921060703114015664040c17417065400540c00c00d42880101c132107040d6084220018802590039000240010f40ca100c100c8440c90040c903000042d003859682010400b094642c000040300e840060f0130490440807441c20f20141014501c101c0c050b4500d190540c00081c600310010382141248607a40e14510300103000000c800c020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 778093803 1250 778092553 778092559
    0x3090e040809010503041b0306020d1407020322090e07080714090118090506070810090b060316020a0f0312240303080c040317030937020a1509170c03030702 69
    0x178075904e0703241c00320490000550740d01d51407002e200c001c0100203007030b00a4409801c407140c007080345001c07000d2060021002664510b01507002081015900c4901d00441c41d07501050750510f4040d6507035514a00304803a68120740b0051604140000c1c0310300e0740203200c110000c0641c28050b21000c3c0302c03580043c3ea84c0380180704503451310380421543d030101503580d080f085c40240c001c5c095540915240c80c0241c8070040c100e078050140c100344840401c183c04a4411317030320300160141c40075055507031710120406941c1501c11007100303610550309624000740e40300700f550b440107220f603913030421035100e00c0c000a06481c3c3c08818400300141c440c1a07200f040d02d0301d40070681200d4052a04035100c1c1c88a18804032039105079000500703400c00030381602008a812034020340c0101c11030070484540300d0720034402c07840045020660296100703803040c95a01921004022200f05400280582810703036a80503c1300c0d40c156003c00c00000309042240170000328424081d1f07080e60040391005007151304e004600080d280d109100000744 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 778095053 1250 778093803 778093807
    0x10c0f05340503031032101e200a080d05060d05061e070f0806010f0e0a060306080c0405010e011a041508041101021f110412150b270402010c05030307090303090e0408090105 76
    0x1040380700c4c3c0d9a16104101c23541e015000748001c000d00130710031074419034400191440801184102040028174800442c0c2041300c144c00d141c2442070711405040c02800b103603841409118444081074080c01080d00645030f40144c144405050080c1140304080100304a0600801c05203a00e00141c000b18502c0d40000c0174640420061300c1d801c4d058501c003c018002c40d4008001090203d0900d82581c0170320180c401180446005a8201007040305680b824010b0083d6401194010440011403e4413982c8080d8012031990405480c2c1d150102d905601540d9140040c0551082c0700c148080d400004281603000c0c0f0151105420311500d50f42d0610207202d2510440d9950308400320200c440174141d80240c9444814403201008a0a000b528500002d588020b1107143c020780000314078280c4080c080380420158081e041c51401c2d045032a94140041080e0705200101c40f840c00040c5081c80154030840b01a00d40c10030340c0d0301310b09006200844030f1b0000d0a12240010901020401030401c0e61804502403900c03607 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 778096303 1250 778095053 778095079
    0x3010303080a0f0c02100e01020c1f0609022a1c05090414040503190801140d0201020c0405090d1112072603040302010c0f05340503031032 61
    0x50050404840c806a0f1601e40480c59026075030116009002600c2c0c3c0c02e05014607020b0f506000d00b00d02c074004184540741c1c00aa18140e079416020700301c44503061041000505070750f44160304801d81e40405400c075156200c205001c1280000c40e00701c80001140d000044c00960051204000702a82e040008014024086980c45495550340c02428101e541080c50665500303040c50916501d800500880030844000301e061102240700b810468100e40c2d80c0000442e030143c0c6101400496020642c090781140a00c080050f1a900d49014441c0201100c80042c15500032003a00200395004209000140303030020382c458a004480c010a5401142d040010b50341182c81c0e0100154404018000c00108650301100f00414181c066101150043d4140c07103110600802ca42d0482d0144140c806007281c0850686101040c1040c0c02407a403444c02101540410610f01c60f181c0510f50f406c21903ca503400001c50f4410700c1800d07032019004007007107035452115503000f0008c60100c0c2c0204c100c00d1410301409140c8480 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 778097553 1250 778096303 778096321
    0x6090507171320040c0c030509040c090803130f0b070c09020a030612080306030105071b03030e031c1a150301090c020c04061e0e011406070203160e04030e0609060301030308 76
    0x54001c480d80200028091060107241c03d0180c44640c00e00c0e4840d5243c00c000c459a5401404d5100c401d43d4190f48052030b1205800410004140c1c000c80081001141c80e40032840d06800c00003407100124400403642050b107048050309922540d6045100882000d00103c0e0001d81da100c41401941c011040c00360f181c14000c00210000d182d540c0c41001c011045015902c2400683d400850160105078003e1000b030755030190079a80c054210409014000140c3c1c1c560000c203200e40d028003c400229000e8901d454015a1185614580305100a075070b0303607445203e141c01c91b114041c030404101054903101c4000407500b811705454001445030b400c983c1d460790034800c2c5291003481911034690b0020420000d09803243c0d50074204003080a050405042d100c00085040d4070700e01d0119049030446c104800e5941c0e40b80091081c01d8000c0c1c5401c9815206415074900b42d01c0711000d004010f0041308495499501e01400d00900c800c8100010718000c840800c6100b240d03440d0001102e064a4141c01c151020303440d1101c20b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 778098803 1250 778097553 778097581
    0x6090b0f210711010b0306040b18010b120d0e0a1409070509090c0304061a0a0515040302030102040621060e040f0305070609060509280308070908060c0d0609050717 72
    0x11907052008110108540c0e1504250083c02d4200e60400030014800c6031000e25507551340c01e460203003540560000081d845000c0312a01c0c070000c1c3c0264000f041800340103000c50a1030821454a0365183c000c040b0300300e64a40e0003c1180c0001004480c0b603000c991404c4043d160155180150324000e160440001e20098010f40446401e003c01400300001c42c0340c5400c0b541c401c0c0d04191011600107086c01004c0d00c1e41c1c801500d4060711460020a000302141c40d08042001103c4860018140030b1000c2c04000f0241e078003131010348010500340d100c038030400c00034081e0800121944844110200d18040060080907110f9010551080c0e0154400d034445200c2d00302650305000f034810040410f401c180d80e000800155420407405000b80008a6049000003002081c0c02d000b100d4014490b1000290340c10003203485078045a40140700b60a0843c22a621044141c0c1800b008860748a0402030004100310303001d4080c0b20b0a402031015480821084c14000381c01041d11f50b00c618804050380090010a00407420408 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 778100053 1250 778098803 778098847
    0x408070318080708100507020c01202b0f050f070303022811060618130221010902130207050c0f060904090b0117010209090106050a021509030304060606090b0f 70
    0x881e11801d9540d150185d032800100b01c0341c43e80d10f003010080750f50350b800013410700b00c1048161109802840001c1e07203528039800006d941002d0b8031420a900090303100340c200880402c107241c90040d20b682040e05c806861614083c1c2e800c020440104034180c0c14103a081c0580309110303894a00942c0e102c245802012041c105411040c1d01c898510108000050300003408400e0450302c40140d5100703640d11020800c4203000b5200e13400d001c00780180003070300707103450b07181e03c118801c3c401005448040407901c3c08142c3d0a4150340d44014903990b8155100541c81c00551100200207818410340c07606810b5620b550301e40340320301e00705400b500072682059240c4e660b010540d91900c0002e0010402103501d402c1c041c24040c82880349105c0540060b40410484106008540c010840502a0b21040c1d1030000111000c0d8804400c807004c5001d0003070b481e20b50301518406103016a4010004603202c2c142820240111140c60784028144810b0030750030881d910924050700c41810f50880580e07141d039400320042a50052801c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 778101303 1250 778100053 778100069
    0xa0903080307050c010e010e15060301020f041706060f011e0c05250503070b040b0a050f0703050304030215091c17010801060314010b0a050d1b030b0702150408070318 73
    0x8810044443d6102c406040c1c2e6041280c028804c0200d40000c2c94202d503001628101c542d0000b0181c18600f00021014036008000900014074000091190000c55005a081084080c04c090f8428030f1481041080300d41218040b074880700d64100900020344035541c541400311214030316071944c69085000d00c2c1e0701161203401ca415150440e243c14102c80654118800701075009554603030106503414005a814256050201c980b440d050415500c455660024000d070010480100080c50084003c20040c0007503e209445003038890900f45800390502211010088c00d030082082000900f0b40c0000b0b0043e100509070700d20300c51210b0165822980b0b8500f580280300c0c0303040328030300029200f101580010300f124060720240b100d42114822250030b0318204c550403584202d2603032050203589410729040e54020310a0b00801c0a4000361858050481107035401a54101c001000308061543c0501c8044444001049003a00919095540744218051608042c1c1040540d80420059000300d41c2040003409241d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 778102553 1250 778101303 778101307
    0x70309060e010e072c06190f050f090412031802040207142139012403030912020301150f080d05040803070212010f09080304050d0c02150a090308 64
    0x60350403107001c3c040d00105030840d480744810028030202e12560303000c4030f400b1240d001c4142c1c4501400c240d40618016121503132000307101c40d05555024080450400904484454034840303480e02040101a840c0100c140340a00000d004220004a04c194140d00000c11401d0004000e040074006000504440340002c0d0400c5c0700054101c03d00058490700203890006e03004803204510328015209024901840c07188405005200301003a03840c9540c0c40303161007042401c0450541c42210b614400100c2d0015800030750365502c19046000c1c0d180c404015090781d0442190505140c91554024101c404511446411103c1c1c4000207046540a40000c00003079016030040b0300b8580c03903c14406104a0030f00c00da000311b10a08003001002405801581c00700e50311000039600303100d80394003802801e6001d499048010355a40c0d115414aa0803441041842405900c0141e16441d061400b149448400c1543d0b400703104c40d035180b0100503601c5140160440d4500300403252110000b500c19110700800e80c1006228040c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 778103803 1250 778102553 778102571
    0x40309090f02070209090d052506111801090f060e1c050708010e160314011407021b030613140106081504020f040e060720030c0c0117070c020907030906 67
    0x341c0d070040d107a52402200c2016454407036414141c1c0d241d0100074030740d01290050100368100080d400d0b11041c5907020300100802c01030655a100301301c4903c0000500c040c0b1000c00d140c88000200d420b2000100805c2c01c1c018081800c00071200d00c1e0041510a18007041014000b40c001034984000000e0403115100e02800303400d41e60318205450b5049401000300c40c1d03281440f035600000c030009001f81401c00d0300c10a002c1071401d41c2c8030800511041a402030f040d6480e403900000070140f180120707205002580c00742c1641001190111044001104194070a40c03108040c003580c0142010f180351002e501442c0d038218900c0d004001800341806a00c0084207018014481c1008002c9008240c800c0344200c880070b400f92043d104100403580d00302e4459609174040e01c0001d007901d0050034020700c1c4444003000151100e0350000e040340386a00c0540c40940c00c5e00884120501c0d541c110b15207075060552141420018a42800018415078901030003070700c1010a0800306600707038002c2d400b4040960f04000c06001100d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 778105053 1250 778103803 778103831
    0x2070b07020d03060e0403031112042111151012031d030102070f022b08130605030c090d0305210103050f030a0c080717070f1e02060d0504030909 64
    0x181121a000035001c1e06260380c04141c440e00c0f4201c16180d004007401181e803101c0c2c400f100102034400e0410140c190400803e0342e241c0103075a000707104bd03100e04070300c21803030310030b92010448141780e4100750082c0000743e0110300c181d150200d0002c429140a14440302256600301b420b5010b11010340c8503100311001080c40e0000d05900406a032544200c044024441041c00000d0608030310503883d02425a09000000c0c50052414803003800300d02d025800d00005d42020310454041c211311041d821503a51000041c07440080303e5403407041c0000d12580c20500d085181089242d142d601c0b810f001948100c0b00c1e2401d44040500a4041d20500c2c420148406030251000943d50605102804191050701c1405913080704448008204c401e8551603030344010341702c00150b0303c042c49500156001c98045590032040c1095202903005028584d004a185041000c0e403070030440024114180d094201005410748a0050b0304c5050403500000800310000419903624103003100c80b800d80307800160302d0600741040042204 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 778106303 1250 778105053 778105073
    0x206030114150c03070b18031803011505090417041a07170a05091207330905101d090907140904020121020f0a08150f130c02100207 58
    0x1110548100b641e00d260004500d6a50160900b0030000e030b88104101400900c402a0003508000085404c4451918601e10541543c2102d155002101d5828220004d0703480c003400b40c00d0002e028035052108407070030700c1b01203407008a00501c0038041c50308152115516a8500381202c00a21111551092824030940c54550641c80901c05035202181400364905010748107040341d916440e0394403040e1504020109029410020105034100c6000e444c1c1d0010395040403d003904a0001407500d84043d11548041c003d0600349520803070810054118007d000680f99200601c11240740390411000540c903180a0a10000f0390380201a001340303114045c003040e6940002c01031300f42d44d403c5400003506c036601d08c2400801c20f1704480280c001202c07201801100745481720080802d2124407409031a002c907619040d141540702d50b44450002c0c03001d00404c8510341500e00c43d44407942c81102c0c03030350710051490f00090f6101e02c42d51100140643d920b00c004d4116008101414400d001410155190a040c1c02c02003c0310b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 778107553 1250 778106303 778106339
    0x2040603030c021215011a0f0a090527010e1f032f0f010c0804030b01180608010e0a06180c120c08060103051c090b030a0905011b08150102070302060301 67
    0xd007100810b028a503a07005c01d140b0729540c94001c43e0a8268a000304c201c00a480103040e40c100e40c103040200801c1450000300620f03205103692685e8003600d24010a020304618280707050484804135410841c101200b01180d14111010361002c0c110035200c3c60003d9041c021106404020540a100008100700524005601d80d80990409002d028803000085a403102d8186140398440cbc94006009625030254400c0182d8038020340606062584942c0c030805124800c0e002560b500b401e803840144441140c1c016240500500002401404406005140d90307040b0341c00001e0989498011444035040c440c11701c44181500903520307110361030380c0d2138803180640c0143c04d0542d130981d00d524010940200000b21603040703a910800030702c803114a50416045580340d0103224020842c1550303000480c00c201e140510300840c40c96034000303441c907550700d4020700f115640004921001000740d00711030a2508a240c1d154040c2c1c28034207030b480e00306140004030304000302600004c0d400031000c0008118505241035035450 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 778108803 1250 778107553 778107559
    0x60b13180b0a0b0d170c06070e0a0b091c1104060603092d06150e0117011a061b010e01020304080c010c0c20031c0c05010501050f240702040603030c02 66
    0x309884540d54030050f11160103002c0d402030f030000c407800e0000c1d01c02160800e129039940c43c03040c144000071600e02d092143c180e071520002411100c018a0915110388203000402200e0301c114944042d280104540002d200d2103102c0f074406034410a82804101084220480d5009204010460700c80b10301500903c80440d00b500c1c02021405081080980c87c0c4050848000d42003026140f007045a44100203401d140a0004c0e0400c0100b800103080d0180161a5020f000381d000001c0c150300d1240f44440c21140007a68000d80807407040090002d43c0c54500c1215401001651481d206074541140540504151203000c91107610000400040c011100c0c00751500c41900c4000303110781c90030480211071204d19010081c00c20b10301d0b90b0b4410710b9100542c3d440007004c1c03000f9042d46c007044007032044803806445035009000801c0c5000000000c120082c8903180c00740104461f0b6000c40f00d0b811000c00c41900f503194411b04001514909045810a40350a44d003819900034000e025160726480d00a114007580c03101240 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 778110053 1250 778108803 778108823
    0x2d07020f030c07290909100e010b030708070f0516020d0507270519050403030b09190c111507023c0a030804110a0911030115050a0c060b1318 62
    0x741280f9010096800c60b4110303020701340116042003200c29440a4507d401d401501d40e400540031028000a600a00c011429241c4a2230000307405000701000910380020003030700005801000390032500366404801c648840c04641070252021802641e00b2074400b503ca4030840b1400a0301401d04400c44421219115041c45000e04410604041c1d039030641e0112254194030304c408006c440954040c070342c054024500400d0040020000c103000540c25201540102441d6050189400aa0241e803000340c0071450525101d64240b8507058445a031603c403400071581400100d08500d00c01c1207a0032441140d042c0d0521250b2200c041025002c20362110081a8880e581012680010108581a0315601511900304540c0c8903910054405a4680f072958070070355490011482c00c2ca18407400001c0115680c8a5540354102080020130914030401d613030402004004a0203015446000482e0340d039441040480c0e07001070a0b000810018240c0741600c506860100d2111a10844031030340711045000700103440c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 778111303 1250 778110053 778110089
    0xe0303010b040311090f0105091b0c060703061d04020603280c030c0815220e061f081002090307030204180629150f1b062d07020f030c07 60
    0x705174820112440d0080d29003000040205003002240207074040d00500d12420540b01c40f1401803942c1c0c00411242c03c0940c00fa20802180d103805100300340140c213008660501c051a000c00c03002c0a0800180024056440400400d41e041c004c900b01700540107804203c0088040c3e2255104020132003000100002404d01c400e5102140c02910640e00400300c0c100c000014403000c40a210a04c2c0e42000108100319406200da80d01e1100d0307210320079a9030016405050181032404101c010030b4a070715010074503025218010444820300048544028000b00c03c0541c8400c2c102e070000f03060081560001c0c1d081402c0c114124081500040214481c0b03111700c408018180070f0a08107030f510662124040208c40345001c1400b102c2c941030780c100d1044034061000500d0880c0c01590070003d80c11100800e601d140c030003c2d90790071020040c081c666022402d0703909410100c0780c5034100321214015655030514501010085100c85200b407090210342401c9400f00d035541c0c0c42c22540c040e918800c4d17100741c1d001c407081c040f500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 778112553 1250 778111303 778111309
    0x120115080a0c0509061c020d061703280c05100509010c0903080d150308040305010c090b0a1205150a030506070f0509101419050304021201090f150e0303010b040311 72
    0xc80780820007941e4440c1001130344030a1000b65405031020000c0301040941c95900814240000c5c40c11844111011074070f64a80300300e0b040c00d107140f00f0051400360410f1208010207942c514141c1e41d9203001c0012003004c1c0c03170701c1c0ca01035a2803198100050b00c1070040456100545a082e005140140780b100000c0109401c0490200d030000d055002c004d203009000c04c2080300c110360b150040c002c01c000300c007000c6001590341e54940c811540a580229101d94492285c403440f03540040c9400002c0c000d00340241e15012100f500100300c100350861528100350303204041880341c0b186030361081518801404c0540300503103c0c101595111401c4071511700041c981a0441c0d8254440c0050750b11103240907114a2000340362000c1592040c544144204c00601e0610035885009855030141000203004c1d10340950740d00700360050110000c1d000e24000030517070404280000207101600403400241c0c00160105544980603021005403a010f10212164807005c0700206a0220700c100800440340710302407614503c0340130418 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 778113803 1250 778112553 778112561
    0x515040c06110606060d060504090c0515120609071e03062607140118060e030706050705032a030c0105010512060f010905040503040531050108030717120115080a 71
    0x110031510b0f00880082259814130b50050040ba004104010034035a07220004901168003200081c1d85c10004008104410304080380c83d01c406582c1d0100c500c1c0b81100c0316011640d80740002d45124044d05090340003e00702c80c41041e0f860211a003d4038000400e2148542c004d01402950280030034400315159504103046c0390042a03501c01c40702c05d002e401510b150010750042c1c05040103a144c1400518400c6c1c44410b0120760b103410140005440369480840d05c0d8044c10b1811301e1319080704084c441c0c100540713070100b04004181d07605ea0b10740b511501c0c55280c0c002e50800c00c0c5500200c5e03500c211300c0040b45800501e50103400581c10380d4001c2c0c80b0101d8401d05210030f80d60b1100c095411040320003042e030050000d8401c0303800c03040d405070003501180d252507038a101051074210700400301c201100744004184805101008440441c02c4a144180400e50414120a48a00c40c01c4001081903075141051034400c480c1000340d0703020070f00c92061481a5a9200c11070780c2442c810001d050002100030b0300003140d114031442 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 778115053 1250 778113803 778113827
    0x303090c060322200a0f0e0a0902090a0f050a0b011713120917070b0a0f110601030501020910050a0914040912030b0103150e06060f04030515040c06 65
    0x80104030090024050040a51002d40422162038011101e40c0781c2141e0f824683c000319201340c4081c4280910f10007214400d1194804661050b60040c0d41000200e40600d030317143c06d40e0351180e02d240031900c2c4c00d0309540c000e0014400080d048140034040016000d4540d009020760880b100302408507075141c80340142210310b40c180700f50200e2031081c8008501594100010751000c00034440c481040d8040e281c0d1344200305d11040700c0e8005002520144940c00000703024400b20b01f91900140903113420103050f003490f4003491410500300449282c06802d42d505c149480715981042d0420380f07103207584904065020350f002c0d07401c69000f086242007080340f0300c1c4034404440c60343c0d406aa441420b01d044c1100807007a00b00d10300c0045c0c0d101d03448403904004541e0461a002c4145c1a0b91000034a1003c11000502916400416051030320030031007003003081c00308001d01d866100b05c040300c00350350b11a40445c0b900102c0c010740e04041c1280c4190414540d01d5603c5500c1180150b00a0b00c0c0c1800481c0c0d100c000300c81d0401803079 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 778116303 1250 778115053 778115071
    0x4051c02061608040806040602030711030c0a1511120f06011412060111010f05070206010503010603081b07150e090606431b1a2b020a03150501020303 66
    0x36222800340700d0a8002c2c6800d120310340c614a0141d843d00340c5850013000b900d00b030300c2055001051010ba950081d22090503401280701440c00d280e4110041c03629081c2d101d0b0b0150185150f1400e15110f4041c43c1d02c100715000c544880903490b5a40c054504c5001c0c00c0c110b1b02a40d061940d8804034840798020b15040211585009240386000401e80810911840c00f800080c1403110709a04e181d5001070a00805034030300340d4803000042c1841e05442c003d00c2c00d4810f90005010743d14040d0300307101003664201121004010030f218900142c0c88000050301d4119544e21462581d042c000007404010340c06110001030f00411120841962521810031045104941c00280c5025900b130382035105181104031041e0380307101d9008481c801c4604900c0604600c0300c401088174a00004811410b103480c0110104015000c003801d5003145480391001005248102c5a11301203000700d0a19002c0395540942e106112092542c03000e40d11030156600c0036014200b483e44660a591010ba40403400d035100005503407103081d540d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 778117553 1250 778116303 778116307
    0x70503010213031b0914071d010c0609150905030c01060906060c020910050a0801021b031207050d060810091109061309080c0f0c0a0806010e0106141204050304051c0206 74
    0x5035aa06040801d00c2004054006500b44001040d810b14400c01c5407070004112040701b9490601c2e030080059501400306500d1074a42010035a069904c103a166150035441900007c0084480c00d180300c17209044901300003000e0424010b4020010040090006030203181c00078041c064450312044d0079201c280c003132040042c90315604040035140030340120340c1240d0000c440c40c03206a11038010030500754242d084160141c1d00041c1d0b03081400000460a040302d072039030380518109205d02e40c8241e1101e1001e0941001c000c030210f91604000c0546d230000c80102500804c8a5001601e410440b0140100d5407064a84001076034a200302c40c00c0051240340f03e1040140a040002c00d42071441c0c0c001e202002c800d48650314280001e515800782004080d5444c0303070080c02081815100380c200001340040707810401558000a004200300c04204600e141500c01c1410000701924580601c02c4641c01080c40c8280c1e07000d17561051100b4807202000410650b00c2c255100229455003043c1070440c4100070800942110302 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 778118803 1250 778117553 778117559
    0x2120c0303040809120d0302030601120b0d0303050702030f0304120e0603042409020607080d06210b061c030c0303150b04090e07030534031a100f080708070503010213 73
    0x204100900113290014004469400258075082ca400580c900ba03501190780003052144a40c0c111925101d0403191080c140b002d110780c100401c0035201020001002c1c1902c1d0804584218028815030b680e0040c1d00e1b00c000c0e22440c10781440304150910001d10404103801011504003800d00d10202c905c5140c020740341100c01400c0720600e12048080d00d640801440d40c0f8900c2e000107a40b078900511005018407802600c0f0741180e920101261240d81c40701c0314240040e507103465041030614503c80c116412501141550b0303035080210b1144000315991010350000d071202c0314109500550319194050090b503040200794603083c1042d044d041c09020320000342c00180410003501b60301e0382000102c01c207403100f41c80000d5540e80d00d0a1130040392525079448000e809181024000305076a07004120070b200259410520324548880b00c401903441c20740168007000800003a8045407080e000c90060041a00801e1050b1743c8a01450304d4044a000c0d1060500540e03000041c580303014000d9610900c0020307824104030745 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 778120053 1250 778118803 778118813
    0x4060b0c0c19050301021206090703060317030a0207020904080316020c0f1c120801030510050717060d05030c1b1905120f06100504050702150a020f040b071202120c030304 75
    0x39078000d03650b07881e2041d04041482d071800c6c0003400d8400c1c000b080301c90950508800304080844000c007042e04240c83d02904001044905c29444020021455403507603a0712400803201c040d00c2460b40184d00001000107200402c01c9040003584500c0342403410901880594a08030f0301c415214170f20591040311442224406c1ca080f0110005c00d800703210754000c3c059000d035a0070881104190140e404140201c0042080c4001404180c0c4022480032040109103045400a802d01e41d25445203891001407c0009990343c480354080050b0980000c107c1340c980d01d00341c09031561001c03460002103a50002c4000c03281c0d5400c1442800c500840c81080c6034154900b0481405a2101a0480000f00c1c0c401c80c4007209580c1024030a00d80a01c1e841c13044084010f041a050106036440504a00c04541c4518151900c51030f980540c0e40d00304040e00805a030720340e90604404024015138000806028002031130300100040040404030400e4550265150075901441c2c7c07500d02e00034054071025940007040003900240c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 778121303 1250 778120053 778120069
    0xc0c060e04020d0e0601060f030603240e070308041d0609070302030717150a06050306240d1d070f030b040305300f01080307020a090f060b160204060b0c0c 68
    0xc030068001400c0c400403200c00c00641d4007140c41083d4980040c0b006018881c0c0c043c186501c045081d003401d10541e880d566440149002c510084c004c510388154a007844a0202d0300b0009891030030004036000305459050200144d1302c2407144a001c81140b0f0f00c04242641c5d041e960f1442541c00520300d8146581d458019800b940c0010034082c204645144900b01a0076840c1c48580134807891025442c09690303600c02e100a2081640000050000c28410005e0903030f2202d40c0201d400400d08100c12000101d80c2680c46c9074022240e1062049080514202298144414503140900c10704103e0340280d548000d2050b041308280406801403079028000360110740104002c20040426031410880500c0030440ea540b68003c00c101d650703444c900304c014040c81031640c80403240501108000b461400506030300040342e18005110382c24182e91101d01d98620b080c0e00b070780003100600025940c0c65075492802a070041c10424010124802c501d800070100b090342c070010a503400c8910810091481c8001d00c0d0805c6041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 778122553 1250 778121303 778121327
    0x303130f080406020f100513031103270a09050702030a11031b0105180613020904170a0207081612060e07082a060c030a08151e0f010c0c06 61
    0x10900019400001d81c400004100910321075001e0041c03103034071103512814201001c243e181550f0820052001004200411034400d65160610b01c40e01c88030120800c1c11b60084416051280b03a03101c2c0e00341d503000b15a124496500c20b00710741060141c1d4070b070494042180c00c144c03078290060b8000e00030500704a0042c80c41c07403c2e50801d03400320f0742408207000030700c10400842540810143d454405010811400307030781c0e500d0004412030180500d40f801030344055040715170000c003030310442801000c6800e00505e06070710707609040c5605107542d40340058500a503551119108040030b500c144080246458243d007007090503612440485001c404240e1108030141242e0070285036035004195000a580200300410744020f11010480350490b1060610303d00e0000e00041414094403082005040240d40481160801c003c40e08029005489501052440810550b0a039800c101e0300d40e4084005002180b0710117009800b01c407a0a00e01014000441e90710a40c1e002c0203208603400c000900805005440e55055 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 778123803 1250 778122553 778122563
    0x305120304060f0f1a0d03080c070602071e02100807020a15022b0c030b060316200a2109030b0c070209040602090406121115040b030702010b0111070503030313 70
    0x110030a0f40b0151011038124000300041140d40d941c900015141c2c011451a076000700319400114a0202d0b14050008a0004c1035001c04003070000c0c8140030003445d0760503240091703000001081d00340d140900e5810030b0002d008059200382c070b100c01a40b40c101e203e036440c42e202e419140d014125101340d6a8030310a042c1c0c2600c1c11010f4054003400f02030360040410700740611950f0300400c00d140907140407040404644108842100309410411040c4140d1200400c4030340082c6056860390100e0460b500448046c40f4042d900c0713400107404551f41114441c0040c0014895004d941c030400741482d86402031060303000011180006c6810000108081851202101ea00c00c61100383c5071714100269001900301001102c088951950100e04524182014030442000d0020000320040300e040343d0300ca0231a44104c03002d285104240c01e401c6c01007132140c0da20079a80107010260095849043c20180a07000e88903146041d8001840085100e1100c40d0008140f001c540c4085c1c041c5143d51101051410409800c10003503403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 778125053 1250 778123803 778123811
    0xf12050705102405010e090408070c0b0d050109060608040b07050c16080606040c0516170f030f06011e030b0402090a0315061e121a01090c18030512030406 68
    0x70034002d01422030030041e0020001440e014080c0c500e03201401d500c0121614282e440c0052101c1d0742c0101c40040c180c0001c44031210745580300c0c038100c1054030600c20700620401601c0000900710b40042c1c0134280416140005110b147c0e2a42100c004588540c85030070009000784000c24041811300c40240d0304082c0300d1504070b00d4412140105c61809608141d80e00c140c40c0c4040d001c00420f0b40901105401c08000c46040c4603a8520100051660103925104000040301140c602c0c00c000c0d80c0d0480d400d40c9800c0303130710f40b948604030400e00c80703080c0d00102e490f03813070f005900e1002510641c0305400d84001c3d11714000c81d11200e01b0002e6022001001c3c030b00d0780c55800950070080712882e0f507949140000194410f10781141d0181e103c1c5016002e64040340d10181410080401d0017809007203010041054071441107108401e900c090619400000c028000202c1d210003110010401007407070340028141083c0d640320300315020340d1004d481705805458070018100b40c1004500144104144006507001030240358081 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 778126303 1250 778125053 778125067
    0x330603061809070f08030306061c1e0519110324060409020703110601030f06020705150103060506040c1107031212020a020312060f090c03060109030602131a0301030f1205 75
    0x407440c1c44054801e40c8803035020007802c0025481228039800a4900b04010b10f04500700080840c13030038010400a6100b40355480d1140805002c0b40c0d00550020140d82c81d0b170303140400c58400300402054160340602e0760740a0b03a080300a40400f64010202003102c025800307403031541e40d10458142c0080c030b07000d40003c240030b2a1481d10240c1d500b0010704040c003026000169036401c1c61a000d40310b06904003031150300707801c074030010004a00c808507082819500302c1805070b0360380c4003450000e04008042000e82c401c101d01000100c01d0200c0c07640094411942070783d0802010001d001e09550f00c01a44401094660168000307000084a03010b0900c4010301c2814609000280c10301d00710240e810540e40f201c010b03400810303400812041c201c0b06a0b00840e00382e80e0480c0b0280c920001c608910002426104000d00010106009903c1a445800155080076085440b5008040d0882030100c040c441d0100d60443c4200c20700c0d082240707400b1641200e0380150003010b110516600c15002c0c40c1840030311401e1040c18030001c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 778127553 1250 778126303 778126339
    0x4060509010e0609090d170c04090e0a141209040c020c060a121508030703030c05160c0e0105010504050303030411060904050f04150c120f0b150333060306 68
    0x903034040c05800701ea5107000e2401c00180900b00d400204600800e900c9140b2040c01c02d0b4100c2c00b401d100c01403040511205648020ba410050b2043d030b40010001440d240511030940004220300b08028454000060440a82c1c007600c0d039920f80f0401d01181400c4100106c120340e01d41a803000c503042c1b81ca401a180c1003494440020f075581c101707010283c0441c01d1401c410181c0c01d03031486100b003411101ca0301001060f0801d4800c83e80d0f030065400c0101410b54403071a000d51103000e242640d0309001c280b014000001c0c46864020701001c698407554060140c00030010403598000d50554050361400340045003580e555407142c0c141085181c0043d90420700403c0450700c207403241c3c001c0500c201d21416111a90381468501442c41c665007102a180d40c91600c3c0c2e101c4005a441604450480030328100810310840801c0280014203440d682c195000b092005030540410300c04000d0b501c100d0240d00c8468926a181002c1c00c0300c82c1e000b0508070100ca42c40c6091640c180342071009190001400741082100707180300100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 778128803 1250 778127553 778127569
    0xc0f0a080403050105130305070308040507030b07050a1e05092202030f090613330509012c030a03020f090a0311030c0604030c0512100c030507030c0507030c11040605 73
    0xa0360040d200240a01c2800307000d005080c1c0044901000d140d8600e4183c8000301203009600c001400c0059002c0070030309010701040541c001d940c01489001c050708140c0c6024050340e00038013000011030b00031104200000806405415240000d0b194580703800f91000401000c1010142100e2100c010303002c01168003541440a50b100c0c00c17100124104500300500e844e0f213052402401044c0000c10501040c0005100000320b20b00d940a4a41c0741000103904a0802906501114014100d928000c100014088150009684a10f500d01d1190003094402c200c03401c00c40c2d1640e8464850350080000c90944c5100e5801401300e020281388503818140c4500c0040d145440750350090b42c03c1c0c01480e4008401303190030302440707007043c00498049141c2851036840459110452040500c01d0790a01c0030f1250700b40d400c3c00044120328000b442006502000100030b4000c14056074647d00107403410b8101c2a0351070250701168061038041c2c85e141701300314665403a210200103d03031b8459005510345034006942d40350140c1c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 778130053 1250 778128803 778128823
    0xa0b2d041127070234090c021018030806061e091c050c0f0121020313120f121e050604020c012f0301120b091e0d030609020a0f050c0f 59
    0x10141c058003c8010316914192000d155902c14001440c01407243d03607171000c0001080f60b491100c0400c4105603610182d01b480c0786120f020602600302250350300002070309030300504e455200f520f903852540c032030609016007405559040e41c0001d0406003103500b4035802c04068950f40d40020601c10482103014413003221500e22000490345c1e07620803000070103a444c000c07140c140d0700a82841c0482c48201c1100b00c080502c0d400c0008100002d5000000c600842c4100e030f01c104840d600121a54110800d04000501020300241e007800091203100540c010f410450051842e03915040108035140d0700544404001041c0241801d54456070030492460914000c0c001c041021480411501c054504809140d100d400c03151841c50040104100510040140b000303101001c94201e140107106550700070b10f140c606010040d50800d080c1d41d45201480405001400184802c840d650038030145e40d0342c013400b606034080d0090710804241e01c0300110000c80e111300c000d400038240c504202c54502d01d00421450a042d0074103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 778131303 1250 778130053 778130057
    0xb1e1f050a02010e031602010c1511030f06010201090812100f0b0d1a06030c0f0d15140405060f01050c0124032609120a0b2d04112707 59
    0x1203144001e054081c803410000d05074290240d4502129000203001c0c81e0301c54200203040c042102c83c0303c01400328464402c1c1002c0b10400c070811000c035264400b45000e4100b103c5130542003030320f42c0001d111548117019450b00e899000300400e05010440607a801c21403c002c1144540c125800c01c002410080003100200400c5c2240c0e800e036441e217030008a0400c1c3c40440b81c0196000c807903c0400c0026464103422a41d210405084103501c0300018011050f00344241510245da02e810a030950070030030008210380e01204d5460800200d80d5114106010558100303d41c5a680001142030540300e55001d20014510400000300000c1d03400000e0286211000c0b501d408100440a490010f0041000845492041d0002e00001e00c0700d0441c0360010060718490030030003900800c0d4030000c0300300d018010404c18046c1940182100c01a1403e50401032840308c01c1032100c3c088180e0100b034a2000581c0194060065800840d4149501a54030034014660000e400c00c1e25010050500300b040c0060201446010f11055 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 778132553 1250 778131303 778131307
    0x30a150b0312070c090c1e020313120b0103020f060c010f0903110f070b18041407031d10050c0c07080f1b010c02010f0e03010f140106030b1e1f05 64
    0x2040c1810718101c4042d441003040b40040140e40b02240221460f402102c03109100030803812000e40d02105d00c5110001007041c0d007000003540d40c0000c0d0700030000d40004040c880d6940c0300f1035901e98a60459a0300c1034409003221302000d00600260030480030007188642c002e0301d0b01d80b510020403641030841d00c10460101085580d06ea44800b0142c2c0841c0c10101813607050020315191807081401a00e0300313110b2007020500080080c42c5610000c191040d000c00000c010010891040710801d90090302c031080720803a0003e4544080481c2c002c0000c440d4104520840b0018140c0c0302552138540020030015009000700034090000c05403682d07003080030802400305040502400810003420900d001c000b2002c0c8000100d84a410400a0f47e025841e10802e03602481c11b5440c0e4010300c01d0a0702ca1001d0501c05a40550a1040004034100b0380c1e040301e5030218402401600f41e07030361171008800b1584010380c1e00740d022600d08882d01c0c02c40b03903d030f80d0b600240c0030040607102c01018011080e038034101040740000201d100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 778133803 1250 778132553 778132571
    0x6060d0b0102161212020303091504020d0b070201051006020f07050d02130203070504030605100e07050307031415120606030c0904050f10140609010614071103100b091023030a15 78
    0x100441c645d03418200340015420750600d0303c01c2c9502c44021140d144c6814003c000020295a0b8051805401070781000041c091801c0601000b8082e0400300c55004c1519154200090914800107482c060b180c5e0b04000340c030100342017104000b4079901e503443c141d0b03201c10f10504404040c1880d2000b1400f0308003075101c407592030b85945091705c10f5580040c510418281180010022902642420b170791101440c50010354a54603e4400d4000706a42c4070300d00b260981d8881044014180c0c5103d90394141800c0ba40b02d8400301180800603600c03c4100d130f8182c0c2541003180c40f88203505142c805243c005200b8400cbc0c412461302c66004600e01500b43c0307461100c02e5100c8444006032509020129004481030300c4a00481d8181480070700782c4110a070041140450002c0d48805100c007965100b901818000d003515a288421480003020b4440001c0043c4122070140216a9114240b401d04044654071048006883e00700301e483c0e0b141540c2d922495425014418a510000c1c04050220316851601072000030000b607 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 778135053 1250 778133803 778133813
    0x60114060d020a05071b080c0d051c03050106111c0f09030503030702011406101d06040f03050f07080615060d020f28090b07140106080703210806060d0b01021612 71
    0x101903505a1003114106d0207004a5101007001c4c042800181c035020108403080c5415850042c40d402c40803d82a1404c40302c1044a80c96007016048030129500d1980300d051610300d00d034503a00d0708020360440b20000358403550345034010440200c51184605064011315541c0c1c441c5810350740704555000050355505a40034000754061223140d040710050700d8648440741d85c3c41d8040c0c003d1210480824030a0109500a8406d940d85011100a48043c108a22485640f03150140e51448000b0406450380512000850004400540e8510031b0400d0708038210414000010b00025600140a80e44e001d03400300002d20400f007002004244003a02c04d1070039542c58185840d850859a5009080d1080249082080040d0001c0d50151484141c0111400341c054681110341401081c02c0e0b48007c0d054000c030640042805203481d1008130107142025101c54902d40c00c14211045201120502e40c0b219080c04103040c0d28110ba07009607040c1030f041c01100c040b00d0420303291542c140c0c007e5206940c5012a080100e01b001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 778136303 1250 778135053 778135073
    0x709020a030515010f0e0f1002010203010305010f02093312070e041a1903140609010b01030b090f0912040803040f09020a05070213020412030302071a010602060114060d020a0507 78
    0x2410422243d46140450f00000301480e9586000200300b002060443c142552147d4502d0203200c2d0007040c00f030140070340c401c1c00380c040e41092005458a5103010b0309440c404050707000311150140700038104805074000c1420001d07981c501110450940c003070318032521030351801240101583c40c54076400760481d180810f0020880e041c00d1040902070340c1070030141101c055034207014281c0404c0c1201c0d1045142d900e1001c0d032108685031350000d014000f00020100054602160060007071000e07030024000c0301d00c10401581030701c0031505401c0d0800744400020b60b500c0749485815810140c0d05060781e915160711604d000d940e030400e0b0060300444d08009020020864052400c00080040400950500415200181080c01a1107020b0300403030710314103e050341105a82c101c2d80505224003a0000092403400c4c02402074200520445007134111140c00b008580f0710b084480e0407100c0d01e900411182c7c0c01c140d103a044203015034403e49d803c810f0030301c0700d1084541c1070300142018410950754180c4a000341d080c030070020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 778137553 1250 778136303 778136311
    0xb09090f0714030f1603200d0905030316090902040e01060e0111010c05030a0e0c09060d08070501060906090b1f0e12060a050f1315020a1416150b2805030709020a0305 73
    0x4c181f41041c8800514505180e200442e03240740302d9039845035101e54031480078169840c4014001e01000007003180c80d1030701120303032211020b0965642c0005501e400101040f0322890168030b603984c40000041040303078841d00031941c40712018900801003d54480009080d200e054540c000401d102200f0405091001d02c80c030f04920400c04014030080ca00740000c52002c000103000b2500651407051141d051220386021154181da01800810005d5030b40c0c03000100130181401050403450078020765080a10741140c2d084442d00412a888407100c1c41c5600a0381d60503046801980c02c10021415103491103401c3c80040d200c1c0c0044c01c0080794520b001c88480c4c082c1c2400501c0c0d07040404030419904c001c0f6450403540385c0c0e2500d400000580e101e406e514140c1d4440440390a0303000c1344200041000d02480c802e28481321292044402070301040c580c2059500b9942085070b0a034008512054494907048079000d1320520100580c1502005504c5101080c100103d6401046071940c0010b16455001e074917114007130344 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 778138803 1250 778137553 778137557
    0x1009080a0c180b0a03080f0c030309010501050a0e01030201020d0804020301111b10051b0304110603190b04060506120c1b0d1407020603011707050a08070603060b09090f0714030f16 79
    0x3185059a00284c240303012404003078441c1d50b001c03c00e80a440d440c03c0c212507401000d40b003101d84138a051060f0901900090285038041c0038044c1000440340314007081d0030b05070381d4160050050308145190031511103600400582c0e043d901c42c21440c18154104008082800c41d0b001e410321942103104200d071030301c01c8007007040e92094980001c02c103448886213080c4500580f104045e503503a07115070510803064400310342e44a40c0818000f0070300a5841c0160901d51514407090000d01402c40c1040c01c010480f80795104590b0890400c12400e4400c402444034242e001005092035030400031041416804080100001d5189902024103c0b458a401c4480b0000106480080ca40b0744a05030740230484600061003041c904004003810100f44180034004940034003405130804540950b07504209a45400902c60140881e1900030041000300c122130489602c04c2c1e0141443c5460380f2000410403418000a0800b01001031610300301420b141d050b0000e50060300d090481e07a4540c2000940d8098982ca09040501 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 778140053 1250 778138803 778138811
    0x213030c0b0703020c01110721051c020706120e01110309120a0e0405040221030a09050102030313031b0b040c0905090109030e040e1f062904051009080a0c18 69
    0xb9a0004103131800309000c0c42e020020b8500090080e140007401c1d00300710700000080c0c010f085d406900100e0340c0049c41c0180b00326403a01103101c0194080300800c500c0c0c1801038206140a003c950b00900d991144a000400f0004200c3c05d02c4100c00e0071121640480036041d00e0000074080c0403c410001d42c100f250701c0500c40c42c03820078401130140503100b018400031300458031a80000c09641d1102c2c142070001d00c03107044401003085c100e60507641303076401110f245c07001c2904480085550352000094900c01c000070400f03290000c0702902d042c3c40e044040240c49200f00c101203105800206d40d1907060b03020340e100b101001d0032503007080c07421419104020212901a858002e01d280400e50240101100031020743d0001203111440800d10f0805000401c0c09042e0f502c2c1611155031241a40d0000c422950700340b00d100c801d1555041d40502c010184e00c2407019840c401d2200b8415840e107a490035001c51000d00304410740c0c50f502c8080b0707414482c4da01002d0301c000d850180e003001818144403050b04240b01c1090104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 778141303 1250 778140053 778140067
    0x6020715020303070e0a1706060a06030c12020d0e070f0e01050d1a04080f13030c06080c03010b03190608010902010207090e1f0b030f160504020a0807030c0903060213030c0b 76
    0x399203010040c602c00c1000b48009a40c5c40c145c0300e2582071006007400000004040070404803040d078481d02075980d03601800300e103078001030205c0c840e108010110b9001d0382d840d0358004c6045c221601a420184c1e95400311075490070065046607081102c4401800d10414002d0740c140740034100342c03013a201640864002e10300c0c0000c85001481c2e0f000e136071403440507141700242c0b20748450500c1151030080700840040c807500001e001e42803481e4511a03004803071140001208013921210304903004c0c1001e8400310204541800184103c1500102940d404250003501c01d01d4111200c2056094804642c170491441e55034030b0b044d40c15960b0501580d03024004204003071080000012485a444021491b800a60b103240032050032020059000041000e000408a0704407001d2009280d4032011b05000101e0551103070000014907051900030749803a8545074032024125584c03000240e000c0c001240c400b20400800f10740120014605102820702607450321561301c1c4840c1945024401c50300550844d4407899014403901d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 778142553 1250 778141303 778141307
    0x6042d14060703030e0a08040609030b01080f0a0f14060414160812090f120d080919020f1314071b0b0c0f040308030c03060f060c0721061506020715 65
    0x50380b0540d03040c500099455041a0024100020110010407200e4006030014045030301580d500c00b9203005150390b0502d030740d03507140196440d0b000315184185500400c04000c00715070080740b4a2b10a9004502580b010314565403420b040010445081300c3c084001c050000d124081006090b02c050700103980002c0c568140302d0000d0351440c240040368501500012480b10035241c10f441925440800780c0f82c0c2c0142044103e0981c1c036843c0754070302c2d440000e40c0c0038001020201d001600e510321002c03000b80c100d0b20111070340074002c88845c1458041d410040c40303240c800c4016098032410701e0180c3c0440c112101070828000082902c180c03000340fa0b030032442c04102d10b00480d4100c40c0b800c0d0081c0c0080c0c0d80c0c0e5031311040b004410016000f940e001501d0100d020040081d03480e40c01c801144607000480350707000400e9201007001864001d8000c012019800041d05104041c01c048004003400150703490316191841541d0f82e441900c1300da07040c1c1860301c582048104496a01044014060703c0901c2601c824403c4034500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 778143803 1250 778142553 778142557
    0xf010602011e020d02090d150507051e0307050f070b18070e22170a02060a060b0306040504140703030309110a150c0309030b09010b09060303031009020906042d1406 72
    0x20b070070010760006240c210700a043d030450351006005840c40391041d01c64100015100c0402c045242501c2c201400110704612030022103d208520942003500c400f4405440c01540e00000c0c5400203110b003c100007030313100d100d5001404003148964070074a440c0c03070170b103203610f2081400080a04150b40103403401d101c0c2c00340d031945c101e504c032103910301110314580d00d010b185469003e000c1000e4105103e007584880203a002100601e00b00100740c08640003522112a6002200c100e44152503100d0000d001040b094a0103420454209014060003407405100c61410342c1071070070717a500890202b5600d284080401004000011700440122000c542c40c07890268123100788a90091040308010750500c810007014040d042c0318001c0d50b08218125440d02d0325030380c86402400300d410890320540c001c500052640c0b074008200c0f4410103513810702001c001e16050807100650080030b015544182c0c1031001140781ca180c1c440300e181041d001060a00d0f4240700280820361070140c1e40204c1c502d008416614995501c403241 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 778145053 1250 778143803 778143851
    0xb0f01021f0615020303010602012d09110604090209040f0c02060714040306050f07030e0c012309030d08040308090604020f090402010c0b070e10092d08030705060f01060201 76
    0x3440101e25090414440002d18064011001c003603a90500503855950000165040e50030b103400030170070a40e05044200c1d002400c1003451a140c41408904e00e10590503802c0140d04074400c0030700c0021440300000040c61030f0865007206400c2d80d400300d0030301a0392409001c2d000d0f10815030f94041001040a500c000d440300001840e40c414000c0424502d204520000101d900460308140d04000e40d013050900c0300d03c004426102c00c03000a007040d07000803d1034004108004020320584411040c88000b107820707c2c07412040c6c061109a43d4061010800546041c040084075134903c1ea2404214a41450b010300440300240804000c2d138040030070400140c036410a150915032085030740034030654903413004a40b1110458001014079581400f8000c0c919040241d901d4280812910300c1c0c5c042d2a4510300315039101c0036215040d00000c03a80c0000c1c00300702c40400c0480100020300d0440408a4850b00114590b0f400900102c9455001d001006450485410658007610341880244010f02c4075619400c86086020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 778146303 1250 778145053 778145083
    0xb06040f0e0402060d110904050105011107031511041418130b040f080c0f0d0c110405070512090607120c0e0906010e0d03050702130b0109141c1103010b0f0102 70
    0x1c4049003d550754001604c4100302840d409012580c40365900640b59009280c03228002e86c140740000c207a40d80155040e0350601070f014024031260303181d900c03003410455014141d018010303511800210101c51610080010b44140d0b46260076a1400c803003400003540802c03824000c865128424061101405601341900d10b400c140942915152410003040d044002e400040000e04009008141e02c1e501242d8902c001d4130442c1036030910b000c40c1c0320984030115610001850380d08540ea200c1e940d031905900507034000c2c3c05894207030b007050380c41e0164940b010710640d030000e415409901000b80c40c80d4480c0e074070002c4050f500810f1003610380401c0042d0412152410545c40391790301e0000554564407800f0300e01c03d82c144c001d1004206607500e040146c03965014840a9015002a40084940200500071408841e60683d51200c1e40c3d442c041c00e14801c09441c5c8011584210303070307002c040501802d100706a6200d9000e43c50b02e5410720079180030035003110005014240640d0100c20351076043c0c0e8010454140042c074030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 778147553 1250 778146303 778146329
    0xc11040c140c011104150206090616031505040228050703050a21051302040b030601060207060c0f0b010906141e04020c01020c01060b070506240126011403010b06040f 73
    0x3107402c2c9015002520045203900c1d4041000504000d0310b214924900102c0e40a542003a1248070f05541c80d4030080343c071407444595070b91024400a101ea8001000c598140c44000c07141511600001d042e6402000c040c030620340500c450a00181442d0307034114140c00d00f03040071880c11405640144c020b000303000c8010309002013140391a01104030070091000030380030100d0812461030a1a001d021039941c40701c003071b40034070b1404c2c582c00c00310f080c0003400070705860b1150000d01d462403030108111400f04154004458603180b0903910f800088070f032001940a4100198081061401c02c041d201403021803112041c8074601010a820114209044c2d03241c01c5071090710050780d141c160a4450780a803103007890300141d940c606000020180d14400c05041c4103846031040e41d070661182c2d44007501d042c200d44448040e084080d41050a0340d07020300030850901c1310f803502280c1907004915080d001e0700f900341c0c0040501c15210a611f00039103803e00c122040c10800b202c900382801d040070140800c0440324016100d80f0014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 778148803 1250 778147553 778147567
    0x5091e010504050f031f020a1d220f060609140904021507050f062403031c0e010b0d30090603180b0f0906010812041401020705090a0603022e0f09080d0c11040c14 71
    0x3030f41c02141c8100be90020a0040e60341e10b04004095050030b00c280c1e211200001000c83c510300c2c03c40030190180303400400c9294a4000c40240202c0c9611180301102e9030b00c1042d10a5031840c0c03051010900c26007003c0e50600c50100c02900c2032400d1124180410b104e50802c03c60103610650810001e1000a02d0180c0064000c1941006600521410050302e9010440d1050303442001280013850000c6540240700000303101031580400a40c01880c182c22022910803030007030041621a0740019850000b0080c04501c3c403229031640e000c5088103841040500300207404000c40d000c01004511300518800c00240140c441c03400a2900b54003443c0204e4010240308a44800140e10070440c11014000050859003181030107400300000b02894401240202c03100c42054544a09100c0412243c1440e5186074a40b0b802c1d02c10201c5104012004010070710502e42c0000c15000c6040061650303400748c2d0b4480b0001e00400c0d0410003c41114580c8492140c0d051010421006d68000410300021400784011601c40003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 778150053 1250 778148803 778148869
    0x4120f02070914180c0108130f0606060203070b06010f0c080d090b0f19050105060703030b030f032b0c0203040314030d02030705091e010504050f031f020a1d 69
    0x10003640541e0070241010ba5070140c50820320942c034001d0300d000c0010001d00881d81001c64841700e002c049180071650600000b200020850342c1000030a12480018118590b140da0b480129051500f044005a10104140d82084165803245400c99003d0a0001003841075080080c45094211401020b10301c3c0441c1c2e80c10340880030b07000400030a0340008a41c040b49010200c03d40f881a00311102e4045070184900c5ea04c0d0303c038651065234143c40014001d241380000d6510b058010700445074805d60144504802c40007844030038405440c40c0c1404500210701d0622545205160304c03074190350302c0545490b00c500ca1074855000412502181d41c0b05000714004001c4042960450141c010316544080c00041046001a4080010044005d0486001c0e040c90f000254072003255100610301801b2600c01c0105119601c0e000620142d0548000c0031500700c40100030086030f080109110401600e0303008a1300000194108110803403442118040500141020300090608130304034045205903015101115a540 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 778151303 1250 778150053 778150063
    0x607031a030703060b0a0e0906070c110901030b0a060e09030301300804051002032b02040513020304020f1e01080417070c060306081b090705041206020309100504120f02 74
    0xc40d005041c2d070070a60307880c1040302c0a028210f04041c811400e03000702141880402440314001c04403030001b0180360303403941e4066a0085610101761440d4207072078020340b00c556030300c11840e0107540700701d48407449030818010020507100c03103030030000c0b800080c502088401440001941e045074020b1301c2118500d22501d0281030300c4070b68000c42d83d00303c40091805009111004d1b00030000c07541c0035a0380001c0441c4011040b40c5034040c0aa501010348018646400628105000e0a130002a00c402c010320f0144da0702d0001d0030040000104100003600801040103518241401140d00c1d070041d41c07036804030007049000030026400f001d941414412800003040600482007480d8480350100d0102070f075246e6840c00c2c40003404080b03100303440010303003008004100d1240101d00c1c444c01940084c2c52400c254a01c03001c100401d24014810310412000b4031001900a0000e02c0d400d01050140c0750061783d03400c11403106400e21081550f503c45007400c0c88284800244642d03081070700c0d80c55601d001004d105481c07008034288 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 778152553 1250 778151303 778151351
    0xf231503040602070201020c04022b0e010c020106050a050d02090f2502060a06060e010c0b0414060408040905100f180b040f0f060807061e14070f0b1305060703 70
    0x28080200320030000150700034140503000b60211030228020604105c03d80c0f2800c006107854080044900840130300b541061500483e9500000c20703021280a03100c0c0c21030303200da603107100140c2d12610100200d00b0480c00c24000f0b0081035601105015081d0007080302da220141210a45c4000c1c2c01c00120300e89a0081204642c5c070300340544200b800c4501000039525441594040542072900000046682c02100e01c800c49c1607042e1070781c00c180c2c01c6945424103204401082501d00b448250300000221100384000f61042d841006419122400c26990604a5000610345030b00308010480601c541a500107010089a0f0307c00c002c24601040760101c000500b41c60303007420783c03c40e00b00410401c0311813268114211342061604100849550ba408040c0d13200203074419007000c10b50107060104000c00c0c0440140d90b554080c100500c0c00e51040100030490352201300d01390781803000d0f56803040800a8031281d0640107000440964a03095554994603101d4401500e4501403569400762050f64071401c032a10421 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 778153803 1250 778152553 778152589
    0x4080910050403110d050c15090d030f110c010e0621040809041a060f090102070312020a030f0f170a0612080405100f08011202010903020919060f23 65
    0x8900e0420380a05280c000d80000c41c0c2c07021250f00b03548214201016207050450708000200700016840050080820f6003600c0480b0544d0300b0441c104540c0c4603404014441440790b6246550600340c0e036001001986078005c903601640184a810040742ea0118002c04802d104032146940c40c203140d1041d82c40c505051040c8003401344000100414032402d800546215202900c0c1401038550480041032024500c50341140c0c40070f814407003150300c0301c0381070040c0c400442d040c0101c0b010261281c60ba0075401003038a03103010060344000030600403d580031940417580085801c22140c44c200c64480a090066201001c0300b02044c0c000000f1450341541d0000c20050ad911384408880072400c0c205450a903100f40a21030055259005c0c0401940c421914900d1807000350341c654446900303086401c070103044190300981c10845c03e1400840035a03192490a40540c2c01c007075080780410326000450301600c099078000c7c550707000122020000d03807444202e208410b0030109070b484200f0340c5401c00280200003150603048 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 778155053 1250 778153803 778153819
    0xe03032d0714010c030b010315030605040807050708010207060b0a0b070f170a091502150c070606030b07050702090c031006121d1014060f04020903010e011815020304120503040809 79
    0x4002c044d03100d5541c1ca102980e05001903800c0c84019810348805035180f4851582e5680300300007052140e441150003d1080c11203510707000c45c648400340783c11203542059106950000d004000c0240501c500c00240005695588140e03140412001e02d50007100d40207080700402070258010040c000855561074004030982645600c151500200023013114000d40d0740e080703442d50300b0740c00403800001d464450304010000c020103980d078070140c100c082d0007003802251060345030346d0048001158840a03e2041c07000f42d441c2900d401682c010024038000241070707032010b40000c1040c401a40e21204241c81507c4250420302cde412551a42c02c1c0004214084034154041c03a08180c10401d01e00109016070303c5034200c0803c5c48425a091200a041c0c8000d61300e0aa10941301d4200c0310700c0f07003410b4000d0f1a5a0000400000c1d030011307100e01c41420b603211409400d001700590843c00c410015074001d80395103400da58000314110f103025035403070b03040d04001030310305c0c0500a01000150030494910704507003003c0d0b0003030701d00c103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 778156303 1250 778155053 778155083
    0x40b0a090911040504060e060904020607061116060f050402060d020a090e090a12020c06120a0b0d080a0f05120f04020d050115051c0302060a15091503030e03032d07 72
    0x100b180c00c80d00a291099040580c0080c400303a00c0c100c22030041c1d400a001c8540c139212982007080d183e006c042c0848000e0713140c201e603210010064000d010880d0001e00c924040c00c030107141a03403ca074100e00811f002d09240c4014400035071140025502d1141850381c0060360350958900070ba8402403980c0c08801e02c65501000c000c42810301003540c803a0309100300402020540041c0d0182d0302d580e0010400358006500b0304c91298030810350b2000c2600404504800111b221050010440d1041081801d840030741c8001000f00c100da078003018525000007207192850401c68000800d8648171006005044841d400002182c1503544504031020403a40c0540204075100101c81c18007104a080e00c42d49100302c0090000d01200840c480003000d4056250780500040d50b10031507604001c24070404800f0b00024440c101003901c1c1010b20500da5449a05850540780c4c40c60351400030420f0325000d808901036001440101c1524406140041c80d05440a0111240701016421100c0754010044d0180400217030700404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 778157553 1250 778156303 778156331
    0x1d2101050a0b0a0f061215080f0106050a1d0f180d0801081b0105071b120c08010c030e060a021608030f070e011404060503180d17100506040b0a0909 65
    0xd00c0322460540d040c2102c00d42c0c4c0d24070032540404a1160b60080384041c1d103100c0c881c0419500a06d00c1800e049017200300161244805450082e5040d074016290307659040034070140c58031006d008001c2841160100580080c501a500c002001528116038407103d4004614481c2515102d60117400041c030403213510440c40e44d030041103040c0030721034000180600403262400d004200206014a0b5041e11040d14000d0281d07a6800f0500c6034400001000300d2a040100301f02086003401346205014000e210715040c00d1440301821a2030702256042030500d0010300c54844040824400d40c4003000210050300c2d565010050080502e00b038030010244c200c0001000310306911003244a02504050761103c40041002c1d0040d03d0350580d0720441030080b0018842000302a1107080250740c0403c802ea00e41e40301d074400c910301c81c0c90200049080c0001c0749034204411006004414910713400549604188400da00d4080402c2140c0b180340128010300200144426402d40aa4403490007440740c01c80403c4081d01040b50 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 778158803 1250 778157553 778157561
    0x41d12032a09120f030a02030403140a050a02100c0c0b040321021e1207030201051b090f0f0402090a032402130b030601140a02060106030b011d2101050a 67
    0x41c241d0a80c40014070040c0541080351200d072110040541c182c81d00c40020204035509282c0d0008003a244100002007140c044144040c191824440c0c000b152a1405e40c984124151745103030b03844505620014501000c10f82c001600110b00b90181c522200b0103920b588106e5248489a501a1513024503000014a1a29003001002182c1c05260511100e85540c08255403e40070748584e140140e100400d0107400ca003074010500150f221890880d000a8030926035805640c01c01c140035800350f55100300b00401c40812130b81c0300041360f8140114030f00c2d059202c03001034010070719407440707a000d91000d82c84508c02e40c03601d60480750b50600040100c811a5230324030300b070460200c071910307281d0400b6202000e401e4000d440b40241c81350740c29000461400142400c4030f0100c0c1ea04010300306410492020700418403a140031004284900e029030103061250304003c009025550584e80003410003030071207410340384080e901441807800c56040f1118114005414800f03035802c0c03c0013881c0c200d60352800062048044003940 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 778160053 1250 778158803 778158811
    0x10030219080f151303090323010504050f060705130e060f031009030e0612040210140703080912120a090602040819060b060702030604060c0512090a0b0108070b09041d1203 75
    0xc020b1960f90444050401c2503011401004500c5104013840001c444011012341146030004410b903400c3ca0005035800e603681507405451542090b03d241e21a8001030150652025490619070f00d002d6510140000c00d0a5a10501d42170141c5900402c0c4240d895044060622000404885464807403580d1000205010507085000c15020344c90341803c0d0078032406440100d1590340540210303070340ea82c01b8020403903003694422082160107a54600c82205a502900180b030007070751503803510300d032900000f454405003100354a00d800c030501101c92510601d08201d0b13400041e4484c08903030510b0074903182003c1e0040b500042c20740d000340000b40c418802d81494190219028070301c140401007000085c462103104441c006901a041500098003240c2923801c0f96142c8001440c1041c0b0b45015003030382110090080d00c010101d0f40041a00300b083c090301c81c9850303014084c02c101804604d854270044044034414100d440340910b40310f01c898007240111030f940d602d06c1010a410b85600c1400c00504e62480c0c0c1c0112 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 778161303 1250 778160053 778160083
    0xb010212030916141e041d0a0311010515100c12030b0109120b0705070c18020703080a0b010f0c0203160f05011407050304180e070905060f0910030219080f 68
    0xc0001070035021912243c0140780c001d0100000812111180f5405d0504030360340e150040e0b101c5070014200d030340108214618903440c5010b0002c03503d5030720780104061203584030021180e050105010100349044030006c3d14201c112001c101d140204e082c25151842c0005c07002d001d0b0002c00c0d142740032444c1c15420006030103600342c0c3d41c00c1c036194840c92000710700100c030100604081869400941503901800040400c02e0141965509044c3e807030004a0031075a0300451801495008550441056080340c0f1083d0404540007080c07040e146460002800706680c0c1c1400c904000d400c101520964800b4011b100c0f52012075611003151310344035901480507126502c9400e0000d000003400c10740c914101c0e4142d480c4181d00c040910b14007803400008810440140761035101095481410404014040207040002d0410f040003007110315000382000020710b80b10280074019803080d020401100c8107100403109603581100d001c3d4900314003404c600305403c0c150704640350f6403082540c0a00020b2000a49094000e446 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 778162553 1250 778161303 778161343
    0x904090515060f0d050d141903090303272d0c0e0903041401030b0a0e0a0c081005090a1508160305070b18040b060f040b0705010e060108100b0102120309 67
    0x72414002e0303a0f404c1c400e0203000340e00494009904c0c58424450f031312062603c10650303420202001d140700c42c1c0e81c0140c0c5a190110342d4902d8000b04040e010b00481181d1034a00b0380c444009c041845503d461400400b1000f486034500c0c181c040f111001c04205040c0441c4100c0c609401103c103441c1c0400d1294990040d00e07007941c2c1150000c0c884520010440341611204003040e014591120010741c06041c20007241540280d003044040b401c1824840c0282c42242c0c40c00012540b000d00c00005000040301400107143d8040308401400b0b00d07282c43c041c181e0801c20018000410102085d204200c2031402e8200742c2c070318051011500e00d81803010361b06400b600d0041307013500c000301e035100980c0c0d18030321413580b2240108003c40150b40303d034030b002e9010011030b80001d03007550315100e10303540094010b900503000600ca45c000441c080090250034420410800e60010040074a54100000c1c00d94620010a1110b0240e0b200c02d00e6903c140d01c2400090a0002c00e90311058590420f484d0300741e16010005800507202c03540c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 778163803 1250 778162553 778162579
    0xa0501120f0b2707030b180d030c0e0d06150603111225360513060b03071112160f0807080a0e010e0306060108190e06070e100309080f090409051506 65
    0x82c107e0140c0d040342c060401413140d2040b014043e80980f0400516034180041c0c40d1040100340c454801c40040c440c4583c3d40052403c2c4845000d407040c06468000784105480c00128880c4403440400311100040e403503000205658950300e481e4450b1400c2904c00810005401000c0c0072503400190702c00b48002100c0011020b4843c5018000700194118109812080f04020030440341c00c003000d803030000d05946c41000c40c1154842c900340310580d1081e2181e40010b41e000b034444210000c00e1000d80c0c149080300d040c0314503000540381400414100108054a000d413540501c0b42048440c4084806156200c902d0580f143c084c080041c0c0300035810304071703640403810301103104040e46030200e034070b42c418541619010b2540c0c6420382e0343d0007400e035403881d40010b05607158154910001e0802074144a0543c6a42e0350260003013890a0103030940025420b0414141052080070001d02070b02c0a0310209480d0b10310042d160b035034180020b8003a0481440141c014002e211f40618a048501905486510150b4040c008079007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 778165053 1250 778163803 778163821
    0x110c07061e0e0d0b0601032a090f030b01090b01171611060402090705090a0302030708030a230f090a090c03062105033f0a0501120f0b2707030b 63
    0xc640d410041d80030a41e480c1d0f0a0010b003062048a0301704c5018900018055410700c15000741004107540308640c140c025071240d154070760009880c0080c2034010440201c3c51f01c0c650301e102c5038010600a040000e5259111014680d2003106404801220b421000b00241000342e28003d4403034410318120002200001d001c480e0000001d8060301840d07000e813000b0300503a58003201306e4854001020565004003a0100000940c0e010080c0801a100320006155190a44e40d0090007222500e2480d40c44c10300158003003480444400306540f6400101408180e0340c054481c001884a88540c0080c10a50719004040801c0c40c1c0c9a80020300352003044d084602c050480c030380c6c038007404540c0d024000c25543c41000454031408030601803503440d400104201500c9030f110460000490702d2011f0b91890300700c0140c104081c1c0ba455004480c01008000c88034041040c0e00c0c1c540302764940011a024103440710321804100020704002c18564280c0d401c14042c050152098402c0351100b01501c01581c401e003101000c40c1e4110 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 778166303 1250 778165053 778165067
    0x8092d040e031804060504141503010b031e01020403061811040e0309010309060b03030a050a02070e06060703180b0307030605030f010605181b030f0405010c14030a110c07061e 77
    0x562408001d50900a01c0e0480e54600c25007990101d0300a520b581c0d000a41e904d95000f048c6030b54581c0c0c42089804d00d4102213918400070f804074620301c0b0f681003143ca203016440c042080c0d51805141c001d8020040d40c1010101d029100300d600040040b440c1102d202c600c2d040c651150032076903106070030007a02085104104000c0c1c407c84e0391122899081005250120b6019030311141d9101e11a000100b456004280000d045030405c440803408104005840e441035a818801d2001603d17403003102071000d05140003c190103008412000b02401444044911801d0003001e5100091084941da036540340340c1020020090882c1d072141500130b20a0407203540c000303c010b0050a050380c0004d8401030b21042d02c031482c03003042d00014103c5141045148690790b43c001d64100198401c0740741121190f05400e20b407400d43e00b110360603102e000c20400c880404403100c041000c2182d07040765001502103203c22031031415030224405c1c07100b2801640b007240000680c20350040a584080182018048007900c0240c0003614a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 778167553 1250 778166303 778166321
    0x10c0b0a0c03110703080601090e071d0303070f0507081e0a06570c02190e0109151a040b030406090b24030a02010806040908092d04 58
    0xa12840800034010321016804030111031010300d40842d4241c0c00000c01c03d100c2c1c0c03042100340d00007521882007001a58005030020003c1c102540b0f103190501c1c2103500140140c010010440c42482c2c1030198005941d401c1050720031250b00260302d0303808403d0510301141e07281010f10400005000e04c03404070342c003540d01c601420380e501e010350041d1501d00502c0e07680b031004114400c21490980c1980e10501d08440408900c02d0040b88501c00103850102e8107111140e000c0c1904001c882c076420f14441750030380d0300d5010390580c030700690548106401510070035448944c0c00c2ca6420001d03151f107409000066258082e0040c0c003075003400500c5200c4041d100c103011340d541c0c032030b5090010040208003c00c0200b40205002180e10500400c00040e14180503652a0400f00042c2c1e0001c0c050301c0c5075030054103c0d9407903e001c114030780c0d4120000d0a490b500d690018144001c01012507102c5c9550361031403010f0040d92011101c000400508082e0311500c03c01c00105056a002c0c0d542645d1000819800c0d4981058403c035520 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 778168803 1250 778167553 778167563
    0x27150603100209150304031701090509070b09010507030c05071205010f060e2211060403050a0c05100e060304060204121b06050a050f0a2c090a02090a0e04110d0b04050606010c 77
    0x3400d0f130311440f610705a2004d003046040081041c60050121400000640a81240c1002050364242a081d00c0e28000c49500000602c98080200c0d0031207a0300581140c0034107074103040c91031070301800d81000e40c100240360f131000541403501c034048010400190b0008007426078546041100d00d48500c0c01800c02082140d081c42103050070500150400295038501e000688100b40c105011100d02c80413070419041035000300c036540d0100105d0b9080000d41c0910b04058042990141d00031084580000c1500081c0c050507801084000082018008140c0449018254002241c44e08423410324044648100e5904028030755001161f000c900244034800311001e00e45156299410888030048640084d4018203216052014100d01140805002a030069a82c2405d103595034094001c1e40600c406100010b00c0c1c603450600c10861041181d568003e00000d65241412100880c0c3d103620b0016a02ca206032000760340034800b00b040c0f20400c41a81e03c9940724900c02ca0a450a41d00c1d03117401034030781520098009103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 778170053 1250 778168803 778168819
    0x18010204080102070221070e1f060807030f050f0c0a02010b091e0106091202041a032508060606250f0c0f091401170a06230106050c0627150603100209 66
    0x3144e0012410203801c45050349c1c08400000c00c0d515000f40ca0b000030b921640102d2500c030100b00c4100e030988629400118000c0e010b100518149001041d8404c00420461001ca4085040d03c03142e0702c00d52043c80f003201c0213440034080c1d0510b01e1015550046511510794802034a00c00896601e10907250f25003207884c000bc13100c100100950070170000d0080c41c0307081080c2e5000c103001d0320b4680e0b0b4204405004030100282c00c03c0074180c04c0c4581d4106844907040001d05601400a1103101e803604011965800d10554203641c01c3e0160718141f00421220810141c04440280c5401c4180010842400101e079000c03899005102d9030342840005840d2040b6245100d100462300401c1922104070281d402002c448007903c1e180845503407103404440342091144003114605d1740072800204910406800b404d0b031800c2440c01c00912202c280c0da03d00000303120b42c0d03040f802e10444504010f407040540300d2150402007695101c118140140c6204042201c02501c6841408240030101810340308941c421640948840 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 778171303 1250 778170053 778170059
    0x90f030d08011809060c0e0307050a030b010512011d070513060e19021605071a0906040306020f07080409020c061005060f0313021215070504060e091801020408010207022107 76
    0xc894185602c583e44a0354856075000c001590030700c10000440d24980754146e0801880082c14500f220301e80005001e01d000610a00105040800f1517044550442d01c000819101c205100d014005240100c415003804d0a0910103000c8041420800d0b20700a454000c50407810b00d001c0402e1360124450312994001100c08200304c50700c000388070b0284440050ac05441c29903400c0c0030200ca5014400191080e420555003448811440c044850f580e1100c600c00c10706005a9034000f0f4068801d1384001454a1781c0065817600c1c0012040680d9480c64202c0800c9413100d69495060010754010b800380b1146004100c0012010070300c940c5190280c171009807000d818904407000811031984050310080400c0001750440c401a40c13504001400004403c010388075054200d6040c910031100a0010002d10034180014800349034864200c0d13165100c2141d040466444005156203003000244003007440d5400000e01042900e0150000c04445109684481440c0e441d110000c0b4603010f4056900c0503604410410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 778172553 1250 778171303 778171319
    0xe0106051c2d05100515240a0507050c030105070f0e0f0a0f0e0c0a02151504060b04080f0102070b010b091903030239060c03040317090f030d0801 64
    0x110405803103441c50380c01c08040e0700d0384880c184448440c02c41e0110407034400d4000f0024107124503071141c44801018009070070410711101041c180615501d01809260185000c104c0060259002007110200301940d59041a070f0000c1c51030344401001d5441d446070300c20f4a4242e040c1441070b1071003624540d8071903500303000d8940103c0d0341c14400703401103a002e01c0295049a040c0c0d40c4407070413002400710080003135110b0300d000c40b10700d454400208885040c0d4003d2041138201e90300442c844140c011002018203050360341080b484805001c01340450f800070b20340440441d5800c4081700030000c0d2003540c070031109466101c0c008a402e034400c40e440101010f8054004001c419152405060540e5000306000845d520b58241c909401d04641d000350300680c0001030070403007680b0451000703000300401c4076090703550440c18548140102c903440700360f40070b14000184102401001d0040d100030315030000d030036081c48038100c410151030b820030204644902030b42ea07240ca1191400065002c070583c0140c94000b4980c4c603004038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 778173803 1250 778172553 778172599
    0x7121203051311041d01020d1a1912151a010212160b0604090206130303030b040501140d05250e010602160e040203031e0a030b0306060f0d0804080712060e010605 71
    0x4901422051703e450109014080c0090301c04800240300c0000c400e0601e0003414500001d00e18a07602900200d00c8900c1038680c42100344082d5041c070564140700d03030a146400c211100d00407a84400043c80d040510200408a4050b1091110264203c1341000b02c1c045080030503211304c03140c55115442c6041000c000400c0209a071307621510050000403a00c2d0150003050581e44002054840705085038000e2040580521911060a1b8180c0d0704001a605004581d82510706245119100d00c1381042c0140030000108a2510300d5000c2c100310400c0100c4800c0420b00d040100e011750b04802e0701681c000b080f8a403001810b0320314800d9240750891000e207003c00e41010000040c1c01660103000c2044605005134190107559465a20407d4081d40d46e0001d500083c00c4600550445d40300b90820030601070756699424100c0c0c90f00b1b80840318400788010514010000b44940d038008401c070700520000003603541856003c40d803a01d01644043c0041c03441c03030462500322a024010341e40e111480c0200f4051803414010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 778175053 1250 778173803 778173821
    0x10c0516020d020909100f06060905190302061603020c151209071511060601030b060306061c0f02040e0f0702060c0d0213260106120b090712120305131104 68
    0x1141c2040303400d4000c9512004d00b2190f148060f44820300344241c40c2140d05c00e542c146000c060b0100091800c04400908004080c400d49110f4068a40e880c8580c2c109907101c08021680109010790b01c122a0303801c100e039000b8a58040c0c0150090b6035414555040c60b1841c4a01b641079003003064500f912005007450303d45030140000107188145000402c08200800101001c07103026240c821041807030303c2e5582e190a000408030b904041c140140014103864504c15240c000c881102c040d5140d029000120466283d07103813513504818140b411484400c2c410ba4002d0064500008441503a540c43d2a041211000c080d03451500580c0540c0001c0e2400701c401d0042e1911320090f0f0710241c039008034643c4890f502d944c030f0380040001c031213505241e035001a50030200300025002c001c000e0142c586041d070300380d003820300317614000d420464500d0018040b20002e002312400340c2016000e0094090303050400300030300b03070264190b02c010030314010104500048104078941041e41c4640d0303824614000605000150071210303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 778176303 1250 778175053 778175059
    0x12020a0b0c071a04030606051206041203290a061d09060402270a120305041a0909040b0a060b07020d02010c080d18021503310804031112010c051602 65
    0x1c0080f84000d240c082c40b0078a0744103044916156070441c06d1002c00ca41069000f98450140b020306030380d021202080c150350084d0024100c40400031046800d07030160141035206246103180c00e00c00c00703601c840f98100720080001511460900c50b00e1f00c00969040384c0e0842d404120720303011075401c040c6180c10f54005a010001400160074241451008680014034000c42040441140d00b5407000f401c100c8014030042c585000b48101e000740a071400b074490711540c020051030f1403c800803101e55000290481c2c010003001b81022a041c0340600b4405818201500e00c4c421550410a000803004603000c180e0703030301c1074008142009405541d401500c0300c9203804400c850ba044180100c1d401240b0b1407040e8a0a03221203451569402900d104025140c0c01d03051001c0c0c0c1d0f0241c24428420800e2184410b64a590040c09102500b0704c0307510101111401e80f000014411140001c010080001c00040704418003019950620342c0d124038103096081e0342c815201100090401e01804c1d0000750790020716003542d0300107 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 778177553 1250 778176303 778176313
    0x509030a121b080306281e0302060a05040f0506120106030914030408030a110109170d0e10020421120c060f06090203090708010c0f030c0e0909100612020a0b0c 70
    0x4002c0d0806604241d205807a8100c001c0100b01982c1010f2480d0407a28501014501503916010402d0036401c00398000c0c15641c0106200140810704610804400b035500246001c0c0c50b215650b1000f400c0d513006009683c6251501c0400284038185174099906c0b0240b20150b41c00e0701ea0034804210001e0041d07810656009103044901c100d5502c0a10007000505611400345649110614001d44100c01c0d5201607440c5a1402c100c003804245486502e0f28000820306480e07560b01c002ca43d0701009001d50003e601024060100c040c1c030001e0041e8000d20840d41b8070640c0c200d1070265010400504160340c03801034600b60103c004804034034850740b48041c0d100d00c50000000c800d032280c60032008651a981107001a554004240803d84100b0050700008000302e000034040b41032540d80003012040d10302402002d0545880030b1180709402114550044040502811080e140c00001c096071800c0d01c0e009001407501e882c00c04103922100c613400c0e010464028140c4c40c41030f0b25082800e0b01550144050702140c6c094 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 778178803 1250 778177553 778177577
    0x90f020702100203090102010b061809060303121518070e0123030406050f060a0311100c0b0403020c09070e21030708070b0412050a020d2a06050108010c0509030a12 72
    0x2004000c640b4008158000c40e1251125070000e8210b80e42d40502c5441b826080c0101c05072904556031428412100380d50754822629180e010138554003403101468610090b0748204180000a151060303121041228101800300071500d06031400407055858200140880c1c620304001e5002d031842d00003481507650490340000c1c402d40c2c6180c6540081d60100c440a440c2e00c103002c464540c110215411100466122446500e03641d10001e840c0144c540890055064225030b4120b140142d04421440d504030703002c0c0c15980340c01d1034005d448480042819109001580200d280c175031044500d42101e22001e003190b0300703500180b40780010306101541041e0540c44100603200004024402820801c1d00c0740043c5001820580340240301042c8402d074190801c0000c0c0152807400b9800030ba800410010760800158031601d50a400794882058451581150f03221150383e030410a00c5c1c1c2c00641224400e034004c1000b101d602c0b404903132505c101c80c074a95159008056480100d203104416038010301e05410b000030b101003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 778180053 1250 778178803 778178809
    0xc041d010e0709050a18060b15040308070314090a12020a030c150201060e0f06060d0b030319080609130201120e070306020703030c0e011d061b1e0a020109090f020702 73
    0x700601e00e018907600803101c10000a16140659900f101e1240c82c28032401080f503a5460b954400c41d500a01001d0710f420400155454840510300b04120a01c03155640f15243e042c030a0080c0e10048049002401da842c504614800301030a03100a920000d1085a0b020319000020100200c007090999000442c01c40c0040054000807002e001400140c41004c4424022a8060300b11081c9d6481000d22004400c01c004401011002c1d07141d018100310b8000c1c0d10b50081021980080c80d2a00a2681501c0001020740990403840c40303804929000b903a80c40340580d103403024018280d0059034000d01000300e15100c440150301130081e001808181c820f000654003074003003440340380c207095034005e440796640040c0003814554540903040d00944103040c10f1068694460000340f10080205100151303080c0001006441d80d00c83c0115644cc66101e12004016518900c6032500d898071840080c01d00d085d103d085441885000c26440381e016016140c920f6000e2900c1600405800980c0300b4607800d9900300070f032000582d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 778181303 1250 778180053 778180061
    0x90b2404231003150605030103050c1309051b150903070b030601110a030e0a0b0909010b0c030909040b060907230304230a0309050604030c05060d021e030a0507050c0c041d01 76
    0x1807055907001c18050b000400e84d90741240c5035009042045000c00061020441c001108003d0319000d03107000000300c01942c070100040400100040890161001c282902401203504c0520a43c048501c0c003c604103056802940340710340e9055641580142030200304202e8528055940020103040c5110420b0b440301181b800e107400140c1c01c0300441c1d4115890304070344c107012041c00060590524400d1805203040e00151004005105a00a5810010f1440c829400500a4420206000c1d0907601181040c1ca0f0280346081c2c200c403514011004900042e061501c14900f9800385038034a0f81d082c2242e10b2900284c605507000410030349100400100148601796145090801c1d0300b1494040d2101907818680140349901030340c0840d22901052001f8004981171006000031240100c171707991755502d200f507a108007a0003140c44803840303690310700644c01541a04800641c82403080040801141c0e03a0110180e03114001d801c151144d9030320134003c0d0141810294000240058009151300706240613a030320a00755 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 778182553 1250 778181303 778181329
    0x170a0c0314011508100e1b130602010b13020f030103031817060603010b100203120a0f02190e04110d0b13050a0603110901030b041209030606090b240423 67
    0x8401480440d41204c2d4080c2803aa0009a02620788045502e04102d500f80703401c0c0039214484481c804a01130b030300e06a180c0d0403500c00d4007404912202d21580ca8001034024108884401c0c050710340540c1a8944a00b075108031080f80c402503040318116421520129203608502183c0300186c07540c800c001c654480707403584030074140300c604000784100e10340300040c07509441002c0c0700d05010701c06107484444c007150040b06448002101c001c25004031750741c0052074070140c4403154100139807a20000d107908021708250300100c01420a41c1301d145c0440c0031002480201e402140340002e00740e00034080c44501050941040a00710001400090100e82154408048a500381c43c1a0b040f143d9605040080024854030340c00c11104c00c440400031580746484100a6120040004110201d014151000c890040c440a4003854210000f08595600d03040401c00400f00f56681c2440b40c006000c0d00d101d2400180d9030848040e01d4152802d0500d45480864403910752086a4112680c03848001000d040d110941c1c85008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 778183803 1250 778182553 778182569
    0x3120a0507030f061809080909091c051305040e010b0306010b0405120c0918121c0f0c0f0305090c0d06060521071221030507030b01170a0c031401 64
    0x11424446005411600c1c40b20f1203091030384c280081040250780c085080000a00d0382103012520310001c0c40d000407688100044590b01000610a0200d400030000388241c845c80c071649030f981085020300b41070360140189070314004440a082014066070800390806100c1404441c00482e4078801c180000e410201c090b04604141000810100800d10301020f0003207090743c0083c058111405101d0104031440001081c00c1c0040c842202035403031030302c0304201c1030f405181c406441607140e8040104a500d50a500c10b485d01c46030f82000d0340d86562038041c0c440e40c21300110a4442c2c80401127100d00c20340c050724000b044c01d1a240604044009642c550701c001e07614440c8281c900044a44c108000c002110b40d031400c0700a0351140413403146800c1080090004c0079070707460001c1e4120008141ca490f118089000548070f11030961249481d900c02d4041d003207030b4081c5e0b400c4d803420300a0148003801180c903119202c0d05c08459a1324480441c40415803a40040c062034418a00406d01d5281070790b80c49407402083e4440c1007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 778185053 1250 778183803 778183811
    0x1008160f033c0204062c18030a02012c2d1e070e0709030f0c05040c0e1203031611070506120108071211012106080a1a010807150203120a 60
    0x440c9005d10500000e020b0b150661541e9141202070b0110b100401e901103800822020041031001488403441e4044c03001003421680e4900704c52030700a001e0010f41044284440449500c2103410048548003d0110380301c1d00104500f0308552038103021030040c038510010603410050500d44001d010701104c10b1101014190b030f6070140b080607039185002c000b81c0c070120303000c8601c030240b10290351701031050000c9a4100219201c140c585041800850526600c60fa40c41460300036070f88021070700701c01441d0407154201c0301c41d49030216045009842c1d11040300c6880304003464401d07844256000c0c0c070303d80c85808214001c5a1060351500042203850b0700801d030101c92540b0a40040202c1d07101088034201412080142e03800805540d2303a004558024079101c0e0381800f02c020041c07450b4512260000080c00200c50f8184099070742c1b038035140c1e250701c6040b0301a01c01240c10b2010741210030707041e1006070403071b0300e4000100300c5140340c43c02d0034082d00c042d00500411400100051103200285071403c0d070080c402410001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 778186303 1250 778185053 778185173
    0x50402132f040e070f030e030a120e010c120216020303210703020a020309041806090b01170f030909040206040906080309120d02070605031902031008160f03 69
    0xd18194080c604604840c1c01004103008003d040400a038200c0300e10704012034103042d440d0301500500808600311501d440f011900109282d40210048201144c0403030800080c114160001e003038613072850014011408003c001011124070341d008014002c8030f0003a2810301685540081c2c19036002842e0a80502440020400030100000071640c10110f581000c42c50301c903001801075200d0040140351031280e95115012090300140d08550540183c1c007030070411001c6041d01d4243d8111701c0a0003200740030504622080d40418000070903c040c24031080c025400c0c2200c42040250304200200101d030460130601c800030b0412000d02810000c0d024541c007131a00d03900e400c010f002e1342a400c405100070a51103100d84000321600402c20320f0565085207401c50303036035440014008cc031503005c0c4006007445200204020010401000b40c1c020366032150b0540700449491346020000c42064056080443d111030002c02c0054100c240c0d08002182448a5074890f50070000c032030700041e900720002103031700070209035003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 778187553 1250 778186303 778186361
    0x90218040605011e03080708090603270a24090f030c02030c010e060703080702010e030403032f072108030a050702100e07060311130f0915150305040213 67
    0x20340901500100000e00b0544130040c0143e044142c8405409502c0006140d400d1001c004d0450380c502d040904125a281440003500038103207003406242c8610b440300840c0c5c80c2800c0003ca00003c465401203146041c0201d60301c12400301c1c0110041040f94540c0e070701d04e4000083c150808080086020b921803240c5000280107150034004100407850411541502070000c59560f142a1034081e03405203010105941c80310003d900609030071140294034400405c0000c2010b901c0f01c08800c3d90101c80070006494090030b4000350b01c1c140b8a110342c02480d04262414021085c5108444502c0b4030108205402d840094442d00c203180c1c0140d6600080903103a6080003a1039404104c503411666906204005012201514139195a6907014180030951110310240c006141e680c1a613060b00710449100440e0b0f6a90f07220030f00c22180074401d161182d8100101100c80f80e1a1000c1c14080b6600703104104030040310458211300900c0c008208030f0b4840441c00103844d0b5240c481c801c01c413071107420032200008800140b40c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 778188803 1250 778187553 778187561
    0x1201091b0e0a06150305060307050a09200a0f18350f03031314030406030510140f090408120711010e06010302100f020a05060f0703061d0c09040902180406 68
    0x2c841168189802080000c0d105060036000c2d450038940004c00e41c40300b000003030429000f41d200381c0e80311010020114400c1010b5102464440800170041441e0102000c118a540606260480852803490290110a003e06411500c03c02c400000112240d10b81244202c84400503054030000503a0444400401f003022460403502100b210007004100c27503110315a5513a100080c400c1050307201407011901003144207003800310b00c101d4910070340e038039140c039400018010101150040d810702c02e000ca001032540e60081e100303c0466400b42203040004203850a200c06003101070300031504054100221402c5c080004520741c0520a00c6c2c1da48010345202941c141c2c04c2d602c01036500f9541e41c000c0c000400040c0c1d10000c281e031120015080c0324145141c0c68200740e04180030408003500600668080001c51001180f5407486280980c40030881241c03984010510740014602c03240018440030082500184c1070710250036035510040000c104810790350f002c1401003400070801c014070040038040c0400c120b20390213 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 778190053 1250 778188803 778188811
    0x1f090f23011806060603200a11030c21040806071419092c010311030c060c0705100f0f0c051e030717030c0403030c05030415050a031104060203091201091b0e 69
    0xe03091004911400740c8000300048000d803100001f00004104607514014a60105030380d04076401d49407210142884140c4070000c20720041700425442d078038440d85a14100580e0140d0f0b1054008006a0303541d0941500c285001c407102411850081c0548840d061f0803401003003514204c4e503074020b1801c1c0f50580c441311000341068641403a8100408859045003807403e81c07411203030450350001664044401190038001490500d9400943c000745860f4080d000040030411104160b4200e03c144c0c640303101c00c8614008000c10040050486071005100c10300c10201c6a00050040060792400c4000540a1003000591800002183c1011841b035042c010406145107000071584211861840c020108441300d1045000c02800d2110f031850301e5050001c10415540a8003806c0b8a13490351a0710304030050440d8101c15400c000203030400d8150300805444070203580484109800860904103200104407100700300000500c0035660714480100440c10f01e001ea0043e0890484801c0c0542d4100364650b005120020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 778191303 1250 778190053 778190057
    0x140403110708120703030b0d0206030c040e07030216241b08060609010e100306080303071d0d0b0117010f0f0605120d2118051f090f230118060606 64
    0x20f841c008021804121000140e0600e4002440101c480002d0fa2844900c6406500118040100320b0800c078500e00600580703100881003412541c96030012030582c840c07800341c031185201c1c4541c1c0c1d1002070003056440481c101c16003107035070110001850740740c21039904001410070312218140b000e1610f40c01480440c0c11a1040d107071a8541041040040e00b00b04d06010700ca40600702c0468008841d6100381d004502404180c01641d50300c2c1000c04004103408400c2c2510300d040c40300b000c4640c03000d1a104c088240110350042081295a180c88894032040ea091981c0a0465403214030f0546200704904c40c148501e100341d0f000040e45401c2c501808552005406054029800326000103000c0f90400f08000f905a61a907080340304040c0b12520001902c030b0010b5100c810f00042c07072101c3c1004008280a440340031242440e003028841080100165841c2440103441030950024070703004a00b00400e03110200f03800e405801d140c809039805803400c4400181e101c10030380d0061604032041104900454008101c0c034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 778192553 1250 778191303 778191313
    0xc14040506071e060c031a0f0307050f060c06040f05070621150315240b0708070204090b0108030705010614010806040f0608070605090f06040b0a080a140403110708 72
    0x84004600240b01e44900a0844640121a150020300c030711100000c0c03a501040600c401030034040301801900d070260001883c14a84a03e0700b402d41020007002c0c0d000c00c001001440140d143c101440004040200001d800034000c10000c40b02000c02c0040902843c4555041c0c22013038010304140c1d003000c403142c0155040110315242c2c80020314842084406141d0031401c0001e0094954810700d020110552004010346000f01d44010076051503031041950782040003a41d41181c190b002c442d6021009401881c01c074900601c811808640700e5401b501d5004c3c40035100284a031800d4599154103078090780411142e41c00080c0ca0010003a003801885c000780004110400000c034040c00190524000411140c010341c5d5403141e1003807051440d0441802444042c0a40c0d03841c44e1220300003480da900c00c0c8903603405100c0c50320b000500c0f41400700072101121089486103090500102c0308031034400025251858598075450485104400d48407887d000354071980b511141003145111450411078580e102d0726254100c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 778193803 1250 778192553 778192559
    0x22110306030d030b0d020d201f031509021b0d09060903030f2c0102160b070f060609060e0403030e0706021e160603060812070f02090a09060f0c1404 65
    0x40020041c0b0914560b003004138140082c04041154807001c4000070b07502c54000368064023070040c0403071840c0000080e910741e070407a1460319060020201d100d0308505414200c827001d14118521070b901c41092101c0a0001204055851700c2c00700598024402c01c0306140c440300c038030407400c1d1010005240550341909049100c01e00d800e5020744110214807001d804c0c003c1d00121048160712881c0304041640b000f80100180d1710f0440c2100c0c18120304240c50b00e01500c242031292548a111580c2e210031180c414043c98030344042540ca410203064107010864609c0d40350700300891072400741e000b910080e042100c3c00c170401e8900b50a00078241d45180d030917215203821504003408003d0340403c0840d035089590340c013020030146103032205d440c0551a0001e140c4c094582e51001c20303840d516401c840126540c1c00b00319a1544614480d80010b0f2140110003000001102d0860b00141041c400c829404280c0d0707200091901c00d02c0d12a402511a202d140305c0025696441e144605070300007000c4021101521319403410581 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 778195053 1250 778193803 778193809
    0x204061e08010e01090507050702120d1403010b0a2a0501090b01120b070e030a020a08070f170a0609020105041508060406080a05060402120a08280323060a0522110306 73
    0x74060245c441c400d5101e000040e881801001294209903024001c800c9120100f041e054660046078070702d1000403540b0040e41045e560340001d0b2416240d02522141c039001c0030b01400c0d240b80c1600030b03440510b0302424180c24404072080600c881c105001e030b8004120743d591450032854040d0141c00404101c0c8804440d9004941840030142c0d01209038103180d0840909400000e02d03000042c1c038001c4d400032a0b210045481100815044200c13540c05411409175070f15045803545000d51031182103104c6d07108014520200b2840d801410010b8010305040307142c10346420480407001d00b801d216402183e00c0c4024040b41d4141031081100500c00072000d0700203018540e4545843d19409000a44181011140c0d501c10120034425656401c1d4401440755652519040c540303810314580c4201c0d55850540441078600e54000c1c040d5601c0482c6c000000d0100000107620400440009400c490b00300c09090b0020030b45845030300010b403030017080d007800e4120303a5112404c2e01e0503030f001c25164114240d414000c1c403140761 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 778196303 1250 778195053 778195079
    0x10f140a0f0f0204060203120601020102211306140618010602100e0c0306090a060f060e0f04030e03010606110f0c0108010b1b0a0b071107080723040204061e0801 71
    0x1154529020980940300014036002d0060100034000b49840014000303040c80e00040100700784503940d500c0104503511440103908034022607036210850100c7c00a890790b0024540e0303400303030b105142808200104005440c0d0308116644104004000500c1905001292420120901140480c0d500c20a05507052039002900d411141c50801146900e44c0c040d1844030034180b11001c540e070009000c8920340d01d403044440b59102c00c905400d0b11001d103002103c080071000d5014071000e0310000a01d01949803549030010b407644100500a0341004044040a4201c5d81c0c02c0c0507582c0100115903034101c50b4920b01c50b000d400e000309240b84035001d40c040000030500340d800c2881941101c00031080c02e0b440d258000608440c0000d880c108120501904200008001911003078074000c080c6503548100042d0190001e82c1e0b10310050003014100d80c0500000c00000c0c400e01c00c80294508407401c0d000100c413000010806a801c1130708a940482c03c51441c44a101c101070b03074081c40451a9242408055141c04160602a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 778197553 1250 778196303 778196311
    0xf181d0f01060219020102031207030c170f0c030403031b080601171005040905100c0c1a0403080c0d090233131a2101060e01111009021206010b0301050102010f14 71
    0x4e083d0782a411400d680c000e00c00e407442ca040d149611601d601d4500340040c010400c001c885004100c1764218400030141d2034008600c03681d60940012010f0f150103900c0070154200604c06c400701516103202004101660350ba8503040b869984860f4a941000b42c0007401c1e040104001c12020b402140421130381c2c032601000e940c1140d170182e80c0003500c0d1390203040540c109459900103942c5181005141c0a0040d031160301c1255080c05000c410340359001034002007010740300a4070081c00044116000c02c031090340c001c000b0891100001c40000b0402c1140d40416032108101c442c400b4418001c01d100300f141042016540c446503e914065880d001c2c00c40b140c50030204c40d6000e00000d42062202c88480655160204e882904501d4072070807141c1104500b01181c80f10034007801b070019803600d0460380954013036040b11041260481c040e0000480707400040006000000f004d0764010300c0028035440b0070009100c2e042c00b03086003550b00f0f0381c0d9605210000e42503032201c0d58903422841ca00700b082070028404030f0105401c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 778198803 1250 778197553 778197583
    0x1020f070e0a11040e1009020306060901080a06150c1e020d03120b120307021005040b090f03031e040306060b0301062f031602091f060f181d0f010602 66
    0x3680d111282c804004040200e041104160001800720741081072141d9070f0720405003090640040364941c3d607d541a8041076460070f4100c0003d02c100b01031903001d52200d6910014501002604550b140d0050a506d141004080301103410305074034100344100340401e40341080010a01d50340e12100c540c0031849c0c0a003265000780c2080310400d00705841007581d800401d6a400001e00c41c042000500c00c550fa103e07800581c0481c861038090000281d40c40c02402030700c0844d1800c401483c1070109610038000f414a00c2003100e036050004104040d40840d540c00050501d1281d41082a1202c2c00c5140610490704140c01c417000f420030520040010b6544811003a1480e04100504580b003d070542602d940112003200c0c204160001290980d8812002821040c0d03060023210b400304282c440003245000e00720b0b0f980e203521140240b80c100340328480c021070018080c11442c4c500b07a54000340340c01c1e00c400c0c502700381c0d0000305032080310304942c2c0c0f5a90101820540c201072800c0c400916540351503006035a030200b2a0071140c07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 778200053 1250 778198803 778198829
    0xf0a0f240c0206160b07200f03090d0236181c031401090c0f1b02150441010e090c0c060a0606112e0906022701020f07 52
    0x8846401e4441c6203211740c0620030b4007003402c0181c80580300c0300210854034503119074040c2110100200283d42c40b540d050580c0918600724101c2c0c00e000180b07003501c405a81202a641030744109401001410407c000c80e2205524021182182c10000440c090003c520440510380d0f11014904081800170140e0854210040b4000e514901a00a82009a103415008881c040006800d02c8203401c82e000c11103240d5250200e600d02040107544501585e0312450704102c1e00c8845200500700a24811595034440560707500b010340c1c1e405c00c100420324002c0545a002d0740c1c030b20380440c903038610038101c11f01240b03a40003160001c1144000030086940c600031144101746c10320104640346440c07001c4401041c8c2710b500390b41d12894a00c42e010702420091042c1c0700001d09240564035035000c0030030301542010b00090342442c48196500e00602c1000103002d1010481d60f24200800010583d1005140c081e02402004c0452550011078240b0901c6445500303055401252681e404010045102400c4c1c07001410101 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 778201303 1250 778200053 778200067
    0x10603090c080318030610060504030f2a090501060c0f0f21030203090c03060405100b030c040c03090204050105120a030c050a02030303010807080705041104050f0f0a0f240c0206 78
    0x100c08120745a000d090580400900c800790649050f00e0b0f144480401d504854946e11000441c224510180c0314100000b0014402800020f1a1a0f03030803403158042c0503103d40c0030055481065060145415045140c03200c07000401c00d4a6050042a0050215040c0f500b100a1140c49a0300b0744030359000001e100210290303048040100f807081320400090307666419000580d099401070022340c0196500e500c43e100700600000380e840c000400a00c00c2e40d0010244c40c6c0c01e0089a01c601c0509141400c0d60352500500750441703040c1d1168840c008090042d5980480c607400c80303005000407102d068005500a1f03681c0354101d1100f030000103002006641c545810b00e41c200721130602c1c3e81031140446000307615000000c00011410000541c1030103071101d142c1501e1495940354100402c445444110280c046401d110820143c50482110400e2020140151891007003a20006a4030a075a41141900354440c2d070061000003145c212a62403041c07400206040707100a420302800043d0180743c02846a0b1000442c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 778202553 1250 778201303 778201313
    0x10b0d0f050a06020f0c01060f0b190e060703031b0804210207030615031406061e010c02040e210705030711150c0307032706081e0906040c0b0f0301060309 68
    0x202c0ca102d4100000319125400050600710b1580000b090704610f60a1400101d00700c240806694105c803401240c003440d0411315960300310b884140e548464184140d40707180881c0c9494640040401a11a0764009410700151240c114100c2c20b010303034801002007200400c0300003400c07900301d10001490108070444400c51094200e240130100d0300000d1281d030070200c90301c2208864000e80401d4910034000030141c0c50100c51980c0d5141403c441303050344080101c5170308000701c2280f010f0f418001e00600d00000c005001e42c0110b402e540d49182184103603845401c01c0c201030300d004001008480003010900d4074000407901c6003a0f03030f0b00a025004c0c201b031001c408403c41654542001c050f441072241c452584424540c800d40392240c00c00c1c403050700850f0324032854a40c00d03041b0f650802c50601d08402c822030074506200c801c03543d440c0f005001c101140b8007900102c4841d541c8d051041c1c1301e6484000145000c0c5050300c1c004580121a50000c00c41a07018080c0241c0541500142c3e41911454500021400b01c1790600c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 778203803 1250 778202553 778202563
    0x9012f0f07120e060703051204110319061a1302030606040312021515100320040f140109030c1505070807060f24120f0b180f010b0d0f05 60
    0x20036050480000e18504220070501c58900301c0070700c0d0f1141e841464820050001500c00c00100600007002080041c254407011a07945070010301411030901d00c20b45407030200b4030b000c00c10004003419040c442c2d80402001014004c0f1403154a0b120701300e03400646400045105800300d8007034000055004030000c3d0098032410190750041d60017286180c414459400040e48407004164007803401e450500c0051741618407070710701c0d030300c0ca52020b0445407000c2d50760350045005107641c02100c001e041c04480701d10404d002c90805040505081c2d100e141403a4580030148900080c0e200e0441e041c081c5401081000c42d402a070007101311041140c00000c515490b803011103c0b4070401c48002c00600010a416050110070351103404010103284d0108000e81038561900201c4400984048640e19000c0051042018070091140c105220b110034604844107540c4008a80c0c400325119911f120140c4d0f49180100820090320301c1c40300d10440200411500c1c070006c0303001c801d5100d102070036504c0303942d8080302001400c1203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 778205053 1250 778203803 778203817
    0x25031b0e0312030403090e07031815110c0d08010503150f0c070b010e0702010f092f040f09150e0a02150d050109050703060b161e06050f070809012f 65
    0x102c090340c0386040d280240804407030f80900d08601003110005200303d8017038802c401c0d440c0c000c802c2400841407940e40b00d0001501080360030501c203803074800414086015601604001d20160090031500c0e601070402000d82c40140c0c04184640c1c070400310720f0626803811405941140700c0025264055680300071142c01c3e48103c480051000820800000b0000d4580d18454040e200301c4e40240645110b441c03903031081d50700c508805400f950641d500c41c400c9240c1704810a07071803500c488181100d504104005012207050700c181c0d0f0100ba071541e0440c010030240a68840c121b10444a04014480001d0215940c1c1c05180d840240a02e00100c80001c0c040c060905895a044260000344884d68642e58880b02612040d100c42002c00e0404202050042034002582c42c9900da904549107815903980b02c005400e035a0002540781e42e5204011030000c40c0103405020b2003503c080444c0c0c0301034184110001d04000000380281d041e80d141504000d220001607441141c81c00e8030210000380302111091201003440355207 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 778206303 1250 778205053 778205083
    0xb0d02100c17040e0906040309151101091b050909030706020d020919080c181311060a0503010e0612031902010e25060813080d060b0325031b0e03 64
    0x100000072018000b01c010804c0e5002d010f060f081d03a07191445040c2d50782030305031401804626850003c1c000f90850700e00d110b000124500e8140c03c081e07940c84003142118200b4400f43d84e0752000012034160785548038003a80081100b56600780309480c02140c115201e01841c2300041c6215000110038000c0c40b00d07a015100540f200501386995640c0c045441c2c02000c0c0e103842090403034041c02e4841a11490f0100603002154440b4141c9141d650b229006210780d803204000484060823030114803e0f40761203100280c0400c6849440329681d950500400342d003d40c00c01400944210000070800d4072000001c03080e502800e0709102c10040c1000030007002c0e409029140001029441021480960804196403045105c07440d07404580b042c544481003105e41c150b0480b50041c031000d01101100016140500800c8031000303c2ca000034005846207402c401940c000d46540f070082c0c41c900d0540350f0f1018140820743c0c2c8940305080800000c41c0b00003100001c3e8141c007400009004041003030401c1e6450500082000813400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 778207553 1250 778206303 778206323
    0x20c0a0b030c070213090201020f06220503040801150602070906120209042d02040e010212063c0f030f060723031e010906260c09071d01030b0d02100c 66
    0x21740c8002c000e00311034400b68014401c0c0440b241a2801c0401c0080c01501c0c1148a22440e442d2081e02036415a01250121510300c810800005d03a00000e101c0c10398030b420594008010640b601b40c00900d400f950350890380515151090410640040c1f0035528400c95040d500c030055a81d460901d61074204208280f0610038681c55403038041d80c004e200022400d2882200e0800052000461482c200d0007800c0707980d016502440041140c0b4074010100145151004000c0b414042611892000070040c01c254200150312400700f1090918040e0000f060780881580180340c0d400b1114409540d514020300f0b5101844a14840140780100800d05030f00b8207610030210079030781c0c207101c031030341d04545107100000b801c440005001082c001c0c2580070f26003c48080d004003200196001103036002e4041042902c90071441484084900750f125544030a12403480390311b5001541100c1d11001c40f820200381034142c101403078242d00307801035aa404014140c5540680b24000380b070b03144090030349600b00c10362400f401030050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 778208803 1250 778207553 778207579
    0x30209100306091a030a03110307050a0c1a0c06010e070905150a0801050306070903030e0117040f1421090402040b0d060306060e010612090221070312020c0a0b030c0702 74
    0x60b000b100c100c1d03c808804100c0e21324010380303902d03200310403240544e03054000d9094007020910030032030040041c0168042e04d191110584d40c16113400c0707a22102b25450306002c481000000c1d048aa000100d0407003640091a0920320743d24140c4500050107140402410013022404c040d01c200e03d031001900001d4a04507040107001580816070b041303040c4074800121117200125081c20b0210f030150146080b40c075001280340c25540c05071009803050044604002d81c50a508114110f64030b4401e002d0f0f8001c6406001c80400c1d401d05c2805400d41a459020541c0200a099052100b20a1b82010141c01a44150f180c0b00c2540c0002c001e4032445c0c0c000341000700e010400b0b0038200200d81c84602120b21419042084950365003d0709c8101000b48108404140c6107200c2020490840c4c10071346590788010080010016490b10030001802c00041941555000b02014405c00a10031051881005203000401900107444002241c01c0d84501851822110100100e11079803405416129405d50040c410380c08564 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 778210053 1250 778208803 778208807
    0x1e08040f090b040b010e010c0b0613140a0f0204050307050607050f03030f0a0b0f090a050a0e0d050703030b0405060913151d0c012d02030d05040803011a0f1903020910 73
    0x15100440900c00d504c0c0c40058040d942c0120344101d454030040e150848000300a458072040c0c07071030042a854214405030329202d01c40325a482035a0f00f07100492020901ca082c603d1205088440d4aa80180380510411082c81f45030740003d0210b04460f001c0b504150349072420b103041810118980350010710f901c404001c0c00b00407102411200d03c01e450b0440204070049503802005808034a80c4583da41280750000450200101508510382c00821190041090501640c48a281110744038136040016000302c0c4000805a0600440089440448007882103041290000d503d500002e0031048080141104640070000f140d220784201070341000080001d2030300b00c0c0343c2e141b0300c600595a078081800b038408481503540c052444441c90780408140da030701d10000ba044035010544414039a0040d80b2080c0180903a4607640c0c001e86104900c114140340d202d500d85007800c00f20030031020000300d01000c02c5c8002c0203403074030b00400d81d0796500030381c42203038001d00c00c5040c260000d2240350000343c0c004601c0c0c5803a81800da = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 778211303 1250 778210053 778210061
    0x11030d020c09250c05031c0b12070b040603320106090803030f0a1a090c0909090a0809060d0902120d090f060c0b0903040b03040b060112091e08040f09 66
    0x508161181c81159403182207007100d01403243d0380340c4107002400300b80d103048500c1603261030605417050f0100d034600401800300401000f629812080d0751a19000c56030308a060480c10070300d060a412009002260a02c07030342410318000c0d405500100346e80c4440103100c0c02c1407802c14190404c0c2d69524100101403a8181c42c0c65001c1c00d024841c040703120940002403144000044911411060b0f5001040303481d04481000581a00303140c02c02c0000c4860b804041e9503a40b4501c203030203620440ea001d42d4644800040c4025107800500b04411500301940c01000f007000201194521402101d20503a15450640c0c03240041864080194010800100c13000c510071000900507840001926254105541c4020710000013106001d9074000900b840b600c40c000a40a105594101140340156401c0030340340d0038005070750781045905a42080ea01d0040c00300650700074801044005013240c003070140142c1030f1107411500c5c6050303031540c1b0380514958404042c03020304425035024200d03544000a100382d5031558007000e4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 778212553 1250 778211303 778211323
    0x30b06091b040f0504051312110f01021b070f030209071101061701090201021015030206030a020409231f170c09090c09550f0b040b060405040911030d02 67
    0xb8a00d0440890510301100180342d948a608c5442252200e280d0a0112455140300d41d49040c58499030703800d4010070800380080c10040c40d1000c001e00000c009440c5d400c1c40c00996501c4800030030007050007031015840d2003078a194020000d040058044010344441801042d26502044050320281e6a8043c400b90641007000e0b001c0c002d9080314080018200030700110b54040e4240881000c61500130001070034644090741d4000742248006044c940d441c200002960440014840e844003074402c81021520903000107600008120114068076034480102c031003298041c05031103000d00303040e940341101000402200c8083d06003d410fa0142d818400020740d80c600244440610071203403000040e50742c1c43e0312400a102d4031561100740c841e0500001c0c3e04070010908540408c840c0745500707602446a01440b803105100620010001001800c0d85015800c6490041c40760344114203183c02d4200c156a02410754044e00c104890006025010380b409411310048083c2d4aa050f006d0040461030b0342e9008100d1030a6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 778213803 1250 778212553 778212559
    0xc030a0e0f040507080610030204030b0f010f0f0501050901031a03070f092708030403020a12021b010810030204150306110325080109110906130816030b06091b040f05 73
    0x41c50302044100002e07118221101400145840000b0300e46103450501c0282c80002410010700d0a0f480391182208032001b00c480007190440701c00100400088101c42c20000c10a0660711800c040c18000000e080e84520000700d4100340d00d404428000101410b185c400039200102111041503690442d03000080180c030541001900e0b00b030400500f83e104003000c6010380541603800da07820f200303a50303201d5660300042d00680071441640c01131b00005070b5000075030b4841052031300182901081078008060188014030098100004481400040c04c4080c1e40c900036a0780c103c5002c1030340a200103205c00c90010690000d407456090542e2a00780701c07401c034000c2d4001c0c807110f0401c030621069000c41d0710703007010841840f00006005000401000c58943e00400303400d1030a40101d8075141030300000403a00d400c000b10004170104003100c00c0180c030340c00300120400002c0103400120711501c2e6132290400d0940044c01180030b114183c001038240d0381859501c1e10171790b4801c885d01d515151945225540d0700c029008a0380 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 778215053 1250 778213803 778213819
    0x6050411070503070f11091311180406091b0303050d0b0a0b1e040b0a05030a0606081303030519060803030103120302070b0c07020d081605060a0606091a0c030a0e 71
    0xd8031542242121542074006005602d030050603901c0e1945c50090318030030354040035810359070300c4182c6d2006078a0b400340140f211200c502c16a1428000090195940381c64401c2c120b0307c0d07003012a025041d4055901541011001a144c0410f003015607070a01d040c1d180c081d250311201d03404010160414041d060000060300c0c07c01c0349102160902a01d100301740101020000d06003d02d0808140152009252448500c1c1c1c1c1420213548400550480c3c201201003400700c2c002004028203410704c3e108400081c4814038290303615050003120075000100c11000601003549840010b41d803182420364040300903007400c204108240e51159181e480350020300040b600d4642c1070040702c1480b0311a0080da0302d141c0d0080f03c2c14105032103000c60301c0c44591021000300d8004900000d0500442c40b018040c241050702d894410388040460700c3d0031410300c0e00040c130705092540341580a01415521000301e40a8810b50601c0f06004081504d42c1499402800340d044103a12001031000501c640c048612100540c090354104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 778216303 1250 778215053 778215071
    0x1060f081c020a080f040905010905180c01120c030e06090102040303080a0603051009110d081308010e0c01110a0c03050d0f0302090907080604060b072126100b0d060504 74
    0xa03001001515120340140c2c4101d083e440840c404500410300078400b48030281ca01681c55144c1415034400364402c81d02c4603900c00412061404507140c0c00c1c0d0740d2010101501440319440006041c1c428080603001d461681e8040e0f0010aa010f41d000c070f40019201000c84d035903403810038102d0303020358046c0c0001c500055034000455000314942c01141c085d00c1d482400b400c00800e01d80a050010002000309640d10f940c241402031294641c99151400903004114031655640c411442c8481200150300100c0c00e40e240c002c59480c502c10225a03c0c0390100e09190448000c01e2004a00f803502c44c00c8080600801d81584000042080000d4000c030240000e40740c64000c0d041c010426400c83c05800d6403da00114180001000f10f0321401e045540004002c10005d2a1034860303c88620030741000900302c2d44045000d09426040c8102400c00700000031a280c0140b070386200344460041c000455400c880040411000301d0211440000414007829400503800d445c0c0d8072000f05140940024898180a285401c00c24 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 778217553 1250 778216303 778216333
    0xe150c010f0623220e0a02030705190b031003023606130c0320030604151a07020310020703031e1a06030a061203080a11130e040c03020301060f08 64
    0xa2404200b1103d00c1d4140c003000c0320a00a90b0140150014920400e555841c10344070302d984180710180000800818140340d00d48140742c580920390f040701d8803880015803c00c004450340403941c2c041d200a645a02d07140e8580d480141c2d0f02159607000203512507211140130400543d50400d02c030100400e4400010466100304094030202402d03603642341c01003400017020440001c1a040a111101c03a8a0002030350a40e2480f40c40c081180c1401e0b0b008044400800c0c000c80d85040c0c0a00c1030003d010305010040c092600620054280802d0080400d0301d0003ca140025503605100c40d030f88828503900f00350b60350391442c5002801088181d84998600c00c2d01d0070b00d210000c10521510502c04058a04c600c10702c5403450030801aa08020b00c9400100d46520b40070a2a042040040d942c2074806d80350b245446c10460240c10680d040d41c40e02092100302030040b016000204014402241c143d0302c030003a825246d60815144540e46a040030750507600f002c4001511701441405001100d00d8181503465a170100001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 778218803 1250 778217553 778217579
    0x230f1504110a0503070c05060c040906050406080307020d08130f150806010e010c08090d0b07021207030507020d0201052119060f03080901090e09100c050c06070e150c010f06 76
    0x9441d0303012005001d4805820b010703100654000791682850980ea0105545540c500307082100d600049820102c0c0030800c01c02c8502454020340400c55050120324200b080ba299a400b8550000c0d01c107a1202d9406c0041c071200f4421580c141c03400212040da200d440c0c8031801216001407060f14034045001c880100260b105121850040300c05079500c401c40e8411000448014015182c144d40050041140309460b03620054520010b80c41183d0b880428906200e020303051451081c0b4046202800700100d00c0040d43c007400b03c0d00600d03811200d1480100007800100e6250242c4c0b03c42104440b0034150084490010b0b0242e580308001802d18040c5c20320112800f82c007694594400c5d0400e20b82c0305c88052000583c00c101900c1280d0b018034010040d40e42d10b001c01d0300e00c0b0300169000403080d00008983c1c00003c800e0701488183c1920f80c1441132610410380d04240e0389501c002d09a00810460101180c241e9662218400303980d8403010a0b20b4491014204c52402815108001c3c04050b03c2c00000050245103000f03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 778220053 1250 778218803 778218821
    0x11e0602010528060902070b01080f0303010e0415021c060e0a02070803010902070201020f06010e1b12070e06160320060103020a09090213061e08160306230f1504 71
    0x40041c40980c0c401c80e0101d079601c43d44010050854039207a000c02d80e50841e2014001c01805a64030903801c0d450a0312042c2440f060010a04c074642041006200601310318030740e07a400c66480b0340441160805101450300a009508400c0f4a416101c202665130000d1600702500745c401d5503191140c41d446100c05c8404070300c42c4580080c21000e00b4401000802d07840e42c0502400390060040d1051003d500314141c2c107140c000d030040301d06d8100c02414440341622070130020141c2c202d400350162500d43c40c0d40c0448081040103141d04100120031207506200c4d01c0d141b00707450380340810b00c0140c03000e01c8140c6801740c643c00c45500c94215203440f090803280a500002400d604030382d000b804003807125080c20701c81005040f185000340e030040350b41c000c00f8808140b83d101d0b8100500e2071620040a481105080804101450340b0120307e50b8041b01d02400c083c22030141c1242220f074010b20003e800b43c400007100e0744c0650b1a102c80d03011688031700c1c1001311a200205c400e84c451100240c0c14442000c00008000850324101c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 778221303 1250 778220053 778220071
    0x140601090509150402190e010c08031807030b010825050d150603051204210308071803062a0c05060c03090f0a03200105090309190905011e06020105 65
    0x2520030021414074500664000c0081c500e140d504003c1840450706980c0601040100c4841506d15000030541c442800b1241e51000d00e050850500507807101d14541c00064200442d11180420cc04801720f81000404001c40d031104014040d5070307540040c903465a017540d1b810500201c4000c1d41d550401156490101519001080c2001b0000c85440d1014110920b0700c036012035035a61400800400c404001c0f403004104036a6000c0e503a0380c100f620800c10030380c0d8010702c0705002c0303050341a08001a03003010300540e020807140740036024820250318010a0b02110f600c050718451400401070000d001110355003207802d41140c0500903d604041e41144d03514400070000c2d09a401c540e000c60303202884800115040213529044038443d80184c01203d0402e00c1c0c1100440110b1015005c0ca421840c44550304c158a08203400204514645504000e807030b48106001640310321590743d02074861f0211860040e0144c1840001000f181d0b8461240c0e07103c0354403444500c00281180305002900d1407050081d14480d038070807 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 778222553 1250 778221303 778221317
    0xe0c030d030203060d05030d061503200f071a041b21140d0201140c0a090b030604090f03170a0501140f010311120109050105092e0e0405010c0201140601 67
    0x1402044000390001381c4440c0c2d0082c43c10320302d40e020910410103055100000c41000410514010000c04031503203843d1150240345c1011130502100403040b414006040c038403a241e42e0b80d81d040c0300751015075100e0228010484444602c048142c0c9803907003902e61280744074146480b200017440c180806d0840d103500ca100c03c0f0000d14826807414440100380040003600c10291500358800506c101410800c42502c8900180e541d2002255441c1c02c81807226001150140040d01d000c0c079034400103100e810075003e060100030700000880c0498039140e20030045186c00101c0580b14088515005040f545550410340c1302c50014008900310010601c00c1030704031501980b0301040e4884640030321036a04d000c0300c401030516035200782c858260b900c0a4000d2280c2074014044c8c90310340d818074500c20101d45068100b0790007400c043c001c00400000d6444903030818107000b07140100c1405000c0d079a0002a0306a08a44044d416007000e00080110540140c0700382c0c1c3c1560028040035401e2200902e500004441c100d00007408 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 778223803 1250 778222553 778222573
    0x402031b042d1d061506040504051f06091832151e0906031204080a021314130f060612031205331203090109060507020603010b0d0923010e0c03 63
    0x40e175007481c0d8600f48050070560415a4030b4000900f11001210481031040100c207000802154040410300a0040d600f441000d2030b084c0a00d20400c5180080802c502c595146c0c00d03086002d5501000106a008403003c00e218207510b0441d20365920302c1903e55001c4040c1d0384001607424504020048207000e500003c48108000d04010403100301005040b25406009082420303101029260041020301619402410582014418051010083c00010720018640420403800700e015000c100e402c040d030810548105019070030116650480c0845c010310107440d180000808090001107015454029214110001141034200068503022642d88c1a0b0f0700101514101121602d400640602c00f604030102d100705140f00403400c1000d01c400d4071401ea90010400c0140c0b0b683c010741250241000c0e14056040080326408102140010701070030407552000310f4909140d4000b17071700107070060b5042100f4015418440041c103141034400548a010b650070141e42c10001100010070180883e0094020000603034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 778225053 1250 778223803 778223821
    0x1a04080c04090201051b0f0f01020f0d0504080d020a0e0a050609030616030e07033206150f030a030801080601150816090f06020102030f0f0402031b042d1d06 69
    0x41003403c0b07050000c01d005000b00d16500100c050307079412900b00104900128148220302e01001030400d0206a80100480f102e524500c2090721a0320106400200e51521a0b180048039405030030951882c2500c08110369035580ea10141042200800f6a10001c4180e192010300105200c2e001406e9050f03030201001c5150804a0340401c0e10085251070001003411000400394101041c4c2e900544080d40b50f621501c0c2080c1c07036412030340700705041007002da80450003598480781c5854005212500802c0784445d04603641c7c594450b0f02008a40050941b18244c11900e000742c6a14000c0c000e6039042d00c104000403605121010004112284070744810a155075480c10450044c8415000c4004010042c60001a004811600c4070003420f1a03400168491a203c003c50b03601901c01000030141c429240140f00142e200851511024011a10f21103c1940c440703021078050102180c3e0100008281156180860307040380381585d00c44441c180a008222030000740035600c00350548070020a801240c003040d02d01c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 778226303 1250 778225053 778225061
    0xf060305250902040f080f03040609032a060216083009030105040b09011406010f0309060b060412050105010b040e01210203330705040b0c010b0402070c1a04080c04 72
    0x100e0407030403002a0b151030410b010780e0080c1d88084c80c0040d020310107009800f414444050300004c2d0200541c201131a060700100014084e10001e0200304660b00c2d03102054100032a814500e81d01d01680440c602c0e40e030302c002550f40550541c0c248807084100404540c03480042a0450003003c84c1c109108211a0242c028141c5120020a58084481001911315684081c05003610483c0281d003449110320f4504001c03400c0d1480041101c0c0ca14503542c0400c02e0030b80e0400340015002c8030a213800035500400b80340c40002003c5000e00355610070310104000a900d14a50784040c80b180c4214001d000c0c990fa15401c0400d18041d074090041312102d06001402044400200300a401e0744455020861550503000700741040c0440000d98004030345200800603d0b414180703506106012010300348210718208a00074218000c0340030702c01400200203560500c03c00250000000000c009008640d12003aa00c1c0165001c10188034400c0400461000a007030318050101f40e81c02ca07110040941b00c00d20074081048018 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 778227553 1250 778226303 778226353
    0x15160f090b220515070b090102071703040201050c07081614060d0e030d090c05041d1509010b09011206110406050a030207080f0d0e011a030a02040e0708030c030307030f060305 77
    0xb40300740352000400f651818030813104140c01c04d1240d5503900103810110401c4000a0854500341e004205000004100c003240c0b07144009406113040c0c6075151440100d5407445800391070459480b5089021841c0e40001c40c16036041d05001e46100d40c01c43d42c804201d210b0405460981c1c0c1d00500034800b5440005958018480098081045d02d280585902c2030750201c2c7c64035507059464480f010410310a604044c0f02d8110078080d0040039000c0070200074110390b510341400e04091000000c80000c40c1e01d1001c01d41049221840041c4044400d40c0c50384030121a03400f2042003600c005040c42d0300e03003886001030411181a155940d40341d5151091084081d4060351000d181210743c0d80f010481c440440703070000c010300341070607036800041074410422074100d003541c24100c0c84081401c3c61000d0311070103035400103525000590540e40481d01600708050541018543d6100411b00e001c00a000c50310032a0210003144144a0780d24200100d48a070700c0305400312a03aa001c01040c3d42d002442150301080d000580c0540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 778228803 1250 778227553 778227607
    0x901050f04110c100627110d090303050402030d080417130b0f121b040302040b060d11042310030209040905010e0a05010f0b060301061115160f090b 65
    0x24162103001100306603009003c0a441904201c40c2070b01c82c6143d9014680040401e80800481c0d44e40002c0e80306040408013200b200c000340d640c0b0410f1035160801041e154100c1121204012585d1581005809003508840891090066090303451049006414160245e0780000300510645818411524194460201c40c401d4440c44000024840c040c0401050400e00038030002c1d440d58141c0c0541241003002801c0c5240d00301001d100a00741070124400c0e0b03003c60f50100e0f008200900300c01d010554500ca507807040d446460401c4080411518040024801c6035036800782c03078140441d0005034010040b000614640e101605560461510340701e40c000e0010181c008000203000352442d90707140d0840700b1420b0a00070a80003010b0a0051090038413030580304090307504040c011500d01c1400141144014025001441144d02c44114000d0080143d0524100e188040a4076820310910013a880c610800300500012040c00407105030074030a400c45400c6070404a40c150401030b804805c154050991414401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 778230053 1250 778228803 778228811
    0x30a171003021009092d150e18150708040605060319030207080c0607050a030c0c03080711151801110c0402120708060105041a0a0302070b07080a0f0b0901050f04 71
    0x50b03500e20405030310700260398540c1398000385024501000d8446207111b01c21003101d140c0c0707030382c4001d804000303c4c2c01600001000056441c85500901c1d0030000a500107041400700d000130821000707150041070444034090821610006200e4a400c2c0d000341c1c08844c03003000528101c010600042e42900300075041840101510421050100303484418140720707000340e0060788031401c00c1140501c07e10200c0b02144003542c1551500c54a43c07100743d034070241c580000f410868115020b81c1402400e600b84400ba603842880380d6614501d0b03091a403111151201c4451050100d0f0860020f04100c1d45c003280e0a0241c01002c2400b150f0a6200644950340c60821150f56070260208141c51507483c2d1009000328102014402410b080c4404000c4c158803005140304c3c1409002c000c24080d0002800d4490300807107601604d40d0b510303007910400f00c02900aa00c4010668921041480841b5030019621486a9500102000714048040c044400d444034a800290015029001808141001c0642d07412880c03010348089 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 778231303 1250 778230053 778230059
    0x140a180902180408090d0f06092d0804030b1b0706020705010507030204210303110f04030c060801030305030f0703021902030c0d05160b06060c15011401020703150b130203010602010c030e030a1710 86
    0x102c140e620f200d1045418107510310700d4588004203007400e4135403140d480307201d405528024bd40c1c2144a100364003001d8625942c1c90005200182100c00340030f06e401003200900e45461143c80d204004e0341080908071000d50078080051130082c442d10036141180c610750050489114010321000140c11802ca0036400c06494000074148501c0440c024030601c21030b1114030381c1d2589141024480412560000420007004100400c0441d5002068a4001100c20072410403034440b1a01035000f0702c00c40461944000f14184062090340e0080050301c4d510190805480380342400c14412200f612440c0584081050b17071020200c0030034100c0c1052070707010402074686842c1030b1114271910300d0301e010041401440c0507440014081c505410a40c00443d01e0203000911465046660301001120007940520180b5034850346280c0c036642d10440c1c2010521020021982d030350b1101d034024081c101c0c03c0c444401007030901156111181e400002c4440f449030a50ba0303800942d000480b640441b460240620a070310180c03007004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 778232553 1250 778231303 778231313
    0xf0f0301020315030106092c0a052d16170709060305030301060f0f090e041a0c0306011407050c01180e01150f020109020a140a180902180408090d0f 65
    0x110b000c3c181800340c1c8000442900101170075038034039030080c003102414801802c40e400703800200f050700c1011222105041c05248440a80f40c40da940b44040c01600c644180400c0b01030059488850b82030920942c11080c0100e00211350340d69020582c0891000c0c0c0f8070b1404c000c102070380c103007480f001000a42034075038542d591904c7c501901d0b226002500d00f9000080100001900321508841408081c01c040000c2488041d01030400c9480f4483c000b01e07244960300103000c10440e07840349160300c200030103184290b003000f5040b025940c00c120354250201e240d900c80c07450708080175010307240050350080050034403440c020011030b000e940c0e028881c0511a800760380460941c00741e1004601030711441c40190300a400b0f40400070700c080d1846da070030415a450811449c0140c0c594410443c191411a095102146000404200c0c001203603488500c006c400e03100500c0c500501d6400c0400043d00072aa07980d000c040c280b010300d135540410341740149085c10401c1034440c2c9060a0000c010701a0082d4281c1c8030200d269210 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 778233803 1250 778232553 778232557
    0x3110f0408100e0a0f0204181a04050714061b01060f0b070210030e0604030309230609070603051608040201120c050921030d0f02210708010605090a050f0f030102 71
    0x101d40c40710b4000040782e1000814911404844155501c010300c0c01e507407a611102c20040d001c080c040d00a40d00c8403140c00e50321107007a40c0c0804599000b8040d00048106144510b03081e2405d07078040b540ca0259010009044410820208483c03600810300c0b4a04000180110b00c0114840340c54030044d501c8400004110b18011060001070001208007591003034030b1300c100600120600400b40515103081d400041c40c000010741c0b80d070f003c3d40c982400540b81c1c201c1d050060140c0383e05205011880f03400b11035580c80c03501c013061060245010f0780072550425221172081e000d0754012105001444495560100310501c9441c1c103a030061f0043c1410721504000002240036524000c00303c6002c030b140058141400e0030404200b400c801004000d4101031070a100f1029220b110f082c0d220b100003030719014850300800141e8110b4212a0f00700750402ea1810342101035040e40c1d517040f501540070802c81000007800b580074504541410400402d81c001d014100720030041d001103607144e5035130030614015200803103417400d00c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 778235053 1250 778233803 778233809
    0xb0612060a0506040816050a032003010f0204081f0209030303131b090212090a110d03030608060a0905100e0d141306120e03160f0213060e0f151003110f04 68
    0x20203807000b010b03c10444006c0341c0e42a406540501c801520401c081307108981e079100550400000c280c1d006c462500000d0142001065020b059440007600203204000060404d09540502d480300716904250607a520403801210121505504200b00040140104210440c4054418404a81e2104039084841c02c840701c2900a68541580003400010740300c3c0500c5095440001c240003801c03050b07507039518401404481c0c0900c901400c01c0d20450301c101406500507034080d00111080f6901860410b4040010b03012310a403d44550141960780745101505005046680200724001d040c1903845603c211781105c0711044603061000103009018500402a60301401003041d6900c0740002c3c8544420542100c007500406d0036240c1c401c0000940d0a403584041c20349840d040005506420380324008112507182403400740d400c1c2c41c640040800d4040380b0582d4036026043c121003c04044e130710440340101c10b00c40039124651201e9180c1c0030408151003604024002141c0741010790400c82030700301092041c0c100360 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 778236303 1250 778235053 778235069
    0x619050c0f160e0415020a031d06062b11011b03031d0304180c0507050f01050f1503030919050a1205010c020c0d03051e04120c05040b0612060a050604 66
    0x1100c1c450350041c0c07003040401520940e00408001c0c1040c2d80d0310179441607903035142c030502500461511341e5a03010380c1c46141c445029503900c00310070121280807a00c0742001c985042c451300c0c0c24840214042942404603086000100546d40c800c00941c55101155200c020240c4c10803407060040000507454101014403903100b0381700454041c1216154581c040301411102010760310521082040c0c00440400c0320000c0c01c41d010002e5085000c1c881121207100342c15000d445031140c0c03101c1e0654844150303c850310a002800707003000292580858401040b1030a04410b905900034040d0070070503d40080007040d40b80c0c010030b40842c0e0680ea80b020645c100d5a036400384200043c1c5480300c005110080c02804040a020b20103480f660100c0030004007410a0340e1805420800c0200340d040382004207100101e2142c4280034025107540c2c1d2071407581086003400b0001c58400d03116880000c0c050401e40141d040e1380303c00070035280c10108050040d8103c1a0002d22a5510074500b8070000340545640d0001d0028088103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 778237410 1107 778236303 778236313
    0x10516140304081c02070e01062006070e040b19032910150806030304170c0604080c120a0201020a080304060e010510050109080c0619050c0f 62
    0x10344014503010700c800940880c2c000d0002907110041328100415185280c41134008907107982140c840c511240340726000611a1900401c0420503503450000340031043d0f04110109494450155070041c00700303040010380c84650816026441111030280e4900228801035018124146000e100203006019070b021907501002030b403034a5110021100b0130640303060034110003412403810385120351513800310490030a0350458003030008580b04110090145040900d0007501700e00080d12180200c401d030041c1caaa201107540c40300050405803c2d910020041c2154050601030240046860680c07641e000002500050381d001981c19000d6038802c56035901d90310b5a142c010050139106c0f4210081c2d50820042120580500d44260220b030026a211b412486d0317140c0c81543ca13175042002540d0080c80c10403021107a40b2624426038440390f01840c1880ca002003460100d4145a1041540891034000c = true := by decide +kernel

theorem cover : BRFrame.Cov 778057553 778237410 := by
  have h0 := BRFrame.cov_init 778057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 778057553 ≤ n) (h2 : n < 778237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
