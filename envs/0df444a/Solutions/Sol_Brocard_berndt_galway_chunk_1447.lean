-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1447
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:02:03.15041+00:00
-- url     : https://prove2.me/submissions/8daa76fd-b891-4492-8781-e0a8ec23eea6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 260071942 ≤ n < 260251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 260073192 1250 260071942 260071949
    0x3031d07090e0c0405101e03111915030e01050c0c1e160e04051203070e09060a0807060905100207030816170403200924030f0d081906 59
    0x1540540c4040c86036842560100703580030702d100c04440d040001c180200c0d042c2e038030803121150070403d803920810420755601c2c11000340012021001d0303c800d00310750301d01592458544029000d00104c0030880303800751a1444940203031240c07079100d25650040303030740090240902404000080d402c0402240400d540d030401e60303c544000e1005810001e1101011001950030034411050300c4c452800140c3c6080f880c940502c000d0021030900a0980c60541440e0f0701c0d00c01c402c41200225070080003009402c41d4090002485c01038110340326442c0e40c0342c210005a03107401980180b50240245030300010000d4201503086d00700d44050794003289110701c03031400ba13813210141d11024105080411800ea600c190300012010303404e100f6414085001040c0b8004030007074005400465501180c0804c891800b4440c50517600030710004c40e0540da481c030780202c40151105402d4402a28034400071740d07180050380c040c0000350041c400c0004469100540f2040200002d00c282c504d0810301051080c0d2400d0b0030524001c25099 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 260074442 1250 260073192 260073251
    0x414070905070c080c1527030f030105090a1409010b0f0603040201051c060308040f1e29090303031609090509190305070b0c0a030e1b060c03041508040303 68
    0x100201c0b92a40c054543c00310701400101d016104480e00030403054001c0d01e0040c0c0b0000440c002c1740418801c0e00000207107d0900c4105684140200001c091004048a05482054030b405155031540c502d8100503045e50f10036024552048000c0010100b015403008580c200200c50300741e03007115183d081c04080d200950b030103400a00200410a04140b42e1a00d03140e1228a600000808031350b2600c80151a400c1a0401610040c62000810400c586603200c480250a083d911b0aa118601041040004008100d030303515500000d41c1d00b00300c420310300140c989400000c0d050302d6036403800d500d01c109144125034a076400300b42021408a036194907881403910404800d001801220740b5203980d00340c80055070500b201000801c011010005040140c01c2d40505030310700f091a01c0310400500075040c3c640648030310309543d00480e43c0030001c60b8981084104107100780c40c0305a842e61940d890700d00314412604020350260350302000481e0b5a5019840620030b90095904001c0d0700300c00502c00c20300c45101c11305041da = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 260075692 1250 260074442 260074457
    0x213060912020f120706020a0606150c1101120e100c2c0f1306090b0105070f08160f0503030405060a0603030f0e01180608040515060123040b03041407090507 69
    0x509040360b403c50994002030040901901e280141c514007041900300100680200785000d0400030781d4002c3d0400341910f0014803000c017a00c480e004001514078100580070b40c1c080280c0f4409a4000d140010380d28503240740901400c00314001e025030b210601e0b44010b00c12407521007650591441040c851540c14191000e00710303800b414400034015091200d000a43c40b1081c02580301c01c0395a06081102030300410324000c160310386803010040840d520390f800075051003403c0010000140550383c41940142e480100a0b4464410107001416a4200c1360014101c0e45200c1084c400c1c0600000031314801e82c45501150101d070f46410060b03084c0c4d0004d110060105a80b203c100d02c8603030240c80164603800042c500810450080f0600d9603140700c1c55400000800c08203c240803c0c00001e01c00c0e4030754420a00841c0c1200d00b0000002803140d5984045403803107002c1c6c43d5002400c103219200311002026524005501c80c10039003040b05541c600c60905d8405485040b800199850a50040c588a59500d440b0300340e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 260076942 1250 260075692 260075729
    0x5040837020d061109090f0a0b03030a05070b0907030203030c0304080d03091709130609060302120706021c020c10080708091204060f09090606050408100623010e040f02130609 77
    0x4e840300070001103001d0024809064284ca6600009200700f106102c255524100760400c0401c40341c08481c00c5010b0b80041106a1010382c114080780c030001c2e444000b040603692140c202508003001030304000e42c5400f00040c030034100000000030b0000d50300e02200341c07015288115420f404a4060380001000c082001440c1181d400c1c0c02d402034408032801900480728403104402610464800d03410203458155500c40c1481541407048142c054156080b00810364035040c14800703565030348801c50f807010b541000080c080000d8420b010b0f1542e030f03840140181c05000144180a00032210444012000035084000142030340000241d604540e01410381c42d919041c18254121120104001c448003801007035080000c0c61001d074441c0074004c2903951b8807140c856080c00140d908083c503118503044183d007442000d002203a1034441071070703921410b6800b500c0301e81b1107000107994004003c040158414a803070040d13a8090040d4000709000004407000102094031080e0079100c100280c0104406548042c4c41e21 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 260078192 1250 260076942 260076953
    0x807050a060e0301020912060a0c0e060313020604080a08030711160b1312060207030e090108060f0601120509060403090609060212030c130605070303060504092105040837020d 77
    0x90060780b101400241c40d001c0e81402140010840101408981c0c0c8034204220440c459032080e9202c62031140751078206110560000b818600000d400301d82d80b98142d0b1032240466481c541120700070138001c0d05954140185082403495500201c3d80300d4080740b80c1c0c01442d860000040b0744007081003581a900c405c89800c203030454042d600264031804840031447d1011030034511109400300d00360320884000da6940d03210718004040405c0c0403070441c01482d05100601c40580b000c2103456000322050079a13080340d540d20004980c044040d2826420305031810b4280900124046801d5104501075100c45400b03507919201160549940d124190068100c02c0c0c0c0b280c0c500005000650b04100500c0b10107041071081c0b0400c20201009134072030710210360009490403c05415016800060500b15810000d409045d1030300440614126003400944151b000c59030f00f0140a10103403400b40643c0800c403204050540c080039003c40084204660300f101c1e150800702c0001207a403180c60300c281d015101c1e0610700c4265403038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 260079442 1250 260078192 260078207
    0x706180206070b1b0408061006050306031c0e060a080912032205070305071d011a030105120f071205120306060f1602060307030203160903020102120a020a1502130807050a06 76
    0xc13482031444041c02041912882d4050405040c83c02d026003054200a00c6140c10052294018010f00409004111842e40c2c0801c20308616a000c1c05903500804000b1001c40d9800d0b211549664002130100e040760680384e000d1a1580b181608900721a6541d0441c00454600d0002b180c03840300c42200258596215105043d860452030301c034100310341c4000d03101d549190810300c06401103000c8103ca200300005230540c0705821130040c0500030304031203040c2305101111001c0c401409014000c03045401c2c0410101c20400c00156a507448070240d919454503000c0c102c030291135408041e0b9841c4504c0c0301c221460040001142d01459008044615242441050a445070002c00c180c0702d51814038056500962900001588110203d0740c0c0140c2e04e1034100b0105c00c40b501c0da894403c0030420401d4043c80180d80028040140e40100900d0b01d8640c821004100d1405482440040c00304d601040054102e81c400d40240c640440d410f07403440340460320b50b0b0764995518840c0c070a141c2d00240c50f66041085a005845 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 260080692 1250 260079442 260079451
    0x405040e0a0b13031b0602190f230c012d02040e060909030c1912050c1f0f0e0f011d0703080a0e06070507030606060302070309150201020412080706180206070b 70
    0xb001c05d04e21020ba045c010802d00001000c0d00e00c15000150074480740302c824500504e00c5420300b0030890b00203804200030050b1551400000c0480c240500f801c450382076680c1960441a2910b00a100d41044c12007844031143d0350401c0b102c41c018080280c101004c0a0380299425a5001e04010f9080d0380c80c2000c00044442c05065030445000c02c0008511107101809000b8481000340070300c14a880b050b20306603150003070103000d01041000a01003131030021004030b14108013400c17484608034502d8400702d0f080c0c010881a10000d54591620480901c850008a403600b89030788603a00030001d9011500c1c2c48248282c403014082160f8210310f00900014501901816070140e03d440d0000d010309400c8080744459000f034a040d2029031002d8401c104010890040e280a00f94514040d4100841580e0240c034030358482c0203c4e003003000c0080022070014400d6054030010035464480b080c1da2401810280d007540c1c003000081d43c0550030301a00344200c0e030300e11346039000d05c50b4041c1a0318030b85840764940b03005450b805030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 260081942 1250 260080692 260080697
    0x302090d2310050f0105010f0f0309020a09090c0905011215050c1908160e0102030921030403080d060501030203010b2205031213080a03210b0a03080405040e0a0b1303 73
    0x20300d941d160300801c01c0c09595035a103040050f550911400c41441c3c4041603000c2810050002c01c0d1610595010301904511801820042600d034641c0c800580005c2e0355402c01382d8024544290ba000b8070680b50002d901700d80c0031480422650740c03581c124032040051004007628113401030100d1955468154803c0341d01c8490042c44604002400c4c130a034105e280001031400001e0400002d00510100c1c4105012846144d41402d81c490007030030340042d443c1e018129950388940b82030400c03030343c0e00342c1007649181481c0c40c80d0b0140e80d669510780ca05030b58690080302140c8032291601c4070100f119402482100c2c1030307400029180e420400c4d03043c01000d44080c0016030070640e15004100081d40e44040281280c4804240300a6444025200e0036020800e030552100c0042d40c030942610021940018a10312001c009481c88014081d00c50052400340088504950700455240000418060507002800580d032f011901407100e80084804942e45011081000c1d00b20f0305400081240c3c01910032413440154460b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 260083192 1250 260081942 260081993
    0x102090a030b150604030b0106030b040b241c06031a0402090a27030f02100b0d0f03050f0d0212010e07080f1009091a0903070b070305060d0f14010501060302090d 71
    0xf10205049400551003282d901c14004014468103406008210302d42c01c09a0301003004048603000580390701e86650080c02d296000c401e8034402c0013054400c03120403460850360921103460340781010b002084a88010f60b800b122940010300050b06c08640389011360340040207854a40c0701e4080b480028054800c00032071007030700c00a4524001001c040c01d441150702940718019022010303807000c4d08241e04120151001d5140c04c2e0303c5100341e036585503401e0f200b5400c010008107107955480e007036807540305800c0008500d61010600f4a5804d082d90002d1015000382c441940044c0d80e0748818404402003a40c1160200b10a60b0001d640400c0c00c045103580500d03100e80d8039400c0750342c4001c3d60040306d5202209584400701481c02a031100224140c1c0c2c0c1d0001502e00c0218901f0115880380c414601018059000f01610b80700490034564844154031072040c1c0210203506260700c04c0c5001400c145842200480c0b03542400000034083c0e01078400d48504c1d24000c1c1c506140c003607080d500c80c0d8807005080e100441170000c0c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 260084442 1250 260083192 260083231
    0x1403070302162d02060f0702040624031d06060f06090a0f030c0b030f07030c090b0c030a032405060702031608030403150b010903110307180c110102090a030b 69
    0x240b4050400c06000300c03008003000c5440e000d401c10b0f00d200103040024041d101c0d8403400c0180c84400c21280e014050740c0c0240c0c0c07100c08074400100507010035803141818240c01510f1a01441c1041114480c2c040700d41c87c20414140c01c0003074010710300300e0141d0032071a80d0000e00008405041000d04071503260001000b0600c0e254034800002e5111501d5000001700c91354000052080000660f0080003030080000c202d411480c0011031310034040c8004141c98101600c603a00c25a116001d19200702c09450790b820041d84a19108520a031f4a811034001000080c5c10400c118007081107610002402c2031103809400b180d1400d1406100881d4000c1d40100d80520036440d040c0e48011104012401420340a00071315969803941c140030180c0807070342c1880c164861401c103440807160b0b044030409044a61054020b008213810781c1c002030400070980c1c0545811020041580b602c201c55a110031009211a22220280000c19110a081b07000d015142c0d500940e03601c0301030001c0380c40b21040c150f0015944c50061100c190 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 260085692 1250 260084442 260084467
    0x604090b01050613090615110703081b011811010e010804030203040b0f091e090c130512030c060903091207081e0709060306090201030c0c050a150b060705070302120604031403070302 80
    0x217681c0071f142c0c0d840201d140505682e510100c5a256a10318200800a00d403e42d19112958850140542140440c0c18401c000e03515080d00800c911080000a91110030554203107901d544202c059010f00150002c6511259580219043c80c01150036500460070f180c14804001c0455000680c444824001070020b801c145e84e0703196440360840c440d0121f101c400e02c0d40d04144244154040c0500740250380a014403105811100c0000782242c00c11a0340084a0388646c40c1c00d13042d0b11800301c40000da4024003082210154002004204c42d903026500481943c407898070030350311114503000318141500646c1c07031300000941455456141c1c0f03100380195148295143e001c4412100d41d688211242521000310106540c0c040c030419400c000541441e101c000082d660b502d4840080d500001c11000700c0500d14080d1203180c1d40680883c03c4080c09056580b02903083c4942e4038011440f00301c1c0300350100c40654440701c0300801c545001b1030307268540c88140c990352140384519800050543e0105139003400000741004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 260086942 1250 260085692 260085701
    0x161112061302041d0307062d0506030606010f0c0803041a0405010c030c08012402011104080f060108030a080f04030c02041407090801060b0a08040f1a0f0604090b0105061309 76
    0x45541c0040d030790a200510601c8155206114108201300488211400001010040721541d650040700016682c80d08614480713440c94000b602c44a88180c82100300c1c03544a5507001e18003804040301211b0090342c5100045072000500f26104000442181c5031400080e5000040d44d040b5100b440c1220881c440e1500004c600e500448066410760f44030240064282e406101da98000704003864405900d41c1041c0001404c48070b107143d034849007030011031386a141c030b1701c02c2d0710a00d0641e5030b00c0300640d640c075a5140e00d2a914140351210700024042c02e800010100d000100300c4082242039150001207540c0c443c0c0c0c0003001103008006805001c11400c1150044e43c440c42030510802e040519000c050a02c0000140303045c42c103400030441d5030f142840c24071a4034486000e5840c840094940004903542d58680a6030302c0c03605000007002400c901505c80000c5010388881449000c0e421051310503a6181810401918030189002e060352004a0041c0b1050520100519400e0401c00a00544a9803070101c201100d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 260088192 1250 260086942 260086951
    0x20a0503011103040c050d0c290c0c03120a140c070506030a2c030d0b03010204080304170d05090904020906011b030e03071e0b0703020f0703062016111206 68
    0xb07660002c100010001c1080c012006000d080d6420f41d20203580703a803940200142c074090361a20080f0030080300520000d0801d04c1060300c003001c801e41c0e124095003030340d5640c7da000c0e2203103036101e401146505d1541080040c19222541c840360b44100040c6e0f40190442501d40c04141c05001e039010b51000412980c1300e9000031401201643c038006102d0800911440d050a081240c0c00d10709840b0584e8004048000025a0246030060000007040f0380c04900081c02072140758400d06403400080384c0081c41500e040181004c90401006540e0584600c06049030b65105419220354040025400304002d030802e0881c26900420606020316540c1216400244144410340c00306c0c000b68406180608505041c8080b000814401707086200400c04030078141c2000c5494028541d016002240e202d091501c00c01c80b88500701015825201074548900f07040010308000345640d20a1504920301079841c07148041110000e40100c10f400d400c0050759950001c441c10b0031014513034080d00d000d4003107030400e10602c25140507 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 260089442 1250 260088192 260088221
    0x30210021c2003120f130b1003051e0a030e210a02030c040b03100b28150504060c020d03030f02040b0c010c0905031b03120c060712020c030f07020a050301 68
    0xc00c00c08281c102d01c0940d103400c100300305400920810b504150030321341060b0050501e200c07400343c83d5035841e184d0950012841024010041c40402d0112542c0c0018001c01968040d005440c840d20078200500c1441500c0609032003190300824103000441d02c500295400e2541c01089915141c0d481c0742e80401041fa50304031004a41c01040f40c600c1185000c20089280c50700a0f40d0621410309448002600c4d450380d08000e40000c1e440303d1400d00296144241d229103017246041141c9101050080d11240ca5158050307c095000482240401e184c0554151002c50b0240c1e65071403c104029402c0c400e0031180c0940450925896407900703e02d0441c0c42c0090005069003001460311014501c00e8a82540c0d04010ba440078004500b0041c0700b280c4002c560a2505080401441080d210380f40101b841c2c282201e01c0d03604041000b2650700346110000c180030b406560550340d243d06803145032240404074403039031401c901d080d481001002066500391014003030541c0020401c0820f1640d85001c80e007940e6607100103801 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 260090692 1250 260089442 260089457
    0x30c06020d1b080106021609020304020a0e07020604030f05090627031e01060b040807060807050910080402310902210102070c080a02090f0421020d0f080907030210021c 74
    0x1071140e0203c0c02c0707401008039200411680450700503000b04580280202d4541d20b80000000c2d05548880368070100030310070750300604014644010001e442d00c0007501c044002030200c41c100c0710f44034401c1058507018540201014905843c0040300d070243c1d6229a03407001c3c80c00880e9110300640d5000c0c0103c10340c505017840c0c421070700c01c92040b0442c00c4654541060440750001d1200307106045c0300280d500140d901c1070420092030740f12810140e800d030040c00381c83c95101c200b800c179204095510541ca42d020b1403090700e0300d080c12300d00321a800c03d2020340d0400c0d55020070442c15107510000da664121403001030010f04604496917045103075640e20001c0791000c6041369000920340c0704111000400c42d008003024806000800350690000d411100047c00b09541c458403140802c0074000d44034294000d813591a00c0c1e045000007400d0010791164500c150250209201750503581d2000d0040500d148500c070880c0190100c40d055508101d04107500d0412841184201d800c804002c9940c13540081455400340c80b00342 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 260091942 1250 260090692 260090741
    0xf060a050703060603060b0403080307230a1b02090f10031a160207030b0a1e09061b090311060f07050303010e090c0114030a0911040c12051003080403030c06020d 71
    0x107043d60b0b0301d50f01c014105803602d0010000103035600d06440950f80d03c20401c0f56281c903080011030b0071005c030300e0351004c0d4084103c1503c2400354031700008140181c01178a460400760318100c3c00d100040344603013010750401c04d0400025521203c2e01c4249500c2204c05003011580e40c0c0b69240c0864140741c0c0c4c00b0704011900f9541c00c2c41046005041103461140d020b20081403954256610f0501c00c03a0082c110015041d15503e100c02ea4510012020180000c0390208000c03001140c02c10001611601c0114940c00e4061501c012250b403150300301d40c1c266501f018011091800d01803e00c0307400d900c4403540c8202e80c0014010500022811310080d8000c0401e070f00f0110b241c0c103240c2c48060030180341c50f40c4e26040c80501c005102560010300701762503200e104e606e00080d80c081c042c101030a02d26a802903040e0301a140000c40c806207500701c1034159941e2000e00d42003140b540d5030010071404c17404078000904258002d100401c00284250800e0088620841c0058100320000303051078166107110a04144080d929038209 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 260093192 1250 260091942 260091947
    0x40602041a031509090a0809061903090201030f11390d110703111210020d09140c0d150207020a0f0305011401050a0506090a030c0902040806070503090613050f060a0507 74
    0xc00080200301c03100307580c40c204011700c0c95483d45c1121000f031450802142d03250032a5220000d56401d514130000c0f02c0fa890040039402401000303240400c0340402c0c40d1030003201d03103c01c9620a03200d80e102d240c0c00907071420281c07445007400840403460b9444a4220f050780d06c03841000034058054000122402020303051081580648400b40c507042042050784450020000324181c0d54403501c149500f943c0c3c4041d01d41d00b07450494102603107545040b82031400000e0041c1480c1040c0e02ca00b02260080320803008a80c3c00205080c2ca400341012141d50102e00b80c404540451724100c0140d82c0e94190040c01464007003a68007207000d900043d8818582c02048013020010320400f070056003161150340c03486242c0d80d81001c00040350a000344c0162401240003203454207603a00c031404120055604040408811a915114240654880e015021045c0121004a07010798050800d0301c0c000e00500c0058007407540d80c2807584000341000002501c55200e8982900032000341813180134090440350002003a14949807002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 260094442 1250 260093192 260093221
    0x2031606231b03060a06140d0603380c0a200114070e011e03091703150105130501080a0f0f1406030a0c1a0f040807090612110405040602041a03 63
    0x36010b820204108016842c1d40e100404810b503031040c00c00c448000e4021229049034003c0c9216085107034500714020003032201e001070100f011041c0c00071704040090141c80502e41401d003018800d01c0c481c41c88000c907110880000241c0030004452504024403000e4801902c000400c1d41c0713915680341d54906058041c46880e0f40c1080c0d1115540c100001b642c90030000081131081c10100f51301000c000030600c901002d01c2174000d05000c98200c0d044074288100c5040c83c40c0c03582c2c001d071061030707088000740c0d02020507502a40c00d0700c44e0123030302c81c800c61215031a2000540701c407007000305081d003401c0c2d41d21114290300301e0f14131603901c02c82c0d202180001e94114284151b0713610a13000c0d200360b20940c42900f40c28000b80c038a100f214160703440c6004040410b0300c11044009107005001000c0d990040110740400c005800107400c50480f8011002440b15a1383c40038803100f00c1c41102009041e20411540070b60703590519422564100c0c4c8100c400501e07069440300107000c0400e040a0f2a001c2d041d002052140f042200ca64 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 260095692 1250 260094442 260094481
    0xf0201110c030307120e0a0302150f0f010e07051b0c01090f05130228050d060603020f0a0e010c020603100f150804020d0c05091303120c0203160623 65
    0x480d980340404044005650b030000401010070055804032a16007000035822403001c04005800701d0784811214039003e516600b40050b0320480165000006480075600c81c0040c0c055a0850361042e41c036400c0102100d03040d03100825010521408200f030340c1500039080440401030608101804441d250200014210990795201c0741031203100c5c213001d000c00d6450341d00b0307074484403540d100040e40c800c29518030001c0f900b00e40880500e4003040c4100c108103503800c54001d0241401c000f00c1045a80c1d00d0b14004e60481c0680b00b41c0518880c001d1100494240c02101e203c01c0305141410300c07245803921036001a0390b5034800c030341e10118480090010008403451760304441c05420008210108001007150041074148010400380c800c102203807403081402030050011024110103042c107071107450102402c0f02c1c01150f9400890014000009503c0800032600c01d41d90103041d01c0d07000d50300e092220000b0443e0319510580c141d034180c0da9035191184611041445080c058200740010010349094101a0080b41c0300c0301 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 260096942 1250 260095692 260095721
    0x310021209011b120603060903051210080c0d03230d0e010e0a06020f0706061508070c21050f03010305010e0c090f1303050c0109030e04150501140901030902030a030f0201 75
    0xb0000f07155109500c201201424035111514407503112140010340420303440603000b280fa006040c0b003819408402411040880c00c504d0f005502d4800c003085804100344103403040da4002d83c0d8000d18915015440d48403050081c07074941c00043c0d8400c03070303000c1ca0044404c0615100400041032070040c28940960400c2100b003100820850341e44480b030640711003078a0300040c20181e00181050a8020440560360060340058003081312580703601c504031b00d0680d0601007002140d0301c0000900c504c1c4c8a03400320b1542c00d030720a00030481005407684034200e42c00785006140901800b40081c0340082c0c072000145000354095000400c00c10f0070103540605010305110f40c28002e21107003041009ca201c8441e003040d0003001d41190410940c089041c1182c1c0c60044003c0700b01c00d23500f0002900103155000034680c0480710121001c202d42c101646c004408918103201c1d13203022800001030b078020708140d84041d04c1004418100070810169580c0082d041591200c41180852202c8180c80704650342441002038024804 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 260098192 1250 260096942 260096951
    0x1b060809030f030115050403050a0f020f0a050f13020405040e0a02121203180a120e0901090b1305040218040b040303050c030c090d2a06031a0d0b070e031002120901 72
    0x1d0350142c01c00e00c01401a480d051640c41000c14265128004850007586c00105485074100240303840ca9040d81d1780182607203d400010160300441c03400036144821120001c03e5580c0e40c076481c1040c0320306040249003600c0c12645c2400300240c0c0b134440c0d01a0600c0c000320503010b4284410b2501c104005070902130091030051f440000d615081307139a060122030704450000041354000042c0440d4520700f11070750b0802000009032044511802d904082402e0194204540082040ea2548084030465102001d1203034041d6901c90701c0c1110166a5000c039801c203001030b240140c842486000314202600540c1c0491304103110394108000d140c0c0c10720541c0d0b040039a2009492a50078105090042c60080c1903d40348100e800c00001c40c02c00200300071004c0c1450031b4800c403085001c504448030b007040f001c511604d1f001ca030400846044103d4080d80036070a517100189000800351032034075010641d003c01041e10051113040e40e08840036540400450046603140d81d00582d41c1c05c04410b400118050241c013210300da80c1031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 260099442 1250 260098192 260098207
    0xb0415060921110909160e1603050601140711040207030503040c0e070203070b071e030b01030b04060509130c081204050f01050313170715060509010605030108281b06080903 76
    0x1100c0710301d010501101c40280940781c5c1040541010176101c0042c100e028041000180c4180e40a901c0740700c2c0c8420400d098022122442c240e064030000c40e007040c00613191100701e14840d0115805810b110703000d081800d00080c880e0012400b260300041080d000b080c40070040000700011a040341002e40396510010602e82030028010313503039006258004010b0304a00d40040c4c0e410f807003443c11000c4140359007940183c0c200700d400c001d0010b02c16500910300003418003040c1e0361182011f00640342201c10184c0300e00002e07a02c2840c03918241e1f0074000100c03000c802484000a003000c082210410b00561404415641d51910007004840103071100d8050522400380f04010301e00c03030303602012049650805182c12084200d101040924480c045005106200b4440d0041a880c07143c0e02030011f0700c10603100c03601c03d82d0700c030302066841d40001d201707080495100d41111010030940c19075003034040c1c0c01c200098040340e246545506415000a0900780d1602c2d1248080104960200000e500a145200503600c0d210340d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 260100692 1250 260099442 260099453
    0x10170c0d050a060e0c0c0a08030402040e0115050a21060c03020403020a0306050a05060a03050a02040903022d1b0d060f0204030204020412060f0c051206180c0c0706030b130b0415060921 81
    0x447d40d202800385000440010b05645413908520020185030008101c03054010390030024182c440d000e4030b07000e44a01e00021034103161216454281c118803d4004191142c05e60b03490000c7d10f015030003401015000c0c400000141c40e1419001d010310b02c00c48000c52140f40c00068281140d0004043c43c2c0304038480ca000300b020401c04101042d8603901694080b8070481035050591500c000041c0410801690b0365240040c4040c40c50807814401e000003c0d520354911041c0c89140b5584101803441d40540039800c6000040c1d001e07070020590035005039000d4102562500020300304e80040d403000e101011611104403c0200602c101100034049010030014002d140c0002005401400140d0600402010105100342c1e5a01d04411800d101901603d0346c40c41c100c0075014058021501111240c400d4001c04502c02c0d00034002c01c1002ca0f8080d040028000d00421060003529203200c0958001e5510074244000c0504104e00350054485910341031211464040740f00403209903108180c441d80f4134181c0380000180c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 260101942 1250 260100692 260100703
    0x80a290601051317030a0e0a0602060601110c090a020a08090a0b060f03010902060a02210f070b1f0608010503100e06040f0212060f01030c0510170c0d050a060e0c0c 72
    0x4081c81d040b51111404072008060f9100b03900188509851080411003030100000107041c2200117541e62128031150005015108066020301d40c0940c0015000443d154400e05185151000300022201d8052240012a000040c280c560b061141d40014041803100e0700300d000e0680000c1e558004200c1d54109440706c10030b0000107018180f18502c8900c401c21642da00750000c04035650003c1010355516440000030f5910001c1168070074118240e4000d04c4510116601690380000106540603c1c00d0820350314404100f81c024078001c60110802c0c51185080402d8076400064030301d903100c00750313039506201c2054038103134000c14641c800504020700e881c1121804180c0725081548003803100c503207004c46e03c0061180d2829015001a41c49a0000c0080c1012842c0209040320301814000100c15141e1007030018800c00040180042b03800603c42070100010303108603e90051504442c11304061420390460192081550054041921110140243c02c000340740150891f10b01200780d032515004880c401e40780c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 260103192 1250 260101942 260101951
    0x300711070b0901020f100203060301110705100c09080a0c090e4b0307020406050d0203030306190b0d0f0e0a020112022203050a11040b1c05070807080a29 67
    0x1c0105031042564000c0012212a24044007981c64030f4641418aa00941045403418402d608100019480c000c0c03003001c8071810f94014000d4006080e89000c0380018110707030b028050401c2003281c000252900b0070f000305c040140c07143d100400446d14051000d000d0300e0b4102d050f40701d40d4214208a203440c0c0c189a540b0001c00f2072002e40b480002698840d000c3c00d000004034065106001d48251444044010000304011407007217504015658440c8144040a110300c40020340507030007000400c0701c51506003d200792000c0ca0700024038290352960074607001b940100d00b5211049840d2200404180c0c454051210032121003c0280b00030f900d50740000701402c503504450340c141540009d41c0c0c2202607880c442d184180c510113100c00360259407480c0599542e0f62240003500e000200e51080d0300c0c18545070083d2010003078010a0340d089044400134580c3d0036194640212081d00c03034101c00243e40d10060000c02d000b0314082020704401030090030715280d2441400c0b03204c1102c4504c00a20303c0c0f12526140f160303410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 260104442 1250 260103192 260103209
    0x8011a010809070b0301061e0507020a171f0903030e0303040803241804060f29030f010f05070219050d050f0706050f01060e061201030605060630071107 67
    0x250311424842ca007041d0311600545000d180000001c128203802515540c48441d01d622445075441589004a03468012088029070201d51002c2c20001d85000307000d500c1d4941683c1082d100990000704c00340090b514202154900561180300500c1803642510034030901000d050040c614500d01503030b40000e5884002c2906100d201c2d0314a80b202c10681c650096190204050588108050710110440003d8821182140e05074280f500c0d00f201c00c4a94000c809903041c42407021802440c07214005a65031000d00c0a0941501c0b0740382100301000c2c2c0900541102d05104030000541d41000e0300000d0500c03e089408000742800d2015220001308005002041211a450103a49401d0700f01d00c59903480c0f080307002c00303450360b41440c1c1030007481300341009200c1c101d4a4940b184c2522041700d5040c44000c0c0182800046581580c100401c08107038283c200a074000801060395140c8242c6e422414482652542c2c2015108a20709000240c60404004503400c401c1c1414642059103010040d83e41c0c52140d401440e05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 260105692 1250 260104442 260104457
    0x6030a0807140a240b030a020f060d06120303050601170103030c080403050a050d02011508060c03040c080f010c0323180327030705010c050304060e0a0302090103060e01050108011a01 80
    0x1c2c01281c40034030050b030702400280d81c10320707180303041c0024020500d48820308580c3c2403a400c0c1e60522800d01c5031a0000301e025001c0c00c00d0b083c2d40e8080003030302080c2c03141d802d400040c10813823072808a00c1885258060303c00c0110505480031203040013400c4440082049040c0701082d0300c503100814035607010724110380d030524003669001024540700005024540c002411441501a03200400c000840c0302c0b882c80c111a03008002401c000e2407540880b0364103100340780c03c0f80c0104000c104589499070007036500070700030400503001d0b42c2da0b00c07009440e169041c41d41c120035940d10400d00f4407161303041c0621020070407a5410007000740c80915460709140b0f00a0b00f039000c814600002d1608000052080c0c0b0750b03140c4081202050b10842c001c42d86440603002ca806846402161804141980698200d80c040747e000401903003480c1c149001614113a403c2c61a695010541c0b0070000010f036140b41103a40a98803510b0040ba208244030541d5003910b9046e00146400e07414413125004415240090b5074104209103062007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 260106942 1250 260105692 260105707
    0x7031e0b150f090306092d03040b120103050c01030b090a02160501020c0d081312080411042945131412040504110c0d0e130506030a08 59
    0x100740c041510511549003401140880035050154094180d03003005805964080d81c0314039415494007981c1076041c104051080d40c03106101c261100d00c21040704c0da00e040781d2400b070f126000a0155007001e01030b260000205001402080014840c4000050003802e003030254000000c0005e8805000403e00e100503036000c03c40c1000c80c0005950108040d400034000c550320100020059215040619840c1c0882d075004082480341324903000000b001e5401c00100d06c065000030b007048585a1020b4410344100d904420744950582da540716080b103804a01400c00c190144004049880e6020f2210361807080c141e00141001045400d4600c540008802c100000300040c00050181190341c03101c400c0300d260725140c04010450b0030545101401d41c0c00381c4039240c824041b49100c19503801c0d01031703840011680b052004000d241405d03081640143c142d080a81e09001540340d45904d042c140f0401e10b800242c649924041c2070030440c0c4181e0110f0b02405050016203884408030780d03208010311009002c14070005010303 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 260108192 1250 260106942 260106949
    0x61e13060207050c1833040b1807020303060109050105130e0714070825030e091314060103060c09030305091504050a03030503090d1b0b0408040918050607031e0b 71
    0x920412001442842e80c04092070443d070030711004562041d006e03044c00a00070941c0b040448041990b400101c40b0070804ea10080a100203040078451403908550752808a402c0340c491203403004c5c0704403041d5004544a00d85540010f050001d030fa030243c0d040c00410811040c0d13040d905148001566019005c58103152181c41c400c44066540180c84118142d01141c40b44c20030400c500205020100c2e064070310314501c1500000b03141c020388a1002000f05038085201c180ea410705818159210030038507210200c94490f9101c94110007245411441582c00c05401407041002c2481801d5100d801440d103501585c0c21590094614456109c170b1600c154040b221616024019030110390141001401068003140d803460003800d5070b04141c4414055001d003600c8020490702c01c1000352602032500d0896910007690f034031884510131014105441e41c050070000400c40c0c10342400b0b80d0881c1498000729400c00c80280c1000c90502d83d011381608105400c3c208221034001c4a01e08510721200f50f00d03000103101c00a80f000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 260109442 1250 260108192 260108203
    0x3100e10060308030402090606041511151302010f11030a05090f060406022413020f0d021e04050c191101021201090608010b0a0501050a050d0908030405061e1306020705 74
    0x5403280301c0c180710010040024a00186014520079950881651510420080700303004a01440f01140c50b8a041e1450003845501015508a220000d98101d81880401c0d070541240480d81740c00507104d4a5414411941d0081601254001130b1604403070180c4900d2043d602c82c8104880441000804680d100d007e5a031003882000c0101c005249070341d00c65594001035224009a08400c0d4996903002d0b202c880fa80803180c4181c45401d090309802968034083d4200040c900e12840000d411984407403a0a00680b00c800004103103c407000c0201301c055444808100546600410071046180c00344204011403c00105051940905062524081080700a09402809028000e2034440003140000402c0c4015a210b4015101100001d2054040c03035418001c82c00d040d8401c050028404201c140103140c41000600009002120040740c032100c00e450b99581500140d40586039078014030b0034440360034082c40300b645060344100817140080c9005e82c043c8081c02d14031038019024030380020b154070410006005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 260110692 1250 260109442 260109463
    0xc09141305010e090708031e0327060117010b03121c050a090611070308061509090a0b030106060f090302091506070302011a03010204050a030807260a030b0105070203100e 75
    0x1400c01c400e6a4902e070380d02003080300b60360301c1c40c0a00800d00d02284068000c811104064044019000014204030040044d5030000709011035009030034071002c40e0760301d41c8909006080b0740b041c014100b81d4100764a405011030b0710703001e03184940e00d080107c40c01a10080791a0605584401d0159140c0c0341c80d0084c8814148014168070384035142001304810300c4040c0d40886030b0640103c2c8200800d0718000007103c424850482c020f00411091400121a454080a8208260b014058980c24011868040380e40c5c16801d50b5001091034071024004110f04092003541c00400e4145806290034201c01806000300000d80400703030245541c1000a00d0b041503902c151508105c024001a43e58101820300900030000702e640000c0780c01d8008001000e6243c1402520107880c0001c0c01e041c1d2091a65843c8542680002c508036200c10110070700340554680f40d40229081800b540c416a03452010940040440d42046c01d898103010045c030010001d600c001541c0c01001c2409100080c2c841c0312900c240b45410388681 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 260111942 1250 260110692 260110729
    0x8070b0703020a0c0609150311031302011b030c061413030c02010201060e0103111008060a050607141203010e060301180803090106030804171006080d4a040c0914 71
    0x40006000b54403c0d02c2c10308480c000c0c051f450f580701c0c3c845022402d40300b61200645c3c0185060000c01e583e0288594144075151050408407103100c1110007550440d140c08405502040640d0b02d250240603640c05907034285210202183d80384d2819054108145444100160802050700401c20469000b540450007030004080c0d162402e696a1401000c0303401c01c0005a03018405100d01c1d9203070745006140780b50207010700400c1000a070b41800705002c019000420142c0b00100c80e0800c600b54500240142d4004020100405a803581000381c1c4190015018205a010381e2422601c011292020180c5084041e400300c40940e498071003110281c0548810b40001d07082c840000b03000980100d403039240c0124072045030b050302c1c3d00c0500031081008613540780c030a8101680150400b00c0e42c0e83e209941c4001075030207a070302000700ca89c0d0b100c440184212441000c1c018a444d0b1802c149520700e04100ca100d408941150b05004411810b08020604002445880c8500104e40c11140d900d698002c1c0302000c076a0b450707 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 260113192 1250 260111942 260111963
    0x1030b0c070f210305160c0f061a100e03030702010e03010f050a020a0f080c042610060905090d120c0210020c10050903030912030a020c25050a08070b0703020a 70
    0x2420b20020540c2d040ca034403807079200101443e0081c98024041c191081d202d0801c90080c10078400c2c026640420031a104a624061012200001900074030400da61440c20a0501c0c4e120300c1d0010600034540004c4400005201d50010b20950383e590010440c2c01c4542d0a02e014000e50740c02c10082405840055407080146082c1020420040859400380c20310500742d5071141040c001e0f030b61064807614002d40717428003042820841409081d414040600300840342c8100d96261a4030303948640d05001a100b41040d041e511844c04214802c050b0280700d4008144001078000403082d00e01c0605103a0041107400203491300c0340c810024041c001d00a42c9c0a00d0300031641903545007012103400740ca5592140c071218419140101160702203500100307032032081d99444014000c0390301c4003227007501c1600300400107182c0c580c080051000d210002d108880d08110910000b060300c0120b444d03144c0e00c494a6400250045501010401014070300040c91011a035003451b5440e41d03183c0d181812414500c07401000b40c00d1403402c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 260114442 1250 260113192 260113223
    0x307320a0302130b01030f0b09040809061b0d080109144c090c080f0402030106051206040c050609030a0803060f0d080c06070806010806010e12010609140c0903030301030b0c07 77
    0x3c54215428840c02640d0030010000c21700411021104c003201c18641010300c19002800103081200100340c140402411181040e0f0b00c0b1055402c00c0103080d4040e0741c00d4124031321023003102760098603490260030411018003140c101341500140c191802006109440382d800d80d4a44841d00400b4000312554504002c018602242c0c00d031680140400000c2c41c2d240000503400081c2c1840500c00c50400030103036a155001c6444422001c1c41207038000c1d0040c2d0f455507850800203001c0e95142142c449c5a211040074141915003410044003401c030b00c2d03115034040c0004000248040c0d4022070b0300c4100d130382d00c00502901d80d103807000481c44034500240d0485d000342d44c1d510308105102c0c40078080c0402c0d6545104407207413691040402c40b100036080c0c0f00d5902058040001c00c0f45903000f040502ca81c0b0801915002d05200b40c00c00b05070070f5441991041410a40d03c07001400e0248407042840c1c0d000c0800e8005510344003240d804240e0b1fa11052002034000c44201002c030380c0010300c03041183c3d100740d000390540c1c5e81b4845 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 260115692 1250 260114442 260114479
    0x30503030a020403030e0a06020a080d020408030a200609060a0c0306080313050310060f050402090414040303061706011503050615040602060f0a150501030e010e19020307320a0302 79
    0x5010a5021609116006d103076803814003000004d444040d070180198007195515200c1b140c02c0120028003083c0c090001150400d4200041c2c0700240d0140e039101d40c902d4180c1d0500c0040d0303010020f0549540c0141c001c103c84058001170940d000240301000241c04031155108900030b0016400001c8280000900100b421502c8a608401e43d0030803025030348409580c07000c100441d1003038490300300e14641d00501002240f41c254040c054080b80644045000c0b07145140c0c180d041c000c11901180401d075075400912000283c0003007050404460401040c441d410310155102102051320740c1e40c00c1603203a000040d5903480342e10f002983c1d8100070303081c1a2655142c00c2c0c00b81d05c0300c00c221800342c0031102e0302000030901c000310f000c0e11000e030400589180d40141400011005030042038810501507480f03014100c10048200001d9420200344504100c1948043c0304160515902c0d0b072104d2943d100c10021071030b035181301e03070340104440207200c008082400c0c0380b20115001000c240d001030341c052a1204803a01211 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 260116942 1250 260115692 260115697
    0xa14030706141920070b04060e0d0519170106020601140103061202100201022115010e03030a031e021c050106020304150c0204060506070507140103020909041b030503030a02 76
    0x10310900c402e21400044480031110600200c61030710b000314a584030520204415800011078400c8103607038401e59541801c606003e54417040b0200c83c00d0108004000c1403000b01d124655a00c18990060080d85040c0c8070001c1042c015425648080d419800c1a20506c80c050f0040d905180502d0304540b1141d070707403000080d448034801d03c2181c40e0450945012038196101303100d2181540e002216012805140b5000e0140050744084003500790740d400c100e0400b1580c40700c9411100081c0241c1d480401d46410207013100c219002c103454a0501091402460036541d003c400c0d00c038014503c3c980003034291814040d20703d40e07105043c214a045480020b00c10b0000d0704045003a0b207000030045090013140d9803118101e0ba00d100d20b2103070200b02580c8040c1251014480d4401601c081e000403c04124203844100241055110003c1110b0f50f51002c24100f0040b002d2b0000202c40150900b000c6007050319000c007154080000800003040c01e0005142c660320005118031003005540c00200301c031344130700e003c404400082d03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 260118192 1250 260116942 260116957
    0xf0b0309010b0d0b010b070c05041d0c090f0117011103250908061b07140a050706030e0a02040c030905060403270305030a0327060209011b02210a1403 66
    0x40d42801c100080e03506003c10314490080d03218116180580c42c1c0b20a04400382c0254200300e8540c80925800a107a0b615400b030b803074000c40c00340e4481c0c42c414002254140352010b0f10b24820300880c1503d04000f120f071000e50f502c5044614070b000030545071071644403c03401018030094003003080a002c0103010307489519403941d99036845000b0f80c0d80d09042c404101503a00b81418400c00c4016401400012180e0018000503981034410301d141e035003080303055560800071003810307011016141c0c030144404051000c1000800014455428100000045048495101c41d01c070780c0d002e40155140c4190f03060040c03003136029031000c640000a0341d40c0e03070a280c0340c0140003543e840b08502c10340300b014041081d411025610f00301100d6010005615040e014001607020f84140080d0260100038526002122014a494070807428801c031001642c41ca0354500141c030391041d90141c50b203009038048140340140c5905401c00100d441e545081d185d443e03141a00c85140112001e8001e01d2f03a244810300f01d42a1030300001030040b1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 260119442 1250 260118192 260118211
    0x20a080103020418321212010b041503020703050f12010e070e06030406050c040b03010b03010f0f030f0609110a0801230402010f05091305070f110303010513050901060f0b03 76
    0x1c400705003420b10f880150341000942540c00462845c4640e80801488110800c1c4400900d2551045040c1031403c05800051046010340005150507001d1015881540540700007050281003a0401c001207210382a007400c09414150700040c03003000c1c103019009491400c0d103081c81d0b00b5910049114200c0e4041800c0c0708182c1081043c41c041801e05014400c008420310b80940018199611a15400041c00d00500100380d401d1003040081604084480254044c00c040c04c00b140d640d5140811800f42c00341c0d154031801c11030800d4001400000e014008480b0102c0e00324001150702c00c81420119521000c580442e40d2003030103085c000441c09019003010100000d50849425580a120048600d14000b110020f0000b070040d07030681455070180c0007421070700b800602030f9103800c1381c4242039400700c443c00d40c0d040d000300e070041c0c010358140c40d4800840100b0700d1919019604651400300450032030024150703003807901a100c0000500900e802d46c802d000804460300b004805940c1c4184019050380152402c080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 260120692 1250 260119442 260119451
    0x60f09020c1c1403190e0f06011a0f1c0c0908100506030613060902040c112b0c02040b03100507110606010c03030f0f110301080d030b030303060f0105040306020a0801030204 76
    0x81210401800c6001c1503948076901c0b103a2183c0741c000d28550000b0110f82101c41d810008008a110f140306a0b100d101100009094201c8401e4081e0300d0440160b01040a9006542901145058407420384060100b51094140c5811352086550381500d085203429101c03510b045a007040e841c3c2d00c41d0704102151400003d032212540092020000ea6400300d8040341c140c0e000b080491081d01d2024002d00009002d00e400089482c0140e000902380d0f00800800d000250082c4070120240c40c0c24410500a4454a91004036000d070950102074044c1442e201c000c1400b81600700803096481c2d07900010a1408001d00347c0340400d25400f4400010301099071083c0000d034140c85017480321500000d4031030151105031583c110035025079070f0450141510506000301241c40300360034201d5604a000d804031071002c0c05182c985075070400b121145400d0042c4008001c150a20500880170744000c0201c98000c030003540d103d4242e80390b420041e1950b200d16440107250301c1c800a030000b010765024031702c1070589100311390500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 260121942 1250 260120692 260120713
    0x2190510151d040201051312022701030b0606130807080105060616060504080d0507020a0b090a0201170702010e030c0105041a162f1b0901080a0b0406060f09020c 71
    0x4103900780c002c40000d04450410307010701c900c0da01032196005105244c4076241945030f9160404004842e03015426103524164414114601040541c00350390008141320009000031408800c4042c040c40050090308082011800356103617501120749140c00d80f2000084c003aa41c0150315669512480351070180c3d440c000114100d40340409c02c031210b031910034240043c6d940c2e4a071a40002070070094000c0b62007020404c00101e02030100c0c01000d115101a4002c0d0061400c281400824100020300c1540d454101c0046070b40142c0c0c01c140301c44400c0d160131280d2002e641d50380c0d5059004002c0500708407c503201c0851075035242001504020700c42c5202e40080c55454001c10390b500d2a03180c0c19544504000101c40c28495903506c102c0e1242000d4440d0702406603c01c0542122003000840e081d1680341a422401c070f20a1044004591042c2c2e0201c02d498825036503140c41c2c0840d8a4441c848002080502c001c0082014060a5000b00e4040e001204041003443d03070307a004141c000d500c0300300148a9801400c6101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 260123192 1250 260121942 260121971
    0x30a051306080124121d010f0e120f090904050a1103030a0915140a030f18082a06010b2206090504020702061201030b0603160302010f0f02190510 64
    0x1241210013411405400961860400101c4100c4031305000421055991410644156000342040070301d125004980b1520701d96805825507051800702200a1700700803e044510000041032070f21114901036168842620103070f003444512543e84d40e260300003400c50500040c81000b18200010920034141e05029000d10820300d0b49034010007104102040003020108690328560300380a100b40180e203015058441003198040c840c1d007103030110200103503a0b05020500310b6001d00c588504000c0b01c0040300902002681c810b81c2510404030b940c034941c3c10030012030a98001483d115a4005030b03e60039a1038a6840e40d075480c0c0c154201c1c0f5501c4007405c0c00040080302c0003440500030390503036146980344164181408140300181d400444100d800070307010812203402c90500d480780c5020b58800d40b20366940342896010145448140b01010b244045d43c0041000143e03003103811910266240c1c205540c0141e48404140c1c01c00706803036004003603016000400d0003000000720b0044801d4400c29401c102603581c11522 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 260124442 1250 260123192 260123207
    0x1e1401020304030b091009140d02010e0a020d0309030506071715010c0206090d05010213060f090e0f10090504050c01120c05310b13270c020c03030a051306 68
    0x4640581c104110900c0801c840c0900c00b6400691001151a0000d10100e45400c0700c03040681507030f115011104180d0b6441c3c05108000e8202401d100a00060a482c5541c944800300c20704024400c1600e02d00000c10140206072903070066401c2015615140342054000d004611035072411003600040000103201c0701c00da40003c0d802d29106035504607512880c1d40c00d000c11303640042c20550344000100d8011300011024001402101079150100b146a89052005400c0950454108060144c5c3c11410300c01044e21000d0240d100c0c00f120110501a1110722410001c207809070099050a820041008103200000510340498402a40c496081c0200013603400102d40070550500c000400c1002007540c0e00b902c04603015600000204a803171a8140442040d810031200c1e48a0441d400307011070480f12049041c006070000b1320b541100c401d0941c2824460810320562804030f01100b50343c0e111a076041c144200b014618000b07019003113982e00c1540c00307001740441d000311001c41d40c10210b101d00895101d00c01d200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 260125692 1250 260124442 260124479
    0x303090605034606030209010902030730020f12010e0c070204150e040b010e070503061302130e070905030c0f06071e120c15060308040b0702040908041e 67
    0x30b0300e003285031060495808042c802c0004408070f504038199600c4405001d140c90100c503154080050910320354030600c403007240141d1003800c100d44180204141542c124404202d1004010f00280b400c0108080c40d429134000585800156031004c103240810364404002052001000101182c00742c4e03070343d0150300c02440c04076100e6030480400d00407003005003010b0300003501d004040c0c0f8060301402e4940f100c0540754001258182c0d08a03541c00e0042024500304400960403d0303151802525514009000c1342e12800c540081c08042580050352540303c0103c40070000141403030240b030300c109052030380c0010603035082802024071034000d5800c041c00e00d1a0120620055803805040d0b18208003c039103448042440040141218030010281032002803003880c4007408000a5440e658001c8104d170074060941d4604040c02c890540c0303070810500215400d08240d40449240801c1555500f402d840441d01501002d640200007140100c2c1c003003100c450f20044045812513001030900c003160366149a01403542c0c20359 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 260126942 1250 260125692 260125711
    0x18040c0516020d0209090d11010b0a050f04020c060703060f06030203040c0911040b0a170106030b011707030204120c0311101205070309050a03171f150306050316030309060503 77
    0x80d05650450303070030211010a0005006010100d551340200c0c4803848200c60101e082d401c01e01118101640100031003080d0301c9000b008002841008003c10000b48450080903c2004c0240d001002a40c681d01160f8030701c008034003512042e0600040c0607018283c1c9006401c84a850010f000c111170b0b01c24030940e4401c039040540d10a0862904025400908458104c0c88490350100004100c0c540700e0301c010314100c946551034001040000c581c44484482c180c110404241c100740244106c0c0e1307403100d070a6104504040400d0700940310140290000d02c21640600b00301075407280c81400784180d000244040341c0c0140822030000e003103401080b0b01210056915030103c0c8000742c400c10a00503e41c04140d0000d40d42c1800079140360903803165468400f11110440010b01401c0740390907a04c0841941a03001002e040780c104509041040c04401408a0301400202d420b003011403c480038400c0c0c0000c0d0003030801909480308001c0503481c1e50341040050005502003403030144002030040c4604100c9110300c0303440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 260128192 1250 260126942 260126947
    0x20f10020901030605100507061b0203070201030b030309040c11162711030a050907090c020c0d0218040f060e0d0e060c12040f0e0603010515210a0818040c05 69
    0x118140029009503011604056494202103415181c16045d015088466103403151100c4c050b1a104003540d41e900c415201810f5445000c915154001050765005542420081450850980404d10358018900007a500c036013000c0d0b04510254002c6c0c01e564070384060300241c500c00400c5006115070000c1c10700c59600c030401e00c0170b40d000f011500751a211212203e610404103002c521400b0001e110b8105417070503080203560b8018800418010808600201840001480b84003611b540180d00e0380280142c69000f00c180324020011943c82d0b030381459400340c2c1c45c80d50340420304041c01d00d000100072440c0c0840d40c8500d0b040b9000912800010800081e07681c603a00d0802c0040f000c4180309060704000024034852180201d40c000044003103001e88064840703131604000c040d1500740b40740c03030b8008040e1484d4000d9141205011100c000c80400515040740ac1c0c0e0b80c3c400b40480f4a00020148014100c41c1c0c446004018442081004a1008117100b90b41d5800c0d40c00c03101c4140341000100c0b00008503000104a04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 260129442 1250 260128192 260128213
    0xb09060906010f080a0f05010b030601030b030d0813141509161206020a0201020c011d010f0908190203122d1e09010209040f05040501110f0a0503060d06020a030b090601020f 76
    0xb601490382d110300c140720003054510b400380d080407d5a100303800140005c50044104815540c1c944100300200034114010410780c0000200503100301170103001c0c0c040d12031a0102c0d51003886020300760180540f203d4800c843d5000d80e80c01c5810f18603401a80c8920b118080c10008034103104215401000352500d1200701c0406c6200b903034403200298485d42d45807017955000d014400500b8020701c2900002109001c00102c900b540214141c01c540c08000c150f5401498614540003065004054030041c5855a10007510708001d410309170700d140601e03d07003050307012001801c00c210702072184014050781c002c1d4441c1640e407070784040a10780303088002c440c410f81504007082d041d160800295415604595407800040c44c280001010406588040002495441e111814001001800d205a040301c00a11001900b02001c0f140c10042c2c0d0322546004608008010001c510355944d060246003200364085008c40d0307209c201610250181049040c007070b1140d4071940000b8015400440c180030928400381c0505102c440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 260130692 1250 260129442 260129447
    0x30601060509210f0a23060103121809020d05010b040e0f06120f010213080106050604060c0816060f2d05130f1a0714040501030b040b10030b09060906010f 68
    0x1001a01081c0549018a9002c0c0c03d11060090a40d001c846402404134500349042c000340e03449840500700d0308814524040c880b44080490040e054070340c8800c4c990100d000021049403142e001c00d00080c1d0741081404000384128113a4018a018060720200384a580e0362140403000170f0045101d8a072003209140c0020300366100318140036a120300e004001ca078404030301c80541403070400c03c00c01c13103101c60f90700040c2e00b210700c0c2c0d0400305040241241c134000c0c0402401e141c04104140113a01c5448140510301c584103003002a0701054400b800e4001502200c01542030814402800303070b01c0100600c15103000b4100c2e0984450003c44003810200009032010540700c0101107008010041c194842c1064000301203000036140000003014900540c00c0d0000301d0410001301201c40e0010f81200107220005448048401c03642040e80c08031503017400c000464043c414082806845401071255024074441f003240d01c074035003640c02459010300c1a10211600e65905042c045800c0c000d480081c04200d410114801300e51 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 260131942 1250 260130692 260130709
    0x10f09090f091e02030f0f1c02070e07170a050103080405100207030614010609060c2103090f0602190c0b130821190519020a0c0c0311040506030601060509 68
    0x10000d5400103010002603c0d111a089050041039002841921580c01546820080c5610710710340c240c080c144601c42440401e81d220742504a02c850707190f0000700245414024014000105210003146c2d4651800c10b5005140603185583c501c3d4042070540070508900f0307607100e00d82c185c951182c503071403505033404200720f0b11002c0f007040e52046204008001c00000d01e035004400c00345108803000a100d505000c1c010b480141c0c540c000c88100b289107400840803c1e60708000500074481030813803001050900c5000c50240c040b581c40681441031840c1100d0401480381d00901c480d0b41d01c021501c0c0c660903800d2003104c50340b415401c003500c1001580301098a00480e007010f42c0105100c0c1e0740451600b081d00300e80c2d01e920351112a80810203108113082102181e6414a002d4040310548810015403409042c0543d1000030062440e00441d80464405920750044003040c030695001034940344541d50700d25022481455090406001d00d0410020541d00d0400003a19030680d561034680d181407618682c24030004c44d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 260133192 1250 260131942 260131961
    0x6190b0108012610021911100906140f070305060f01021c031d0c0a0b16031404050402040803030105040c0504032f0d03020606041b0e010c0215031602010605010f0909 73
    0x1c41c0081e0050f45119420886107113200351500001da00c561001e40c0a01c903101640f5903020074021401079101d915800442c00e4440e0355019240000c81c80200e040c1100100f841d4601c0100c14009031090000004d42001c80c0e070320410403a83c00f4801551a80203202c1040348a0201a000d40e2000401c0449000280a50840d100c01c0c0d140009007901c1551554010783e41000d00c84d00300d90884480d82c500703800e0400c100030141441030841840c7c03200c8641c1100c00840540400b60800040801c2200402044812240240300040040d520b490b15600482e07200c0d8028418288900d1400c000d00c0800ca00540c00e560449400408200000314940c203100c1002c2800720301c840300300021084800131540c503031003840040c0c0d000c1e45c010491441c080f424881101c0000c2c00c0c200040c88186400a54643c4c012142c00c1104822700c0cac4001681d1503480420300c0d046511402126100d0084208140d0030385011170300940259590090003e151b03982c0054075038144603611a40000c0092200740b080349400c0d003080541 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 260134442 1250 260133192 260133239
    0xb040c0f210908070c06050a0c0f030309080d020a0e0a24050c0d0c0302060f0c0318031b01140a0212070e120f0106090b0f0a1202120f06190b010801 65
    0x21480784a0380601210707000b030000c0380d0701c0c0c40114825040c40b5030700c2110b1003d400705007011351400f40c0740c05015203d004401c01c0240003004000c070600c10036209400071a4240c3e40020440c2c1c55242a2005402a40040d9844800104c4440c1c402496250040c50311040301d00d480ba00c00c07800f9100c451400c614903074621446081c03190400c00303111032140400c100c001c400c030103a40390300d070340749040c50001d04000024000d00c64002101042c810700040310803c6070b030096862900141e003156420180c90850007a444060100d86102e8940d100001c019003180100ad0b0940944403404d66078480503004900403424007112a80310f00001808043c0034a501d1500c4002c0107000035501c800e2510083d142290710a20503c280e51103150400680102d4040c040400714101c440700003803044103003c01c0b0030050034400c08000071300d918201030654442d400d10780c000e080040103030307010a50345500a40d40d07030303a003a5581e500b0040d4094152211502c0c52041910000b0160b41c2c2007100c2e440e04006101c00411b401002c1031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 260135692 1250 260134442 260134487
    0x2010c17030a0903030b040209130e07030f0503181c020405060f030f0f0c10080a05070c020303040306050618040209130201091502010b0310200706140702010f0b040c0f 74
    0x440c64000c0014600c629450400425100300e24540241940d0010820902607401888228a503568900030758840a207041c40019540e042c102e42c03030f440c0164550010300310001c08a40b000622802000401c04080142d03031040304040c100040c061b0810000390010401050001c41030011300e0150011038000d84002d0039038214103c040b0001e401c244407600503140c154070890f10300b1039007071090045080c00281103c5a198406820002400000c0700514548809a0b00c000141c15903016510071405950050101c2c1c0c1c540b5103c1c980a001090160740c100c0c41185291003100d007810305102041d1003590b01803c3c40d9050703280c840c0903140d5460b0104049040c441c0c10b40000ca0088804502d15a01a14075070011484164000030705007814465481750380d2550a0411600c41c0162074005c203e800700c0030242140d03850405040910003846022469a041c1c2d00c01414012242d5054101180111020750104003100d5090100003c498070380950502051085084a00382401055006070740d00d45020000b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 260136942 1250 260135692 260135723
    0x8100e070c0818120f0d03050a0603120c05010501050a0f0b0a020f0105070c14061e0702030d05070f0e0a05100e0607020a06021c0f0e060a02030d1d0c010302120402010c 74
    0x16080d4005440c01c20f070009200445940034908007048958014449001d0029200c2044c840740e00c8040b462621410300d51250b01007032120362281d000300003c0d0b400140300c241c0e0245582c0000d1502c001d0420030741d110340c00d080010400b440c003418a8800c0321010620704070218501002040103412454400d01035005003607890604441c02e0049034461a0b0503920710342940380030f24144041e5403070032502c2c1d4266442042040101440111310f03840c0040c0840c503c4200c2d5a41200403442c5216651903020030034200828080d58580040111310315020b0b5031900303205230803000d00307000320315009100b40c03030b801180c41038441c040c2405940351008008014003640e16080c0f054020071003400150344070600680c0a802108141d003070b50b0381c1d882d01c180c090b403400ca00c411507c1e200040480c401420828400c0c00000b075054500c1d070003001200c0b000c8440c0c07403090080500041140100da0032040c82c00303103a8012041c14144a44c4039208a4210b8808240003038000d1701ca680044a00146840c0103c50000c5c050705603e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 260138192 1250 260136942 260136953
    0x70906050f09040f1a010f080a2310060608070813020f01030f02040306020c0304051207030c03031209150c0207090b060d0f090206030a020904060e010305031606110403111008100e070c 81
    0x11580902d4910345c1c1c285524001850014210039441220a0f4200d0002131000840c1d140075084100201c0001c04d2890f051140c44508201c2e140c4121002c207440c00d240003030941d0300150303542d1041c6c0c000d40f610480c0c0d564007030707050418a00c60318000754061215010b4002c0c540c0a03600550301046402c500505180e200e9030b400040364405003104000c0d81c40030070108080c1c5400d101c0ea070031100740c1ea00a062010303d9079691750f103814030502005050200081d020b40024005502c550071842d0400301c0119114110fa00180050800c2802c103401401106070100d0038003664050a20a0360740a44010301d0094084442c01c010200503418440d01521082c1c40000343e41c0d48006140501c00c0010010381c1c03038101c0700400081303443d60350024440f88440001000810b4001c070070ba50000f1031460784201008814078011006040d40103070750880540205010091000c0c0500d03032040400141d4404284400e00070003034801207021601085a0100e030042800041400310a054020b1414100300e05000b00750f6444 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 260139442 1250 260138192 260138213
    0xc08071718010608060115110604140307121e1e120608010903081e07081321050c120c1903030e0703030e100309052d060403050c070906050f09040f 65
    0x80701c15903000d80014007c007004081c035012901c0d00d40c101040100c031107107403981c2c40b40c00003040580165203e400c15440041d081c400c58100582c03200c0c60b0142a40020809081141624151103803040c0444100f10058098513000048401d120421082240c0e1400202ca1010618141100fa1510390340000f07180c06003401402e41c20f0380300b03440c4c2080d2490810381e4403800c8000d2190850720003200c0414444450341103009030741c001e21055980e26081d10b00c2d0030700c1d802030b142c820001d5103040012201885040c0d4480090482c41c664407060700e901c010780445103126130140703501e49141c070342040282420300103a000404003068032071b081c042840c0901061003810401c99600540109840e980c61034040d24100d43c030010081c0c0f01c0c1c18204002d1886864613070381e4605625100c4201a01040c004610703a4689002c00a0740038440212080c610301454020700c25003045904146920408001144400c2140600350903600c010700481e8910940c0d0b4100521928094016900610030f15030a0b004100c42011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 260140692 1250 260139442 260139449
    0x20c04090302011d01020f3411030c4005280e10110c1002070302070e0403021906020c011505030c190302040902031e0a02040c080717180106 62
    0x10704612004801d5840384030401420181c5c5d104110395501d0f040c81c031095607940081c0003641182c0004c850002003c2440040b03002d103580314100ca82c0030801241c00343e101d03008102501a18922091441400540020301e0412240c50149914100080643c00314546d8040322904012070512030702c0c049901202c006840c1c0150200c2d1040d804041c641400c1701d8002203005103601001030300c01c80c40700203480b50012455004032646030984500041e080c0815030b4040c01201040d5416480d08403241d01c000d41c0151310450140c01510800954a0150280b0314130032609500034080145030303c060f03d0140d00580030100c807225824084102109424031503040c450907225800300c0c41900744800c00d458042c0405d403a0b8402c00a0289200f582d401500041c01101e40c16100414001c1d80303440000d041901d6500210641c00012030320f624103060000307010014900964003000034001e0520304035600001102d000d00811100c00c0b800c50140d52010340f89612210070072a01e000c40b80b42c9801c06094510039403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 260141942 1250 260140692 260140697
    0x60515130e0601020109230607050a120515060d05010f1406040605070606030b0702031314102006041b0905010e060d0f14010c0206060301060f180f050f0411010c08090d03020c040903 80
    0x7c8205010040c081d000000750800d50700302104a80d0082096600c0c0c42040940c607103ca0100700104c140f0840e44801b0640208055142c0c6070311904000107002c2485105900c40b01c42ea07000507005203800010000b0790000d403240c2e1074a41019002e4880c1da0154004403040c43e0742c0d22000010400510419010300015409565659042c1e5018074040d00c0381c0d000384010004a1003400c0c01a5500364001d4000d103041c0c100101c00c250705810700c4100c070000000c003101a01a8070200004c0088840c034003031810b0103085903640c0f00750310f5407240e04c1103450034080d103a20f1380003000204180d49002e050706c40d4814440c50f054514446143e8031820a400b840b401118640e440d059041400c64040c801a036000c0016402045800c1c5070001150b910103403446811209856400f80c40d40c42815500701c00c445100801e4240070b14280050300d1410324030125400d84602e1a0305075405841e41c403c4440701e1081d42c01a031b009081609c000100b00d00b50508100403002d40c80744140c00740031510703540603041205000e034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 260143192 1250 260141942 260141993
    0x6030507020c040501060e010e1f090317040302060a21090b0907050d0c061107121a1f030b07091d04060606090605120a0905030c01060515130e0601020109 68
    0x8900c041d14200b00054030520442c202401405101e6002c03100d804035640c2403a003652201001000b10305004e08001580c046546003070a902c1c4140c0d0000d80c1c4208891107134440c80b0ba0044508c25029150107030b800001d501410030013000c0041d501c613030038020440210501911030030b10b8007900301e812118004401c4418465a604100280310140460340c000d15080e1601c03150f514141d524601100d480d40516802d200c3c10000714800f1003c10007191015000c0003e42840c404031604202034540410a4045160825140042e81031a00445401c400c2210349139400343c000e0469031240d40e4984c0c000d000a0030480c0da0900012415840c4403205003c500102c01c0520f40d0605081000c00d03604260010740c140440c0712801c2058a038054111145c58076684a801d0b91074441c0d2844c0310141c120448080c01c1440003280601c10900c066112030115001202d446460302d81180485080f80500d03136550525141c07504c001c105000c00310b80345643c8204140700001c2c030451a5580c8100c160140f0300c0c646c4002d40712 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 260144442 1250 260143192 260143201
    0x1051509010902040f030204051807170d050405060d0b310c0e0904081303080712020c030c01051c0b06210717130320210909060603070504080106060305 67
    0x80c442980944101c40040d4074050605400c40c01c1e00000d440300900540d030740c07000034001041c20360749503415030700182c1501c1d040341e520118501d2100c80181c88030101d0054443c0a25110b0080c0100c50807500068445814812503800c502d004103000070001d508854541c500403038091040d0b41c6a0003c00c4180c001803003001c01440c509040310000c1c41298240aa00660010141c0ea0340003820381c416808489240e482c2c042062042c019295540024600380011400348108410304981c400e0113032460342190a044880c104244d40e07030104012440c0810810410b400d0b03200d0074000001d001d03541c820070109003883c0e4240450080d0b841500e041c103d0700c401440d81c20b0500921300409030814850b00d00305080d41c140590059480001508000e1903483d0294590304240c020310380524658465025488402c0c110746d00142c403a1b59600404212190312903170b00324400402c10075106100409403000e281036403040144502c9504c06821401072060500001405403000d01980015240a98012401d03061 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 260145692 1250 260144442 260144449
    0x10605041703042106090c120b06040b09270d050403020a090603080d0515030f060106030608030418020a05071e0204050a0e0a290112120206090601060c03030e010515 73
    0xa403904107805038104000400c40b0404c071102c0038104404002c148019440030f850302000a01c1c0c030150041c40e40340e400c00001030a0949021032041c00e40510460049540c1d110104000c807030082c0000381d8050f800102084100303030403010095801c010f8146d04218001c071404400d103005020070402c0d0000b00c0006051003181020700709807000304020041407040c6c0f419543c449030303540124104410f4466859002400c3c13602013450402c0ca00c1005819200e8204051301095140c01d401d000d20300119050002c0000c50312400801c89040719210088400c0c180e040d0661100a5844054284200b0400340f00407800301d4500401940081d501804004461001c0e10602003928001003005019601c1c00f281002043c3d0042404d508055200d900307034000301c000b0240d50a03040045201614190700c85400030842d90700f1044049072250146607008203003088840b00300c0e500c001c00c41d02a9140c1d0031810041022500402d0701c0300c215846801d0114016000a11450031101c08850619010904014481c120305 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 260146942 1250 260145692 260145719
    0xb0402011112031f05060d0506040e030f0f070c0e0f0702011d030702090c040902070b06030609010902011e141801090602010b15070f0b01060804170a09030308070c0b01060504 77
    0x15a40310140c584441d00b02014030090100400ca606504500e5400a0b904014040700b0400790100a10040d280d00b41e0a0741e8100420080724050f004910303041c0320b07051000700007003038805102144414034a020350710340ba0760761943c0060b14111101e961640c000704608800c840a684107004100c0481d47d1844c00b0003000303003941c0703001407000d41d11481245519074000000c0704032404540c0546241501d6150a068800b1502c40c41d07000e00300061020a00d1402c00c541d400185015420484c01c5803030136160359451070f00b22100304100902003000081980c2403104210350244118003941403001e4540c528203900d600c84da0203a030100d00e009602ca22140615a00961240007a1525200804c0b0111410020030645020045800640030f4089220b0040108054041d44000d40c0300b22a0040c65a54a80290865000303803402c45400305165504481c1c061080d061b5000c2c021203503a1280d07400e1850703c2c01d803403520340038010600b0000c2c4480103401241507112154002e00b0240c2d915980c5501d000301920984 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 260148192 1250 260146942 260146967
    0x11030c04230f01060c0b040c09050901020c12030105090615040308130815161107080a0308011a0f0304020d0501140f18070f052209060507090821090402160b040201 72
    0x40c0d10150041c842254005d204604c60340d4001c4685480381c94600304074429084079409000b0840c2007404110003d83e040d0050300d28030b503496085543c9c591102401e009140007d01405400240c2d00002607018502003000e2100c03109192041407500d500c035101c0c00c1c40c992105114a04803c6802010803d02408000030100d18040c1b0a00070300300c0c1042068030310320130503000c0000c00b042140f01d02e02000240a100003401020b0130000c590084c1c24900d00605004000d03c200480203c81031054000c0d0700c1403808882c04c1d40b044610305491581d41d6801c2019038443c10805031219942c0d0300c074418110b03180d2040c0c1801a204d500201c0580c1c81e12000d28101592001002c0100d81c02449081201003030122807007056560490f80b4104442010600c10505001c100c003103200541420035900502c41240d105500805440e61400b1625464502160b46c0d80c3c0e1070355900e041f90f00784115145014211601622003410000d00241c940720305101029440c080c0341900360b034403800386020700c4110341e001050035800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 260149442 1250 260148192 260148211
    0x1305010306021903021801230d061e0f0605181810050402070c0302042d1a10081303050405060a0206160206040308070804030c0b09160f050d11030c0423 67
    0x14103200e0581c80406c07078104001181401081d1520360b02c00718041c4004c803038607484c21207115141c2000c0506900139120070b00c01c1800c07441c5040c6012507022008101c22040e14101030150481c1c0745070010440f02d41c0d11000c02450f450403818145031503590390ba20740d00d1103004001001050303030604402c2140021801e80c000782c0302d07910410507903000414040c08001100d804035400240051009405600d20b401000039000540032055401a407025950041c603004010721111200102101c0070720000b070241c50343c4600130821113000100d458402c01d01d000b486030300c1f9250041c2171a650f000402c1e25500804480340240e0007480820090034040c0300f00001d2001148014086070034951000382c8020406419601001040f400007418103002e2454a0412544030a840f0030314070303050303d005845000c07003605003800d00511600003d840e01c440042c0d034151040200141021000b80c0d0394181d654501c5801540c02d8010b420442c001a07503184500e103240c222407070b002c08402204410880e120180100702802 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 260150692 1250 260149442 260149447
    0xa0507060b0f130f0b04020310060e0f060f18060d06031502030f0c0309030909040605070e121207020301061208090909030f0702010f020312090d0f02210702130501030602190302 78
    0x341a52a58880f1960045220000032104400b0343c00c04003814656500f02d40017030000040c0100410244021000c90315240c2c0c1c2c0c801c040c40c8000c104460075100c82d034482da0010044c048200320a0040d8000d00c00318200c1c120001c05504118041406500710b1003480100031b87d1401c00300140180b41800c0760441c0405941145140303413102110042c00c0002d4025940c1c004040f00207580f20300c04100f15800d02c0d00050890704140340a00d06540908400c4640c14005814941207103054200f91042600c4114039101410640001d41301031001038101002c1030342e040d900d82d01e001a5988541c0c0d40710040a0060340038958134010202131017242d620142035240c0592040201058210038030043d43c01890742442c1031034a0300c1507030074200e20303602500c002007a4022680040c0040d00343c0004980304600c80a46401c0c10035a500c450590303c2ea00c0c0d0b5201d078000340901c9000d20800001e03000c01040020b100410743d01410400316200021988260011560180d001444188014011500c0c101c101402c4c94290f2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 260151942 1250 260150692 260150719
    0xb040911040b070303151707260d030b03120d0b01081b041e08061003021509090c13170d0e22050c09060a030515011b030f02070b0a0507060b 62
    0x6105206095000d001c0503a1482d42c01c1c00825003900c200001d07c46040c640400742507100388551500c215100701c114503103d040b003820002c5440443c0400600f01c04010309862141884190094082d1109603076150040400b01d045d035061031005003070401e221540c0001c031024400d0014003541c501500000c0b22040716a001018045000f044405442d007009504000c103051b0042814408856000b1189071300800d001c01400e180c80801000c100c0e03000311406d2002003040d24900c080c84c8142061160030001d880002421701c40e0820080034002c040d84401101c10f683c0d410790324104031b05004605a030381c10500c10110b0ba5a804155101075041c202c0d040c0c9420219425400002e00c16072082d4806180c4400001d004441f855041e1482c0c1d50f0040e10541d50340050100080c02400704071a00902c1c03407020a580000780d40f040b2804e458044048039241c00203003160310300395407200030360900004520030340101144040b4584003404440102c3d845091710340203076107003840580d02c001700014050381d050107030315 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 260153192 1250 260151942 260151959
    0x1006080c040b0c07050604120b060a1d191d071a1b0a0605090a0209180a0b0411030109080c0d0305060a0603020c0f01020a0806090906130602031f0b04091104 69
    0x10780441c0c46440c1c1080d03690f218142d149040c207040340d003c2540850302040c0082c0c181e82c55821a040305210340000e00442d50b4071801c10010485070700941550585507080340400d4041c01c0411904020029800400c21101d0030811085d56a034040e040d03003900f0464540d0806030300820105001e0890344044d87c1c0c14810380b6010404a018000b42e20061680d0b101c1c0d501e00810f01403000b02961078002d0300c217104c24603089042a030341d0030185a0480c01001303000300058003200d82d034141c5070f41c11100c2d034003500420840751102c86040388060701c1aa000005502c0341415076809105002109120f02401521000100c4140d414040e0302c40c7e01e8003d041c20801084110740d10018100c096401ca03040058440c0288120645071182c11302504a03e0b61000841104c00c41e00315082c030b171040404640320421035951480c0141c40c1c3c2070681c1c880b105c0c6e8040c8513140001410300c5d006580e1104c554081154a2810381100c9031210f00f580d4002e15a83c8400282480072005070300a84507007000e840c048614051529048 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 260154442 1250 260153192 260153197
    0x201021c020a0b060f04051005031212010b0306220b041a0a0b0a031e020c280602071e03030e060601090302060301050d060b0d050f0d0311120a02160b1006080c 70
    0x10310500f001000106241e4840c980070700d60801c080d0040000d40f5090700410f5050481b401650f100c1c0c814055480742c0201c082d01102d800d160369280f81c02c42c69185c10a50310032500042d00c0702d41d008245001240746464402c403024580008000042581c000c4801480210f076500d000907204d640300390f44a9446030700c5000c070100450740c00c005600e50314410030004034010000b40c600340700003401ca01d641f864100b01c42e80140c1004142c1348143c9203540724140780f03c1480740c00550714030807007803001a6a1000c00c10303036800b0f442d10300d008101b0252200d14030149509070010300380007100070a80e108017400c81c001042003116030100080c2491005c05007150009546c5000500c1035a1241703494000c1042040402c1d000800800b1026101080d0160185070a545862504115001d90311500e288104040d2082c0603b000241d011406c0e11300e00500808a00103214005000d861400c1d0204002d481c44186000b01c040594010790820701d03141050003030034000011a038044010000110203002c0d03164001007c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 260155692 1250 260154442 260154463
    0x70804061d10210906060f09050403141c020a081005040c05090d0606030203010c020f061f090b15040b07020405061008070c030c08030a05011403011a12070e130201021c02 75
    0x800c00d941e10460000781d10300c910700c220414500c0e07081104c90804c0000d50340140058908121100c8205500e801c0844102d0300704490140c00a0152030900070403210b00c6000b40883c810140e40c26074144061280b403420303030b402580c0b01c0e03002502c510100140d4000460124015240c100c07000d01210352402c000078030a01a144580388502c801c0b544c020100300031035000d48001c66000c0c0013401104d1105002035200c0306074261489182c041c480002c0c1490fa000c03010064000d04107084d081c201c40c2040c440701c00500248001503003021100c2c104a5400d420035020b44010104006400d0f40c41c0c0c0544148001d41d14050b00c0c450042e007414001c041340e190443e9071260b100007145001c0a07000354900302100c2041e0100c0005e04440400424001145510303001a41070700c102e8483e100c940d0744d8210500d800c031002a2880851021381179088034052074005103081c0b42c7c59007501220003032929191250107200081d41c14021029100280c00c0440d60140b0141d002181d542c10040000f0b920030401a4071481c0c140c6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 260156942 1250 260155692 260155697
    0xa14010b0f1b1e010501080d05090415080c1c050604080f0d020a02280c031202012901030b01080708060d02040e01020c01050103030207350c06070804061d10 69
    0x3880c06072201860107403501c005000035444040308510440989500d0001400810082e141140340c069540c14054070303040f40c00c014024000c6200d0b002d811195900042281c82d44640c0f1841001c1110b028106684040d101c210054030f64003406d9400c2040480f54034001c1d840686420044e100414000301e4103640c00350b040742410356103003000b004040580c4207000500c3c103468400b142c0c1140322980054400e07490904607404049000182c01d070a005189102c5c030041814000c200c0c2072001418040f010490980c0500020030300300d00c1e01042d00c0c00301c8a11282c0785e11b008005c07455000150391600584006200031709040c0081c2c1440a030060648100406840c058060350310503100715200d0b03912440752508844000c540b80c1352405481d0703003e05400e1006800511510602040e907003d0b0512050481c95401c0a140000c0c071001c1643d14902d1005002c0b419600850f0300101d842e03120f2600a0541d07503c1404002d55550812501401c9505005500d202d00c40700e0488480c207a0310388250500c1c80ca4000d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 260158192 1250 260156942 260156947
    0x90402010c050a0c06200d030f0f06060804050111090a170309091e060406120b040606081c030c03051006110c040e010c0305060405060a05091b070c05090a14010b 71
    0x2800140c1c1c1c0c880d0a2100207140d03104001000043c004074402c403006a40003075541d13580c8000000d60138451410040c4401e540c43e08000003141465010f944048405d00d50b0590114001986070315840031515035520600115844c1000c0100f002828803554010a000324406420151240041401c0344118000c0d80c44660705405481100381c420400e1722906040109260304501e003a40d200c1c505001040d600500d106d102402244452070301e800389405440d0a50520a0790000c662642840c42d200600f054400f10354807440030603080e10900c2214440e2984100081d86400c0e1003034014101d1300c1c410461820545407105005804d0b00940300c0318100c0c0d000c0e00d0641d14240000100c80e013400f0b00389419036405450528030620002040d0046024503041345c40800c0540c0d00d1000f0710040c0d60007100d0065100d81d00a005105601d0643e8500b6004266900a05c8628500c144420500e40c4003074429100900c40d40f00c200302c24a4056100ba07482118118240208408100b1038112181c044c06100e01e9903801 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 260159442 1250 260158192 260158201
    0x3120f0e040c2001020d0513020f09060102030906070f020d1113090c1701020c07060906090803040b04030f050304080a061a0607050706030c030b15130b0c06010e060d020d0c0609061d09 81
    0x250151860346000a400708030300d090092248e000407201c450100d010f040008a00500d924000d00c60601ca0030068000d585000142420020b05034820036044411400140c03021015840750f9692500c03080c414009040700c1c042c6801000340b0781c0c05030780d0007000c090304001c0c168000444c00c131080411190090b042d4003102850307810b100d0280c05440c5010107507100d10300000542540c0b0040748011190b982d152114495114404681c84e84a980942c10016208020410024000242826545010700b00b500c0c1050b86803141d0750f040c140603c400344e50b00368032801d030b1080b41c43d03400d642003a5000c411620036241011a0f82c4003605c5082603c5681c0c241340c0d685600d1015107009400003031080c0e1004040c600026001441214944c0008040ca0303408194210003144c0b6009010440d080b03004140020405d5078a001c040700d48008000306102e030000d040a03100401030301c07a28422000117115010440d40142084e20081108440354800010000c42c0f26802c140400d0280d541c2800c0070003560015070a568 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 260160692 1250 260159442 260159507
    0x3050a02071a18010e0a02120102070f0c08150103020f090703180303091b050307140402090402030c0c0105160c0f02190321050f030f06040603120f0e040c 68
    0x11900e000d02541000301c01003186008001c0001d00c1051100c464111001512003007508854000d420070201b40d100043c00c00262400d42d400340d0644c0700f9034002600c0e001127030f80c514030610f542500845515450240c244a50f6005006444074140b208104803400c4d80341d40c000602080d10900028041c2800c0c6002c5070310148a9000071500c2d801ba41008004840300b0302d0010000d100640e000c1e1002450003104e0395020401c1c845640c1280c02c003d00170518242002c0c0094064101c94410fa07a106900304500405612140045c610507071501e0041034a603e03500340c3c81760a444005010390222401602042401900308903844c51b142e4021803100182e5185201250383d2004015407654001e94030803000040205501c80006200034035a0003400c160700a06040e9004c0c0200000c0e402d80440500010b08400103240d111680f19400410100d1050b6403602d40400881d251406400002e0016162445440d0004002e41d030456054808000801c101d680040810312a4a11050800303440e02d8800000700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 260161942 1250 260160692 260160697
    0x31b090e040219080c09090a020603042003010f0c080a0b060d0e100e030702030d0e01080a0507020a0c0810150506070f17040f05010e0612070806060c010609091a01060c0303050a02 79
    0x100e002054440440d114404c440e0b0700c002d00d2882d54892501c140c00607400748000720303100700429806416503003191074503a504454140c1c10881640784240c0313440c1c0d501c00c0c0e075024010844d003400002400140b0031a1a40c00901d0389000601c8200018244480c003101910b030380c41200c0501030340c0040000c0684118102d40d0038454800d1181c0b001d0750400740c410f2040c86003c001804c81602c00c40c211032032561107400a551035a80e50341e40e81d0100e10380c503001403000074441c0c100b2540440184165004010301d0717a540800085a60840151544500c0c1d02e6541c20a4900c00c248038018410743d000c0c081881d01c4002000307841a00e60050068181314102410444904102101d583e80810481d03111516000c0d1300c0d0030606c4c513208060008459107080300c070500303160040303a010a503400204500e56480c10070036900540c0103010940c00650803c0540c035046030a01c1307214081c18040710b02081000e003904060000c00c0c840f04400002032014070041100a030050212151140c1c10708021500f40c2c1e9040c0322800a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 260163192 1250 260161942 260161969
    0xb1305100504030c0b040f06110c010c1416030501060605090d14030f031e0c070b06100909020c030301090c02010b13050703090f0303020a02120309120c0708010e0706031b090e0402 79
    0x105030550100d01c00075045c3c081d1007a55a003004407588103235a01808c5500c5a00911040a580c008028400055125000840700a8041e540c018110611072040524001000c50107100c40c0d41340341001e1041203001c1c001e03000103054500c1c1c000e081c0300100c03000902c034100c4000d0040903140b000c05000792140061007542c540750540901c90303480c0d15140741c0b05510341540801e03044504051000007154900c682c415035462941001d8400007039540c99060003660744044400780d081c40442c2e000000e001500e800145031410b000000f540d00c03549070100d400255452007200758156410b10769800070540707611282201c55a13000b0740219282c0c40d8103200703400601e0380f480060320441e00c03000f070380c400d154041d00246a50380040d402c0b28a01c2c0000c0341d5401c0c450006461042058208000703065080303a801000c0c01d00400350b10240c075403080e0b407142020708440940c0e506403541e41100d8020050b0716058401c0c01003440b1000070110381c4541c001001000024035000306540102068041015500e6030035817880345 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 260164442 1250 260163192 260163203
    0x5011e061812150e03030103081c060308030925060804081309021908060906060a1d03030c060618090d0f030920040f090b040308041b0e0703060b130510050403 70
    0x42d10140d040001a0711032100d00c1d080b905081c20803414406000000301c03070489803c070038950700b40752540c40d00314244c1500c17078102c0c0b0754140c0b200400700120319460000c41c0910200030050544203244070f040807003d02e02403240003110490140070402030b07401c0040c40342d005a014425035500c50b00c41c40e90640103040c5410000700240b022070142c050300303681005d01d40e14403001e40702c0140b80d44e191010410000000c0b1101034002005000c0343c203c080c0900c440f00c1d604c10400181c1c031608412200480c0c995082180000c099070b01c010140450b42c00d010400e90b8032030904400600480c03500c020750590b80c030400c60051702080030201107440194800e500c200042c95000190b1400003c4000a2010501c0341e01003c40c49a460312480503a6120715100d12000035622016441242c0d136141c81c180c3d01e40100401c161a5072004007144c69100010030881c002070103215400c1040343c18400001011201c0030b40012030041c00400500e2001400b060341503040b507100310b0340840c0c0c0a421030400c440c0b81c021640300501 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 260165692 1250 260164442 260164469
    0xf03080402010918021305040e0d050309072c01080f07030b0408070b070816020102040807030602130e0403020303010305010b1219020102120c010905010e070b07110d0206070308040605011e0618 85
    0x184d00740a900100382042995079803d0150340c40718100b04c12a144071160141c2c0703501c0054110846400398025541c020724900a80706a10355030301c0084001844401c500086246940261424204040807036026045a900070442146080c407140e03511841404041c14a0107040000f9003000104021142030a03446203030302d0424102100c1c040c1c001881a17071030b02c5203900c3c0c001d4801c0700d1034814401d4800315061000200300c9113245449400c001e41c01005506c001400c200c20203d020885940c0c030b50300aa2096000b5503896240d8107000c0d08403081c000516116a40700029858899000500c00c691f00b0b41410407010844c8140c40142d01c0c00d9082d00b032080089002044003d44484103501c6503040b58002c6c0c009006115500c210f6544688440c010501d081c4c4060114034046078210003c510560b05c003a2174620780100d1500001d55540100c01d0440c005051841000100304550280600500050210103941440c0b40b602d55800001c50041008100b4060540021044427818030380c01095010080d00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 260166942 1250 260165692 260165729
    0xc0c070b07080c0c0121050628080c0a0b0307030e010e010e0a0b0903120c030a150f1701110405040911090c030106091403071202060d1d0c0109030f030804020109 71
    0x1140d800020801d9002d0141d04c07401c00c00c3c0e5024000092000c8241c0c1d81248013512001d505900800014003020b0f00040e03601d050a5101880b02c0001c66844d45032000d00392a90310307001c0c0c2c1c01c0c40c0c03004440c0da890050704407040c10007441100c0c60550f90400c1c040c0c02c0204034050201822801400d038404d2462480d03003880024042804003007841080c1c18015200c40755a581c80112041e541e2207151042c0e41002414000900c0c01210b00d0061500240101c00100700542c0202103c00d441540b500410070503941100c5c2041540300099040e49000c030303214028082030410b18502e58050140344911401251903a100008210503010300d401071080c0144880502c0c00c00c0c1d030310358400760024065000130401085e0080740301d42040c010416040c100400800806080052204034028513402c200d130802411b101c2d00004c5040390060141d03015610b2003d0014140c501d0a0600e80b00140710400d0500240b60303820b00104218030f102010007509403d010181c5e0311103100482e81c0b004c03603501044600d6902038050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 260168192 1250 260166942 260166953
    0x12020a0c1a07020f0f0601090902180c0a08090a0b0708130807050709150e0105060a120c020604020a120213020702120f030705010501050108060607020409060605060408010f230c0c070b07 82
    0xc9000e0b070155401c072601da200c00b203490b5a81e4513040f644549164080d900400c1014026006452510f10140c034101c0a24050840c82455020588100c000204042240e41d001903002681a038403504a0009084007180d1f40c580c110100000b0300348408101c9201c001400d409250100c2d0380d00543e1015002e6a12455420f000d905c9800b00d004040391103082c104c0c084a0394210404400c00d030344804036001c40176440c003420000c0c0d0740d1011085009000c000703260a00501d0140c42400b00d40c00440d0090310503850240304000308484590002e4403203005038080c0c3c1e030160b00c5085080900b0340c03104200503916045800042c400d2001d94140101074454400341c1880c1000100281040601c180e000f44882e0b603c460042d00c8000003192915000344060140001600e002d420a0301c01ca03020350000070340c1ca610744000c070350b40e03034060340103412117079101d401d0a00d0102d40751140034080c10007150b840003c40000c030051003207594040c1400454a03c00714003214914800e2102200a240ca4080d050707a43c5168030f80b1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 260169442 1250 260168192 260168243
    0x4230f01021903020408030301210c0329070f03020711030712060b0616020108070c0506131a010501021e03090a030f050118030e011115010b070c0f030312020a0c 71
    0xb0640180401d00e15100954002d009840c283c0745500c016504682c24003081d0340b401c204640304100c101540c1040c80780424030f84031020002d140184034810b940c030118110b0b0703c5260190542400b000b51504100504a544170940651a040519000d84da44e02c2d107081610f00201c00322901941402580c00c0050b1450203d980e0055084c442d140030701c4180300c1d0310101f0082e030140e02801071403400345850b5070006601c261180b039444100303810440c10307001003610307086d10b030030000c5982424030601e07141e81805103c07120864404800d40c4042842e859030501c40000e4503114040c444500303402c0381d69000c94402d4800d005079040310b00040c00c0c41d50991381e2400c001c066400704070810798007546800108442808604c51804a094060700d948090518090045403503007622041c0c0c14041c0200c04103400c0301d135210900d0900810082c440705e030f102c2d1074a0404051b508100d07800088142d200560801c000790304562001c981c40031140005890707440d01081962101019100140110070000301c4c0c1040d10a034504 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 260170692 1250 260169442 260169457
    0xf0301080c120106050105160219140111011a0d032c150c060c03100f08030a0e010906120203100e04150c0906091703040e0a02040303170f04230f0102 66
    0x42c264401c0450300a41030880f04a0701545001031410001d10740c07155441c20360400042d01c0a4218a0a80e4040034291541c41c85904060903958034034810800641c0e01640b00c1400b2000c1400070844801d02c0c400c040507451003c0c031468000e41c0380b800348109240c050001404110346082c1000d00740c04c3c1e00003880740c80c0100f24132007a200d10a00340d0380007450108001601ca021821070001c0030180c4407441184a60b030001060f0348070071035002801080700000140301c0d200074510305000716100e09404c2c1c0080c00d8140c3c090552810030000700b81c1008a83d6221049400c000b102c040c005070f49488852070182078840c60b82040148042003000e000400c07645403034140021340c1c1c40c0800c0200a60f8644101c42d003040512a02000400b031070400c0c0030000c04441701c0000c0305a4001104d01d405c0d62240e4510b42d28204442d1018816408502041415041910940104513014140002d032404400040760361402400c06000328403c1c61185001400c08602036044030500403c8402c000700c840b1a0740d001c1c3d40642c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 260171942 1250 260170692 260170699
    0x60a050f010b03011508040203120f0904060b030f0103200405160807050306060a1b061805010e010605060f03090f03040f140a03170a09030606090e1915110f0301080c 73
    0x10000922142e101d066a059a009036010078210120390340032a070780d0350060010b0368540114003140c1104000c03100100000e0001e08a002d44540101003000206c9185a0005540a20800411207103c460f115240d0542e640326400c5143c6040d0380103a00712001e4010b000f00c0c0c1151401083c044520b003111a64001c011056031803103910742e86c0400440306400700f500c080d6000003050040840090140358808400f113510300603034000340ca0301d0300d0b0702003560010311860403011002c0800300c09000c001e010340301d18581100002e0012030301e410046280d901c6003201070760701090301001080c4800c0702446025400002082241d071540d8891603034182052151185500507030034442c101e0891b080004054080381c0d005400c096800d40c1c2c560003082c80c0d034002442030003000102071740840014100e01c10b1074081c0c6401d500004a006404004910700201660405994505c0f29002c0300083c2c860151014000c221080100d400101c6000102190080846031000150040004500c6081c0050700c0b44013030000302c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 260173192 1250 260171942 260171971
    0x6071b1a04110a030c050d03050c030a030b0a0603150b07020301020c060703020c070501020f100203091203010303030606090501032a030608011103091e10152612090d0f080705060a05 80
    0x8030400c20307860703d540b000a0800100c203a08021915142200310444c2e4000e05195140c4008500070718203550083c401540484d9440c6084259400d02d0107440300908600c3c2810080354280c50700301c0030b80200912444000d0000060241c00b15102901aa00000e041200301c84003804c00031005406074101c50010030062003080000221076100007030303501005803000003030700d0024150320404002e5400200103030070920840e92410519403116009500840c001d640015605050440040c40040b0f070f039020714101805c24908150002c52540607000c1000e444c4905d012481c0d021000742d01070422903000c0c100310751815210124050075040210300c2a025082995400c0c4541800741180303805010804a6680c0600a031490300c1d98198000700c02d042481aa26008603910441502d040040381c803441e007101301c0d8400360041e0000c01c0180b0124030404030341076402c10354840c022030000c01564078090044d050824208081c0140b480440e0b10440e040f0041c2e5556140c4175008a000c2c150a950800710b0f100c2c1d6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 260174442 1250 260173192 260173223
    0x11509120507140d02060f1305090930090d03030f02040b07120203040303080c0a0c020d060c09080303071b060b0904120206011202090f0405161d060406060206071b1a04 74
    0xc4c60502030710a070b00502d031509040344910050b0300b0750800c80c80403400061034000403419507220200315104140d030341c1c0101212610b40c1c1d41480e03103c02050400c40c86505454030182d0804410007a101a000c05484040c5103104505044003c1c200d04a5115a80c0d0310015003c20301c01d4600b002000c0e132074001c24101c0b14006900c0c0c03040340d40b031141d440060002000c17080480c0603001d5090061052615a02d0000010395490f0002000e8640e81981210056503d8024030200c5401040060040c9071090103135055203800c18001d030540c111445c1254440d01d64601340002c1040950040f03074103e601400c500000d1030545440b040d203c454400b000c2c050700c541c200010384542c03d040c40403a5194041d0000035552a91540702c610713610041e00844040c0507400c3c040031380209540c4030301c0c001d183c5102502280d10240c50580d144081c0607004900840c06e0000c144403507900001d03042d1b000000c43c9000340300c80255841c610509030b00000020300e0a5800807901d1070300040303c10340c3c5002d07a00450000c50f12880c07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 260175692 1250 260174442 260174449
    0x4060f08010b042405060706090501050a0e060a110316051303080702030f0307320f0106050f0901150e1512040606120c0306020c0a080313140a0302030301150912050714 74
    0x1c004080c1300c0e038a280400622250419034060002240f040300042100348680c0e03685829240c04503205200e03141d48e60550013010b401002010707040345864400304100c00d01d1002d40f107190b100044c2030b00c00c280c2c4900c44001105106d0001c0301c8400c03003140c42005205403030340351030111544454001ea229204204008840f40004401c95086643c03110074100c0d044000b12008006403001d240c0040302031040052141c00b03900501500c0b541c0c290030b00c00050000c0c1130801b0040f41a0891b081c55010300d2004005101442481000c0303c100d0348503041c0030b00c42641040002d003407900340c2ca41c0c1480b508000b00f21b1044007207950510b64021031052009001c25508c4840807000350030720740000342c0b0b60002c2950030400320b00260b0081440007915421789844015079111003440e64000e56003e034a00c40800390001c203200407500e603900002d01000c080c0500303140c5520020342e20701040c080d0640b01c0e031203100841d407a58003843d0317a50020a49440c1c0c00203401c4003801c000e070f1a80e045128605581d04100044200b514 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 260176942 1250 260175692 260175731
    0x3050106140a031802101e030603030203091c020d0b07020705040e0a0b042303070203010b060f1e0405130c082206021803060f180c0d03080604060f08010b04 69
    0xc5040941604010320b5020480142c440044005482507418182c030025885101c4c0001d907034400c42e21165100124450400b00008040342500f007054500002400001d501000f00c60421504480081e403000c6034a03045c2081841e6514025405a24400303420b042042d04040c840c480d44031a004d0b07800280d55403003408261150804072040a420600520780040e008126064101e400360070681460400000303074002c0c0d041e001031400191390010941c0c1c011032809008450703d00c0c905403030301170800c1c240307003040d50290240310000c140800d288400304451501c3d0700c0c10340d4000c106c010480c940020100c11640d00506000150000242c2240b000a8100701303507580d50720707000070f08246807941454151920307c000d401030350b51150a40d001401c540c0b171942e400c01500e0b014448003110f5003d10706083d062140f002c02e40182d80d60f85908480c0210080342d40b001c00c1d000203107406060907041a914003001a00412854001600492105d90b0100b1401310561003a5041042942c040025032503810f0b0714032460 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 260178192 1250 260176942 260176967
    0xb09010506060703030c17090c0f04060e160c0203060a050a151a091f02010b09010608060607021509041a0a0f0e01090c0203120103030203070201031116030f020a0b01030b0703050106 80
    0x38004103c0e010029219038007981080c3c07030503e00319103c0e02018080036510311003500c2c1030b41c440d40048040c001502d05501c1c4081d05071030860707041040b0341c0707031186141e56454000c1000c150194510604d8000602910326185541d500034169045840d1045264000380410354100e501c0e6460100103444650484542c01f064400e07a8500510700120300030072030404c1c0e00001c0341a4014045000c1060380c0e07410020342c62500700c19070b0000b040c1c542d4410180b0018050581c000403c010146040c0300705901c4403c100c814041d0140c0d0041c58000038160400b1452203202c1495402c1461f05542ca116404415001501010100e03484420241d03107400f11840b401c000c0c05086807615507800100b100e50620b510000300100c40340192814481042d40e04102c0c80400d0f40140d0168100042040456078176100e1100140302e4841568180000d100c0b050020309001640101406441603408049078000c0196158191380266500f0341580c480c40c021811035019203c45021034101000031074164011445034152 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 260179442 1250 260178192 260178199
    0x8011a030910050901060806010f150203030103110409020f131a04091e030908030a03060f0518044d04020702010c0f30020d05090a0e0604060b0301080a0b09010506 72
    0xc00c0782e40c9558018000070300400d21640d82c45500103290481884914002c200405c544890a40341403035061030010000c1c88181150401c200500000d80c04214803000080280c600045890071840481c4402e407401501f65440442d2603d199111041c03900302c4030031629003070640440c4010341400e0105a82041100401056a501d03100004441840f4003803850f0340213142c04100c01c0d82d21490107085030b200340110400079403616001d004099000032403c00a25050301c220318030701070b402c00420444001506c02401101c06ca00c48a02c94003401e1400c2c2c4c2e00ca071052008042c3c41100b003414002012200035543c2009103040042000303840e0030310a8503076013034041c1c4806a81912a070380d40c01e0f02900101003107a2411101111039078040e0b0600005100d80203070110701858140c08140270340741032900320a1008001040154000c241c41d14a1100103c440041c000e550645484001130301814883e00b1031041c0c400048000251403030009241f050310360003242209211349602d104c0300d0980d031046402940 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 260180692 1250 260179442 260179453
    0x90a180b040c2021030a0b06030135030a17060406050f0114071a01032609060a0e040203100f0807060906110c09010f08010f02030f0109090c0b070308011a0309 70
    0x3611510f481d1240c1e6041441401d848811348104034100b0303a00691011031340d4900002c010083c0801ca50301c121000c1000444600742590b00d400c0c400d10b5641000000300468600c41b03081c1110080c0120009212034044400350303030b1986403071400102400c1080d1030b4002c243c8459004594241414881c05050303800c0502080b041c0a00c0200548060752141c41000125104005681c04500e0394030f0402c615207624136208501e549141802c5030040290300c8214660fa60899a4104c01a1942c04031005071909452107504ca842030402600c880034004012038105000104201059910040440c150341c80741e002e41080c16110765a80c1d9603400729000e20700110746407020500046014100540c4038403880d508942030320815801046240000780d003c407100c2090075100740810b840c00c0c091701c001c883c0c81d12811821487c000c0501069110b041c814811215961105102401f48a525a50142500310b42250350b9103400d18006100000900c9034070401c82070143c200300140f1040701164051103c4000800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 260181942 1250 260180692 260180717
    0xf0212060a2f030c04031a061036031703010509010617060d0804080319030f0e0c120a05060106020d120b013c05030402040b0a030b0c03040503090a180b040c 69
    0x10599001404c143d005aa05210000024541e134a40d000d0700c0d54410030301140c0e030034008203100c00040496400402d21a40d01280601492013480c0c44031544049442002c0024030300c6518072011190750400383c52003050107481800501034400840c1224000d503031307200307003a82c1e1100100c1e04802c14003041c044030382d0703a403000c20a20328040c82442d15003030050820b185010756031203080e8034660104c2d82003891590407030f50343d9146a42600c04c14012120044c000d1000000420702d4984074120810030910070390b49803051901c0004200300e0b034000d017a8081c0855840f075841d0f00001c1d654850040003400007610351041d80d41d03602c066004e0b01448120603140c0c2800340e2501c00405482815103a60403810565480214012082ca100042c103451015242ea80d036074201401880103441c1f5407070b0403900404584004000107060440515886000c0b02806902ca072107626040d030440c03181c9502a548a010031002180d0380050700c0c00440c0d400711040040000c03d1110041c003040c0c0e00304c0f40840c1c0c0411102078034003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 260183192 1250 260181942 260182031
    0xd050a0503040b09101d0606011d0d110301060f0f06090e0a0902030c0a14010305010b0301060e1203041e080d02150a020a050c0d0903020910080d03090f0212060a 71
    0x150840101d034252007001c2c08040d90344045940b01010031b802c400e44002041a071401c1030025030381090084c40c0c40082080318115044036080742210190241ca00c0b8400e5000380107a000604110450040013400642c3d51101c2030402e0307801d00d000b0380042c0340d42503d000840d80e0051500702c044550700e01d0020920350b60820080c00030004da850070380c1c15000c0c500021140b9520710300d5600180c40e211364000c10040070b0b01d0005003140d00c1600042c258020030001031026a0b044170310f440c1e401800f122207040c5440006041030840c080d41d40300b021034010701142500700e509880c12100039030300d520b001c03240c00045179107080703a541d42c0408100010000907804901e07500c2e01c43d00107004d076824905003c3c1c03a00005000c010b140071500c0c1c54080000d40101030070700840c038200d81e0f069000000c2e841402140b505020046440c0c08901506509140d40d88035072408114842c002101c14039001841901c488060308005512500211614504a0b10300031500c036009410030701080c40750314040b480c9440144540d100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 260184442 1250 260183192 260183213
    0x30301030515040c0608070507020a08070f080c0d12050c03040f05040509030304021e01090b0d05011d09060f040f120e120f0a0b0417030703090303060501030b0916200703050d050a050304 82
    0xc1f010408200104005038072003c513404004d00080c801003585602e065070f104441c0c005908241110703040000c010308556104045089059042020624031034150706066900d80b00790805010103000105001401850b403154000803508140c0d020f014903660010b0280d200d22048400035071084019403500c0b03891f12a100b00240004046c1042e00d1026155070250000b81c000c09409803400340c44030018028604448000e208000140d44c00c4102414030245070303916194010a0540310104210015040c0078070031401c1a0a260042c3c01000002d020b950010407500154040301ccc0140d054010300c2c21104030009100c030385140c1d10400b82070039001a985841120902510a0311116030340010154000440002103000d0b6616071030001d5090010300d07001c2e064920341d0380714506261401b142a072058440918156010700c0002c0c0e44405020904420b584a4030010358448a01d130034500b551211500000750038013681d002c0c030200e548800c1090401c41c0c440c803440400400054052000c00c0006980340c10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 260185692 1250 260184442 260184451
    0x24080c0a080606090607050718140f0603070e0a0903090e07020c01270b120109110a110f0717012a0507030c080a121503030509061c0608030301030515040c0608 70
    0x221500d0003001300006003140e08009001d44181d00030301810060340714540041250110101024852150110360b4003411403801030034401120740242c000f440c00e950522520000d041c02e1a04028681030032100c403070080401c0201100800c01e8140c02060707904507000428441e030001d9000301086c1c41c0e800011524407800aa141d0446d0b8604c034100d075202030070150f0b12005002c940000d0381d02c811000c5180a000c403010781c00942d8180c0b52101d5950315034824801c4a0101d605810090b40c60703040400c509242060003a2400d116028001004c00c6500c010008503031100310107002400145003d0050171000c0c000c4185204458503440e42c0e0510a50041c8042e007003850290901c80329040700c3d40c40c0c441c01a0f02c840c00000000d91103407940c82c1c040545201f070151180802000802d001e0031907401900d284141e0004502c100004903c160310a8139074030182900d020489014040c0c603955010302c95883d00300303001c11110343c0070b0552540d44149400039498403d540000d0000c903050328000003034420810180 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 260186942 1250 260185692 260185699
    0x90a02070602130603050910050609010b0306032a0307080106051e1504030501020901200c04050a0e0703060902090c180f010306170d020712051e070f24080c0a0806 72
    0x100702030340308448110f240002d001c41e03100032407145044180c490410031464112034100e0f1030201400125141c09543c981501c044194207503981c2ca9040003e86444180c0d480d641249880700322018640e0914540c018030f00b4403e0307080300c1c0c0040c1c60701101400d03501c01c0d00450b034000c0f200d0060020060f040e0030400300390740800350034aa142001c0000b00c1e0519405a041551143e40010b201151035a008002c0d10b100d00c41540e8400030a0303200202d107500da2100b1040f480c4229103510201c0e416020940c0030302d14240a0b03808495001da5249000c0019007160f80003a445400c1000000e8400340d01007046038407c4281080c14044076208104100c000d445800c00181015039802000ca04401500c0c1101814044240280040803d000000f03180010303640180b51892000300c40e003030004800003182021407540c00345905000f801c401c035075841c1410991125404504c581c10000b40f19256000f124641003023808407640782480120300b51215075003504c1d041d00070782042080b14405407003159200d41006008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 260188192 1250 260186942 260186947
    0x30d0212031f060e190302060313030e280f1203140904020301090f0605040e0d03020c0a021f03050106030203040201050901030b0112020f21040f1704360b090a02070602 74
    0x4010014580c0b0560001c0000c100c02c0102502d140c503241744441c400380803d12984c260203045a02003612400050716800070000c01d02e5a007000c143c0241d4950384c1780714000d0003040400104c03004942400c0c00c0c03c014082c071f62084000115264480185041c1501c0451508005c8840c80d581c0403108001d8482d6103241e985014006c0c4462030b0b9460000f1802402011000300352101c280c00708108681056200303600c25486c4c854001400e0002040d125000c1d102404c0068460044500d140c0c148090120025403000d45000320b220b038405009105803502221303035020440d03a0f0320364409a0491105480280c0826024840d0040e65032198011005805040c0b41c4180c80b50011a01142030340c020b040741c11003822001c070306011030788aa9080c01e0120f02d0180b0340030025007401d48420000340302070761018141d54500200030400c40382e1070701160000c000300e07400340b1540a0381001400940d003013480440c000a58103202011012154007444034800002054803030551280e401c1c1a00030344c00110304072000d6809 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 260189442 1250 260188192 260188231
    0xa0e1912052109100c02010f0c08120109140a09020f100201021c0b1002010b09010b07021f0e040606080403080f070c080408030d061d010605030612010227030d021203 73
    0x180e05080011061a60b515a11a03184808000da44404003c405081000390b00d07503400544c3c1d01120340c03440b5582c2820140900b802606141000d8426042c11150b0469030000009041000c6d502580d124501c09074100700a858450141c001d4800d603081c0607500c8400200d20307020702d2a040629521003845400010300c0d142d52511240e25501d1584104003001e42d80f9010810319060841c500c5801103400e2008014201c2c0c3c020018130103001c1070141c1450301d0000309500c011500d4000c004e80c04051056a042080b415082d0014008020030603e82e0045040c03000c0050780e82c0c0200412401164961580166607840f000d414041a0b801001321007004030028005010860100041010346411009107649520150032032040d60072560010100000c0c3c2103080e05040500c2d81104e0640b80d06142203552500c032000000c1241d104030041c10300da9403000607082500019450688681404c0c017030070041400042d0101034452943c0f881e0034016801011340288110402070045910041d038040d89280c40c0e11 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 260190692 1250 260189442 260189473
    0x3081b0604030c05100204060816050c0703060e070b0c0a260409060e130206040605030603071716170705010305061c050f010b0604050109050607060b060c030a0e191205 74
    0x1401d54090340031030400315464052010501c102c0d070080c0d040840a601e8540340030f1000303114100c01040b100703140346031008500301580314500300c0e0880000c80040b10f017815164200307000200a15004446a8810f07003c2c00100d1040301010b685a0780320ac41b01400e450800342d281e503000c8070141d001f844030303010544981030540b4000201071304c060162504005940c42c02c00d55404017802020700003207282c2c0b1400b0741000050740c41804070b07400e0b40e2039894007a03201c1d00c1d2500441d11b4841c00c0e811a440148000c0b1a6104954001420850304808462181c00325030380d5030009408059078034410031568005d450284080d50198000c1500040701406050060400070091a10794508090496281c0c002e1002611040e40900881200d030303c0440b1101e20f0149041c00280502403103200e0607004000110f030308814009180d101d107c3c44c0d18003429056540d0b0782c4007442034903a40480707a20801b02d0300c40c402400487c140325a0320404c1207107403020155020300f02410212a804049000c0301c0d00c0c85104034810005030f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 260191942 1250 260190692 260190703
    0x60f0c020115080a02030303061504050a091e05060f0409110d0302030306100503010510030f090609050c1801030f02150712021c020115090f090605130b0603030c0703081b 75
    0x1415a0000480402c8030805808492580d80703c0005a0302c51990040581c0e008003c4070380140f030460b00b141c813184c440314a01c9c0c3d050155a20240c9d0103c0d09020010f00440c054118021121404482c1082d40d080c9111031422100e0a0315600e0f04400b0540905216003065440b20000302c3c002d0351500c0344605224005290046201e80860040e00003100f417240d9401d014802983c000080e06002d41190b06100120341c03140c3c5035105c0d00041644645a000c42d28490380d110203000380c3c01030004e20659407c0e00b081c03035560303047c0100d50b40601d2640d00d031491064010690203040e240e1000131007030061144d4003000b8440300001103051228004000a40000d01203410380c0c031681d803503030300942050000c03482c1001105c040c1c4140c000c1564100910710050f062080c0d1800142c0325100000038145038001c2e95500204060100200014a0301c000d0010281e2011440c59082c0c1c440c9080083d43d91312032091540780d0007886900e2070180d100c00700c2413000802c004050318036203900701803050310300410300102850074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 260193192 1250 260191942 260191961
    0x18040b0402070203031c1506021207110d0b0414010603080d020306030c13050103050d0c0807060e030f0a0e03060702011419020d02070803090c040216031206090e0d120c0c0f060f 78
    0x1c82c40c1c1444404400d10f14003900c40154449105102a03070708e03010003c1e4a0307c1e003008995280d000c0004a0100704220380e4031001040f0f0f00038200c01e1200c0480c0c500000242815076064981d52442e4141c19082d480502900045c0ca0344038003168140345400305a60007a4001808150b0f0502515074600d106d51a5000b0012440c0c04039540070443e9451420f00d50304052002c90480e041115007110701011171100b9089400c100d0340708000141c001d000080ea20704601500c1d9aa44a4a9001405a031055440038220001060072002c5c3d51543d01c0303110301a402ca4900c20700003082c5100303420008007940784030b1294007140c00f4142405841c054201d5494800c9030711041e01140d8100d408802d0140e9040c080211038510f94081d034086141c42d2415480054003446920004c080007411410f20305580c0e4242c100c080201031800003170280c00c008c42070058807004485801800111b4000d10b06010285a000d4a02e148515841c0c222212203242c541c0b030706050015006a036503545610380060141c41c51f229003240c0703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 260194442 1250 260193192 260193217
    0x80a06091110051806090d0807170309070801150e0c0c03070c030c090b0415092301090b030d0f0e01030203060f0d0501050709170d030b1207180608010218040b040207020303 76
    0x11070002d100b0425010030900b00130350003410103024404164455203800c40b807058004500c0340d1612160300d0b1040090140e1045d40d013001c1d502100740300c40c1410000d46401a10381d80402400000034150740864410824821035006140030008201020484002004c59401c0102070720302e40907840e210390a1070385c600e5008a503c0c41c0700d404100305080592207407210040c41141c0601c41700060540c980302c000840d028411080d9070350b00459200408141c2940038890003440a80555a52409580010140801160f020780a04020190b0441c03184c0d4980c0102000c5031034141c40207007038500441c0203404c024030b2950081311024414109941d4052041c42092181d00041158545881c00421519803603121201c0c4405845141c8491140415002002040340c900002d280100d07034005004d5407080c072421070f0107001d0400d0104030360066a011101501d600c06091020581d034106207400c03031183c1822042c0d21a1030555010a03850a43c0212401e184001c3c0054100a4070760002070950740406881d001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 260195692 1250 260194442 260194447
    0xf080d0804050c06030402310c0302031006050a0c0609050f0d0507050604120908011b11030a09120c050d050706020d2c12010f060311030d02071a0d05190e0106080a0609111005 77
    0x41640240134000e44040d00b49425403ccd414600c0e1034007181e481601a4a09100020032a4059035220700f070790202e07554009001f405210076601b0704c2c44e111400d0884c4c2112901451118a950a00410448411591240040103a50f03155100d0681c000003400c441c0f01006414000003e101c2c3d400d020b50750300c0d0038030400f41c203203034003808d034005003c0b0f1200c2003c240c100e4000f0300c250404290004000d40486010030106210341e030141c9400052208141c01050740714102c1d0b1009002c1c4000000da14082d40c00176001c1711000202580141c07101c100501c01d00c94100d4200c00000c2d01300b00e0100da800075404c0302421180005440c00304840c25a28004208a112a9581c1d820014010100c800340c41c1c0ea030040d40a0042d40340ca03980020b442d409a8003d0900115113035010187e40b401000c11245c0c0c1103511442003000d81000724000a43c0158080b0b0070f011582010340103106131030103214020071220001c004140c0141c1c0ca50b10b0001520070244141e80c9242c5103044000e0a80704c0c9103841100ba83ca564031141d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 260196942 1250 260195692 260195779
    0x308030a0207080729060a140d0501060605070b0124031a2706040203041703090a0c0303080114031b010e0414150117070c17130f080d0804050c06030402 67
    0x10510031a25007a00f05c5d800a00c1056200c203070020041d40d0380d40000c0221004540b001c144107000d4554005d0866107440000140d041c0d01c40003411090f441114800303040d990320080d9100c01e59128001c00304003450b400c1452080c034007a50000580d200703400130000c1c0842c050000a0301e0402d444008082c102d1800340e4510360060f042c0903981e48082c04440850a505003910342d00780c040b0003d64080c1c400ca9000001c141c2d01a401c00006c010940e0040c841442541c8901d80200306000a21452000702403129204500f8034000c80c04542080801031101c1841407040011140140e003107282982013555150a030111000c2d15040c18410044000d489032183c8600000402c00715805d452101c2030a9100d00b44107100d03611408213602c4a403c24100c50b046644000351a90754070405010b10740d68502d150780010461145150141221300c8007060300c1c40295002d006403104041150020010b80165494203a1407804070b01440e0424000b4012441007100004400c1703411003000c0340786407952100b85001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 260198192 1250 260196942 260196983
    0xf0412020f3a05031801050c030706060f060c0b0f07050c0a110f0901120b0717070f09050f0108060913080406120501050a4203061a0909010308030a02070807 69
    0x2040401d5690703140350020007507521480d80724064600903482985c54600c1e0404660b2090742901c4150b081034080d255103e90b1481c10310020f2800c1d10400702084c89840c00025014014040d188071b158000d0308200315a500c44440401c403a2005000c2c9040c0131040c001036004503010015582682d100d99240c0e030100d003040082180402d803900c0311034440c2c0c5038032005200954501952030049503008012079a1916200010b0355061008025001200380b198104603000f944200c40082e08107440d01c64605550f00c501c20302402074160000d10b40822440c00c0031585508101100540c071100d82502c0c0f45040000d0b560340c10b803d03130069000000248100300741e0312556a481c4142401400b044500401c8a40341178180d20881c00030145a403c00c118075941321140400756202b40703032180300b00b10400510a28102015000f440240a190b0400540134505090034038944d04841c1d20002c002d100905a80c41c694460420703500c000c0100c4442a000e00c086000140b003013024204103441141c0ca464044080d00c0030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 260199442 1250 260198192 260198269
    0x230603120c1506011202032a0f040b09040912021e0303010609050f122e020a0203030c0705030c010c090819020120010b18100801020f0412020f 63
    0x600c40c60000420189a0010300001e90300c148404001000b03000740e543d00d0050f9400d42d2000b40e0481032900020811030041c80108088601044004550309220000070a041050141d00700801640e04104030600c001200fa4000d406204001800458082020b907214a9084507404c0d004025070301198060140c0f01c0340c1800d0050309031a69000314110341c0760010080090f04540703e410700030f1080082441c0c03a0f8460300740a02e00102440c040706d070828128510030302220f0760198504e0000d1024204001890700074002c6800050141c0e00070340c2580c803411741c80446a40244803c032914802000581402482030241e01c0f5103182d00d450343d582c05450030380c5c014180860407141112600c980c1c1c0082c0c0c0143c3c2c01030061b0050007280f00184044010003421180180309000055a00130b981721040c80090022240c100d02c00d01c0c500120341c8645540b0008582030340110000b2070008601440705000398924000d45407030480c00100300100388240d84000c61040300340d0019101c01d00d003400410300703611200c2c1c07100c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 260200692 1250 260199442 260199463
    0x1c020102040f14030604080306130603030503060414011203050306031006060206150102010c0f080c090306090105070f0c050d080c0d0507020a0b0106050901080c0c031c0501050f0f03100e01230603 86
    0x1580a040f400c104000b94503410020b0000348a1000071011501c180c95412140342303990031345d9404101c81c039200e0501030403d40040300c12a101c1c50424080509580c885c8501c0c60480c1d0850b000c0c03444100b442e40e4140c490f034100801b5290544180458402c2e10159405048000c1c20181c01901150800f042491a8401160349042c156810600c1001ca0290710142c5005d00d0841031804002c1511030302400c0c20b903403084d10300007a0b2512858051002240065002c50300582054490600b0010740490507100f24900c141e004d041ca41052515145180c090004140d00060100046182c891060224011980191a042d005a20020034034041140e02d10707000b405411641441420016000b000030409034008100c0391a400c8003084564010b1400c000341c907403960a24030074084d58a034044070100144000d110b01d502c01c110318400400c0a007458250080b1181e4042e010b821420401c0044c40041c1412403400d2040750350b60710308010010115030301040c07001240121015107040040c101440c01a4100c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 260201942 1250 260200692 260200709
    0x105040204061d0f100314090606060406030e0c09090a031403060307060c140106030807112b2103091401020306010504030215070c090b01030f1104050f031c020102040f 74
    0x34401903801101d0200c26001c1c40f0300000a070302200d00464810107036205a00c0c0c12010b45007140760701c0b503056040b00c03500c141072440452050343c42c413611566409050702d0454000208200a1000c20f100e50008400c4541407821186446138800104d007a054086524001c1d94024111404c1016446461601d1300e03031140d4011030442c14410b00094480850340302c1c0800344080c49254034200714581e0084458840302400070494180e4a0401c0034060f80110402c81d40c441000000f580d40d0300d00044015500c0807510b11103907200040b0600c810789821100d409440d511070340b00e248565601d603c1c0c600090b041c43c40c0e602003101516454043c1160701d45ea01c0402c480c0e4018400c0110a9900c181518200e0341c049032400e0080300f80c070303107421194882c020303000c0c114402000000c156032402d50800c9072001e01c00c0e070b030070000d00e51010911000c440e240030001180e280200030410042ca800030b203580c0c43c520028103456a40020000010b402038400320400b0160750007007000c000e265040d06890000b8010031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 260203192 1250 260201942 260201947
    0x10030209060307081c1e27080601090e011812170408070b100801050108011409030307080a11040e0a0609110c070603021605030703080a061d0a0c050f040e0f01050402 73
    0xb070b0380261074614032680641c1c0d001c45d040b144c101c0130b445089505405a0807039119540e0f0903145900503d0711000b10100381c10800c0c100c032021000e0304caa0b990b101c11a001c1d0000340a0903401c008881c8003412041c16200790564031940f80c5d00f405031074020901c40061003020910060b080710720b40a056003071158140c609100421080001150801c03040300c403080e07401240c411160382c2c0d0b441c05100485950b004605ca130b41c600340000c60303190300550120b0754070b242c40020709409964829443e0365a100031644034000a240401248480455810041e01e42c2951040e841c10561981c00003e0341c800304641c400c85680c0c5400302004268120300c02c80c100d80c00f11111030741c540030031100250307a1410b4a00c80d410805a0018500001c44503180c8590001c07130340507065aa6442d20303800c000345243d10980d5075252580c0341102c0080d41092820141e0324030540c0c814120000d03038910001c080144100d803c8803003440707010400c034001a8000c0c2c00a00250805410170b441e54201040c401d401c0150503040356010701d104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 260204442 1250 260203192 260203199
    0x21903080708090604080609030306040518100f0e01180212060601080f07031107030c0b07050315010305130221010b01050a0e040e0a1209092003191410030209060307 73
    0x500007150300c140c0d0802c00c03607990f03000080c000c10b81c0c520540d8000c0c1c03014054907050020500010001b10702600003250f081c041901d51542e1011000084818510070342c0c06048051455003840e0001c00012071003c00014600d2200c188150a4031404c0c030360040300403080c0c0d0f450000c514050a0001c10480c21070010300062515100191103000c004d865108070001903000190140e01c603800c00c801c42d5000d09600340d100d0711a8513018181c10881c3e0401c131075041c186000903030290710403001d403403150b03a6008034041c5070030888006400801000d00b00c1d010300304c1000e1300c200140e11138807480065140300d4014200d880c08204e807882e0865940d5a2440d04005081028400ea95030103660100480000c40d00060522201001c45c0d1408404450013028400e00c080981d10154200c40701c0011035100344000d0203440aa22340795140984017a40030985240c0501c0418150f0b40c0c00c1c032408546005440e000100200c1c0254040d0000c0000c9a4038031400007580d80070300031400d10f00c0c14641c0002040d07004190140c107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 260205692 1250 260204442 260204453
    0x20307090b0f13060302031212070201090507170c03010c270f0306110c0d030629120c04030c03080d0b010806030604030807030908040807080601050d031e0921021903 73
    0x281d500b040d51048500c066402c0c0d80a90540c8841c0007540e00904864041c0480c0499031816000040c1391004108240c0c000380030140180954100113034403402401c1040d080562081c000d0104801d001a64401c0c074009024a4609114204035840311351614038180200d02c0c1100750242045034244044601e881c020001440158280000d07254000c40202d184c0c001116400307814024a0207001d124070032146681740c030507015445101a00d900107610201c40784062800d04d903c0420203100c4c41080001c120540042c0c05112099400c80300c1142860b180560741d84a003102524140c006441e1260001203801c0040710a00c43c0c01c3d071400c403c1c28071240d14904140003c0d120b2000400190900ae02e00b40010102d6201e44e0140c030360190310140c0c03a910b0b82d0700da11590303039980075500500c6203900c40c100000c151392500c2207030b1590080e0b1690342e66200082680302081040310b00e40756034080c0f0281c20350214802407086041600c8452144100c1d224048500420012401426078210700c1508050144007160 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 260206942 1250 260205692 260205709
    0x906072321070804050609120d20040303120f09020f12100609020d050a050c07031b020d060b04062306030c09040203090f0c06040e0601110721020307090b 68
    0x102018405440d140c403000d0310401412041030010750020141c0411600c036821054450045000d42d08a070392542d14980019520030304020400202c00781400344914008460b0022044403207440c05843c40c10301540c185881a422503041140450a200096103a0300c00341d104d5500d460941c100c05204141d4160003041d10580c10a4200740540130104900c0c08840040007040011407180d00100021540c6101800080d00210640048035041c5004030780c0002503409001e01610618400e203283c9045a40e0540300040c8040c2036179940000504981c3c09a9585444198058001c06010420a0703040c0100400c81e6015001040700c524600710003180d0026800011207032110642d241c0c0d940303465141d02d803040384c010086044d520a00000c104000031402180e503075210802002101d4440d50700504011840c061400788880c2d04110300005245984a04450404040e0300c01c240c0708010b131614031400c409012060010003d05c01c02ca5640304504042000c48010086490200603031007200c030008203040e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 260208192 1250 260206942 260206997
    0x804150504150c02070819030e240a1707090305060709150f0309050a0606060221180111010c0305150d0b0604090203070806070905011704020a0b0f070f0b090607 71
    0x1a580c070040488204d00811000300900741280c200d07501c048010302e82103420300307188004800103080c10000da0114100b40b82c0802101440d20340740c4d0340740304c078120700003105030401b083e92010841104842c0000115030b5410030f008118507691031481c5400e50a141d417501d04040e142d20204484040c08000185480500f4441503c6c180303030003020880442002c9002d4110603002034001d00415821408003d0554007000440790301e07400796401c5060164106e0340340c0348905c21120103090f0030491454003c5101883d07001501c0141401c1c2c40d100000011942120011418000882d60320000d110001001e114200282c1804441c40544101d1590343d480080101a21480c000c075150450039007150340911255001e4280c0c44c049407068a0004402802c100152044c0707030105440c010500603059840d000305d0f01c100d401409403149181b524a1810065205d403800c2c08007a201803049100007054545210401030191030055242e0078400052410401c01405d40c005105180380c2804d243d007804080107002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 260209442 1250 260208192 260208233
    0x111806060d06030c15020c09010803070b0712020705010b0a0b070f060911090a02030a0f0204031e1103030d02030604050a050f0708060607081c06080708070e09030c06070804150504 79
    0x44814405041d400780540e5080280801010301c00811a6044d00c544645502d001c0c0e400ca0714424101e50174420950703820300a036042d5410070044580800c1500c0c9001d500b11030036141421103100d00c075a40c0005c0f40c108680031503842c1d4494000681ca440c19405c0c0308007802540402c50b1501d0200e80d6400310802c4c1291004003100e4135034a401c000d00802c1085003000030000741080449140407044d020007548101c0e03000c03005a103031900d40a4416620700c00d88054075400a554464001a00404500d81c1d0154000b16a0068819150181610300f840a04003060807140301607100d092540800c0300b5a4001003a5012141c83c1c00100220341000154082e000000390070040416201e11000c034050340300300b8102070802903002690300711815580150a4614034112010080c403034480240d19154282c42c80349401301c1d4072244090220014000b821038208007090b013124600002c4001c40742c10027400b00c4240010840240030001401401244211a0710698078100f100d4906070340e807500315002c1c55480000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 260210692 1250 260209442 260209447
    0x10b0f060409091e141207122f03070506010e1b071e03081e0103030e040b06040f0b030711031e0702011205010e0703140606030109110403080409060311180606 70
    0x6002200b105583c85190000780428503c1d0241031480d410400e4003c4207178107228501c0614100e082074015500c0b240d034040c05000921183c0c40c42240c1c000603811100c181c13908865114004146c014031101e2000c182c0714080e50721a80c0d241420b41c10010141d00070380b1a044d6510400c400703254440c03000d0030a0b0a505502a86400c1d650400304d048405100d92585c448810204000c241034204c1c00961041400c2c0d0003550200c0702542c01a03440e52402e2100a000c00c2e02d110344244240f8190300a0400040060039590420740e40d9000341c0c604220f035500102341d12000009010200764024814000100d801009616000706042e840c4543d0f00004040d540080020603048110784c403d9602001c0c8508015060240b541c40f54460601030394240e51440c0800d1030003c00d26140316614200d41d10a00c401059141160b19020445020340b4502d088940354500410020000032a51406800927020341480060b19a085103014a503071120800035520984c000e4a503400110700003d030071680302d902a0780b402d8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 260211942 1250 260210692 260210711
    0x608010c110d180f0807150216053606151303110f060711040b0d030219050a050f030403060b06070807020f12011119080712090c15030e010b0f060409 66
    0x78120f28a500107024a201c2c0b07080000d50641d00241040c141ca4042800f030160540c0070b1350590b40c03041d0340b4040041003240b000c2d08020034a05108121514414514061805200e516089241d00301e401c000c0314040c410b8000740101d82c1025096075070300c5444101201e01d000003865210b0451a00d80c4001000c189001804210320744a801d1500c420080c0900f185460b400759140c141c54010b403d604040c040c0b80742030905130303480ca0848000e044080e0903030050020358048403c03000001070001002c0c0c5152080b842880c000840822072004110007100145444905510301541a10700c10b40806110783d00a00c603041c0818000070484142c00d81c111400c1c40c0d206210350104400c460705e550000d01d2540303031500150b030101c0290000c0c88860140000c03000c411413440c0701540d1541040e070f40c10000031207850b038074540e03000541c0c49450038501500c200d00c000782c2c3e1240c1100640d4500720903038001907103070680c0c00d02042007401600f49101c0100d03a2807030104000000708150380108d00c0f503100711a440c0d035400d6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 260213192 1250 260211942 260211977
    0xc110304150e040c0f0e012307050a0812090d0215130201030b0405010801060501081b07030c0c0e01060f123602130501030b0709080d030b040b090a0608010c110d 71
    0x200703490607016005002002e0102d001904801c2c5c1c4420000100300307120700c900c00e60344c030481c1c4001c105100d100071044480003144218815400c403c404607010b1003000320070008500c641e00540350f030403c0c41c000201d6500c0d010748664203006a0528075000c0d903010308004100700c400040078960000b1301c054203400d108000d0004a01a0a00421164100f4034040010030081410b41000054903402e0b2100001b6848000c8680070080008546450b020340501c04a40001e110700214483c42d800344090410b1135440d98001d01c07a060342070703000c8030200c1c4c80f4140c0710301e1042c1c0081c4509040301c0083c0c0108184032050f15035001c1c411210070103002c0310b40d4030781c0b240c1411030304041788400c2c0e0b51700980941407160144540c0707001000d00303010a482c2c401032200004c46140c0708203801c205503503219014101d01601d50b64190087c09002c181c0036445925604400b0f85a01d8180d202481240601c1d4080391842c90131000c1401c507080501d0000402144100e2242001800600c075050170400b403802120b00e511a0841 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 260214442 1250 260213192 260213207
    0x705011d090a021902030903060601030213090e06040b090f0601050603131e03020f0f0d050d091401090b130305070b150a1d010b161103120a030f0c11030415 69
    0x4a59100c201d050521005070750b81e50151010700040d07108424112007640041e0b070360307000d0400340c0f5506034400d00c001580c40d403090b00980f0120240100607202c66441e4607016003a10a401511009680301d40d040000f8440c0604801b5080202030014207000c2c2c0c907100c2c01c80e84800b01401360034001d003000030224040d1007402c000b5011040d04800c0245c1c940350050914550240c3c0380000350b0040c17207030062641c000300b80441e0031706603400000000c2c010501c50400c103691300c0c0c00070810062403a035140c03500c0000c510401c40105072444441b00000312011140b50052003c1001307007007404030900400c50400026040811a40b00036084a40403030b6543c0d800c400c0d0000e0424040d003542d000040c1c5400011455000340d40803840c0c4941449848030750f80c940008070024061650352940c404840729000c008100c40c00c2d20046189400360598418100703143da145a00e6024604580000e9a1400760f500c40d400f0703c0c031440101c1d05840c07406240074000074503225901d000700c0c09034078250790140e800b60b054280140c04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 260215692 1250 260214442 260214497
    0xf12071706011d0a06111002040602190302070b0d090606090506061806070c0b0406080a1512140123060609010e01080a0b030a0804080606030a03050f090d080c010c20070501 76
    0x344d0f070010703902c440004003020303486040b03a5039510440da0744402078403050003628191605a40101801a4241c0c1c403c203042401910a4095000c2c85101043c22400e010080083d44810000401c0721a8039180c010300712a5141d01c001c400d14981414030400b5a1414202d81c407200c605000f221400303441d000040c400744520b01000b4054504e134440000c451203183d0180c011989180c4545101c2c0e96020407000c2130b80e0104103640c078060f825100c140421180d04d00f410301170f84d020b001c0481804a402501508664070040c1c4004080d0f03400c1e00052010300c255030b07442d50014090359100d0402e00204006000074143d4110941405a1140000e50711407566010720f42090b0f005040b10150341c1c5504082c4096441409000898024036000410342d0400250b0390b80d000c0e80c0b5a848a2404044500c03083c400e421110515510075040c083c40c9001ca5804e101601c003441c000300002406000d06080a403180310b41003c404003d45840f0b0481c07010160124136881160401c1c2010f1000c0c00d28a5071600d8218507810 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 260216942 1250 260215692 260215699
    0x4240911190f0303020a030f03020301210819020303010f0501020c090c3f090f0c10030209030106090f050105030613060c09051002010501090b030705060403260f12071706011d 77
    0x1000000b03060340000c0c101141b5010303440b6a00b0300c0a840d0320032000d0744824000c030458040e10040c08031081e11410880c1c1203842c040d400e15420040110380003001010060803103001039002200600c03c02160b07102d4031004001c01d000a14906401d04041000c11a00034400c03907444102040140740403015a040c40384c0c9a12078020300103124080344030402d14801c00340403602842e01d075600207101c074000080c1e001c84501400d0b000380400c40981c001c000d5807415035807801c804c05400b44070601c026282400344c040a04400302010403000d40e464003030011104141e102c50300c0b80c1e201206000303214100703905190038150044004107080d40555001d40d0b010002d54000d94000442c603154088a0b03506500c114145d912014040c0031030480ca40806503a4038940c09050b038891010441040000d007007403508444200c8581e0310748104000c0844190ba03d40203a114061b8001002072081700081c3c01c0901164020500d0420720840404141c581c54050740040095050001101d5200000640740014050340103004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 260218192 1250 260216942 260216969
    0x308061908070803040321020613150e060103020405091218030102090a061107240305060d0b01060f02211204020325030606090c0203030f1e0424091119 67
    0x141c3e00070360b0301d40c058072042d100c4900c120b400540311403050584054800a81e070003009180c0719502462003060720500d003201c1030f6a048008200d02c00c1c440c0592204412110050b041c1c56143d4018002500c400a2003007400d60003414104121a6464040d00c404100401c401c103984010741002c030340284901364803d6400302d55580c000607a03c1e40f10101002d68400402503800080d41d501c04021b0310b240ca070480c10a90741c0001581c04a142c070940c441c940c0104010080c04840c0c0302c9840341c0002003c00c1c0c012400060a0201c1400102d8040041c814559810244903041400220f58414180600b0000014082c48003010030b0640d501040b000c1043c040030941055450b15029500400e00054403048581c0b178182400082e2820080c4113034454200e0540142d855aa00c054070b19802560041140468600c1d660004500708400040d6030311a0784140016100038010b15800c021070038046040e50f045904101601000032004014460010030540d184410ac446654038030311625103c2c1c210b4500c00000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 260219442 1250 260218192 260218199
    0xf0c0e0c070510050907140a0b040308220602100905031c0c020f0114010302040b0102071d071d010906030c110307050a0c1211010c031b030806120109030806190807 72
    0x800c01401c00a00c1074040360000d400950708a403e03900200e807003400a03000040104400c4841051104150000400c0c3c0c0280d11785502c1c020351540c00c40e030020b840186d80490181040c403200311348854520b043c0c3e0315140343c0b9480c10700002c0d9100030641c80e000001d03403a4030f105401c1102c10010b132011140c3c07070300656500c0240c071488440201914080140180b1440d412152244030600c1800707444100368070303071069980c215028400903224001400741144030b80328001400b540c0441b0090b104494424100f046420880c1000340811420711002d4a5079440c0310070052260b030091b02d8581110500d040118520f9900082500d40c0010119480814000016100301300000855010585032141e00c200065075200d104803031103a503141d50020b1004401c00d201298030341c000d219000190b4481c4c6403040b00394401402c4807407070307602240b4214007050081041c0305052030144031004503e40d105008008000d82510300400ca000b019005c280200042a4900140b82d40000c81402030700d101030445a22035503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 260220692 1250 260219442 260219461
    0xd0e010e0c031606050306060a020a150f0b06030c270a0603050115030203040302032b1802030f011107020111070e040b0703050105150a18150f020c030102090306040f0c0e 75
    0x40750114481d003d01200d03400404002c1112034140d8515540700f1341187d40e82400e0100710352017503c000082d88504a061000511344c2c0c0b4031110418000d0b207011a40111212540c01a681c0c000b46451007110284200012008048240d0b07542d44083d40560041c1007030550300300c500039115102d0540000305c00340d022030b200b909074100a04031410004e41c0c000418005d0021012400300b61401001a0002c009070361441c071580802c15103004500094800004030300440c581118600340007007100d010100308000943c43c2c2030000d401e4024029009000346450300c161011188182c0300000d040c010103000507400104104201409440c492241e51164182403c01c407444003012180320001908110003c00c05044c03400c143c010303a4442c0c00100f428480b1040080c2c80161a0392006500d0381000c00c00060750b90741500c01042a282c05456080600d4610b14000b0b0130b08903041a8540644e004000c01e000c0e1751000038807558880c1d0840c641e55134000880c81c0c014001c2d50310f503104810741c9813a481070009040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 260221942 1250 260220692 260220703
    0x80a09140a0516050108070c03030605030d0c110d0b0610091a040302270103080c19081c020c0601140d0f0507060f3002090a030c0905010b0f0703050d0e010e 69
    0x180a60b084a00c0060f103076541070181c090324021343d4001111603000c51a071a02400407102c010b4031904021460179229000b20b45050303011071440b80012141000d08080c84801404902c02d28010b80b001001001c3d00d482e041686c07040600810701402d80356004100b101e201380f165802a050615020036801045400000e054009000680c401d00860344929440341c0302561110510382c044540d000660701e161110191500700011800300e03030141c0801305d0b0405040c4140001d08500c940d4920b629901d003c40c00f0402c0c06040320b01c0000e110b104000d0f985058000007a580d04507010b44202e21250750b018000b0420125441e040205004c0e1001800c5c020000040b440300140c507490340e1180540319400344115108000100003150350181407240304060840140f10965a95600301c0152030081c0e00740109400130043d07401647c41400000c03040c441c0b132415000c0c40d03005100e105025400c1c6000020300d6810380c0320f040300050601800048003411404250406000101c0c901c0c000c1103090001d5201c15101c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 260223192 1250 260221942 260221963
    0x130f0305010501051c06051003050d081807052404031502041802031306050601090506120f1b040b071106040e0403030e0f0c06070c1707091401060c03080a0914 70
    0x7542040c00100e1182018604407040f03945c078140d08099a100d9071540c42c01400007400302c05a2031040307880800030900c00c200c0081484042c2d960300e20149491000429911150a0f000041c0c1e00f0110040140ba41c99801d0006081348010f1612203440c818022120f80e480b4540c00141500350700c0460f040c5c0824541d002d002200e07004a404060381c91080c91141c103e1000b107401c20010400000044081125503000742d034414010b0403c01d0101d6102c0e400201141c100618402004405000700404603124403c803a400404085d803800b00782009200c0300203207025900801c904c0c40000326459090180055032010001c0340600714650b81c50f00c82c14080500c040444054021074106454494000c80000e41d084486c910000078101a85601701040019400030070156000e84031002c002c030715540c0f25640c92084140c0d550003031020b64501141c4406403040064014400340e42e43c801000030030703082814500c02c2e55240c9480ac03181e940b183d1a2400a10780e4280c080c00e240f0801880720380c000030010740303030020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 260224442 1250 260223192 260223203
    0x606140c03160c090b011b0807060605090c0405040e060412050c0a020d0b060405180606041d06010f0f0608070e04021b01050403020c13180618061103010f0e07091505130f03 76
    0x98680385c401925a010b43d03000704940c40724188010008104642c026003030303280c4200804185036a1321400940e4144040e2007424401c01c1c0050704100c646800d102d1f44060340e92170000f03800706103821b1f04c541c402c20120001d00001e1110010b14000f00c20000c0c031200100c6540208480c0125405090112100c0e80c2240d01602851030100070500d0501d404600e600040f030184010000380c0c0d912000d000140c800e2680c901034845d003113080200200800d001c00e501801d44000c0c500002403070701800b40400110b6a10810070f02507090f0034004032603403080c200c135062482580c02503600c4241001e0614070a10040341000c03607510700b6040c4010541e010603840380185080300c02402a00301c040440703080341c040e0328942c0000081602c00c80700040094001030440c41e500ca130542040010b41c0c45038416941908038401449030000010f000c026080b128410107086203601ca980117151081000e000c82441d8010030b0b112480c00300b02e0350001440b890440312500e50b07514006580c545da81c3c0041c94409035600080b900c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 260225692 1250 260224442 260224451
    0x150106050a1b0f020121060306020a0215040c03020d0c0503030d0b0406061706041d0a031e050a2115080303060f1210051314030304030e01030606140c03160c09 70
    0x48564126050800d82c5820400300e2800a103158010b490341034170b0321070405c3d10b4841e52090200682c0548a0100107502400015035645c043ca200242000f01c01030a042004001d44140404070b0010b8000c0c20540307506440c425810035240c280191111a140e0209505202c00255100c642c500358004025594060f82c0901c49a40c603207034103035149100700c0c4c00864242d00070320002d1035500d0300d6000340f49460740500500680d0703080d41103a20704003010141c0c00e0b00414400035802c0b0ba8802c664841c110001d0252825509003901c00358010080d9407200d20360843d445460314440852109544446030b01c40303a0309610302c451a034821110f03031250022903004e4882d03c5580402002401c00e4802d4a01801c0e01c031000c0d011009980d40518010000a0081c2c0745041c0b107407071208000740c60115010302e80c002e00401180c8a2806180c014088014111200e04040c21300d00101704042d0051035000c51131083c6201d054407001c1904003170b450750154403003404070300c40c40d030307103080306000c0400c3d00343e0151026540f0030720 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 260226942 1250 260225692 260225717
    0xa030506030607020a030e040f11041503110301140310240b071e03020712150e1219171008071710020703031401030b0610090b0904050702150106050a 66
    0x648030b01003203030400d000d6001001d180b00042d200f8001c51411140003000041c106d0843c0c05894200c544148800550313640c005000e02604010717041c10590348040d03107400c0c000b0380544c030f02100d41800180328505200c4a103000040003640c0600c15800c1460281c00200141c0c09140340100c400b043c90060703145c85265201c0c2c049045c80d02401141c50058000d80340284200c1c0041c08402140000c0c0c0056007180034001c004105964401e100c89512405560540ad506180450700e6040710b404a00407507181c2d0001c442e440510030300c1015284a9400c19014a40302201000d040d01c0310390906d503207480f21980c0b110070420f1681002c4124000d0714040c1c401c4031102ca0310341c62241017000d4800b09905d6941c1c043d04040c0d04100c09900284036080c420303d004141000c80c0c1c1d4021064042c2a001241e00881d08000c02c807072402d241c514400c400ca1580740005419107000740d01010791244d0784001e0700076901d620000722005d0007040040400900101160019a0340d200d000749036402640000d40085c3c2c0011142c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 260228192 1250 260226942 260226949
    0x11b0507050f0904110f030f01020a030b0f01051201050405061507060501171b1306090e01090302010e011808090d0803070324050f010315080d090801050901020f0d0203060f13020a030506 82
    0x3c51040390f02501d2803841040907410000100224940c80c0c0d07162041e00710304102c40000f80050706044100c2d80b404658010700204025483c001152024100300e801d1103000e8200d030b40c0c1c54039a4110395095070001801c0c1c0300d000105a420017043c10041a05070001241c81c2004000d5008a0480300c6400c1017502c25075102c8059034503490f0261510142c1c4803085102421854945404051a03940304000100b0f2a81c40d14001c00740c410058910b15540d654560050a040d0203024041422420f54001c00001c41e0074011a54030a20000000c0c010400106001480745c807080d0340c0035076058118102c0e9803a85400407000b00500425100001d803100102c1c9902c1c480352070082c00c001511001803040e2854005040110001e18106000070342c00d204226002032407070420301040845005e2076a814100904120846080d15070280c88241a41e20400c07100e102a069182030b11110b050364800543d0300c8d00c0d4200080c1003024100341555200302d6940300c140820902d41c0c014806080300f91010f001960342e20080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 260229442 1250 260228192 260228209
    0x4060308130f03021e03030909090a020a0501390605010f09060506030705161112070503060c13060f0c2315010608070c05120705010204081009051506011b0507050f 72
    0x175000710b08008507002c9040480c0e12441d01c034501500b180d0616540100140d0b031320a05036544139190f04000202420350600031502000f8220a00300075600e030f0744501c402c8580c64902c240c10a80c0710745005d40b26144840d82c01c14180040d82042c018030040d6141c4400c0c0d641701040344581300c496480d0101c00070385410541d083c0c92059450f5141d00c3d080c80c3c290b070b40c140c0743c1458904007220781e114403202da00d41c0ca65450010100120304038004204160418003132520308403010744000c580303003000d0113510300307851082007481c082e51070502d800309803000c4000d03054030707103030341c0c1e480d0081c20385800442140e801c030a03c040346040d00a410007140c1d10b1412aa1004c2e01105080c01083e00055403076002030fa110340200c140000d403d104108842e07080160040702d40715600040b200b201c2c079035000607040100441c100300310b89a02c090b030712003081220059600c07980d48500441082c00503540c00d00000b07410744e00511944000145c2c0b00020046401e079440e000791102c2030790003018440c08518a14940d541040d006 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 260230692 1250 260229442 260229449
    0x13080a050a030e01050c0610061403060d030e0612091c0305060307050108061c0b0a0c0206090c04091509060b03070f1d040807050d11120306060715060504060308130f 73
    0x1d01090700207502d04036208080704504a050100412080c442400100503662050000722001d15201d41000401448018540d0940844200c24000d004695641c198244041d9505041040c00484044041085401601010309041d5215001c1201c030ba00042aa0021740c521405500d0622100f41d80960403190180c44141d010b903c1150180440e502480400c0d401c50001000151508a104c100c15103a07490354008985101c102e0041c0280300c50a40984045188940081c1c485031800d61201e80d50340b40c0028800c0e00c074071f49a03a007407814000e00c81c5103e48000007102c0b003402186403a04150f8040c1807109100c038041d1246400008510304600d001c0010f544c0c8111034144040940a00100185009407003070305e42080030024007001800401041d0a801e0b00c1d0f0b02d030141800c407028541810058102d083d05c241100c02c00401290755601000c4650155210904141a0f0540a941c0005103800d420242c0c000349050008800c2c4150352000d0304615a0360751100c0241070301d030b00c0c0c3c04035600e40510 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 260231942 1250 260230692 260230703
    0x3020f090f01120e0a11030a0308160504051008042003070324091a0a180209310b01210b0a0b040906051501020c0a0909080403060203070513080a 64
    0x204030346074640360341200d4880c88145441e0700c40c00302c0080c01c041254080351014481d40d01c601040d40400044101d080f552000c00c4015082d8070381c260320041d10410f8000d00402e0390108051400c0310b601c0c0030b00c0c01d8030040c000150603204100ba030b001029142940c181d40a6841000b21000002d419004848443c110710018015000c81072a590f24562040400c0014045c007808880088500e020184148100a4000d071403000d819552010b012000c4040030b481c01102c517050403040138101c20004d01859a146c2c0c1580c099000341c0e5003881034105a40b056040000b0440c201600c240302d50381304428a101c442c094245205181d0340c450a00c190072604804440c0240c04610280e804210800101c40c1c1c004c940d10380110711544400001000c8500e6581d0854006e540c0d6001d10031036240c00c240b6542c0840c020f00003440d400380458006013448569100c3c0c050303a1912070b00810200301010007998001e640c4140e041d1340340d013020007010380603401c2200c0d11640d81034a0040040c00072030000e41e9008842c0c004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 260233192 1250 260231942 260231947
    0x50d0305070c03051006091b09060c030519030603020a0f0f0b0304111002060907050102060603100c120203070c030905101202130314010b1203041203050306010c0f06090203100608030d0e15011202030d03020f 91
    0x694140c2e0101d21140080e018028203100d41c10140401c3d41c441500c0c030b000d55073f0001c0e009065104201e80c54400e60000e01c813a03005c80f038051001880d0741e95024142c03940718840e5512580c440c45c10601c4800c5690540b9004001c4480e1480c1c082d80001d45507000328400c3c8161880305407510b00480c0ea4190803103c0c6d0794180c0c0246d5000300d44a225520165114070185400d00d1010700803010354007640d1003940c401e0b00107030301c144102051550100303542001d0042141c1801a00042000080544040c030007084034050b0b00040c020500a143d0402400a65010b85841c8481c4582d11596008180701c0941a0050391031001428103a400070044074160744207140000d11603555901e08544503040180800e06001008500138082040310b01031082031841340e0380110b03503c0f0152040c981004100000c640d01c03581810420b000311500401a901c205800d00400104094904031092810070110f5044000b03154075800401d205c060040004100d6000340c007110340e26644684e00b10708911402d0303805034502005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 260234442 1250 260233192 260233199
    0x1106070305030610031503050d0f0815211609050c07050307030c022202133015140708060d020a03030806030a0c08150a06050d0305070c03051006091b09 67
    0x61340300c0c0d0344622442d10380010a02009880d00c01c0d4440305400580d00d591140e6254070205511041401e0301c0780d943e141800c140c0c20302c50005201c02c80d181d5443c03481010354003a080d00c00d441c01d2200d122407101e1034044400110049541c044400024001c071031100d811300d800181d01ca81960110f0b41100d5002c8002c603d0302855440c21030308000c0d03c0c501282d0010030646500000c8410800c01e08200111010041c1e84020100c0030601c031030859400294044902c10b00500f00c50502c905080211044814140d80310029103401440688001d02401c000c0740341c042010030099070350000501c240312940381c801c1251914005c01070702c06ca40b008003d5000002c64014400244980c11154001ca0f002c1e0440782d044480c0e6540c0e0213000e12a400c00f160681c0590504c1000c588407050f003c1c1c020998441c1001302c18142000301d640340c0300755100682440400180e0300300b00310f03890341810b00558201c1c09481c2030300380e103000840141045100c0c1000444c113018150350b000c007001d030040a00c0c00315611100c0c0018038 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 260235692 1250 260234442 260234449
    0x6282102010801030201050c030f0a120e01060803030105240a0509090708010b03150103090501090803100e0103020904060c091805010f0b181c150c09080601030302150c090d0f11060703050306 84
    0x3520100109005c03e0092b1071681442e5405010079209036140e80314042071b140048421500c40040307000c5560705000e000c02c10310388080100d0741511301c2540d50600b034008001006005a04100d180c520411002900e0700c58254032802528040c0811501c68005c3d071507030141124071a100f1b00a403814010101f0114a1403501c18500309205941810003045d0740c1a1612070320308581c1c8103801542d26210000401c521811002c2d4580007601d1090b2110300d49504580124a6a16005000806060b84c8907011103040b400b038000e29000313014a0000c40e194042403807280d0060304080c400c030b444c0c2d060601d0000c510050040241c0c1c02c82e8004a203034500c0d10300d070641040203800508104400f00b0350511451300100b01200c02d1001c94098044010031203c009110082078002d40781d1094009410a80060001035408260780348154000c1c080700420752910301001c44c151182500384c55101c9169900d0004015024079800d42d01e5009803081c080d440e03c81030900505100d070f0080100011810030002e0034514 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 260236942 1250 260235692 260235697
    0xd0f0816050a03180c050406090905300301061214040203031c0f020c010608060603060720160611070b4006090306050a090b01030b0628210201080103020105 69
    0x2099160100b10f0b042c3c10800c070300761010440740030382c0c00c5d001c204c0d0117000034106406450000d01c00ca45081000070703450b86815444208141c00075080090402c5030446480540c680e4070b0b51103012a0704540c1e40e595900c8007811401c40014032801060070038104981014280102c00d100707030f0b0040c0240d403428441000c0e09030069400462990316965592940344101001e01c09401c620039a0400040e00c0e50520003018a0300400420a070b201e0341c4581c0c02c101c0d0096000340682c050010700385584404014641e94181415813450140900c1421344100160315644100c2c0800f601e0f02120544000c66120b419020452142c546081000c2c01e0303004018034003500200c020200b15030700d10380310400c01c0003c082c12000c90402d60700030310001c0c1c039420091040c003d2902c507980d0048100300d0100464207480c0e0f100c0c00c04100500c40074101407454400242582c5880346210a11441a4092590203110740201c0343c001605000700c0014803282c580101c040e000310504c100009070161601c05e0305a103113500441d840c1e0b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 260238192 1250 260236942 260236957
    0xe090105041e020a050c070e041707030504050306192a1409031902090114090601052101090510080307050c0d020315040f030e030105160e030c120d0f081605 69
    0x103020220b0074404050340c51000d42032022265440c10340e51070868000500d840b010340c0204400d480c1820510000840d00ea958080e030307102da0301d00c1c1d54464406017004d842c05c0c0115406a900750003443c040000d10f41c0078484841c200c0c0c103440c04c10041d40b07041ea004070100b40094401150000c09262030b20404034028801000321403502d8881a2926401c40c0202c0d0604000441c8000d42c01e101a40e52003c504e8202c04280c0913050341030707050710080c3c9203070001449058081c2c94941070280006140d40c21103001c00c540100724004402e566981d5a41d0390311400203000882d0303061007100da100300102c0c0103070300401211741c083d820400901c1d00900e03103010400f0b69213400b13008036403506c02c01003000c80e410107000307100381705500840c48189070500908025100c0c1d1810391050f80300380d140604009007600e404441140d42c4c110f51404024016812010915119070007190552041003c2c2c908900c0c0c15000175145800c2c056545c604903000340b801c02c1580c1c0c19809644816000025051707282c8003d104001134084c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 260239442 1250 260238192 260238221
    0x40f1e1b08012c0a02120307030f080403020a030509150c0d1101090f0605180d0207080c0a150e010302041a0306031209031c051c05070207080d0242090705010e09010504 74
    0x48810b91700040e41e400740d003008080650030104080040c941c00501c65407581001c1d04200340703617260503a4001d4481c070701c03043c2c0101405000300e292501c58940d840341c0389050540410a03503807005015a0750303641c3c01110407120001085119900c641c41c2040c05040780079036100d00c004491030394558030300014003c020440b00c00241d5030b02419110f0003003040003070201c1e2019000b0f0000b079410407081c01c0c03c0c40000b0129038000c155210701000751f485101c100c20040e96040c5031083c00d00341c1c1c00c40103e010384116440002d010001c0c003200c00c0d800510000460050310110704503071028200404503c480e0003240d40c0700d41c0c15049000880961002000341c2c1c1d03840700507032400030700c0c1031200d956240c00491100e0f1640ca107960303102e040108858040156002500e030050041c81d014984140080d903526040492107507038030b102d20741814091415565201440c42d29075107d400b110240c202e8420408040750550450b1080c41e500162035402450302c1c041182020344880500d0303080c84d090201408881d02c0c00c220 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 260240692 1250 260239442 260239453
    0x60304020609060a09060f021903050c01110a0f02010b120c0d030215071d120c0105090102070506070302061b1c02090d1a2d040f1e1b08012c 62
    0x10390f803624000c1156100544800103c40d0410000a0000c3e00e4024040b0035035000c9a884990080080905030140d0307403610b0b12569030039404417001d000d080e040450440c4c0c0b145c0400d01d50401b9812103540c0c40c4404081d030080101018180400c0801d01c01100c0c00445a00302c02141d001a0810040341e00070395000b4011209001616601407030300805c01c9400e1307000900760441107580d0700d07a4450b00010514003241e0305101c0d002c081d41b5090b00e44448801c0541400000071705090282d00900004004100007084075840742d200381000f0f5141c0c4e9003100d580300426002d0a1510303c6000d841e080e1000710680c40100c8915010856000001303600001102d9886074280045070005521341c09512040c2d055081d01070b281e0305100d02d10320100c0030701600007003030320840c900c48941e00304487c20170a17482604a03a0440e000e0f1840e0401c030007203c544c1e1400a5030300a060600742d041c8611421a000304c02ca00f2111401820b40d40c1c0011030803a42007502e6036420004000102c00c7c41c20000c10340321100318102c07007600c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 260241942 1250 260240692 260240707
    0x2091804170c03030601031802010801091a03010f0f0c021f020a090504020c15060402040302011d0a030804081b062a03090315042a061107120f0b0907050f0603040206 73
    0x110180c01c840642e20701680300100300015961b05001b01ca5011002a1140018100d264000713408010140208000269a031601105a040300e0615546009d4054003c002d0340c100400b440016060480204180c50b050108680728580b002422205040b01c29074000040b11a040011000c0c1d0710000c0c0e550100085403074081680c0d900c6100812008200c0c0d070082040da500f50000c085d24910003001e86108901c10f11007003016076000242c1c40806d900e003910444100b2562030001d90f548206400140804201040c0803400c81c0c0c0000b90400c07040c1c64010b103002141124801c00c80107205143c0c1042c01607484840c0d8807448007542c8640d200691100054909029055010901c0d1401d04400100710300407c0082c0018001c84007000110b6090a0504107813103000c0f9141aa84a8214811403041151088182d0702e10b11717040c441c0701c0240807840d40c0300c3c070a6180c0d400c119003900042c010a4555001000c0071401460001860808071352024203d501000082000c104490f00000d200b6a0044020041d04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 260243192 1250 260241942 260241983
    0x6070c0806060906010305011214031926150d051203070c030305010801060e010b0c190804030b0901060509010504020a020102040812071a07050304020f040b191802091804 75
    0x400a44000d000920062a2900030040c000401400003070505103800018031404920001c03004185400c050704024000d034101d40c0750300e1072044509a444045010314003243e07941d40104254401c000c401d010844a07031a410b2404208102071300c06c54007034a0305803410080c5092802c0c070626064003a5003990f613285201c0180c036169134001c45604001481c0c0c00161000c1580510800d400340050500070030205050240035185120180145040141c01103817640da1010b080100304001d50484400c1c0100c502c540c0380c81041c0c1c2d0858001181d07021030700c02c005200f800c014800e1070211040181203040caa4a0003042c880254002000101195000c00000c0b035001e0040011000701140c1e600403581d907034000e08298054041c0c0415041043d076200e41071001c0239a0100549801030303012103d80c0807180e1604002402085400304081d0030110182c8030202044010b10100c0843d10401e1400421050701c4000c80200d10820100650140c01b01502c519110011060903601c07911401200d1981581900c46 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 260244442 1250 260243192 260243213
    0x10819050901020903010f091a190207030c060b01030b0102070614040b19030b010215010902030a02040504050703331509120c0812040509040b091e0a0b10060507110607 74
    0x8061642e0340000302c0b60020b0030240f09040c554080800e00b00b000b12201d641e100c4400006031003c08540342c8001c0800c440d580a0458007910a0182c03c0465035800c9518025025109440040e1407041c03602298545650090140140844059010f844000d080840035203981c41d25103000c0314001007d000114a0f5801c0a0040040c445048444098200800401400d4995851003181190084102c04140c8143c0c400a641901c8600001507106c0d40c504030303400000e0203941d00c0703280d005007040240b103407464043d40041c2e800c00400140603e486410040d01d5802c04011036a1003680340051010002c800181302400303d00da03410f10704610342d15522280b5111607441c03040c0948500e071010608021f1030008200340040c40804554241c2030034505800502050340040024003404071100006403200001d001c441480a5903c2c0c2c2c0743c5402e00840407066440c0c0d22110102c60450880020a1850400800c440c0071034846a50301c6151500654a440a810303000c110550450001d011401c00140e41000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 260245692 1250 260244442 260244451
    0x121c05090a092703050a0507030315030602071a06010207030206130801050c0a1106010501081315150f050f0d150e060a09030f090302100c020102030f120115170601081905 75
    0x103022402040f2410001c030340c249070b14404011044201c5a4800281e048001c2d50014215802c00541320204c0d0704061300904402c280b190801140704401004028840d80584040c2e030080726a29000b0104072507a07007140e1300681d62540580e1001d02c007000145440c070000d040314003600c0008540566680706d0f443c2991b8043e541c40020607004100300713003260b80c4484581c90100d80c101c014241c0f54500b4002a0045001800c1007140300c00c103c0304a0b0502c44401141189820009410408685a8040a59500205e00030301688008184000407207152061041d5140c2400900501980e02c06541703a051070b00d668070780e800302562038482100458400744002c03407042c142c02d440131803c49510310380180b500c1e0342d0941820070b0125581d0180701585803681d010b165400203040c00310a5580b10300050b85507004052140c1080da00004407800c4110043c0050b604036450707003a509540004000c000d48100c10000c40b08914045880300194070756100c1c3c40c019400c0340c3c0c03012000c030780f020a0152202c142c50342103d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 260246942 1250 260245692 260245709
    0xe09150d020a0f051c020d030f110d0e0102010b0a150507050a05010603060902270c0d150f051203070f110d0501020c0a0b10030c0e0c0f0c0a060506121c05090a 70
    0x140c0412130340c00e080c01c0040451100314024400840107034002500d2404a0300090100412070b980c00382028060300303803d01c8860b660012030b00c60701c4030b00360000c002215140b41e072401035003410340c0d002940c184200c3d450103070342c900080300881e081d05800841d503940120f031003510540f1400b40e1308008101c0030710035940554018080030420007024014454160344000e010b188400d0388100c18962a002c0c020225017041194110503901c800d0701c45500060071404641d10051050710301c001139405541d441c0e80080766800d0b40d1000e0401c017018491516400b45a40280000790b00c8084100040e000d01c903000d40c2440000e040030b44050b0561034917400ca81028420a2069010a484034103000c5a918041d5200c002500103200650540d0342d000c10f00b81c40c41c403550b080d5000b0b03800460707002166402500d40b0b40400200e42500c85c01d001551542e00c0c21080401d44903140b415000c6800f43c108101c44e00040d49005004103c1d020903044043c010b08a00d10140d01001414001a10a956841c440400070300384803 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 260248192 1250 260246942 260246969
    0x1020f0303013818060a020d03050a061e05040f050f0c07030201060f090e0f030a020a06050a060b0a020d1103090609131e02040501020106170715090801050c03010806070e09150d020a 80
    0x3203074544281981c0b0000c24480e4609000041d00380d80d00240b0300345110214a00404c468640f034040800cd801180c0020514018901404054002c101c0d411011540122800d009501d000caa00303d0032201d0a0f500c0009034803400d80011501c0c1d040800400680d07101c0c0c80001905691095105510505504510707141c81e1101041e00305404100041c0c5038911683d1b0245103084100320002e035513a014840d000307021940f220700148510003141d201c0350083c2420490540d0310b00c040c0702c0c021745074417440000e4008941034100c091410000001a20f08692014218514002030007007004086210b11051100094031150b120420900c440030402040da2000340c00f58031581403800190a444464000c44065010282c203800022000600e01c0101c1c0d100307000300200300c80a508100e5264070140c10540d8291b08180500c5012642980114103c503540030070f4962944070b1400c01ca9050300132100716540f003154000407035000e05e40c58000807120603005124881b41c501c44d6022030f2601803207520600404076078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 260249442 1250 260248192 260248207
    0x40603020306100e030304060e04090609030f1106010308073201021c0504020604331d030a0c090509010b030712061503050d0503040201030b040905010504030e01020f03030138 77
    0x5480f088082444904011158046100101e5528002d078400c0e074080203500002242c02e070300c50394414884075812520600c00a00f1905010f481041c01802620014800c513001284000020400b10b040c1c1c0c5d4841181454054151a000824841e10300c994039007031400054404441d000301c0802d4074120900700003607150f141c412000031030384aa2810340e40020307003481c0800005a80c0d00003260b0a0340c14441800140b08010a005142c03a503600d104880300c0808201184409500300960032034880b821003055040160312400d054442034080300041c4409075140c0c0074841c179400c0d85c100300da01c1910b4100014022802c040042e04d007035410b80c031000500c001680c0f000300b031042a0284040302183c80100040369407035680c600390b031a104821603004220010020404680c46a00011980f000091007441082c3c21420414000c010a44080b004506079401140142d400441c004200380c0e40e19011314156841c100e5031044a1a45a41038861a8400301c864000c490314104483c2c4488004161151603000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 260250692 1250 260249442 260249449
    0x4030801061416080a1403040809091005100f1407030c05100519050709120b0603010c030e0a030c0507090e0601080f0304180c0c120e2815090902040603020306 70
    0x40701c003103000d240400c60b20030307100f040f0701881003096842903200e560790a01500803140070301082c1010407584d0001083c0024132035070b003001d0100410200c40ba01c0f2b0b06c0d29106000e40085000e8481c0d1038001d078501c4003110703a03940600c007d00c100460500b020b905400341c405148400d03901545d000c90110b50f680b0f200005024041194042d884074180042049040615800c81030010b6a4032412149445600103104a8842d1689100401c0600e1282d0948402c5141c09480e2040c00c59100b4020343c0380002c0b028000f03109008841456100f5000341003126465113040796101101501591103100d044400a00b04005200d03d0760f52400c0603018003600c0d410b0103005401c002c130300c200e147d000d42e1061205100b040380e1080c80e40d84003011a82c000070b180b0a080e005a5695180c40790103000d8040600e0040e204076081010301131006000c0307421098901040c4c02d0060684600d8903131880b5a1a007100c00d024081109038100209412400e00c210326541d202c2944040e03038050382004002070703004418041c8509 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 260251798 1106 260250692 260250707
    0x815011b030e03060705220311040e0a0b09030703111c080703090f0302070807051206070c0512180a0506070b0f0a0f0207060501140306011d04020a0504050403080106 73
    0xa000385c1c025003035400c01c0d880b0766000a05991405484110304440905070395006900c030070340c20388200a0000800d11141081e00b10300c2002404000b0841072104d4600c903500c484000e40e03880c1039a18000b410480c840450f22070070ba0040d40c507664805c1903c42c1c10541000e07030386040841d0f075842c04030440c05404c00c0c6130064a4109034003002010301d540031403840b00343c03000c46003191603180d030b0f4030144090a8a08414080c83d9046040440d00306441900e40d035078043e0043c800c84108210740898a04d403580001088900d4841c100341c00122400c2c0081c03440d0080500310359060404d03601d17450b0544240c800400f40c8007000400000550603074500d9104aa48890200c801c54503070300a442d04c1d00080c0070a0040e4260ba0000401135641464001441d5060747c1ea0200c1d05140d0002140d00489a540003034400c07a400117408402142a0f103540c465984554041d070340351050303945449800703030114 = true := by decide +kernel

theorem cover : BRFrame.Cov 260071942 260251798 := by
  have h0 := BRFrame.cov_init 260071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 260071942 ≤ n) (h2 : n < 260251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
