-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3211
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:59:32.046821+00:00
-- url     : https://prove2.me/submissions/d91f6259-3a8d-456c-af50-fabcd7cb25dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 577338129 ≤ n < 577517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 577339379 1250 577338129 577338149
    0x20f0f12010e012702060a030207060902130509100b01021b12010c022103010f06120f0501080a0201020f070503061b160f03030c020610090f0e061003020901060f0f110f07 75
    0xe1a80d404c043c01d403242490070300c02810f82108110a0f00001d8243c440c0301030700f10606030700184900810802d90030001038a030f0018900c81c02c8441140c0b1250191400300c1d0501c4407401443c0b562003054810f40716030b100400c01a4018144070207000c1442000d202e003403400c00d030300800605180c00014000d00603801c8090380d550281c40c42c40302502100482c007070000c1c6100040c6105000510260180042c0403044608a1501c2c000420210044400a04c0d1189e24011180d0501d000421004030003d40502198404c0e4201c60303030010303500c0006495110754010254107400100109010028034141c1f80c1c204016903803020714210100c25401550400100129000520050b40200341501441000074051150014040d2071500150b00d03052040d032801105422561035105031003240c0142d01944103010401d0858210742041e819401c2282d02610080b4401da04290011440714403501c4085095001c40d10b906a008428a20035510903920807420f000c5e52145100412105030104200c42c01812144c0c1d03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 577340629 1250 577339379 577339391
    0x60a0c1b030327030813020d051203100506040503030915041e090c0302030906010b130e0a052205062403061603110702030304120c0515040609050d020f0f12010e01 72
    0x4000d01c3c031401c4481c01a5802103c540da81d102103601300442c03031381c0301c1801201c144c05450325100048103200b40c80702c0030b41544160005500418101b60043d4003460340a000c0c81005130340e403030800045206501403560940c0080c040403480e03091400300000c0368656250800d007441e440f41e0000b8001301c45444503c0e96120906801c1140040728480c18030190060302c0c0952031413030801c00c49980c650040c0b040ea00e0a04001903045c00340303032a91003d00e015000703d5485880358104106030601600d0b06903518069600100c1d5080d10001041e581d0103000c0c1c0d40440600501d643e00c82c09840761003c1e240d04044110180b074030b00300179664280041882584482c91258540315607080040403510000305a0108010411820025036000000da900f110350140c041402d078503191811148148140d84069080300156044807440c42040c40648140c403400d40e641c044240d03941040200492406a0180d0800390315000c040300e9007405403455285120241800c0580080b01d111203084030a8000d4640942e51744407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 577341879 1250 577340629 577340651
    0x1305060a0603031209020d03121b05040504061d071409060301120c0503060c0d1a060c0f0f19020405040f050f010c0314010b1b0106050402191808060a0c1b0303 70
    0x450b000c99190030380078007007103401000e41c0402c0c00c8840e140805000d100e6080c0d11f1080c0e000580cac00206985070030a0041e800308402c4400944103802a0142c640b107181080000b12b100a520041e120024110044660302611803c200365442760701e901c2d100040407000c001c145030036211000194020545e501185a40540b64140345520502075004107100350031100c20300500c1c15017401590000034604000003502c0c042119201008034480c09029000300000c03808245110000c01d004049e00750314401c0e500d91518a9529039202c6003505800c0302034148000700e620143c1016130065611502c144101640840e82e52125460b00060181c80c1c50a44c3d19650110300039903050207148030300000001640015410301281a440c0d0040764522801210051410b0300407844c00d40081000b0000540304540c1c5a4007940a40201000380080c03101041c00540c00c0413200c2c5d800f20213401195070801c05049036803a200c4605010b040303100c540c603081289822101c100101004d8811810368840e49001030342c50426 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 577343129 1250 577341879 577341887
    0x15070314011d090a050309040b030c1206101a0a110a06060e15040b061b120d0c030b0916121e0c0305011e09180b040b06032109091305060a060303 64
    0x1d03d0007a6030381156203a00300050000041d2030302d100d421900855810a6207010034540030406194550100c100f948000c40303850080b80d00760041c0c00082200740c19986a1650020452418103200d007100b000700204110944a0a99800001500001d03640c0020301c5880d02c80c00d40b1202c1c0c100721074000601c414402844508104401c0d050030558080c8600342e103490025001c4c0c0116002d0030b030101e000d0403c0040d0f0074070034130211002028441d01c407500d4258105800c0028408848500040b910b000310a00c01c80c07902090582c455407001c1c54081740318101120444e01c03951802d200a45207502c44444101c952101c030321440110405040000c1c24880d11030b0700609542c0f06034001b030940b030f8000c02c190300c10300d90400592064a6203100041070403583d80c840910b592541050142400c1d01c00c4e0217110030004201c11440c01108100c0c1100d010300766000c0700c864422500781c0c007400201d50410500280b41421014030743c0c04026011201403002003903c820b810302c40d0480307040345070960b200002d02c01c150300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 577344379 1250 577343129 577343131
    0x1420b13090c02150a020d020415020d0e0f030a02150c0709090b0601030c140715020a05030708011403070314070b07120212120a091b090c0212070515070314011d 71
    0x8500c000c2031130751404800900ca40b00060050164540c00107481c08030032a1075012500284242e50b50502a83c890240c000c0d00c07004c82400980003e000c01402c00c02e2032605400d03c0c0448103004014001d440c916a0070011007522003840050f03207401c144440b2000c03041c1800610f0003007c8028020403d907074145401c0c0007881c40149058141403a0120002c0d525521207219140000301d030090390355a40321030a0404444100d0ba071191595400082e0140c22242e1210155004032040d803a0380440b03980301d00001e070102d40004a5283c241d4049139003000811460401c0c1c0c2c1d020f082d00d009a0380728544448041141d5803201005841c640d90308100e1240581d4104240d90780070545441080c20000c0c1403081401c1c941001c0d2400309030300e4075a4100000d104400310200b1036010841540592240e440341000301a055801d4020094000c072210585410203410840340c11540c003401810b04007403110070480b02c1c020040c00303140405641e043c500787c0c85a03006100343d02030000301a204501d02c000f9054848101781c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 577345629 1250 577344379 577344401
    0x3809130b160509061b06040c03061506050d0c0306050a080f0f0303100501110c130c02121306031e0920010314010303051c090804050301420b1309 64
    0x311109040d0403040e0b120060354000b050445209646100600500c0005410340d0f4003000e185c041c2e01e0920041029452500c02200d11442051100c509040038107250710b21684203030310100304100300004480c01180d011034090991400c000030ba80d525840424406141c41d007000819900590424040030010020041503010080041d403451400c1440d01d000f003103140c8611030502c190701c0010611070405000303032040050041c0c58a100340c01802c002001400d510601400940203202000c800d82d0780590403600480910740d412a05189019070440081920100c0724440104a40381903810000601851900500801600e2400040c090544407a0500b0800e0720707060510f040081280400e1148241b030449816040c041c0d100e060700140c0c004848020f01071305400c10703e0060a40108040c0002900a0700d0054000b08000e0300c0d105801c01044c14455800842100400c00744001220b0011060b80c002d003400041c21425507582614801c03a8200540b60201080c124905002060a500c51024414 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 577346879 1250 577345629 577345651
    0x1050a020310080a081e0d092001050403020f060c0f0f01060e060105040e0a1d0102040e0f102402011e0b010f230d110c0a03030506043809130b 63
    0x1100d6903680411a00c1803803100c86c0da20301d102820040340e0f80f0110580e06144514581031002c006145820751f4910042e6002c1b11406280701c4481e0240d5118030300760b40943e98082c10803101b1203800000c00406810480d0300070450710940800100b000020b11150080040240002c40e40034141484001c5d020001030250b81089001c1c4800c01550030459000d58001c0d11190000801a054440c0d000d50000340c0703254a00c42d9800000d00040d94800180307181d03c10b0500c450741400c19100c0d5100e20070048528400e0554055000c0080d0f03841c0401c45403980c0e1003030f59a00000600c0d0f15114520364004091400e0012201c0d03603000f4030082560055000c00d1741107020b00e0118442e101800341c0680107180740030403001402000c900d09040d14a50780c803031400d0825440304c99440385040d01140d907840100c0355080f00080d0800700410211b04060003409440807907000000300c8600076204c065101c02480c204d003010124000fa419140d03444454455010b521040d80081c2041c1450400f0130a00390f02400240020b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 577348129 1250 577346879 577346893
    0x30d1e0f020a27031e0506090c0303040e0c04030b0a0b130c051806090402030109062d0515090d12110601030b01060e21031312030801050f1201050a02031008 69
    0x10303503401040c402d4611554890741d600803030003000c2400c2c0340102d50002800711040c402408010f6000c0981700403c18400c0084441c151749000d2201d440d080e1001919070135038028007091100368822102c182c0e00c410202c001e90704040d901d0721048029901907491441e400c1d039901c48510281482c001e141c400740c1d032001c13080c00340054110b0018002e1298010040243c04130251500b4280d071104120b507040740b4003c10664036941c42d0548030000300503600c140d1001086052035003603914541c2e0000d440a005407125004117034a03200505c205002c4050701200c100ca010007070050a0340e1007041c0f40c0842401950010242036800380e001e03064030800c2e092100e00c1e0b13001e18010030016458120310b6064483c11300d09a060000020701203825040c205a11400405e0845042e0241540000191000785030445403c400260380703a4101e491201c40341006400603151100501480c200002c3d14a098200030780311014850710080c02c1402c480003501c81c000c14030303000412310a840b81480100c00140511f07030050598 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 577349379 1250 577348129 577348147
    0x1203041217190c050a1d0a0806090d020d110a1127010906061b060f180f050c012607120c020c040b18130f0c0e0708010602010507140705030d1e0f02 65
    0x691a14081b4207001da041100e041c41d294807810140303001008000d040390b003e410581d4035562100e004051005c0103119211740c1700d1000d4071031040c030b6540d4000304002d4101070301e5a0f1118654010040b8449400401040d1400d050204c00008403000c002032100405455041c803800d141524459880f400400071041e034120b0300d007840c030743c092510035600420025252418000c4c107005030040c03040344031076031162008000c14000601551900503124109031841c40075400015034012400340301e880f80511040049240b41380704110605e4002c505802c0407541800e0841954050f5240715003481d0042c1c021400511031070410380103480d00100111b505c00c9901402401c9c200000c1c00c010f10711078a00340c0040b2014107002c0c60544080c0c50a42001d80280c0c0035454122400310282c0648403840010300d09800005c0b47c80c410b11803617003d203200ea55060b0002c0c4141e101800550824281540d890004005c5414542c556100c1d14000c030320142c14282d84a50a00328131801c440b0075a22030282140100070701d02c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 577350629 1250 577349379 577349387
    0xe0709061802030406061a0a2c0d11060a02150c180d0813090903200c120319030915050601080604091e06020d0605031203041217190c050a 61
    0xa000018090060703c2c0c1c0e40d0343c1040740150481d5403150700180d04000401c02d00402d070000030300c0c907011241c81d8202119141c0c23008039118000c4035000200d8003440c0040407058502650b888525502070313001c20f440700e01400001072682d80300a4010300075a100c598a000201c80d003211159004002c034004c981401080b0468484801c42c0c50a1240700342d104024074402c0107004e1040c1c3e0012020b9000100301c0070f44400c8444010980b100c0b0a034080382c42d021145440501d110305090014003900c001c0c0007402300e40001c0c000c02501a080c00d04071804144001c4140b803d066007001d0200b441c0d9900811481041d08101110f0184c840349841014200740030041c41d0398005031469000301d026a0009146920f50401501c81c0f5220283e1544010031840c2010a10a50790080c01c03180c2c905510030000160744070304050b61040388442d800702c070382000c1c800600800d501c00310305061680d0034280243ca1803e0440c0c1200c2807001102c081d82d0544042102d400b0f0380240d07100d0000e840c3e55508016103000d038a103030094 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 577351879 1250 577350629 577350659
    0x70902030601050c0a0c05040f020702131e02030f0601080c0a1d04020d140f09010e0a060f060302030a0b01031b0806190605031b120303010e1302010e1002010e070906 73
    0x11145600000071801591064040383e07140c103c0c10050f20980b003482d10703052045480c00d125241c45181410b00d4401110f00314401c59407900d40c000c24510084114000000161140c64a15001d003003070300070303031501c0b403a000c2c001940306002d01800084c10b4601720001401c2060044c240c48200c000038403081d01c0c0e060b00680174403802c58140e400652990711410019000e40f042d902420109818601404c407103200c0c58007014001c0b495540541e15941d2a120a5401c80f006003040c40c40585c0550101408186150300002034225400000b1904586a0300803e00e00f00c1858070031170f51010001c0040050195841c8007019010810b2558841d061905100700d41d2048060102c41c0c03014099913100305031400c41d51200d80200400b809813946080e0001c508818110002c20490082c441ca0004d07140c0c2210220849060b02c00e00d01040449880d03080311034060b2200d541d0200c1c144250769100318120f40e907800e100c400e000c144d130340080b44010101e0403040c1801d11a0741700070f0909080c40014000840c0b04001c07a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 577353129 1250 577351879 577351889
    0xa0b1506120432060106050c0a0b0c190f021203060a0302060d06180b030c060406090b0c0118140f0609060109090503131403070b0a08040807080d0c0e0415030507 71
    0x4407954540c0d00300303041e8001c21003901101e1101c244055000044142940c4500000d10806640a03aa0307540000c0c0c901e17114581600c01ca5810007104203002985041501d9001800b080200d41005103103540002c0e0400c035a42e41ca4042840000c1030028981c2c10481d801da45074131b0740c41e40d5040d41030034400b00e01ea004030350000a203d544080349a0700d0310f010681c00100107004240203a8042084480a003000301120b03080300c5d019010340b01c1c05030f00504007a800c89088500340d0ba0354580c070304e107812030600050f007010050304801d54803410140c81c40301041c00541001030090950344501e0050103186498000012381418003504403904102e62034002058a504440c9845004242003410346401030540c422800d1510100d00800004104180d1880003085121019411100400e448441911040c0a05a43d5800045051000400050441c409461050700c40c44045041c200200c3c03040041c1d0b003841c8802c0000904411015503a8649801a802d070301c1c45000000c07000da4150b441d85074440c1c1d040c0c021 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 577354379 1250 577353129 577353157
    0x110319020306010509071e08070906030501031505130c03030306140f0a06030213090614042a0309060605060304060b090106050c0a1103070b0d0203040b0a020921030d0e0a0b1506 78
    0x252010b405030713030200171f40324061590060201224402038600701c4203480d032400140440c000400c2950003403141074141d90300240d20000c4003c0c4480c00303a01400b8010708420220000c144540002010066000040c602c280c502003880d50508a03072004891038a0781140c4124001110041d10392070310a0311805895681c41e01590380c0ca40407101603c844c03883d0380100350852401c8000503000951000c090381c0508112020f01c500c1c2248400101032040003040320100900740d00c0072403c024082d40c0070340340d80ea12488010132030035580c100007a07083d0401c036001d462490b2604c91381807041c94030b60380342405130100381815410a00e080c68181d90b00c2c100304070300030510420310400b10410755042144100034440e0b610a550303181c60b810580710180d001503030b040310f403002000045070608805000307070707005d10401038108441600201e541c0c0d2200c1c3e10886c4043c0031030004000c2a00403541900840c1e140211000041030020301528196940740e900802d40d01520304544401b100b991784407421079a0381c0d841001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 577355629 1250 577354379 577354381
    0x1208091209060304030c03180b030a0509160e0601200c01110706020a111801080a030905030c09070323090a050f160b07060e0a0b0402180f010603110705030403110319020306010509 79
    0x207405d90748c44206042002c0207600795071002403620f1021005502c207155125092189450300074801d540c442078074040f07407800001d00e03070244170724903a800349954004814540320091800b00c0354000500000d07894601801e421041e00c00f01207507040030010075542c0c1160010002070b4944000252070b032100340c400901444410320100c20590780c0c0341c9034281c00710800640c0d14055940c1c1014645e5404800c004a01084000c40b0006061401144100d020704003d000c0c00000e58030740c0400c40041284201e40044003c180b0b03150a00070281d41d040c1c904c10300b41e0f1001041c0c1245141040d07498010140d03004407680d070182c412120210390781c01910044818406103951120268a41500909000391288403a80b26070b540782d6060000d0300c141d5500a60090350100641c030071031180750b108494103d0707650318100309100042100c18400c0c3c0c01050035510035541c01341031035420780d640c0e81168006c0e031043d01c0d41c2c031018402c501c072445c0030f005501c0312010798600c4203000d460340e602280e1120414801d00d4842c0c1003103c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 577356879 1250 577355629 577355633
    0x30504120c1802040f0e01080c040225080406031a1f022a10050a1d0126010807050a1805071202030a0c02191a06010c1208091209060304030c 62
    0x80c000025022a0481c99501200c2402c440020b420520641c81c000c514444002101d0103440ea03501e060343c2d58503001d04164003292051002a501000341c040e0380d504080320060391000d004c41d0904c00c5c144201c610560b0741d07140c01e01c01003c1d502a2044070360301c22645010311347c036542d0300c401904100c4180302d03081d4145020a08185c1c2800b041d4038074194892000c210040d4410082010b499840b58105c85544480c01d4840048502c0d0040300c00d0b505c0402c0c0c400301c0d010350002c0d0000c1001c00c5110145420000c0407090301c80b503d03110050503591b0090011310001400214800e000440240c007040e04c0c0c0c1d111540c503054410388d10011900680030500d50750808900d029108400a03050308081a00941d40c0342044002500100740c80c9049000600840a10b5028400514941d25030f29802030403402d4000d280d026031300000c0d0006021076051081c100403003000940050002c69603000c45483d03002141c41c0501a05050401c020501e007980308042001449075500c2501f0790381c2258042c980320710002018 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 577358129 1250 577356879 577356893
    0x218101107060201020c07090204080a02010c02030c0307080a0b0105010e090a020f0405040501060f14041a0c191a0603030f0703051c020d091b08060c07031206090c021903050412 78
    0x4151120841c040c2050201d41c0540540090490b04494021121400d51b140e40c03000c12801030780175807070322070700440b05100143d88a05d41400c0840d00003400d441180e61a000020300e009030542c080e1102d908020f01920034800400c0c03c0c1801088282090030180743c1c444000b5880400003001404000c0e404a2850302401000702070f0380c023400d0b000d03100b04195615400c002d0101e211154a02c40025880030540d4501a003a00907a41107d4110480070040381c040e814240c51500300d400010720a1180c4961981d800078482e0380f10048900032400803400321410a240d40d52154002c100324040d5100300a0400e02c1030b0907a0850758840c0e058a40355444500c100110f040c036605040e003804083c0e0010800340c6000080f07612043e6000d200b00d650340340142c1ca2100d04145810607105e96600c541000000914460583c4000c1009600c42e10f48650050300502582c0200c0d20503402c04031300e044c2d0312038181040742d070104110081001901e810404103000741d0780050040c03203503001e408401c0d154440303080c5c100704e00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 577359379 1250 577358129 577358147
    0xb0402011b02180a0f0b091501110109060608060a021c05091903050a0e150d02031b03090601150c0b0a0e2a0a05010f0504030b06010c1a1504021810 65
    0x20080102590f204005650180318400352042c2c0b00d810304c0d0550780c8070303029641d01c0384804820015082c21001d9030b4900c06d103601d0340b0a1940281c14001d10b404180103940c0288a802d0a503882180005802400c14001d54504840200700484840c41000304411051614022045400840710b02003030750340d11003c000341001d0100c040010b480d03076220034000825802c01c000d810880304a560308880c081085040001984010341c50101a4004208822f21211580c0007594401600060a01301c20080c0208411035031007200d800390035822a5006018413058507045012000301d42c9403c0c1040c01c3c260312104402d4502030310446c012569129a80002d042c14461001c0344503158040c1442801504015000c3c055888010343c0b2440c1c580c0e42c04140d56024400070b01c2120055648d1a0070507040d550b4840300501c0180600f41482000880c01002070b83c400c0108202d0700b8010881610341c107200380c540b200c100a40d611507100394014041100d0410821811110070602241d8035182055000019940b00813 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 577360629 1250 577359379 577359383
    0x1207081b10050f1e040f030201020f030403052508030a0509104b0e070b070f0201020105010e06130902131401031718040b0f060a03060609120b0402011b 67
    0x160303150341103400041d94441c0d445010100c07141c00c0166640c401051225124005102c0c0f81c0c0d0a00d00441c010990000000446a04ca4000103140088261b10350307a054004450403000144001041101900c8104901c090310900c941c51400c8401c01c0d40c0c4001190200800801c440f076070703070b01c0004c0d10140104000707822102c02c00c40400c108002aa815510b0303411070345041e0230780800c40041ca800c0c403501d042407904002c0b41d2014018201d40001c0305001614005141c1714540c8641306001c640c0520400040402601c6212100d11012440c4006400d40e8016030005203054041d03001c200300358983e54400303028080810030002e4821640d00c0051903800301180d024076110f24280030803480c18034940351141a0f03409101c030f1110600728203901075024810741c08801c00300040c00c81c640040d410183c22150505a0060908010082c440003140c11a0000311030280000e880c0d030420001982c1140c40c08005d00400400145203080d01e80391642002406040241000200f3311074031121420b0245112a1396 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 577361879 1250 577360629 577360633
    0x301060e010b070b010509010608070f031b0503070809010515010e0103152c060604150c05101a0d021008040c0803040605030a0506010804030206070f12020c0d0905031207081b 77
    0x561240c80b14101d035000402e003103519030f0054002140324904280411704031080b80c0e41d10b40082d40d0b201e01c1181c45884401160090544400303030714107460b0101c0042d40c59102c4644c1c0b92500c0c0c6c6001240100f0b100400b40c0010030691421050080021001100004819013820305007050760301c64004030014501c030000c03030003605801c0d000820041080c84026100404c803028820340000411341c401030a041c00d50728035600030310401080011101d905000000c4284504104942c0701e2680c07121824085001a0010440d96484e00c0d526240050603064145079401c3c0d640744800f88950b4080354407040540c98800034050300600240800400c03041ea44003030407516003580d440d10b54560010780103030000d441401d10141400b000480d15407240c1d0400c0e110f6034155004003446e4503052030542c2d1300a541c0c4611000c06c0035080341c0c0c07030310740c40540010245e0a81180003829608000c19006080089641000b40f00c0d42100b8540e0803088135010070b80721a680c200b502c0319903c3c0d00300340d46514540b003102d000311418 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 577363129 1250 577361879 577361881
    0xc090a080d030c181404091a0a1a09010306020f0405100c021005070b0604090809100c1203090503030a2403050610050411040e0c04030506010e1608011a090301060e 72
    0x951800305000141c0d81d4141c605002c546014201035620110b54a241c0511840c03000301040703100038610205820120103000040c0362005c5440d540301d0341d200c20344c4070650950385406104c034180151046c02e10204900b500e841c5680c0c1c6100c002001900184005000950085140713905030b800c002c21100100030050000c101440f90600140014001000903031080120800c11001d190045088a00d5582d1001e00014140e4030282000f0080c9601c00054400840512808006032a1104098140103050701c80c0b034606081c42c40e15100c0900e8400e180010541484184000550004152908003003101000705070300c0014180d0681504501e401320b0310860b042e03680003060101c0403600e81d0240c141c0a06d410001d54403801444103441180d400001848030400041200c11109040c0c650000d50121249180071380c1d944450f840e00c00c0c2a0801528060030005110806c05d0722110426151a2410303d1119585018003950200b260300040c08041d840002d000b81c1d03540e800b0360100014100201c0100c80c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 577364379 1250 577363129 577363139
    0x15041703011d01060f05042304020f13090218091302030a0602030106080601021501060c031814010816141b1605040b03011b0c02060706021c1a0d0204050c090a 70
    0x1440e0310b45541203080d92512400810040c2c8502e002d8035480f02d0544540d86000e10f4100380320107000c8284003824080b00304d0040c0840690312070004080c280b01840d405901d4140382546500c43c1c0c1d4a9501858500d4410002c0c5403600604c1003034044860412210b400d41c0369104c07080039001656941000f540750041c00035040410465601850588280e84e0343d0150365541d034401643d64000003c01984003a1902c030041101d03600c00d8401c1c41c5181e200745445114048143d4880006c0303240303504800810311042d04040d481b541d101d004140e0112175480c060388001344801d400f0341408034289110440d640b002039800c4100a00b21010950703001d4030801c030303140c0b4a2050502c140d5025140610351045c0d0400d507050710300d40b030705014141800c64a00400c4041c039900007401c0d651030100010480e080001400403001180c103d202401c0741050100d6000b6003a40b600400700d04580b548290000c455060943c84c0880340c07100807810f0480c40d41a80c0014850300ca00d0300d50040e5020741c0c40c4480d8441550140454 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 577365629 1250 577364379 577364399
    0x9100b0d02041d071e0201020d0204030f02101b06020a03020f0d2f16020d0f062003070e1e0a0303020f01060f0e130606030b040318171504170301 64
    0x400c0740c07504034510140c005043c048005102e029142880018004900c1c45120201c1c007007003c040c01074a000040c645400026140b09036001644261000d40082d11140d0550038942c00c1400c00180d9444c00c8c56244492134441b1560010015024203038640c04180c05947e18065411961092140d00c5440d4540141d0404080a4a00c2980850b5060340c0c0d0140c0c600e1002c035241070405649038064000b41010403991800c000c0c1c3c04400806d031303440070040d0274843c04150055015400203005003c04601c4c0103c40951414858580c4510107d40104000304200c0079886990003881c414116141150b44024040300c158078000411003a42c80031100b0301c004205500007804607400380b081c100902074144c0d940000f0f010f0f9801441181c03183c03000e51000901c4580c40e4030329074002501c40c4000081c4103132651201140324008a404501240d40c1030391369010040c1d24101c50004010017000390042c000d800c0e10030703600c5010f4140500c900c0310ba100007040400483d01d1000c140e09601e4000540c0740d60791007031602 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 577366879 1250 577365629 577365637
    0xe10090c0f09020714060c220e0405031e04030209040609060b03060108030a0e0910060f030e0316030e0901150302131505071a09060c18040c090906090b090609100b0d02 74
    0x31030685c03c1c682106440c0c14045649403042c0341d00d04010b030401d070008031900036840040304080d4a054221001080d0a00c10840c8a0300981c0103c00540c1c40301c4129511406076415008914030b140800c0c4030402c0180d031a440d0003640541e1010020903000030524058000d0407441c1c401e140c0c980188000482c203c1d0000002e00081d4002d50b50701140320740514280114100c040e1400388480d445a00309010050142e58004080103541c80d001410042682d4683d0039604048481da20844080c00c40f01c090560260804900340c00803960441c80b03525051550a10251582035401415004160b409040380b4041001c80142141c00c210721040c54000b02c0100701e079101c070004549900c41d02445169180b1031660721403083c89181c000b809162622010071146802114a079585000c0c40300d0640d00b030740c1f80c901403d200b0343c1c0c550703d80400850802c84a0b03001d4901a400c145c04c070603e090580f120f107503201c5803060b4208506403244800e5407621080c0300d18008071a0410341d042440040c03060741030101c6074010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 577368129 1250 577366879 577366883
    0xa180e06040c03021e090d0524070215150109030503030a0c030e0a0c0620010c0c02090106021203040f020a05060a180608010501050d0b12100e0607030e10090c0f090207 74
    0x8110400b00d00000b03030224011901000004005c0c0409801c05c40d030a080200460f090040181603401d00d2aa11940b03010041411030340c4039400440c42c3c0c4d07144940704441075001659400502440104001e40344580c0708010700c5513100c15800038840019900440342000030f960040d0030307a43c0e2071808014a0016000140c1c02c0e0000030700d411281000d0035808592100103a6021840100c1d6624000049941c4503c8003404a101c20b42c80c204903040100c24401c00454440316185c5440b20a064010401d4001050f0300103800d5401c0380000c8a409080981165842640201030300011121070000c0b8a02040640105402902c005018010316030810301d0242804002c940010aa5403a0700d811243e4603000c0c49250b021034014003180800c1c0c1020f400c5000f81a501420103105c907800d83d0710803842c00c0382005100400c07560300d0982040c4a0b109000003503001241c1c0c18288a20001014034070350752615101842441c41d550710000003040000d0581c0802050110095013200742c950b031a2a00a40c403030801 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 577369379 1250 577368129 577368131
    0x150c040510110c03011808130b0d1d01060f060c06020409020c030322020f0d060b0603010b0a02100b0f010f0e130b0f0109030305041206020c0604030504080d0503010e0c0a180e0604 79
    0x100203482ca01401006d08020b142c058070407603021507039101125500121404e200302403541d117003c12149100c0000e02002d0302075141c08038004d0b00e8040451001024207022601c43d03414001c051110119010418089410a00d130440800225041c0f0308000d010703980004540794000255040300800010181d40500c454401407d8200c2062803e007202c0e2407040e070000d400000c10704203c000c501d040700c03032050890300400e408944a03c80a001074003d034402d0f04080c00b200b50101d644560960304116220040310744110070096148039030700050804041c50320032810410310b41c20030100b01c1d00c1120014204140644903154011500050350050080171000346d014060102151045600c28083c20341265010345482c5d02e414240116282000d8943c002500d419401708990550072404102052255009648440d212800d0040b0716052600c0c101c0e51000304030b8140b005002002150000c1138002290120160361034054003021b450b080d00341c1100350703011741030741c000050120f00c0c40740001d02c22001220 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 577370629 1250 577369379 577369393
    0x30c03140105073507270f030f1505070207030218130201030c03150e09060f0103080a03021b0d2001091a13170901020c060c150c04051011 61
    0x11080c02c03100c085809a0015665091902d40c4420a01c05242d0341210010040c80f48200c00c0800103a0420649a1100040c424090010b1601031001207840c41ea81105501c181e003841c18a1841e481e290a010281091480c51000c0080100b41d8031f041d68501400001031209192004020b9142d004600c02a40910712a8180030b110924013154a481211084140c1c814208550011002041c6189401060640e100300d0410000d00d00c0d68144000c25800000100600e0034200850500e40058101d51400082c500180001a0a14180c86840044d440e00580f24410030180b00644200200d401404c0c3c001c1c00a40c0360403039448504d03142900e4072407203550040c03138240d40c1d110300326041d002d0050f000007403025000c0c0e42d00b101d00c683d80e40c009402d01c0c41c4803c1303010705440b2114214030b00c200604c030030030000551184c296014040e022214900315001130130a42885140d545402ca4241009a0242500002059050341006640241801410301c1000c20f02d92007010b0400c4100e00000200c07403103100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 577371879 1250 577370629 577370663
    0x80a0209180604030e1036091103040203070e0c0d0209060d060306050a24030303020d0212090709180206031302030708100209030c0d050319021f0c1706100f020313030c03 75
    0x87c01c10360206482d0b170800e142035041c00d02c0c2a03501100f01c81c040fa040da1022030002c0c01e209103000f1104815580440303180c5e00d04007481010b2500007030713611031244551810100300c0240c0c1001e00351801c1100d203100141e80da03085400003400508c98840c00d0b481c080e02c1e0000220502c5881d41c05144074070100081001240d204c04804103540c0074125008803100e8000409000180c4a90054403404008200260800301d8103c115286c460003180c11041075401074004100038242405200440428520004210708158010440901c80113242c0014600606500402c5403000c0000500a00c00390302512440401c061410010b58032840300e0740c0c801d2043c00c46405061800041e2030030740951002c0150b2411041105020480c8506c0b00c4003000d5002c0c141c20040200c2e50102c07501946542c0f003400148000580302d010780020391441145040340103480420000340c503080c0185d81c400e02d0300e0401d845900d6450b07c0072451403103080700840d540008030000104000b0a420a501680d101d040c031041400c03290 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 577373129 1250 577371879 577371887
    0x606030c030218240a09060e0403080c09030706030209120a0803060f0f03300c0601150302070c0b0c1002040b030901110a0503041101110d080603070807080a0209180604030e10 77
    0x90f84e0305940d0104640c1e4450324040c0039058489410009099034045c680e5504644c1304950207644084001084901007108055114115607031007034988540360b007021b143c031002c0b03a40c465190045c0003d05500249403075880c0e645048030301c041c1c8050700c100d500291452034540c5068000744c030403901416503036803904180e1602c4941c54200c400c0140041c9040c030500810008400e550000b0400c1241c1d243d1040000b1494900040005140d20b030024040d0394540043c4d88441040039030448101441070004d80c0020f602c1d01c0000c800c070703022904016190600e0540c041e0600c01c0c80c04404010358070024000501d0f4602e0005544140030007c0200026004203203189014860001031400280081001400217104429803450540f01071410030b403010202a0401d191419000000010507020340800c941d038942003009402908044000e8050a8503001e40340f130381c4801c0008000d225807180c2000609042c0c0654124514220b910216991401e00b820094040180180d10718050503403025a0600c0343c0c0a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 577374379 1250 577373129 577373131
    0x18030c071a25020d020d0b06010f2604172101050a050a03060504240506040c0e01120506040f1409011514060a020109020a08011d1b010513030606030c030218 69
    0x4540300302e03981c0000c2105035030040c404004049900058081e20040961100e0085500e124890080d85a150800d90005094000d254022008200ca44072404191401030490b6011b400342c41240707040c0c030b0340301c0c0e00d0001d0748403403005500d042c8090301007294180c0c114040300b16124418039940040700c590b2990244441d081841c0562a001109400200b00262065101a9006018621002c880c41803400d4465a0703c0103072074000502e0b1b444506014051030548248500c044007801c00000b02075694001034050007003251601c0c1d11351340d12400180d070358031690400300c8030000201082052250640081000c0601074480409561070070f190340324094030026403207040c2d40101e40a20242c020103420004143e1201c4d015030110f54881003408011703183d0f801120045c01146002295502e4004503030304940e8280d2041200d0369000c51110f80c120900d440c880d040b1800300f03180c01952507030303407000400c08801c0c43d5000416551808200005100803140800141c034801c4031003481a5010400e442c0740118 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 577375629 1250 577374379 577374397
    0x8130e150a0b182b0609110306041502130b0c0f06010e04110f03160b090f0f0a090c0903050607030c0e0303090109090c090504020d020304030f0914010818030c071a 72
    0x150103031415242c6400201610090166140c48011151400c600c01d404d002c00c0404a0714191603611035010006290030018500c01c003600103103400d10306034903010440c2104c036940c1c160081d40051358940c08041500d01c1000342c038116060540c0c500d92100000e0f07807080315080013541d60091348004900e00d0040301d00b40e4004c82d040500b20744e116000394204045400015040d940c54032a03c11091804c074030002c2054010044000714a454000b1340c001c1c00f508a1b00030111030310801d982d407045155541ca2840c3c110035a000341c000081c18030310017101600c01030500d41010f0017a200d540d04021065070f141e003000000459030f45d0355407060b0388044145036980c011a90310343e0100306c081c681840760b60110760020001116501c1c049082175541d10214040340d0003000100900340d0004100700c10306030880038044010050b03141045410345000040d01e007044403031101504214200300428905404d41b1003030b50b140702d408d206aa80d16541a104150346010500c2118801204035001500b201280c2082d03034903200c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 577376879 1250 577375629 577375657
    0x61103030402100512100801110a0c0b060d15020408120f030f1902040807210209042406080f121804020f0408070612060b04030f08130e150a0b 63
    0x249480c0d08000d0302600c0342030f8a030100304080c00b07103a00e2043c103490018018905a0f4507940101d0174010b180b4251075140c0c42c1c03115070603401c201e02c02405600c8900400031a8103c103500d802600c4000014410722140c0e60041c04002c01c03032810140c5540700381c0c01082103c14480c102c42c13402d01100c1c203680150003201110307504898144000748410050380c0c03805500080c0500e40d440451041c866070b0f8100d0308141c00c42c1c00651b200850038072600d004000801c00c010049000c0361030b051003960000303c603074400900041c03408280484010003007c004464a20000c016002445026100d16105e075450080d10301c100702c244950790704100366000d0712049414503903190b03900700e4000da47c000a000103503012921300600c80340100700c0094200b4080c04003034080c00300d90b0740360b8203000816101d4100b524400d410021110308100801c1001410407052a0205030303001eaa032540b681250b0340c845002682a071710004040b06c04c1e00800210b1201e05540c0024800d08445d21002c89482d2421441507014881c842c0481d5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 577378129 1250 577376879 577376881
    0x602011e020d090506010b070606080106080307030f0302070b1e0a0c080a0902010203090d1b0602030c0d0c061407050d0e070515280305040213050708061c081603080106110303 77
    0x100401c0d0014600c0318000301d004280604256107003450244244d0182840100c003050117000c0000a0252800401c4a28001d0050900304910300341c03207100d030450081c1481020045041c1160182d015120f02a420002800042c40c01045140c034034003032a103002c0c0c08290344c000001d000c00745e184140d440c405016034600c1c802d80d860086502c000c020101090b4158401032104420715592202c00c0f0784254031031000040c00011160140310640340c0e82c0c1110056403c24030400a10603400500c0b80d61001891074100d000940506112000308002010031443c1514141085a115000001400010112102040001100c1d280b0305d480d60700a00a0a42c001010f04400e800c0c0c08461018003d2403013a00d01214442d400c00c00f044251b10100c0c02d0a002094440382040158a03001c080c40311814201103052100d03252004004052401c0100040d1017601030551020301e900c50140e44580d0103912841d01c2e940c40200040d800d03054407080c070f0100c0014003264004180743d84980030040450004400840c21 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 577379379 1250 577378129 577378181
    0x242120a1a1c02030303131403030714090402040918051009081e09030d0804050c010822050c030708060103020910030203030304030318020913120e030714040b09040b0a06060201 78
    0xc40445210549240720b61156500e01603a0f050000718081e0140440801140141c4e140c0743d510001d10440c109100d4105000700303c00c3c43d81069062107800c1016001c071b82d0300d6060f500004c00900480e000f4039903052800a281034000b01c25106104031900030000c590000c0803000c0c60a0960300d154800500380f5406008120744500c0141d85690200c007000c50341800c195868012074607098400c90140000b456800034041400020710082e00a085c080c40c0c51080341c9080c42d40031070260201000408004066464042800001d0014198410009081d80c001d16035074404a590b40742c013800107034451600c140104000f507141c007101e4400c0b2030b8007801031421a602c0351000ea0040880700454580340544840043c0141e8130b59140d1403050f4541a01290203c0071400e204000740102800700003801051100850f60f1303903001032460101e40c0c2a4503c400d24032800d901050103440200c0c5469002040c040501041016139a02c0505c960313182c4000700112030b610071040b0f00f030314001074030b100704140880c0348005 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 577380629 1250 577379379 577379389
    0x1902090d0209090705040e0307030806010f05030403080405070906060f12020901020c130204090c030c02061608060f060d02040626040f03030e390901030242120a1a 72
    0x5480b5501c4000d88440075079420214069404200d0041c09230b82000034013908058000d11500d421103000e1070a54204160031002400501c40904040e0600c00144009010084100a044003400c800c41090109940d00e100260070060b00306207143c04200c4130168054001442d109540348100c05a00802d070b501071120900074640515561300d05150b401300004600b11000e4000c2403010000f03681c0c000303402030580300c0007420420041c00c40c3c041d181c80f103041c40140701d600c28191a080b8034200d0303015010000400020b0390034455002d0400c140c90001c00c00041043e000b182c03c02440e000c0c0000a106000314945c0341060b035404840050851007194003103000f180c81384e4441c0c01207a10b21000c0720004044411840d0380c0c0c204911005110101c040e550781d0400d80e07064800390341c1403c281c0f081403055045900003001c4c04109203890001103401080c401c0d4048120b4091115000d6280c0681e0751850141e005440031b502801d10584024018004103415500b1841954000d03503030700365007100c1c89111104200c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 577381879 1250 577380629 577380631
    0x21e1504170a1a0903041d010e060108090604080c01020d1a010f02070803040b03040206070f0b010302040e03070302070e0606120f090d110c01030c050409020d06030b0601020c100509040908040303081902090d0209 93
    0x4585d1005000100300f13016050103809107a0290000ca114561500c0c0301008403103002003078a41005034640a00c05035a40018403280c11a0380b004c1e016494100600050b4024000c48001d00002820040c901410b224503140da40346525082e0381d400300300c1107010000e90b0784880134440d403c46a803042008102580c00d04014540062004014901e49086a15034aa51028003441540c05c400124010011423501d4407504140b01d8820015509060f83c584002e901e1f1a03c911403250403030743c00030005105654a0040f0b4911001055602c074550800c9111100c03800310848140072140710b4403960110f8a8060f01e0030842203100c10004002c0428903a0044010340407062606080c00802d12000c40c07580064006000c6c200440300000070450f207142000101250080d01103070540d0001e0004004170341f54000c0c060858015801c1250b03030340c040f06010030300801c5c580502810b00c06003c900030082561290595009100c21315408160401f05250402244650f0404aa110300510200c10042c00c11140d42 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 577383129 1250 577381879 577381891
    0x7030509070906080309040509070501020c0d26030901050603071208130305010f1509020a02070614090916030c0e0906010c0303020d050405030415030b0a03021e1504170a1a 76
    0xe00c440e41c1d554500c0c0b030280e540d9034002041c1034002181a03000782c100f078030030a6400301c10540180741103454600007130348031800540c40600402011000704140060000d104d10050b99203405685080a04045c010498100341c8400d8201d50811020074942d14000440304156410007420741300401c41d0750b464140691003a5420b1600d0070450000202140c020302c02c4006011b00c9100c0070400200112110248100319084191900d105124060010703500059074420380d120750800d450210001c0800030b0450090101059100b90020f041040605040e40c81460b0242652001d212902180606982101c1d1344a141034104c0c810500050f00340d03114081000e0002d0003414014644015480b03030605a660460f41135456900c00a420041103602c1070703034004207100902d0100040340310000024401c008510000e4418414450511407954410f091102072010041141541d51000400c04685412500c1130a030400e401440710aa54000403400401303040d402404145150880b00d14410006005890 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 577384379 1250 577383129 577383133
    0xc060f04050705210a050c01020f03071505100b070615050904051c0507020a030f0b0f010b0301060e060d141027020d0e0303070503040b070c030e010f030b130f05070e030607030509 79
    0x11329076074010180088403d141c050000f03440600300c200b001910713043d518070095256610800c9490082144020311018259045801203002d07210702c02076542c018920307080b03030392043c000040900400c5100d511004118400000c1c0f40d00c0da5a0750001c01851200c22200034140e508841d010981d18680703010400541d18207070811078180380807900801c0110b00c0c203810403500c00c01d040300c4401c14007606214031588044040c00703040caa5070420569801d140010f110326803c0c8040d140d5001c0725581d68405a500c5d03412000010009905000b0071002e20913410340d1100c0303244014401c0819185c0c0c03030032a800304100803410b52030304104680c12000f00a42c42407012124443c2d035908031049a0000f4001140107241940d19144c803800c203030501042121000c1c04500a12860020140009401084801b55001c09081c603c0e901d034500e50050300540440c510159005002c80c40c86080400c0075071204100c10480e450030003459403080b10641c0d040c0d90307119049605a0004c0001000079102c0e420090b0700c06c0305001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 577385629 1250 577384379 577384429
    0x60d0902150f071b081b06120c031905091b060f07050d0305160f050c0c0913060b030d0c02130b090414011a0604060e040e10020c060f04050705 63
    0x210788555800829401d4185900040c82e041032003a40d18031504541080ca45000c0c0440c5400042c50b510140542d1400c00c034807214541100310394500090b0341d026444844189200c4c41d0106100e4000d500444e03042980b040e8500702010188a507100c1c5074401c1404c20010800521540e00c10342c000561124515880002088142c20100014000c0c0080501c108001c1c080100c0500000d000d9450041034805410300d18000e00d01401e41c0615580f224402608050356a04e4400c480c203810089440742680c0c00c030000364140540d64541c4140080f19070f000b88000c0280b000380e44205520381012058000c0000c0264041401514140c89114800c60340400300003000c00c0c0c07030404100406801c035401e82e1a0b4015840c0560400005e000381c242041501228121010503000019043d018a0080c0b2080040c6d08030341c50501d03101c5510200c46004407034101e0700c030103030500d501c0c5019601c40742400c05180100c601055045051410090040340d0040203401041d00300014458020710a658001c14500c1c265 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 577386879 1250 577385629 577385659
    0x90609060702030a0605061c0b0c1605061006170c30072109152403120905030303070f080406060e1512030f09100504031b0f060e060d0902 61
    0x440644c6601c40c81d4041403502c0d00900304003c00c80c1d40c10101c00e684200e20810000150b880c62800d6102d01c04103a0345481c1d1158025058503c04c0f40707040101030303201d8001484540301c414400c801c01c03502199a2030081008a0b0300b40c002d012010754895003080f5003030203030114540c0c1001c0460001e480c05600000d10483c0303200c80c05284d9070b0951300790000ca0a09990400500412001d10710b00d454005003d1200340142c0d60b94515243c002083e0f8050150b5451110001402481c1e085d844200d031200d0340911f40e078680c2018008041c00c40c1190b004121074070720020741400c011003038920030441380d21101c44601500d007041c0c400300c900800841e65107645070000700d08980103079401809000781084406006c24080f040c04002d0304540c4140016910500c000c1011440041c226488202e0a64130750070156a48402a6590b01036600000c0c0004811060b40800c0242c03600c4880c110303035071644002841980d40c00240c50300030f0402000d40e00000c0c1040761444920903a0401e5504030b10241a09038500c0d249 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 577388129 1250 577386879 577386883
    0x7031703061203040b0406021603020d060504020f040609020c060f04020d060510091e0b03071202042c06151008220c0603020c07140a03021012090c03050d0309030509060906070203 79
    0x240d00805c520340c6001c2418042940d042102030b01c07009560407141078003400c40d00098600c2d24500e5004000d01d4445c80090115160100301c588103180181c4140100303611404113034040d400c08001f030941c5204800004683d1010001d403c1d008640240c41284c01080c0764560a01615008061002011002c8400210b4000610420300e42000340c0505c0f03c3e004020761542425110300110081c820360200d402481113040000304512920b5045138002440703001c803018008030814081c3c42100b00b070800c01000310030460100340c45200300c540c40e4050315a07008070020045442d00050328900090f802100181042518141180300c40301b030300a1040b980000350780c3d080f089240e0354220000190b000304240a03161030030407401000e420315039070000c0412008408107580b0340d210b00c0080d11428042456035000e43c042c1c0c0c95040002c418500900c100c503040c0c185150701c10940d10003100c2d9032041507600ba0010303200344503090990398036a403110700d852208410000960132038040b06a10000c10400b8030010713502 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 577389379 1250 577388129 577388137
    0x1906050a180515060f0c01060308040f081203010e04151e02041505071e030504030605091608010e06070e030c06030a0b0103051602060a0c050c1614010207031703061203 74
    0x40718a110010140200101c815128040c1c507a1000d5810001000201c0c2c0c0c0e0b6a00b03550700807108824850300c46620291450240c4907036440a404148001400f080110222030104192190302c412900300c1d000c01c000a620380d1009104d040d00d07455036100410005040851544800c621240c00400c1e6050328051b100e0351003080701000009254009820030040501c1010000801e006040a03400c18400d0b4a69500c0508501140c410344c3c3d810005402c101401017040c0d5024642019080115152018903a55602d58000c0c44050300030009a00081d44c42e014040c03090360300c9100c0c2c05424140c40c0c40d0b0007a110740c0350f4144110307890300585840100a40341d02014500c108121074012621423009400942220005846008003125405000c0441174001411035004000759000192503c0e00300c03000c4411740501c401769101800f42c180010300350040c0805020507641100d48420b04143c003030005a076200300c03900c4001d0658003503411030800504290301071980001d000d0302c00034480d1420851142550702c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 577390629 1250 577389379 577389389
    0x80d030c0206011509300c03170301050d1401020f0c01021b06090319020a0804060c150501050d020d1712091005040b0a0203072c010806030a03081906050a 68
    0x25a48002030140c07541084914018040590907010207502d1360b00081c802c0740345014100080c0d00141150980002150006488a110208904c82c860151a00c220803800034401505c01000d255941545440e12404490407190014403592480b0516941d01012140c20613045409541c00c3c05102c44030103106c0300800303822004c0c00005070749106910310f20700498141e4a10303081661050b82004214900082280c02091083e101040c0d000040d5800324540709484500400c0e4403004940012170a411400b0a00c0c2a407003550035410b80e103012030b11070045a800744240da501c0f504a003245009070409070404e408407401080c144145118240c0b650300d1984c40b40c586190103860300400c000c0e03541400e003c040c0704994400c0c0c080c07105040c180c542c06803400014019203001c40d03001000c201018010751165501d0101d040d03241079000c5000b90481c2126040c0e852050200d245c1d0701c00610545030219408044591685401c60b1640b59483c10007200300d81c07202ca9146003995072a01080c55030f911504171303008003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 577391879 1250 577390629 577390631
    0x322020a0503012412120809120d0f142208090402071a010902070b0105280306150b070804120227060f03010b09010b0904150e061903030c060f0204080d03 68
    0x11000c20303040c2d402d880040e070000d52a03041c1400c1d000000703282c1d0401346c84194801d281c01c281c075855003e482410500301d1045403c26000000d01144050000d800c40900c0b060003e10801c00d100720700d410548100021503c001d100ca842c88001604511400c032900400c6025008084c184654080420100e034490001500c510403170560754001d040e00f211600f400742400f481b0035401c00c501c503500c2d1941d40b041030184030b10682400400702414011038500140190901996440d800e80d00d080107801804803641404082a4105011454428401c00c54050b0382d0711440807840e252411000c1a00030415100890b80200e00341c055440f4a05a130482e014101044044034166041c214104044044515507942c000c4c0d0501c9100d0f211030b80c50030030860444d03c1404285581308542c01c00a40103052200c4410030b0081490303004034004c20b04240240c440c45058820340f003086c82e101078000c4920502e20000700080c6600c00104000b50301d84d004580c240004640150a0980b180f01a6040000a000c3c0c5000a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 577393129 1250 577391879 577391921
    0x30b0d0507050f220c050c0319030515061905130e070905040b061206031f0e0c0406030b0c0f0d0c05120f130f02061b10110322020a050301 61
    0x80c50210880d541c1d03400102c9681d030030140b020190002c0303510082584041e15644500c103980450040045031f04400d000010340c2d40e100010311004540c00682c0c6506c400080c03030700000503540300b0040319081a030307100289901d0400b5444001c159030f0b04d68200c00c52080250a0046440314080c4800c0e0328050b00254030a040c0e2884d0043c8010000020303035002602c11400d111424029440d1041101d4601d0700004600c00d4950f031f10404286018140312070101d00c820300003055640c0003030a03845018070340205016604181030034810003094401600000c4c0105880340c01003046524044003c210300d15080c02e5590800c1c0e1680030500884152445880100c1c5d80000c0c0c04184204040da001d0340003036080c001d00d800c0d090005d800e5000a01c6408020120000300a84d10305658811055900c0c0c400f02d0740100c0240c2010020a540700c0c001e414528442e2414801001c0388181d0040c02d4070f11038080404110baa4012010356013141004e405402d82e005004a680402c01b81c0302801026400842d2650410039 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 577394379 1250 577393129 577393139
    0x3011d0628090b010306030218062b0b0906040b0708040c0506040b0405030d0c050d12020408030a050a18030f0f021807031e060b09150409020a02010f0c02010e0d030507030b0d0507 79
    0x20b4441c076a205134105450300f0800e10059031256514140e20b0310018600859540388008075055910032220224011901c03022100050f140328180e410080c031610101090b40c88080c0456901c420941e0000d000c02e40100002d0140c0c0d1141c885543d1240c0203260700848070b0f035100702143c0d0301d50060300000e0010340002014002424104054a044c60480c91b00d412460100d403200c0c0e46800761740303204a003000440c100051050805030103480143c070214007526501c50040c1e0001d8002d40c02030ba141e5012410b10550182c0c0300300c0003000001103940080c1c01100040c030300e0f501e4441000d07401c1c2c01240d100f84840f4507605207040090000344a114541c400150754100546002100e805a14502501c1400c2031024001c41034420181c0d00e1103070313081d5811b6101d169a1046c840e00d50240e5000041c10074404aa00c0c40c902e0750541020040c910029002c110310003145e5070032405d0342c0070450445415401403201164051003030340001d40c0140589400152050705000003449001c40000c1610706078091201401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 577395629 1250 577394379 577394381
    0xa060906080a03080109020a0e180a0612050c04200a08010e0c07030219170c01020409061505030f040302010b030706020a1505160e0f0d0812070503011d062809 70
    0x4094402100202a80442c65030000d200d000140260007800d600410703140d40c0a80500b0605445030750007003404502444403204010142c40c00c9030210806801c240e0001002c119802c0c05810981d001000fa040c400300400500c009031071216594609030103089140d4003045050740260404040030f035104c80c129454010706040c0400d02402c842c1090904100d4100065000500c011100541004a4081d9407140c02c049240006131201c000301c0302000142009032540650080c0181c8042000030440349803540665400a5001e81d80c203008944100041082c40c0304e20f402441d4800d1103880085001407030782002c0703410100554403d4026a111841050410040d00d003000c00340305002c50200315919016107440a0020303004d000c001480750a0341140c0303031621451856105018040c0c41012040207a2400742216841081042100b049e04004103884502c18021241224070056402d2003882010b120441d0303405010f0034050b0b0020381400c00800a40001c203a410840b0a4802079018a500d8020020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 577396879 1250 577395629 577395641
    0x50f04032009060a06080c0403020928060b0702131d1506060a020d140c0102042715090b0a1203051b06010e0408030c12011404060801061a0a090e0a0609 67
    0x14400d00b0752500f0002c158843c00c854004841032494004d8458641d1509140c0510882d04043d4004034680d082002120303d23803001c68036244081d403107031040c2d861441c1260100d0700305000c2c08070180d0040042c800985030000102c52403600b0250002000031018416007041d14804000000c55085005004945400400e205a208106031907162800c07481400003522400541340810520684041045495200c101501c48030080700000310759850302d403041060103114081540ca4105140015206950728a01469185010340300b81c55242c0c3e81041a1000034203210401680c011003130710000902c0400c0001403152050107516220340d510742c0400d041200035000390702502158403600c0104440e1265000b002d501c55002191f4035102e86071700440d51024400e038101c086011038041c00224408521101c0404455022601000f2059803560324038242c955621803484034403040c0032403001080c51b69004051f000203d140441d04646c941c2c0194001101c280d518907801a81d90384188000e80c20380c4200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 577398129 1250 577396879 577396943
    0x2060610110309042706060302090601031a10030e0709020a080906010303050d15030b10050a090e030301050f01031103042603090c0127090f0f050709030f03050f0403 73
    0x400740d840300c0c48010035903078896800c01500650b0b9440e09481180c88905007000c0004d00f21001c08800d072036504142024120710700007640b00e45d0710032003c03c01e658020b10034181a020b0324882e10382080002d00400c5003c6000c0b4040c0c0050680b100c0d07800d900d1042c180007070006400c8041c0300507114201508000c09141c0002c0c290004c40e4072007801800880d8000064644060340134001213840c1000340078100e407104c02580000c1c2941c01000920a00e50030118607801a202c0076a080c1084e00d42e901c0011080d00d80a42d5503500c0c0750002c20050009007868840048225410b050204140c00204180d149681c0111000d85441c1c00c814000b0184070340c0e44607034aa81940852419045041115a060321880c202411030306101c5001e4004002c140582030303012081c40d8011010307981c1c070b65030301c520800751113050710b0700309003500c1c0060709880040c651086a0040007140c3d106419641035680b2180d40904941c0d0940600109000c0d5019101103080100013452041c44852541d40448413002d0100a442020b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 577399379 1250 577398129 577398137
    0xf08060a0b030721020901060e090a020a0c02060304052b020f01090309050f040f05070201020c0114070e1002190804030330020d020c0a050f06010611030a0f020c040c02060610 77
    0x2000c455560002044001e8a200501c007070361a12100c000744c0f0b0f4004000d60000e4002c81c2c81c0d0000a50703240c00802002e02440c1c184c07401c86003641d403046010103d102d1302c1c10072400b04104210400142c141000a160710a2184003101c4210880703540000400241c010300700c6510002175604248680d0501440350300c2c1d100d02c8000e00c48074800b603502a05d00c003604d010302070060052018540301a1b0b41c54005e03110510b800e000170055800c01706002800b03544501100007040d8213005561840c83c04108440d4400e459680c0c4110005403200104000144140e51b06011840741d1007030030f58500160501c1d210701e01d2140b40c02580e81c91551130007515410048aa401c00c14034100c1c0320b0442c0031580c0204000da60b4801400607035800c000c180b00c1009024008140c4000e01c02c4940c040b00300314001034a444130701c50b2031044403850b13a80d07503c0807548000486e0a0b5401c6800c00e12102c11507500a40348022214041e00584411940d2038010904880381000f010005901110900586003071252031044041c0a03854 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 577400629 1250 577399379 577399391
    0xf06150611030904020d091506061d03120f0d06120b0906132303040e011e1208090a0e10150f05160302031b0c01020105181b03030d060f08060a 63
    0x81c203140c40307001d2400c106010700d40002e504206800c1c15808901e9450b4420200c4c2d0070050507102e01c2000703010030b0084401181e031400041c1c0000503906190020b125008004101c46201c50340254540d410a1801c00c040c0241030190010306c0e8450b010f101c02525100290384120291400d082682c1540a040200d071500500184200303500851604159980c0201c24418080c400010b9088180f4030300290350701a020216020a0046003912098100d424081c1441c1c0c11440c602030340c1e075110800e07219400b0072030f01426200d400901d408000d400041d00c01051100c11aa84030001c02c03104200300c0d45080240c0358141d0500c090700c7c00100007030500e02e652a00ca07070140b07c0281c015005114003103111000200035812142014400c100301c4001002003614100921000c03107026903a09144a40c5902550801d00094507880c504400e1808052648000b44450240c900080401c10503007103d00340c050204025014107a801ea015540043c640a0b996480c6286000d04403402d00034050b00007101d050030301c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 577401879 1250 577400629 577400657
    0x8010b010201230f04050717060603010b030c0d0b0604090204020d05090d02011b051e07080c061b09060a0327170307140d20031e100b0c0a0f061506 65
    0x143d2500d5010845031401801600d035400e200703180c4082c66001c910b41901c61a002c201e200300100d0480d026910550091181c0b035414010107031604035000d80241c2000c1c031142c2940c0404d03416400140c1040b0b000d40b001a080d412a00802d0580e032240d400305501c00d403600c040c050010000c2011425a0440b1703c020400027101c010b940707410480d114001010008007051541d4842c0185000140030207014220903514800d03464070b0031481d040b880c2400058010703d0002645e0500c5951003805035003c900e880361812100304108040e54105100390810180d03107000a0f100d24848075110f00414024000c808070f02d060700d1500d150a450103e010076900799040c41400340058008100f0002c9001d2a0403041c0c80c2c100681c210070040c4691140308407030044a81b020080301d0104070003140100c05508000d00722905c1108512070f0a841903038055803039420403a0070403140015070041c1c05130031452010340700c0010300394891824034520f501c0140e0348240e503034081000c0600007500010041c040c90801c480c0b482d8402c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 577403129 1250 577401879 577401941
    0xf02031915170c030106080706090f0806070309081606050901111804180c030c06140702030a06050a06050904060f0b2b11120c09090102040f090f0902060408010b010201 74
    0x1449042154120408411640d0005000d44a0f041c44090b000f000103546d540040356941c0e0303803482610081910002c011a01c000d4030300781b40050f0345514000703000a464201085005000320842640e0f80d8901f030100c0c000d8540350001c81207465014080108403420f002d03034840d0842d4010b003151420a0800c11096021014803498281150011540081d4000140048500c11100701000800340841c0201c01710070480b110305844142c1703c07241d84114032000108090801442000310180d4142d002240720f000094054000c6640041005000f2405940c1d80010445081056808440c410b1701d6200350745203a071585c80f4044004c8021201c94140e5034411032111031074440b1000704400c0d09260000f07242030007859590342d00e81c03841c0070f42007031110b030800e5400d541c681c0340c1401841d20802c03003c004104914014000da409640750b0000403030740c041c5000c1c3e403039004100149080d203201d5103c01c500300150f070b01c002c0580b00504030400003260740c810010009003182d04080c03885103100445080781d21440c1e10303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 577404379 1250 577403129 577403171
    0xb18011109010903021318030f030b01030501180c090f0b0d0c030b1305100312080403030c021f051914040615031e050f011506080a0c0203190c060f020319 68
    0x1560108a82002c6d064200050140700101004000e501c008900405030300044080d004607141c2d07002c110311445400110140d80c070078800c107100301c5055000b0f4060410b4030350107030103540943d040c0b19901036034804415034001015440040a5000407031019410b0604e8014038062110340d103400c110340400c420000b40404041888441c94507610000689070440c81200340c4065a0800c16403030784210300601c0105040c004440407400a030408120769001400020000c02440b41400d8103580d041000c0c0601000780002440483c0c02000741c1c01d40d4044c915580708200001d21098021388103464941000000d81c0c0741e80c607159007445c800007020404079190b20031100c0b103200215280220a0500d003402e81ca080c3c001c0016507840d510709003911a00c0402c020704401160761948500c0d038280d4503907600d08111202d0911500244c0c10403c41401e48003051001c1c00811000c03420403014840c00b94031014101e41c1103082d0200b4140c0d0001c1802400e5504850000c00074104d040f00340901039040500c3c4000d00300d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 577405629 1250 577404379 577404383
    0x8060106050a1206050d0c090e06150613050904080c0f060603070612020d0e010b0f0d15050c040e0907061e0906050306013b1219030306030b18011109010903 69
    0x3e004109100c40c58080d81142c401400010420404d00d0f4950610302c2c546141841004400c40c6002580e140c54940403803194820200d601c0116690030301542440718981c003a1211003059200c2c4540400c6c1940e4060b44140a14000c071040c0b0388a0202c64071143c5800342c110b40242c0c20b54085020008550b40000e00442039a0840c98840040c9482507011006801240c0c420381c8100d040000d81c0c540d001055003e0b0824440407a502101e140e02071042c0145c14040100103005400c4154038900c281c90a03420550f08092010a00b9240655070301040c0c1200390103680700c010341c0d08104010032101d94400220010304844215401030000014009800004144103240602002200040c81a07000303129038035010801e801d1194000f10002d58004c02680000b0040980460b4a22a956542840c04010800145c2d20009192040283c8091880c00b4200345080b0201a02e4410110000e280700042902076141d03d1140e0100040042c20582941c80000f41d220b0184000c3c028100e950784d01c00307002800c4903 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 577406879 1250 577405629 577405637
    0x1020d11070507060c1e151e0c030603080403080a020a02192c0f06120a06061a030606120c07020a140f030d0f0302031b07050a1703010f0918060501080703050708060106050a 76
    0x2c880f6140c1000461f908503000345100e482d00349209001d136008116924042d0440c0820000101c0b45202a02150000e02002d0b1400310113110900c0060f2120005042584036401200e003600c031b450b400074140038043d14081881211845042000d00e100c900c5840103a83c1010046c003000c008814561528030005000c3d01e414001400415002e84034199140c150580c4102a2000d58009041440140c0143d00c2200c9100c0034424801604160110659010303070342c0103158514140c3c03100c1d400102c42901920014012500300072080050741d420716a440102100b1840c495401e4007a010030091704030100681c6c2c02504010400302d04035900c060300c0c42400b10309042c0181c030303a15800440807002d0303001c01c12031800d1400004c50b4014010002064000284229541890111a41480c40305c60000781308800c0030388003121050000484903088000b0300840d040302d00b4200d001680302e035001d0f15000c1c2e100c1e117016005090103005000d8280080030141110300c004201551411100130220320640c05e081c8100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 577408129 1250 577406879 577406933
    0xc0907092304110f070507140105270a0b1209010905070605030a0605130e0f01090b28020a091a190f030e070b0306040b030319050310080312061c05060402060c01020d11070507060c 79
    0x300c03042f1020046c8140020700310180039a02c41c00041696400101c59191070410140015000c80050041e840350952220240002c41d00d031000607a1240c10141c24100d0721921000086115214050010b0307138102c03090000b040c103084203001141000c84c040c03d090744913410589250003007030f00300091a400c105500300c0c58141000d074640081544e204410882c8481d800002d944500c0b592001e01502902c00d2560049031841c4000041040c0740300e0301c07118000d2481015202054140100c01e003001c90102da040200c0c0141103ea01ca03810032078242c000f079910b50008010b1185904080c8120014030006800940c58100d20b5951207000301d00014810003041000030004945510f0180868020140c03282200d485903051600134500ea0b9040f150280190350365410080200c3d020340703c0b0300100da0000c010f008251119028401d007540250046200b540d020064552a40c40e244102028642c0c0e03000000d4031030300145000c50a14001e5805542084018000480442d04000120341928505050f02c0f0032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 577409379 1250 577408129 577408177
    0x30a0f120509120c040b03031303030e0a0801022814040311031906061a0406200c0d050105190b060a030c0314090c0907092304110f070507140105 64
    0x200d4400c0141150f00701d10f16000f900b28010340042c02441040088506200c9100007005142c5d4900a5001000d0302040140301000417a000700d002681841c00a080f10070015126070406080ea84040b8000c3c2002000d910500180110520301c803801e19000d01c0c010041814203a052001801140800342440f5000142c10501d40d80070401c1981c02c4858002082500c02a42010401040503100e41358820207003010b48603000d40d40b03804a030103582141d00c601c541126040100385410040c00d066a02d83d21030182d581c0000d079106101400340a07c00d50001c1481d10b010304046c0a0750b16100c0b00a40d24a052111003031007559440162a1407016a20f80010f01a5582074114040c101505510142c408000c05204142c4000300d41280b444400b554000c91540b0380c0c0c1d00469003107105129200c4c441d0100e05150b00c07031410b803035244026000b000b04080340d2149148860a455400110040500e2900050326020070000340040700045ca0030705606001c003c1440000303000ca10444025003140e1586103190b2503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 577410629 1250 577409379 577409387
    0x6060d0e07210c05030d050a0c02180c0a021207210c0611192a14070f030c06140307030b03031c02130e06060904050903191706030a0f12 60
    0x3004008103414100c02950012600c2d2210003494020b40b0b424660b0355000c11141400515031030a912a0390780c0b140f622014003021504d600e44c1e03e0041342c0c03001030b0282034035903940c43c4d403a161b005400c02c1440d507a0300c891951010f450315000000708080c011084c0519004200708039034072103242080d8020628204400602140c00c115000e1000304000d1515111842c000904d030083d1076107012801c188099545011001d50300d14200c182c0312441250321220446108056504a048482c410a9050300f00e00e00300c41501e0502985810200c0d0f2108816420000e1208a40510005001038113100302c10ba00980c1912100c0c1c400200071009064948801481648040044940103505400f003a1060031242e001000030b58041403803c800c1000c900e40c0407031540c03442c030890f40c081d0400038001880d0400c00c20034080074010003000302601380402d1102c82c12066001700c422110354101e0b0740303520301c0d200d52070019a01d04602422044c040d40c400d17170042000403464051000960b030080787c1c0e43c00c02418400b08031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 577411879 1250 577410629 577410643
    0xe01150f05090f0426071b0b03390408061b0f09012f060a0f0c050403110d0f05160603020f0d0f020426070503010b090f06030c0a0308030a0b01020606060d0e 69
    0x2a0044100041e040140180c01d600007640007124001d00040503910308808e0b0707480c042a0343e11511044500304e05529944030000200080c00c400a001c080c5105d6044402c0054005a00c03203540741c0c020030100700c02030701180b0640291902016801e8141489100d41035410702a022030641030000302c156548200b818842103135240c1d540035050507080c490302c44600391134400545850302c04900749a8800c41d41034650043d00d6140169079201801c081c90341c0c81d12440c0c8600c1c06145138000c903040c03100c0000325031014480640396020707030000c11803e100c3c614240d03d4049258820b00405206102000b0300b811600c0c00c4515461900f00041003000c40e46080750001d110b0395100c00200b0480c01c2200c183d400380041c10400c1d4004441c252100c041d03a0f0418542070703500b85042c10f90300c8521000015000d1015000964100170003030125a110503600e00800c083d402c00f070f00240c910381e90120800a0400303580c051203410300760a2000c1d281c0c500f410b0010582c10b0080c41103a01103982c40310f680c240301c0c80c03081081c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 577413129 1250 577411879 577411943
    0x9121f05070e0a240e011d060705010903020714030c211f06180203070c0f140a0b04050606100f03020706140711060106030c08190e01150f05090f04 65
    0x1c4a5844e503151000150f80d4940302c03001460f0b070407000102c00200e0050010050314041a190180a41200100c0625400c03c1d500780e10f600810038010500841c03002d2281c0b040c6203100e03030024010981032114450180c00d454002c3e5110b5440040105440e48509100c102030f1000340284403800c04803601d8140c10404070050000c1c88202040c1d41000f1100c2c150096402c40f503a82080103001382800301600180d110032211100400c000b00000d800040f81e0a2551140038040c00d130903404406c0860b03945040c141e290342e00307a5180c69520284400c1c080c080c80560b822000c100c941900c40c4210880180c9164100e05440092545c041a28414031201c0d4002e04844540310a080d6068a403d54000c0c1914920060585640c0329281c001301e0050b00a02c2a0030f440206616800f00c180e43d07920201098070440c00400182a441c1c01a001d00888240980a0000e5000140d00c40c02e030300340a110744140c03241d58001486103a0841c00d00a8824200135202d0b0450740184413100201c503d564100c0d03520b1050311003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 577414379 1250 577413129 577413139
    0x3010207060906150801090b01050f01050f12070311180907020102041d0702060721020a030603021c0b06041103130507030b0118061a1204061104090209121f05070e 72
    0x52082025075482000344c5090242c00011058844103410308076585981c6c0280340c8101c1000510140c0383c50f158641003400c051401c28903100c1e0540d00c404960b08980754100a5800301c10a006000c2e07090b015068420b40d606040c01e0410a4000456200081030000c03e030148a9900c0810320003072007901114050020600e0812540c2c0d41004100c85a81c0300722a5000140203001c04a545c00b88101c10a2800b101c14030401907035401c200e0141c80003980064403942c10325698180c000010b8031902c03481d0717140800c0c06c03c0e8804824400c0c100b18007440401004540b15a20703201c1e603000010501d40c1a01d070010344500300cac038045840303034540b1910345407954001501c08503108000094182d016005030850400e02d0310f0a1120300e0b901e4a007100c880144514000e04400107004041600182c40c410541c024010180030801c01b034900320014060b4400e03000781110b580c0024255500c0e0429000010382c10003924000c2c03d00800c641c42a0040340c4e8482944642c0a4036200424059881034039030207908500141 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 577415629 1250 577414379 577414391
    0xf071a01090207080a0e30100504030c031412011e240305100b070b09160b04120c0e0a140c0405280e0a0b040c090510050c0a0c17060c03010b180301020706 68
    0x14000000b019020401c402d441884100c0c0d03142d003170900509c3d00aa074140c480320000e000305d0390141c0f41c00e40c3c540c4070341c10001020b0090140401001c140c0c20300802040d110032080e02c110401c102c0780444550071640506240300b18a00b10040c5040001180e10081d1400095640351140d9000c0c0b103a0542d48461126000410341c541480b080840319806050580f048600e9642c1d40c85100380785503018480c00040c0003092100308151031020300c0310240d1511034041121b005031075400100c0b080a00b1b8400040140d590b4200142070b00d62602032a4104020401c42402c0920b4100080d207001c003c9a0050000d0031036402d4004460000c0d01c98101500804505010300c0c81e245444000a000011489100d6424041d000c20014010038400c01aa0f0340130781804c41c2400c84c100166019809028034044510410102002069401139180050500b00f00c040c0030440940241c58074125010340082170703076881000108502503000d8101c40100c0c42c1140180a284000d000090080c00340e41405051281000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 577416879 1250 577415629 577415689
    0x402160210051b0d0e0906060d0e0c0102070602160303050a1b030309110d02011e1b0b09010e0f03040e072606040c11100e030f071a01090207080a0e 65
    0x60007400c6040035000249154041c400001540c940b5004013410106070171910307910031130824114055004c08050401031034054290b0040c1e046901c00314006080d0b070803403480c0c0c900035a414401d0b10300400c0e141c03005150048e8140100d107244046440024148480014103c21070350051114000400901502c00512001410050081c01401100f114403140309400c4140d585400382c15050f800d50107a41d140031850241e07107480c590411300c0c440d250600c000c000114150070840c0c51015142031180c1001507070347c1402c4040c50b09540c9940c400d001c0e41d400c203d1984003500c000005a60495170104a00403d58550500c150341c41c3d40102954416600e000711080102c9841d03500140c0036413003d44081215800581040351080720b2154140300e41d41020f07545102030350b00f0390041007030050b000c4140d9103030843c003c03c07504650b800b0b00400c5407001c40301c100b1070009542c0c0c201c1c0c240c0108048501989000240e58410443e80304420300752092103a800306a0195855506d13100c01c0507444000c100840203104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 577418129 1250 577416879 577416887
    0x1e02120c0c1912020d060e0a050109060b0409050a080703030605040507020a0b1012021905091006030e0a0b0f070c05030a0c0501110408070303051608040303081911090402160210 78
    0x18640c214011031140100281d0b007241c030016402154100d425400c6000e25035802c205145a0301d100c280c038200d4a400034100504414441429141c1c858000010603030700a00d00402a1a5000c0d0b04a201d03e00e0310002501003800460000829644481819950011441c095000702855003217190014070381000c0100007500001e182c0c040600030203908a581e0b880e100420b4600b4000c0c0a501102d44001d0000001401c10482d000d84000482403440002600c4070701061280034111020f82042380268420080b481e05072080040543e85032010782816596901c0320040e2500c0074020000c48481c404c0010005881090819962503200040c2c0e940c1d600c80020041c103903840300006840551908040c46010301c00b5030203c03001c8a15020140c050945140c9050b200c6800503040306010038410722106001440f050700620265100783c440904a0400e0f040e1891180780c400342416000b40381104102207002d204040d1250b0200440b40943e5036403155000d0a211010078400035004541000810112a04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 577419379 1250 577418129 577418143
    0x12150e04150c0e010f03090b0703092306060d061401171e0705090c040e09011d06060109150903211b0c0909022d040f020702011e02120c 60
    0x55480c500d01c03028400c519404603802211418045210700e0b414030000d50107100502003425007424005030002880e1501c84510408441c2031000a41c0e501d14034040000d00b404140822014414400c941424041e81da0f0340c540d0041c14040c400c1180038200c0041001d290040b0741000303100003542c04196940d00d480503000005400350302103409050300035444550180758040184403a82c004240e0746e40b80500b0710800301c401610b111000c01d42004049502c09400b20f5060003200b24a00000e060108400d01420030300341f80000c1e00c07242c1c100d135091021680e40100b01c0070659840307e4080d42e02c0351301440240d801e06050b500043c08000356624403103441c228001d42c40c002e1125911100c60f104c0f40c40b60142d0303144d80a42401080d0501c034100034403543d5401d900c040c6400d84040e1428520103592441030760610506040b07604140c01c2001840b5040c2841d016502c0034840040e025800c0020580c0041c201d07591b0610180c000c01203071041801160b102700414042a0115a522583c0e541ca5981003a182c0300c5d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 577420629 1250 577419379 577419383
    0xc1106280e010503041209051005090f010306030818030f1209090f13060b030c0406090c090f1a090312160309080d080c160209090705280612150e04 65
    0x12a009080c0514020712001030080d00507901d091560b980d542c0c0307003000003504c1c001990030000e202202007a16180ea4003002200d42c21521441d440e040d1034020000300101c209442810141806000c000140c00da200b552048504000071801c0d00d0321072070100e840d01185141180c42d43c82113511030000280140002c0c1580d4000f030302c08125950380e440a031103207180151025601c1910310700d80c0c040411a2a40a100c60040080030b03240000c07004400101924000e400c801c03c1955981c400e1018150820400720041014101c501c100a10300345039003040074400c68428450010000d10766041703036400c1c0a41b00d2400341d0462800d0726070ba007408001841c0e030840b510460209005a5010560b803a00140c0f0761003050b038a43d590f6280d41d58030b001c10034107a004540d07a502d1140000e2100d9005903994000b4505c144e5400004101d880c0c0751108109252602082c00f4418031061078040d9001d03080c91020005650030707420311101c00498543c035100280440c90310b242c003181c00604007045490102103c2d502841c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 577421879 1250 577420629 577420687
    0x17040b09030c06070803071d190e0a05070e120703080711130207050d0f0507140f01060501090b070615090203090d0f08270109051f1d0a030c1106 64
    0x5002c0a083c005240b044410141100c00240b0028000520800320b100f05140d0000070aaa85244e81d80842c5003242c60000e4081d140001100501080884001207a844042210144020f007070040018080c0e030203542659010340e40d0100e00030075440040080710015a8040402d035900c0c0702c00d003058505026410300b0070b403003516a9a805011a5030034000c1e54000f130f070070401801e42c1c058400403d460300c428006000701400014018080455004003d64840c0032981002c0c00b0040c2e02c8a032100d0031a20b10f41c00007814070000a030103100280c454000e44600d84e501c040d0001303502802081e4001855641d0340400641c0380000700f004000b007808200303420160342d90b032500101920303001810b540380a401c440f19114620b541c3c0769074580881c030f40002007101c09500b000182456250b21340d00e003841000d80725995400420150031041c4130051041414591b100e2050b8140c0c03400c190300c1617071110100500a8100700b00c0c1e0b0720700340038002001e0800c42c001c0b000404a80c0c0e030701d00708449003003000d41d0801400101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 577423129 1250 577421879 577421893
    0x23010501180e090d170114040216020405040b07110a0302070b0d060f1205070f0e06091801020d0b130c0203180f121e0708070e0a091403070b0903040f0b0717040b0903 73
    0x5204807280c5c0c14180c80c581c200c12608102140188002504602d24101030082d00410900240c1c95500c01c0034010341c0518904001c510305954043d00c08a01000540030071340c041500040429404900d0784103803800b1404860365000da41001002074600da4000104a503019400000e00101c0e070004441c58510420076582070558400c1000c076440c640b88551090520010b0004d8002d141a552040d071041a40344481051003890804a08980081c3d80f450007080c1c1c0c9548600c500d1500300042610b0808488050041c0c900320030000f5124010000d9800041e441030300220841d6445003000e80c0034070310203440c14440611019600e983e0342c041814455011001180c40301c034200d030124051003524420130040244070b01d0031800c55140d103402005211119038034002000081c64181c003d86908070110300035606c40f4014200035a607000081d1002d10103a004010421501440d00d00c1081211240c058441e02c86040d400c00042c48070f441d81c3c40a00d01c2000003000301c1d0b201e0784000540b00d0301c0401d4044a100b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 577424379 1250 577423129 577423157
    0xd0501050a060c0b06032d070e040507030b10031b06030507020a0302070b07020a0b160506070206041716140f0f03030c0723070e040623010501180e090d 67
    0x200280207407800126001d00f0803011905014405401010280455103034070f04801d0075000e60a10406901c0c0b00c0320340981c4a003151882042001e01400018480d4456414155545a5100c0d50703480003d00c3c1081e498000703210789c2030b5404880021608052485070f044c4e451280500284040e008800209107000e0109240c1440054603c2440b6410f40007407a11300e0802d01200000d030005502280c0c0038105200202c4c1c0103d440e0081d05c5030b034100b61801c84018049242c00c49c01c00c5801445201158010340070000812040410b44d01391f090810b03030300e6580b0313014800e000140400c48500500302342c2a02e02d0040001c18000b80c0030544451017010364204a081500e55034803880260740310303c5641300a005190125000c81c50700481600f0b1a02688466039074501c0090424007a5071220a400e41c1a4040009002d04c500600c400c03100603610a0000701907240e5120030501c010b004003410850b201701d40100172010519650003501c2c003600c030072001d4904091040e0f0f84d034042c0000407000805004140c48 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 577425629 1250 577424379 577424389
    0xd0b040e150a050a110d050109141e0a09061a09070c0515090114090a031202030c0d0b130e03030405070803090604092d050612030313060905010905030a050d050105 72
    0x1040801140c1c41e40c516840d00e0084074040c140151038142a240e41e15007600410a05600901c080c900048000c1076540c50040c442c0c007290201a066103441c0a420108104131810f82000180880d149840c03c50303e81350403003010024192840010b1080d440c092140d16039055012140840210403180ca00803603840203002c0f00c1d04140ca4900a1150744540e454181c0c0c0c0390000081c0d540025000c0001541011000c5494103894044d5400301d41500320585001c00d16034400c0c40300c410b10f95030000c29031440c00d104102c400d0500c02c840e038940c40c2e56542c84c8003141ea507a4030021030969803030550040c008a5010303c2266166841560100c0c3d080c4035480d000501d042000c41a01c5031844001e1a50f03051a240c00c1140001d0b141c0c070038884a00101c6044141242001e0034500210082c0c20000011149009414003140712070080818400d54000e108001909103d58414100300398071030000700f2084500d1800300d0140c0501c030001006e5000c00f1601c0900c1c0c40c1e2240c042e0080001545087c45241d90b50001c2c42 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 577426879 1250 577425629 577425643
    0x1211040c0f050d05150d21020a0209010303180e1008100b090c13031e020102250504200403080306090f06060304120509030a050f120313020f0112020d0b040e 69
    0x290100d841440b00d03001081c0c0d15841310342e00ca142020100c121400313500c001000c1024265085601d12014a84440711a0404462200c4646580010710031900d054000410030401444001c08001e401c0500c281010008601c243c02403400400240041c2004500303a48544020b009101071842072500c8410b030080d05002c0c176104107502400316200ca88803200510015807000703600006030902c40c0b80010014400c00c40c089030003018914816480c450a1000a0600317504200c03400505540203030844a450100c00704270200c50040320001050300c4205880311018081c0d04002030914800b080010038450b00030003c6104100448001c03400ba41c5405126405400c181c0f101a00500240700050000711089003032228015241000f906001051000030718011405404030703201e401c4100700031607e0300304120a8205224484e40707141140b402151072504034001010180c0318040410742c06069074001c030300c80712491403000e81c25950348800407c6103000d040480420360049203084a10601990086494 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 577428129 1250 577426879 577426907
    0x50405060403021203071b140907020607120603020901030c0303031d03030a0209121906050132040b0303040b03040c0608040f2634030507060c091211040c 68
    0x90400b4155001e0151509100e050840d243c8130810402011912851850041c2210341114003542c2d814507a03c6004515100f00d039501030b0311943e06004245d0740120765030358400707000e14201841e0340600c0051000f1300385a6002940111a6400100c02d0040e080844802d80740646c8040c00b90381c032014820440000103201084154100384003080c800d6501f03030018000801d0043c45040089008171840741080e07000c400b005615521108541c08004690090278014a100841850f42d04003000d0315520b80b10809c8205030270b16517902d41c440c40c95621580144e02012004d021692642c4d01d503800415540d00035641907a44210710140000e100f40700f201000c4c03142ea40f02d280e60040d01465a590705003600315100c0000c58640340071030701106640580280040604202048000e00714070200d04006205001c055050320280000c0d030400b080e004401c0b18403141d445080040c0341c1c1c00903402200c4100c06a0042c40d01c0c40043c41180b01484000c007119500420112010821080d0118080d1014004003000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 577429379 1250 577428129 577428139
    0xf0a0215070507030f1206090509010905100b01020a08090d0506010f060e03010209010905090405070312120614090c0d0e0102040f090b1009170705090703060e070804025a01050405 79
    0xd0000e91b40306200340c10702c0e01520800890682e454054234000d40d030f82210f84441580d55903a2000900c8020415a2000405020100008552100000d45881440340c020b4010030000900c05d2642c1c480440c0109556044815030303140d07585510003483c4001d803511840c40005d43c3e02c81c15000c1444c0603c00c545111005071504213200e4070304414400600c10042064505008002c00040445d0744004420800529692180141408c2d0040f16040390095008074030301030315810310302405440e407100b25600f00448a80310b5072a142e4003442d4001500594440b60040d50002c50000740c00c00c241900d0350281d814160042c4040c0c1d0144040c00408c0907038181d120009801c882003003050f05440f0b01503001c0c5e495406d09407080d1f00d480300301158500400303848801c0000c1d0f484030108090001413149580040861030502520f00740760b000036020319044494120b95000490b45580e2050a8041a00c0c60075010300110048803000303408080d4805c100b9007115484c10701001914041d610034012074080e2040242 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 577430629 1250 577429379 577429397
    0x305061201230c07060c0e010921240c0c0210030c20030f071506120302030702010f0c120f0e01110a0b0c040b040e060a150c02010804020102030f0a021507050703 71
    0x2c0103a02c410182105450920802c00e00c000f04e5840d000f95046d4000385c3d1503000700400c0c0800014140e442591003c40900400d9014030309001c1d45000803a0304a4000051001402070ba80d1515280382c82820b04450341032410307003600b2801d90030003101580c280c0200ea4001400c1c000420980c2660102c003504000146641d2500c0200c41d00c0180c01c610000100d81102d0074005200003580465000c0c3c0d0050b903e4011500d070340b00780700285000303600140c0f1080081030713070700d041c2a540a50349000c0d980000381800100e0000307600c6144030300704400c0456042034071880408050440a1300c11103c21400c6000500c0c012854031895000f040140c0c000242c003002030100c401c107a128240e94103805820108002020403000440f05548006000031388516000d211450901c0320820035581c2c92075115182405403140107406260700016000300e5145c0a00740820b66584910040b4254400c2c3c80121140e02004200074010680c0007a00e0000d001910014a0841c1c54907002910742d07004151000700081d9041c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 577431879 1250 577430629 577430681
    0xc0411190f0e040b1c03031b030501080c0105040b04120f0807031107090c0c140f0f070603060e0f0c0703111002040608010e010f1701020d09060209010e0111210702100305061201 78
    0x74000d882461b020346000152544004050f20381700202018031f02c00261144010301440d1f605001800070070409081c200c1c9064900300c0722880134003da1080c4001908040c1088050100c98040202400c0d4488000e80c0e843c013030b520b070181040f81d851315090006c0c0b0030800c2c04100c4070014450300c11054515154006003440c15510302900c140980d101c00203902626200d20f40b0814100003c000600183d4080d0400c242040c000604031946903015034680203581061114060541c005541c0010307401e400f840d074a12180c141074464600e03a240c08105849095800905400c0360760281040d1502952000b1250b41e84490601c4000002c4c0036242900c880310004008502c00a42001d440a8080001508189203d891081292004402565090b800140746011981d00040740c4d40c0c189004d0138030080d12003031070b81c409a50b0303811140d24450250407aa21101c01001620940e014aa8000c210360504240e80100030043d142c1035402ca40503000c03640110b210190180950f840000e48105540700c80d403141e17 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 577433129 1250 577431879 577431919
    0x120a0507060b0f03071403030c06161e0503131406270a0206162d1104230a090f15110708121b070507050901050a06020c0411190f0e040b 60
    0xd61b081c0ea90500c001c0020416001041c0700d9640b0030000110301d034140303218415001c0c03d80107180007100340c10f1350080e0440b2001c40c1c200055a4220301143c40205061510b41307008518001e201e0607140c001c6c8140d00810281d01000180a101d208010300c9114608a10b1080140d640c1d03641e05000f5403101c018801060301e44010402c681d411406600c1d24840010104140003a042e165000d0031882042800b15400740440f102d0091260001034504100d4150300300f040081a041000b541c280100d1403502140340d2103040e03001820781e250013068201e000e080ea8940140d400c0302c2012903110450601c880302c0ba02c55145019203001641100300c261400414140000104200070030312a258017106e084081c0d00903c0002030180c0922910041117001e040c00104505860143e010922608203410700b030000b2a400f040c800ca43d50015180070642117283c107407005640c000d102070190840f005442c100704166004085c0100a03106854100d4617110541c180400c1e18442c1810740d070845402e0700000d00780f9280c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 577434379 1250 577433129 577433159
    0xc0b060f0603130204061d1b0c0d02010209090108060705040b0a0519120506030313090b0609060a090303030b0a051806032802010207091418120a0507060b0f0307 71
    0x1005051540460401001410341d8100b0f40d00d4800190010a8190031400c05128840161a01188100184600852804920000030b0101500110b1a01c92100c89650402603d10003402c0c0800d803903c261000b8402030003034128240e072511644060b000000c0002c0702080850080555030b4605281c1402e19407200c0da6a4400300d001d0040210410070400d00341c114406074991401555034090b4081c540d054407100340c49000e000c1d01d2003a003013081010407030f10389082441c048544c081070118150069500145140c0500c8440c1c0c0d0300300c80002204000036620221100c01e5901c00e40f0200080b00e1044140315540140c3e0007040d4100c2410f240b46460840340c015501c0e4801801004c03a0b401c25000e070108031000c1c00d0b03000400d1078480d00504400840d80c05000703090207041101c5003040156100f4000c80441200940724940b0b48001143c2c240c0c48a60901500b503211055035030b074664410074140f004084d9445443c056071418a844a10002403802c2c525000741048018010802c1c982003072584a50941 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 577435629 1250 577434379 577434391
    0x606180f02041a1806032e051f020f03030702010c0801080f07121b03060b03010e030c0a1b030506090610080120030703270501184b021009060c0b 64
    0x1040340b01e40c0d13540340d0700c0000031072140030b040d1000c8028444008003074820703048040d4801c0203c5010030f41400759447e81580b2210803886260b10720081c1e1704541007030303003030001601d130140d17a5000c008108000c075501500491881c020f580e440300c20036030b691745000d80c03a240d4000030707003666412416042100c400c2c5480d954841c03600849008042038001905002c0c2c021150b44222000380e120801d202c682e2401b84141c000c1d80c5510005107143c1440c2030720164aa4148100040c01e407058080359003c0e00341d0801e134030000346038404211402d60a000b080350b80e4800c01201c00c10065005d225011800c1354040c002e01d0319401c0314541c0210640510703c50342125400c018451010141d0343c0740c0080f9070055018903141e94005800b00b021020195080803400d541d116400e159100d42203500d40c80000b0340444003440f07a903180c10144840300300300d8501c020299000c0650034a00307101d2030714103042d200d0b0a1507401c07081d28803c40340340f624030043c03003001c1e08c074400f49100b4100411805032210b0007041c00082c40540c444 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 577436879 1250 577435629 577435657
    0x30503010303051b060a060305160f1509080303090102030109150b07110f1e04151d0406180b060a06030c2307060c050a110102092b0606180f02041a 65
    0x3d913950201c54607003c0308032421b1200b03036240c031803c0043c05418014030403180f0409003800b80b518107040c0210503050180c41080016002d00290300c3c0340a10460284c00500040d0050b680e0701d04040200174042e41081c000d0641182c600115a030002c0390315480103084a084100309070038461207880e440601418440380c1ba400644580e003c0c002e581e04e94001914424440340000c40072110350f018002100d016482c0300740b01e656050300038003d507481000446070480c04c1551131581c070ba0790303485c103940500007000f4000400c1c500700c0b65050408c884e04000c00c0c490103003070f985a41d4480d0f03541000c0702a100d0400118020641082205103104000420040a00101d0b00c40c903140c0b69036981c130b01c0c1c01c991804d500040051f0020880342c0c01c07564440d02c810b60800780907009504006030315000030321018502c0c1c80d4482400050309040d500c0d060f080b020810030340d00b0042c02c200c1155190100b00e40390000c0301c512003145142c2040110041c1d511300c00d035019a01c02c074283d050341d0305216110207040c0c0e00c0891180565 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 577438129 1250 577436879 577436917
    0x1505040201020c03031909050f0a0b070609020d0602030a0b0312220506040902040503100603030e092e060e04090c2c01060c0c090b0f130204030b090c030d0c03050301030305 76
    0x141c400300020321403406c150104090044500e00000c0608245411082c40303000702021010441c0e40d81680030003660a50004190345844038540900180801d6070300075005030110141d0340900c0980d6025500c14094894103021481d481020140c135080007442d1200700c4101403109840401d840342010120750b0001411746100d44d111030018045030003039070018249035000201840a0309060140c0b4011428186040c06a107041d039402520342700080c030440d801245000c00241e1103038a035040e00030046601d58110000d00c1907111440040310707402c2c05003401203900e07802c46110b1810f240c450125042d030002c1d810380c1c8850620f64401c2440720101100e80c180b034030b07901e1800900c40844003401d00030105611000c54119247c40c2c0071880142c1c3c2c0d03200081148c070b041101e130560f89401d07000c3c0c160802c045030f1054801d03c00700000320090066402c080d0109020204100342c03004d0016004101c1c1404404507550a50341c48411207001d460014003c000800500040000038090f1010309070b144060f04c00e50f400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 577439379 1250 577438129 577438153
    0xd1b1403070c0821040c1505030403121802040c0c030206100e04020d0221010903020706051206010e04020c0138010f03050405070e27060c0a2a080403050709050103150504020102 78
    0x4002404c0d10f096580030100a010000c0d40c03007d003402140449903003012415032a150314040c1280a03043c207036a880320b440d0029100400e12615290309120342c02441042003c00c5030740c00918000300d000c000c4002d4403d82001c076030000c050442000458034403850400361660741d903003444000001043c0480c0c1011016425016101800b4819004201c400000181d842c011342002442c0030260707407001090000803c442e0700062850107040d5031240d401c1c01e04070300e06035a6070f002c02c001748640d207040707111546000b5410040d110306031813103201030f04c221050401400c8183d06100a1007200100c01340401c1d4091261510705010390400e651090203801515120760340ca610b1002000000c50701c0c00c01202c8014034001080f20281c0d43c4003212001d0000400541c60403040e203050b40e1180c00045802d00820900503108140c42c482d40d603a1144c0d00b0000100d581c8600d02e070422a903001070104640b10f0040401c042019481441010b041301c0d00084c040c21550a250602c1c0003d02000d003042c0d0460003080c0b0383d100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 577440629 1250 577439379 577439437
    0x10b06041a1c1d1b01050a0c26130b0405030304120c03060501030c1706010522150602061e07020a08070809040603111201060f09050702030d1b1403070c08 68
    0xa000f01c420100b10203880c1c89503030007500301012207106210301103841c2142c1009981c0a000d459260105c0d040001d03031444581800101017510745242c1b060380c07581038900c01d00521810f000e0f00c40310194401945041c0d480d910b50940343c0c000c5000303035a0164403d200401c919219040800300f2940600040c40c122a100c2c0c03180d505844e0242c00503a040380302100204003040c0d8102c100c00341e80003910060421941013a0000350844a01d10804568940581c58030303048180903030148100c001040801d40806640d20000f0f901e400080341c1c600c0a0008080d13607407003907150100c5030702d2060826034090800f0340c0c959070f03030320300541c00ca4207007900c10309814010b0796050b0700c1d28490003001e9800703480e5402841540c07100b048034018003801103e4090f41081810000b02000340410003d81b00560800f080b180d0360a0812491402030050580c489801c0581c0b002c0e5480c02c5207030302041d8680c19940e00c241601c0010710850342e480103440c0600082c10002c00e4070080750004015110b100e09005000004401d048605a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 577441879 1250 577440629 577440641
    0x30711030a0c11011107060806060d1b02061014010f030b0627030307080405060315031e010f0c050d1119030506030607030b0108040308040f021003090302010b06041a1c 74
    0x10301042540b0703142c10034480402030344000e1031400d190074403c102000680c0c58840740d013440303468107001c0c0c9140860b110356100d40c1503070700c040e07881082042040480c04882056560603803000380540a201c0201d12070f0028180c00c1070a4588140c510104103403460300448130308401e007400706c0816699110341e8900d03a603501c004000b002e8064070741d40644a1030340094212040750000c0240704e03900400428000408881c203032001c40c0c41c1100c48540302d0740c904050f0860f4545540d09603605000382180486650200c0390110f1400c841c26008104172209a990740080b60115082500841c905220050284000b40c000440c10b4a054507100d00b042c7c02c1e24007584044c05140e1700000820740303c0003082510b040c10048164051038500d02405880b8030030001a1405501078005001c21400000050600022a21001d99140c1c086c0000081d607032010070040017019004c50440040d401d00f54980090301d00141550151052154002e500346090445013000c0da01101004010004a840030a02d179070842c4140703 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 577443129 1250 577441879 577441897
    0xe0712050403080a0507020f0a080d180c0315020405091501020106271404031742010206010b0f210a0c081f030b0c12040c05040b0d080d0203071103 65
    0x100c11903040c495403038825174600502e54400c40d400207141940c0c00c100050038403481a00825003603034030354200b400c40c006446400000c030a0b032104d04589074100138451610004030780c016281e808803d82c0032841d03401a8401e0b4072555621840500c086581c188446030f189001c20414000000d480755a01001070300a841070740f0300c214007034a0361a241c50b1030200b400707086c0c072000400500e1856403603c0c1d6009045801d01000302c140c2c0708008000600c40c0e02101500c80b035034480130003140d40d60400d0790440c98550b000c6482c101d641c180031518172080950000070002c1c180c4d55000481418810301900710350007130300a140b0700310225040b1300450701c049004400240c0a1155501c021030344269440340174050a40c0540048407560000c52044442e80f000041b9a040d2540107610f420207072151030641c04180101e13031a00031510042414402003156100c01d100c21580c0c20385090002030408020031036401c81e50b140140891508100c3c0b80e00b800342c42c1d4015588002c0c0341c14440d880900035070082c1d113075421014036 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 577444379 1250 577443129 577443137
    0x30818120d0f0302041d060102071706060109050d03020c04150302040e0c0a1d0106050a0302040312030f0c0302070b1602070f06050a09050402250206160503210708010e0712050403 79
    0x100a10740c0402125840002c604042d45003600c0c00001a5446c0c82420007021700b2003802c404245181c0c0301b41710f950010021001e1554005480140b01511000c00f0390340a0301250482c0c100065509208800345081905a0083c0c226a41300c101844040d1850801040440000312004001688d40d03115251103404d24030028030002c3d00c01c2042c080002c4007a005048200001c05a00751049a4040440e06440c081c0c038207a51600140751080e806030280741c20080500700b03040030042040d64180e201000d0151045024001c0f070b0012f0400350304900c5250400707440c0c5814440020448116804c6d5801c0304901c0d8412140c40d942d40c1d07103c0440100240c3c1192000035000140204c20310341c005a408050a0200e404528012034040c82480c800b445250340030320035003841049410b40d603e034002d80700485504103103950740554510744503407070394414426204c20440148502c0091302042131000e00c40c18880c0c072411041d03400c0100c803110125000f08107904110011010300712030359103400f81c18012407098803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 577445629 1250 577444379 577444393
    0x303040f030233070c0b03070f020c100f050309030c0f06180601060f0818030408070911130531050f07140414010e15030615030c030103081812 63
    0x20410240025a0050004204010712543ca414564180ea09915900d0409455a80704c15207450804007219603c07090003510080b08100c0d1803a00300341c5103130a100d0a0782c20380d04082500c20400040f144035100480010302c1d00002c2c0d400c05400f03100151f401c0003280086908003e4a00d10182c0707040e601c082c50184d03079000a03003801642c00140e4442600420f851020f0035403581041e80c01040d0074a12494801080304001c08120051140a0580c641501c01c00c00c0e40c0d40c42d81c44501071980e40c0000e1040c0c3c014940341030b0f910551a82c003041950401c05111011450a49c5441c081140004800d80e0181c0ca882c0110074036401115980480303034407594114004281d1b0704c1e0059920781c0580700180a0814000081d004581b80c01e0014210b90a88141e2148104001160801255501c0c42250015001280c50295007d00078140020f58420b80084981a002c4910b264001c040da001c00c0ea4030100400043c00140000354003200607201a10b48414100311440d58000010010500403d1080395030700310724 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 577446879 1250 577445629 577445633
    0x30a0f0605041107230c01030c0c0b010605030709140f01030207050f0703060506120309102303090a05010605030f030405010c0327060801140307031b050d0c081b090718050303040f03 80
    0x10f210254805c2c20b00e504030b009410690040e54440c0c2154904c2030416903a0b203061120700d80212004440281c03c150a00025a141c9a0281140d402900c0315804200c0d0800006084030300a06c01c4258400701900c04a0a5881c0c0c00064019410807030042700d16008008031051014400c11419004500501c004500346c04d1010038048840340c400c281ca401c54008021402c0c054a94911b020020001e40c80d101315102030301c00d10107a001d0300c0d4000500c0384203400814800d60b40d1000481c03c65841c0a07100030404140c1c0c0f4001c055854070080c00210079a001440100301540c000d5011101281c001d04101000d0110200a46034010605101c403142e14a81c6009020503984024428090f02034000450101e02144000036035441103407000034001c0364044a0203d05140808c0c01100500000d030041d05e0f032451901c1c0c4000b03461140e01441a89200d0400b40d0ba03041c003001c1ca0b0792010044042d0504080e610b40000c107e40d070b15620b103480f6041c0030006030b0020721505d0400003080140075954107408424254 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 577448129 1250 577446879 577446893
    0x216232b1104020405031e03090a0b0c060105040e0706080c040f03061a01140708090604120302070305010b06070c17070503031306021207021503040303090501020d0c02150c030a0f0605041107 84
    0x80c080b402603105000901c669200094511800c103200d041c805121112000ca040c0b441c451102419001281d1010001e00858440090690030b5206c100b901d0842e1703202c070144800c445450060303128550100b402040303002e000e00502c50700314016650003460251035552014501106e0342c4110343c2c4a545d00700d8040703901d10841d41d130404c0601c03d18110426034020340e5200d0443c01185000351000c03000040300380d0381d07903941b00445004195410765512000f10604020707482e6102803005913299400d10100000701d281480031511155417060f000403800381070005a0180b03602c0790100303459910980c0d00204003650104003400b030010060341155680e50030240028103000102d090352228a00520007000141c0d03a890760989182d948142461320382d60340341800c0b80900f0071407202a0203075200083d034011900154000c2d025901c101c1c0c0071034900c08904d40c040c1e50501022600100d05a80c05c4c0041000c00300140c00c191011100c14101095181d00c03000041c080b2941c201c2c080c08104030000d6600100050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 577449379 1250 577448129 577448153
    0x60c030403181203020610060f11010e102703050706050a230a0b030613060b01022506030e03030405070306050601020f0f0313051807030c0306080f060105010216232b 73
    0x155600c1f00d11070785407001c05884002c8200c812814481e0380703440c50342200320951240300090655030441e40000e00d00c4000400908200a03035200c050110a440103452002444055940341c0c540d1325246000440d8490070000c10000d08200302141c3c071443c030b48200000e0155040154800c01294268504081c890a822a040d031101e060090300294100241860f8040d5041900c0750803480c0130940400d0000100c1c104850b111141c002d40b8541a024081e880d00c0300ba01d0f000b52141600c04102d405034075002c0d181d4902080300c0003000ca034042d00e400d20015000d0f0300455003002060040340c1000d401c40d00354909103201c100c050500b503070011078101390b001c0005104400505060701c4014071340d000442441022100144804c0500d42c69508030446603101f544940c0050104c101078441c802c0c1c02040705074a540080c40382d24018810021440c82d820b0408102070b007100c203200042c445d48035590580100d000724015129510412900d031607005440f1049007945d440e901b100300c0956000041c9480031078260 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 577450629 1250 577449379 577449391
    0x60b010909090c30081e03060913080903120c1203040305070b060d0f060b18062115010807030c0801060311040f0e0d030b0a0801050405060c0304031812030206 70
    0x1050141d6100071841501941040c0c9845828011920404440e0250402c18200207410040544415134080c0310821028001c00c210762480e160032010643d825003003034001942d1090303011641d90301140a0862464102c9041803281c2c8080d418003031482d00190420001000710383c040c0c400025044034840c400d01180030b94a0040160604500781502c0c001c25502401c8401803c2581400c0440c006541d9807052041850b03015007910745841c41d030f06d880c0001c0e02801c03100381e00600300c5202c0c1d800d1401c1000129841078802615410319403881d55440821405d8103012a03145000390155a0300d61402041d06c40d01900c64036000788201855850f01d405181d2640d032001c00785914120f400c1c00050454071001c03160700012035021521045204840008010301100514144034040d00085840e4040e08882440304084610090351a034540000707099841c220f50090450700130381c000401c4208024055608036000b49080030190651080c0e0003e40407080d0094002c0a03054038403041003550402446510803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 577451879 1250 577450629 577450631
    0xa090f0b040c0806012d0512060906031207110d060504140f0d030c0219030806031e03030f07090b0f0306040c0302131401030e102a05030f180604060b010909 69
    0x1640c1100c0060503c407003e0030250402110030414844545010007000740d902d25a10000e0a00b03a1041c0d001d406a40012081581e840c400000942d0502e89648854404c031806800b03003445a04220b055280c0b50b0020000f114966014501c040c2580c440402d5400114492040040d66013428106124000c0d9240d125140075807140002030310440340400c07210a40c06031814041241580240d00380d080400318040001080c3d9001100000d040c0d0064a990081c0f2066003501d81c15800741000600741e03c4104035008480d1b00c1000881c581024803242e0031b5000071140317400c8461a0f156100e2104540c403224200c1c002800c04418408a803400b0710501680d070380ba070704085141c800703840324002400d00d0314400e00c3d0070328010901f055001d074000c1c1c11010b29205440195003031140070021400080685a4046401d5501c20f200079580e50306441c8003203204c95064a5007811a40d030640ca0300b01880c03001b410b8501ca010351074801c410fa8602085030030f008a2041c0300c0071894909842c00104080b100d1386c0081062 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 577453129 1250 577451879 577451891
    0xa0902090c180910090504030909050903040f0b0c070803070302062d07080901020903101d03041a1305091306111903091416090509060c04230a090f0b04 67
    0x2c09410818801c240080d220403040780d944400e240100e030040c2d807180e407050341400100410994020414401d5582d0700c0d0041109443c1d11007643d6403401180905038403e80e07580807d100f00d041c44005012098010380445030a25254001103095400c060002c40269000d2403e001f0701b50700040c8400614010b00015800101016407051881c000181031034007402503c4010414060003034040301c981c1c03000541155080d60040444100900c0740c0c22010112010100028072800b0b0b0100441f8101c0b0901c00340785450310701c010029080396011185000380c0c0c248241c0d00107000c2d142c40d0380e40c900c80e05071002c103005104001d042c4501658503140070304049c00820000c0c0c540224603940d541200c1040b92500080407101460446400129951070700d01c240f01e213207071031007100d807054212030143e4000c10004e201c240c0f00c04003100e81e40c10b8180c50201c0301d84001c0c001804044180043e564542e881d8404051868140c0400314a03003455a412003401191508848280c5c1500c9000e0307012002400d640c00c00030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 577454379 1250 577453129 577453147
    0x4080403030c0f0803010b120a02071a0c0910051b070e070c030e031b210a0b0601030207150c0908122b02031e0708041109070210050a0902090c 63
    0x5620550000900344046441c000003440020b1a1070000c1c0703507001c05160b5607540c407441903601e980c021960000b0701800000014a54608900951b0082584104031841180b1082d284420640e402480d10050110030b11042c002c0b55602e06c800013040800d0307203886944131b6036841c6680046a10440541c5c040e8403e41c000c0140d036159500d4071341d0000da40d01e4000380f040c50034130302142c8281c2c02c0781e01160703d1312440c164503640c3e04000e00701d40183c400440f0402054202c42c144954200115401511117820a44481d00840c500111250344010140340040c9000f0345a940c81c600c1036225a1021500c55a6042d40742440e500700d1000c10150110400412041d00070100051880c400c80320010705a1a481a107019421200403070118a524021015500c034a0a1184007040f0050448074074640b40c1c0c80d40100e41c0b85405a080070380116000f103105141c0c542c00e80c09020403000c014040e0300852040c0f0540c0c1ca100c041c18402d16006403004070000c90280c002d07004100350700b800545880d080352420071a01c0300d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 577455629 1250 577454379 577454393
    0x6040c150c060e030c011808040504020f2502090c0c03030c09180106120513200102071d180c010206070e0301060324200a03090606031407060210020304 67
    0x450348160000c1054a85000d0100c1d6030580d4400018110b500300301481d10503a101102400303900f02c0a100821113418136554907090a40c80709009040c03c44208018840c90a25070000c0100240201a991511001c62400011002440d0808030584803480a10003180b070090400c0c0c0d0400d4aa0350018201440c8258442c0c0f20320020708801c019100002d00c07501c150f01c817074940601c05019400401421741e5901d038040c0c10b11a9810404045901e4540040d24000003191020380480c0c00a90b003003020903e503e0803103070708102d154441d4150b10900c2c5000405442d044a10780d04200744000c000348504008262180a4813a02a8603d598010594608850b60b00090040c1d00410a2510104890040002c00c0c01030100c1d400c040c0800c2d01440310102605600490340c1355003110303003104000100308210340040035004100000a45c0d802007104c0d201c01882134105450950003481e0000c0c10550b242e8544007140300c50320b00c400158205110820140c1d40500c0100846403038000c0c10343c518603050343d41d80c0d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 577456879 1250 577455629 577455653
    0xd0509060a050c12060a0302190611070b070807060605060f0406020f010c0c260d0605010f030b090c09041401060c1b06020a0204050a020c010e0f0705012105040312050f040c080604 79
    0x1500c1c041c4c20001a116680c2e206041d0085401502d1728030b80350b0710b101c04810f03054101d010306c001045150030350380c1d440c0f1000a01300c1c04440481d400f81d420704100f41d459100560003180181c03070840d107801d03000c2425500c07a0000c181c85c1e000e4100e003036920303803600d480681840c0703001c0a4410b02e41d240401410034143c000c240b1080b0385600c840754040e4200340350004588900d840030032500c55440410004107000c10f0742d010f0001d4901c00d82340c2c001d402c01010006c03026103002c2c603012a0406d02d4200450558034000014024000000307101080c20b102d070390500009074000740d00c46030000c1c960326000000e0200808139024208805641ea80c0224200a03010759a5400c1d840c0c002c1c0555170751380c0041c1c0394034525030541e10340e802030500a020481c500344c0030981c0c404406000038101d0103151000a02e540c05415160035603c103800700f02c040060310b910741c1001010010b00607030500280407c0300104c0c01c0342d4170649106070485403900d00e950810382002c0c111719009410520b82c583c030000c180404198488050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 577458129 1250 577456879 577456897
    0x105030c09120a050d020706110a0c2102120d090e04050601032909070602010614150c0a080a090801110703020a0b04030e060c0318060a0c110409080d0509060a050c 72
    0xc080c082e480c0d00c03074502e031412440e00074049004102817002070507404215403040715010b6a594041d2181803005c291606804c020040940003c0381c802c0102d030416540d805440144184110300407080e94002c6512110000c0c41201c1c0c1d86c200380d090001042e080f102075000f0308800102c0c0c009504d06079842d2030b03030340f401800041e1540340ca00c030881c1820809040070200503080c441100c000d506005407190358803000b502421001d9403c02e50f0101d41c00d410f00c0c038040d505e440018440d0b40300340d001400a168a900c4242074030140d003d8045807202041d101d10003004080919035420b0000c0b4580700504e800c46030019282c0180700810800c1c9800300742d0018580940c25040825541c5588032403070180e034500d415129640d0004004121003000c0c15010010306490b0014101c0d5540d0b00c2c4210042040c0d9106a02048000c43c0600f0410408034072413139890b1449030340141002411500b25164682150408400084a203840f0070410900440502820341c001d44480405c0c032403800c05161100c0d0074001d100701c0b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 577459379 1250 577458129 577458139
    0x1e101505040e1005240d0c05030a0e010c0905010c02130608030307021207030c03110c0a0b1c06151103090d061a0114030105040b030a06020a02070501180303120209030a0215040906050105030c09 85
    0x81685c2d10300b00104440340080044030803c081007483d0405402a0030498841884d9481d000c203c030300014060003240c60181035a61781409580c00d000064910402d592000d07a0054401c3c440b41c09010510710499000c0c08103000107540341c2c9070840000b403400d00281c0d500300300c648051206400094000400c280d510b03516080c00074070701001c0c001e1185000d070b041c004a90701007024940000c1c1891040010914000c1d8140ca00c850601e0012488082d1582481880710407507142245d1081c00d40309010001121403180c09881c40c0c2600d2500051003071300384150a4580d00d950380511608084e182d081031000040c2070034030315040824029848858041441418000c545070700c68205659400e101c0d44010702c4c2e1105045494015900b0025030b946018058a40400c1045c1c0c9002c50580c0c110450b0402c42c2d915942c0c01d1010144016214040c2d041034080075094411501010700598034880540071100c0c002d4041ca860740e2618100000b0780c1ca00c0d911040c10300c20200140b18080e40c801c8200d030704110302552 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 577460629 1250 577459379 577459429
    0x100f150e0d05060f011403010b030a030809150403050d050721022d04030b28022a011401060c02030a06020c0c09010f080606091e101505040e1005 64
    0x45080307419002030003081c03070140300100701e0040703189580c542c16a5500500c0034008211b0f2418182214540d581c490341c1580301d40550000a40301d194007613440000c010680b800c2e0b0301031440d20719442c84251021030109101080b420101c904511600d9440401850036a406562007100310035440d00c0030782c0185005400081300050801c0d00000c02e404110700d001c44524001aa41f8451042d030054041224183d40e6800821201000b5011030341040d61040644144150340000c1440254000040e45220340c91030b0510030b11201c10b0b02028a16021403400115040c0e111661074108981c0507041003041c0101800d0302c00250314006810305410764800c074010307a113200e4141442c1c41e0502500240707a00c0140203002181d04004501d4800c1201c00c00320840d00b5a4942070100000740c902260001c0344041080b18a940615841500e039800c907004550303075408507840300d401400c903c20b0360340c068000c40c1d8001001c002414035080580e50090300c544e89498510b0a090002d01c44890754070403071070f502031000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 577461879 1250 577460629 577460657
    0xb0610090807080304090c080f01140d021f03050703060b0906130e011502071a0702061309290901030309061101060503010911010e180711100e06100f15 67
    0x180444000c1c0884004540001d6541c0ca440c42d620741c0036020b21200242803120f0f8a0348203015001482c02104050801c0d41107a080565142000c421410f642d40d03c440349a1019000d03031240d514920074051908040c404d1600824805811342d40064200d10405281040412152103004183c2da44078404031100740d03540307030301400e586060603041e0005082d0301248000052000036040314105042c0c526000d8996059451580b856541d480c1e400f10f915603d02080000018a0002d0041c4404516000110100e0362030f420000b045984090041c034800c503c4031031801400381c11142d001440301c8226520362440d0f0441c1e4000701801d00710b10841d0103011180d501350032801000c0d000b10014000c00344c002c1107e0340d054100003104049040005000c51a081c0a4500d41d040130b04c80341d184111003c0030480d45444949040350681c819880c4510b4070f029800c4e00fa0f0546015000303903100c0c2c2140b403005214500b40f40310903180105550f4083c40000401e00c00400400b08030801408135003205040010b01c030200d41d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 577463129 1250 577461879 577461887
    0x7090909110411070506090c010801030210052b060821131223030a0f05090a32060c0a110a031b0906080f07030204052d010e0a05040b0610 61
    0x10041907520070f0801c034101e0704020105003c0c00b10140920f044581d41e803500f0400701d072200711208525001420b80001840075040001030131620110718500b031172500c20140c041c2701451301d00f03000500260000412a5a59810601981c40509000740c080c0009580404203100c520344411032948020a01262103051900e80c4100c1c200107001e049012001c0718003034a811030080c00059280b40381e818081000f500b03040e03000020351314403081d103458030080c5840c0c203c000c0e80e5a410000e40c1c1c5074800d010400109030302880c84451106100284640013030306203002446210a9002840c503405160244100c04038400c00103215145544c0041c58001001c210b100030400000f2190030180c00000c0302001403400f94601940501228002c180401c1081d80302c6c01d2403a1a840208580f04a0313a1240c20284050701d850751015400a409940307441031118807035400c01c0082c640c06401e0b4000006000100100038041d08080d61000c00800100716030703d000e9907070561201c406000c0b280286c00020242180d40e0003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 577464379 1250 577463129 577463153
    0x7060207050f130504110616021003090210030f0f06080714030613060e01021e0307030617070603111603110105010605161e0506100807090203092509090f02090f07090909 75
    0x9047c0c1c1d55a00000c01c0404545a41c0b840200c3c003176a030100d17000301c4c0248640310b00c01c1c078a503004160407044030507031800318007610f108441039001641c0c900f10300204c1215845440300606400b000b070820a03150040c440000f41001140d9400398112008010003482900309103461654040000502034100c2d40303145009000b0007901444221526450401645c1c1c1c42000d54400c813060b0780c1c14845140c59805404203240c81d000c00403115840710f101440407078002c1c0c22800040b80000b214a040000d44c07008001c0c0007203041802c1c0c1c081410902d40d607010312820300071640503114604201e850400140415840c60b03500420142c030300c0500030402d200768101d0020102c503035a001400c4480c0360803c1c0c9565541b0194501c220091791044501c00034440320113009407807140c1040b9010b0120b0b049602200c1029502c080010081e014a8040100381c20700544100c03c922400b0310a901d10003c580e105203c0010400340100800103189002c000300590b01c008060f09a0301204008503c03480344d0706e0302c1020388075 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 577465629 1250 577464379 577464413
    0x1e0c0a171f0905061005031f18140709060605190e0a03150c030b03030405010e180702060a0e01140631051501091409180d0207060207050f130504 64
    0xc0750341600300c00311000381c10810103140a0803d03140c113500c03820f2881c10035607024410203400d50030020500300059681600112042e0412001103501070075202c07103411031240e800c42202d41a0440c020410945002c0045d1400f5001c0c01004014550070300c5400382c6030f4000c4102d0480b01c840754005071001d41d032107510007e49a030400382c01c041440391645010540c00c1a5003808111091600340d14100e02c0d8482d00801010b003001802452030103051800440d074945080c86c062350004d0803443c403403200c82e00c0e02545a1140c182d40c2d02605182c241140d0f1700c8203669080800c3d861980c1002607180195002030b0901d500100102c960300c101916000d80764038000000c901c0452941446015a81c10298682107140304000324090f41608101c5c400044d0b079203e0042c0138482582048001c0311001342801440070750000400242070030303144a42840c407440d1160081c518030042c0c02458041101d160100715040150004540c0000048880008500a4000c0c4052403244548030000303e02403242d0302c003185541031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 577466879 1250 577465629 577465663
    0xb010b1e0d090212010b0609040504030201020c0d1106151f1404120c0b120106230d090b01050102030406020d0c022106071e050f0721021e0c0a17 64
    0x4807207034140100a1500300380c168080c011000401005042c10b00c00c80b01c41c4c641c010035103800c080402081c8401030000400072800e40d0b42c01c0007812050882000303941108001c60303640da240407a80e00c0e120350402d54080c00c00012100010001d90069503030300c00c1441c01e40301920514114004411f8100c41001c000042540c0801c000140464400a0020840300c80b90180c1d40c0c81140079911017940785c1c184600310319090724812035001440680e02c40c941c07420103114004408100c000c1c0c1c508803140250b01c00984444d015030340b40700351801c104400b00e5403801840240040c50400b850890040e44130f4640da088401006040f071075442c2107555118800001030404403607100f4102c0c981c0080b07640d4038011765042001c15030300b210b203102e80018a02466201d000540c1d620b420210342c0214a102500700420840b88128807000280c840c443c405d580c0d1141005950080404149100440440e6010000300d039069410400c0c3c0c0b150350380c0b628000001140d85944075418101c25000f681c1e4102010045810382103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 577468129 1250 577466879 577466887
    0x40507021c021014012103051c0f0506040b0901170a05031b0613020607030c020d050d05090414060f01260a061a130e06060403080c0105070807020a0b010b1e 69
    0x74550015110180b240000d4041003609403400708400040303000d124841200d121420501c00c42d00d01454000001803203130908900b03001c4056401030400c0c059581e2754038019522800d0040803240c40c051550026411398080158581c014085203400c40b0502501b00f9403401c030321041e0401c2d001048164262a00113040d2503e645011a403600c080c03c00c00b600e1030003481a00f020030081102e40015003081030b170003800b16160224581d0259110a103894059a00c2071104401d032010903010702001c000e0540303664030b03955a0690541000119220042503100c01c485c0b480800040e13031244002201d21200034200302c180c2c803a40c0c20b801c149040108030b002e0f034107151590912140e0030050b0450b0082e100c04010f075a60701000311075510141d0084035498038019400760001c204d94090786601603000100031740350520f03058890f103070000554048802e890081e90341754204040960720402440d00102c1d0761002d0901c01031184c40e1240d0042c811701804006034400118039a41081640303100040c0e00001d080c0980f1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 577469379 1250 577468129 577468183
    0x10e120a200a06090b12060109120b100f050d0b0a150e010503060a020319110903010e1515010c110102010f0c0804021338063103080904050702 63
    0x72459040c0c0300907005100c0d0303101c0801c0250190a02c0010354542d48610ba00300841031000c41000c5502811890502c48480400300c3c0048000034801d00c01c60059020750711030308004d103894040508540c0518500044c111080c82241d462004039000c143d0030001c80801a1510f504850040c482602c2c69080c111040b800094540748076040d40d4102d8008a0070384038559140d121000591008a55590707140c3c819036100c4844c4d00c030310781c040486649802c0c00c082c240000c901c0800d0031692585c00c1e0000d04d91000b03044401513240d03440090352021110911804401d0805c0001e4403105480030700070400721000c260302c6900e0b4403d51200500d11034058040c05542031200001d010800f0542d81a801910740795280c2c0c0b0191410301482c2d02e110340c401d00c03125585902c600741c81c051038021100802401d0a03f07210b00420703aa01809003488031807560041c08011840e810990340c03c00101d903101d8802c09049001c1000c035107000199040c00c80280d40100c0d040c1e481ea94120b0500b242c100070720958540508007810 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 577470629 1250 577469379 577469423
    0x3120310052101050106050307091e090518070503012708120408040311011706010c05100203011e0f050f0108150d14010605040e07050103021b0d020309011b02010e120a 74
    0x42c00b0200e5000030001d0380d072a4207007110544800c50b00e8101180300d03603e0412110a96003c0c00c114901c00c1c0403024041500c496220040e0399003a070300d60202c60300e0781703888290388130082c0702000090000710000c000c1440c0d040200b600417109a1140d03814040102990303c24881f0700c0080b42d440c0721500c0c4210318645001d18000e00941c01038081903407a0100c420807030701d5650082681d041c8401901c0030782d0025684000c01142e00c0d80025404507500d018202d0070340c801c405140041e40c06081c08000805100c2d10580f01b0050010580c0d010b4001910b0000003009251184030094110000a107010010341d92004450000c04161004c1d19802000c42c0541106104450300345800d64854240240b06503a135400400c001d03030360a41025921500440420010b030f6000f90300506140c01c2610340c0c0030340a05098a868100306403285010003503080010041000e43c0e101112131074101c8a40910701c192040c41d0002400329100303140c01c500a002c51311803039003018070400c85180d0555204d20b010b0040c84e03c2c3c040040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 577471879 1250 577470629 577470679
    0x507050f0d0f0605061206041d03070b063c0a120f140c010509060903070f08030403062703030b0103020d020d0603060f060302100f0314010306021305010302090312031005 75
    0x42c1020701d418408685481c020080b036000c0d00c0d0016006686485d0201048000c061074261070b01010014644000b0f4150180003600742c15020710701d14005d034030742581880210014414410714150065801402c100001c200d20144245280c88511031110140c02040401065410130540801c80141041c20480080c0841da092403050340c06480404114404035034950311a50100d0103d4000e0000050900b400030180284c000010122120190740c0d001d000908a001d4006a0190300700040500c28001c250048030103010800042ca01d2004036100108100105d41c0001420180c85940e12500daa11036015181894003103c811540c8040400d401001090a4031081b91a582400a0302907003e0f410300c251812207801405d40d0600c01242ca00c2111031410114040c0141a43ca11111202c1440246a1400786204c0d11005907079660b96001290716014907400141010300400c800c80260710b000c1640d180c1d030824603960344d40fa030b2242c03100c10b0305058242d04540d400c443ca4500418500102d1440c5d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 577473129 1250 577471879 577471901
    0xc071709040b1905060d06090507080a11090a0501110a0b070c0525050607050102070b150f09150409030306090f15090b06120a0e06090303090c0f0307090507050f0d 72
    0x400400310b1000500c404000c0960414040740810b45080015040c440014010044160380004100340c44000d03850481d02e041d600303540040d282c14204401c0c10041c1c07194080b8000724504540c2410307800e100080c207030340b000c1c060345040096129041030300c3c800030007c07001c556030310081c1c80c200e0380ba00031401080040c41c198203880d13a104500f00103803041c0420129803020780000740d409c18200d05040030300805074000541104c4030343d8208480d901242c0b9082440b405564005521280710a805040061407604c0588651140034010140154490800c0030744010010944000c84c0310b06290605800420460340402c681e24200303131140501e04025032020050b44c8011900c0744400307498105500071200c0400030150170a10803c0702a0240c1c014540300c0341e000c82e540310040b50b0314441403544e13400e0a50540307082d00306910200903c041c1036001e0146141c081015a40e429000c41440006503507940284183c0280d140c0d40e0000c11031003403107031080ba240300e00095049640c0b100002d080d0303801840c1622003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 577474379 1250 577473129 577473131
    0x20705010b130c020d14030a020322060603060f020a0e090702240106091e09020d020f160c050d020d0602160203071509050f011d010318050a05010e030f0301030b0c07170904 76
    0x2031701e03186801101c524120111480305181513039540d00c417000080d8005440b0344880d50902d03011602c09140d910460054622501c00400d0b114910710340917003501d4a41d101442c1240c010b0005040c840e5005503440c81c88401255024425118000140d041c02c40742c0100c82c010710200c0c28209031203811600c0b0b00381210700a688400100d642c889007014000221034044420f074103120010031080043e074000d0b02100c14031503030052400e00c545456142c1c40d03000111946424408402400074007080b200400010a000d40ba0031008078016400103205145d13003007000b040283d003c540103c1c01c0e0390480b80300070a558042d08440c1c00a07124510001c402604000c201c0016400c4480400c00c2d04091010f4040e20780c041e182c074880201c00c114110a01411078101504069460407410200b2600c6a500d2105138003480140c81c141c211400e201c3e007501c0030a803040c5280e60081002200c007007080001c0724112a00301c22520340c180c40e01e0711580b1043c492140040c0c0140d00b0300c05003100c142c4110300240f00c84481258 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 577475629 1250 577474379 577474393
    0x907201207050d030603020928061712040503070618050603010803120105010c12120f0f0903170720011e1d07062705030a03020c0a0f051003020705010b130c02 70
    0x1008401751002400025048000f0001007030140e012480561600c0a40c00c0c030720024119804858011591150300c110030724004114411403041c010301040001e2030380b0210881c60f050501c00860358840c102c0c45484100901a010b40c980f40303030308580c80c0010b0240245415500d59440000a41d2078228800d5200e58a0300500006025030040e8281030000354080098a0700e4180c601068800040220035886103580300c1403014604880da04c100c41503912114000100402c8504000341040d00000c03034104d1002048043c400340a400803483c10f074519500144c484c42d0041d00c44100d01402f00e0000e1081110981c8075080e642c1422034026035285910307801440301c203400400150f603942100784104000b044000652003104034181c45092044141201c0c0c09030150b948902192408460910a80040e0402d08280300903141c01e004e50340c0140049108108024101400200042d200301c0640c030034140d001811204001003900a9015101c1c01815030032288124030388000a40500458a401401060 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 577476879 1250 577475629 577475653
    0x10f0b0f0903150601111b040504080903010903110f060f2a2b020a0804020f01020f0604061523040c03090b040f0507050d0f0b070e270a0b090720120705 67
    0x20300d001c0c0c1f85080a583c80e0140c0b280b00103004c0205005001078426100822128581307403804d00401d950320380310342d90301e0328140d604612040c108183c1c680706070b0650b0805001c3c0181900d000654a070044c181c0f0501844051440d640c075015102a40900d400e8000b01080900407160360340b1884181042824030400010407070f1124208070310510040a02080c20304020a025007010079000384031005c18011580e066100c0301710140361100884003102c103162146c41015629526111000051803003164000040584170340340756070100c4235908280030302d0b65100d0149045100b030308500c2c05560041d040e2040c41c03e15040c088150740b100030341940c90b80300d04075001607613042610041e040250000081c440506899642c25440d40c070180620f000c00c42d40503a402c8613940d80124034000c540e221088490341c079405840b6905070340401081b1903100380c5050141501034541000c065402031345458aa91076040054044003102d5084011091500c03c00d01001b009500e200c008140903030151084035440103140d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 577478129 1250 577476879 577476883
    0x9070e0a09110d020306070e0402090406080102071401050121030504120311010c05030606040e0c0c0111030405070522020904060f0902040303080f090d0c030c0206030f0402090f010f0b0f090315060111 88
    0x61240217425501072000500810301c681c0400c41030540041c0094602081000003e00f0748240303406c882800c3e50f0000c2c00d1010000340c41c070314409100d800030007807017158540004451440c00419400700b1a403805c2c1910350406100303c088601a142d10b01500c82da841c2c00c1d080003080e5442c3d0742c007030300b18030740c80c00038400103c2e0b0080059038442c50300146041c3c034003401d01c0188100020b0142040202e0340c41441005140300007801514822a80503850700d88910345410018030305283da60069000c2c0150350601102d03411549a0700060f080342c01405659492007402080050030305921000c402e484074940403480c0300c2150014000c40303000e40d80d6038600b9160410482c0c0071243c1643d000b0143d80c026943d20040d540500e600c40c040034081d00301110400d100c0c0d00440e42e01c1d80200c44140901071a0003c0004503d0304020042d040080e03070150301c42640c10145007000302c150398020030003907038404034007500c40003480400c03142d030060090207503003250b080c3c24408031002c4402d0700d40c01e01142c11014030112113a00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 577479379 1250 577478129 577478149
    0x803180105160c0611042c0402062a10050108010f0509070e100b03010e0708150f1e0406080607091a0f0706020f030f090f07050108040b09070e0a0911 66
    0x890000b051200d211a0079034402550000c1194029102c140e00d5039030300d0a10001c0c1c070091001d10000480050302034042c2100c8000a90a40d0302580030006010158031500d007a1075021108410114000442c1c0310000300382000800c2d14a21481036407004002c1b498603070001c60403920b00c0e030300038001b58041c0b015180c1603c0c0704549009140d84201c108024404c000c6030090b800034080c403260000b880d1a0b48003a0b00e2940709802c6919061100d2091250050b4401e0201e5404010302a18104912410000440b41c901407e40140b0031113106040d14582c0b034040e00021003800c0c0040080182a40d02c04006480c2c26048400e0008079100d218005407001941104030340c4d0300100049285840c02e100d00e1380c08250485402a10f0150f4203105440105820000035070144c030300c50040403901e152480603a46040c3d28112040403680118100300001d9803c030284607080f81c3c0c001d0006580d9070703400040070702d00b1089510585285c01200140040068079902081c142406440050030091032001070041c1244 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 577480629 1250 577479379 577479391
    0x6091b060e041a030d020304063911180f06060705030403031815020a0b0a022a01020d02070c0608070c150504150507030f050a06030804060c0318030803180105 70
    0x114524007800145080d070b20400d003648030114642045040680403038500019a90440050780c0f0020302880300e1600901c10320f108200d80d807460b4600e99a0500e81c03480500b5581030300c240282d071420451041024900c1c0b6a40c03840d1007d000d00d803040c1062072460140e04415030f05030314a82000d0b4040b40c0e85080c141c048450081d080340055141518580d01100d008190b1500c1c014100c0c410000481c110411050b4002e004a250b40100718039032003803c0000c24200054080310396581304100e8403051103454180608d208038051a11031003900c1103154940644a42a03e2106c2a8800102c0c18104a040f00012042e01c01c0d0350780340c0c60755945024064628095080016001d43d01e142d101602c411510b8118607801881031b00c45008061080b001d0509882d0706481e80008252102d45034920001e00744074039640014200c4080c40024990380318807000e07202c1e41c0500800c1001d4500341382c0601d8000d000c0e60030180c44184041301e01e5a0b40b410050700c20340007543e0b62110207a848401d004030850500a00740994 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 577481879 1250 577480629 577480637
    0xe0c0405180a0608030d14060406050f01050703120501080109120201290d0b090c030f0a08040302090705130e01030605070302070203120c01110415020c030a030906050d0e010906091b06 81
    0x1c00859125409403002001a00d0341a2103400c0824070407010f101a000c10004c4940204a04040040d2151407001c000d01986c0150b1410204004aa60b119010300d150398081c02c1280c4d5034601800c0c100d03000204086002059820f1100001380c04030305511669145016801040c02495180c400303c0c282c03540d40c81c0e80c1040d000c1008031600c440c2c0c00c10a00f4610350b00e00405550110b101a501e0fa8042c4400300c0d408441ca400500c40b0110f10f0800780001301c85083e004010300142200ca41d100c1c0203501440c0406405001000c00042c140c40c0283c088588108031203005140059807003540c8428801c00f4003045800c14106004034040328000d00943d107036903a004016001081c284106002c590308040c0c1255025034131010841d5445da0414001c0003d80526041c075114051035002c0a441c1010f80c500c018001e61000410b000400c0d80a48500d064494903e0007030307926090b0340c1000380542000034800c3e0b400e528110001040040700d03400128480d110b070079541c000000c000c41c210002811441b50300085 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 577483129 1250 577481879 577481899
    0x115081506090c0720100e150a08040b060a0b0708090102190b0f0408090d030309050d1403130c031205090f091302040203060402130b0d11040b0904090303090209100e0c0405 76
    0x5034220045640c8070782c803d02c2c0502440602400030302c1c4203180d506c003c0c011500030340300a40076003044848051003a030010707a040c0c40c008202c1002413031000d0091019261003130700380101f03110f9568000f80c00010164180c455480764964100800303260700c00801107002d0f100e41000f200ba852296072500b4081e43e0403185034801540c9009525114007402041180e0650b030410000c446a40d410000c1514540a66400641c400f414980b2518000710314040f441802990403440381c49140d0081100d030300ad00d400600314084000340c81c020040641d07541001b003501003d03140c1d01a0b00d582c010b01620080d0301c2211920300900c440b00520801890644a4032038503e030407001c032405414039800039604294081d0005240480711003c5108002c1310342c11101c80c1880000c1e02a441d00000c0c000d0900510400a01d0340c43d01e4500560b500052256200c140d01640c0c5580c0000241402503020b02a9603030003910035443c0d460050941c80c074030b1006004680d10004c0c02c1000c07031044600f80303043e60b0503500003408181c28 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 577484379 1250 577483129 577483133
    0x60207061209030c060e011e14070f05130b09090a090803060418200306150a0e0a0f0c050904060602071511071a09130c120c020115081506090c07 64
    0x1d411542d00650a12400f1442a40010380c0c600c035a0000308254000020111441c0ba44030b991007000b025000b40e040d040c1070400001071084001d840e00b0507071034100310481501006003070301d017800380043ca8140c9603403240300012003803103e400510501d03000701c40326900c954030662104121074011202402a00080c400540d05003003a0380035900448145844211182d1f2a603990f05d0125850203008400718011440011503060400800c0e401c060a0006400400050004a5240c1341944505c0d40342c4210031000c110f0300e04a50f0b00c0721140f814950710900241d0b1403c44080c141d50300007880c0d5409280380103000100d03d4800315801056950729124003401d004c0d480c80440d4246041410840030340544080064100545001e2214229000691036181c80c407400410420040e804101082103007001e048142c5503500542d00d88509a115000044403030721608100e00400203403090040800610b41d01003544071001440d040105a5002400d41036a1410244500a2000d6407403245000d428048100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 577485629 1250 577484379 577484381
    0x90c0c0f0a152301090b0a033c120804150c0e090108070e01050d031106071d0907021e01150f23010503070c110603130c060228140a1b0602070612 64
    0x241008001c003c14883e0b03840361a0000c0f40c1c0e00c4441c12400c86203602d00c081c2e0303027000c04181d1250f41e1100ca40c10000d900446845080b140200401040100000400004d041280c40b0080f43c1244407001030800508204040142030500c6508040b48500001800001c08860000300a4240c505072104051300764a01000e0150103c1985011014800f507600c9203803005c13008100e0f80388142c60942d19030000c03c5485400c18404103005e09030601420441d41000020398001036000a00301510803840e07000b404071b07040d150040060495074542c1c0d4911000009070580740380a803509950609201c407c0c401d0b00755901101c011203e140380c0e40458402d000250840340240a521403d602800d08010003100c2200054035940c070403250004620b100302a05414403c640c440000a0300c2135000030480c0c240307020348100e5100e045800e0307048d074800200c801004000d180c0c201c2c003002c1708041e0204c44881ca46440c001c8602c446140000303040c88008a0001401840040d8000899032941c503a0000b86080045404c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 577486879 1250 577485629 577485641
    0xf0506010824120a0602070c0e0c040302010915090305060106200303060a0506130f0627060e0f0a09110a020f070e0106140c0d0f0e0d02090c0c0f0a15230109 69
    0x1084c020080c20a01040040c0014035049101d503040914a07400c1911641d030920021709480a154418082440181d801803068815980c080d00801250580314034112002c048a80000701a0b0280708000078031590804144401c40740d0807021810303820340242541f6034030b00084440c107610850314042044541002c400908244141242159606465640b1502d54803c1c9603c64000120130750a803c00c4111203850314a0317440000180103012504d00b80307004040300c060441c07072072080541420880b001e5598400040c01080c41d42000c0c4400c0840c070041124030b0f040b142441e0090300980a507550554130215444054808400d610b00355039003003031011582c940007134140302d010120070840410805802c11072558408200e03541d0700902d07400008010000781d40580c00c540900d25281d00303140140d464100141d84160380e0041207072121050240d96140c50501c442c91129170141c250380c0004e001c00404100c546100c1c0c0300090000445100c610024810825081c1801c040c00100500c020b11240d0080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 577488129 1250 577486879 577486909
    0x100302040e030c010221011728060e010b090f1306020a0323040303061502030d090c0302130e06060a0b090d0203120412060c0309020307090b01030f0f0506010824 71
    0x140e041880c03c414180c01c81c1d119811007060703415140002d615009941950502404088003030040c0c0c03e880118850b540d0420181d050104909490201c440a000f1054000001d0f0410010320044038a40030080c004e0160f043d00034014002c0e18001041c0801d00071419000f0b089601070104886441d4950740700135080580803030304043c0c95003000c05110041090b9200710030b8501600840f14102840d01a08540280e400003100b80104201c1001041d0040240c030300850000c0800708505541d40340110180e030031030b00300962102c41459014900b030398a5100041070300054007110700680700d4504102c880c680500c2400c0540808101d4001142004030b04268100d2002d0200d40010104458004054000d03400120b00c4402914280d002e019090140da05d60341d0040c18100104240341d004640c5074100c44c024011120707103409203d50640d1091780015200558441c0c20021000d10742900d501408040d516140008c02000c0803035020041640c1509551030034046409041c030940c000e08c50103160755a04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 577489379 1250 577488129 577488133
    0x1051e030a1104090f080306130615140403050706120f0908041806080d020d0201140405070b03090f060406020c06330a03020607050606010207061e200a03050301050f09100302040e 79
    0x13680b0006114003000c900d21034400d41079951070345419001e102940403100381e070b500104e041c0201041800c2c15800c446522a00d985002100d107900c1c41d05d24941b40c41070303500c001d000d44203004000401d00d60211b0400d0b12540f52003c140103907200810380c034013aa02e46800c090044042040308210b100000c40c0094188101d1a40100d480d035910082175003400c1500c5e12942c09a00003441301c0c10115428419000d009030001184206810681c03283c6507102c0203405924815040080400d20388402040046000c810310012118103251629141020790004e2540b44214420f10011174500341d14950300000f10f6460300025911421502000e194400b0005046078204000d4840800961141401482854010310052002d410018002854045242d001c0300410041c0460088541640e0004200c600c410f03180c1146003800302825036080c80312556036464207100700030b00c5508040c1c00070040d60481d83c0403120040184403000c01d000700060119569404104042400c2c001403a040c1e000c1e048014110003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 577490629 1250 577489379 577489391
    0x601170106080c100c050a20032d030409060b1e09010230040b04080f0304060509010c021f18080102071113140901050603010606110c01031a0402040e01051e030a1104 73
    0xb101d508203490300005541e01a0b9244020488c68202c50582100b090145e000f0a21880705190700746c8900010707200b84c080032480c103802203c00380b0300f003050700c01800c5d620134108191941c4101c10718059000344851034000d2680d04040a80100c818142c0b00c00300c006030003a00c0b1840c2040340110440c11240c0c4000c1b035540040b000c5160503013a1002400c054640008565034403820402d1062601c0d41d0f00c0311248003903000b000305010b01b65101c0251882060f081c20501c003035800718800070340c005410882641400845c04c0c0461503080c2e00160000807401e50842c500d41198949440ca802d07845641809802e04070f801703100001c4c500702112401d0700111a08000281c0700e4070440449150003040d5070620081c0c0d103c0c1c041c01404d140c01e20030600145100e0420001022005944079191070503540c0c402e05165940c20303c107040c0500068810280440100704654a584801803440c50140070300966001e02c0c42c890440300e00c4544103440c441c250400400034000e90249644807a00da1a581003115000340e1944 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 577491879 1250 577490629 577490633
    0xd050106091a0a092922050a062103051b01020304080d052208090a0512010c020c030d1e0e0a0f03060c1409130b060c0601170106080c100c 61
    0x11160b0640100e8100340d62030844981c80c100141c03c411600a205118a000394450b01c0400580d5008031110a2140304070110108200150300b1029940482d4420001c80e200740341d01d800240e000c00d214900c0307840b003007045645170b200307040350710340340044a052100884955001083c0603030041c008540e600f217858680c03642002c006a00b0780c0c00981e0202c4084802040c8203103c0d000a00451f80c1c48041030300000048583c1c0d01904440b00492440a080c03000001f83c8010281c81c0c064111016000281020520580c411050780c020041d0030703100c00060245400e200000d150200b14044120707001d03920b060f01100c01000c10b80b001c0030041c0c1031100740254042c142c0c0b22034949041410003818000031410a907880d5041540c151150704140504100d04920808072035405a0305031001c58100740d4030580f00080d4a03071709000402045010039408200455020072040340012080c0c1a100384800d00150141d50840050a03510ba81c015209175400c102003002d0701d810030b80380411522010340340000b07100d041c0d9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 577493129 1250 577491879 577491881
    0x50111011d030c0d050306010f03020904150f090b0f031e070806090105011401110d030b0103060302210706050c03091e061801081f09050a09230c0607020d020d05010609 74
    0x4032030380c100d01d90000b10300107202070824801d1601c90109410001d142d480e05400003040c55040b6507000d0280350307011030768881c20303261035202c0010305001088840b0030681f10942e074507004000d481207aa1090038030008011900309424a04408000940242203c14007a00b04004204055028038964030903000001108501000b9090181403ea00006465410441c8081050f030f01d5011107818080300140107000d40302c0000301000041a50b04c2c00180d0164800d004074060030244e40060742c03200d07000e000300c40340c580034600c0400803035503400c111a405940c2e06000d0701d91b80149203012002d46c1080c02044101d0400c0e00250b0612500601c40c13810003a03840001661a8011114060b5240380503c0c4a08036940c2040c800380c0c0180c0659500d5501c95110a15205000d1043c0140c1414507140c502080310f07108207800c22031449034440c4050081c4012421080151b10041190041d0751081444451103030400070f0890300d038150007412502400d15586c080c41500f40702c081d412201036680d01c00c005120106 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 577494379 1250 577493129 577493171
    0x150304030503040318030302030d0e070f0b180405010315051b1210050f06071b03020a0b0a2a02010c170316090e1e070302042103110a050705011101 65
    0x469100c1c1601c83c145410024400300100324001c00c43c40064500748080f0350000300342d960040c54001d01244901c55461040c0c2400565400b0308000704c00814040b4041146034003414403081d055250080040d9000c082100360340003840040c0c10380c4e500c0b18900582c1c0c5075907000b803503200445000038420105c17800040310b03c1d80d00800b04802e01411842c107100c10711805d00c03030341c03402090211003494240103c84000303480e034407643c50700400300030216088a144901511501000315001000c160031540d890001542a034030010700f0400092958004100c103080d002d212440e0300204909902070315005900544013080800002d440587c079035411100c810304e040c40110300c542c1d100e80d1144549215203402410001c0d00d9000701d04241d549004014800444d090561864040078444107042d4840e0f00080d4001e00c00c07030300140c1c000715a07260ba00c007080c50040c4200140c0d6100c1d9440c0c0086581b000c003070301d89880407800d0040558203c44001c22566105241e440380034805040001602109001c0d00010460 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 577495629 1250 577494379 577494383
    0x231c0602070b07031e200a020a02090406050f130f0f03020312090313080a020306040b06060c0601030503040e151f050f18040b01021605211b1f080103020906150304 72
    0x1744442141001c1d400600f20325140c0200e0310010300c0a448200706450080c40c042e102c00c141054081881d503007a0384200324078041b50303030050958030302402c141c180700e0040c3c081210b88188113290f03600407807411400c108074002800d4104001076036030012a0f80d506160304c68507500b502103100038001c15182405201c01c041c0204c401c24010f40c2e880c10954001e1408504991045a468005019680140c0c5001c500c45501980c04291030400b85d03141030001c0c1c1d550040d140c56060500c9054004810400b00000400036191140d0401e5010754075207200240c404003907001150015114402c0752600c0100e1051500103422501b80681815800754406000c1c1d00252402c08524600f500014240d0809128034152414203202a15108003084602d040b41500c1e44075090081b81010100c0e074900107441c07001201c90030030340e050f94841c80d4010341c40c41d81c58504108a512a1034603403128401540c101003a190071096075122a03d50741c0c44c5800704801840c00400044d0491607220b04601ca03150083c00030742c4194 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 577496879 1250 577495629 577495631
    0xb04020c0d1202131206060b0309030a080f060102030d0c0909090b0411040b090103121403090a0b0a020c101515080a0510050d080304060e0115231c0602070b0703 71
    0x641e0058010122008074590a010781c2c03040125040180d2508864402c3d00c803080940c040800c038034a403640007000076901c01d44060302d010050101a0b440800100200541d584d1745403200d0b240c1c40c2d840d81c8101820b441c11030151740200074285400071325400c116580c00c0c80e0700341612010340e82c403404000d91351001001c4844107003c00801003000059401680100e2094404200000403900032803402d50060001925072540c8031402141c1501c500102502400b04010060b2a410700c8074819903501701c0b0a00846901006070000394410329980b00369010829400d00400780300d021610b8240003840c80c0e040301ca0340040d0b5080c02084d140d5240710030343c0b5150b1144c0d413040824681507440b00c0c2100c0002d04943c2071078000000c204425a100250031070b16a802482103550707501c4030300c0d12000030400c1155400d0f03c4c0d401c008280310700c114442210341c201d4102000c22290003121010510079440b14650341c0360b10420f0300540400c042d5006911740c11051047d5001440c0810944030300941d008100d60700b00c00a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 577498129 1250 577496879 577496893
    0xe06010e180a0f05090102030402010c0308040501091506331b0f0503040503074a070914090f0c0304080417010510080d020a020118320d0f02130b04020c 67
    0x700b403e5204269019901400031410740c2001c0d80000c001d12050b41c00602000b500d84003082c00d2110039400380c1c0700103512280201002140c814030102400341e9202d407034003c00c0205901010f40311101c0310140d0070a06405604005140d182040e6a08200038140704005007a000083e0000740c030304120403c3c031074002d6006546513844c0600305450b01c9815048641d06008940c00154415a01d0030001c00b007265400c1001e050350165030080654200e88194004900068000c0c030161741d4000d01c01c002030304d041600f641440105403041c08040402a542e840341d131030b00107001901d03141c1444061074000f031040240a190990390301e45404074000510200c07500c1e955510038171400300ca00c40036680c001c2c800400a0000c15480f800c0c0a5294818040041d0610a450502102030992480312001400c0e80e1460300f8603011019092002000580700060040c0c805130442030a00c2ca04071060a14250b07000310444000c003440e9080c04844c59884140c400340584131032101210350303030b180094003140d07941800904c04 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 577499379 1250 577498129 577498151
    0x312040509010f060203030a1a030d09050102010f02090915040902030a1202101a0d1b1235091c0311160605071e06060b030910060e06010e180a 63
    0x40641c1039100440200029030100449500801643d03805030303000c9000201301d100c06008103801c09146001c0340d8140111035590290540200d2050155082a030081210f9542012182c1c220311590140d5644451403200080c910400604c1c404214507010b000862031418036030100b4a0040320790170465500c0911040d41105590400c61035a188240940c1405002e0b4030040381c0355880c22005400b4005c0e03220f120b04800f03000310101e0001000e4004031a4803880355448200c04d00c10414410100d8004014034200c50800c116004c44600a001c0c0010314600b02c209465489007960101c0011501703da4094411170b60f0300a64180003c00354005d840302c4039119540d0190a0829101c039003160800c04000710107201a40e40038041e5403075103034019800040004240d825400303100c8218002040d0900380200401d590f086040514001c2c61340c074040703941c0c00424907681402e0340c00354015442c144a40b9000100150300c541c484007900c04024013070200d11309603001400040c1c6000c660b041100d40d114000000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 577500629 1250 577499379 577499389
    0x618040f051306051e010320032505040b01021903030b03010c050409150602120904140108070f06022808071505090f0a05210c10090c0603020702280503120405 70
    0x1a2010030580158851790021417010b800303e4060101611403a0f103191004005024441e0728003032800c008040702c800e4040c0015841031440000080342d03881000382c400003182d003000e0180d4140058140c02502e100d1151018820710311851420907410180c59a0445441e51805e1245424421203030f0395440d552403c0c03659907000d681c2030180414045044a00400042e6030100b20107052250071032007183e032501c5100c000b40161013400310700e001980703024000040c50940042c6c030b441122a0221001441076131110240c1e11034031a100b100410060340426001000c02210411a1092192541c2418051b50341c0303034141d140196090009840f03664100b03000c810107081128984441c03000c4010540e440c45e1b40e07200c0e9124040c2402540b50700c807003917498501c01402c100030345000aa4850807614840c40003948000603101c1c02d081603511a41c040c4000c01e03018400e008031140c094020f00305540c80e03c54140f1110300e1002c4040300e0024088041e00216507070f81e06100f40d000544822200545860400007046 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 577501879 1250 577500629 577500631
    0x50106080606031b161505010302030c031f05040c240801170309041130010f140f04110a050c0c0906030d0302030a060e1806070302090618040f05130605 67
    0x500c240010703c10096102d0107003d0316841c02c40c142a000d610380c03d081070803803410200306074010f0440003108a0606003a00e55804641200e0003102110400b16040081c03546130220a01d00501d00c0909901c00124445039801682d0040e100c1d00c00141c916944518850b121005039540c00d0903d0300c2c3c14280700d44658019102409040502200c0b8009244282c045549109110005019546030122125160308600503a030707082c544801003e405106038002803c00700c405040364111b0342d40010000c82d03041107420f035800646002c00d010354205456041041810050055900e601c60384a0000186c22a2103c0180a5513130594550381e48841c400c11080b82460740c4215914080c8020705e08008860b13500185007540071a01c1c2c100180e40c3e445842c4074102400058000c05034a4100000340440d2845c0a030442c0e02024050003540c895071104a412030585c40f030788001c15031040c07007030041c042c0030300f0640c1030320843d59401480001c01c0034000b6885416138804450810b0387c50701050a04003413200d070380a22 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 577503129 1250 577501879 577501891
    0xd051e0c0d0905341a04060e040906020a050c0f1501030f052d07080d1b0804080105040b040b13030915030209090a0914030304020a0902070203150c1e03040f062a0305010608 76
    0x1c00040c5c0c14801020300d82c1c0100c0c03003548100060515444411303221030780f002c841c45401940c1556503c81401d009880e42c3c0c08441c4003801e5120303a8078400301c03010000c41e10108003100b1022155484c0d00c1c1d5140e000c0e81c0b07000d08005680c0360140042100017601c0d0407003400740070000c03501d600c0e1444d1004507044d8100002644804110781104001da82c200b039004580015250803000b400202040324107000081d40156005180158a44001e200c1444908840903219921a9908000c035540c0c00302e810042c24900c04000303003c82c015060520544000c07da030088400414a40181410100400075011a0082e50a45001035480030503e080c468000e4842c01351603a600000c0d850350801c0d0340840e080b620350b0320a850009034040f550004658081c02a46104c44840b1241c10050074850343d4001d80d42d0280e1030001d03000340415162a20740b00707498140c0303102e90340101e80d082e50517120741c40f80c8004d0410b0140201107c0360241c031001c00b0310712000c5442049206036030001100e41c1001d0000d001c0c0722028100c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 577504379 1250 577503129 577503149
    0x10906090e060616080f070209061002071404201b0318061c09031107080106050d060207030e03030f0d0609020301150e030709020d051e0c0d090534 65
    0x1403100c0781412070595002402507030620f950b00001d5840c54080d13144060010003404000071410b82c1c038808000501241e82c001c0715110890385a00d410088541200c0d02c00101582150038204404003010b044080c003c1d07809807001c208480384003940d180641620102d000f03021404606040100407115031040c070100b08200641c81c002d40090021944c1510040c038900c150400243e8010000d00e51252800c0e040c404e071000e000001440c5409458a004840701ca1158818240001101501401020109c42018007480d41005543d00c80b40041c2d40207000036828020481d41603512510100f0003803401c00008545682c81e07480310007142080d525158009040107005100508c020300d02002c0204034861a8101070803000b17103d00110f800d110b525800021440d02c041020100e418103500716030310a080b862a01d060411440b401d140030b01a06450041000d02e041c8401e60510890b40d104440d01030046040710928000400080d840856114068070b03030f80c0d01011504103560f9000d40020261140c42c40c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 577505629 1250 577504379 577504397
    0xc03010317070602040b3c0a18051c06150605120405010623030606030d0c02101202070f0b06011403070531030c0b1c0e01150e0105010906 61
    0x16070106100c0c1141c041d003810500092000204500c0e50304450080c0f0b50100c074a42c960000680e6100320380703a117100b5031041c10814241d040d0120804030980900041c071000d51800e125503c0006c981404c0a2a030120100c41041b902080980d200038284402c25420810911291010b140c440709071741110480c5440d280c01000140540b9410030140c03002038011400143c15a601c50401c41d02500c419446114150030460106481c20480303010074040490a404603103085d01c1d4603051542d10400c80c241800083c0c26503000c3d000500d019802820110124584202031407403032910038080303a01c0040116a1035101d00c0c124004c01c43c50500103944550b0034200840c101d0024407404a091000610301e0040013400210500e880c0c09450080e040401800041c01c64122800369202c0002420300056540c2c90b607001c00022001120390841e1a01c0e1010030040e400c8084104141000d055104100e0919548815403c0c00c078100115210009040c0148089855458500054405540d0703811040c00c01000507 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 577506879 1250 577505629 577505633
    0x80a080a03090510110301051e030706051308060c09040f0221070315090c020609030a020d03020904021216140703020a02280b0301230d0209150a030311060c030103 72
    0x401518650401400c000c030b071450292030000d040004241040388200d140c445601101700301400658180c45083e21310540320b0b180c0b4078007180d600d85d4040b2815456030044005000c0580300301d0181c02202d03c07071800c0410441e181c500f42c5080c2581242e403001415408160011a464107004060110030309200840c82c000e20390708203203e5101009010005211103102140d042c82c8240d01441020201000003d02c09485003080409002100c014034014400c800214040e2000441101c0d11049030f500100240301c5d240313500350040d40004141d15030082d428416400d500720000b0045225a0481107000390804020002604408a00744a052110002d10081001039000a04041071503011146c0744440900460350001c00340d081d59400c41d248a08000010341800c60b200a1130503280e16803030003c20081a10b044d4000e04c144c001c03140f5400304040003c0c4016003014112545c11a6547c001d65540f5160300010440342c54090340102d0010385605031007071820b070080c00016040b1540814140c5194515 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 577508129 1250 577506879 577506893
    0x9081b041407050d0b060c030403050c03010c020705093909040c0f210207080715061202100513051f0305010b09030303240a0f050f03010c020304091a190f080a 70
    0x4030014804c4e645c0d14031642849581700e4098074200035030321044a540301d40328036007180c80f6150f9004142c020b60170100f504c000c0034008245101640d40c083c051400790382d510030070003801c50604c01c248050242c0744040c8503400511401e5182c00141642c800c0e87d51001c00745c0501c030880307017020400c074200010700d82a48403099020840421894010700c50500c00c00041c40000001e21440400508519000410008100c688128540441184007003001a0748c0d44007201d144150421100070b41c002400c6c0c45940c0d403980610040c00c04a045003504401d110340f01c001003a020019a880c46e000103085032040a0883d925000c1c040c0507095080401c1c1c10b14900802096903800003802a0070300180303c0365180070020005800f034600140081c0b4162110340e035000541110120f6015581c040c0702e980141c00c02c00d0074140281c01740e00740107a00452516282c01c200d0001044141a2005800007600f0340340e001e96034025014058104c04485200440c1c40d012204407150f50130740c03043e1b08a8011501040220b500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 577509379 1250 577508129 577508137
    0x5030c010c1514180609061302011b0f17030c030c0c010b0a090e0705010c051507120f090618020a060305100909140d020a05030306060901030609090b1807050a1509081b04140705 78
    0x108d0610304450901c1c600c01030310750810011000400c1907041d00304100384078400101145441c09811001915002c415000c030f0503103c2107601c03031807116040000c52002c0c40b080e0020103160245c18000140d013035140e400a5004a01c03030f4085101280c80786e5221000f42401c0c0700180003410242400c1c0c1c01c0c0002c9956240e240c501403d6a20b0130642c04d8000580c2950081641d43d11550208000300041c252418003c0020020803606071225443c20403009040b941004481c880c10b40c0007001000100c3c5000c904400ae408001e00741140100b0b0b0810019030320b21240160354520340b1400e50701d410504520540744c98566594092003c40d44211800c6001c00e1003c0308880d009201502c41c0307503841d01408016405008280d02c0383e441549090080300c184100c424a690003044800081c071321455a07034074034036a182518040e81e50f01c240812410860000c1c0c00302082a03030700301414401ca80a64a5030100d0078042c008000056501c198000f000c07407407416200d51045100304040220007401c2110b0000c1041c02 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 577510629 1250 577509379 577509391
    0x201060f12050138040c05090409080d0e01020910020c1806030304031202010e01060902090315041a010e15040c05040b0c07080601060e0a0f05030c010c151418060906 73
    0x58001d4500140701081d04101c005080140e031441400303107000410218a041001507646540038020302600924180c06441c500c06460b9441909000700a03080000500500004542d0b94104102c421020f0700d42d400351a0413078207000001a2909802c10a12055110541101085402007501ca10141c0c2e02d400900c12032040244911031550703a03140101c2c1c0340d441183c00144c0308421007454000003550540000100805141c02071000994a00c50700080e8062600a42c0d07140d00001c4600d052141140e01c0a54482e0250f503401140d9408811850561002a0404441090420104281e00c09807401868044030242e404104035200c41c54010401e0007107006201c41c0b16400100784020003401c00a10000e0b00c180781c1074483c1960f41d080c000c0e0402c42c450001c24060202d00f0000076129040b00035070b40071120040c000c1c0520000c40001122a0085848215030340e8982c89810707000d40600d48503004040e00e0f12850b0582c05d00702102c4440780c1c0c07030214400d241c0a901040400610702c4020403c035401c54 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 577511879 1250 577510629 577510649
    0x209160201090c0e01140109030330090804150806091611060c0c0f0304031115040b04080703020112020a090b0313061e0e070608040f0c090f05040b0105010201060f 72
    0x15064101240506100a400b804049082c00c0100300081c2c0404880e0403204007451907100000e80100541d1000d019210203000300d02ca080305029031904000b0781132401e01e0640d2024071080140b9031408125001a41c040c1d171041008170b001d116101c0025a0701940e00050309002c0c02c14604480040c240d000010102000c28843d412410f4031240542c2421421840190989260f464100815003158108000c001c4080c8500d01540140e084013204440c20350340c108440301d01e001c201e43d0078401035151a24036075030580c0d02040009058004140504047c1c240f41029080091860000528001c1000c0180103940d01c10401210307030720380100f9074a00320740c6400552900c0c0e0740d40c1d40c070341040340b00c2800c0c0181c1101d0070800e41040343c48540d0131802500d18a42c0003001030050006c8020b80d6a045c0d8000d0b440440c2d0311300d001c00c0101d003e0781020300c4138603c40c80141d90680d444000d000280c6e40c42004606105440b4000c1c0400c01031200c802074090700c820f20003084102c0ca0700840742e411a0b103078800c001c112 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 577513129 1250 577511879 577511911
    0x604020907081005191a3f04150605060a02070b0a020307150f0f020415081f1d07091a0c03040504060b030403120e03071b03021005030403080106090605090126010617130209 76
    0x100c0071f0032144c080c00189178051a206440c0c28200707c0b151101c2c40c002414442e14014001c5030500c2c01c00203586502006a00528003e0b0034450301c04070039030054191604bd44000d0040d030380003840c040441100030700c9220000c14468610540340050b82d1440895804c000d005000c1440050301945405012280a1404039a91788510020008402e04036641da1041c20780c6500119600103002c0200000d68140301101c80d0581e00c0300000c913640c00c140e004610442b40c040c0901203243e00c941c800340c5865160f860036249440d5407440000c041b185aa44a04007140d00401044149a00b014290342005070003001403106914280c4007680707070300c505607000700429152240d0b003004900480c5524051075000e8160700d040850600081d009400c00c40c1c0c118000380818002249561044105008403030306519282d040202070001540c0b480241040340100b8103440941000d0003c0305c1000a009141030340b00c0c1030402c1d40001d00031251040061100740d52456500100f801611144040d5900110f0b1006003590 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 577514379 1250 577513129 577513207
    0xc0807120c021f0e0603072f030a1e0905090105010f0e0603040803041704050d080f1c0f0c020c090a1503051c08090604020907081005191a 61
    0x3080c041c540010350006004203070220066012001100304501d19102c1c041084840d0080201e1341c4002c0360900009108418103d0318641c0041290a01c2510036003011446000e401d400c9180da0410030002c00021040c80c014025018000d500c405e6001d21072420400d403c0c00e24010515039241032007054108140d14202c510414482c0310740082c2c004000303140580d070741040e0514104580082c2c41c00d0b1036901d001c168844400001d07500304e50032600054148600790156480e5014184c002c1d400c0c103242000d04119040719411109010071408070201400196200070b03070f84a20445070030550a1003590700099001903d0703070303842800940c8035020300c0700802c2d084480701c00b005240b0204c2c0d01c020301078815480d1074022064101ca24686146d1550740b0002c45a54005519a03a44401d03503019401c841d50001051541d8411742400780d03ca0424190303d41202d580340081144d500c17122041c03410805142400b808050410382d004007916051001d054104041e8440c010034602640b010100b100c1030900c03101403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 577515629 1250 577514379 577514387
    0xc050f030a0320100f06060e09010f1202060c0a050a111002060610031805010209010311030c0313110a060e0a08150a020706060306021209010608030a020309010302130305060108030d06060c080712 86
    0x403202010440030312401c0c210000c0317880503200f1409124041080841e0001550130000c401d81d04884581c1c9400400c0da00c1d0483c100b0329501c00503410380c0c0000040100c51803e00c0100190129244503a0082c41440000d05140004c4942e0754a15480b5204000002d140c90f540065080e03002001241c0c8822001d0440c102900104280052803001d0b485908080303043c44010743c0074120351802030700c092103a00c075000040e914502c070484014a0405007400890a00400e52201d11059480b078100403002041101c0001c0d850700d880d178013110000320a0689402542851036030007009000b201c0c010600900e00c0003035589804170040094159a501182c8501841f5203338010f03000468001d041150744040c100c000380c6590f24222400703000c42d800c0405c005010b81002080720904055640514140f094000045001e07500a0600c500904110880800810b00901548d402025071340300031940c80c030184080300b0035903c03e03910910900460640c0c52001c54982011a400aa0b108034400b2802208a8040d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 577516879 1250 577515629 577515643
    0x806030a050601030317220b070306050604080106090b0f010c0b0a0f11091e0603060f0406080d0c05061006020c061b060c091e060d050c040902070c050f030a0320 71
    0x28001e40b02c0d0030000010b01d034008090302a84041c41032018900d90b55694482a10000120310f01141d0010014020120710a03a8919400942c145800300d022541c80700010782c0d680140d040810540d5440354200003400451244101c800c105507518002c0c0f84070080080e00c03805a001000e440c400c040701c0001c0785c5802c00e500040003544104000c100c0c8074a100240c404a400030180240102e600c80e11076070b0550040f07403500560f140f005003940c2c9540d950130140489001d4800080c1d0308282c4548002c140e1200074014003d40d90001d1b95140948001c5003081890803201034840e2020750781c520000d02003203602140f40b45010728141c4486540b05d81d050343c4442680d0b2460050313030480c050304c07091204034000c56004104000044035107400031900e01c1300312042e01d083c1202c20380d07011200300321304800c2d40051340046911122401400d400c241d40e03400d10b0b00590303004100840b1f10f400700c100e084c4294a0440c1c8070b032441c02400c0c2d005100034007851341c0c0034250a28845040d0418030401413049a886402c01020b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 577517985 1106 577516879 577516883
    0xe0f06010e0409021c02091311010507031116091a0616021210020403060f0605091305160f081507140306010207121b0e070f0806030a 59
    0x19603091001c1401160055140d14502e00542d99444000401c816042480840c404840c810080d41a2000f054150109600300340c00e4046021030440c00349050007828007030341c0c42c441030405440001881c0e400c1039840c071488030700010030400e00b501d8204540d40780d0b400388441180340078900308040300c100110303410480c00c1c0300300801800c0000480d000c00c1c0c000317801c194210600911660500004400700401c0503000542002005000d01c540c000c842c90100781002114100400618402406800b1680320374241200741c00b440018002441710b40501ca10000c43c0369550007054040a07460721070014075001d54bd00d02c00700d17421001002d610414076035951414140c1050340780c000c141c1000d4010340c114440c4035004100c07148106d0440034202d000300f0700c2020300b400020013070003a4512a0401c1e03010307050000600c0b0750300f0b40012000303060036410f0600d00c0082e03851001083c0303080c0d440d001c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 577338129 577517985 := by
  have h0 := BRFrame.cov_init 577338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 577338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 577338129 ≤ n) (h2 : n < 577517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
