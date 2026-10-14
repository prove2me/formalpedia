-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1055
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:01:57.594453+00:00
-- url     : https://prove2.me/submissions/d9ef917c-f2bc-448c-adac-e4a76895850d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 189568345 ≤ n < 189748201 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 189569595 1250 189568345 189568373
    0x1c0c11280821060d08030103020114041e090b040c0e0f18040c140108090619020d0213090507080105091603020f04060c170c0d08061c0c030606090902060d0207 70
    0x140c1080410b000070422140c60340c580515850010b00b0b1070541d1402c1c104081c14000c3d11000341806000e10043c0b000d544907410300000d40c01d8103c032142c070b0b0984a86900c5100c80c110340c1c4040c480454002d05000b65646401810020142560140400c0d0780e81e00001d0201c010201189001d00c856204075100ca40c0c503900b900104103109441c1c1c54050800d03082000d005440d9001d000190050844843c0c4554412002d480c450308078840608215142e006808541c95003440b00c01035200e0b001e20080f0b00140e41071004190650142111300265440e00e50039000f5100d004002e103041c8000b8034010081515801c41b0a9801640540f20000b06500d462080d00280104451010189808640410900d0700302a00030180c0703000d01c280461249050f0b00c1c81040d8403401e901180e068111044000c50703180075890681e0052401020018509154081ca040314911103601765030100e051601002800f026105003000742a403244240140345164011850174070031155200d103c0307039000440d40180040440c1e1710107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 189570845 1250 189569595 189569603
    0x31305010302093c0904080f07030e090915011403030717040e0408090102100504020a12050c0423012102130213030b0601020d0e03070e07090801021c0c1128 69
    0x85401c4000d201c030805010b004c0b40100c603c408011040c80b10340313000e04a4500c900e44c0011001d2a059031311280c1c10641d04050310031824030420301014540350341e81403122442540c09000a1041070351040503030300c40e0f04041c2e0051524440809618202d914080100c848407508412a03940801c5071800030b201501c0b955000340079911044041c001009240320003010140426401ca0303c4881001c48031104880741030307600940c0000100303010804100c14821185840e8000c0d020345004545102c0401c00ba25942d40c100380c0c1d1104444030000e56a056060340c140500307601054078114a40c6501615803202c08844080e205150640c10313081e41407440d804a4a400520400114540f6640c0c50400840a0241c40850160180c001000380399031042e844011000c100600a0807401c2ca0100c0d82d0000d002c5c06040001000700d500004600c0d100309000900200d040c0c1c5004e40142401680c0d404200c039110300c0c11504002900030f1040c05030800280042c60340400d08a030f04203c0d0380b41c000d002c618ac11a00c400030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 189572095 1250 189570845 189570889
    0xa1d1c02070b2101060f0c0b09010e01050a0501170601060207032d0308040b1b090d030e180403080112030509010e1906032306100503090712051e03130501030209 71
    0x81450600f200c40825815903a034002165903226107043c1c8842c103400c0c20311000103002c000b109020420800c0410b80100c03114000042d04103a440205084da001114400c0e13405480340010820401ca0321100c0c0401040c00c00500700950401900940b0b440c030510014056a00b0b91000c1000c912000c2e0108100c10010940d203603803151207143c05080030300d00700c90540c4c0203210783c800503107c00c41c01c0304400d100316024101c1515000510f8100301c02d00200c0ca405900300988450000c080c0c0d250b04048540d010040c1c5481a01c2d8035152500408605050f084a401151071044000002c0c0c0c1001c140e480d5503001b42800450091410080380c1003140380c1d00081c0101409038400a07a040c3c0541c07102c1d04440e002c00c150800c01c402107041610741c500a0300c2040d0040c3c1007010010445104102440d0081034440c03d03031f141c503642c0e401654004604144240d5454214420040700c0544a140aa0b1b0a20b00030340654101599802c00f54003401c3c043c8500d505040d00010002c00c00c2c0d440d00c8180001d809200d00c15 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 189573345 1250 189572095 189572107
    0xc03090e010e150a05130e0102041205071701020901050304060b0111011d070510020303040f0f0501020a030507020f01050f01051212030a0915020306060a03020705150106080a1d1c02070b 82
    0x1480541069030701e00e143c200541ea1251450610b611031005407031014040f6459614144586001401c003440e02e0703419550309200c040381b40c005a60035010076070f0044004040c0e0900745200006800c00e010204541a8810020003103c0e0741c010f000d4035880754200a001911404078401655102c100c0c0784001419407908400d83c64102100035042c40000d904000c80700c10903100c2040c0700f01c02ca141d03030008001d40e09c103000240000309291003150a0030b00c10118503007110f0196944500b0380e0030125170321000c070b43c84200300500a1340c10001c44402100080080c02942810b0720114044101801707668003a0020901c5074504180800518004641a900c1d140e41c81c80c16200000060410303040c120b8801c50b030b00e81d8110140c00b0500a60340502002000103262031640c000641c02036004401c120307005c3c0a0949030030701d00c1e039010b1007660080c00b03507481c1c0340d04a10f000559041298200d602c070454150307143c451245014400202ca0150050004041491100701c5e403090f40381000035800310001c07600000e44 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 189574595 1250 189573345 189573359
    0x906060d050408041712030c090a03080403080a2606090c0c2a0105040f05190b1804050108011802060c01321008062419050a060c030f0c03090e01 64
    0xc1040305c039248038001e0640c524281d02c0c1e845840c0b143c28410710706802d00c0401c0362900c45a00030510030600915281126560350342e10040781d0010390054843d075402041008501e80c00038940020b090340d8041055100c26002d600782d50044003c1d0005000e90401c40000300022b007070500303c60b031515290003260f24440034024a1201c2240c401d60b0a103000d1101c04160321194003d000340c4050303074404100080c0b21820032061256902040d201c0d04070401441d400054120909002010f06615103203030006185094014881540c006901c00100d513850000d03c103524203100c0a001c18484e90403100c041e80e60340e21069441c013600340e19455074009424007402c840303c030403009452086080d002942920950391550280d0910142e4800c1d0501500303d0000181d6020310500c0e00380201d201c1040e044004911040821601d0328440e074a00d841c00344807001400b25241020b40d40d4000c0c20180f90000000e07903140e50061050340d5030110001407060006a0204050082481c0b0000d0725402c1081807a13036940e000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 189575845 1250 189574595 189574597
    0x20906070b040203010b03010212150109050d03230412080d2703020d050909010b0a2703050f010902010e1c0f1101030c030c02190309080109030302070317070e0906060d050408 77
    0x60b040780710303628020300883d040c2018001e4503c0c0146401c0c003180c0326916006540840340c440c100080c10802c41c0040852255606140710003814000da86920403c94598108050b480b6aa004026210790034030040245090312086403141e1580205842c2d2275001c0c81880c0700251820321074891a04840300324410340085034000000c0443e000c0c0d804c507949070148500c240d409100b0001c0c442d4000e040c0c3c0e8018071004603400300030960102c580c6007804034000096040443c1584050413080c0b00001184200203004040140e51042d150600c02005104007990000c2e101c01014001940610021811052900501e895070b001090b00071000c0c66503603078285000380031500c5000d43c180c0424540b0350782e0000f0a200b0701c110040311205400400a281d2140050801caa01e500c4048040040802c40400c0f5140b0030700030384144a10030b03200581c90741041e24000d0104860402208a4035514108200001c4ea1062030300030300100540b030028107611000d01240061052a0f01006564144801e0000f0070803941c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 189577095 1250 189575845 189575851
    0x1605060912092d0d1b0e220311031306091e051c02150406020d08090a2415051e0312090316030311010605010806180406020906070b 58
    0x2006441d18505064084003450003100311194201007000d0341d02101a0b251a04940903200a050a004542011000030041e00c950b4004a861003d4500c444021030030041ca0540580450800754038103182415800001c10b01c00600d0808070052208400c081c140204203840303040c400e110580b0b039100401081411004000c2c460940022016080042c2c1007038004906080c011404800e03502080c50581040a0f012803104402131441c9d44100c00001aa41c424882d4041010400307601e4580303280080181c14404454000824004c4480812014000102c0c40c041c846910031520301440c0c800400070800c2194035580700728118a0003e01d44d600c201080782c01c10464a08032444526001d01103905d09840c08040c0b01c281d050b03070000c0c0c01c200c2c042c8403c6d009400901c40c05411112030701030000c1011883d82e1141e00640225007050000480b9100c28041c02d4064442800c1088083c185030003c54101400084040d5401030024003142c00c10110f50103c680f4104001c208070744400150900030306008041d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 189578345 1250 189577095 189577111
    0x20a02091f0306140c0f1804110c010b09400803070503060a0f0f0e0a090206040b0706050601080f0c07030e1002031b060708010308070302010f0507031a121f02160506 73
    0x300c4002420709000b28101c1d01b007500c031036000e181026181800b1441c00c0c0080074503986c0c89a19550504000a4070b100500070085090001080000000080c001c000b84090481c005c508031200018661005500c0e541c4400d20404840d0350407829182003070014080e41e003e000700b420b440002402040d69106001d54091042144e04550050742c1b1990034551300c0c5207200703501d8054248903040000d02040b200980d44110095004940d083c02c40d800120998410b40203440e0000b0085011020f0018520801e0391080f820700b0205c1c200e040c10715040c804850024400a91004001288800c040c858a00303004400800b52803000c002d2406600030b504c1b038000c142d18981c4849011203122018200182a82c05200b03a83c665186503400c40e1581c0c9d800b54000b070300c00d03415592070b801c81e90740780b58a80c411103105203e260b4000a200e10710b504013548080896501611503c51215045140000400c0c6500700011a89241000820320003d402c042d000f1740e140c0f900d0321400d0101071130038000003003642486000d01d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 189579595 1250 189578345 189578381
    0xe0301090c053a0c05060c060403110c01092c040c081006180e031e03040b01080c01020c01030518060c0309070e010b07030509011b0507030203100903020a02091f0306 73
    0x11500452580303022801c1e00000c40030003030080c542c010108141898105010740041107040b9103c07004585103900004040c452644800302700810703d5404003613a01c100030044090013100f04441c00080c2025454002c06080700710081c1d04400f4a040700b414040d0f582d142150f0882d09140900384038070a02c1c4103104840c02c2e8040e6022458800c03d05104403416149200607100d2031900308c03000c450041456100162951004008010341440e52403100c507581c0c442e03402c20fa95a403800746041d02c1c0404041c0d01407166030f44000c02000032a80c01040030f03520301c0e1081c41c0000d407582d940d02440c5580b190884e490304460003003030244100229450019882102801d0450325450780d11a00b0300f0092a091080020101c0144071190020344a01c004200d8418145000c0b119001c00600700d102c0205240c2040b500c542c419042041142814000f0250300c06000c601008091110b882c06921401701e43c00081c030070028800003650799482d903049400d5280e0f01042510400b516450203500a000c0005880300d5952 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 189580845 1250 189579595 189579619
    0x909072a0b0c0a09030b06120f06090106091b0c0c1a0d0b0108040803040305210108100501090203220602040b0a021e0307020109032301020a0309020103060906030519030e0301090c05 80
    0x121140c210343c40c0c40c0d09a5a80e028851031038440304500c0e036010b4035059101503074440348140c0391001c1012504c00d50040380502020304002049900f100c4460b4400130005042c00394015094880c480011001100303403c1c01c80341d00c181458140d1042c0010341180350b400c4d0048440f03172030141c48100501101412a00e003004407400d044019914128102c800400c8a07104000080001c0d208034040c100b000501c04003151a0115105511100300090304800d1003540004c0c0b00381401d0595000f61030041c4400401181355040051140c2c0f6009409004e02100680190a200c208140c60f4103c40040511451958880d010b14038001e48440e000103010840620750030100f0703403a03031001c41200c0c0c03182e07416151640114990350b1030501c02900a1070001c640c900081c0841c0c1d402e4404e00081600700d000e40e0b400900c0c09400e2001600301c1e10b05802c40441146800742c01d1000440c001180b072412108000c480801d100280740c00c0f181900c01b0a180e036055402c0a00110402c40200c2c511004c0d61000c5074000c0c0614 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 189582095 1250 189580845 189580861
    0x10305090318061623010f05091018080d021207030e060f0a1b08100f14090402150403060b0f040c0215090307080c0706020d140909072a0b 61
    0x40203002c0304260814094040450a01c0d0180c02456840d00441e8464070300d20540e10380f110300b85403014040c80c2c4081c54070013504440c0420b03c03803002c10088010081155040811410340d079801d25048003e0f5941d0345410710000340c3d4501507010440c543c44009180c1e20002c080c00600603410a4009202d4801c15802007008240039010300036025151000510703890355a03210008803580b0240a00408540d030b13101441d4000400c069108084040b5101c81285003415102e800780b4110070741c080010650120000d1040e60a06685c0032100380b41250b114046455600006000c604144600545048001000010800c00d50070800100d20201c1f82c02089084400c148015038403000786e80c6005070401c990889045114030329068102c01c12104507414500c0d25640d0344119400490a5003140c0d006510801c0030035070400c100e2048030300e54945481a100714003940c0703c0138020706611034802c20080c00024100b40c452980704071208a072214941001b00030a540e035104000d04c480589130485404002a02c034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 189583345 1250 189582095 189582097
    0xd18050717010e120a0f11030708031302040504060b030d0e0108010924140319080d0914010c05120601180e0a1b03090302070608060a09020c1c020d080a0c0504050d17180103050903 79
    0x1f64050010f10315043c1c15aa0b589200e0b800103015000c0b2040784c00d0b82c00003588461041c0c1d0702c201c0c82000002500d2a07903004152030854030400325010007414580c00b84090342d1009a0034110b6000788404909648018980200601030388020200e0204210001841d5581c4254845140c0400d43c2074408414404004040c01e01070154042c164104c1000280c0e0b40e131045038080314400340160503c400d401c1440840714290741050f040c0318001400801c8803c1d29006410b8426040313282420075500300d030340ea925419020101446020710032400301c000520884c540f80c0059400072502a4000300f82c1c9207241000d0001d000c0404141c005126643e0081403d40c000c0350312900441c0020180446a45441c0703084001c0d600c80d04040b1490300540703d4011601c01c030381c0c0400521b400150050034000010141c010075503c0000c1a4600403030612518842081d0440c0466094840c107480040c214006810400e143d00c3c0c900e8007420400d04000340394019480d11142d103080c0318500b40c0c0c081c080c98681003035860392 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 189584595 1250 189583345 189583367
    0xc1e0310060305011a0a0908010c0c05011104030201020a0b0403030603050a0309031110050d020c10020c03120f1509060303071505150307080d05090a0b0f0d18050717010e120a0f 78
    0x45185480072081e1721000d881c090401307080589804586945c843c1021420744508004034008a40d196220500308078080c0504662250401d262500302803a42e00002e513541c500f2080545404940c00c0460300b898801d400c1900595040320071503011040d1071a0003032103101d65100c290703804c6070402400951441c2984008981700050741d035140c106610b94400c3c50081d4094007240c4cae100d1081400e9510711200e01c0c0040e00500803400051038484004412200404900810105a1000b54400c000c05003004250582d04844242d40c081c1b001d41d24800420b1542c8912100640992007452241042e0000ca421440c4035101e65046190403000d80c10625640c0e8010f4060103625401c554040480d1074070820103001000d000038490040c2c181c0d6040c0040c500c0d800034030442e2031040009824540a14035000301c2002c02481c403900c0d001c80c006a240d0303a480e4041e6000301d194091520311040601d1600b500b141c8000d00740390341030b50341450304010b2580300c690016100d0004600704038110380e81540070703031030b9601 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 189585845 1250 189584595 189584609
    0x2303060f0f100504060f030218011d040305070b180c0d03080415061511010605010e21030d0e011b0c0305120403020304153204030b0c1e031006030501 66
    0x2020307103030003100e800c25070307030041541000c8280714200040c0d6a4840c00b03444000d12140821607041800c60040c004000000c0141c103600302c12034030041084403000c00ca02d07001100d00580c0e91380b9541382c41c03400311198461143d000c1d0000f02500c0602403100009031080a0703005241085600300d0703181d281030055896940340041c2c0401d892000050114801e03000400300e082103600c00140260b2502700704183d0200010000000400196910400300c0e003d100d0720300a0502401c01c051503100000c00602460b00d01d644840c00007500016950140c9800c01c2500c001140075601440042c03003201c1ca1500070048500c0c1202082080c05040c03d0044c05054101d07003590b00341c0d0700c0c00c0ca400c0e0300031044244501e014004500310321081200080c0b90303400c105800c20046c02c87d92098441c840c8900307038118104603900040c205107c0422556012003141c0c080302c0880390701404440c000d5903822640301c00c44c003130580403010b091110044150ba540000b802184142c01c05c4114070202da4035450200c0c1120b4003401804c0b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 189587095 1250 189585845 189585871
    0x305070e091302060316080709050a14031e160510091e050907030506010f020d0503011211060403060b090901060303300c02030a0e0f0d061113230306 66
    0x540e5905081420950100042d0a8100665500d034046102c80d401203d00d43c9050004040204200d58003c48043c2c00440b03601d010b02d000d82c1010005169000b10b4403450304c80e841d450410002c562818080c4400842c0460703441910240428bd265072034499226514050800518010500e403600c403041c60f41c8500282d0b25203482c0d03400c00383d10700c8103c208810a450141146400003038241c0e2100280b511400d0035560204541c2000f000150a114035007030101c043d90800d0303800e50f1406610105a074115800c119801c00300032240d0600350164101c0c08509a00302070b0005000c410b01030240c02c40c0c0140b200690343ca12280d1358902840d400c07110503000003030001e02c0d1012058244d401c500d440c4846101c20305240c45042c0c1741c900c070400455010f02e01d80c10242c0c10114180040c10f401009812000170184d480c41c56000034400040c0000c4080d4a00400c09943c0311019903242298001b50394000303c1321111800e02507100d640030842000044103c0c0504a03e80b420710400c0e04010a941d40905001c0c0c2d422 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 189588345 1250 189587095 189587117
    0x4231201270b0c031b070c090c1b08030703060512060f0121080d0b130b0f030102070503041a040506030f040b0604021c090201110a0803010302040c05030702030304061509050c030a0c030507 83
    0x2e034070f0380d40058100b02d20001c1c8421840e0700c0c44943ca0003050b2103840340307010001c05841c00012205076a0144007100034010101d03546c184c0b5100c001003511042d54004d80269599440001c150300038000d07178101c3c1d13401000c0304009811250001843c107004200d03004085255a03a50384103980f018400d04609018941d415145600262410000c2e2002d0580c0b00008a02d18209030003040031040112140b850b4586c13109200d5043e81882c044480d01800141c6c025490098252075039036880c400d40c800c42c0200e00324010001c0380484007109941c040c0c403005010a42d03909040c641d030700e0301c4002601c040d40d40c807a050700400d94901e45882191001e40840c0284044200ba406440c0010100c110080c1c0c144000200c280d4a000014082c07264201e01c0b441c0d825460b9410f500502c012184419845030510100b0800d21030895000000c0e01d5000d540300d14082008584041c405001c64080c1d03110b441070318200028060612003c0018600c64903030f1403020400032034020011000e80700242e0348030000c6a03080c2c6407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 189589595 1250 189588345 189588361
    0xe011d0d030f09020904060c03140c16050f011e0c0504030317100302190801180b010b0708130902040602160506180a0b0f270604231201270b 62
    0x1d82468034100000082041113600030520082003110204d0740c03140d5508103009000e8040c8540100ba00c016920112a490000c0c910706c50391141403601688000c503c0d028200f00001040f0100d402c5059100070302a402d851110040c00040710014000361506121800c00340c0c42c0b00c0d0050b20103c3c1d401d030b41d0306020381d07200100b500e019003005010403541d000080f0b0f0200141e01e88014001d580c04000300c00c00c12040c07070000322508480c2002c10039407101c150b40c285c05010844043c189415150110080390b600c203d6850300b5001440f070500c51003540380d101c0d00d000030411220750180003102c0c4603400f5645400390b010b098018030a11409807950290080c0080c42d074002518110310201d06020300b116126544800310f0106540180000311a0301c0b00010740050b0302d64802100c40c0c6090480c40c8100f01480d0510006121350040e402200a1082800c1207014a00740305941a00803102c0604030040500340300b400d050191490303000d41a0540c030380c4400107407151310854031090b2081c1c00040940d0741d1380310200c0c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 189590845 1250 189589595 189589601
    0x14010801090f0f1d0d0c0206122d01030b0c12010630090c0f080706080a1404030f030c051303060c03090c0b0409060e0108100b03120a02010e011d0d03 66
    0x801641556212456030503c100d118820707106400918103000300512400f500e00e000110303920b940810030744007121001a140d038029105800441c1e800c60302240d4035143c01c221214001d4060035000e040422661000340b8860303000d50305980c0a0540b03401d065441c40c10344825441840ca660b0107040008004002c03061040c400b4110b001031841030400c00c1000d02d003e5040400340004a07540069803035040e20108007403180b911000707040500e00700085903d0641c0d05034503a13246200e0b80044c00f0b01207000941c0140039034800840c0d20304008600d202d0b400d00d824010800302e0140e2001001c030b840c00502c0d8001d54012000c0c1c801889618909290ba14296610035000d030401a195030141034985202710b0015052403043c5004c1d04c0c009082e40d49907403030f0000400544050341d201501911a1400510115801040e80ec826040b0807101083d07455141011928000098890142411b408a0905881c03603064200d43c2c607282c0713018021300c80702d0201d80c0d402960190b4415070040b25030040340d0b24107a030ba0080d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 189592095 1250 189590845 189590861
    0xc0d0b04110a051e09060d05060103030804060609230708090d0c0c0b0307020f1902060904022a031c0c081b040e0403050406020d0f0e15091503010303091401080109 72
    0x24020041265554000c54283e0201044e40440304155009002c03950400d0202c03142c0c031800840d5500000d8140e0b4490684403001030101404006031000000d0910445420400c01044840410444111550081c0e520f880c203440b1008010180f60b004280094803ca8459014542a8024212654150000390303003240f041c2c0d40c21180100d5a8a0002d00080c10a02640c81110315070040e018054920051a081c8040300d0303040804041c040b403541001d40c035a001550703071200081e03e00607510a90b45408840c1d1900c0c550328600e0030f0150b810081c07030036400440a0036000074008134014001e401200c40e041074440c0e0317202d02e100003241800094488119030b00c44004075000441745034540380d19003c007610610000c41d810390106000207010011254100f2800c101c10341540740c150701d00c44100a00826400741d103000580b08100130844070020402040c03c45500d16802400d03000e06c074031241c48000c0d054000f44402d5001c18004003001030140c8000b61a840e40080c16035400c00d050b17083c410030300004d01c1ca01c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 189593345 1250 189592095 189592099
    0x120a1430190e0f450108070f0608010609180b040c1d0901030f0f0c030f0b0f0702060f01060f02031c0f0b09010e060402070c050d0b010806070f0203040e0703150b0c0c0d0b0411 77
    0x44013040c0f250780f02020145020b0400b41c400303080389604010020100000503030100b41040007040c010400c1e03550000c0e09000ba00d40400156070340cbd41c0f1f480c0f04c0710f015002040219034002e280207a00d65003103404c561482c24510f0780c400681d08902c0c02d01c0800034046801d103c090503031084507045400240c40c9240394000306104034401a01661a03486000605400c490100c540000f503005002d04504002000c50b482002d80c4010282e918101040f03291a20042c8500018081410b8402c2d0b9901d009105407141000e82c3e42d014205161440c3c40d1034081d040d021045041c01e450142441e0300380c1041c0410905864541104d0070958849409010003075204800a0711030ba501c0301e0002c01c15035a484048801240580e9452002d541044556402c1c110041c100d1414054080c845801e40768010064800f100d109906003085075440b004140c01404108420300391122038030b000400d0804610000d0480da000500c101c4400124903402e1140d25200b48101525030000540002c0000b40d112007040305680740 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 189594595 1250 189593345 189593449
    0xe0a0513051501030209060a060c0f081902012f04060c080702120a060b0a12020103050405010b030316030311040b040b0901030b120a1430190e0f 64
    0x145849403414440140081481110b01c0d070010415031520760741007900b0901c101e5070340102d10310300100a00360081c40d003030007080700c0f0740c03d206801480315400c1960800103089890030892204401b0080c000d00d501490007010f14801c2001d06402400240d510464500441046181c20305100702a200106203900499500004000200040c3c40f416074042c8002c8610f002844103c0da1031905901307031030039003500ca0700070003400030104100c25540320f0009a140e020f0034002050b803180d00340340d4050802004001d07014800040c601400c94010300310407042038013a5904021107015410110454070039803180c2071000300280014803079003180134020f040c901014140042c074209200042881340a0302141c4004642140d1018424010003074404001030703904001801059602e80d03688a1000e0b10b80b094004120465817071200c4246001e403c4507400e44200001301139990038450014214106c1004113030140c49445214565800c0c405d2000b14240340c0c11442d0110b5284170900c00c030035402407902c4d68400c00b075 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 189595845 1250 189594595 189594631
    0xe091002040e04021f02060114030309191a0301050303071403090a062c031903090e09031e0c1c0309140105060a15020d08070507050d020c0103060f0e0a05 68
    0x180300910060140842c40c40003890503004100951241255851012400c891429480c1c0d50104050b03054804580b014500b0140c0e0202007451401000e00c09500101d40310b20646460020043c0c0004403100342d071031424100100115000355000a01c2582d40540c1b051018600045060b0450150242c00700c00b100c0c00d05d210032001a56404003617003d030001c2004a07000048001c204961300ea020981e0b00d03c042140105100803035513864804408840365010b4604e0303182098400c9041e200107040701c184641003814841c049030744981c4507000b08e00c1c084500030440d941c0d020651065030f02e99601c000280c80324440341400c10410115000d8081c00b0183e40d030000000084007042503c0e24051120000551442d25906110010fa816000700c1614242c00c403228407280d0340010680b074103049034a0200c50646500c98140e8050143e0b440041050040614180c0c00550004145409501c02d98050020a030345d03015103400080180243c9607403041610010f803c00f6a1500f006402100b03c0c0400030001d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 189597095 1250 189595845 189595873
    0x140705100506031605061b010e1014070804021f0516080403050c03060606031302040f020a0e030c06040b0406030b300105061c0b250201060e0901020705070e09 70
    0x842100e88422125544038140480c40c00c0401c0002c1c95101614095111241090002070f210302071115544034200b110310303003004910301c2034120b5030103025040b0803075401410812290000e0700c00d5a441000c031100340400524203901c14480d0601481c0c01408040350392039218500200c0036804500c0100f03000b8200311030400c224000c000c42c4078403402a10360755121821407903da818807041d404002d20070742c410b005020503555002d04aa0b0001007040202070346000c20300c0410040d0800012028080d0310220302d0700e05494201e01c560b100d044003101031300c64800d50300c03081045600650040c007841782410702c01444014001d0b40a1a0b0b4150014000602401603c074404116921891220351003103048141c03201c0103209009a43d0841c2c0216480d140c0481540c1c40011081e0703180d2006401140b020000c143c0d0840c6001e5094600030880080d01a000400140640070785002d100300c0c619151400002030705010306209030342c074055200b00900809440c04101c00001040a040d003034072405031140030360388a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 189598345 1250 189597095 189597103
    0xa02180a060203070302070e070f120e0102070809130e100c090b0a0c030810140d022103030907120506070f0504090c2102310b0d06030b0603160303140705 68
    0x41c00254000c0d41c2e2000341d0302d80241410881d41c0001104100340b0240301e40350ba04036120300003c0041c4d00e011384441d2503c810901c090a401c0c4c0007a880c651001a80d038040c490b610005003c500700c140c4610b0550340f4200701071421501304101030800c0d500810700f09014149250480700c2088a18640260340544889441d04141c0c400c01c20000440d921286050400d6000000a6400703079402c0c0c50696060702d082c003041003030410810b4a51051800c500c1e1a01190741307800f4039200c400403800722034269a170031000f06560307980103550b8040184100880050816180c0c055441041d5004008c0c19054658600070b0350031070018445c0f40c051000c2800003150754a4644120001d1602e1643c0c2c910465550b60083c0402505c5a04084080c0e1b00401c0505802e04c07002080c4030740481d410b002d1650035000840382d1505951160031014801c480016581d0003c1c015070800b4064134043da80d00041511940201070740c0d54500c0081200d40c0703064546c1040424011904070f103442c04801d0100f0b103401c03215035540f420 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 189599595 1250 189598345 189598349
    0x90a02090a02070555050d0e0f130504030302162604030201050a0f0e04060902030108011a0a170a0f05060708061012020904020706050c0720090a02180a 67
    0x911907001c0f484400b88502002480103004a425404100e905100b0340300070707418a51605580c0d9204890511516403696901c05001503890303030200241e03800300e440c0460f158203c951154001903c110240e581501d016200c0e6070901c2d20042840002048440e070311400340800410540030306900740611414040800c44040440f4495846901d0080141003030040c081407050038554001d80c144070910060b40c10800b00e400c0142e40b1f00301402d01c114509003c0703d644202c6007800b074001e03086c4400000c034001e01d5005541a40c844000a00c5211620300d050341f081203a2090040d0301c841c512008202414082440c03074110310034882590b210151640310743c1c844548445c021130703517903000c20704002419901003c6141c21500880c1d5000684264000c020641c49090356103038019075001906c15103581c3c80d07604403a91070b0740c0028103000c1c1c0d191040c220442500b20403c10303200c001c180300340f0007100003c1e070105260341800140316644c16261030390448000d4002040314400d90304505c9a62a85507940c074840341c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 189600845 1250 189599595 189599611
    0x9090f1b0810060203030f0703020d1b1121090907090911030919150e0a0609050609120708031311031b010f020304080c010503041506090c110c010c0308090a0209 71
    0x120781c1419001c0020002c9507038010400c642050082c8214100e600a01340c1d0007088924026860b080050800401800560619041d22041c01003850503035802402130f8540d001c0c5001983c0c0440c282400302c2d500450110311401000700100466a00c92030041c000d10780001903458030b1500341361941d05080c2201d40e4981d10100710100070081102d281d07000c00c40e5828185e007000c800c50aa00e4140e03642c000c0c500820060fa0f41c501c1d15440c04041e40001088090540c6d5000030052202c0643d608100d80c0791032003910380c450035010301c0c0c1200804c00213120131103002ca94810806440e550ba940a6291200030845048803142c203802d5080c00c0c241c0e0300b00004090804007109070000d06040500141c0b50242d60400d11041d900144800c121003413000c142041f2050080c02e042e56281e0352480c0c001c000752140541000d08614240000ca644203c40d8000000203045444210a11038444d2040743d5410103e2407041c000b80602c062440001d1080b400d0a8004140e081103c41090055001429a2000700c903462 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 189602095 1250 189600845 189600857
    0x50c010504061b05070b01180209060f03040501050906090d0302030c07140d0306050f06030c0703030b0a0e1012050303150f030d02100605040605180c04050904050c0306070302040609090f1b 83
    0x401981d5043da002041c81645003400d91901040b962941d0804030144100c0c0b0380c9116041d001c000040040d0125082e000e002032119542c0c0b62040b0189880390800d07501950f956107428001580b814002071500d0080a41000400c0d580045200440c00795000600883e400c480c00e10407480041c110300d9060000d0b4403440040d009042c00300350014102e4140e90b1206204403014003044100d9107461040b00d410214081c00150765280b00d0502f03401502200305e000d43c020f0365502c0c00092042003c02507070300400b4494075405100340c0e264070001da589150280a4500d03002000461006410703030f100325800a60103000c40c0042000580064208a4110314850160304035406107800420240b281d00d001c0c0c0400c4408000b05400c02c1d000c00d40f412400c003201076100781c494000ca0a612140c00a440081c0781c010540030301c9150a14290f921003c140340b00070300070320802001c40d600600900070b0720191409039649104081c0b0f40340d11140a048a5031000321040d40d5140403d50047d26080d02840e016103d460300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 189603345 1250 189602095 189602111
    0x3402010e0105070e010f1803080403050703030f020a12032003010f2603120a0e01061212230901210605010f030e0a080d1d012903030d0507050c01050406 67
    0x2040c01c2d00e0b4010641c03400c10820352540d0f034890fa0480348510030000d203440c0007079003041550765183e601415a000603119120104000041220006012003624440da035983d02c0c104200c00244e968444044004040e59860744003d90207034881d40c00004101004580040855501c00b1320160030307402078100b0100d0400c100800e000040d5a048408444070006608402c40fa0340380050545030300411144200c1c0108150210703142601c1e03a00481c0f40000820b000704503040d0303107400d2072a201808010031101f12807162264a1594014903031240c103600740181e40844495040000101540800712803818040c070030742c40ca071500c80c201204a61038a00c086000406608080c000340c80c0c0c00c41080305004060410200c400e482e480420940351b000d5100a1460701c8401b00002080a4441003078102080ca008495044041905401c6003070b080314409898007030403401c000350800140026205980583c82003221400c245034a034003d0307500180754540316040170310403502d00307080d40d400755020384039291240c00e1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 189604595 1250 189603345 189603371
    0x10b01030617030a030b010228020109090e070302010509040f020310030512071e03030b040e06070305010b04050108060f0f1005070507380c01020d0510050a06020303340201 76
    0x410014203030400ba80440b04041c04000b95580c82848107890070180c0707a502c8040d099000b04081102100a480c83c609040350728452166101c03801c1c001640040d00840000840941901c10301c03600400700300c05400d4107400c0d90015645540700b1007002d6000790342e607034008a146140e88050350040d410300da034046186166081440c644140200750300f92840003084802c0c00a00e01c05c0b210841d01c40d1008103182900d00c14181600180b07060441d0540090601103801c1100e500482c1180c41580d05460404c1266218601c6854500980c01403a011810316400b10b4035503c0c10100c0c00308100d030000d216000c0c03040340d0800310741c6189490002c030002c9500824540100311041c403042029098800d400d490395015000c0c415010343c22101103405e00743c00810031030000c00751201100d140302c0440c402550f8a00395a14038000500d4210360400b2040304440010801d460000090340442c1c540303500450541c0ca60b01d54818412818451b5120306454440900d802445e825501000c0f500803a00001208822114 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 189605845 1250 189604595 189604601
    0x71a0d05060108060a03110a051e01020706140906030a090c030305070b060402031303080a0917040512120406120204031a1501080c190908030f07140a0c03020d021c0302010b0103 78
    0x300700d05002d0803804100c0e582d100c60080c0c0084076048415400c607000f459001c540c0d42c48c07194014030741080130800d46805030113100c0000c1480200a900b2182d61541d9580110f8144a0099525280300001c0064040c0c03840d014000d140c00c40ea4a500019020800c0c4d503d42c28500906d510880c00300b50701050000901962540940e805507096600f5451744c40c107544007824801e600b280060038040024046140c501090380807034540c1e03a00041c036105440f0b81025141c03258001d4400c480c82541069418822458042940c1c80d94056020b1701c1410a81407190944100600c0c9100300c8007107070300780030000c040751000401c1d89221075032a851002c50b05208002580c501890507286040c84285e50521041c00b2941c41110580201c038030201e100307662000c90403903072180f80c1c1d40001018070000c0b81d01c603105a0814000d0210314850034001c0c0040d1000f02101e500d030b111044001d440d03080d110104001604202c0300c0c811f102840141803e0100034801083d403907138000d11005500603995101060306a580501c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 189607095 1250 189605845 189605851
    0x4080d020610030b04080304030c0506040c1a0c0d05090315040b06090604150501050d060905010e160815010507080c01020a031506030b061c0905030307021f090f1202071a0d05 77
    0x5441d916020306684900f000c0031350240000f000c40f1400800a414180314040303200d225035000c0140e03409407c1a0400e0611510f96005407807a200d00a05600949090202280c25100f01d00c00903040040500c3c030180e40d82d82203001d0103074041c082c46480c1d800d9904010805e504c500e204101124031800c10505001e03a0100051089004510381a5240300780c8116200c03444c110351007440c1017995000ca003160358001d0714250380305680b194100320008c9507410071a049140700d41c005290044041540d0503007258014410f5424040b440c4405810428551062005185107400b401e03026150001c40b0b0b00c100e08a03031107490302e5000655104003030300d00415a00004001402549070034400b56400a0004d116445415504c1d40c4500c650100c4004121507a00004030090b00304041d2034036841c12640c042d44658245a0600c10483e40c2000c0002c013100d1031140b012800d0f00481d038481c800c0742a42d03a00314040c05100340e48055106070b0301c0018081c69584860075440720b02090b60340d287c0c108007018006856001e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 189608345 1250 189607095 189607111
    0xf010c050405060904050a02040b040303050d150e13050328030e010c0906050702150703050c160f0314100507051b0c091603140c04170a0b1501030e0304080d0206 71
    0x4000400503a0f50b06000d803188600e044800150039250003d00380700a10851b84200c8207280046030000034150000c0c0540050b05001905004110703907210070500c00b00181c003c11700b101484401040c078208036001104407681c484ca04a0b0b00d0030f42c0b00704411883c2d0b140039080011042c1518014600e850b41401940f5402201e10002d0280100c02c1d42c0c007426440c0e01e401001c007003080c0440d03607806554900959031800c56401070110f41e902d00310f007801049a40b01100c011005e104460002004d40c001403071800446500a1850380054116904d80d101e9003107605007500c0741d00c034188000809c61310a2282a001e03112035200c03a03a85070301e0b0580c030702d08203148102210700c00d41042d698911140c8520711950340c0080e05074880c01480d0411082a00213001e01e00c801014050b008041000c84203140c0010001c2d551401c610340c1c401041c2060f0503a0320754058000030701091040c404990800c500120780b09006005050214040000655051543d0020307800981d040c0c1c01041d08051807034040c00b0203904000c45c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 189609595 1250 189608345 189608347
    0x30f03241508091b1504030308072007030f06020705010e0c0a0803030c0d0c0903051b12010c0c0b0601110609060106080105060703140703140d1a03010b030a0b06030c10020f010c05 79
    0x1c440380c42a201c035003000600b00069001c00031310f201c903514030b001d0200124102080e152202d0f00d905000700303130a10813981400454510560580106480c00010116901580003480d4003400c2d40d6031040c0c40701c40260304850543d002d100c410000380080c002c030b05030f003082a001040244a1030040001d84c8a0307031303441100c40303410400c140311100002c802242d2180341401d02c0400d4010b010003007124000e04503400903001e0700034203150b81d2442640307200b01e07042c03828100c030007001041c0ea4611141c2201c558220180100341420107540000f51400a210760000c4141440d00101c4c02d60b10415040000848440040d070300244014000160000100383c09840240e130f48505010701035078041c103001d030710791519110120089414410184101c0e00c540c2c90a0f01e00400c40d88504000001001610b069406105140d45020000e00f84d818140309a005071100280100170603956030301d460019420150040c2d805010f00303010824646c68100104140445540c000d050040360122540e0840741010542d00030090 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 189610845 1250 189609595 189609601
    0xb031b011803110603040c030c0b07110a061709030c0a230105070203040909110a06020c0a081b090604090501090b1609150f09031b030605010e040f030f03241508 71
    0x1915070b00650080320513141c4035580e03181d50800c035000039010351006104807441c076004202841d00b00d004d0030303030203200f00c501941d6207001500700400980d15010f2a03001884501805160b41c800a01840d002141c0c602a6441c01840c00d05044c2440708405064580032040780c003202d88241100365808885c04c0c070900801c1a8241004000e44a00c030318408c15803075684900174082404060303011140d0750700f802030021201c180d4070480a5120361045114912500d030203140042c0f500404130303242c2c516001d01100c4940c09110103040140709000580320b0b0350010703524040310b00011402d1042158040c021050303e009490f0070a0a62402e50002e41c1107000c00403400820050440e281c4400389110400e0300b84a0600403103004203d81d03910841d8002381115003080450444c00e0f501c41c2000003941d0180c801448140c1c0c880f00140c0100200b9900184051250380445020901ca1000012884034a1801040c81400c00c03902000c50f224011403161803004181c001c00000070030741c1c05828030038900d0500000c945 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 189612095 1250 189610845 189610853
    0x209040b09010204050d03090e0f091002070807050102040b040509150315130c030b10050301020c070302010e0114130e0f070f14040504020c03040906060903050706030209040b031b011803 82
    0x1a10040c0442880d00124034022800c0d01550090b00c3c2c0075003000c0200c0b0241c1002414008544101c1140f5400138000c601000ba0102c0306901c15009400140382a50b0301040d000c009511030041a61421000d020a0000520a0000b0700040614207145611a0b0906041100200b00501720340211440071106500c1ea03140401ca082400c1c620001d007000c00c0d81c94251480d1036200910009000004580d030120400040d01515030289102410301450281c8031000d0508038800c800c00d0400741c0e03104140800066209e02540300307004006142409840b001c13040045800d03007141304040460f441102c002e00c1400481d810742070307004080b0040c0c04800d040c0300ca00580110040b2050004120030300840d81000481b4200312001404081d00441d9146482c02c80d150b140d4000380145200281000c800041d110f22030560300d01500d41060203408141d11b0400250000d6000084213030f0006d440f9034401019035001d0100141810603d1180d40c07403400a1000107140e60010014140407030405401031002ca = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 189613345 1250 189612095 189612109
    0x9050916030c060c060216050f01051605070206031806070201090618030c0609020109180509150105010f08071412060a051f03051305010227012102090d050106121103030702 76
    0xd40359030500ca1605404c50502101078450001c51800c520315100940c410804005501c038070108050000b00b2294644580030700300b00c003106000400060b400c0c132120b005407404000660700501070141c402d00c4542e152840c942030a00231030301400540d6603440c60740c040c081c5500a021841c0d20b20f005c40c4030031200c1994060000241000c1c003504061345e403400c100459000d02d10380b801400c1c3d2107907951002811400c2c1e407000b42c034007101d0b007149074021340307144141c5249150895810395005840f0500002e080d10b0084036003490040209d010400d060390707501103400c000300040c0b181103103400c0988690316018050003e01d0b0160b602048c0200341280f051000144010350a0080c0212454007145135220501801c412000d80ea5000e000e03540b000848500d600c1401da041902104801c3c03103c810403010b080156040106030b10245501d000035074a07401c49444d668020940131a0040590f45015030503150a03084a04030341003048503040210b450402e10203510030006c0c2c5800c0480c010351521b5034507400b2980e4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 189614595 1250 189613345 189613349
    0x50d050130030e04021602030c090402010c020d061b0504080c01110c0409020607020a080309090a090506131e0c0501020f01090512030c0d11120a05090a0201050901050d050109050916030c 82
    0x4030440074031149042500c2514040e0b12504003c0066440c2c81c406610100d6442c451401207200b4400c4040505440c18461400740c4a9074058581a000c08200c3e02403140782d0301100030840301142d4034191040c00500f81c0003060000f11160b074559494034245145207180c1500d02030b005041c80000c030f0410001c0c440014502c0d802c85030941d004242c8241d14030104119019001c4029841074035080086181040040a00301c1051b0813115580c041e103402c60340400315000041c0c043d20b107401040001d8200400c0e04490020284124181c01c98201d00242c40c40c21a00003080840b041d4084510400040d0b90400009002c941948000c10002125070382d025a0355179944150340c0f800102000141c0845041030507a11040b03c2d00806110342c84c07118407103041c0b0ba8010110261510303440804503031007035194030946228801010082035070b131109400560301500401400f504201040201c21200941c500409009100d070240c0407d0900f040001d0070705100094042d080e2141c03080c0301c1000441c1724a030060003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 189615845 1250 189614595 189614669
    0xb01020f0c040c0e041b020d09061e050d0203090604060e030f030a0f110d060302010906030203130605060f030708010b030f0114010902030a0b04091a0a0e03040b1305040903050d0501 80
    0x4020742102c40a54110750f8105045500520308101c410886c0394a100454010500d03509031100c0154016041d154010389014443c0081d60b0488089032540000d218200d41e8155814990300740302c0500001816a4412994854a504172406000c00c11a050241440c201c0e003040c0990300304468005032070b000f400000c20070700f946a00c661030700c260324401c0e5100d40f0141c01c10314000c954413031101c007158002c0c08a610080f80016110320001440c10301c02e1083ea4042e02480000128081c40f6490b00320182c0000f402c0d299201114500d42c0a45035810003203480100350341d10010460b84460b0080508006a10035090200e90411180410f40c0000d40034450545501c68801603c0392070301440180200154030400e07801910740428101404040558101075858240c40401b465031103813074100540c0c8094000031000e034401e1100388203c280b2000074200320341d041781d040c0011a5645e000201607485841c0290082840040c00c8200307800c0c00c2c00f80c1800741c00900001021141081d11744035184090102100c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 189617095 1250 189615845 189615851
    0x6030b18060d050703051c050708090f1908010c08010b09031504050c10050306030f28140d03051f060f0c030309050609030301050415080c0d02060f0415030b01020f0c04 74
    0x5031655948080c254225420030104c604e415142d2401d2980d4110840f800096080040b00e4000d00e513100d0f40444480780da008110505056400051107003101c101030103258048910030181c020ba08950811400414102e000031810825260000c1c00707031034040e04007c0509008000f0003003c0e880018001900c070902d4940700d0303c80da03140c0c2007241c03c0040c4808407981c001c51106502c1501d6a10002541c0219811000d880060925080d01030f900c0d0100c004114461000445221251560703040c03008400b80201e00307240420b06403400640c01c3c003205500280200b0b070b03210144000b1200c3c1d030307150302d50406003035a11180541c00e19001628060710724200004100d248016082014400d401a043c8194400300719401c6042c03484402e5242e03002401018052454101034140e40c1c0c0410310104103c079200c1c0c0182c507000c3d00510a019281e42c00403001e98000c1e104015001080aa040040c001441407070501141c000f10150f00906882d24440c04504540c042a44444032440218551a854000b15000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 189618345 1250 189617095 189617101
    0x81b03100b0a03021b0a02030d030b010507024b060a2a0b060415090914120a081b0306090411102007081f110703030207050706030b18 59
    0x8000c4685181d0481c003a0000046071191807241c241d000741159406051443c0c80385802c00390501e50302d401d07038580039505034090440002924000e6100340c007691018500a480c000b0940c01095004003100c02070051000300c00740b1010300c031007204001b6091412190035000100c040c0c00c14060030300c5048074524410743c4000740e107111080c000c49459400c80006420003c8035103010503454003804400c0400c0d2034000d0b441e00000e803145803d21540481101aa640c0101d0508001e40c1000900d000242240c41a000c0e000114110008010044004030301100c03040d41ea404040008214000180c8110300301c0c400008401c0c6040c1303018068a030b1119090702c0c20f1841e50b0310303420803070207405011440ca42c00003290b84140c52410351050708010984080161a030028400c3c20001d0355035249032040310b240381c2107070059980c0e030040001c0c2404110151000800c1140d074a820314481940031035421401709a0018060f0700304801440420010003850900700952600940480d0b204015948007002c0c1c00d0500b800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 189619595 1250 189618345 189618361
    0x150307050405120d140a0906031109060f0c07060c0305030a0c09030b07020f0f0303130305130f121401060e150a0e070e18040f060c050d0f0204060f081b03 68
    0x76a0010440105034035000201c80610729140c12040c26010005a0802407480000014204507041302003140c2d50580c44c0da1034071700d040b402801034281e1a022131204020791051541e44034090110038a9040e82e07569604140c0e003e03180361010941c40341080c02489003541c00801c0d0404180c0760311041c1c103035001c1121600b070b51b002c859074081c84c0c1000b411544003506126000d60300088003400900d96004075610f1118007017842d6901d000442c0c0700302814121401040c0040d1242e070240550711000b01c51102c000e601d40d016008a050f050300024140004100c0d0720701800070f07400b02612810300c810000c001180c01d03c04036000104005280501d840c401e114a80f102ea00c500403040300816a06140f1961400c11070002400d841c081d500d400d12510480b0021480c0b080884002400f4651181d480e41d805459595410082c001d6240014244a02030040340d4100b01e1a0055200b041621040143e4031421720502130b212584543c6a40c08029580d0100441c0455500104048555080d070540c0c0702e40c5c0f2112 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 189620845 1250 189619595 189619597
    0x705060a1101020c2b08010302030a03030915050108060411060a0818070305060405010f14070801122117180304090b120a030e1507030f080403021c09090b0108010515030705 76
    0x80c40d4100f4805e2411441105040035081c040c0800050801c142071030500104690301e035800c3c00041d40c560040340304640003c3c000d521500510f44102d03c03822441c4250040c06c000c07035001340e110b00215040901040708200d200e01c54041c052030111a241d00708102510002d041d000000c19081840750360880440300c0c024100454401103900204452a034034061602c113010b419414000d0780c01c50f040c48615407540c522080c0c5a03110304525542c2c6080f6a107001c404049074109200c023520901c01e400e1150720f40000c909101003c14400f52112290020385001c800e1440600400d0580800241500825404808401c8038212a0712190206951110200040240c42880048600f40c0b05605e44401015000a5694080002100e1030500038840031032400c0c0b10700c5203540c0200062280e840032034406000b031001e550002e000b441220320540301030444490134407400f8852030200e8900b240070003180c007007800f842e05030540a2a20000399450000844d1160b00540403c1101c41000700c0081c5010384504 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 189622095 1250 189620845 189620857
    0x302210c0102040603140c0702150d020f03070804110f030d11100c020601030507050a12030c05010b04060902070506090114070804050f0a08041701091104020c0102120a0606110705060a110102 84
    0x100c0210341c0d60340d80304405001801603004040079492a0300004e2044002001a603c0d0070360003a003c0310846240c00c6000b1095440580c0944240c0d038280310300080864803c0c0074610030301c981d49030311180e4100303402d240306984103c80010f0b100b082e030141e041c801a140030a88074402e64990800000700c00503600042d00308180007006985142c41c03c80c1c5040443c0d030004120307048902a07070594481a03100c005028809406001d40c1c030f0035804460101d1300080c4103101e42c1c948107008000020f19001ca000008003550515413114421a8010801d242440700900c80c29801900d124001c110013101d12880c1d000c42c0c1d40c010190003d00100c04005001e1203010b014101c209440b203025581c1108032444d00c128182c106001e021580c0544294a01c00ca1780148607241c100d071f4010200d0505003000500700400b942c81400d1207078140d5000e0080d400501c1d0843c013000d010710a00b00740880c1503810003000906400c00600b4490b803e9000340350800041c0c8569040380d00c81e20b103914010f51158403900c107290191240d2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 189623345 1250 189622095 189622117
    0xa1809060e010c0c02090f041110030e06040b0106170405070303050c0a14070306060603021305040c03021e120906150120030304050a110307051e21100501050d030221 73
    0x80343c903140d640f503400101c540b002d9200310340c80c405a0b1181c2420102034402106c3c01085c50613020454001454182c180f81c40b44a081c0c60086098659200c2090130b095040d607040b20784414000062001c1d80c0c03c07558001c0b40c0c1141843d000c05515040d1100740c0d40d080d4511002d000e04c1400100d01c0c0c205001840355221494200541ca10300d0041c00103000c1c0c0d101e107203100c19034805141c80c0010400d94424001c4886145e48011052840c9003010304210007400c502e1003003000d066080164190b50028103044165900c10080540d0719007030300301c101800c1850010078a4505821120400c0020100390380514481007081c03a08150302002d100008040c00076000501c100d510003c03003088108280040c1070b003080b9100b0188564210400001e040d911065802100c0c3d0002401c0c698880410090610f8821054002d120f091f04459a0510315400fa091402100c8641c00000201a425840d8000c29004003815500303d01a82a81c0e10029100d84880c5441d04054021120b09091203000209990005040d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 189624595 1250 189623345 189623351
    0x140f060702040f02190e030c040b03061927020a06031e0b0a0905090610090b03070b0f0405040603080c06010f120b060d0503030a02090405100503060c131503020403050c0a1809060e01 80
    0x2a00d82c0c086d01158100f86018847d00c180c585042490400780110001d002c405001401192070704034100142141c184203824075903030354911030004401c02581900480c00c8417950b41d00b80c1c1c205401404031114542d04070009041c10f199000f2290303c3d02c400f10780c13022080080001088000070000a404401d0b80e071040c440700b030600c010f000100001040b031900444d100b04001d00156590003030312003540c12075100164160403800702001802c1d00700c1e00400c0800d00c140a0b50340b4180e180d0707002030b0441d40b0301e40040d20329400c003042c12000e50004016a5024103800b03000320f1a058582210020041d8048400500011074117010600d182c40d03030100040b0031903010301901d8881c981030b00380380000c0d0810107039548110b04060204040006203613102c8159213000e0082c0c55141c0e6136a543c0d000c507500132640d0700049503100f00000340c40c04208020314040306403a03078050b83e1541745091551502c40301c1290382e481b801d01d038002004181482c2d41181500740642e003000c00d080340241801402004441e54200c00c55003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 189625845 1250 189624595 189624637
    0x50a021f0f140408041802210624070f03021c0302030a150e130f05030a030204230f12030405040e010903020d0f1d060403020d0606140f060702040f02 66
    0x19054016031031888000004112009421003104903242c2c050358003510421007004107000c20413440945125010035000d015140c50307640c01c2d0851040d03d2812445904208080c01c0c80200e1034421940d0000c1200940b02c005100c2000b80b1098291044000c01411400115a08010103009101c0c90003103002584204840c280e03100c1015010b07510842d502400c09161911986107082000c2e4080240c07520f209101c1c41541c0c9002ca1400007480d060340584000942075005400120304000808500a41c1c0e5400b58a95180a0452052881581c01100034205c4424040516118018010010441140c0030480c0d020359802e4242903109540040390002d01784010800b03003050540140c2d0000d44250700701c580709128608101c0f0341580d80400303031001a05580c581c4508000041908445100040480c0d00e0284c1c0c07513002031312200310f1407400c80715540c84004c20070900c103010b444960302001c260344a280d85107540000030700c14494001c0003482980d5031582c90750151340c0e41d03064828282d04142c510400d84 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 189627095 1250 189625845 189625903
    0x801020a1101060902120609090f07120213060b0921070b1908010e0103081c0f090c0e091f06090e03071709130902041104061718030a050a02 62
    0x54030542050450341c03c1080008070b04145108644030740704000401606034980c0420060300c0d10700175290b401d007031007120341640a800d01031201100074030303080ca485192070001d481880001c804c51251018240e02d424400c03c40401800112462910120740007200300f1020b500f03001c0c102401800981c554401c1600c08110800f40500500349420034210050b01403241ca401251508004d00805580c803040368010400188004080c1070002000c1460101030300042a1410841d4800d5401944498940c2ca40c241844000c038440e00c054a0140c900000616020860340d82d1015840ca020580c9038081d08000c0c0040d0f0158400e001501a0210a000d54030101c40302c26034903040100309907515507031016410000401402200d242a0019081c0d016030030b0071050100050848640c1a45c101da1200b4003c042009044020320140c94240c80307035488004030100051b40000010030351b140d80200c2038007880c20940004140e542c1800703940780090341c8a00a00c000c0341055814089a1100030b64418016012 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 189628345 1250 189627095 189627107
    0x80a121505010329011b061418070e0c0c070305030403060203091006030312020307030b19080d0c020d061104090608010b1c0b1f050a0801050403080903070b060f04060801020a 77
    0x5070826079052203002200d0090595a980d542c0c154004003600e00c4401206501901da240300c905500100207560041c030341c81c1c46007600c034800712003100300d40910100a403410480220070201c00082d0700a140b0a1304082500c9a142c10140c04000b030f00303102254190070100200074110255500c0720a803a22265a0710f0034001940040c2c9904240b03001c1c0608030301880c8541e218005c1120b4140c0e9481411400d10b420040096001401030000c0507201c40165102c0e40ba035901800104601c3d0141401c0d1a181c1446d80b800e01520545610410203400160005641d80700441c61015820120004003103103281c1071a8004d11803030744600a40340c104000007503490700c10340c800c0741d041c14151142e011000040e01801c1c0d0b04061034800514400c5030a011030320140041d05845140b1003280e44030880c41d515a4001400c0c007803164006201d5170b45507805c0104056100a01c590800c110f030380211b00b000410b6a0300c00886600a004600038420407000d4041c50f42ca07070b0002c000420100000310756804902800800c2c1c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 189629595 1250 189628345 189628349
    0xb030316030201052203180e0403110106060c030503040b0a090f032303090d120e0a060e120306030d0c02010507020a060201050708010503060709090b06090301141b0a080103080a1215 80
    0x140d413030a0000348024000100b1446102e0900d40035041c515481e0350150794560001c0e0340c4044401d510b51002c038000c0317144040540030710301985074880d8504410941c076081d80c00c00e400c41c0c010821003402d80380c002500041030b00c1d0401e138480032441c5c295482c426110009c0144841c040d100908040010041c0742d003104060400c801e06c03243d02203003130041a16120043c48265000440c6520001d8198a858442c0c1140e268602940e81c001c6402e009254071a0718100303821405940c4260f84185107aa440010840d400c0e2801c007400606096244c002c0000307440e0200002c401c01031003c00f10012085a101c5c90071111143c2e802450200320a4965000034001c2100b26140d2000c10300381d400214151400142c000d10614160341d6202440303080450080c00303450b4030440c064010209020403405980c080c0501030803011001c0081c035183c82c000c00110006826400659001c4d0400c100c155800c40d408000c403415a500700c11015a00d05504808841a024035998070948a140288010340451483c1081701 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 189630845 1250 189629595 189629597
    0x902091905070c110613050909030d0605030a120c0303061a0c0d030e030307030b0a0e0a200c0c1507121d0a0f35010b0406090e0a0b06040b03031603 65
    0x4a140e40d6588151294250f100e40a441100c40828a80c914a008401040d40c41c041089030071019a40c0c5000c80d590020079075032002550000310300d144c0810868401c3d40001c0104070020300c190480794542c17007490701402101d00200010790460005040c040e402410081010b101c05850300c0040c080c0000c056009181448101d0242100081c443e078030034003613030310032008001c050341c65a12074007400c1d00180a0402c0045d0000700b2164001a240da1143c046441b40c5010000410580c21510645804c0140780d220300208140c1030140c12401d807000070344881d40e1042500c800402410306000ca640f00d000d4150000c21169400280b00c0059500070038809103028240e52444d505400c500400c144542c40e0300688140705a0b0400401942d540c007000b0b01d4211103246504003441451020a4940b0040f490b10b505241e034441c01c00004a052510410005094805003003000001d0201029112075807140c0c0a00710950307017008243c50f80e4495000603980e40000303040381d9079101c003402201382c0504d211200354 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 189632095 1250 189630845 189630851
    0x70209011d060f010e032406011701030314160f060b040603050a0809011103030f0603060609090c040c050d0905010f0609050402030d03090c05040c27080a0f0609020919 74
    0x1d0701030300090950940824811210850780d40d1205202a800e41c3c0900c1604004c6100e01c01e106984051140590240c1d19003184d580c01c4482c440c902440c800040d0002e41040800100c03442e90085550781e040c103407941850100c142c1c03410b01c03414203280d000b607545c0710800c2a4046001c00811100f1810100e506215503418403601d516041007104030b80d001d2101400a030020015040041c00800c000e243d00b4405040803c524605210440d29640013162200c4041041c4014012a45000c021040e4484001c45035000b49252030004d094035541286646070007244c407803134101c0809000d0780c2500c80008501e003042001c0300c11420031078040d00b0501709040d4501e00e00700d0007040c0e03000280a02813007243c01400521404600e5242200105258581070702c859a4842d00440c4c295903c4c0254890781101380d94207034003444480301d040e1025a0003854404d005500c00405c0103400702c0810000030250b00040700380810095410030002901d0624002540300d0400d6003041400c816011a03a440444030307207020 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 189633345 1250 189632095 189632099
    0x6190306060908030a05030405031308030d050c03100e07021213050405220201050307090503070603050405010b09060312090a0806090a05070b031314011409010b011b0f121e020307020901 82
    0x140c82d1038100340200301a0b50070420060100301d00580c02142c02c030344201c045034a031550719070024101034150341108041e85c00c0003c500e580e60501d030103803070f400400c2300b06e03480c2c41e60400400c003c903c1000340c0b1031941c81e6212100041d003010700074000750041c1400300e038100d6914211185003000c072405600990b8403851070200415500070600240081c00c03e42c0d07400e070b21000c8007a500192180c0d013004003100d00b0000098030100d100d880034403043d40101102c2d100030507903080a01c3c1150940b0944c9401a0043c0d0080040100076600003600705620300c0d0076054181d45080310f801081d40c80b00b06410003581e5200d407078280001e980b80081d60a818900030f10503078000a8446403081e40307a100580b80c000c039a0f41700c2d01000d000304120786503c00c03181e000c0c00d0001509400071307001c4260544044801c2e0556035034030a8035149550700b0036401d00b444000390f204c0080e482c06035543d0056200008401824080c06507001e6a265401043e02181d9820000c1c2141d990000952000307581358407400c42280114025000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 189634595 1250 189633345 189633347
    0x207060503100b0c0f010c170606071113090204150f051206060405070309050a05070303090f0810020c030912030406030f050112030309020a0b0a09080c0a0e0a0507020109020619030606 81
    0x292401840c2140000500c0c81c6840d42403042034004e03144461a80c0218800c0501801d02481040221f500c541c0711303001c8008041703208003907041005040f5800b410042061100085001000907020241150b16240c2064008820001407800ba00000d400610340b003202108107404e0143c0340122001c1d00034044d05035460320244481c42010612100700ca50011004c640d1500d4141c1103da07005030103240000da8801c00740c941600d0429000e00903101a04101e40610615510210080141004c01001c00b4603618044810f83e40f0554028001c00c0c075035002c10134030440d02e014001c03600c0d045001810030b8000c649014000d80c0303d900a00c03070b101c0407901d840e40d08050744000f4000e0504070f400501c8103180388150307510260701070210444101e9002c000f0000210305800020702809504c0c2c110381d102e40410741000c0742c180c640010b034904544101c3d401d403010400d44003042622640a00340401c0801d0f261034108084e80540134903407000b54008808250540b00c46042200036a0f87d901c90303078080c46000d6585d40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 189635845 1250 189634595 189634597
    0xf0905070509150109060327030e030f07060903030305060616050607020c03010b150903120307020703060e03070804031e060c0807180506030105040c02070b0301030f020a091514040e0d03050702070605 88
    0x203c2c0c50210303220610401040d40281d200880b03105140d03446581701b00d5860540d4040b1030f501030049010400e2800c4140c001c2c10200502c05103d00300038001c00030303941007060243c81c1056a03c03000382090744480025182d6200c10302034605d844540004500300f507074685401611000100e807030a00601c5948810007592505004204c0c6a060140c20400c0c09400641480c200740e00040c03807185c051040411421541c11940c0043d03200380f40960203003007114291b10300181501c0c0300400d0742c1141d030310a1000074041030072001198100e9500450103448000701034103903404002420f00103860341c1e103848400913070190088140392041045e0b540780d001c1c402286454000b0035500d8010b9a07002001880180964101540704141c0d40b4100d004480d15203070b41f0300104070b0302d520980003110041940141d100460a02d49003c2d009007440c4078080c80f140d0308015051007210038900c50204110300844866940d40c03243e40c0207100c909104001c0e1600e0108200028018090a0300c0400c0184248900010800d00c600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 189637095 1250 189635845 189635881
    0x60a06030c0311210d020d020105010e0630070303080105060c0706050309011436030a0e0a030b041407050609010c020613080303040c03030e0109081e010f0905070509 73
    0x903005075805042d61210100c019490f142c6607000020400455490104201c4640b0700360219001001d800c40c2c042002810000250714400075a810328006100c540311b1110b04d03540c070040548601c030781c1e243d60312901e00000039201d503002c1071850201100204020082005403e6900945481620741d9030380040c010148200c81c41030300c031604816000c0c400a0321800c004c2d60810701e03403c00424100300d0f074810042c400b50b058031a500c0103041c038400607940c8101080c00312602c1c15142001400324540c0c04815880b48580f483d40020001e5400d5800165030b00c45c203004c80034540080008909282c01c0c5081d421280946040d03140030b02c00c0a00c00255407600c1d9007100c0559038181d442c02281700240e424020b1907008040e072041c0d0a80d0a00d400700308450100042d510a41c0114182090280346044c003134040c0f01801121410080500000e100b182400a81c0c008400b0301000180701c0700700d203a4112801420520094002a0308201410041c4030b00080c08905a42d0300b00d40044c00d03030b10b40140c603e80c010056 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 189638345 1250 189637095 189637103
    0x30909010b090f0d24110c0715020d08040f050a0c090518030a0210090f0b040807060b0307030b011503290f04050112021212121609060818070b0a090305060a0603 71
    0x44118802e00503d81c4a40440c40205c00000b140740036809050b10416040000724140c281d12018040102a4900c0c0c02e280611038580041d00b512040204000c0940360010805888021848030030340400408001c002c0410b904107201840740e50311814010003501041d01d642c0458010280c40d0510403c01001320381d00484640c00030980c000807400f49401822003d04140d60030b2941c0100398021030030b03001c03500e03200d02c0c071a2515030303031300c0c0d61502d0608202e58656601c140039038002401131000070b4640424506550645411511840c001d003000c4014002501c12950200c032000282d0390b122a1a000c00e1640400403101c81c0000b6003000c0500c82220320912544500002891040001d820b1941c110350322101c00000b9100c10080d1268001e101d0340c010349074030340502e400d1003c1018002e010084122501500e1611014841c41c00c81c0c028180301e40641102100c02d101400b51140360001c01c000002403801c0d602990702c8240c200700180034180340d0721060300c0b907002d1940000c00d0300d051032096005070381d80 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 189639595 1250 189638345 189638363
    0x108040809060d092a270f0b09101202040b0316080d12020c030a031107120804170c06181501090203090105011502030f13030b1302131a0d05030909010b090f0d 70
    0x80c140201c248a40341048400c51440686900141246c1900900b100104038840c0440e14200d48402d20440c4440206040240c05002000f80250700342c116420f42000e40440703000c240c440c82e000009003413008003c12022111002c2d0800903849402045982101745035403902c051034240960100306034418542c1000c0f06400c00c2110140c514025403040d00c042c000c139101e50341400040c1e50342d80900c008030480070000c07071440010001000250030700b00c440d0030141403400307062080b408a000e0f540c6801a01484c00119101d20900c2c1850f0100040484094114991134403542d4a0580e00c00039401514a9a11035084c400041040b500c403032044c0c8044442d0303500071071070304098041610b01500710068001c80140030403000804907001e1034505000e14070307541d11425000584e10400c00070070b08041c5c1800e0307034034207001854000d290701ea100104884410350b2034100c0400c0300d1a01c2030952084a00f1903901469040020408080280142040e110162400302c07014118504012010540e807800a1030144 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 189640845 1250 189639595 189639599
    0x30c08041401110f03150604050f01030e0102091809010f050910020c0118051506090720030c031209010507141b0a12120b09150108040809060d092a 65
    0xc00003000c10041c80d008000152801245041500c0d07507103c085a024039040210600c0700011865842d210078a5048520503d05468072000ca1105155802d516051640d1f44054003078000302901241c81a480003040515038030b00d1200d00006090090b14400c0c225842c2038804c06108500b442424096403c0c1002441c0318000029901d02039840400303000c0c019500c0321900c290b0b112000186c21900ea200c0d5000d0643c00b582880d00403240e100041c03060384100c07494000d1121042c0c00004103440300201c941104a1008411420b910750700c00c419001d000c1d80320029540c0d10809240000341c1c080c1821400901c1562500002165841d8518030528500c14042001c40b150071a104007400c042082601a20903082d09500c0b070511800110f21004003051500c030020000300c14621a03440c10340c104454190207030800c0c1c0444000b0a0345440d41c6414840400081018800500c041c0c44c202301004008075620414200c1791000b402e62031100f102d00d060202c404120000640c030301c03080c0102809810000e018 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 189642095 1250 189640845 189640853
    0x1205010302090115020109050706051c0501060e150708031021020609090604150b0318011a0906150304050a0c060c03170c0c0703110f0607030e010818010e060a0507030c0804 76
    0x3201d130f6101142950b60303030801306001072001c1c010a00144016202c654540229550300d800700112031070070038051071030071005208554000e65041d07100c4005a40744022060003080110651290032800740c04690080100903d491a003142035060741d0005030181d000c4c0d0600e545018281562900c002d40c072074403e00109856052210701c569104100a0000c0758034080c02c10801c410342d885402c403008400c000004c2201d000401e10340c03000302c0c003000700003001000c40d408a40d01d0780d100c0711a03100380305020040204481e07070798040200c940c100310328402d541c1d64185494440d5a50b0407548040752195210a00014043d008444541038190035840b03074558400000001000f0190092040307100c0c00c0d0038043c030030380c80c50100412800340d4402c0481640850000c41080b1000d6003890701c451003001b04200d0800020780c01048451400b20a080c0304445446243c50007090300000e00500c142d540c03810703103141684000000c06a01a4110203420001521030701400c5041d01c050b10702900c040343c48000828001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 189643345 1250 189642095 189642119
    0x616030e0d0f0e04061511060112030e06071b090606081003110d0501020d0e030903061f060302090d0f031725050304021c05060108060a14010501051b070b04030312050103020901 78
    0x24000308002466604e80092040c10b2000660b1b0100140648016000b1001c003007101038090603030030040600c5283d003503400030903105141c007820b03021b0080030841c1c000700052072054828444144001c3c800d00d5494081c40001040244104800a0705980210b4680d030b1340302c1461000d8035001021054810318580501000506080f002c0302c541d9404c22204085080a100c0ea00d1041003a4002d9690b41781c00404161070003401405100d21001000520f82c0004809018101194034030304015071550230310030006030502034604025011070741d10b4042c6c1003010341c05200c1c0c10790f080e020301e142a10780e1200740c080c240d00111400f1034200e1843c0741410a00b0207021704041c583c070510051000c0003031a030258556100d2038480404030341d550301c0390300144008881440b100da40510f480604120303c40d0042c0003660503440600c1141d05002d800682c061088121842c105a5000708000310f43c0c040b41d6030824440346600c98401500000c20900070040743c1800c60055034126038008002140c21f908245098030f079 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 189644595 1250 189643345 189643367
    0xe0609011101050a06031505070206070f02010908191205060a05010c02030a2001090902070b13030c02030109080c0f030c0604031b15060501031404020d030e120616030e0d0f 76
    0x41c0300c0c68811150030380030240110741c4180700510001c00ca051031450040c6250104c08103400c007084c01c100c10841e00660008146a1009083c6480d01580b00c4110b0140d0045c0507104000d000b0f000e00084012484504030000800c000060350303441d82c02400040d220b07044400698640c0c1e4042d400d4a8200100c0d0321442d01a02c0c40d50004054401220103a9904172400280c81e1000d0300b807055000c3d0001d195a00240c1e03190041480400135850541c01d995039403154240244400144404441c0c0c090034036208410010dc6030b40d01400070081c0010034100482e0710f801080c805240d5100780000103007000d07404815150541003240042856440c2c0396800d8401409140580e030075114174040b8000418110301031144500d1400a00141180c20300e030005003034030b448140b0a460252418244401030715201b101882c0030b501881c06900020301d5000040021021258910161240c0c43c24865940c2c1610074664403104203890400c11542c200441503103412002481d00d02007a0f100d0002070205004d0076090341 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 189645845 1250 189644595 189644597
    0x30813080c031507030213090615320c15250512090321010510030e0616020f0102070605090709090c1e03020a0311120f10180f0807210e060901 63
    0x2c02d245001e01a0000301c80d4560001e07840710b40741c4d00100010405450954050310741490500450b241c07950400c07103040d00b0307001c0d154bd10b00706010340c0d58079004800040c1c4030b031140d65001340c1b0007104801c02655400c0c0e40c207989100860b2841f10341301d01c0d41582d03500c1d41e500c109140d8507040c3c107200540e1400c49010000800c100c58a000400c4061b041d4170141c0034001d415a03e03150301450b1541081d040c004410b107084040c0b0285071030140000d00c40040064201c0e40700201d554041d0790140c410f20101d040a1181d072a00c1d02a40c0086075a808001a40d0840c81c422102c2c2800c6079100c60741c80700031005481c0000d80207010b4403012002800a0710310503101c03100f110411852031403e95500ea000c6110f11156520546101d440310140001c9490101c010350700d9003101000800c2400244c00b078540d11852030100700c0c50100d0f030314043d1451400c0d181030200d2442d9044001c09103112242d0034035000030b40c0503c50444040038004211620841c096402c0d21040c801c9640b101c040344c5036a001c1c080710b41c0c400c1e03048034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 189647095 1250 189645845 189645847
    0x207060905070f031509030e0f0a0f0b0405150a0e100e090414011802010509010e0d0203070905160503040302060105090c1201060210110c030703032004030813080c0315070302 77
    0x110204000b00324860040120182d1140110301c0c5080c0403c00c08004003200ba50a804c20f101d16000c41e500c81400c403404001151061900380341400015031014440c0d108480320b000f009000103030440b920303014208440e01650310b007001d168070303401418581c0700fa9031040307020038070b410540449800d052031110400007050030314000006d1107000080d9212401c42e0708403020441c0c04240304d0070a00038005d04104004410a2100c0da0301a540040c145002c4e00303083c981080140d03d144c80702c650712000180f1400c0c0c1c0150a480d11a9155a4843c000d804201c0e8010701494407a180400100d00c01e0040341d100b0358140e8040c1c166030f400c0002b005210300000e13101c1100014180008c1d22142d000c200c410303008003000e800034240f00c0c1ca10001142a103102400f011440715041c000a20002004801c032840c43c0d52600d000501c400a603441c14045640000c0075071109100030130701000300141c5000410f00085407083d03a0911580e11021190f80b5040100c00e550950807100c00784556030010140d00750040c40c541005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 189648345 1250 189647095 189647111
    0xf1b05040513150b07031209120314060102120c0a06020f09010807052d0702040f05010e0c070309140d05150103020103051012030c02010516080d110a02120c070b0409050f0702010b0f04020706 84
    0x40c40503a02da0a4094a02701d10323182c032005090b0340600c105001d83c07404e0b5525070480e00d01080040e41702c1e46100c115003064440051403041556007800300c0d05400746e104504546800101c0b2060103d90001084180402c6503540030503006070182d0241c45180007051180f074620034114445580c00344000d01010886401400b0003001030f642d83c0960301988882c103030b0006056140038092400f6840250aa1503007a00800031107020075400024202680d9101140080a40900c400b08800b90303c152005095801440746005168070b15488690480c0e000341d030284001c0c0c0b2000701d40304000580340304108400a401c203102c1c001a008540c04010f50340141800c0d070824266000c141203600d403400703045444c06000500010341400521418011143c1b40c4881802e00e00d0070070000c6d59803880301c080c031031890f1004a81991140701c10400040585540503c0a03251a910380d24a0040e21040d20304414894080c800580c002e4414890302d009000001c000c040c00c3e1174a0000e0000941c40220300752203054545101e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 189649595 1250 189648345 189648377
    0xd030e0301020d1103042003101e060314060a11070f150501060327050c09090709140105120a020f010c11030303010b0c0f0a020904060f1b05040513150b0703 69
    0x40300d2042043c40071042d0341c3d207094034000c001d90041d02d41c0b008016040c905252503c8c0c40004030181c01e01d5000d00001200105089509036001c03550703500c6c0d0050307070900b070003c000c000c150f02c2020101c1c200d460881e045600c40c4d02c0003c064440c0302080000442d028840796001c00d010780380b00103406003d00d030142d800702d190300e02d52410b6031800d0f041840865120100c01404140083c1145100307100b0f0000703955220300b16510035881d105004071f80e520503070003040403a0a0b55028010b1800405410b10100020800046000c01d040000d02c107003440307070002d10301c0c900c041030003c2105649030358010b0800140048110055580d050328030020345901c51482203840098a08100550203001e070340c20110703201d0601000c510720300361503000503460070340003004203400584078a90398a41150348120045480d102d248150401840f0b014442d010380004007111400a0360420000d00c195102910358030100740031080b822050302d072010b9a5010046944504100c0c100f41007000d0441c09200749807660444581400c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 189650845 1250 189649595 189649601
    0x8032106010c141b040e030405010c02130f05100b0a0e010f120501090603020f030d140d0209030a030f1d0d0f0318030305040e0105040507080a050907180f18020d030e0301020d 77
    0x7a1181c0c4a50188209440c1040400716540c0001001c0302c052000740300b80c1207047e03180d000300e00c00c86040c00600900d010455695544600442141c03020030001d40380d052020b0743c060a000e8400916030b420318240400c01a81400c00c84041707889540f911300210388408011540d1422109500c0b08010221507080d04684e02401294028030800001082550850040098980318402c1c064800da104541c1070101c0f54201503003007000344400340c519840715440d01c20040a841b52030031540d8540949105081016044100804604c015503503031001170030b80f4001d05124440c070415642d408110071080000080c0c1500c0158101403091030314001c080f495582007000c4c0c1c901c60300308030046200820284581d8094420841c0100800c0710180800d00303200e072000d06200e5000c4d040405841d142c00c0010308400c410030035480184060444e1314220b50b42600132000400080c03061080c424113050150803008e140300c000400d81078004002642014650b0340079200b040c0d85010780d94041d5020300c900140448584 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 189652095 1250 189650845 189650873
    0x1030c0e0910080a080c07050103140a050403030b15190e0114130b040e1f03020d031d0a2c040804060c050f030708040510080f060f0d0807030207030b0108032106010c 73
    0x40c0740c840d06c8801d0782070198108106130b00b1290426152903054411900c1118505801250855000689440300c0c2005c4000e0300c0d14172807040d041020401c8050141011000902c1d00d88403030401610701c001142030480300e50441c641024002000707180344100320300642000b882e010b640c5c5407020040035a01c0301600c4254000d9030284040d4860002044070202c103203036640c0d90300350309031f41d2040980b42180d0000d4107003401510007508001c441c1036446600d4034148207003e9a00c0000300f10643d281d546a0030141c0080e2400c09080944146070025903072000b0035003819005560028005052608020040700c04c1d81d01040c05490b079100c0e880898400600920040c041e1700d011700101d0780d0341c900b010140517003c05040202d0040110440401910003007442c2c6250300404202e40f840c0828881e48001400003051040c00b40c124440060a40105a0005031981c112407041180782030580e652a005500c90180c00d1002d046004a420700800282c0c54080d003540c04041414001c1d9108115101d50307032034040742 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 189653345 1250 189652095 189652103
    0x170910230114120d1b0501090c1e050607020a030204110d0c021e15150604081203150607051009030309050d0f021e070b0a091205060604060501030c0e0910080a 70
    0x400c00c0b05030500301910014000c0e003003800200520502c1c014014501c0003000c1c030340c20000c01445130080800c80d017034000300c00690300080202030349900c41d52900d5802030b00e400503641186101c0000122400c2c400d09480c0a26001840340f034080d4610303024032001d4140700286488000702080208c0440300c561240c030748125881d030b00501c001c190b0006445c4550218031848040e070391200005050301c9060381c5a0f164030075040d03010600384480040214080d40900c1d00400385031b0060000c01c04010b0709800c05984101a00407604824030340b11000c0c082d09100d1361030040c1803500801c1c0080c08100143e00001801840b030f1038009810056a1070b082d080140c5c140303900f00047c00e0230801c454515410403541800d04032814507a020310310300f8045295103e1413442284825000400c401107010300174100b00c0000c0c492400c08210316000d620300240c451000302d4003d07100703524002010445500c00e01c100d10003240e141d210880e4108905041000c003c0c802003074802c03c0081ca400200d0b9805050001c1e21000c1d100d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 189654595 1250 189653345 189653369
    0x20a17011805070504120f0c0b0a08040c0501050901080406050c040e1303020106050312040e0a0f020c210313140f0d0207060905090606040605161a0105011709102301 73
    0x16040c004001e851000e4070f0001000b405020034807010200b10700040e001580030700ba81203990403610308010f0001d000d0f03218070f40b6180041001c070038503508016210320481c4280880351580c0d4560006603035a0081d095118006080c0c40c000500140e8154807880d04800d00b890f905042680d144140c50001008640c003e1800e030420694104247d024003d28000d49001c8001d0402d07250307070050707002060166101d40301c0307a140d00d031011888060301d552280c0c0c101b0200e858290b5517105c4e10141b15076296500e00d0505914404584100399121120040d240100410101d6103180d040302e407142d2940400801c0d075444540650000000d000c8810000320b200d209803030b00030341030303851070184048c0c10380a0b55400203025442c014108170721070740d895040707900743d4440341080c503220700080c00754007801040894001c0515050680840044d1004c800c400d040311030982e20011141204074048800d100155004000f030b40c005034002c140d1480503002007000940683d16280d11901c4251f500c2d0b16100d003a800306006c217603 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 189655845 1250 189654595 189654629
    0x801020f0a120902011b02060702150a02070605040506031b22090e010b030309010f090b04120605060105070507091e020d0504050106060f0507020409031704061a0114030a020a1701 79
    0x74005030000b48664850004002500b05500080d24003100c00d0f2002c0d50200c0b02c0d8940e00308541e05d1105407401c203034020300b07916050b0041c0d030483e030030940c84420180050f00c40c922000070f22034411001c440584901601240c11902d0b000d040702e040c041d604030003684070030060090200003605600781c4034400440b060725800d2149406c2100044404405401207541d0404040341807a8400004031a20002c00b8a410301081840410843c2d850590b07401011031340b400082c1c0010501910765000300514040c00e000c21151b00e030600199403600c541074000b0015008600200240c4e80c0c65848090f095100e100760b9003251910900c040120b80c02404850040d03940c46060200b40700c024070500010b07210f80e01307140240c80d03940c8101900501542000074403803912411081d08052242d50342c42010050304460300220b0400786464030103400703c002c010040038400c0c1e0003068158420b181407034810130604021031840e142c000f03580c006540024081c5040c02241a841c4030030f14080e441c014002c101201c0a069004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 189657095 1250 189655845 189655847
    0x60927060a1703070b09151806070314040311010b040e1605010507021809031603030207050c030d0c080d09020d05060a0b06190807030e0318090109060602031c060801020f0a 76
    0x10009400104a81000551480c0e180c280001113030003281c0c010301c0c500f001d0b603101002c0b6481c00e41c0c84800782c001c440c034000a000d0780c081c911410030268940c150542c2c80542d03400400304c0407151448601e0141440c41004140840d00600e112035071a060301d00042450030b41c01e00031609462015681414641c0450001c020030074a00d4040e9000d00b030246131542c50039003e600002c0080d0f0141050550240461b0b000c04c00d0341500704104c0329030780200d041c0c40301d40c01c0c0b0900b8040c2c000d400c48103082c1c0751801001013000c01d505c2c004c5101c8480ca41c890301c604248201c9500c4d00c040541092807403d150643da43e1402c130140e036408a0341c0540d81c0c45031004141c1464441c80010a40b41c54013400e40c0180410300000c0b100d0404024901440d02c00f07171420588507981d00c50b0860242030841602d06c00c5000029451410324040c00c0c1400c1c0c0000c0503503078081103907030799100441200d91034810100140c10600c40145406910444400c8102c101030012840f5900c81260f1801c9030701501803641040f8000950741929 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 189658345 1250 189657095 189657109
    0x503060a050c0703050c070503060705090906010905092715010303110c01050d0207081c15080309130510090606030c080618040206030c0708070503030601030b06040f0506092706 78
    0xa0404818070075401d001880d0945030161110040501030045030002001c2801c02503c1c0003000c000741241d20300c0c01c0001c0d02900710303441120f055001384100d2002074602d50003000781108a03280078003051a6a0350706440100c01881c030540306c0820045000c0221a000004c211443d42000c040f000d00341c195140d40f9014019621b1107040b40500e400035140b5610070ba070000259040d000300040c025070f90300000d20700140303170f446500c0c1d10107032074103500c4200d04500506600440c1c040300d250b011510050380300d4008660b00d00071898807503800407118a40d08640f0240303800c03207500b00400e040fa2040107600c80414106a40c0c55410000022381d441d40c0a9211075070062109410082c15036608404a900d981e0304141c0c10300041020740241c1c0c0000c04505c1401d003c5044403000b031703000240f40e601ca410528016443c4c3d80140e8900303000904042c2810f2903403405404075800c40d6030b240740c0d422420340350070705200464010403565680000c0d03d2980d10faa450f000b2820344615280c40c120411940350031b000304120 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 189659595 1250 189658345 189658351
    0x2106311b0617041b050402160201030e031c0906021204060905010b0f0603072d05040801060f21080d0501120c06090b0d0e0307060e1e01090209010e0601032004050306 73
    0x10050904031034810200c0ca440e406400a8000b1000300002d8100c040e44c8000940344c1c0d000a410502c0080d00e6114155904a9640303442c0c400d82c0c0c244010340b400000c1d80e41c0c0e40030300a84200ca4580001c00c00030a006503034860101c1c144910009810700b810304d9044001e8540c200da0a0310b0140d02e0b06604d108106003072103a00b0644c1d104442011040080b440850007a0200820300c0050140801c1c0255060780140d41943e011342c0e042400e0745001e91030720340041c800d41062058403181d6003000ca0101e00c2c0001b42080d00c05403840716501212101000201c8070806540360030503100d0a800700141c0038440c005002e424017901c3c03008082688400186400701d10300010780d001d401040040c0c2c40501519140c00100e40440a05140200d55511010601403d44c030036090b005040520340806d410200d88080307035114000b070303003581038428605014040b6070130703030728a2100258807281000041c40905116400c160300141c041c90001801d00000c52072030744040394403c00c60800c05012800304001d2600f007040382e034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 189660845 1250 189659595 189659597
    0xb0a18030804060510080d030f050612030f03040c031a06010e01020114130203190506160912020112021e0315030c0307030803072303062106311b06 65
    0x12015510020001040580020300003600c0d08081280c0a02e00c541d000c0c060441c1605403145500c00d038070081c009140d80b11305403145d2410700f00000c1c803502d4051082ea6403146043d001c0d61504800ea5560011540014821950107248560200100d502d000022100c50340c103103510206828000005030481c0d01105c1a2411a03040100c040341c88809245016007001086252000c1e0a034a8800a81803200f02c555122425002403202e42c144000000c0346402041102020004444000000c95940c0d200c0d01031515150003048000005500c100f00110a06491078001070038600d44050788110203102c11001e0704020000720070300c641c1d2000011940c0c42000300320000c01e07188c103443c1d001ca0746405075031001401c409800b000080f40035006140c501c99282501e007140e406200c03840d80300ca440c3d81069444074010030b901d140c4844007401013007503c651803103280e004100940d19143c0c1c410003444408680380f40c1025003c0001d442d507040309480c9400c2072241c00b0f18200b02e2601c05001c088003040e548160 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 189662095 1250 189660845 189660881
    0x30506030307020a15050708071b0503030f0307140c0f0d03111201030b0a0207020a060908060112081e090a030303020301030b0921130e1302040e0706020c0f0409050a0b0a 75
    0x80142d44800218007205e40c03220b04031041c068040800d840a01600c076001e0300c450f4000609100700490010724011159008000307807046a21070050599900070141c07a0008800200f020450041c05410000207404d004540d05180c80c48007072030030b030800004540502003039009104d8802407a4242c0103445030303c8a20a406801c05800011500c0001410311024220301c689001240ba00440d03501211221034000c1d044a0190341c0c0c6410040441005108018190084100108070b405510b02841c407465040400d040c24040320018600716050b0a258212044208021640c1940c543e001500300a600945006841e50b01d90300705200d00f804001e002c0301c0b8a80200b41c0d541030b800101d800c46c034050f01c0b6250601d80c0b1802c00141126003200310b80c1111540100080c200650000854101c1c80000e01c01d07141840707a01e071000e00b100d980c0c80d100c1c02040c000da0460711041c922400c0161125044102c010004540314082d034403240d041201c1c10100b13076010310400040040c50200d81c0612128080038a90030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 189663345 1250 189662095 189662107
    0xc09020d05010b130306020d0f02071406011a07020120010608010e060c07030206010e100e0f1603200a020a0b0903090a0803040b0f0c0109060f2f04091e021303030305060303 76
    0x111103048600000301251f0f400326181403408155131040c802240302c024110741d100700074240b05c0d03114400d10b0407100740c6200d48400419841440c0c6114108010b00030000c86c2440095801900c1146505500c0d00108004481841c01030209001b00c400811191000151041c841d414541c1808001002680104800c000078000240e00140c06411600b4121200f5415203034070841c110070030345607800b02e40030b142160705000211003087d00b824003440341249440b50000c54040e081d81500c9035007503c0004a85c00b42811040f40801d44020406145284180c0d46649650350312608041000e40c0c813102e9a5201151030b07002070034140414405806140f000f58201403510517208082d20070041c41c01142c0c80080303441d0264013025000f048220b40c5c8042d00f0b0040f1041c05108800810441d401c03159000b58040c0c690401031030005850044524100e00c0c00d00d01410940b03250041c1030071901c0c1c20f9841c40451503030f070100758080c03018084482800b030100c80018518140141541c10140c401c5120350802c01078 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 189664595 1250 189663345 189663367
    0x909060e04020a03030f1b15270b1518010303180308030a0908071e110a0605160203030403023304080604060c0909090303020408060708090312130c09020d05010b 71
    0x3c04104c1c1e9041c81c2c0045500d0705050304540100c8085c003628a05034080c1d8201c010814001c1c0b00e0500c1202484007000f25075041d2500c1d10b054160352140040d085503041810012074020080507034000214491500d5200c00000403411182e003001e40780a2042c44003005104055218071440e00e900c2121401e44021030458507004400c1c030010b03080d9940140d6030550103040011110540c0d4040e80c100b0084001c810100b16501d04901926030b0032140c100301c0f507017040b006240c00d22004007901e02543d110307400c0120b1220005c03400c4034a0901a80e02d44800d000020050347da5841304400d8595061100c14260743e500a2002e90400c01c94031a0085c0c2d809001c18030030010300160003a40706070002d0011410800d1503e080d0380765152070300307c0030459051081003014150950000c00c1220400c408503001a43d600c181286d5528041d9500007a6030010045400504034500083d03812945502010010321610382e2440c0584c0d0700365203c0e484140e00400c4010480034280700e4180104a4403640516181020384 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 189665845 1250 189664595 189664609
    0x306090f0c0409180803010e0a0c02011a04050406090b1017070302090609070915180504050705070818033a0909020a030b03070f0e0a020702060d02030603030c0a030909060e0402 78
    0xf8501c405507030307612004503060020700070240f480d42040301d6503500d5031101c205040e250022200980180c5c02c6c00e4240b1000740c0b0500c01d80c010901c020b8410950403c1c01c80c1004081c01d009401038034817030f4886030300c00007192115440c107006052192000c01c03601e251001e021141c4840fa07180b41d002e60801c500400c0035844407900d003a4480300c2240c070702c000c540d5441015074028900742c0180041500c86168a01042d03042a00019060b40d180102d130442659041040103441c42100e02c0c40005609101e0074000032003241c0a001c040202000741d01c448101c29000c24134102c01110004610502291200c1c002d10b50f02c4d00da2103040c1c0008440c040300d6005110080c090110520410020a5001a82001462181d4000c41e01584010140c5904640c0c0c0c5a807254001810f000b1200d86490000200b9135442041c07003110509640980200d04084034102110004c2d000208115018041000040d0400c0000d10140c545a4443d4440218040c144207030141281e18540110b503c8204038000e00000d0f0383c07018 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 189667095 1250 189665845 189665849
    0x8060907050304060e010e010b03102702150705010507110309010906110a0b0f09060708070e060703170708011a04080619090203030714060a02040b090d03020102090a03080306090f0c04 81
    0x41400742c1d482d00d031490080001d10140d200b43c049035103010141c5400c42e00640040241d03140c100c04407035086281007400d604803503000065500e90b40382458502c1d08a040e4111070101940010103114081c845c1e02128192607101110844245c2d64a608204403550000d0000500080b00401941840795110003c0d0020490740a14010300c0100c046402c2c1c0801c081001111495102d2241890350800a000d41058002594400c01600481c00003501291042d003807203100f2000303942c0fa00d42080c1c510341403090b82c0c0e003c2e45094080001c110040da69401207070140d035008280c90398954410358504942da00ca00c3c0c461001c40301080f0002c1200b0032058a001845d180c1080c11100c1c8941080d24420b580401000440c500941500003c204d440174082c22083c6c4915446211050781e4680d642c40481102f20b120724083c141c030b2500c040c40701c0119410b10b0301016604d64481e000041c50108402e0001e44032540c140e01c00c40c0c8006000040100e01c0c1840003101c1e030005080d0f10a2412401c080124540a004174 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 189668345 1250 189667095 189667097
    0x901021504020f060705030918040c03030c0201170106020309010e031b22110a020c041e0c11100605040e0105010e01030b0411090a020405211213081e0d08060907 71
    0x103801103002d5540d050706030204100020039190b40c3d030040c1c2c83c0c00340e1a90818103801d8480c10303140d01c890000c040e003400010b20650780040413120803070031603070309070303800c451516090b410820841d8400703502c010514800341c06840190011922540500001045640620f00c003900030340003198821200700000300ba079141c03050215000202e1068414620024081e107044a503045030500080691000c603110092003000003950a865501b1041c0083c44182c030546a203c2d05444080c070300001e01821954410314540611745131a550916242c200395141c0b0007021a40d880c1c403540c80000300014605071244c80c014400403c000d2080b076140900c9402d23160f40511010302140b0039000050100031410070070319001c0900500d045032a0910740318070760003500580030b500e000300c035035a4500d40c4086002c6402c1031030310304403c01000b002003211140c010a030001070000b8603003071040c0750102d19a42c083c040329a0424400100925980513074002c545410604468078052100342c07030a001180c1c0381c000c81c60fa072103042 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 189669595 1250 189668345 189668383
    0x90d02011a0f010203090a1203080a05010b09120a02100503070320040501200307030302090405091c030b01020109020a1d0601140403031d0607060905070b0a0c0605130c09050615090102 81
    0x2100140e09501c110f0004691247e01641701203402812049140b200340e00960341d106980e514501c0242c03c0f03400030302a60046030400d2002c1220740c0340103014040182e52500585140a610f9404036411803016024800892408030810501d1070b4144a44266046840703d007900c1c045200c40c803011244514013560341002034000040800022528030760b46941d40d03100442c2e80e502000d06004000790444160644030341e040c1000705912100005004d506881515030582071704240303036801da00405c01d0551050565480d0059000036940e070f00c592100404807207051411000c081d10300303a06680402071031241400139120b0100500c100075030945003501c0c0d060034020b80c04d483c420035220005407182903103035204000094410801c00180c020241341440741040b01e4150351a59400100c6005418008001411030710780c01c2c02141190308019013005110350107505542403a202c1031844e141c9a00280380e020f486105001c141d040060540c031540c0120b045040c14146003000003034848035441d6070b140c80100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 189670845 1250 189669595 189669619
    0xd03060501090b0306010309231b031f180b04260d0509010f060305030a090b0f0711210f2104090b040b04020408010c090f050a050d05190308090d02011a 67
    0x4000e5000404043e040000034203110049d80e50f0100040c1d8070036440c11240a030645003491039503a10024102010021b014082c20650150007410800768180201c402030f407202c4842158104601100078410b000d610300700420700c0d00c0d0034101c60001f0003021800000390700714040020f17041d40000341c51700c1c2040d1032004503584e00c4040085016080f08407214030601e00d084400010445d0010080c10150b20948a00c4041c43c0d503210001e090780034a004203e40d0080403c05c280c0000e5107804401c0c15200028041101a455441e8124880d4020201d2000a900c9414001048001049144901c000c0003015141024480c80354860340c0c01184030360880b10340c64040d5040c803581e4035000300c140d48a02510841d141c81c2d50b541e2850191821400b80ca0200e049a0b40203c1c180c1e04100c40601511009003011300ca482c81c00707050064406031210180c42501519030703100c9002000446107500c2d64000c2da200d0389030f818101c0c0c1803414a0380d80700f41072056a01d45448001c02c8589070f140c02450b02012106190040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 189672095 1250 189670845 189670847
    0x71e05160609080d080c040504092423060d060504021c060c030e0303160c081314041404030914060d05010b0a020d05070c0b070c0e09060403020d03060501090b030601 73
    0x28044904a03480356020010400c0c03a4421207a03821620450203d61041105000942c1d09210a449008402070304000900c95401e03c0c0c0c00800c5800d114804005c181e414404060442d0049040820340c241d489220412582403502c040101040b101c0707944d0000f906040c03000031194044442e0081c00141c035100000c0666a07808281001d41d00c12044100c3c401e84280b512400502c60104100d0100f4030b44a0a012100c5000055a03c01c04420340401113200981c0d00650741c0d02c14054045540c40343c01c0004809446802c900b0200400300051519402c4800e042084180c584c17100000b40c13010200e004000110350301c1300858086039103240c2e808540c04066004501c113840303225020120582441c0000a10f10030740d800400d003403400e90b400d417290164400c1c0103c8070f61007280000f07070101622600030b00c41c1813442d41c01003140d03d1041820400d010350311240d003e1514812107051510f900300c1c00030002810703014004040c0c070b445281380400090341801d0021340412403500808030301c02c5011000540903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 189673345 1250 189672095 189672103
    0xa02190e07081b030f1801090f1b0b0f1305040c051902011d07080d0503040b0411130c05030a051807180e010905070f08060c031f0302060a03061a071e05 67
    0x294001d0018269213141510492010307a00640303104064140c10b442c1d400106c00180700f5080400c0c2c0c010344005600070941c4130700101d6052404c40b11070900540b1000030705c4020f6040103091a012008010382c5480b90100c9010b4a0301050788514000d0b81000d1807000d00503405022120300680301045100b032494020412801001d0500d100141d40c0e5913000469221600010310000711480e08048400207018003104550500065400410789110708000c5400111205160050810b000d03144502c40303900c541880007a60107408802c00440ea000042c48170002980c00391640c459907800b03920301405800c03a0550790310030041c4280a02d0302381140e02080c41c505c0c90342110302c0140c0ba20009203c8440a810001d89540c02c621402000441551001450314001301d480d034410403140b0443c0e03096035149881c1700b422100d0700d20b000400c2c2c40b0744d00022005070b403120090b141403d0660350028015042101700015407548442200b400407050054000144100b590020625480713084010032440380e243c120f00d4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 189674595 1250 189673345 189673381
    0x1b050106150e0406050406031a18120a1b030906030f060b0d0608100c020c040513050a030503010f1a04050d030903050a03020c040b040504050601270e0a02190e0708 72
    0x4150078044000e02080e840088410705103030885080010b035680b80100412913050b84001400358421100b41e100301c00c109e40e68203501416a81002c20380f03000600120741414548541203803841c031701081d54003003194010103090000251040d80c4100010a4601401e20708161040e48105625001160f0009842d0b0700400001c000c080c1e982519203c058802c9409003070a4003400c1500d01c80d0340c4070324076000707a1030103034000446154010700f500c09a914103201c0070308402041d10030280d254034020710029030b081100d042050302035594a51654101000100500280d500640f01504022440703000c0643c080100d0342282c0c0300301c0ba80c100c0c000315450159100c171501d82c0098484c1c05501c002806140d00411106529401110708100c42e01c555010481112400d8038058002c0c1c2c4404c0c01802090105407074005065000c004500c45d00f02c603034460340d040c1c0e5070740f8a14030b405401c1840c2030300441c01c00e00e98001c0c0c0005000507520915003000790b10301003d4001400d180c200700038080421140b014010340c90380 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 189675845 1250 189674595 189674609
    0x7030c12020c121b0114040b0c07020f1e0a05010903020312030601021f0b0103141512011b0903050c1f0c02060f1813020f070b191d0d0504061b050106 66
    0xa00d42440000c00b0305031019001c407940965090141700c0c6503d014415029100b168090b012000b235440f40198080d550304840b0080340c2196003180d04100941e40c2c4101580e00300c01c4c0e407031080040e1200340d0070700441c3c4405a01045c10302464050910050b603011540c81c1c0001c00e100c07402c0d52640e991500413031400c0b0b1f1300046180c250301036036409071140c0055048003100c1c413001c1e00d0500070004c144001da052410206e8a1185150003400649002e03e0070343c0048801b60910000400d012084204443c6466200c00c07001010881101c0c6c2002080418840b09031080d1040300c4d042c03417600c0c14046075107565003083d03280b004008905200c401159102c40660702c004082e40c8415071510b859011200142e8060345009200d005104800c443c0c0c19014022108645a1180c020341044000d41d07441600c1c640c00750408421714400a64903800d5080c9100e0760802400d416800d080f480e8200955a081901c441002010080700304002d2010940250306014898901110540e1010300d5040c254010680c58200344 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 189677095 1250 189675845 189675847
    0x190b0403080c070b040b09060307030f051006080a05073906240302100c0201090b03161205060904020f0102100c090501090f05090406020c030d050103050d030507030c12020c12 77
    0x1005201c03425020785101e500e07400841d624241c4595a5000740c3c0a00e20800c070611004101250842c00d050740130b103030000407600b03011900d0700c55800c0b601c090b101c00f1100350051001c5002c04104035641320003540d4000a981d10208094201008018421031800081a10b55602021072201820f490303161030402d112030040c03a0300c40500034541040136000c900b2a821184420802050040d04640301031310490364020031006001251071406d485031505404141c0c1404a00c4034006240c440078401944145110b9041c0b46010780f0400780034164840d00c10300540e5052404081040c640c44006e012a0400c0c0c04039007101420048100403881c209051070300ea49694144400989860b42203002c240699000340c0b04d0290746a10f40e126541041068442e02d58004003000205001c20300d241e009010010400060f203240055001190301a1002a4000c030382075844101c4134820780d91705107d00e41c0c001d00145010701c0551062a001005404000440a0400c0c2d0014012960010401103110807860002c0c0346 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 189678345 1250 189677095 189677099
    0x4090903020303011706070f0e030109060911010221040504050c1c0912020f060c03042a1d0c09010305060f190509090c090711010605060301120204060b0414190b04 72
    0x3526604203111381e0700403a02c502e260000030040446c0c1c040c49a40c0340c0e43c565208080d4250102c03011040d040030607816550341c982850203d45280074042d00e890160079100107480104000a20b4540c40071310b00902d03984018514013030805842d04a81c1102c034115408121900d491907403404901c00c8043d15146251440c3c01913160420341c4c1c00200c94180198085101704980410980e01d9a042c6042c001d269008100040d505c8820000a035400078008c14100320406440c3c20a015948031880c2c1c2454000da01c1141003040700800e41003542e080b0401c4803406841d00305445c8103440d070b0041c4c503400f40c1416107500001c0c3c0c007525000c24007020058014422031030050b51025181c4e4052840c00383c1400740c000c2400040b5000e80c005155458500080c0404c0826960103600f01c4000700c814510160340e54880708000b8450b580e8902841c040c281c040d240209500103441040100d4600d94801c0f421214140001c04c0034000c1c00c41500175004042e81c021075559200e4600001d000119000301442420201340 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 189679595 1250 189678345 189678347
    0xa0201021312050c0411040603051506040303090f050303090a1401031b031406040b031c050d050c0415021506150702041805061b0f070303020d09060b01030c0801180e0304090903 78
    0x18100a4078010f006842840840310140001d40e1104a60341c0244d9904200410482c0d00c264070641c2d0007052501c09c50800d030303c09000501c441d4060750059000405940303003804180c1e10720300c1c8a80203140c101c0045240111f590041840108103100e81d0344824031003140c050099020740c008540046500030420704011200c7c0307002d001083c1400c6060282c440d14000122030f81010711408141110080040145584c03c002c000d480303245004030001000000c0c01075050380e0000c0d004060003030154000300e58940341041c2c003221302d0f94094041e83c0219070180d401c2e01030100c901810180c0280c01036a8504482c1101e0b03210384198851510025005031400c080707009486184001201c0c064840c4007500c0c0c0b43e455418001072070341340e02c40306c03180c86030801c0050340c410312884801009541c1c07081c24050f041510032043d01c0c00b2213491040613107000303440e020080342540c0c0c1031080c2d00d0b039110581880305042d4140b000084488507171440c181000d9641d10f900516582e020070a40c0c000f03250800c01032180c1c14040c50 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 189680845 1250 189679595 189679619
    0x170a030b040c020d0e0f0306040204050c1201121a1005040507050417060103020a150503070302070c0e040c0f060f02030702040b0a1a0c0d0507030e09071b0506011401081b0a02010213 80
    0x102240005c044c9541900305c0d1904001103a90004020f001300304a4545400304801000702400e003145828040024125410b4a44400c46c02880780c1d8817849003181c1c1034181309801030048124064180075110400c465030200600316000d0322010380d03000560740da4556054a9a00c590b030000d0008120303002c4031500052001503c103040e030f0700c02c1e104510101e03034840c0d10310302c000451000380300810010b000290080c2d109034050035409005031030041869540d4060042d04105c02c1c0c0c0c00b81c900e283c0300f440c10b1105840340047d24005141a00d450761050445510007500c030f00aa100080c800c940f240500c010a41d14119086c000e04003038030601558000000107982c90703a000d06818001800360f402c030480c0c11400f80042d150807079015110032020821f007030100072260000402000c18032200404132580c12542d081c00c0074881303115000604082d410f0000040072041c4281c0d1041c1001000010030900100e0303d105100c40c01580f580898486a1b1024184c0c007901808400203c85a54042c001a1191580ca = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 189682095 1250 189680845 189680863
    0xa080102280318030c1a010b070201170601020c240f040f09060e060105030a0e0601062d020c0607210c0605070f0503150a08011119080103170a030b040c02 68
    0x22030308a10710304018081e030950b50828440c3c00d20652031280140880d004008888240d48100240880c200c0000100310541000b070704102c86020f0040744040440d600612113006845050318940c003030b4a0b20000003903442024610f441d0058005802e001c0c1910340c146015421114017094082d103540c0301c441d40783c280303800510a042d1803c0f191140010444054400c40c01500c141c103131000000c0e42c0d1380c40190340d00c0e80040c150200269031030314500103880003800101e000c1e20f541e07a50250704508849654000700e100f00c0074800384200060b422454150002801c06e9045001e0b540c0e0342e201c1029003000c200d81c240781c0c124143d4074401005041e045a6002c03003501d10030b0344038643c01c00c990707196484c0448002c00740c6116070011a5003000818240d1034500100b417030810004107001c10090320f40580f5030940d0300150081c0b01c200e2010986403a005280c01351a0b649600c58a013402c0550b141da181c10100883c02481050284000190302c9180c2c2e2007500312000ca803001034400d0140e10041d41000396039140742 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 189683345 1250 189682095 189682147
    0x9031b050114010b0301080601060e031603030203130e060a0306051305150f090102090310182003010c020d0203190e0315070f02070f090b0f12031806070206180a080102 74
    0x102e001088441c10401a00c3c169501000244491ba007000c00075181500f100000a03454400d8010f50b0075000c1501c5402d0001e10301c01c0c0c0c055529030201100d002100d0308a9007120030721062050030840c80d42ca0303101c240310459402c14800b24070b6480c3c900702140c110001e00d4026209006041c00304000030b4142a5841c0103e6030030725040d90507600c20310982d080740190b80b4800e6040d04035003c42e000126036074002c0c040508103680981002d4940c1e80d035034100c02ca8424118102c040c1220f04e1040140303000e00c80c4084500160000d055a4088520000e49910400040e910a00a0a0844204035208000440040c1c0c00603003203814050096228400901c1d003191214006500c1100b984001480071400104640101b0a00803e030303400d01c0611000b90181c02002604040004100c0c2580c4c1d0b540d80d0240d2045624070040e681d030324035078161f034070014415001e458021407081000e44010385901e0200d8910210700940c188640070100f001481c4046140c0c4401801d6002203807815683c904000c03488036803424 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 189684595 1250 189683345 189683381
    0x4110a02030a021b090622020d0504060b060301060c1e02040c0c052104050d050f030a0507060f090b040206030a09201801060206070f03020408100606030506010e100309031b0501 78
    0x54075070404c20308981c11911500b00058401184c0c09080102c00c52000340f4222450001020084558104981181c00031482c52901c40c2e0500040c42528880c01c3e03101c0c4c0c400c2d100c4a14541c141003010340032220182008040380d1844079003007008170701c14001440c9158010018000260340d0400100709000c0200203580758020781e0000101841480302500051a030122014105441c180070410211a1880142d5450103500b80135054640203100809102d2010385440b5114034690400c0e1045410804e40325040d98545144940440c83c40c00710b25034031690480301300e45d07a41c0c0c1c0c00f41c0701b030060013002c0b10042411480c00c0b4010201d0020391140c0966040540345c40d10380e594507400d1100c1c070303900a11446015030007500200306154440e01d40d83c9507641e614200545840e0307a640540d0324000d43c4591102c903869a807403062000700c0d0f050150680100003441c0c05109403001d400001c000900d55038004091540c5c0307021210405004032003108010440100c1d03404441d902d0f0600c4e501818005480e4502c210f0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 189685845 1250 189684595 189684613
    0xb0105010e0a0f1503061d07020f0f0606040207050a0b01060302030a1404080a08100f060507030f1e0807140403060603050601081c080711063102090c0904110a02030a02 74
    0x10000581c0003102c60030080441a2464412180041302d0020110b404150b121078011032a241011183c5190f032130180e20034503980c501030344001c2c2452004507005103d6000103082414500700050f0300c41d08420304450040c0c2d260070710724055103440c0c82400700401780410341e0b00010381c243d0107902a51141c1c010b10030030301480b825007842c80188036081340c006001a10910042041c9407140d001c0c1c650000c8600d441900d86600c50600308110540c0c1c0d44942c0006000264040030103901c910f1403060801d990400308001ca1801e442d00e014004000c2e10395080203400000141c1080c402e655102d080303035200854981e0799460b8104200504211700080c0c2d90b9100305400011244000980ba00105020300d0b0307041e10383c0d0000c0f802110004005031803102046000060b00381c802d50140046401001d0300303003500303001248150b82d41d0302d503d41c080b1103031050001008c0d411002d40c4900c00700683c0304122840082c0d4920000e40018020803001c0344c410b014140218040e0540c0750000020500b82d52140c00302c2e90445 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 189687095 1250 189685845 189685849
    0x1080106080313090527280506040210030b12010e0f07060504090203070302040338190f180305120109050103111311161a041e080f0301030b0105010e 66
    0x102c1080240610103c00000411002040d0f034801500030100500d64400703d9a02c1d10a81d00a00001c050f420b070a80104a5203134982d06201c003d200c1e940441d1072031000712034581c0c4030300e601d510009102a00a1125192091000d4441c1c0c0c05518030000092910481c2000d0b103603070034006c000307100c2c60300414031030007450103502c00740080e020003219141d60352203203002d041120b128003940018140806243c0c09100c00320002d23100f541c01030f0110000c0c500306a00202614420569100909080340700540d80308140710202c0d00d400d1204443c84c2c0c0c280b0001c50310464140e400f80052001c60b00381e0b5504070202da0841c08065001006100303800103009900000d0b601c503241001261802c4c40020b000b40f1745403407250864203000400c400c0c206520000015101c000e07201100c600d40c490141c0b44c0108442e90340070f008000c3d030165801e028035808000c0803405c2c41d183d41e50701c522002c0004900f40040c00382001e403040100c0300c000c48900c1411030141c1d9449580d245005941c00c00d0a02501d40418039400c1c01500c94 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 189688345 1250 189687095 189687097
    0x40510091104050a140901180618140a0501050907050919080303090706020106060c0213090606150f02011a1c1208150609010c110f0307141203070c1511060708010801060803 76
    0x17540000c2541282c3d0b46442d4420304501c0c1000d0399112850f0301c90100061103c82c8034034101c0c2c88940d444001c9132aa030450081881000b0081c81700a903185480700500103900d41d16010f50f808000d1f805d12903611400080020225002800382a4551603908008102804040055405a07038002c0403030b0885910303154103070300340d504501030307880004c60360b580c0c0e1000340c07503d40080c0e501d1030740b41c0500261071100c60b1903031001d54280707400090039038502d0000c42da1443c0e0312802c030000000542c0700030041742040603615082402c2c0400c0c1684501d14a01750800c41007005c41e10604510391006604942881180b8094245c00b4106d4041c01207020026210b40eaa0400201b10380000c04140d603440c815031002e54403140c944a0302c20000d60001490f4101d0055910108070000c040e1200c40e402140ca5440c64081140c3d10203140300250150700140b200c0400940341e40100e1064402114000710480742031482200d020744a201aa103251044c90180040305030800865410b03142444002c0c400c4585034070030240e40b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 189689595 1250 189688345 189688379
    0x40f03060e0d021b060a031d0c19050d0f0c120b010305120a0f0f050405040f051506040f0303080603010b040513230d21050906070e030a020f040510091104050a 70
    0x10a02c0e181e18803e00340d145c008010705102c0c01500300010406280c101c41c1c603280c035200c06201d441d941f125010120354500450b00611241105981a01c0582000007140030030300a418000c10b90b5494240071020002d4030301c8000f000d001070b148103a00038907041c107204200344402e11060f604c6005658814620040c202c0481d0240c42d21902da05010b8040705104841d16511240c0140c2040401e103c0800c0c15031300c0c1c2c02904811b400d50400442c540c02c0010220f0b9840f00c5128019100d42000c200800040c0a8120381400b1240c00d82080d1101d0741d28040400d001d085010480e80e803003898402040650b100c2e606141c24040c0c0100c0c06004a003d82140d06c4a01e4080302c1c070214840d41c048004004400e100b542c0c040354007d010401441c0c00100c900c90103065031b10980f040b5800e40c00c91020003402603801604001451002c4004100b1051131342c0216886005002c0114000d60303e541c002100c0c0c000d20300e4850000c0c00b103032904014000481c01c0040c15a01300b8040d042c46000000800150101c2146c86054 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 189690845 1250 189689595 189689623
    0x4081f0513170901090b0c0f010506060a1b081608030a0b09040221030c0d0306060f020c090a05130c03030e010f020102033108030c031504020a0210020d02040f03060e0d02 75
    0x8510902d802005503400491589040080d0f2450104040131040c01034800048400010003041d40c02c2e032841401d41e0801440c1301e004020034004058440c0c2e114204083c0d03001703107446100018440d400c082c0d101b4450b0110f02405116103444140c20840c419001750320507a04048100701d10504030041080703206050b80c0c041d51000740e90440030950b80d090103104200708100000c6902e402e02d22600c2070305051141039030001180d56a4000c004068100290b150b5182e198030182009044040004d90202406045144020783e00c00010f1140c5a0490141200340c2d0000705020705540d507454010300f8125400c4d00b07180094840f4040da41d5050050003524040e910003119841c900104d1480e44440c01301c0c007001c945010006050400c046540f05c801107004000c0c584260fa80ca182544280b0392406030080182d001d00e1040012900b420340c0030580c03041e0407428002c0940c0d54004115294040d00603504221400350700080300004200141d0721440d0000c250360240d4031903401e00305090361074a0407615442 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 189692095 1250 189690845 189690863
    0x9050a0309060e1503060315040c03021c080f1c0e010c0f0e0901051e0a1203080105060a050d05060105040815040c14130207030302040905010b0d0501080c01020a03031104081f0513 79
    0x11300010909024561040c4040d007195808165a0380e982c0f003040c030565050703414048010007402542080341401c80c50307072006983c0030030b41d910030f0780c410119214074444540c110303001080d50b0301032a5003440e20071121280c40c0d50510401e0a9103061138002d101e1920f0000104100150022859008415014800c5401030a502a41e0b1900342481003020b24a1401c2007409480400500940d440884040203094103000b20801c00b90366180c040e01822068000510a440500ca040c8403940e0007404c07102d201500340004070f8280c99020041e1080c0c0a05d400c45041401444040720300120b828510358421401001c03884505035584880011264041c071003030b50409010751401100300610380081003032500c01c1c40c00500d020341d10f0219004484080c3c009180203a0009580e500401840c062a405003051034040c0c00c2d055903080000c1d5540c41c02410060034543c40319280789843d408038041c0c90080204006582c500c20b0300900d101e100065960105a035103181c40c0100e10f5030030720500a009030a034000480 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 189693345 1250 189692095 189692119
    0x3090b0a150509390313030206071d1e06040603140c09010504150c050106030c0e0a0e0c10050c0709091704030203070306111306020d02010b1e01050c0f0109050a0309060e 75
    0x302013000da90b9550448004044295030110141c00b0300861180b210a01c04e80348036051840c000f401c02d0320140a03401088081c0140107401c4994242d4007a900100316007000e80e000720f542c210b4140c03c44900116500800100e00010000d8040c1c022003022200e03140100d00d140d80f0b05164407c140544403071207000610a00084c4980c420311303070001903242c11078101080b03004c8056890600707550a541044070082c00042e0204050105150610781000c2100b8052100c0060050ba10340d641d686150901d100e5003072400c035031400500070000c941d000500d49090b2101281c0380d04001000d0714101804407620b2401d00503455103c461032090b01c00b40c0e9402400380c0a00d628607222840a4254603c6a00010034104920010440c059400100030000c40d0042c202c1250441c0002c0d007107444511242e40100da120701d800501c82c2c070040d04c0c181000c43c03d0a2282e01c4854201300700b841d0200c81d4142000545c41c0003e08014040c0001d07010907218400e40c1e490208580b00c100071101d07084103a1416030004440b07841 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 189694595 1250 189693345 189693391
    0xc02030705031b070f120b0105040b0904020411132904060203090405060f030d030b010e0307050a090507051608040306050a0e1c020f1504020405010b03130b060103090b0a150509 78
    0x1490f03800d880d1100c202c0701450340300c075a0305030031400c03da01c400010117030900701604001d01c01998a00412741140d04001c04861000401c0c60706030010b00007880b80e65501100c40c520821481a02c000c0a130080c0f6102019484407903034402c03101d0b0f2041c1000d5900842c0d1043c0d202d02d12500456003500c09650286043c042d000050002510002c0c00e10f650082150030490502e84040200c281c00400a9a000c1180d0b8070b5030340050403c180c084881c5d4042d402109050043d62240d8210b0421150940c0c000a029903400c00102d070540102c0c0540c2d040d03050f42d000c0e81c00034414403130f0180007601c2c06400200401e03110300c054074007210034802d1604e00c3d517041003403024012a00100740400aa005005641c558817000f1401e90512500040c014030400c40075081c841581000e120705805400a603044500d1401c103a089102c140017071440040c1071070a00303000602664400d40181070020387c44441103136141010b01088003d0403c0300704400000fa020400080c151070414070f41400383e034459200076405981000317 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 189695845 1250 189694595 189694627
    0x30c0801060b0702037513060806040803010e0c07031d03150c0c070e0c1615050a0507020f0a0c180b0303040906170114130609050a080306040c0203070503 68
    0x5402ca401300680250044030600300e802124840043c0031000c0403c03401c0c6d03200c5d5580702c00448102a58102e81441c54200511800c0c40b81c00115080710001c0300401400300e4174004c1d000300d820400060103400b06120411103070b88095816100c0d000380e0744405903249100d5912038001d035140034001680c1104012040281d914110115840c0a010742d0004107800c0260210b05900341c9125450100c0026281c4030103106008480103052581418500c508011a030036466000b5001d9202e00502c15001080c10004152401007164010322010300c00c03841d0442e40d04000781300c1220180302600a002001c2d51003d80400c1107a029980081032080b854186580303030300c00380b00d0400b940008583e9401912580d07981000034000030134449602103001814a9070790280e0481e180f001600c1c40e030400611075004807080100c150301c108081080321480c25181880342c050000703c00e0103441405801001001d000c2000e000713510039401601c040c400d5000c4200c00f00d0f5070f44200d20f030182281d0018015030720500c046107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 189697095 1250 189695845 189695893
    0x80403080906090904111206091203180f01060617060108040b0c09191a040b040515071b0f0824071e05040312030c0203072604030c0801060b070203 65
    0x42c048a041c60f02260108201c8003043d10240d50070002403008011516208045031140300190000c1d2901d8145941c1c51070392403420606040150340b0110008850595200000d6403600401c0c085076003c0f650002d10a000341014007800c0002002c0c44846003403030140c9078501f4002c1c001a51841c0e0981e9071a103070308150510113002c5010074002041880020b070f41e0b48914004940d1500b000c0c2d5003007440c0400281c1030391440700740c404244c0c5043c0f004100e418904001d440c2110070554102c0441c40d0131040c0058071b440b44142c010059651450150b0000e40c1c00c1c00084240c96040e45d003040c81640b02e800346a0f65000b405899401c62000e0000000301c03050800609800c012a410300c542c00c10204c544041d081200d070070144e00000e20120701002840340320501c1098806140c10104002c3e40b00201c001c0d101c0c45030100184c04143c1049100e403a80c04244d041e0b04000075680c0100762070b140c0f00d20740804002800c2c80307449400e45c00c244020a8125802d021668070030750041c010548a40d8000d26814018080 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 189698345 1250 189697095 189697099
    0x1101030f0204051503011508010302100c06020708030a0c030b0102030306060412060f0606050a030612020a06031505100c140106140904050c060a11010e0d020d05090f0a03050123040804030809 84
    0x2d200002d100e0301d6402d0382641088074801040d450b5070400c0c1d10390f9484108070582d9410030a0741001000503840d40c0c109080249814600506881c9407424090003034031908034004d001c20701c00010024070300e142d580030790020f4245513410702182192038012a500d00060318801d0340003204100811223001d0132411140c0440c4a800042200d00412000c0c0d07040301d089900100108100043e100640341c0e1603c03e16000d400d4138019070443e01440c0d0081964960300307004100034141e40d00b1004085040d4008040e00410004044055400a0800007800b000341064111511582c000e03c03440281010b01561050341c02145015804042c0101000030454018206072107038016044d440c1070580381c00300109200b10580c3c40c1d5240d100f404001d90b9086030702011401120b0b030040785140120365070105500c0c4a480391483d0035500c1e000688001500e24004a5500c0d5000340048000010820190003010321800000740e03074020b6600c0020b44d080102001c0724000d0404100300700500c000360b2020090305400c0d0700 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 189699595 1250 189698345 189698347
    0x31707050c060f1209030a080403050313060528060b07021011030f04030b07031a010e04060e04140601060503090a0206211305010b030a080d0b0f15031f031101030f02 73
    0x2011010a00b280d120640d01c1540b4540050030310640b91100c00d8a0781c0009031080107503c4c00e41e020400500300c44014100508004001000c0b0301700900c01c0d200032400f96003003134007041181490900084125803c006480c810802a0440c61480405106031811102d0b01d84555261821681c01c018800c0c90b480030b00c1062020b0700c103d0200d2808200f0103058100801c1e006259545d0a504054054601c010051400c050a2107541a41c031070a20b64200382070b007000c0c2050071196003004000f40141045400c14a0f20034030070400c000a01040710a0041130b9298101515800e98075584116000e100444020b4440d900540100c03005045c0040103104000707584501c00d044032542c0f003000340d07012130075509210350101e0541d8560a0002c203104043d18014101d00a0074003004a0743c68034514040c0d0108103288607600c0c00030f4485511080f441e0701e81003030005c141c03035044a15800042d800fa0029600d440c1e1210421000310750f40318461500c3e006494100d017010314080c0c0408011009008001d00c08956150 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 189700845 1250 189699595 189699613
    0x100f020a110a0b19020c06090303070b0405010e0109030c11010228050102091507030201060b09011719110a03051302130509010615020703030806090c030f070e03071409060a03170705 80
    0x3070500c000c0c00040661000d11007413405440c0c002880c040c03410403210b10400041103042050f42c0e00208030341c2210744c005007030005075803603003040c134014038048402e140c0035400c02c1220002c05a10407105684640b0800e06401d01215540049958611603c81d03442c02c80058640d490b260580c222400c00c4443c480d0780094503042610001c10600c101c10403960f44102e0010030b0290400d602030103040064600783c2410780c00c002c0d030107000030800d411000311002100303001000325100c1d200f24102c4020000044405104080101c02051601d510089401001a1901c030101b0110700001c1840c0004603002000d08020041c030a01080c000c20018120300500d40da941c0c40061020351241003a003c0c9540354000e00401791442c140500b186600600c1c09100311000001c10255a5a210543c1d4100f4032051014a01e87d44041050b82c103010700c81449a8184030381d00d800180c10781d204034041c0d41140c054441c05040e403204070a12980c1005c5000c005c05c44540c041d1000d100290207409071407124010000c455140e1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 189702095 1250 189700845 189700859
    0x41103070605090102010e1605040f0b04050f060a12170c0c030604050102030a060b03060a06050a0522090f0513020f0f0d1202060c2805040320100f020a110a 69
    0x118907501110126902040c600c55968080c8510352880e41c000024004080030140200d060b02c00324098144199640da2844001c200c655111114501c400b900801c52401c140b40f00c02100d00302255903d10929007000041141ca4540707083c02c6003036902c42d040b4904000748001030071980d00001c2040941c4d11450b00c0d1030f60281d9017045454051401140010b0b82c034289041d18900351041e6030080c1480a13000c100b80581a02e5090191044030790a103040c82d00e810030443c1c00c545a11618810307101d01496119402600301c410f0410908444440508000302c1c034094440303a043d10401c4400a203042c58500311600941013072101c0d004110303001000c0c900ca0440c6440060805d01c811202a9606100407004211103501046510307007102e41a8030441c1000e4114414001400070806034048244032007003203001d01c40c001c2041d02d018640c849141c03802c83e01c09031402a241c5981c80d060b02e20601108000b007441c6070184146030300075034071503001e411940c42d1034460107081805460040c2c0c101029502c001144 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 189703345 1250 189702095 189702103
    0x1409030109030c030e0f010210020708120403030608010f0c0c02151903020301050901080c0604140105040306060b0c0d050f1623150a1406191802070b0108030c15041103 74
    0x8500c60785892000c03030f074142001010842602d0b0814001e601603a0056650784c0c001070f02e160b001c061120301680d60001889c1c1049180212649028400e520109200805825800c58020f0320003080007040b41070f45a5100e0000d441601d001c00000c85d003082e200c4030240c104055050b402c000a0000c01d8505441101c483d0b035003181c640228000030340e0100050100d40b81c400c145070f004140d15402000c001d002403000601e00c2c45548a02e1000040d035000c0703082164014401c0c2d60065400840c1008042d0341c0ba20000d0003540b098640706c0e078a002c2c20856440b80c0b80914240c1c1e840da0800c103055403c1c1103108009545407600020161000168400440391b40752103501c40d840c1030f0000a0103412941400102e00007500c0300175010032503190901c3d1805200092030407181e41d205c0011110f00b804000d00b40900e10420105070425502c02d2040950035103101195001410f41da8819902e215407aa80c40301c2c55074072070286604003201a0018034492018003101c1e4240d54025001d03410711012400b50100091070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 189704595 1250 189703345 189703361
    0xb180306270c0102060f100302030a06050106030e01200d09020603040f0210080705070209040201120e0601060e06070b1314030a09180507080414210306030715080714090301 76
    0x819148440700000c220040001440c800003402055162001c400203521440004d180c0c207038008030302d00050b03584060110300000440c0c000c0c043c1c81d600c1c109810300034090182402a400424104035840507400384c14400ea000040024030b003003900c900941e494512a43c4080b132900c0d40d181e05c2d41820005650350200440c00b652080e14549810440e40c0705000c40007010342c1d03a01c0700f40076118080102051b0004101c44205504580c011169070b11480161382d40000130088000607490039450780d080e914001603181c180e60031500d521465a40d208200410344c0304940c4020400e00e24030000c80c0300b801001c000b0401a51040c20484980701285a946196400c0038003114001860323031500300003d6181e0f051381b10b501c1c58000c0e001d02c40c600d040b01d805084018058001030103c05100002518081c1c1071000718943c200070001c07064010500e0340c42070754940090b5071580c4a40546800011155001201300700802c5103a2a15141a0783e11002580e00c49410300d000d1900c88020405060310381e40c284078140f2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 189705845 1250 189704595 189704611
    0x30e06090c120304030b0118060b0706050603070524030a060503030f03061c050604030e0402130305070515072019090906060801020a050d11120906040623010b180306 73
    0x1203901000c1c0108040d02c00760080300503079a04100801d1001c1981501d5a90649000d00706540c0120035455800000745940e030300c9402c0d10040411074008003ca15007091f0301880040382110211501c80003044642684401410398034115125000032081d8000003131988804031a00009190f42d40d0750110b420b60b40080003c20240d407000042000341e1514880480d00d10195440501414409940c0e445c0e46540186c806400d100500c01c0007043ca03075890b0102c4964492610f21802041e95900d0256030f909198001d1511601d24000082c00c805c032000c007950007064200711403031110040000000780c05909220300e80e812155901144007403141c0220080020851810006400116400d01c0c41c1111002e0b00002c203264010810011000d612401340c84100100031b10000b8080886000e04806200b0720903558000c3c504c001c00c0115410300480e03114030407030040300d050041e2030080c0c01101c25100d8100e03240d4040b60b02e01005001102c0440c0142900030900e2100c000c0262501e40013034900001200e00603 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 189707095 1250 189705845 189705853
    0xf12011b02031902030f0d18060f0e060c03060a3c1e050105030c0f13140909190f060f05091c050403020303030417040f14040e0606030616030e0609 65
    0xca50002c091942c481e540d501032001d176040050f11092044a0700c02c1c0341d02c205946440b50341ca0209400b030160b64000ca180e0120082103441d40300d01501025104040440c003050244800140c0000c0714001100c3c46035400800000d1030320700304140b41040c040b42c400c941604002002190392035441e50302e60841040300b4a80b851166500e0440c1c6d00e50802d5884504880d03118510300100704c980d0f00003040d00c1e0482142203080e42c0308d41141e00100c1c40c0d4007603945400401b02e400903000890009098040d52494002ea039408034695880005076601c0c044228644c1000d80030720700e84008a0041c1001d000c44c10301c40c01001c100742003207210000c00c0d00c0701034422032402d80000540750b1a038080c0300807480314140581045404d05286400190f2203000c01030001d001b00701a0746650301401104012103000c0e00880429120300c680351160796034114000c00140c3e000c1d03403605000e01d0076004005110b07407255000a0050150356280e103441c07940e18020151000c241500c4030b0100301d40000c24405540307c1ea1401e4018 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 189708345 1250 189707095 189707107
    0x312030b040617070e1801240b121b0c03030412270b0901020703051506010e040504020f012a030804120e0a06030b0f06070b10050f0f12011b0203 64
    0x11a03140e6400f20418140c010428010f0010100702402100c40f680240d201d180d40d080d0752008000582c3e03030301034181d501e0b00b507803000c00441d07030810490700312440650a003943e9180c652004481c13080021aa800da01500006580c90b00c0c400f4070010455040a4510300381013403d04014910b80003910200c0740180c0154800041075803201641c02620705503034810014842142035041528010f010744001c2c1040010413810503402084080011035000c021503203e0802400c1440c1c0c030080681304940040c11448980700c80e85028040c141c022900280700014070036280005507400341c1400941c800d0300549412280001d0781001070240c410b4041d0302c0c1e040310f83c03078186800c0e070b4451034140d144d60070707c07408200d5075410352a82d101d10800c0d100107042c0090718000300c00004140c070041c84070f41d07a403202000940d00304111022455501034028080101d014648030790401003042c0c0701045540d088241407840d41c809141030142d0b010808500d0000141d480341170000710f2400c124490030304006d42d00000390 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 189709595 1250 189708345 189708349
    0x80708070b040812070302090d0f020a05030601060216050a05130902010c060c0c15020304030206010e100f0b09030c091b0d0204170606180702030d0e0c040c120c02060f04060e03040312030b 83
    0x481540121706107011450003000d100001d0200110840c05000b05e42104100021516265400e00182c40020115503243da55050000c0d598411000c8400011001c4000081d044c180140c000040e941e0041c045d420358008028040000e040703c1005034104500700e1084030106250380326024132103610365200d046020f00340c01c0000308003c3c2c104070b845483e403040040101203907001c11640d055803807681c5001000e8880f11a4190000da59411410501e402c0c61000107030821624003c041e56032055094406080006c01040805c80d82110300800b500c09225030140004030030070007064030950100c1d0060502c0d459183e12020480030f4080c000c5542c0c000001d110082c50120780d00074030501c244a041c403031440c106500944030b00801900800b100d448110180000302c00b400440c2c1208000b42c002c02003003148503070050190304410340c0c891a05240240c020381991001c41c0c00c8d0320640d880072700c4094545690b61030000a01050f10441ea040c00203100c0880010088038001d41d031110581d03008583d007488082 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 189710845 1250 189709595 189709627
    0x305091203011a0f0c0f010c0905060a02120c0a0506090c12030418020310030609120807031505120a0b07091e05030a0b04050f0304030305030a27080708070b0408 71
    0x1034004440380061004002c1804002c05002d180c10383e4a00c05a102da0307800b0b41c2001180900c40321004503006945240501100c1544525032481207592442c00881e500c1b0705009603482810503d0005030810758a4142c20b0585c01b0003044041c0400040301d0030304140b9101d0a041c1b45045c0d850f10a070790000e070800b60031031400c88a141c2c1c2c1d1034040d002540c586450308403c000500e20301c00c240e150254022000074142d909d03455080001f5a004901032001030f074245018034000003912080320128a21b0300100d8081072003407140714a14442c0455040261303042c8420400c550314190800a1244110820400051407100305540581d21075151103040c00d0070108644403071859000505035114141900300455900098212010f9800910003000c070b442d01d04105042c250510035050035848009000070800d54400011442200c007203500704010319220920300600200d14038a02504044400f0346408110040024903407d84100183c2e8500300482d85d0703440da803c50486064980c407901145111956810740 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 189712095 1250 189710845 189710863
    0x60c0e030f030309060105040e030d0b011b03080402040e03031b070510020a120b04180f050106052709010b01050a050f0c06011502150420010e030a0605010510020a030909110d0606030509 82
    0x100c00f403101440c075603272265881c001c03644000080d90700d405c006100c690040300385025014004030007000110140c01c018241c44001d8030224011840c001080d0340080700401560b004172442e0100c9890b40c1c3c0c2403581d454503900440c206a6060007610030703a00045c0b10601c010004818140c59195006c08028071150440d07600941e1a8012414000ca40703050f07102c2020f184c5246540040c03850015421403c01d42d00501c00c50b044a9040500030f444040312802201c80410308250514000107070b0340c0d910041d14203a4000760b841d02d0108005100b000103481c020805405088132180c00c40c9c1c100300c080540d9a1900c1803c1e401000281c01c17990765190340c01da0601c8500503000c0c40d414003031018101039035402001740750502c02d02400b103a42d00c241c0303506c0e07071050071840520440201111142d1106040a400078882845201d00c07545501a840303002e540041110b5076240e0301900e60700c000c0ca2138480300d90080c240d01010081400c0d0b00700b2034200404200d2046401400850303400188034a0969140307481c01c007051b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 189713345 1250 189712095 189712099
    0x4060608091006031101050c100504111309080f0702031c170a0e07140103020708070c1712030a020a0e060714010e0708030706090c051e1008090307060c0e030f030309060105 76
    0x41010f0005c28218051600080b0080c41e04980e5001c1e0880070302e0a110078070401203a444c0c105818081406104078041140120403506501424040408002229401d01c80101161400d10400300355500400181292500150903601280e40b019006040c58030605445008528a6032205e5801c01003041a07540c4034103090400c10001109580080c2e03140c0c000c0c8104104400341ea42000b100703074400e4040d205103542c06914691a17441c2841e20580810140c083c9188a813451104a0700303007400080e0104004109048203461610f13003921001c065403103a080d071018441d0880c1005250745800000b40038040c010200c01c092040485861401d44107624007022081d0300481040c041c000010084529060707000c40d0003e215441880c7c0014500c180340c0c072090f4481090b2102820030b0b040855200303840001281d18000c403442c0c0d02030031f0b43d407a442510988900d0b1310500c200300001d80340754800314904240d4100b01408505c0040040c1c9041040c2c42c040e04a074201006002040302c0401c4100d0140c030003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 189714595 1250 189713345 189713351
    0xe04120908060f040201030e0d12180c0303030213030f110306070311040509040c0806070504030b0901090b13020f061c050c040302010c03180308040b030411090603030901120b040606080910 83
    0x1410700703181d995010180c0b000480714504400b04045a001e640644480804034003a55040e00348442d000d0324070001310000041c2c190420486983c80b584120383c4184e013652210241c001c3c1411910110000d400221403e41c0c14418100040007058220f07004a515500c55010790350601800c806050034208090101e106060821071011008070700e0b201031b6025200107a484c50020b40d1142005408070205d40d1008045024070414003240562000003041500d010b66001d0340742d600c401500c1402c8510841c4050b0903080d011000c51071090108070401201400180703840c0312000c5034000640e06621090700401008081d24000302c00402501a650388032644c8220300d404c051441d000a003444d84031290060801c10f0743d21502100c10740700d0402c00041e6030800141600e9030346980012540e0b900544080d80c01504010400c9160300d000d407140ba100d020080e0146080510050041d07810721142c64404800548510942e2415220351044000410b1103030745140c0941000a03101d82410b548101518140342 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 189715845 1250 189714595 189714599
    0xf1a040201050d0209010905150307180609050d020d120914010306150c051f02070314030702120c01060e0a0b040605060c210f190201050c130e07030212010e041209 72
    0x80c2250a80c0c0c1c0e43d80074240c0c05a61a41080d00407a00600950012644038120811000200c031540303000c1c6214000a840e00c0224412001e04a0b070340e0100c03072203802c2c009808200140a40e08150031702001c0b445c03000c0d000910348030072503644560345042e00301d81d0300c0025003201c4100b0030a00031416004030b6000c03e003010000c290a140c0300301c0d594103941c0050300c00e1280c11544d010811104001c1d0b850064501210300c800110b00f6a0b880c0080d6010b00c80c154006400c0c0d0031a103030442c10300c80469004502ca0340041031035006401c8c03001c4607504004400c80b20781d503a074880010310a0040c6481d42c410960320382e0000da8045084100f1044034815007010b4000c907814071002c41c00800014500400c3c0850b0304103100c1d01c03c0c1d04c004d58112407150031006411440f01013101440360741c1c0d07402c000301c06c02e11a400034030695032000701420082c0201b4551007420f02c909501088981d500c243c00310b802981c20b20f0050301d003401c440b4403140c1c62074080e4041d180f515103040420003400080ba14800d40e01080f441e003101158 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 189717095 1250 189715845 189715847
    0xb0c160b1311040614061315020606090609070f0f050c0d121503030507080705070302040207030c0c15090308030a02041e03030f1d011209021f02060609010e070804050307050106030f1a040201 84
    0x14031119406018040000d4844582c7c220300c0e41140042240010441202a01c00c1e40291100c405a840500400150000c6089031500245480c4034058030ba40c0c80558003203502c01111586907550b0b103201800400c01c1103038040203040c03000c003900800741e440d039410481403050075404448030b6042d50300086145480500000b40d02500b114030860308030018a442e0b051a0a146040080da580000d50240c400100442016005004810b85078058a055078a4980c2e5100c07081c10f400b1114642c2d00010320201d014000903102001460700035183e4180181441c0d2a0154114a291340c7d24002191140c41d0304100201a400415804000c41c3c516081d000c4204244201e250190050341145c140300740380300e440c48d070340d25031780d001010352a001000d0450070950008004c01004190710010014000c20300054001c0c203151610030704030b8a14903002e07a0307540c0d140c9000b203c03030a40151048036940010044403020135000d004050155004100141c2c04d004d051400511000300101c00c1e602002a6404100160b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 189718345 1250 189717095 189717119
    0x801020310031203110403060501050f0f0907050c0f0d020f0708030403150b010e130501090c05070b0f090a05070b030f1812090f15071e0b0c160b13110406 68
    0x1280c2c004449800409000f50950103010492501510035074042070000c2800155003105040354030944144402ca40c1040501840030030008660340c019103c2408180403511520003000a81c0b0050b06132880740d106500041d0070300c5c0c84907504900591043c0c09104803c20b040c0f10b0f05000300220801549014a0341e5a0b0011350b0301480880c62001e81d66261140641c0d000e07002210b406880108070060b0180e006401c000184000e001d0500c1d450f10f010036a0b0078040c090b401f01c5400640004100c0281e617990300c0031000e80310000b441c1302940e018103c2c4810006104000d84006062410400c50300c07440d000c0c00328200000300824036546445802070382d12500030089281c8d02c0d10207003e12030b41ea03200c0a22002c240148400c00c030450f017000304c0140c80e079404e125400183c04441d00ca202c00c48411141200350100b2180042805001094400d000c00c07022030451004002c035840901002054001c5912070320714540084545501c4070b08515004400c1100c40c1020b08030441044900304a03440c18550001c00c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 189719595 1250 189718345 189718349
    0x30a0809271303030b03011b1d010507080a090503100c0206100605033c010306050f0609160c02040603031806020d05041208120915160815240a0206010801020310 71
    0xb0400c2141115082c5403003500010181c2901800a000141107001d60f10504400d2030b00c2e00300040c1011003003003002c1c50f02c8032011408500503520302d803e0560545980314107500c401d01003c10700551541c0060241c8050000012b075500008001a00502e4450080c0c01c1101c0281415440461308009201d100c4c2c0050541e03801029144d86000f60500c4c0c0291004280e14400251043c20740440034491000701044045040e2449074200f80610b4890803944680080296032403540101e590000900e000c0c80f801c016488070f0030310702d0403c01d11801c640209040f038040350410740024140041a140703e611841014001f8000c41c40240503210700f020b40100140120300400c07801c10000c3d01c0d60b00500030104d05441d416041468407001030305100c82c2d032582d68006e1251419075001240c0c00614540004d16090780700c1c050503120b2480503901d6074403a02103100119012648a41819080180080d1030003013003a40d0100d001e92556205c00707014002c0e1400c00164040220f5a00400030090400f84824000b81 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 189720845 1250 189719595 189719611
    0x20a02010c120201060b0c0718050105060a050309031303060621020108070c0c03081201080d030e0c100c052e020903120f0c010510060f05030714030a0902030a080927 73
    0x8402c01d164030704038094030403075020301050071002c2918280140007284403021101c0906190150f21010440707031080d00e10900c181940b00105200321a543da0140000750f510501c00001d89181c000031102161a5508a8100f40c5003142d6684080c010844110000d204034000c503101da504940340c5a00082450350010101010000d01c280d090301000b10405281000c2d651160f00161118003405001d42e14920900c03518200340314444118120340e020348514191203200038080c0c01550050301c10700114000f04160b501c20003d204000201154082c0082401454801690b95200c481d00c440d001d07503800c1e022071401440c0d10402c41e98403103a400203012195003559841c1d41c3d84658114074060041d0080d0801c202541d401d080400080920400c0c440d4180c940c0c54840001c618103003e0100c0b801d000490f0700034003050420041222021003503000c1d43d0700100b540c01c08101c5d45090707404241080141c0e542210300c514003068134202450b1000e0748041c114244004034a61001502401443c410060050b075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 189722095 1250 189720845 189720863
    0xf0402060c010b030615010306052d0625030e06120402280e010509010914060411040b0f070c05040524010c0f241803140d06030309080d020a02010c 65
    0x810320103080d003003883c0880d0000c058035031500d085c50000c0c03605c10840b10030500080c504440429989005041e203442c800340b40f2000e502e250044014107400c088803ea90692001040c8951081e014001003450416070007030070304580c441000d15001d00980c40020969102e0340c404d000b030b0040a003a00e1129030307105030110307400e85000d07154003910301c1140c00c0c992040e01060504403021400c01c84003460581214416500321050741c2c0d070307040312808882e50402c401c1c8120701060003054151a140d04004001c0150300360003483c00d82d950180620541c02034010160300230003c600c61041c00403042c0544000d00c015513080c0704901d00306100c41042103040c0c1c00c0e20ba015100c180140100d9101d950144541c0b0b40c0560342001c02c0e8214240404013025481e055030742e65141200c028060781841c092100210760f9100b41d000700f107801e07507001e4580030b8401704d06800f40241030040c140041414001d0200440c040c0c0c85042c10751781003034039860425500b14400d00c15907021100e4000140d9209041c04600d0790411140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 189723345 1250 189722095 189722107
    0x30917030d111b0706020f06071e0e04020408011a040e120d1e0204091a01020d0c06021e040f1a030a021606060602010b01090504060e0f04170a0915080f040206 70
    0x1e09400f90890405004418019030b6080c1140014001c05540c0740b5000c8801054524407220381d1040100c8181c000942100e001c0f00a01c070030250848001c0c04176051601200c494400030404076009076001c10500d03034440c2da100207445941041c0c0700c40c1c0301080c0c03002c0c0490502c0007003083c8daa440103c40344601c6e042c00100b00d10401d01c0da41c03000c400c2d601f0380e101c1912242820301d00800607403c64000d82030581d02e8100f060001000e01035066030b03022810b13009040000031040040d0f5010460b140d0540341c49800f040b00e4100d03c0d500a04040490009075481c580f03680c1818400d404076031254018a0706607001103861508020544c090f00d40c042c08110b00540e4410041d10380d0303c10415448001800360342410408159078fc0c064122807c1c2480a82c2d805020300c0d83c031020070080d11542c0c03144102009840700800c070106810040c182d40113005411003070306606020101c081a40c40300440f400096071911092084464084184440300740e1450442031500389240b003403038030780005003000303224000c0050f02c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 189724595 1250 189723345 189723371
    0x206030f09160603020711010e03060a0b040207060e07080d020f070b0a140d0b09160e090604061e262a040606030509060907180506010c0c0b07030917030d 68
    0x10448202c1016821001580d40d59003000e006904403401c125100c50700c851260420303500c192810325001d50020004c0c885610b404019100034420300c0c4219410a808019200c0070a81500851000c0302c1c0000050020030b10b008111804c11340510218008c540000211203030170309000a241c0d0a99005102c015510321040405882d44040380c45ca84410023000708546100c000c0590020070154020759020180740e9803000710540300311814416502240c0c420000b4110340c00c006000c554809030242c8002640c540351807900d02c50300500c400441c0e442d10b0586060040c8081c140200c00c21031110307640000d024090b5441d05444902d0591840c14000c0f5541e40c1145002e1344c0d80c1c542c1004180a00100501a25000010058502260005407a04c65540460040d07600000e066044030248204c0f20380401c01c81c01a900549005421f442c1044181d0f9520404650310b11012802440c400201070b5480d2010714003c0c02a2001e90f2080d0019440c03d5807040301c02170301000301c81d04440c40c034800060b40d41c03c241c6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 189725845 1250 189724595 189724603
    0x90b01020312070806010e0f01021908040b190e01090f050108060102070e07020c210604020108040809090f040201030b0406030305160302011d1e1b090628061b0206030f09 75
    0x1503048030b0704851024400c19541241e10f06020f01802c1e44d40c15446d00e00c0b00c05128054107515000ca00580c84030404410364400700315074003001449081420f1a26030340d0780f240442c9800035020381c00c0590100a40d0380e65aa00650380c2c411861080c01d00040ba1460004c1850002d162449454184201c00000464582c400d2150101820002c0248007540c00c00c540002c0d80c0e2451f0b1003085000722883d40c041c600044100a080f078145051000611144d91158011a501100030b40201c035850700921180055a0380d4481c41882142032411000503882c150000406660303040b004e2600a41c40e00c941400402c0c5d1100031241100354103011010a07078a9454204d00500c00c41e502d92550155542d1b51460486020503840f800b407140311030244032103001484107603c1c1c60641c802902c0c803111544a01c0ca55081c506520f942c04100140644070945551040204009142c011120b03001680d075001e0180c41d420400c068910031410001d2083c0c02802c2d404166a8407019001c808010554400510041343c100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 189727095 1250 189725845 189725857
    0xf06060f0d050114120102030417070c030803010602060a0501150e1e0307080a1205040b04140607060c080f0a0b0603180f0307030c05060a0209060d0b03010605060403050304050909010510090b010203 87
    0x394081142c2d41c1d5420030580c00b00001c41440344141400d20702d1401028050007568000d5400403080d0800103e007024006040d07000d00d00840350040322910020104480700c001d036001f404150041c26851070404101e00890744140c002d0010441d0301c262001d82203602c00e00441c0c000c8400c0d901e100ba2000e42c00509440c1c5d4005003005681403041c41d8000c6000e090100d401074000d80301c0c0501c0c0c404441908410344081c0154040c1005a183c00c2c881085a19520350100c89c225001400042c5408401d07100d0b0010b9803001d10000780401e0b120390a200740c810000c0c070616448286841c0422509040c50009055488040c19810f0081c18105651014038000d0243c02d40c2280c0e15001c895644c0e81d10318010f015850018000c1c0d415016120000c0e982039050300880f604442e00401c0c10b4546030010040c074000f0010402101d8056607030788004101c9480e1400208061400f5100035031700c481c503220810031143d90081080c811641440148800b07455140c0140085d10b0414801280700e900420040703185d80229 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 189728345 1250 189727095 189727117
    0x100b0306011d040906020403020411160b0a0f140601090605040f030605090f0102040e190b0609090414030a0e041b1b08090306070504061b020102120a0903060603081309050f06060f 79
    0x132030340002c02c02c852680200100d130b00c03d07901408484007081c6049100e021751081c0c0b02c035400202c0901c600046a00801c00d0b0700c846140000614074012201603c2241e0b8420001c004802e407023018056250780101680e802807043e8035284d131605082c00c140184880c401e200040103652140e021a4500c1c105109400d102e4804200840d2503d550f400f60041f0200140da031100c1411800c2012121400d190094024440700501028584403041d0103204944000410940e5840c04151400d100220b003440281807610a90b80e42100c20841da1040004a4920203520044040707038000030b0039040c2d0001d02e42080c406107a0429903100080d07060403a9140724a1400d2076050107001c080000e8103802c4800342099a0840d40c505a07051103102d105801c5c80070b015030190144e80894a101405501440207001c17820140c5442079456907642d64034419540d50360001c032a10b91004c152440e001403c0a03107400100300c80d003814059810034041d4555150400b03032415008400004030544880d10303000403101c131300000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 189729595 1250 189728345 189728351
    0x180803070c03120b030307030507030c0515010503011a030c0103150f0608010e090d0c0b09070b070605011406030411091b0304050d1101091a0709050a090c0206100b0306011d04 77
    0x2242000070310010700c41c14101c1c04545800d1a01d0300c11080f07485040040b0303201800070762038600161015100c1780c03c40c032011020441d150415200081060101d058002c4503298134002039410305003013500352000c0c0842d03003401401342d040031050795900003002e05035101d00b0b0800099030360020308990b00007180c5411a10020582050000e443c1c0c1d88810310504aa007250800002510351015080d12149032100e82e4001801c2d94038410082440364000540042005003101c550320303603850101c0c11641140c0d00558000c0d035940010071514903820428004a28100c910301e20f5490587d58176100b49440c03880c1c460244101c02e00046080c10010320441c2000c00001e1401d4480c90245801950340307900c42d0007040001c40c000800d8040e8901401101600c5034000e901d01f4900344264074103000d02a0050801b41000460300b0006255210114035501408080c0804143d460001c2406850180b0207009001e480076420420007210344040b0980b50001001d10f000010300706818102c11001e040a01c5841d84946 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 189730845 1250 189729595 189729601
    0x90103090b1f090209131a040f0b030c1906030e01020d09080703090503120f071112060f060d02210c0604080f0106092c010908160b06030105011503180803 68
    0x41d0310861000d4091000002e002c0c01d80310441082640100707a031403a0007400c603100c3c1500d09501c80d00001d4003e10020755001a009100b0002010b40e1819255040340a0b074502c0341800c10708041c01a45410302c0e058541d0040707409200c020b000c0759200c0d44988401c056842d07803401c4206c0802e40454511010014003400307841c4207800d200c403155020017012004510404400500d5003004a6000300c1090b130450140d00b0154040d00c40d00070b5a020300c90484428020700324062090360359800d01001000440000d2030146859180071481040203021148504071021251005a40711003690341c012018020340200c00701600211494402e10310a86640310401003401f180040c80052510740b124288030007403082e6903541695000b00c58000ca10054003040c0a880340600d451003490071282190b00b640000307484041502c5804440e007001c04c2c2031300b15804809203031052013480e1003450b40000781140204010752524810644020740480f0200505441c0c500d54529200121000503c19400c0104a83d49113 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 189732095 1250 189730845 189730861
    0xb04090c0806100602060601050714010c080108120708070f05010b0a0b0a0e01110d03020a090b041d0708070c0b06060714010506030610080d0c0213020c060105030d0201020a08010506090103090b 85
    0x9000c500071000c0c01c0c03003035000060306005911807403c21281d064001d030450303403075600c01100e065026900645207440382b181d00740c503008424410000411190742e160581035040245850800c3c07a0080f08a084807000d00503200840c03128811a48800e6105e584140c09441e42c1c6882800343c14104841a80154240b0000501c4c1d51240020700d907039203095407000c0b00120404015145000c6e51041425103034011102c1d841c005000740e00074001342e8a5410040070702541c81d008408654050b4111000b803501c0483c821242c1d1a1003e2602d0b008001420400d501e4948418001c00701c461110000d04072094220100d0344c641c07219001c60f803042d5080f00300421944e01c114186800782c0710075100d0724000d1050304005a05107640c1100441a9202500030701041580c203401250030300e540310700599114000c4000d00e04014150320042c20360b144001c01a100300d41c504400c1501b000d8540c030170b15065900412103c0046607000da07100e41500c0c82105c0c865181c44d11a07004030300030402c03018001d1020805901f40b01c415 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 189733345 1250 189732095 189732113
    0x40905032208070b0915090901080f01270b0402040b13050402120d020d0f050f070f020405100f0306020318030c16080d09061b0209150103140705070807060b0409 71
    0x2aa405000c07480c005036481803010b07618400f0f84100d40b00c1520078002d4860358682180c1d00308450442200c25800c02c91712600044502c8006e038404031241e84000d0086400200a0140040007403801b20700a680c400c40f541c01d0464171081100007403080e81480d000a0465a41d43d10010300c140d4007074001c45c0852a001032a00080405550591081c5183c202042c01e0090000740344518003c19805010008610001600c0070720403c00e10300288502807141c01b09440030103003e03110140c0a0942e03c5250030040c0148001c0380c201520700b40e42c94980200078005406940309117421240c0c41040140d40380e9500b07003585006490074140e81c915000005808820312000501c102c0202800c00e2440c0b0080d035501e8285665029605992000c1010b0750b9042040d540150880d035080c0c690044c02094699441c0c1c00a010148111002200180ca15080700c0d400e50303052095409040c10454001c205007401000a4450702807800018940500050220100070a6030021804410083c0c030a1010340355524041c00b20b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 189734595 1250 189733345 189733387
    0x906050406080a081b01090213020703030b012a230f1009120809030d091209121104110c0111070b0705070201080c0c0307150204090c1404050d0204090503 68
    0x10035428040003148500e004900392962580c04440e003803401580482d00144c0701c000c0040503405541e10240c50000d030310740c2400c01c100e044005000596580ca2441e024040314183d8200c18100104c1002c0d108a04c6040c620b424418640d1806040e00c00f10a031901d0302458150880150481c1540c0d100081841400a03041544424140551b039082c1500c9440d801282d0624801420078440c104003409518001c00c03829402070fa000059078070345180e000100d801d03240c1000c01101c8500c0b0702c80302298010b03440300c040340c003070b01040c6604030740f03c100c03900e80c03640c0e1020444400d032103140e0307801704042100b1009080b15516404100240841503c1c41400304813500320540c1550b0015081000803110b9215004507060039505844143c15074540c100c0501541e0030002400901b40b100308507001c003045c942c40040d010010b08500150707030b032405c00c1582400d41c1c100d02ea81c4024814003600044904105e40d06890070340340c082d20b03031302c4090560b4000140508050398010f0010300001901440404a0703581000e1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 189735845 1250 189734595 189734599
    0xc0328020c06030f060904020409050a03021b0102030c1b032a0906040209060d0915150311060408060703020901180305010542041d1606180909020316090605 69
    0x41c00c010400c00740459807104481c1406916881030014030030b0302e0507040303558005001074400103242d1401d940f01441c02042744400c0c0d000d030b0710215040321224486c0016500703d6000b84080c7d414080c01d5174485983d440b80c02c00b1514680000c0368500c0d0152002c0000c00b411041e4480c42e000000b990700c60040030074203010b0190740200001c00015040341064001c596031000040d28807490400480020b02c01488561800c8074140084c0a803074014080c1c9000301402c5041490031070100c189146044070910f8016426103014907414441040000400f08280e6031001007805c0150703694640000498816081031038408503001c100d000481030110540c0f11a11030f8440800e8880d8807000816001c1c002d00604090000d50b85403101140603070800c0c41d20302c444c612005403012410481003400e0410700e50804428a29560040b49407085c1000280705542c001c8c260b90426502c1c074085540005d440c00703141c1c01240782468540c69404c00b10340301000454140c00d0a00e1504214544070341240000d4000c0d84107540c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 189737095 1250 189735845 189735853
    0x9010b040311061305090915100806150604030201080912030a0b030c030f07060c02060c030a020a03080c0a080c0c1c0504051806100e12010903020a0605130302070306020c032802 78
    0x3100c181001811100b03828040b130100e9130658617100c01c010300d0f04e00040c02d501c258000c00341034510303150040404030b020707504a54489440c107040142c00ca180550041002e00c60300ca4041c202c020b9a00c803a81101c0a880d020f01c1d00c1c00259079410701d41b03440d0001c42082c0b18080c1c800001001041c851aa000241500080b401c0d0b918404c038800805655410480c103c4205800c103010070061180a5510034407020301c054211400c000181d509581141c01c100045c80c0075030400219901010b0744482403da0041160070321900780001000000d0440100506845145100150400307080004009000c40043c400c0003400c1c5200b07034481b000f0302c2c030303003191158601134030a1304052040c001103080c8884c8155809080d802035100b050345c0c00c0b10030b440c110075416040902c1c03680122000d41d080c000d8900b00790281d0000d0a003000b040c50f0440032248018006140172010304002e2000079408503c990840e0340080c40561240020010141140b043d00e1242d6121746100c001c01c00c8929444481407408540e035000c0d5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 189738345 1250 189737095 189737123
    0x12030209100507150e0f0a050d091706010e060f060307020c01020c010306140f041506080411040204030b07030e0f0703050f0106060e0603070309030306180f05010918030c02030a0209010b0403 84
    0x507142c50062460040401e0001e20702c0040c0001e1552252503110480400c40782c1d10785048440350301700700300301c2010303202d5821013135010304426005103024006094001601c603401c115042141c0d00c900341802041059402e010118503a03075a101c1810201c10340007082d59030b07039080c00a0065a5029203c8603d400760040e0102c1039042c0d80030f403017080101e40b4103800e4868a00c0310001084100034203840c0850b8025690b4003c1d01c04514140ca05802030310ae15101c40c0b10134100360812941d05800f00c50854070841c0100300500008020034040303a0055001e0401103a14103001d48441d00300b0210032600350041c496a040081440400500035010105881c02040819200c0c403003100c1d209141a0102c4d0807110800208208601c203500c120401d074028600000c40544450366442c6e41c840b41c1c1c40c00b5a078203480b0303a050114001d180c4a03007401040300c99030820860940c4007800340d041034140c0015040c0300300c000c0710714150344081c800011b105500a0103603400e9038403008580b02c42d0b001030001b03450260b458600 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 189739595 1250 189738345 189738347
    0x7092303010e0313050f060d150f080102040b1210030203100606030f0c020705060c030d06060903060e150703020708070c09050709080a030203030105090c0c0a0c15090e0a0504020a031203020910 85
    0x4036101000c0003560002c4d094288800e20261038038007203226800403810040034511103014800d07001402000d00044402d00d04e016000b1060042039000f20b0b400c2e0344104030801041c641e48044504101c110b01e0218440c0c1e0314421644103c134401e52020b074250044989503800000b90390700c00c9081c0d4103240c03003c008100702092040e00f1151202180c5000d42d00c4008240010b1501001418030050608100ca01d84100d1032012400d031016a4050800310304070b00c9043c401c00c03a01e8094040781090607401007090207103d0303540d04c400c00f2001e0000c00c01d140d4001400010711026500f00c411154110250415140c0d4031594071000b0b14085445800203421074070301140450b40031130b1035001c0d290107500544c19a404d01041205000000c6c2009042e40401c014654003120300303101a00e80d1500601c4491031042c03902081d4210448600c825001f00030b000142400030300c0f5907400300c1e41c006600c0c000028003a5110f10101d001c13080d240e000604000c0075003e520302c1056164008040d082c1042c1c03051194400d903c14 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 189740845 1250 189739595 189739597
    0x6030603020a03171b0a1110090501081003020d050a14031603050a0908060403020706030e010e10090303180b10050409480305060601020a03051207092303010e03 71
    0x294025200803042001c500b5400c01584112004d0307041c145040320030007840c241d0030321400618110b42c000840b400c00340b00400c2e01d01d1503051811380d02c0c60040d46c030700d0000501c0303ca090f014603818840c0c0b08002c103018804e2a440c4501440c2e0107450040c521401d400c24650300d05481201700d60341d58891003082401b20000c002d468012503640394507000340707140340e81c151403541040342c02030100700c403198001030044002c0048600541c0a0f03001341100390300b801c0700103007510040780b0f80c002d07240e051001c002d1000030300003080444100a40300c0003500784064a01140074014051003900384214203401e81e002d20011080041c0a00800c4000907000381d506d8082c40107171100d000c00685455000d40300d503214003542ca100c02c00a00300d09440485042c1110f40700c0701d910020270740416500d00c0c00318001e104204040000a070001c01c00d00007040c951080d81c0d001406440f0302d0308005c81d11490040418540703401a003101003e81488100e10801445208801e519046282c8006102e076090044040c1380404c080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 189742095 1250 189740845 189740849
    0xc0c011403040f02060d06141f0903030e0310022802010c0c0813030510150f030c0320060d0209040b090103080d11090907020d0f090e04031209020301090813060306 72
    0x910024150342d10340d00ca52603542620f4000781e8005404202d0460416024031412014003050010b01c100031600a007071110a43c6842100515605441d0785440784580009031101100e5040c40c1200c060038000300482d0420120f082040d61846c000b040842030180601a0301c422032801c1e05141040b80c01c224000c0f401d0f20910b0210101007000710010324040f0f101c1000030400c0c2644202c0721540301e42d0700e699035860a0501031994100aa9130080c00d4400d00310f08513541d00401200c540d156001b4155200d0110303407000d03444002c040c540d03041c02040c07000c4030041d88c005034200c00030540b039100c2d00582d1400c4060b500584220b480b0301e1401c0b01540151900b080c02c141070380c2d0440402810018441d480c4e00042641e500c3c0d00191550501131941540da81002191050002e540a410205400c09005c0c05101a0719541c1081c807550410130700038041c6688080381c0c0503400d841c004d44085c030a00c048400400e041e14002e501942418001b0003401000002007148a4032014042c482d40e6881c0011030444080b4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 189743345 1250 189742095 189742127
    0x307150516050415032304060b0a0e040209060607031112030f010806070f0f090506040f08070b07150506010e031501230a0b030405010b0a1701180201051207050408010608030c0c01 79
    0x848503469003a1099001141106c00c05200d1a0359090159016840b0b00003194110384c06a20f8500750740b950700785850000010414030b110250542415800200703148070003030005000b6000401c140342072520800c5e043c8208034400382500c042103400f400080c00f561045038019500c0c0100000000c0401000a00783d04c1000d0036681d09070308032041c4108035030003001a54000108038000c0c0c40440c1c075540d208000c100910041c00c82446240c9048005414842c00c1d601c0b4000e5107409000300c10102d9141140c801d000d00c58100001680d948890040e50b0410341d14aa15405206d10b20f10f108001c003190004a0503030343c0080b4220b04d200541c0d600d80b040401ca9810703c940286e800c450400c100210080650341241c440c03070000c90106096001701d000264180e000080f06841c965110309071440a01c510280c00518410f4846a400c2640000c3d180d84140c5901180348924100001c0d00300344100d0684018114280c0244602662902c055a81e40c000e1000018940103008500b400c83d801024010303081088 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 189744595 1250 189743345 189743369
    0x516030201171812041409090d0c020a030804060309111002070603150504020304050d0806040515060c120f07140601260f031b010b011d060c03071505160504 69
    0x841882520310700c0094480d1070f06412028460380001410b00154400f5038a03510b90540303c51401e22640071411003000001d000b001c40c44140b000000c8081108020422241040801c801c0035101140345043c071a4005059030380d010401140302585030b04000e2000b4062040c90141268203c00c02801105107281a0090380c0545000c226103402600301441e140440c02c0310042107580d55000c5020307030313208540440d500e812040307007039000c903420009103070300407805943c06c003d90306d814101164170004450106100740d102180c000c86035107040081c4601040303a402d801d500e0303401580d011003007a0071004e0708889034000303810140c0504400286c068101c5400c02e94082c201001c094103040b01c0c00549858852a000700c01150034901400c00c004c04803d05102040c0c16555101d2011a00f1640b0541c0503a04001911100c00e030140701c030504100c0c442600715255941c4029003034029103540b0030004001c05880c48505512a503116540c03096100711030079101202d0149044c90119094840c41c01142082c5107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 189745845 1250 189744595 189744617
    0x9011e080105011b0c030b06100201050105090103020d050f070605090f011b020409030c0b011805181507020a0611070201030b010f05031302010e031f0b0103060501122304050601030516030201 84
    0x2200c0c00c0814410301002e42d0311040d0000b2078a8103103210b0310a4000f035402c58051f106100b0203044c2407201d00240b10251008102a506080000740490418407002e0b00c41e40421150100780801032044680025002c01102c07112540c5000140c007075007042d981e182c070070950150025029401f0f0118456081080000010200c80b19401c01c4020580c0d940140c040202a84038200005d00880845001e00500881f00700f000c101c004181c0d056030750042030300c03650a00104292a1007480010400c0c61446038500d118a9a076a48100700d10f03148141c08080c00b00350800c0001c3c05480b071a0801001c03018000c1c1d030309211112980e001980c400e074007150700000207401040000c084884841c50301c80b11901c145464280100c242c00068075000c0700340300342402400c0401800500300c072148a1003114200a080c1404000d24103000a40254455803d605c85980c40e10101c0000519410003600440c1700c080d040c42e0799041070704105a44440c240012503003403042d40e03900780107000324101388000c507a416900c4401c054 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 189747095 1250 189745845 189745847
    0x1f0207050a02040e0316061b0c03020c10140a03060509010b0703080c03040501140c0d0e1c08100906120302010b0103050c0d0b1906030b0f06040807050603250509011e08010501 77
    0x44140000300005020903c60781103201c6d031140c40b1403040d900841000c205140301040503020101500429130038003040344c5107900000c1d004a1100c2494104803494038400e24800410750304142d20040c5400c1b1040002002c2e040c1680580c00310701a2501510203460b035a0320781c1d1843c3c50601c15107902401182141001402015120780110b0380300e48900000714a0070801c4065040d01101625480c000d1900401c5419502c4010b02c00c44180d68201801030000380d000056507181c04e5007004070501003007140000100f8000c0c051400c80003c00303001800704180d81c1e40d09824201c130b80c01404100c00550a200d6505000d600c6805424025292946000e1a01041c84d903490000c1c003209803030070381103416283e0f4000705502e8800800e0040c00191408200c3e110104100501d80389280086071090200340424004040300040e403034103546007501e005507240c03202541101c41c02c01040c00d00c3c1a2101c1c07000444c004640c044068810601c084e00e400000c1c5800c20302d40326050070540d1012000910250040040b9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 189748201 1106 189747095 189747101
    0x20702040218131b050703110609060f0703050108100207021816020f030309060105040e0708011505120a0b041104060803030406060815160c0206040b03091f0207050a0204 75
    0x20135800280d40d01a00d410740451000c1141c0480e01608260289600a0406070200d00b06d560503d08405091b903264000c5890000b032802544c003103109203000e4003c0c6416540c0c0c03c000b5103030000c201040c41009401504069078010701003045c3e0070000d071120035010301420301c10042c1c54a0549140019280c8401e07560101195401002004441c602c00708006055460881c0e010401c10300c000d0f00903250603007940000085519040d00044c83d01840c00c03041080755419200703e01d039203d42e44002a00c6106107100646007140c04000540061403030261402c0c00d071070041c0001030142e103031203032546150011a0200c4815a48940902040804204018a0f4103200f0b1180e070207460900820f00790340c0342d120314190078403a07107402c840215906d0b0380c1550003500c045681240c40f4600540c183d0754900d0a00180c8001901c44400340d140c408460088455090708500107000d0b406059080c0002 = true := by decide +kernel

theorem cover : BRFrame.Cov 189568345 189748201 := by
  have h0 := BRFrame.cov_init 189568345
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189568345 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 189568345 ≤ n) (h2 : n < 189748201) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
