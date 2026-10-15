-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4323
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:15:19.413602+00:00
-- url     : https://prove2.me/submissions/24a94bcf-f2a0-491a-8b22-7e4980f9fe46

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 777338129 ≤ n < 777517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 777339379 1250 777338129 777338131
    0x607063206090a090203062806080f07051002031207030605100503090c0609030703021302120f19060302150304111e01030b0f090420040603030e011706090112080c15 73
    0x2041e61014080d0303035580983c0b012070fa4204002075042e000100443c40e401280f00800800c86030008008405030082988071089804030b500401c019000240000442c01080c8404030050106907400700425150020023910391003150219151400d000f004612410700c00c0e031024000d02030141006110404482c4042c04980080320fa420042c41160502120303401c05009550081c1c20250003031002e503041d68200000d01e540303601c240700f511394248100024070b1085080c0700d02480704140aa01e0a04051385032095000c0040c500644ca40e040003810401a201d40260764059540d0801d50340c0c8a8403507141024407510180c861035400302581102000c02d10780d80380319048000d402d880030008a5051414001c20354140d0030000c0c0d01041000000300031440340b000203000341400d42c42d90006241010700280c03c8910942003900021000700b403d10055820a60000c0103111161200ad082d1a013803000550f02d28050113614030707006150038001c04100241e400d9402505070b103425508051200c5682075400d101c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 777340629 1250 777339379 777339391
    0x1805060a0905040b0d120507050a06050a09021216060509031501030c0f080714210a150f291306120c0f150309030e03100617030906070632 61
    0x441c00e040344c000d9141510a01302d0701d50780000c4000c462100d5020694040e0030050050b5024044d50321804005000780c4100b62107500d8446000584414a00500c114442001c0403200c3c20b80c042c40c2d403000503030807114404044402c28130b4100d07901d100c80c07000b003030038a400026000e165000d06c40011041010704180c1038162850310030812000b9940d0036250380d484c1100d20503c01c00b07007000c812004403410981600d030824444da07440381c442140c01480b69450302c04503541c00d440001901c20480d081c06a24028507001d140900c00c1030010b1640442c00c001443c4a040f50140f049080c1c0a01d1105612114070614600100110801405030742d00901d141381508041c044402e4031034084085122141920300d5800d88896810070800c920040c0420780040800e804250103200360342d404541c0c10350b8108007841140141c02c0000c60303060716142044525503082d58410321107030424000c02030302c1c2d1501d00580701e285812140c041b402d0a41601700c9681c5041c1d42e0030f0450414429601d4401d1012003117841c6000341 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 777341879 1250 777340629 777340631
    0x305150a0e01020f041505120c0d1503120e011101020c010204170613061802040f0906060e090a0204050c0c0607020a140c06030117480d031805060a090504 68
    0x1880040742c0c00c0b4802ca4203824a0108248414005c840c0c803604040512280e03814407614150f20300000c04c1d559002115628200d2100190f0014004c0c2d45020b081c60030b28030143d00d281c002c1d00315030300d0512007826914440f040200105450341141e1064641e42024180381000b15902d8265001960203907200340940750000302880c000c0c4003707580008580d8810f41805815004a5040e43d0311038001d442039002da40c869000c8040c2000140c0c3c0c891040d020360044001e00041c40081600d00b801c04c0d501564440b00b800366185c0200002c4600228882d100c1c40c2d81214000f03080d0f0364000d4509241e00440c10040590b108100401c20080d0b00011400030940c01010340c050b0b0320004107480d50761504902400b40d0051400d000401040303140e040303080e10302d2510710161191002e90f584012043d4210001c45806140d402e5404145585081c40450312810340280c404199444103010407041d5032424001420040325940d0318908001d54403500010308001000e0660300c02408000900280203030180610503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 777343129 1250 777341879 777341891
    0x7022506080606040b0301170a0213020318070302090c1b060430020a031d0904060618060305060c090111150709090504030e09060103091502030a0c14070f03090305150a 74
    0x10303c0c002050710300710f9200d01c5a030b0749160b080001c002c0d1141034948010b5030728840d1326180b6006a80d038140f8500d40c42241c0c000147c807480c180e0011980191022140304054000c540e0900240c0c450142083e131003580b86014503507824540c3d4020b4203404045004070310500a41041c4402c1101611070f055001121240c4080b5070350303c0c140f11643c5586617801d03180160b40110280303000207020300010000d04452004d00d440c1c04102d01c0100340c0e482000c8804a9600c0c0e40c644090000032200c0215404011035400b04200080c00c555459a580c2c0001e02240c00c425004a01e1000b26885031500d14079401c003030340c203580703500303000e10702c0288044400d40340724020541204001c200100e9a100d003078800ca4055036811958a0501d0034840d5001000e44074a041584462260003c52188620300d030100711401001a580c0c608099140101c42d00700c109001002040790440414401c10816510b80c1500300f142d41e840d240040ca415150000154001082c1f0b024003002519000c0000f4412845480314581c00d001c0b03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 777344379 1250 777343129 777343141
    0x80c0105030f1b190804051b010e0402090f0a03030e040f0c020c0111030c07030f051c0909050702030714010911030c1e030a050a120e06160b0702250608 67
    0x8500040b182441050001000603080d1100d000e4500c1280d10707003040d002d01d0220300c0040d0a9080c3d030340d8250300c2c000c00c1800c4240001c10a0401500c5203d0195403605c804041c20040000c00d1005502c0e0403501c190b80100702c009040c0d45034915090355110091040c45400d40d00d03e00030f0145501075200c54816450714645071041c0c9440c0c0141c11500d411035024050340c108030070056548203103400e03c0c02410301c0180440ea115400400c51000914000d1003150082d10141c50310b9880c103c0ca19a0b0b81c00301d8402a07144125040c0c20040844c140e8158031001b20300c0c0c2d6140c500807841c5015032600900404c2030000a065140010340c010b003085c90007200c404004137251804e140d0340c1d509240807150416001ea0035000445c0000403580240368009099803410009529018176207030a414050352000e0314400c0070400e04c1d801c01d294000300c4500352a078605018144401e6070108d1100d0300c002d40130501050014440074800c0c050301902801040500d1000d517408410b0030481815400b0b00ea01240c1d1902c04504 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 777345629 1250 777344379 777344387
    0x60415060216121502310f0b09030c150f04170606040516030b0d02030601030602250507380d141012022e0806041e18020a030606080c01 60
    0xc2ca80c2000109400380700051024000703511001c0d2900405040384003030a0481301e00b40300d0700c40d414440701c1002602802e07d000c0c0107120074554801403000038200b066044d10303200030848400019040f1070884140d402144080320b584909003807080c1c4401c00042c04526045210407551b010007500e411210145e5401c41800300312041a10680e8010300c16520300c0b0303407492081e00701508420000c0c2c050502d5503040c1e40860320f022802c0e0011501c40e48c0200e2031946c3c0c0e4100c41d12003046c014030402e00302880c41d820b0701c51603207410040c010541c0f500709003840c0c504c0361240601d09070356282c041d12100c4031811864980c0b0719107404c401c4104001d14103101340040c03280041d40c04940105540100040000d00d89082040c2d07410403514105c0c6c001010710036900107080100b40090a10302004040102d0251403d4001d10710100102281e100740d14102072119898441d0804d51208001813000107074075220351003111040481c01d40001d41c8140300c0d101c04803c100041e00180c08944000d8100d8031340c050440c006503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 777346879 1250 777345629 777345659
    0xc030a0305150d0b04061505131a0306070c03080c040b1605060a09080301171f06032303121005040204030804050a0b0306060a030c0c060f0510061115060415060216 72
    0x142480b00d00c5008140070582903406039040c1f40d582900c40342c003980d84070003080d00c0700d0600941d80e41c7c451b80c070104c000407035010350320001d6140e00460240045281800d00a0107030007610f0b4003e402c012101c00040c42030500340045801404e0312520007502c03002e02d00c450310200c4826200442e85402102d021401c6c42c1002e020301484e0961200c0e5090440c0c1c203004c1110800014074041041501c510074025031041c1001044402c00e01c4101c0002c185281075081500402041b45034500014a0341e4446c40601d0300c0110a69103070b0720907543c80034115250340040b01000821900155070242c4009000010084001c0c01072046401c02d83d042201c1e1540c0c1c0000e954180800c82d16207401800400a01d1075441c825401a100080181081a1014007644400085400700d460030079510355180e0500c10a0b1128441030801814145841c0c8424a80b03032625036181c503113400708000b03400c0700d040100300c440d9103c1d005807103011f682440c4a0000c0d607607000c000b0360303c281c15200e20384002e021080210341600d00344142 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 777348129 1250 777346879 777346883
    0xf12090e27070524130609090b0102030a05070602180a060201090501050603030903070612090c0b040303020f06160f17090304050907050403030914120d0e130203060d08070201050c030a0305150d 85
    0x4a00c0ca0201481210006100900703200c0300310004111010840c100039905d00c0140203940e403010002418581c1d15011900c00d25012070565006110049501c3d0340602100d00d207540c4000b0240c1c44110407a0f01e02c0c61030302051341d1f031a80440d5581e800f094241d030543c811108c15014200070700c1203450301c0c8140340c1c607071040304603c9405400620b02401818098405421442c3c0c0400d0300144c40700e0562191550381c9295048040e01d104005010020305504024407140c400700f0b03901500645c1000b0b1524900c0310380441296040c0050303d00352070002401090b21101c4062500d02805480c5008800d65440740d1040c000c0c81d21a507801c1000c52910780c801e40c01d680c00d8a92684500810505244510303422042145003168042d54000200c0141c01090080d400e61405c00e465034203011040c0400c02852a841c400d400c0441d61051040010325a240380382e92507600c3d0050740c1c0e90358a4409000481c1c040c402c4080c000322603c40050300c5280395915031700c4076214228861043c00030382000c034104080c0003924800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 777349379 1250 777348129 777348139
    0x8010b0702210d0302070326041707060f0c1103030403081b070f150f0b03060604020a050f03150109050901080d0e0105090a1d060d0f12090e270705 65
    0x184005062a0041210408042042c0d5554508051003289800c1e81420041d0000b500442d00d0000c240c1c1040303000c503004d11940c5080e0b140c0c02c440d2118009800300144003500301d0700144105004543c1000403034074490381010b018044801080361582c06416013451400004808102c0c0c0e412001010007580e001e95410395038500d441e113502030783c0060314801080da0b075010f48080110400081030501ca40007200d1040044480c011007107052501100c14028510300e280e4103003180005c40b50707808101540c0c4100c044800503111200b824003211079014849083c00c407114004103100303802d03003480c0041242d400240d0345c05c09801d44890500080318404c2c460898a544510000c240550040c80414045072040c504181003285402c009103280e0380b01d600598071081429111202d00c5047d01e0074640c0418113445042c4a283c1c40c4d510201009070700c000c0a40006409007000c0c40301442a240c240040c16200c032005106e0500034000c080003a1144401c2058005032401ea0260004c04100d00085600081c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 777350629 1250 777349379 777349387
    0x5040e0a09032c0d120206060922050c04060f180207120c021f030e0105090a0b01290720010309030207050f03010618050907060e0f13020d0e061608010b 67
    0x3009603c6003c52800440300000d00c81c4120303a40d4941041090b42d103806a40040203d000035030000c6e007401d00c050700c601d01601d014002c100e101c48030b203080707187c8440d04001201c2a00a660a00342c2c204030300070000d0755006080001c0000c100a980c1001029900390208013081000f080859600720310801c400203008003544415202d030780e8040d0a516120b5030014141070081200964031411010390541030001007035035a102d405404000b4411194842041d174003d000503580c0c1d8a400244050521540c07601c0c0c4c03800c0b9691900795110359141c100b01121f0425590b1100720a240480440e0040c00da03081d142805501254041c0d0b100c0d0040340034140e01500901441400e090602c507440c010a01070541540d220ba01c0010f10b500002d0718141c1c4090340080c001342c14200b01410a0400304268481401c0114085c2140e00540c3c410141d4100b481040340c454554015014129029000d04116030321154a04449882210f00c0410f21a00c24401058200e0041c4010202a5078007402070040540302c200c140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 777351879 1250 777350629 777350657
    0x1c02070513050601030f1d0139020f0a0303020a030b180f0615130f150801140406080604110f10050f180d050d0807080108060610030b03030a05040e0a0903 68
    0xb9001d41c3d0404410326000c41c5500581500701c00b070b141c2e403034801d607400080b841104140f04820b10500c41c1281c4a0040d0010300006003141c42080c11400540230320300e80c83d03d1030380d00c1c01e10700800914100d0003070310095030b40c4004541030140094004410a0740840e00386040c14900c1d14003064941491900000441c90985078996100d06400e001440f46810807504205a02e11240070000b50503209160040058214202106402041940d9005804850890380365802c07854001420784c1c1580d0300340403001e080504170030028000d04441d40c07104800340160002c0c08140443d1000b4001214400d81e040840702414000307119103561035550b4000054014407a42525444000082000d00c000720b0940d5609030101c0c000600e5070130061011030b0654410341c5000f644a03007200c02a1762040f951b0070144119850140c440f500d445004168600c510021003103d41d905000e54040411501d01800701e80e101e0b00204000b502d298072a0081000702010800087e6561182e03001d41c0300700c564103a0794015901680 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 777353129 1250 777351879 777351881
    0x9110f0a080910020f03011a0705030a180308070b060312130b090f120a050d030506011b0510020406020318041107020d050304180522050c1302090a081c02070513 71
    0x70b08125410301412480d50300b0781d0a140040c1c4011440d5660306540c0f545001582160b20400ca010455500c100f80482d030080380021040c1d460080301030602a030b0341e4000950020400c0c249400050801c28041410f509110001c0103c40c071611064084400e5880e00b80074010780f0340110b00050049024030744040c0640b1310098040d003122742c40580054095070b6001c000400318400d6041e0002d8075400040c2800c144101085600e00e9102e030303414200300c07509205000034200031100c10804540d0f400c01c01314004001041185d03120648150004644079030716214000d459600c0f0300581ca100c414100c2c0e591031145841e20400381000300b03a6104a150024603070030b011805814010a81d40b40c002407000158000040b151364a0880003000c0015580c40c0100ca4a482c004501100c150020280f400300000114000b503c080180b4003100c20b1846810107101d04400f92056070700c1c00d50001012040080c406000150350401c3e03014201004c8030091b20300f2400c83e0794a00030301c02c1a50040304001041084501 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 777354379 1250 777353129 777353131
    0x518011505090102010f0204090b1e0d0b06060705160807091b0e06070c080303010614070b010e0603280204050c120613291e06090613050904050709110f0a08 69
    0x2c180004101e07500c071213084a0403604240d2109510315180c0010fa15145803c1810b441000d880c0c1d44102d281c001c440c4086616801d6204005000007501d2000c20002da0300c54054440681c1e1000849143d1031003021020303c1580a8440d28030188506400460041d5140c00368009400301103e00300b400f002c1d40302c03085403030344125401301d07030498401c0044c900861400220b40c03000c1d240c00720042d6075035490150014900305002401103680c070001e120090028001a40182c1160002c0009008540710200060b007030040e079203000d0000a001d81e078140008605240150b01d01030088401700b04070356656036144418404d4a412101030301e510300004e44a0b140c054103100c2a0303c0c0700701e00002c80c0402040700e50600d0080c00864401c56501c0c60040c019494540c9004e141c4100c19842d1400c0412080f01040050041c10009480344402255580000218412070801004c00801c020ba090800b408d0440c1c031521a402036100310382c140b00d15020080004c01c119404403d00c010500e00d4041d283d1000c844001c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 777355629 1250 777354379 777354397
    0x20904050a1b4e050702100c020604030c06230a0c0306050d140a141f02040506040e040501020708041d070c0b040210180b1b0109170307020f10060518011505 69
    0x401010050f00901d81050496070089000340c001014141700001919125000804001142c00c3c43c040329449a800b00d002da802c15414241400c0c001e4403454607201600800201c00d00c0884c071300c000100942d810382c9001e4000c0c08408010400c08401d03000440c152445401090f400000c0f00756440f00145001c4004201044000b09854106090b551059030382d44580881007000e92001038800600503101000c613032120000c80e8114905803410000c9000c90045102d4076054641e6100002c0c140f000c290101d81d0543c0d031048030103a503151204d00c901e00314060040940c2c82c6019000006000d107014a10040366541c02c500b81c8001580c81c0e07030810060f1f6002080410401c41c0c0d80d1501007104004100c014090180950361913126900c00e038148600c4d15035441c99540c2681008a1345020482150002d541303000040c6240b5665a80c0210982c40d160120800303000b54465212201d140c00e00a0348800f0030749900303d4055054200e1070b1038040d03c0180078000d10a01281c0340c82ca038101c0a0154009000f940 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 777356879 1250 777355629 777355727
    0xb070f0201020c03030a1e1401090b060f0a03060e090705030c060a1b050309010f180515070c06090f05010e030c191d0403030b01050301030807030f03020904050a1b 72
    0x1c1c4206016500b540c109a4804100940310700480710481003082c21840c0c21f51000c0c500b08640c0100e03d12860b425641032003840c000c2951103141603178548400d801c84074032080350b03062a5540e805e00c000040041030f0901c55101d00708034500218040480100e050380031190b00900410407a40c400b002c03c4001d60040000c201400042603c1d035102803034210b0145802c50149004c1c42c3c0303450032040090001540c1d10205410048254080348000c140241004282d0b4000c2d0f03507011014508a01d8446d1a100b00e0301c01030010000341c2d4001a4261f44801080143c600b450f8102054039a02c00054170b4240d0b00c40c224503455080910100d40d1070801110140301902c604c4c2e40112101d07030326154420881c1d50702d00790b461148500400c000515425001f400c0c0341d601e003841e10a11319803442e22013002c80d01407001f00608200080c641201c1780d501c01d40603505450001481000f85060410340003000b0104140302085640000c409052814056141c4600385506560405180944120341c1e650540162501d00410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 777358129 1250 777356879 777356887
    0x3002060f0d05251814060f0d05010602070b0a170907150804110102060c030c03091614010f02120403080304050a0609140f07030206070b090f030a09050a0e01030b070f020102 76
    0x3929800b80501a11041c3d0b4100701100760b60390aa101003103414445814030604002d0400e04019041c001801c41e95000003011503030b28418001105c510880c14040314010010507a13a145d0356455010034120340ca0342d021a45001e0b5a41440c04840c02104204008100740506440c680c000002401d980091000c00751030743c080d210b940d880c035000c1520400300300040c80b81d02040200203d5417450411007500740020101c915103101181401d110003400c1041804002c07006c07980c030000030000750710800030310307403240d05595147c44110b12008010f45c0024001400c1c0e0f012180002e00104402c011185c610007401d10346070464031080e07156803005e0822201071040c2e00c040380109250f84115180c00d0b104202c08554042075029551410040c48980095500040820001617503050201c51025a1190a000c400c2d52603030b400380c0c10301c4400300180301680800515100b81c15070129907017055030412100d0f500515201e00c0050b8481c002400000c100554842c00307c1c41244c002d869200154241e44005803030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 777359379 1250 777358129 777358147
    0x9070216151d2103040509010b0903071e271a03030415050c03120115082716171608190c030c030506061309050601032402133002060f 59
    0x8003003601034070002e1390000310b400e105c50329050011034018450205001d00f80450540042e84880c100e10484074082021081c0244034101100d2560041c0382e0452040305400c0b103040030100301b21400d94035006052925500e60b10045804e0906175003044042c1c0298101420008400303c40030803c0d41d0001400f0f0305100c1c0c1014810104014909000444c1151045524090448881503404202401481400c00400c001d5031403460300001c5c900b480c0c01e030b004030b907001c401155406c200281005c0e449100d01740c000890720f41c220000b60700c8171030301c505c3c100c4a444001503604241c10005001d80107851b0020f1007007481400e940701c0e90100c1e103401550b4a240840c1da03556480214071031584200d515070404020441c0343d21303002c1c240640c03d4020800500c24504c4580d580d46d1102c40500000b0301064458001c114801100850110888501c090455480d06940f00c84161100c513803023002c2d84542c01e4000701d1519010265001d03c800c401440912100400d1b03402c1040503040421f070040c00090521801c01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 777360629 1250 777359379 777359419
    0x4080708030a02070e0c12041509110a051002060103020d05012418020703050724020c010905010509030a050304060209040b060a030c03060e1b0d0b09070216151d 71
    0x1800c1280066641e5480b802e4064107110340d07a84240001c9200c2420803050302003c504403182c95500105200c0c40d80d44514000c2402000144460186450302c5c54000420403815070603034020303104490140c5510780c0c84040050207141c020454005030002c030010001401c00c400c2241c05d5500c124004a8114000040c0e8050001e0007a0703468203000c1100404c00c2034000a80d0540b8030b000c0508000e524006280e1005841803003100001013580203c8040001c680d01800300800e00050456802c0d0b5880007403142c0240a800480c00076189540b900c40490351440000044601118a07a104c05045540750b07210100250045010507030072030b48401c20850349544445c02000050709036140050f1515a1100040866031150019445c0c00040c41c140403055954140301c0d40b140c542d01c410507549428444040010b4021f40b141690010140000c1c044502e4012411070002500000d10030300107560755002c1e0500b84002161240451141e002c4031001c0300518004180080b8080d015048150b41740007124 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 777361879 1250 777360629 777360643
    0x1e030907081c030510050622050a0b0705010501050906012a02060a050705060901090c090e030702120a0201020f06040c0302010c1e051f0b100503041b030501020304141c0807050408 79
    0x112512802e05040d00c0142e03007501c10300307811000d400058909a0b007888003080ca140700311040181c404901c0a1010502052130b00e0b0000a0030000d8201030071180c1d942c00720702c107503005030381d0403585542018000300303841c14500b420a100b0f0005079a040480c0c20081919007030102d00075000c0c070151603005d100310701507241c0f44003d2440005542d1074565502c03032802c0550405002400e4221164103100480002c40d504515a405850300c9a10024050150640b014918468154003d400200702d9001c0c1d0640321000c0380c0711031224000e0302520200344603050143e0300d80c0360450f001801c0141c0750340144055403040d6881c00d0031318850004d080c040c0c100240b80d00703818003004038121680e500030005c1030884040203050b08030116042c0b00c14071011400200080e11050840344000c10040040000b0303050004800400800c540c0316159502c00f151641413645c00303903104840c1520301460f942c6030307480c42403000550301001c40b52003000202c1723525007001c0c11962410b0181002040000c148801b05035850b0602080d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 777363129 1250 777361879 777361903
    0x26120108060618091e010e12040609060507200609220608070501051206010e100203030403090e040809042013080f0609072120040f021e03090708 64
    0x70005494400c04200d800c1d4020000030415040f00d400b4059408000034203496001800030b450264502c015032014010040c5141e00c010501c60900308603807400590f8001c0040d51215650452440e0300c409094405201705200141900e123419000040107000c44c018480e010001000186003000c0c1200280c41e5400c00c0d50200c2d141801402c50081c49603035486441c000740340c401d019102892034080064100c0c01a80741b40c0704074140d09030009006a01c03034400d10500c1d41004210011007238001da0029503075001117038203c02107202038002180c0386200c180724030b10566028071402e14042d80c5905000180c60410b4105c819000d90012031850303002988098010b000d01030b8428842c4500d407a1659281860140e00d00c2d2994220300f042c0001420081800d400341e611014a58080f140c255071302c041c1c80c500d9060007514907581040d02ca00406205075110340300480440d014071100740d026003410104e102d0549035907030107070f41040c82e02030005280018584c0041c0e105c0513a002540c0c0e486206d030a00d03c2001c0c07a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 777364379 1250 777363129 777363133
    0xa110702130b1f0e06030604060b070b04140106230f1c060b0906010f08090a020a0e010806100e13060f0f05160305070e060318100204050f010c26120108 67
    0x91410241484582404043c1e8000070b80007000300d0140b00a003803180801d007600c2c040d030300000004d001d80c3c4540c0c10000c020194040d5803541c414040c02c14018a0320152001c86a100c41500c2900820300140521001d0340d84400c1d00c00100f070624111034981c2e44101002c290041c407501c4c00d09840c0d03035544032030075841401070f030f0f5000e20b80459140a0080f5400c44c5522403103124900184000d50740d20000d04200345002c0e003814005074075190201e030300c1c080b10250020b40c014103c01002c244201d0045855049035001411585161602e00d0240540c403454041d0341c40d03600314940042c0c5801c00c2c1d1501005842c0c05800c0c0014500b40004c01d16040d24079070240403a10303a443da02030040c1c0000903408003441c11070703d207030030069401c1008006224464141500744100030100c04201070740444c0b00d4540c8480c0c100c00843d4038065000810901039040303841113030f1046450741058900365004440c1080069804142c510032400821031a5a4003141c0100880601e1824090111440b055030491400380c200307440 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 777365629 1250 777364379 777364391
    0x150309012a030b06070b040f020109151d06210604020409090516060503010f06030b1f02070f15050301050904030e12070e0a0207080702010c021f0c060c09050303030a11070213 77
    0x74000d8203403892035040c02d000d50700c2000302c000810b41d040c1540c1e40081c0d00401403100a0442e00040b00c0140080c0c105400800414a03a0105150800c100012030400c4400b180380100600d000c0020b00d0141c00384c0c0a448211001302e9103442c4080344c0701190700581c004e20041c1051303101c0c02c0e0041103d5195004a9181d44203520078151208030b148140014030b05031174414919030412120341c072a01a030380304000506d51614003004050383c0f0581003d4402c1e01102c41e104032108001c1000f5511820f40c03088410721400032401160344040d013021903241000b41d80f1281e186902c0d100901c0007990005206030b08000c110030203080503503501a049054540250014904103080c0021900c00d14409805018041e01c10024900000c03030030380a60b032040e07409092810305050b140c0007040784640340c68650509200400703441c1003c10342015280c800720340114010005800c1c541016625020b0900980750305620034800240442c0ca19080010003101c203c0805017001b929a021420003200c03240e40c2060161504 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 777366879 1250 777365629 777365711
    0x91012030305100e100909032c040e06070507030c050f033103030903080901090902030c0d1107030207030b040c03060c08060139050c09011203120b15030901 69
    0x510020701414256104e502c9a003070074490109102541d100d41020f5603240d01010341850f0140021082940d6290406a0401c1d44144802c552148140c802481949446101803503607200081c014480d03034158031914901941a181580c80482c42c0c03800701e5852040c0f004030741c44a60144042c0c142081071080d4059444040c0001d02d002c41c01111154140c0c015100c01000130a41c804038400c11681c1003900e255035034180c01d004960401c5d894000218a40c000000e00a100442c8001000760038551b9030100f00311889200c0180c100e04c1110740c050016841410144085100b07118000d8105104025030103641e03035a0359802083d01c982c124004085402e540800c0380c956005201c0208040401c503013000c100a40e203aa104203d5240400d80c0344140d2242c04103420004100306035003000718002d006210030369556403040d920130000d002c11000103a1107443e20201c201c0318050000d01000040c0100210301203415600200c0e08001c015070500d6480301c13000c111642c0614503855280c00c410a0900c0007007084 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 777368129 1250 777366879 777366901
    0x11190312020c090718030b150d05060702121201090209060c0604050d0e03060f07050d020904050405061b180907090e0405061b04050616030c050303010b210c0702091012030305 77
    0x920010900405145009205c0c100b0201c1d44140c90303101800006640311074030701d81911040182840d40000d4140c43c1072051101c0011a41d01c218810344c00c8482202e4459000385990048030a2084d00182c4c9000600c10801c00c5d40140c9502180900101d00b0405141d10303280c41c020050714180c3c0d003500102c1c0001300300c80d481200c00f40021810b600600590420401030607a1001c014150001c20201007030501440a050701142d0780c00740000d200380320608103414040c0e2a20020384082c0140d00c803080b03002c2e60704081034043c0ea0b40655104808140142110107100c1440d400901040c1004803000c0007089065100c0c0d02c00c4c1c06903014030010907440c0b40c1003e1140040800d80318680d01208140030030011980c0f42c404035a0030041410191107610240c2c81c09031001071641c00c3c02421070102000100e1405400b10281645162071101fa11621403c041e629105080594500c2c41450041010b84054146001c21940040c03000d000c0700d22082d610350045880026416040f00065102d4060220824070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 777369379 1250 777368129 777368131
    0x3070c14010e150706050903040f030303060806060102120d05060103090c1211010503060d0f05070803040608070f08100b03060d020a06030213091b120605150901081311190312020c09 80
    0x2003038501220f10103000b084600d80740135000c07000b05481c0d16100098000413040c425500180303204032410320140d0f124039024014180e40d018111903882094000b4210390f02c0003400d40c1d1182800c032141880c00810034010b03405404010304140c10f04d501c5544650005016140501c0140340d00e103620f00038844285021410100c00740c000d10f04100017402844144c0d91001420248994003600450259071186000c43c05e0034400e90040c10280000306002400036004940c01d40f10742c0701e40d0307905031a20700008400c0d260480c003034480981d000d03d405000d0209415070001103800c400004e00e000103201c0e1030303030000c7c41c001001c2c1c100c20002034005c1350300c4031140b04000c4000050000020103010090310641c00311441118220003000308041c3d07800c56003466041e0351002c0040c0c0b00187c01c0c124030805e190204039036507020407407542c00503036028005114031180b00660780e1030aa000e000b0140f00210a410005e0303000c05014907201100da14140000000c0c407103c1100110f05035030700900005101c950400c40c6040c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 777370629 1250 777369379 777369407
    0x2070308120406200d0c1704030c05070801020c030406031d0d02100b0609030606010509060d05040503041502030c0607050c2806050907080303130c120f060f18020607020303070c1401 80
    0x8003a9200501040d04c1c030050300c400c000d0351000091146c0f62004203c40c95090920300e000c020380c1e4a8207101c20f140d03010560044507409201144c890301d03629400c0a00301d118010205509800922050111910030b40101c015900c41212001000c0104081d21703041114032500c1c6005a80140c0d000d010002c194000d54428540440300b00e402c01c1d1100340465140c00005005904200300003903800f00540c0c0f02001d40b17034142c1803044100300d02d24051902950726403180c00307042c491051011101044c0c40c0700100f15640048000d0243c106925003803415115608200c0180143e0301801024001307132000d201801034060b00808944680704454281076040b150301409080c0c2c56040010140000c0000208480d0072a2012080c00e03404825030900d14102440c1d50054a540720300002c3c80002e021074020b400c25014068181008042500e0b1800030445441096806201c2584d00900016142c502c018181650010b000e1701d00d44221551004005104c50b0450300245103414060003465a0001100c0f500c02 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 777371879 1250 777370629 777370661
    0x220c030e0106120615080a03090929190915030224030106080a0f05040305120105011805121203090f010c090e0103060e071e0504240e0702070308120406 67
    0xa0f007002103000c15100180c02c00f50070789440700400146181901c840310000c00e1000160348000240b407400600f8140b03944928500f00d81000c000c00b07001c9a0320141500314100011110104440240a01c002c45e565400359202c01040084001501582402162a84690070190300030080c254410041e503621010001c45200781480e00020822009101300d9054407801d0809007095661010300d94081c01c0c140b0240c440540c1410103110406821102810500120045030345450382c0702d10044030348564200c00003100c01c200d01c0381004181087c0c0000111850f1001c16184c2c1c064040c1d0700a0b07503541c015100301445501c06120300040b00703028032410840174000d1810f4146035160604d0f800c10510103001c090500c507a500c11602600c602004807000621491001016018210300d4401110300c0c00d2140600540c10548ea08501c4c1020512202c500c032803a01400e0049820501100c3c0001c50090a00c01948600d40f00400420036460140511503110164030030702e454240b070010103585280d80a1481c0c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 777373129 1250 777371879 777371891
    0x108011205210d0f0c0e03010e030301060f031b0804020102070b120604020d1509022203020303191b1b06050c150901090b09010204031a070504050906220c030e01 71
    0x10380302152902c42244010864a42414200b601c003099100300740c000a406494489060226001030300104583d0764a500c40d4644611004281030a131440d800c281a9036810800041c0700817401a0000194514945800180510074001c00603410000d404680301040d071000c20003007150ba04206280207402c0700480141001c4100c0c40010402002030034052040350046490600450310703900800700310328803075404020700d55a042124002c0d4040742583e03480030001c003509060204800940c00440707174050001e501c0d000c407440407141c495002c0d4003040100884000d0040e60310402c40134500c08103008001c0c510440e0b454003036070845051031358092400c0c08400c0c040b201c0d480301c000c208509001c0d1070000030f64041c0c0c0d540302c1081c0140700c604c00c010003041211040c0300340c0203415030191060300e1107170001d40c20024101a40881c03c0c00110340481c0000c608210600c5a410088200e540001c1c001d00805c6184040410440c0c601d00d03540500c0c0c8085a503840c000c203070703542d148c09a60700540d0000000c1001e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 777374379 1250 777373129 777373133
    0x6030c03010504151203201e1c02151302151306030c02031903020906040b120702070e18030d1811060a05071b050411120606040f09050a0f0e0c01080112 67
    0x1d0b00780c06070406401e0014044480480000150b4955107080f07400050303c00e05034100305004070410352304c0240300c51481103102c90340d00069400d500415000c1580c004007150b6041c48150700340c0c00d000400c994043d00c01048a58016203d1203080d0060704000560240c07203030011400c4560704502036000d6030804d070920122224143d004003c84901c02c2441c58840e001017400da801b030780a8802c1401e85504104001000141c0400304005028584018281d41a00e0380303842404030303900d489600400c80040f8200002c40c2403000690408604800c144082d00e007070a445070550021500ba00c41142850071b4542e44d41000c001c1c6000c8101d981207401c0700c0440c01c1889845c030082140c01009002400b1142e884c40c000000d14000403841c005180007082481041c0000000c0800c6810554481c0a24411180400c0c224034000d0296000e403075154105d502940d01e024000e202520004e447c444a0f50b03a0380c800c1c45a9603449010382258017200d8001400e001c00ca0500041c003074003059201006401d4002c40e4000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 777375629 1250 777374379 777374399
    0xa030e1005090f03010615020307031205011412071203080a140103150905011b05120c07030509152a070501021506040e0709020a080f01060507021f0e06030c0301050415 74
    0x1940720041c1c80a071040580100828010107107604501f0b07000741060f001185480d070000062101b03501c00d2740e444d207500070240ea03003c041e120b0030f000e408410308020714519000d060805a21912592403001c45002c10354403565100c40b14040c10047d80051590010042e258a0b58051a13200c0c03032000c030042c1815891030301e807a00c2d84142206800c24a60312a0300c88030034402c0941002c10040c1415602047c00b0400000141c85940600d0201c2124800340c400103c3e842c20010658403029010340320751b49404450002c01c008120b818146c1c045d4400107108822400c00d0700040d8a010112074490f60040c8d0148214403840c1000d40d900090440d4400307242d080342e50840700500b98201905035008503600d200c07904040d0400c280b035008019014400704d05001590345c4580443d005005207000d10320300340d8a62500329582d114001006c0d401841264107455940e6199104000020040c5800000c07100300000080c03482e402955616282d100100c01031005190034802c0c000100fa996889414103407400b40616 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 777376879 1250 777375629 777375637
    0x5010f090501140f0f07050d020a0b070f050c010e01060f08120d021812101107050303150a080a0b040204051807030b090c0414151e040f020f0403050a030e1005 70
    0x103040224815070340410603c10401d64030030a10714a003094850300c40013500140d603004003409030345611803000418071550001c210708038a00e41210348920a81d0300d1040c00da440410355000c1c0320400c2400c200354190a01d00388140b110081052001064080c91700e10500428600303508172900d07642158240d0007070484e40ca4101c9420710380c4040c0158540481441c1d010000d06e00d01c0100d60000c600400104d40040c000c1076400302c40031001c0e01004411101001d0248602445038001c1c4994420004611812030084990340d0403a8000c062000c0e1303589555485050400ca8441124503042c0c050a101c1107280a008983d4004050030b10440c100003080805980d43c0384510000d48a499100c02141c004c0409012162000101074810300580c0003806140e0803100044a5101c408807400344840014642020310101441e140040b1840c2c003100d03101000010715140000061080e400c11048001c0c06001d406007000f10700071000750940c0c015900300505075412101c501840b55075200c041e25251500700c0161 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 777378129 1250 777376879 777376889
    0x1003020f0703030f020f030403110d021506010c0528060e1b280e06040f09021f050706050702030306010f050f0d050c0d0e01020415050702031e1005130c05010f09 71
    0x1013000b8610800c610028881c43c1d6031130b0300e046000410030041c0742d0032a480e0709940344980e045560402c58202d00304d850b0700b41c0c480d11072444403030080407031420342c85a86084d180b0350048040d25980c00c0c0e04030750000707190182044071942d908440500700031700c4003602c01c0c07040303001d21400074040e07404850000884121802e4821485908008000a1030b510941c02e0b01582003440d0140b2804240c43d060102507050049581511032030410a0b0300000c00018000c03424241e40c050001e0420102904124913111410b00c000c900704141804500003060075801900d010b4041c41e0086c0da030301d0400800041c80c4410442010080c00020011a6010110314086546122101c00e0000b0280c4070389a00c40254820703c02c40584413410103031180e00924043d8001c008031050031524000900c1200c0041d20503002d003041c040e40c941c0140d020907854110f1110f1039400c806006c010f854280d42642c03240c00403201d096884101113100d4000c104108240d001c00c0d88081d0a090a000c034161407204401842c504146c094 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 777379379 1250 777378129 777378131
    0x304030210050a0f05012114010f110706151d130f0302060906130f0b06030a02060a0914060c1015080f0105100e0705070303230106020307021003020f070303 69
    0x4050610900185440e900030400900203403c1c55800c0e1009421461507900301d99241c20700008154150021704416102d64401c4460302070307140d1325580c80750400105461401e549859a82d68018000d2099038003031416024003d8131a40356082030011106010b803c5404d180084c02c0a01c0403500400498000b000001c42d50142a51214046a080a50f0b40d00c0246444146007403501059008540240714003545021101c036985c8a086180900180341c0c0041d216101c59040c0d00007260180444981c40070018040f5a9428500e5010406550142051500041c402d44017886074403039403c01d10082c078908a4540342800412050140c071610010b1400c401e0680e240c1035030303900071701001d02c3c84002c000700d400340c0309040e03104071410380a01421a40c003541182508000b090446590f800e8900410ba03954800d8141180c594041d80200802202521842d19a507c9200020000400b05010700310990245450f81264414041e00c0010014004185801480560f24050500b003c0c0c550164040c60 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 777380629 1250 777379379 777379381
    0xe0607110a03080301060309050d09150e0301090f080a121b08060d05060106020f0106080d02070308130302060304030f020613201201020a20061003200306160e030613060203 76
    0x15841d1601e503200408110300400000f9031260550f20031091503004801f43c07404100f450100300e44080450140601c8841d0911019954510480e0b0039401440041c1c0006500c0803c0d40340c1c1305064801e0b42040320807070800200c00941940c07045260b01f001c8916030050141c104690220311040f003040050004108481c40000c50715614421b0050380e603504001501c142d075854400094485d90044007a040b03130344c200400010001c00005143c03041c4100703680540a220305603a600c005c81e40c0a9801401502000304011025039075040056004600c252100c0e802107100403406810180020003507910b00c00e030208034002042c10400c8019071070914a0394800321300d085c180001c24521400034104142c0d840411001c85a6800c0090180c000ca0200d1500c500004070850b0980c0c1c580e0101d84004500014401c20400500c20b40050403c0d441c150006000c4c4480b240c002c24545a821113820f03100c000ca800300d01030002c0e00400800840701c0c00340c0c017402e6903141c030444c0010381070740c0224001c2403071b81c3c004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 777381879 1250 777380629 777380663
    0x3020d030c0614060a06050c030a0806061b0c18061012142e06020c0603060a030212010603110a081f0b0307030b0105011701150f09181406010e0607 65
    0x445450759840941000552001c1c108201c400701c0854005005240b040c80c08500140520182d820740c05660000707600e040403641d802c0b140008060320301c50700000c0502c0034000090480303440048100130b600045c4880c41d2000108004400d00240043d01014160180649502d4009400c8950722441c02c140d03020000541c1e00d45c004042001e20744614070314000c144034421116410401a14000c00d103455181c05c80344032400d860042a120f0750000d80d20042c00344865040c5140915071000c2c0c014900312049030340b03401240e80b00b400b042c070a00569644240600c01c01c0b4200d60804111001030302e5038103140742444109980c44800746140610300c488030050300005000781c1c002040020015003500c07003003a568901740d094250b082c040c1c1400700d008480910340260300032080c24100c854002400f460380071203500942d66907542e82c48200c10800c17280408a104101540c02d0035a284d01c108000500d00c0100c80c1541d020000942a01d040010796000898155103090940d00f02c0e5030401c1e803d8071070311250 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 777383129 1250 777381879 777381887
    0x150f0608190813170111090913050c0a030b1b090a06031a060a0914030a0b01030b0402031507120e030405090402130f0501090e010b0d0804090221010308040602101503020d03 76
    0x861003c10350010a1a000b00e030240407080c2086488921600900c000142c90401c840b5070300074502860b801c944043c0010b02c68005100425000600072000da030143c00741c210105458956a4009a4180741d40a007444841030081c801d04083e5104440c02d582465032031400550b111600d4030590b0704042d00d8070f12240701450700120403840d2000040400c1c0da00c0c42c0c1214050300c101d6043c0f0500641c07c03041c0c2e20000c0c0b40c2c2008521041000d50001e2021600da09540d11400881c0300504140d82500c19081e80f02406125119051300542c403549504403c100b11645070b105407031001010000c06c0d00140810000c945030391103255002581164505c001c0c031703244c40140c8020400c81580804060a0800028501005510020341070607100000c2c00f141580100384105142d1010008104d49000c0008002800c031950103003c03129070801124240580d08070484c2da650800703030016a420b2400040c01c100041d010044803564421110040c0030b81440b003032110811504511010b130285001d155004201485 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 777384379 1250 777383129 777383137
    0x904050c040e07140d2c01061809170703030e100e0d0201090507530102032a0c011e05010e010f0911040305030307030515041808071e150f06081908 65
    0x4044105000381120401c07180c080d0046201e90b035030703480c5400c0c0c41c0d15207142c00340148400c45801c0b08003500d000d0349000914035039a101338820340806a8540f05c0004500d014000c03954946804400884c2a4001e540203508200b00744201c6030039603141c582110005480801d50340d007110801c180c019801041c03500c4200b41d007443c4510803020b160b10f01c032084103a481c2c0c80310b40d9106110300721407095444c06005840d40c00c034401500d04030b1240711b0044888414000009540c01440e41e1280703081e06020310001d40500b90342180100c0c01d60240284024082440e4a103e00303801807a05c5181d8407155403401401e4a21038500d0702600c0000354031062403400d00714090301160005d40d03210044995920f81030100800400c01981c4800428844690a42203480c10b40100121000c8220511781c0034401036654064907404404100c4000b001c0210060740041d104013890b211500030884d045602d50100e0283c03046590000312160001d00d0b04005204071140007900645220060181d00b65042440c20300c41c6003809 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 777385629 1250 777384379 777384431
    0x60a0c0e09130b0a05090d1d0d0212072c040336090c090608060f130b06040b030406050622020d060e0c040801140c030c0706020904050c040e07140d 65
    0x2260010321000711030585c00148110010415503009645000040794446494020400820780c60000c074002840c007503d01d40000c1c0d00c000d2400d0b1484207207100c4142041800d6100c020401c0c5855a52080e0341c809001000068045c06260f56180c030307180c2d274040c0c16130704d048500900c56100d10541c04c1803410340d0340c004026600b085d180002c0320b030394400000026203407020003800020120040000d126000364000c0d07018007402488540d038100c00d0001d100c404030808103269801034031880c1a8509440e40001000980800360030550381e460720f4180780040e1200030b82401e0003070f00c420101500303c1021040700d40007503103911405691342c05c40c0380300b140c0949044d4011002c82c00c461002d10a4081c4240020702c12140c0e154021b206d04800400c0219a0100884240d01c001c1c00400004041e95503031001804c4891050000500b0030141e00c0c080b50482d5000c481001d010300c4009414402d09003240344060b070007940c500d0222850041a03500c100d040c080d1a03925406207841d400c9084400e40500d10300c4070856 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 777386879 1250 777385629 777385643
    0xc1d0c0c0102070507170f0610150905090403030203010314030403020d060902011e210605090112020a081504060506030a11040221092b020a110a0e0a0905060a0c0e0913 74
    0x42e200c2c1b0100403001e0100315043c045115403003d41254220100342c00b480386010890188549107026a11080754098610380381c208507000d84003217620344d134188085018070f0007030340d0058580d0704500c0d040c03411184ca07144405540e80b091101704010780d80e02c1030701220a41d00c12000b00e45075010f440141d418481c00c02188982007030793b80c118540c1640c480180c55500064a80202c00d00400210340022113100b030003819046803c1c000144400c070000200100003d2015005407885a59250307a942858001301c5400c0c6c2a01750038050000740701c202c4c040c554000c18128040e140c90f01d02c680c0d0384104c3c1d10840c61000c0c01507802081410140d207040c0c05000c1d01d034a01500d00e200514010081c035846150780c4004c0d42c804201e1041446c5c0c50402c040f420090003d00740c00400d07c50a5a460b200958020754007102d5024048210104601c2c1c0740f0009107006042d04803000c10f02c07000034030304207040c21801440e4a5200b4608000c24181a0380482200d240d03d00c1960483c01c82e458640c02012131740c1201001911407 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 777388129 1250 777386879 777386893
    0x30c0a050d050f0f2a0307090b030a051504020f0d0b0a1512140126071a0c010e01110f03060d0209070203070303051b03070302090a08190c1d0c0c01020705 68
    0x72050500d00345201c4d6021310240c0b502c59a44400e4410760b50341c14a5080341c468100280250380208040040d81c110302c4908082100d541e444c04882079984c000c4031000f0040c0d440340140201494188500c9804410440742035091813940203e1502e680505800000b2554903581c2946140c0c4070540c025000e0140c28840805d01d41d16100060502c5c8400d07040307150018a1f07c0c01402c80349881644c968140e510300256021080080010102030350000303210307100980502440060300d05805410404465a80d600b40c546400d420300030182100e4004980080b2079041400070204107108108482010b60901780c00e903242d03121a00818908020180300a42158402091159207500003002d0001c440c480c0c0d0b418041907450b0005102c5260310741a00c0c19010f07400f800424401402500a40201075001d060624617a5480080515005a010141020301070201c80c5c80d00f4408007060740c1016048040300040082031400300468103d40040140e0420140030640c4c0803c2102901202c1050341c01000b11860 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 777389379 1250 777388129 777388141
    0xc15020313020f0315040201121b09060f0207050f1c15022706091011060a0e0f030301030206040b0304050a06050f0a05070e0d06050606070c290f030c0a050d05 70
    0x305203a1079105034890f8100301c0714030105203030000d085035252440c05508800398a4035401520900358800c884005c2c507858500744030b090a00701c84500c00c030841643c1c030304900c5454280042c0400c0c1c18460322038115000180140203d440303490b21420000f00544951310122080e0408031180214000d009000802c1c2c6403c0120240b9260043c00001d262030040c9070001090482e21114000308640068120005100e0490146040c202d1101c0b801d25a05207070f491880340d0240c1c507080000443d449620750b580d84064842e9450100400c072004802c1038010340c03541d415500081c0040c0168416201071aa002000904004060044903203150f842041071013941070103081421911400ca441e12521460a40003400e15481000300305d4401c1d0000d411f0002d0280c09480701c201611000300401d400040410400000501c4251031130010252220007407080742e04081030140d400501d4205601030071080c40200850b8082908a81d0808000f4102d40c0e55002418010f5400780611802008203919120030004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 777390629 1250 777389379 777389401
    0xa0315090e010c02060426040302091303091202030c061e0a090914040209063a0c0f0609060815130209040506041506110a0b16020c03030406050a0c150203 68
    0x11007101484000c2c40703801c410701404c903178543c41100d0240c000000c090b035101d802030f0721050102585201020b001d281a44a4020031042c03a03098031418920090305640006250380251481c1c05002c803010102901c4a0503000207036280c1d0210f40030340c868140050b0042007a03070742030041e007910160032018035240d40911a024000078402e1048400490600364840501d880b0404014407445d4010810b400e6611100180612900c290a100c03102841d040c00100701480045c2110b1460f42d58030108403032070003452400c0c0400b1885035000c001481c0c0d80100c24051950002c80031802d4540c0d9207802c083c43c3d40c0d00d2020700c0d0b80090b10040741b5080200341820b0b0121007001c1e002000181c2050742c007400a40c94900500044403031203101c1c460740d00c0075a501406540d11400e40c00304541020011101011007507128401d02c401d05030385038142e8070b10070000010030b19014004503140880c228055414a490220050b00c2481140380380ba0401041402280402498010380340303850000c0d0900b1501c900e86101c0310300c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 777391879 1250 777390629 777390641
    0x510080f060709090e0106030501240803030f18010b1306061706010210020706060914041502070803221403090f0a081b0a170d110309010c03050a031509 67
    0x44140034004040c26818000a526070080c003540e070f240d070070540c135142c3c46200400d140c00a0102c95500c0741030000105109000e810701b86010101002c0c0400319960306005008403035401150303141c1080c01005500c1c039400641550020260740d14010301c940d108180e074010f01600101c183c0c0048001e58a004d050141d43c0100261641a120501d422000c00c042510b11181110300700e00691100103080131801c503680140080500c50755000c29069219603136030095560407213140794030001400400041c030000c100d03007406e04410b060b0210b15101c440d0b101d6102c0c0d480020300c00b02010120032018403103410074000c41000c4a401552440128070780b05052916030b0f00080b181403107200c0329020080146801c2854a0481c2c05207001400300860399221400b2414190301e100b035000e400e410002030082401c370201c2900c2103803400a01403203030700e034440540406000c110844007030380180300803082d59811034101184e036501410015299002d07194210050000d4035401c850348903000400140c1c003502d40d0426 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 777393129 1250 777391879 777391889
    0xa0e0c0703081503100f0f060b2808160903050a030e120705090412030207020315060a091b1218030926060106050d0605090f0411090112080d0f0510 65
    0x40c0c80503448243c0c649102c1c102c0d19159540c95080800c0543c0020001e520a071469822103101041030310990001c02c00312001648402c924040c006070550703414469600c0740c14106848044070850a5040400a145010050440c400d1045403130240a080d1300500f4207900641d40981140d10303070403003450f0080c04c004002c01c040c3d000d85d01214040b8046040802d1020503914050006056551035480304820b0b050301e010b201e42070550030000d502c00b6840c00d100c1842500880b0b4500d62580c141035042c480c82d1100c590040303500a1414000103905825104001960259031403c0158140302c416140014241c1182d01c4041d0351420022004043c0c00c038900b90126484540c0801004854461029030b80225070384c8600c0c01c3e0860f83c010700015024002404500700d80441c00149643c403480443d440c4001651810058440c510410003080400c000c40103886200b40ca5149540d49480d060f510020b220003001005104003050380d0380000d81540c06004400f084507000d00c1982001e6040012030700d0b00d8094 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 777394379 1250 777393129 777393137
    0x50105030708190c0506041d0109090f0620181e0a0e0c0c030304110306060f010e040b040209030a032006040b04030c02120d0818010e030412020a0e0c0703 68
    0x515190118100085548241c090000800640c2864030002540c5508444c0b800a10030080b901e0b0700d584020b0806010400c204406140d2080e4080c51240070503408100c0301c2d0b0419241500060701c03a02d401c0381856215001043d15103c0503e01400c1c001001d858012420002c02e4003c0744428401e00d204111105503102024020400240718016881c0202e9a40102c10440204030000642e07520755440b046032070303c4500701084421030307a0459005031810707290201624221210f51070103002c103030b8016004030b401d031465404080001c0e014641c0d0000180c880d5903601c280c00025103554044504240c0c00034240c440301155490040c0c4084120b1602400034100c2e0718455481340d000003021400365400c4a2098850b0b500e03558112401307069a0b070101e801000c50140d91071240e0381008070004404541d00d80c2100c500c1c048000c070107050380408a440e0130ba810b0546008094001004480594500c1d1304440464950b40c004a16240c413981d205040d205103060402c01e00400710005071861a200e65a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 777395629 1250 777394379 777394381
    0x1050705271f1b020f2707080406061d0703051518010806060a0e150d2906040212010b0f070510020a030506101d030c04090305030a0501081f090804051003090605 71
    0x40741c0b0300e400c1c420f4020b40003038040038065480d1a1001014500f030750001010409004a101d05130350030390007a203205010506210034041081840e0203680081d1080b25141d040c1101c0340c1c00300300c56803040500008241907507000410350841960504055000700a440705507105e90000104a200d1400d220394851801024041040d0740b51409101c811a403000c00441d421340c40b0b0312403441c001c0c07101400365a40a1240c40c0c06070002004140920380d84108500c060711014a4020940c1602800a00c6148035601c10040f800100142c5040c0d01d0640b5081e032811522081c0c1320b44034031100c1c85030040c060047d02c59445407107204c00854005110740081da82d800c0c052a211001800060b400024605020488905151070300c5140000740107108080141210219500c410108084440c03038403050b80000e40000c01c10004510b036000b403600411502000748800e00007455142e000304140002259244c0d00d861144050280342c5c01654050070b0000c00c0640701e00d401c450050014440c2c0201111b80c50f00f044 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 777396879 1250 777395629 777395657
    0x4150305030d050c0c03041a09120102070209090102190806030a0605180c0d150513061505031507080c0304050a05010c030605030d03050405071a0c0105091e01050705271f 75
    0x400c0d200324045d01402142068201070000425500c420091301244906220000e080d50725034101503991180031000503600c0d1614014840300001c0280b0401d0b860b80104010302c03146440e01c400c00380341440b85c034140d00b06071070f03600000c0e007031440b0740e03801402660410061000f228510f10480f00141080c60484024040e44400c3c44100010358902401c0003003003002d40f680d00707000e41d0000350780300d070626841e000d140384560b554408403400005070019a8000703400500c014141040030b45204600304190f116180381c614402000c0050092034071000c0c00020010408100741005250402caa11200074041c402010720020010840d84c8112446803040702c0180c44403a0291060742d0080703030030074040c0c01c3e10360410241c0741c0c008440001e000000c0500300050b11580d4002e01c00d0600448450014212400c1d60720340d40044a1001030b1040840d916150501a1041d0488100d4400703c0464041c8940c9a00c0d00358000860b0701c074104215000000d403802c400504c41512840c0040500340d84030058104964 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 777398129 1250 777396879 777396901
    0x30a020721030806010e13200f030703091a0405060402090106031e150504180204060b0f0a08060414090706020d0509130905032a070b030415050604150305030d05 71
    0x10650365074908101031160703400b1a2062a078550311680c107040c41c614914004004c50040d40d0701400b85910103954980b0351021f4001b22201240490041d0b00481c14440b42e22104102d611000e07051301c0605541d10303050410000f0405c9604d00b03c445400c1040d0070340c90141029034440c4421502280b18020580022900324064491680d040960b104219806070524000d10300601e14003200c264003005422001485540f180182500e49034500c080c040308103240d01c180001e0350350f140c0006012080501003440e41e402d91000340d84c1704075450714001d02d560b1a2040441c0040c0083c1c0e998441d070324140320030002c04540001c4d60a046440301c0d030032501c5611000c80204c13428010b280860398170161528110700e94044542105901e5801141a0381c941003003000f8550240700301035210ba164001010034903803050005e2100360f00610300c21800702d18619140e560410024140c0c0d184021069940c0085580c3e915103030f00c1014060290030340c0003030603500c0741880c0d0355a0b040040031404443c10840001d0b42c170424 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 777399379 1250 777398129 777398159
    0xa0605101106061915120c0c1e06020403120c050d0e030712171b0c010906080604020714060c07111221220914010e011404140702030a0207 61
    0x803801422040e160f1000700b011860000510404102c0e400c400820744465040c1589034070b2920b61a41d40c410691343c00c414081e202c40e14112000d1010982e0980d000c15180030282d480720160190302450740a5620382034009000d9500003508801c50303401f0701020070390019410040300e80a5411547c0440c01c08100700c9030b00c0c020041681d05508903100c00c001c007000e00c03980b52458602c100300f00d624030008804000403139003003400001d10812280c00112179400040c071030700c4076014081c0f03403038a200e909100d8080c000310b4001d011036001c0c90380001d0354418020f441003d618400c3c40300c000c0c0c811600301600388101079080707484191001c9403079a840022034500a0041e000c500300e014050184401e01c0074403240c0c03010003804240248501002070400761400d021541c0d942000307441c0c078008404e081040d100208c0c0ca81d84040d01c0f0038000300c001444002c01d104161411109007900c4025495064000710780a40501000700b0001c01951040c0450703640c01002401924009908803001145c2d1110340040181d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 777400629 1250 777399379 777399407
    0x4060b0f1f030e330c030c0304030512070504050414090a08091306030302070f06021b0f060706060f152307020409080313050106140102030412030201140a060510 71
    0x240340800e8a804025428540084410303500700015880d600c3d64400d41041d80d16080e5002c000c151040040d100110300c07000d004600c0760304d001800c080c41c0040c8850078600c000303803801c02d000e103012002034201446601260800c0017122410204e07404c158202400f240c003c4c4c002d039445141484024545070101c0c6494901c21035400c001400c1d4100b140c0c440640b19404080095002120700703025000610300f40c00342c4c1c0001c620036801004001e150400310f005200c9a90001400c540080c00042e11044039250342c0c00c2c1c00c443c2210096120107440c80018409e204050f0002c0c5075505240b0002900b03e600d464101c11180441c0300c802401c040782030110382030303201e04140d40c1da0a0b92085000c00343c07601c41c0d4041c103c0300d4405440062140199298071007680c0003110000001b14941c4043c401700302007030044000405082034144c801c500c2400003c1e40f00c2c0214041c50350081842c420030000d0510035005000c15240c05070100603941424190013004d44440d0103094050740b68940c02c0000103129003c009800c213 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 777401879 1250 777400629 777400639
    0x106091103010e101a120c0c0d0f09090c12060b1903090204180605040317130b22080409051f090914120d05010b0301030309060f03090c090504060b0f 66
    0x43c0c00d2402d0ba000c0400081d05050b401000c2c1c080208100500580801d0798000b442c5656440d1450503480c02402240144005d000710401c0c0800c0e0f146150028180081c559541058082a004000c080310b44260560000b19002e080c5010a801c440d00000c160000040030349081c001151184000c0d07805100b018110300b205000070b003501580501c642c1c40311a030207100603c00b1481a5000c52440741d290300d0140c2c26545a6070321821711040540040010210002d04640500c0c5864076416159480e06101c0000c8d00d0b0812000004801d00e00b00241101440d2050740e20b40005d1310581010041a0024003403141d0141c070b00700c080f401c2411a206070f400d1104071246c0300b64410341070410303440c090510858122403000000c202041c140c40240110b0b90600c200801413600c03402010110070039a10183d00003200494200014008264030581c02d80641e2014104440981440441140207000c4124050a502009074012940b4401070700014040c50062300284401c0707140204214420040034450783d404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 777403129 1250 777401879 777401881
    0x60e070503041a07080124050301051e04060608061009081903170a1e0603021c17070c17030c21091c03031d060406090f0203030d05090106091103 64
    0x80c0c4564011603100b8810303520840c044008241e00403940000740e0321a00401d1180340140013240b0000001c001e401c0da4400c001a80280802002d0b03c40d10060003500e0203514045500210304041c0406400041c101420070070011b6a6400020525101036484500c1640c90f083c1792141c03244512142000d449070600a0a4120010000342c0c008941e2103600300c0034011304610705402d8050403040c0c0c510602c8500004030780d680c903041c0311a449880139400000d11528000e014000b50b2140001d02c54402c10300c0761801d5803110241003410803035407400d00d03502c036100d8006a003034100601c2c081110b044400444031070703142031007031200380380c6900858600002c50303801001812404040ea01500c0f20070007040a0b207514000c5407001184104440b0000c1e092800307078400c03038402050352600c25000b10743d100c0304001030503140004115468a0000d031024003a030380c44640410610840c00202194168001c045941d201c0302890040082c1000300e412034920352801e03900255910080c050b00d0402c0c07820010b0700d0302e1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 777404379 1250 777403129 777403141
    0x50a0e0714010e01200106090e03040623040b0414090105010807052208070f0503060601030603020d0f0510050415050903390a08190912020607020d05010c21060e 71
    0x8280c810340c80f0396042008485c0031000741c000815074500c510b2210400400c50758184080c0b40195911000302030380680c805c100401c052070340022200300d044100248691480e42140c01200c85005a070003040302d801d800100000c60003280e80410741d13600025903003001030360703a508011b440c0500111120300100c0e4081003042082c148110001c01802c4040552a840c0c40d20b0b4107400e1715009142c0c001d8200c0281450041c0414a000c01c48207030300901c02d103014001a0300b182e000c00c14402e41d001e8001d111801485102007040400c1c401d544000039500c404025a00c0d06052240c006552413512001e00c42c907240108007a0703040801180c2c1380740e2200100d041e03116118005e0644203403580d183d00282c00012072600c50710b5a4140038015016003c1c0b1050398039032042041c4000341001c20341a5a0502035465410003405c800c5132402100e4640480c0c00c16102c89860012841d03541301005d00070720035481c0440030039029401c211206100e448540c0c090b5852602c0e048020211b40060043c482c04000c50302c0017a203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 777405629 1250 777404379 777404387
    0x1008150105040b0a0e0c1209011517010e03030403050405100201060812070f080301081c0e01020a03300606091403061b04030c06120b0613060e0a0803040801050a0e071401 75
    0x10010000340c600d00100740d6401d6541217001d41900d00b4800711a0008514880c0f40d400003100f5000540340c0b00800c214486c015115250182e140700d401201c19814488100021003940b01c0b4a0300d80c5100144d941c0c920b041d1070300400d41d6000d809054071031020844602c803120310512401d010750324460000d20301c071450019414180d401900302214240442c0d404000010128000f6600038041c1034001c1c0002c0c800d06070f42401540f5052042e4003044a444049000da0380d00140107046c098250034510030080e903a001d03200780000b050284140791040403000350399a078101c2e4001c0c42204c2d5195a03600d2020786803019455403c0b051503205516034803003004510042c0c1c190011490260317084200c41d283c1640c80c1c0d0354940e0321105501960201c6c0301d1072a0316408000c240a0350030b841104880c0d55143c5542c405810080480c240150402c0010003030103da00354881070b020601410208013102d07110b540d248540c50181070704845038039040d401d11511503050040010540d040d40e41120303800361040302c4100111 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 777406879 1250 777405629 777405641
    0xf2808010515040503010906020903062a0d0e0303070f02070b04030812060f0325150815010504090e010906570c02030d050c03090603060f0315100815010504 69
    0x1401e03110b010000020035503024411080180d00c608001740c2c50b024040c04060601c0c5004158105400210000c86003910f2000ca0041700050595010754580034400080c100825508202d40301307a1100100f07010219030840340f05240721109500303e603a03139074407580c4111882c01180700c000c1400c1c5080c08040e0840c4401034080d0791005020701901000000400020314000421100c0015072040801c507888031180006100c0144c290000d441c404400c01a50007031110400510b003000342a440606042c0b540e2094040740c004080081042c007a0340b003040c4905000b4601640100c07801c070318185016088010111280c02c0d444a494540994060f44000d5409103410b500c44445920030041800100d00351601c00460800d4926912100c0045030380c81070510340100310042205122040c0000344002c04008102c3d20503580c103541640e185d0f02c9000100e84c800b100741c0318199245c0078161040300382c0d400d000d058600c2121092035510702d1958501d03031761b0303110f0550051780c50020040c040144028246074000c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 777408129 1250 777406879 777406909
    0xc08040506010f08120f09040915052d070c050d030606020105060d0f0803070e0409060204080f0a050304090e03070b15010f030c050a0c15140106122f0d020f28080105 73
    0x1103454015510001740c100ca2710780b4400c07950f00000e4882c03415148543d1048580c400e0340b001c0010b16412120209213240c83c1510b1080802046001c0010a0760344a440d0307000c00c20f980642295076003a80706030007401030001402001c00640c60007000803078910b007a14151540607000300f08610041e80300d40700c01031503a000a01210520a0315010528a07850f40c5c071401c3c0e002c1e4018000140c5950030b007180c4e18203040c502502c0301d070316900c040b800300c003c0b44001c81100c04440c0203100020300d802420507854150f001d41d46020709003110700340400070080d01d1261035504040c026031b51070800100010094086441100e2104001001408103401c464041d002c44c01703034580140f0002095510b0440020103607958640a070307101c0c074000c2c0d00400c503058014000b00e9040c0e88204061081c0484203042074403060702d014039920f49803040d540c07001100050310300329160420075803406e41d5512004000000075074028407100e00c3c611313a43d001d00191681d55185100d020320b560fa65520859180000304544d910900c422 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 777409379 1250 777408129 777408157
    0x111030406050c0f04030c050f01031a0f0409050f011b02060103080a0305070530010902160b1b0a0f08010e2716060306170c010f03050c04090c08040506010f0812 71
    0x40380511303841c803c018000031481401034140260600742803204610200089606241c1081d46980e00e180814040d20103015003500c4d0b0360055a18080014081c04001002402d42d0103007098803200520190465002440c2e19a00b040400540c890102d0390340009100203040f07841c0500c060701006219800c4640c1081403450500e051a800689407040d5030707540030300100c4440410903c205140300c1c0d841803c2c0140f442900450500c000203186004020890100030807490f089800211003a81c24114040425030300c1c0b0506848400844000e045460341001e01004591a64000580c1a044003070702ca00c1400941c52003030f4818a100e00c1900004046940c2030740c0e07401000000302ea0280d40d40c011600401d180c4c1e0380415000d24014045002c4071522610005a80151802c48007130b980000418000c0c1002e8600001c40f5918004104020700035904030100c9a41403018481c1400d50100420b8059070145044d100b060340d8584c615010705501d88642c0006404c07003001300c0041e807880c0001e00030950514034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 777410629 1250 777409379 777409387
    0xf0213260d050d091707030905090c041a0d050408030f0c071e02030c030303070203040e01090c02030702130905060a05093a03150b0316020318091e0906060f030111030406050c 77
    0x30350f80c0f0382d00c01d42d0300c3e0b505e0340038902180003028181c1c0001c215005000680d100403841c104402d4588080c07003240a017101d201c1c42c030501d1210480c05003007100e60712880c8000400060509150185a03544240c9507000c0200440010404100d041e10072121402e43c13125402801a0f1881202c907850710501c0000e0380c5c103006820241150391400c2c401184541256409036030f540e402c00740c0e900980841a00712018052418445001494000085480c813a8045a401030351040d440140d01c0070344407071100140700b0700464062290345182508030a0040c600c4409546c8040000501e42240303010440c0c0d42145a912400400d00d410b072039001c024082400c601d404030300c002c81760f001290a0311942c0d00c400f00c006400010408441e01da81d0480c030403c01c0e80d1024610b000301800c010b8407a0055400d0387d6209103110720100f9a40c4d04015204001c00b00991288001c030314001c0e1203a038685604440240c001e0b20343c0c2d4a50030141c41c042c0b1489140003440b0180c2d83c00c5844548031140248002081c00c040030794200 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 777411879 1250 777410629 777410633
    0x7030b19172d03040f080d091d011703090301020309060106180605030f06010309021201200a02060a0903110601080a020103140108061503010f0213260d050d09 70
    0x403190514000d885a5038400c00d480c00201000124035400c0405180d042000d06506202a07034020076071070074440d180c06000d91080022541103205035400003144015921002821400210314030b0110420350316a5050f0540d15040b00300c071401e80035070844c0440651801880070403641d4191040114005040304d090184080c0400e0880c0c0c400d0b02e21910590042c07004002c466072185028254030041402801405d01e0410003a010740009001040e4900700100000c420382d00c00d0380114281900204116012003018520600822140600d12855101d9900744080303a02e2850860b048845143e0040c1810303581e01810344000d1180388011400c0005407004000c0e41c03081004014007810035070026202d405014400901207031200081c0000d8540030000400010f0f101080060b80811500341c0131900b0007002c070001e401803401d826650100b40c40400c01000d00004803054400b51040c2c0030303d00300c4c6d411141070040d120300d409003c4c00240b0751014400d40ca03580c1c4524007801a80c0300b10480424483e00300d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 777413129 1250 777411879 777411889
    0x90d051009080c070b0a0c12350c04060c02010c110630010f17252102030a0f060603120314180712050c0d1a0c03070903020907030b 58
    0x3407026624102d02003007001a03002c050100d14020000201144c1c503000800f0f00160070003060100180c01603001030001149a80200da203c3c55845141c15008511001810300050ba05420080c00e81410358640000707104400c00021207043e100e294075012011542c40e030044944e8500848110341141103401d60110310707190303000544800944007002d40903000c448900080300c1c00c401c24410300050480b000420a10b0003c840030001c0d52260141c010786034100c610702e00e00d05402d444003213002034041101820160f44031030510f010b882c2c5404520b04041000208a80d80240c5000040c3d416003144c500b1400181020418544980c032445020070303010394a4951480c80380c2020800d40c04641c68030301c05201c01d500710555a51000402500b0780030b000504a4070780e07840c07000f400b4030a0710700c4080ca03803101801000c01500722172000c02400903024881610780700c07503040040d40b04044031680c0ca0011690842c0c880040d01e1154000c5d03581d440c90b15242d6020803960201c090319007030916944200e102c100381c480b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 777414379 1250 777413129 777413141
    0x30606030b010e13081c02160b06010905030604120302071e0b06042a0f020106051908010e0d0f120e01140907060306060e0607020a0b04120c0509010308090d0510 71
    0x40e41ca0411550714015048035001001804007825102040d04100001c0b280e40984105402c003c00640b4080005518840280b0030a113614052000c10f81d48a400c12030303d034008510a04080e40c805103110307580c03424507a44500580f8018900120b08a1482c080343c401d5014250030b6000301c171440000300c00d09503503180c9850040415106030060a04100c410b080500a488001d1022041d840020010441c1c400c2c11600304041c41301001309105040414a200350030020180c40001c224010481ca00e40ca00c0004c50762070703ca215820f5083c06282c61100401164440800f8055250401d0302e000c6001d041b00c0a61850307003000040b507036030603d0700c0844130b0920a0845140c021424001e00341020696180b0b04036481d40b1090415040404c18040d0b5940103c01c4202c68505941007600c40318640b001511404864002c0208040017040000d41c80480300181d0f548240541d005400d9503444600340006140240005800c68000700070091180c184000c582c41c90714080d070705032004840403030b24500686203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 777415629 1250 777414379 777414383
    0x905061809150c0c0c010309060209130204031b12030e0a0b0307230903120306040906090308100807060e0d1103160905160e10050702030a080c06060f090c0f0403060603 74
    0xc4a80809800c250080341d2075500700c1c3c03800311024140410201d40d42d68035a0a02c40311030406455200030001c000d090740503501700303481c002c1c4003042d950358030600c3e00c000f500309100668203964900c100e6990f000000300208182c50000082c280c510303e0503141a200441010361154006103403103800107108403107070007a601070340c12942c442c0c900c491424480106036a4009211010140400114000303540009440040c4801451070f50345039600e080000c0d00924500d40c018140b0b81c00d250b0324604040e802000d5501c188511801102c80307039250340d0030680e58a0240110408100304151821407454000b0744e486015200e490f00200900305200420304003061040400b00403080d5031030901031440a0701030ba65015070004452450403109c102d004000f0910034030091b00420180d00e0581285202e00202e88070150060111001010540ba2111a951195030b9030143c0340240c002140b078a251990481d802540010904851034656030b042520075400b0600901c03070140c00700030000006065006100080d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 777416879 1250 777415629 777415633
    0xf1018120c230d0b16030608030405040f150308071707020918011d0d030f05060f0d0206040f0b040f121a1008060a060f2103080a020f1303030212090a0905061809 71
    0x2c240300210321180b01840c5c000304107050521030b080c00055000030903a4115002100c0c00700e21880580b10307000040c20047c001040100c48000c002c41801050001051610700ca00601504039224094041c0c1c2c0f4010600c00a5000e440c02010800320000f8000d000030000d4803c00024002c0c0c059103e0f5540002d90070303549100c68100c000303000d02d855050300c920018440108800e110030710b04400040d211000c0d80f4081846850b500901300190740703130f500589000c2c1c070700300c180d840d0300684403100c400e003035003061140c96940c1c528014040f900c1840340300c0340c110017030b444820300032082d040c040078403840d000c000c015070503c07501c010000801c0c8104101490117030400314000180300c0e0905841c0050789034140c203d42c680e180300341d1226170503000103600c6220f0f1540524000f0840e0b201c950785403000c0e102c0c1c500c41c441204408240b03c0100319152482c02c08481c031a400b194000c000203030150800d8004c4010107036000c01581c81c00c05c08401079422155102400074002010147c1e00520116408400c1d20790004503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 777418129 1250 777416879 777416881
    0xd020a020913022202070804060806041d03090108062b020f01030902100c150f0b090708060612091509071a03040f110f1018120c230d0b 60
    0x507060110300940c00103010125a03400b40c1d0030741c0105140c0d0355801c4206a0607032982e412428070210300d505440d50164000c81059481c6e59a05000f090507100b80e5056214616101d480b0111000c2c2420405030103040c14013460a0042100040d642ca90000f0045600322109081418000c44003101d0742c000621018201d00c80d140040c01403203540c04103407820b241454549030f58074002da501d40e5945218011a45005000e02070503240450300000b00100c04032045003849080600500982c1004008503425101240c095a44131070843e460761007561456040744040000640015642c50340f65440b52001048408866142c203000c0d901500407520546907800900c024440240f5010842710310a51450701c0508600f420303100d02301c0c4c051003544018003a20300c80c60307516541d880e40f00311108241402055007080e4481180c001e030a41c11155220070245800040120306112034243c815689500080c00c201100e00304907602c0d0072102046444031040040a80c0e10045a984600d11501c3d1846141000c0c0d00b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 777419379 1250 777418129 777418133
    0x414010507170316110102120408070515040b011805270106030b04260c1207051e01020301060f02031303060c0c080d0902130b0d1101090b0f0a110d09091d0d020a 71
    0x74001c003c4c0c1c038031281b0b034010052a4124048242a80e402a80084e031450b910030885c42d000c0e1421000745130340e88851009904000610006400307040c12101c507011000c070044000c40c100401c9481c1251107000d580780100d0590b08440c98980b40443c4041203800014505403251117102c00313904d048a045942503210b5044940091800940468188038030f55003e0905c080329414603101d00040380103081001b800315403041030250421034034262401c03c08444511241010b1124041c0d80240240004104040c0b403084005100008840c00c00d554100300342c04450440d910f001c064003108205000304010310042e68007160001000301036090207410002008a550701c148a141004004c940c1c090f90301d00403030300b03c0307a88400c8041d0382c0c83c6a120320440d65482e4842c005841c10030050708031080c0340c42c0204000b07080fa468007008004190035619010304440c0190724065403080c087c0340d81c07030004c2c003484410403229081c2d42220716140642100040300240000a49103000b81e44500807005901400101c4d00b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 777420629 1250 777419379 777419387
    0xc08091c021e0c120f07030602030c121303020706170a241701140c031315021309142505040302181603051014040f020307110d050414010507170316 65
    0x10707840c44c1009030500220007584680c071000c1610015000740d800000084040700c40500315403011840612414040c02c0c44e45503841074601041048025104810b80403450900807004001413401000d0ba00865544140318800600b8680707074190951002d00d100c02503100b45d03129103070303016242d0042d00f04c440d580180003403420344000300c042048025900c0d05000000110004603944401541c02d6144118894a49540c4500598440740728480c804109141c160000200180c201d0340c01e901d040c49003811916582d00b1880d001c0c0c0d140e900300e2281c9800d481e03901040d403609598100d05420950300341035a030703004510141d0004095002c0902e00d00200081201650800c0d1400c01040c40d00300040e140480e036103400007407039000e003203c443c4002c40340626130b07901c40d00440184416910700395100d0400c004007806c1c211403048108490300034800701c040400c0c850802e54046030380400d100b80c581c1c42ca080040d00c4960100b0780990b4000d58203400c2001c41e03682c83d801540202a124008400d03481040030040c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 777421879 1250 777420629 777420649
    0xb09070902040608040f020a08070906170f0606130b13090303050a0605010f0e041d0a02010207151b05100618290120060703020406030c08091c021e0c 66
    0x120014070500c010b1192507070003001181d2041e80052103c00c1612280005260700b4071660101c00b0b18407491402003008c03405500030f0303404c03541700030b0f12100f10f18003400310715441c4c40c2200807011440d80103000080c80c0345801a42e20910074154140000d08020040110340348a00d0204040d0300389407198240f00c00c06516105496210a00321400c2001c1801d00000900a803c081c03503240c200095000884200c0ea250b0b440148416403600380c040950003601c2c0c040b07886048424040e405401100c000141a10080031400032400043c3c6d200307240000080b502d10041140c01c141a0780b507103c2da520281100c0c00511611000d020000914900d03005190340e8141514011081c03441030404a07109114840c2c140c03062000e480d4800d0805031304010800e2444200351040080d03a104c14410507060005407a0198000e0080d036925690904c0164a1400162201c280c260f500c68643c0d0b0280100881007400d032800115895054410b60301e0341e03002000d064260003c0c4c02c521082035080880c128401d8941400c0803 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 777423129 1250 777421879 777421889
    0x90309090b0a05130608061f1a040e0a0b0d0302060a0c02030c0717010b0607030c0506010504090f0b06011b03020c031905100e100504030e0a0e19110d090b0907 70
    0x520000d01c100002c81c200c503926115031401031058100c007045041164200713102400c130444c201c81c9589000c007004e074201040401d01041450340300c6000f196100042003100749211400344580c1c901490300c80240b003445030041031032030519914002591584c1e43c02c1c80021920740243d00070001801d1840301c240446901500c0441075520405c00790070f50007070215448045845c460011140c41c401d10764418050882802c000340c0c030000018000c0100b64100c009484403c0c003c1c01240e03c1a0b07214018042251500d29001e0800030120544000007803100044030791001061400041d400c203c1101d03c1e407040788201085015030000c2107001902c1c1020400b4101041e502032810b01c15041e070741c0b5003e0b10ba102464110b014a0748803800d0000011003045200c5107021480004c00c541c2c54103050090500c414442030320f129600b030179000100240000c0fa114094a4450b0003003816246541080004211041361400c41c48400d101c68800c4860394030403115102c0c0581e002c06041d00c0d040841d1070a1207015081 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 777424379 1250 777423129 777423131
    0x5060a0e07021f110304050f0d0203030403090e041b090603020f030111040608090304081605191a091302030c03010e0c07030e0114132c0c2b020a0309030909 69
    0x400440c107034005122488a04102c41004035041d81c0c90f0b030750002c0c3c10345004038456540b0002c140010440c0000b956403246003480d0564281014031a012603d9200c00d54018000502c002e0082c401982110040d64201d84174030503024513000c14a080d0074100840fa40030702d04c0d13140c0d101030400940c14086240d20000404030000c11060a0807001e241e89070186000340380400c00444009901c1030000c104035405021150212030005081842c111107084070790181c44c1c0280001b102554000401c540c40c5015950000c1e501c241e5066030200e01070198011030104c503440215400e0341c107180129840218018500b40c8a4580d607036040100c5420114409010b0a060708010086000840d80c0848019100c49003442c002c408240104201c07080c0b406905040720302c843d2100c1c0c0c00a405042a00d5803d480004140070380f1941000300c0145d42410030843e180c03100413a00b003000094151060000031a0014105805210000059410700403608403410300400b00ea940d00c1c1c61b90a00d508680080300800402c88 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 777425629 1250 777424379 777424381
    0x210b0112200f04090f0902181b2203060e160e0103061a130b190b03060f190e0618040f0215042106060902040b07080c070f0905060a0e 59
    0x11040110520750022032090000115600400a820a044400800780660180a644044480c3d0b17402804010403c9101c0d008006042d1006c0c90b041700b0f0188240300340e41c0c000c40c0d5495680c0a0385010f600107824a504401b50000201c0c4241d64281044086c43c01007034001000c86a0540c0ea81c40d1000003840d10890f0b080c415800c2000c07140b103c0e11641903ea1141e000b16080e500400b4603002005400e040550090b50301d40e12954080056011500841c012520901d00305840016000b1441c5140613200000004000042076810007103890100310340c020f020321410912488400901102e281c007d441210134180038041c1b1490080a180c14207a41003500c0300d442d003004c1d41c0d500148071040c04028000c141e08090103a01500400544c1d004203c91001648500c121030722031b1844443d1034104884551074030401080128541c400d6034265102c90316224941101c40c2c6900340250007e0403008039034490001c1c0460704101d9209203a00501e1110f2010429080403400c119060100750010799410399030b90 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 777426879 1250 777425629 777425651
    0xa0b06040b07060c0309240f020c1b030c0918060106020102090a120f080309010c1b05070b1c020a050c0c0409030e012f060402010f020606090c0307210b0112 69
    0x2c40d910079902110004202c00341150540c0940301c1d04902901c9900d003c047c0003a1f02e1600c001198006800810800600d2000c08140d0201e000d184a900556400814a840e6402e42c040740f60204440090444076007402180000b040030600b224142c8100c0360340d84030600d8000003082801d024010500081d07042c44110800325001040510a05a503002c036800c14900303000301134189001c140c4d0803120f2940c0da0301d062411a8080d10b030181021000640601324a940034064048150b011039200025010542ca031000401454018000b0b042408581100704c8031500040d1004020f55446038a50725180d0f58241c0034036080c0480589510701403401d00300310754002548059031704490440ad00340400d044000406500903150031003110803100007c5402035000381030014546218a03c00d0341c4044080c50304280881e26588280c48441e000100000442d89926191001c1c5502c01058031341807050183e00d0f100c0a00ca030311440d0500b1400795440d1300d40300080d41e002031102c84460f00c400d030502c0820140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 777428129 1250 777426879 777426899
    0xc03041a0304030f14271915050a11010903020105070e0402130b0a0302070204020f070c080a0506060d0f02040903080106030c050a120906140a05010518070c060b04230a0b0604 77
    0x4001c601d4200103122001c51680c031000c205903452600340d0050111400a012186e002d62540c1e00400340c80b0785090032104e514200c220801c242a16410316a0303041c404543c010035902500310b00001402e0150203081000303460000d00c14000c643c2c0c020303400410741d0701701030b0006020039a550242078081c500400484c3e00303407840c0c24113a100f1544959031003035954a800d04124001c0c02901707802580070307000280030207845003041e01a20003640145150340c1019034038094107548054200b40249180c0114000418601d4600c1c4450346440c005c81d032600c40701c00254001403c44140344012400715881c0d800600440768980320f203420084c26410042d141c10300050340946038840500f649130348142c40d40d00d1030341080140c2c2c000000040e03891103c2d5200d81022003140020f0b0100740102d600130a040e413001c0d080b82100039109401000c20740c6230a02c034542070740c5854028016282d91981c00c140c132501404c0c1010003502c52503240e80c0104a0f016124240700306417006440c3c080e2140e40c030a031001c0c4000c3c000a0f01c2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 777429379 1250 777428129 777428147
    0x6060e010c12110d05120112020a0b090a0b1b1005091902060c1903110606090403080a0603170c162402070902040b09090f151002010603080c03041a030403 68
    0x810460142002c03180d400f140c21020301807505420b03020700c2c2e5840f00301c0c07600070014006241604005040b1a80c03910043c0300d074040002c6010354803040140040003c500280000d11070360a018110b5035220b40c81e070f840903505500001130343d031058000c28500395081c0c1051105121100ca400400d000c1424401405560390f04c1c00da281c07400c3c0e8480c01c81024115603440302162503260072013080c0c0e20318070024240d01c005000503a0050b808203044500101640b0004203149120350300050000042362966141113a11103001042c107209659a0403011002c01c003404841a041028a4101503071030048126050501c84000d40c030380c05a580810050200c03042400c06082002550119641150311a0380100d02d030880503880b8480d00ca100150200380d81841c5401480414410303a4100c01c140c40340c04410388400c008803020000d6220050903038101c2d20b825079012404a186100115506440f61a040010b81c04050b600f00e66510000d0100450643c0303200c6082ca450030f4412403130a529080c0c40150114030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 777430629 1250 777429379 777429383
    0xf0d0b01170612010f14070206010618121e0803190209060d0b01200304240206190902180103140307080a0302030a0e06330321040e150406060e010c 65
    0x160b0307200c3d40000070254000000d940d403001c0c0c180504c80300c501014074400c400361541c034014000c4000106442d07009407103444204e07511344004500645000000d0004240e0f503e003c0f40c050b50b010642c1900e07181c2c0c19803c03402040c000e2054542d01d04001045100800030070340e828480c10b0052040d8129941c030b070b41c103848000698010106450058400403605111a401000004801c14020319400500040580151035000c02c1c0650380d5040740d400b00b203030742c8611303100c000060f40030070005241081c42c105d0340c200196a85201281040795580010300b14007468400070340d055007100040040c8005140304220403496100076504d48011038407113500600c0360711041814540c002010038014540303030b44040c404041c040c0a5549500b41440440d0130401c01480c0300e540300510441d010078500300c0e8078661103001001001084880011102c0004013009035101c1c07400e100c000e00c800140011000d240c14850003000c00c400241d42d01c4030b4108030031280e00390401010410000d280311f90690700403911022310781e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 777431879 1250 777430629 777430639
    0x7080603100b0d151b020c041d1b011412101a0a0507150207030e0f12071206060510180605122701020a020a030206090d1e020a020301020f0d0b011706 66
    0x41a9102c0300019100e2500842c04c0c0503180050081704075400b16151102082c00c417020b201c2d020300f11081006000011606c890340d0b0b00440410380710824a408a0b000a0300113052a0a014101d10003400c010341007054110588000c0c0000c000d407600180900b440681000c426008928060f41b0039800710b4003426203040107002c00003c04c01d040c000701003c10f940d10000003d0540d994007461070000c00848582d020036015130303240701d414185817030803088541d044c400c100c00810081d0300e0309184006819000d4015031f10381e40d0381e20011600340c070f504006401031216074a0b60b0428070b2145030f42036900d10b0300798403400030000180030a06000707480400c95900814130156100821040f440034848850304c194503170000e58400545000700d02d03008107803d41100d0081e025036550b662241c0c02c02d501c404051040794009030310060700b03480010381074002c00c83c4c1c40c000d44110741c6010300715800f180c2244d22203440502d1680c0041000c2d94500c100340200c0d040340d07400b8a041d003400401868100840040601828491 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 777433129 1250 777431879 777431903
    0x20312090c04060909020f18130206070506010b070308150904030c29010f0b2104030c1202101a01020a03080a0b06130905090d0c1101050403060507080603100b0d 71
    0x89404004801c2a000018802c1004a41e00c821a20007480200070890241c101244090242d180810040e03c241002d03020341c0300c19a8480c0030506010642c0c0804070303407001051240001007041044003a0203010a95500340ea00c2401e810003504401004041350b03072a80c000c00720401d8035100c038020a07401ca545402c21045107186442c00c0210340d882d5403c000c00103203829440b004405802c140d04e07030489260340c4c400d03040799895903000f0f50180704050307140b0702d10284200c0d034800c1c0c0ca19185400e80d019001b8035103080c0e080d455a4900400b2002c038104100168440000c0b40400d090510444060404e44006910109031280c0041d4a480d12000007a05005012002554407500d40e00050003110000308103680e41c070b404e600300c91600001e40c06001001c80c50180003035020140000d5455000c41c1689449500c1c52460b55081080900c0c1c00e0114108141448000001002801464000c8040c1e44402500c2d2501c13a0505181520803050307182c0f41405c05030606040d440742004110320a4100c0d0b555605 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 777434379 1250 777433129 777433141
    0x1b080a0b0c0d020c0d090906030206040b0c0c06360f01030c03110a030f05090c0a091505130207030e01020c01090603020d18030221030c040e040204110412140706020312 74
    0x424003400300e80b0200301d070001444400950300070403801c0b00301c401c5444110880341c50b0041017089803c1404003d400007801c11050100c0d0452401400e1800408421182061a5070f0003140c85500401d020748441e6110a11000e0304007285106441403440100b00740c0100f800d47d10001c1d1f0683764545070b0303d0506541e0802c06011900ca40c2060300d42e5400c0550680d580c0b91012402802030840c102e401070164a888089204243e000c10b41203000c4100a003da2021414404840c0052442d400e1010101d4110080000c80c0c0e04c96000c00d0910880b03402d00140c8554060401800b4040c14080c220704541140f1011003035030381c000042c0b0003620981c0c90016250382e8509200d50061840801e8500420144002cac1410190300040c820550030003103240209080004000d01800e01040d2031502648a06101c14041c880c40c071441c603907100b070000304040b5009050a00741c1d61607038042d0700050300c0140064040e10920084440c002491580100100441c03454002c0094890142c1b504a070505445000803e0b4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 777435629 1250 777434379 777434401
    0x80a08010e060d120e131d0f0d02030f0d020c0109151d10090203190b0709140d0b090a17031006050304051b190b0405010915020c040f021e0301031b080a0b 68
    0x240b14041d07840401081c58502e002506800d0324071f4034244c46103d0313407052481c1070310045a84d0ba00da004d00c1e0021410310440ca40502c3e171507003002211452080d0f0900c507902e80341e0424014510480d0191418840030031400030660180c0d1040800d89180c1c0706060a2800c001b400000d058490030800c80340044c0070300a5100003030410900a80000c000303d2008044000d01902c04038250081465460300e2101d559544840c0034074100c000c0364583c3c418000d40c4200e0102d0b6a07054403071b40c0300a600e02680c4d50304031a42d640b982c1c2100c117072221100c1c1c1e8101104103c0b00c2201c80b01d000d0082c180074240342c0c0c11482c143c1c6c3c0781a40c1d9500c1181d158088030802c140d440540d00d07008803040c2c0b00d8403600724030003e65880b15401e0b03070310f50081e1060301c0c001103800c01d001914a80110500d00341800e40d501a02c92041c80800b4880501a00c1d0502c8100355801c0040266849031760040c18207820702e0b10700c0280d503940740d810040d8851524444038450200590001c00142e0b0000845d0412942d0000011039590f417002c2500fa = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 777436879 1250 777435629 777435649
    0xb0a050c07060f02031503060702030f2a10060506090f0d1a090d03050609070f08151e10030e030301030b130209131203020a0207051c080a08010e060d120e 68
    0x805543c00e1501d41030700f04035550003451165913503200d14800d1080701e0b001c256551005a820b480560001c000e0b00303e0800d400710090000000f00c01c0c941ca0b961005203a030642e000101c1c498003400c2e80007442c00a41210680c01079100510044802505100c0e03d0030010b100c190340e1210141c841d9a050340313200100b1200d40518003522002292070401c52615041464840c2b4440d190140000d00d0308001812030311703001c180c65001d002d00f5610f01c600c101e10b00303200351012140580526584885001035401c00c0c1c0d030340c0138200c0102c00e0030400c600300402c203c414442d403104100845c03402c0c1400c116a0301d02020001060b281182e80100150748a40c40e14100911a00811400a07422a410b4010403150198822000c00914131840031060200c1d8407c034201c04034021210300d08016048900308115514000c0b68014028203003424464a6000301c2e80c032900f0503480a030158012480b400010031a00310314941881d80040c4c141c0304d454110b04155680440311000c180440d0074000000d100c070035140c582031820 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 777438129 1250 777436879 777436883
    0x2030a180803030c070c0501050a0516022206090e031e18090f1515041509080d0315080304120201030228050c0c042016050303190b0102010203040b0a050c07 69
    0x2d41d6403030804842500165002c1403094406030300300070f0000340c2c07948101700b00d6071112810354032a03081885141495000b0140202e090341d014004070b40342d40c1c101b0052101d4800c190740709407000510798a000c0c10403040e11404900c802d559002400455160901c1c4009248042c06407143d9903581e06c907001e004c1e102a40c1d44d503440ba802c0f10750101082141444600958010b21070259185a02c189072010400002a000302c0c7c600b6040d070900003000a01c90f4000303407089402013820815000d0b42c48000d084d2600c1c024007069000a84c44644d400b826075102607804000e0600c05d40a5440c02e82420039010702402c001d2802410580d00107903140400b412003040c20a02d08010301c400c032441c0c502d00d600800300c1d00703c0d07200388106002d030b44448600f925103071080566500c0000528440d41103c0f84100241d5000b204444284280920b928400030744140019031203419801ca0781c000954114a201c012a04514002c505682c03040007440003040d94821101e5000803085400b00f0182c2d541c00c040c4042d07010340c03440 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 777439379 1250 777438129 777438133
    0xd180215070c1203020a14160e06030111162102031c0e1b030105072c0402220f090905060609190c0e09060405061c03091a0a030e0d02030a1808 63
    0x142c3e00c04c041e8085030440f0701c24080c0c0c05011a00203103920441d11442000c0c03e0501041c603200080140545a8028681c4448024000601d00c410b0340c03515400b5600079200c030200d0302c4600c00a10208100c100c643c8007026000e44400d401c0310200c01d0060359a104488911400c502c40150381d90001507683c0041019140702810384900044003540002c4c24005081018401c0d400c00000420380c611521007418001041003500c62464481c200c0583c1c50515001035a030456002c01c50301518200003180480d0100b00080d100074080e26109c1c0c00c4840b80020303007001200905040d21800030900c000703100ba0b00010100d8041045444180004404005e038500f000c4c0440c6c14201100b40c410b42100100e001181c0c251085940350340c4030000c000c101c0d80704031602a0b00c40c101d02c8243d16050020456529118800c3c108621103548605061040c4841c62442d142030410010706900055454060030300841d00340303401008003440b0800060345074024034410070300b0441301044051641c00200107610080643c2c0003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 777440629 1250 777439379 777439409
    0x102030a08041b06033303021507021c051c050a0f0e040501140108090a0c06050d0f0203040b06031005070f0e030102040906080a020316060504030320120d180215070c 73
    0x1024003e0007a1440e0071b04003c1c081c4080202e50740b8007108000d400103500e0b044007100c9041d94200300515a091141c1500100184044c3e8010303101c125031400001102c80c3c041c0d0429a8901d4641d1070304040d00e082c16600044034504041c00394205040ea4103041050801c10604d1500007401c50b01c845051140d02c1d8824100800001d04031202014140c1c400c1c420b0f601d06007650b0383d010101740d4401045070000d2158103130032030801110348030350068a0020000c02c400b081d03500760f40c80c8400c141c3c0c0007030341c0985035901ea0380203011081c6020403400686800c980c40c01c0c40302e483c0c094805080752280c00315480510014140501081e6400e40c1110082c14440c0070070040140c40c3c004140c0c0e0b40d044090120701a11890700c48810b0036074004084c104a883c207545007490681103540403288100f05c021b0420f0944c0c1c1d00039000d03807403a00c14400c403940b00d0745901c0d8103a150508482c0d880c3c2503c000a0865185150403109680503031264441d6610400c41d03031075125544d581a1a050050f050701e0b50040b005408284 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 777441879 1250 777440629 777440639
    0x1801090b010503011409060129040b09010306050d02030c21060901050f10150e040912180b0403020a09090507170304090c050f07150b0a0308040504060605090102030a08041b 76
    0x8000e25050398020350003002a03602600055800840944d0031194031381c012001000303040300c040c20200501d810000b031394080d130381e17040b140032084e0b041604011420500400c400101b540e0510a40005003002c84402403602d0603a00403d03221b005192000c0e0080d0603004d41c980c510b4030110f0844442e00c0a01d802c40f03c5030720304001e030180244000d44403400340302442408521255091030b2044199142035000070030032030318200251280300e40441035540164642c48000c1c0031800074512940d50311403940f41d0a200b40d003041851015641c041d000307146207480911060016880c1d818484058818030a0005040111130400504d4405560f20480004900000340035011300080701500480f031880c501403020540c1d410b025100c0c6e000d004442004400c040c8603680c0800e145003196551104241000034030150040089035a0003504c1d08161600200040c040215060a111721002040945000c034103040036680002e40300d106d910550010007a0210204041c050140092182c9100301c0d001c1300354250b552 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 777443129 1250 777441879 777441893
    0x218060a050a082a03012408010e0615030f0601030c020f030f030c0706020a110d0207050d0b0601030603050706030902181e09031c0c03140f1f0e0103060b12011a0405180109 76
    0x1f40a03480f8150640d0f51400846803a1100c83c603107601068071020020381c00c007203405a100d6402400a50f0106203428003420780410400210f01401e41c1c03180c00195841d280700007400f52081d10342078000315448405000c5100e0004825103509486101c20075a80342c9440c0700d00040f03801075080141044d031001417150320f10790f08214004c0350002c5a6098400c000c81580c001e9031901c000d03100f956002014410500c00184400d00c5180c2c0c03281c8141000949941c503510350a00c0c0810b130ba046240030a0350743d07140009515000c3c13030304e0b03991400058905a0510306a01b04030030f5100c0d00310300d408080c03d66a0206607c41c0080c07040da401440b9865110595080c141221400b52540081810100e883c1c8125100e2008440c1b024910443c022034034a035258036044034619030000f6591081c600d20111040103d198085800054002e5004500100b10b110300107041083d94591000100400c2e1301d011007042c40d5155617004810b210008079400903090344d03800d000703511900082000104a51078404e10400300076034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 777444379 1250 777443129 777443131
    0x2010e0f0d081803031308120403032711210303150a0801050603070608060f0a030f1406090703150912080123060d0b0a03150218060a050a082a03 64
    0x40c0c1c2d5502285440340c0b8018108100c0140c5864080d401c204001840000f440d00007002144c4a075103c85e04d0b088690030002030118080e00c04500203a1038401502d050341c1c414003800601e5900740e000c00b07103440c0c007a0741d07045104140b00310250260980402d644100e04a803803c407000300704c252068a81c2ca00e000d103a410b144403501c0100c04d22a035060900070800460501c40c81748035801c0075004160441c01e0110075203001d24028a070380d500480103003469580f0349601d111000114855543d0700c070500c0307583c54103541d40d24010a00115a030f00080c00c0003050180020210101e9030007081c0122303040d90040d0a40080c2080ca40040c00040d40091440040c60340100b586040300c00c48105101c0307030074414460886960709441c805500120900544003411030a0388400d0300300400038480c050090340c940d90840109c01c2414002400d0b0f5002c0f030341d85000c1814400d00880d4181c12162030f480c0c032a51180c080c000d801410000000c100751400044c1380d900c122014204041022000c148406000815100080d44 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 777445629 1250 777444379 777444403
    0x11712040b0a090f060210050c130303020102071703070f05220b0304030207141806040b0d1a01090510030f0302011d01090c081207020d1e0606090e06010806150102010e0f 75
    0x10f040400080d10745881542c00c0160f0b02c0d15805840171a8030a00c204011b0540540741071843c0d9030030042521034004001c1c941e4010b500c29000546c465460f07040180e05228500e100400302c110400820400c1a8400402e450126103402e2a0ba100e080c10843c1c0b620b10321048074403d2040c1c0100001042d00b400401c007940c4078920981c219a00c06403101160040c80e1103042c401038010041c401807688810300c12400c1e0740c3c0b008002d0000106003ca4800203000c0c4c0c084000e054501100c2c1401b80c0002d1007030005018003401a20b04141300310700b00000d403414440c14622011b0302c05004000840101032013900144651250a10b0961440c81031400d007038028203020004a410f403c4c40000000c1d61070001c10410300e43c1091240c0070741441c0c055000d105821044c40411521800300340f048610780318185080c0100940600c00c00290182410810400c59003884150221035101c503004020340c40380010307902d500802c811b44003010390b1040401030b40907007d007181001d16401000b10107100c01c1c50029620b11300b80 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 777446879 1250 777445629 777445637
    0x6070201080a2304021c08190c060609140a060f06080c1315020706090e0109150305060c120f0f2a0c01020c060106050712180302063609011712040b0a 66
    0x8900441e500c9101c0c5400c0303100a100706408d200344003408907040300b1046501118103110340b400300d480d40c4110445419400000c001caa03507042200d400345d41848683d601c4005060100708807800c214001c081901d01c0d10500f02008902c000051850882a0654910700c5040321421003d03070304c4040008036811034201800c014400c0600020b61036210b90000d004460110700b45c2c65980c0d0a080142002c0e04940c8401050454080b9002000841c200200b0b40304d201d51009844c0c40320728010042080178005032035942c105101d2418400305800710100f845d081025000e07582c07001039441300700d040d54080e58125100a500007280d10f52220906400404181c420103050311490ba8817007209440500440c800032b40a0f803507128820b203031301e4006c90a6064000c402c0b400f58403840d680380c0c0005c02580c4910f2086400c001d031482c0d108030ba503e1107402d089483c001e04c4046401101401c002c02c0228005100d010403100d03850ba410040c5060030320082800304014036039682e580d0388460b207107500d5a2003004103c00103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 777448129 1250 777446879 777446899
    0x7120302121018021201031e0b0a0b1003110d15080f010509010c0201090c03170f0703030c02010b010e15090a1502070317040513021c0216170301030206070201080a230402 75
    0x10381403071301c200d0f450901e8407208425541d0079500d892041c40903203015a031851307040741075800214000003280c6105590307641c0c010580041e4181800441119000d0307100515042130350301081d5036400000d40300d02c0210071000140c0144404038803800d00320071b42d016110038010400f640703103148011f4002a10a00500c80203104010560f07200701d089a03088a07000d082e16500310824000a54041791260076641524035150800840720000e603003e9102c2d000840102e40d036624106205170302070003055641c54090030305c4403072041c044011802d89003d401c0c403d07280e994001520215603031f0b180441e4024246000a020043e2913050020b5521400c078002a10381074804410b08c0e42c0d143c0c00b64100c40c142c5034090051003500b20302440c481c000e50400c0703d0740401c09200f05000148080f00f8406000807800841480d18090501d00b4175088005035a1414442d00300100018405a2254000c6602132a030a02c0c18014581c0d0316801c1a004001c405004070013207511031080d5222201d0494002c0c0154000c403410240 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 777449379 1250 777448129 777448169
    0x130b190e030711010503090a0204060e040317072a0b07090807080a052817030a06080102030115050309160e01050405072118080c0f06060109030503071203021210 71
    0x107a8041c80b42e0003440801100d03061101035100d88040c1d90009031910403607440406940c00070301500c0c00ca402954600303056104100626904c103160507180c08030101c0c0d03c042c0d8100100000c00300801c8840164010340d403200040b4458984071044d03003000340c0041403c9800e00303180f00020a071085901c80c0d6640ba20030410081071604000c5007801c1070560107401843e0360080c5c0800f914043c110a60300500992800d1a000c0205903d204044609401100d15a5692402e50b020004845082d044455260320610041c4071003044203c418050014500300942c482d80d600c80c84a15040807041030507010514060002075940891508605a81044078144190f40d41c0d090300311802d66401d06d81c10200800d55604e1080302d0708580c400c0710302640056282c64008016244c0544992002007400e199511001d090350781d8110a0082c1c0d42c00000c240303000d0007a50303d16201c0035503901401e4005403616a4001c48042c4190107039044036a245154900f0b00c0d41850401c250621040700c510459031004c40582140d52 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 777450629 1250 777449379 777449383
    0x7080408010b0103270b04020d210f03060608040b1008100f0f02030708060d0606050612180d081902130602030c1b030304030b0a0b042a030603030503060108130b190e 73
    0xb801c4110030781d440c201c0c0341c0c3d1798560890309070024009a0308044070010140108002001e14020000c01048650114951910080c1910103d40d419010946040c000303203e210351044403950000d0b008081200103803159282c03602d244500e03501c44100d6205000043d40725442c580c020002050007010308105500c1b1000d0048141c2c0702c2141c0380000035440c02c001a503140703004615044c00d980100d00c001481c54445000c144540c1c8000f40e4010700300784500030000500c001080303507020140101c0c0035010020440c1c5000c2d100d403401501801c0046003626508982030040e41c152840c072030300c61b42c90340301240d0b64440180d2071b60703c0220601d820380201281f120344000980c543e4004804060015450306166407030380743c500e80024080c580c2040d15034142c01c44640d11030158403445a40140800c4040c1e243c0002d040e440c0082c0c81c00c1c40240340c10240c0c100003080c0c0000a481c1d110000f801e0022550b90340245130060244000b50090411145000707000f605003081d624102592190441040440d0500250395 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 777451879 1250 777450629 777450671
    0x4061d0109020325030e1e01051509040f0609170c06060a180b040902061216020114060f0f0301150f050607080712050c01050c0a0f0f02120f07080408010b0103 70
    0x3503114642540c0400621088007001104c603440c5400528540d0180029050496510062200004026200745512802c0c030070260840821860415440a183c0c081201c426004101420050301803c0440610015421025084e41d0002d0707180b4070483d001140c90345503000380000c03203130600c5510001181c9050607004181980d1618490f0010003c42c08804d40182a4810f4501e0b001902d56503000010703120140034121122204220400500e0b02c140c1507884103408441c0001103a04008107001c43c1c6151502981c0c001d00c055a015616014040120320540001c5118a0b0150310f03240c0410300e68482000444242e480803060346c1c42c4541d0390802c0002c2400384038030140452208000c0303a00024005034100404d010035042c81030a0020b54003a103400c603002294082d500702ca0000d00c084405902c003c001c403200c140d80c140f041c090010050b0003959800210f011080d418000658010124540800e54403c594040c01c410783d00ca4484801c5401b91001180c11030100c0d0520000e0600440141021 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 777453129 1250 777451879 777451891
    0xd18110d05060f0c0903010203040602190f1e030e0303070e09010807032a050a0801060302010210060b0313140118020a1a0a1202040e0103050105071e0c080706020904061d01090203 79
    0x402403515420b200c10f00c80d00000e00701d640b0380001000f0700255038500380041e61049021380700058560a410b011800c080030000708403402c102400040901c000d03013000c8030b054070803090394480840d64a40c4e041035008000207c005041c5c0d10010040208090303010342083c0c80d181c401e0300c80b0030310ba9036218803299554045020051202400e240c3d40890782c1c802d070000c641130500a112215050303a4560100751800b0f43d903004845240d44403007040c015540c0400c56014200701b0f1031410450a031603c4d409003030500015001c0c12007030001310401c006201c0c00c400701015248000e0020000103d041120b90b96050940400f04d0084440e402c0001b184c036101c140b284900c245010400e0b2030204035040464640000096121049609100100c3d01c10354910401e4040c610800002a6a003001c0f81c000c1d04a40030025410511a4000c8048400c41d900c070000c028880d6010300e82c0d43e100d011524044005c0d001d540c409540151405400091400407458200c40b0401c0c4040d0810031a40c03520741c194103901c41203900e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 777454379 1250 777453129 777453133
    0x50409060906060f32090f0a180c050d110a081005090a03020c10121e1a0a061b080d060320030c1c0b0f060307050f0a031103030d18110d05 61
    0x102000c1c01c424505e8600c01001e40c188000c0c6800300ca10b00090b40c1e041e00351050010403842804201c0810041c2c803510ba003806801c0d00f010010034040d41d0398800c54184e4028540a074125208220030800103900f030260005004025407911a00c400c1442d90319a490444100854104004945003840c081081805550954050b10700c034801c0300240111401c0d0703110b00d01d04220740c2c0082410029010310510701c0d41070601c1c10055882c5620501c00083d1448000c40d01c84003814901404181d0340d50810503402c03181c65080c8540b02c103440c1902d600404810010280000400144101c9031142c2c9a22000c03d50f8440c25242284a1341403005102c0c03840f082d41d01d0354250340301c40c007903021034034081c40c010303480480c81c41c086e40c0009190313904c002c0c940c10182c5a400e215400c80f020301200c0e160600000000d06420740340d0f00c0726002d43c2d000189040085200140c040390300f1041000c81c40d02e0910840b0f4001a040000780601c1120002d06150900c10100585004141050400702840c0504030101081c0e04040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 777455629 1250 777454379 777454409
    0x1b110411090d02100c0605130b1602150702120c01090201300218030a06060602060711070b0a02070b16030e0f0607021e030a0b0f0f1b0c0304050409060906060f 70
    0x200f07200c124030f54541c0c2413042c07007000c20020001500d00d0054500c6160402002c48020715240381c18140c09201030034030440742c102c10201d8080d155002544840c0c140010810801503110140c0603410441340840310b407400b81d4002410004c8110540052803083c1c0300382c0e99020f18000c941001d1114143c840380b00c02c07115814030401000c011a9801a000c0b02c0c190445250318043e4900c002841d001a5000c05c8036569100d0000704811501130003225841040f0b030900380c1541445040c46502e68045026000e0820310108102046500c01c20000002d450000c42099680810041c1c0c540080e1600200b10b000602c02d191400c1ca9003403100000010b01c1025004e107003031132200d40c200214506880810b0640d0f00c0000600760145e40e080007903c2c0701d14050002c2803428103207041d040e0851007000f81711500400a541c00c2c88006680304803042c900e040d4000050391600c007001119402d501c0340e035101544c49400d1180c01014040c7c0e80d840810740341d03c40c0e6020440d0079603510380c0810f0952135120741d00c0b4a000d550 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 777456879 1250 777455629 777455633
    0x603150b0609060403060f0b0f06070609110a0308190e0a060804020d06020d020714070819060f05070e010e040501030b181504211409010f1b110411090d 67
    0x14122400c004801090315003084098000b09a90360859801038074001e80f01e5201500042c0f6501c121035000c1130968011840180c22804240b0511404400405956039040c49105000c0242c62a607800723a4000c0503520344990f281061a280d4100e26110686524039213140c51205028a1070011f0038080600002d5402d40741c400c0984950b0360003402607802c4900c80180d50000f600750700c020801080c11010060700c520141c1400c0d04294034040c4040c2050303000d0003013441a5100096007160180401c2001d295003000e501c0c0c102d015002016078a005e0f2800c0c00f050284458104686404001017030344d90118524208080000361102840042c3c2407020020111382ea02024500340d0704081980350864070280d01c00030b0000105002150291651040280c6803a40d24085c982c0915440b41c96242c090485160b0405082c0300e48038000a440c140042d80140d201000e00900c4c0e146041940c4030a12203402806007080340e5494811282c7e02d104501d0b003100000382e640b426096491200020308510351440382a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 777458129 1250 777456879 777456881
    0x31202013e0a0503180c0102100b01120603050d200a0b06011106010801050103031106070e04110c24011502060106050a1214040b0a060e01050f03030f2217250f03060608060a060315 79
    0x205154ad810000800c0c0c0348607400c0708038011800214402c0b001032180d00301c900c0c0002e00f910024038210180c0c00700703098100030b24400000c000c1119904440b206805072181d02c010707554400003044404c00c3c0d01484000003240881940424100d80c020341700d00d030b16250040700310b5448901c100c65040206200c40d0707105d5100e04050348100d0b2071109450380540f61080114880303103802a0ba481041c4403200c4c02d50f5200d4203400110301a4014840c108400f074204400d690065140c0905028030300820078080741e18800180314143c0c05094000a401c208500c02c1c10032140b22403881d00301c805987ca0401040424012039891180900300c81c03d4403c800780390b90912041002c5040121602541403000313005101c0501c500b18010b00c5900101403c400102c0d04a5140c1d01e20042c15030302c00a940580c00400c0340150001048131034012511400d42e01d180c1c02030440c0e01185102d075400c100a40700d18054003008001d100c0e880001920864012110f040e82c0d5014110140c2d80d1502004000d070358450744049104140d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 777459379 1250 777458129 777458141
    0x1509171b12030d0b030705040e010617030405090109020901030603060e0a03021216140f0111030106020c0d02061209120d0b030705030705011421040606031202013e0a0503180c010210 80
    0x40107096846c81c5030342c0c60006003a1011603104440303036507503048101300f00d00090310400a00c0100743c001d0b6041501c2c1400068030f20005206d5100e91580000304070000d6803080e032124000d950300032420001510401c414664640008104801510070600100400300041c02951002c01520513086410303c00381d03680d4003080d400c10350b03c50003603c680746081b01d1540b000e0003003841c40c20100c251b40b9180d40c0740c4140245002d030302180d00b6014100964031040941c036482c3c01c0b0785202a200781803521548074100594030b809654143c0724041c40000c5150891001d1a40100c450020b007201240c0e007194590342055101c56080c41414081510205015810704042015141e2580d40000c050f55002910707926042c03540342102c040b26110f50b500003e20410650b01c117500741307440c003038030080248008842e42d6500070100501d940c3e005640c0a410820a411001201d007507945002980a8451518101c05000354000fa01c00003050003040341082d80816001941c050030f280305a00a1040b000902001401444 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 777460629 1250 777459379 777459401
    0xc0e01091511011b0309050613050303010b0a180602010203150901140904081917012301200a06020c070501081b0a09081603120c0302071509171b12030d 67
    0x14039104401804c0d40c2c3e00d444942120070304d0b200440d0140c06864a58141140103000d100c0c070a0003865040d0103e500003058a040d00e121900403661990890425140030072000341a00300040c0d44800803c1441c0c0c190041c6000740c00e10a240b141400c0800104601c000c0d0900070440d0b00c40740040b06d05d481e031410440a40c0c000380a40d214520b00464a210001040c03030b11021400850114140b402c4401d0460180074010658404080c2c665003084400950b901076040c4480d0407c10285507101800d9074070080700300030500351401c89100c8219440d182c800780d00300d100c0d804110700031541d00080320350040711110311600300040344044420718101050020b80080d030541c2c0400101d0000840c201c1d0f400c01c08141002d030120410142d42c2e01e540760050b0b021624403081410400c080c60003600181c0c0000701c01007074841d80c1c01d41c070b101803440d4441194118003541c0b02c05010040c405024007140301c041218880301e05500039101c08402080140b000d2140d40060b10807960b4801c200c4c40805e084145d001c0c030540f107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 777461879 1250 777460629 777460631
    0xd08090f06040b1e2503020414090c0d020d09020406081501060804050a1211100b010c02010305041106040303090602100204060e0d0507031b05031606082a0d0c0e0109151101 76
    0x18403500c84100080b00c215031005d82d11121001c0750700115000201c91146031950b2074154a130900b0186580070032100c40884a00400c401004100310660050a480c0d4951b01c4000031504c85040c005214040c3ca5880b000f03a006a103052400303d1502d0021a44a1701940c441c0e0285026901c0c1003802ca400b080b008005944078002e41c0c0d0303104009004078070039204030399180e56803d5950000e411072600f08041009840041807810403818250390308030005c50030703047e02420001915501d606000750a13401902d806944001700180200406410002c3d0605503001d540c02c07117401810064880c01240700b203000740030102d02e8203980b121251601c0000880420b02c190156503100d0358a94400d460b04601a4001c810342050142c14403680c1410000054a07503d104255443d452a12101520340503025180560383e03800d00264240c503000da1840d00e080b60302442040c030344e210500e100b110020080861100001450030180807110362050310080d040e518084011a0004100403058400e1240c61660700342035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 777463129 1250 777461879 777461911
    0x40501090609030903110a03051b040e070b130902090d110105130609090c0203030411100207081504060f02130905150402040f030501050c03090304062f0d08090f06040b 74
    0x2030002e014401d1803510944a900c01d080c05d51810f0003041000400d103501407901140204045600014404a08500403598401070102c54000c04c005e8008520805c0c070600c03540c00001441d001034401400300c0750011292440158640b40300c0c0c010391080016040c2e1000358001600080b030031480401b590f010301410050b140c42c03164503420542c00d01941c408004aa0031074020045024035002e010500300320791024500c3c528140e80c3c3c00310b034078010b04032240c09580380c0000c1809060081041d40081c2543d401261100074005042c038280500885088600314108050198015020300903151201e1035011001c40c51801c0c5281c080c02408010807240c40c40e44208034000d0103485910041c0064a108c480010308103081d800c1541c00e69030040c01d46c41c04c01e4000c0040020b0403401109680694003546801c2d1070340300049140b80031003581045800e8201340117641600b480e080005078034181410030349030101c40e45e540a500c2510b60301854120001078015000050010b030f08500c685501809030b440c400c1e2a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 777464379 1250 777463129 777463133
    0x130305030a1d01090201110a03080a0e07030812072c010f020c060a091a0a09140307030b2e0b0f09040f0e03031012080f09010c02131a090c09010804050109 68
    0x30a032000b07103800940d41d074803450030540d42d21102c8600c00e100c6410041c0412040c40c5d4004202d51070042c51203007966650340d001c03c40c4510030310018004507008211281c42d41d002d4080686101015151400410f194109055480c1140c11181020420701103241d0b210101e000c00544600208807030150460184030700c100905c1e030b200400362060b206075075218000340f4140780c12a40720102e0b107a6080010078003808107130340b400e600007086002c0da000a88409140c025200c086403506107250030050090710840208020300b00c0e614081d02401040c080c202240318804002c100300c01c05c82d40502c0060290400200d5000f05150380240426030020b400002d880d02e041c00003c0888400600c00000c9400000500609040080381710014201300d04039909056020b68991845110343c0d190090800c00118240c54181c0c0582e0035075410f00d4020b803010301d0030005507000200420b980c00e40e040c80b2a008644112003814014101d0b44211001541e85103003a10300c10042d603680301e0042003141c4640d02d4194a01c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 777465629 1250 777464379 777464411
    0x20a09051903020a1406040b07030504050901090203090118111e0a1212020616030e0322050a09110406031e06060203030105090901020a080714221d130305030a 70
    0x40084030807103851004070706520401c01d68a4403588280040602c0510f110540e6071001d0880381250014200680c2d50b0645103400d4569000e298010369024929200004094400b600114411070140008012001480c800343d40004810304014080c160b00303d984002600705032000030344940c05038000d900581c0303000c000254009910b8110302d2405481110040812401c80c05e044aa031030180060100d03803409801c21103000d440d450440040644030003002441d075000b841190903010074a10b481807e01080a140b0540c800c0501c901f034060925482c0010341c0509512030065140e41108011307190603d00705040700a040c80190f0800070040a0041400c122100e100d90002081c03607030091a20307585882c0c104403910130001e1611100f64010082010790b107134030800c40341c3d00050301d04020046102a006108050184101d502d18102d804a82c952110008128980407182111506100c041d84000f4214141105860790080c9003595030100000038041c00146a02014bc400c000400701d0b4600b00c500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 777466879 1250 777465629 777465649
    0x11a0412080702040c0801031e060e16080705030c0d08090109080a1b060f0c060e1c1701270b0303120a09031101020c0c01030902040b031204060314010e0a020a0905 72
    0x45039070348001092011030030036000c0c0c820010300300c0c200850150715580340c034403400d0b10b007a010030040512030410004004842c0e01c19a41c5404160444a00070b20003c1c0000128403a4001d886440c413885c03500003000d00c1d00007900281000050850780b0300010300e0303076410000d8021002e00d03814444209004251003074204103441c0f542d40505031104030355500500c040000c2c1000e4001e601080311b02105000e01e650802c02c240c3d03215602017000079841c5002d1300c2c01804c292a40602030756a001c80701c100a00b05502031804200d0031144c6151200513640d808040824002c03c0502d208480f218498100000085501584500e14041c0c02e581c5000c0c2c02c24404c40082808441c04017841d681c8030b040c00700f496803080101071b20219241c02149803901500401d992200c5802101c1d0405498002c0d62046485a400030000345c1005001c650300088112288201c540003070291700700091a04c40841c507110001c0079001c2c102c4808048100141c3c0381c030300c84103003c1c0d0320044150080c0064182c00080b40e40310103d50b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 777468129 1250 777466879 777466883
    0x9150e010c0c0332060c0906130510020307060e010e0703021203211603090201020709090c1706091605010806060306010c0c090507031a0a0e0402150d050726011a0412 73
    0x20740701042c52403e044602c1c100134a11016684880c04002243c0313201004c03030348400d01c111102070304c80b05a04043d007203480c09500000d0700001c00d845c50041e20341c0c00201078010746200d03460a02582c03001000250132208450100b03440d81c0d010840030005810701c0b9003e0804e005550f41541e1915054240c0045e03000d00721106e0044081d0000200b115180b00399603c0c02001302145000d011540329500004d40da51068061b451042d41e0700c0307400204004086240c07000414018002e02c6a240209079441c0c1c6030442107a001485014802c00c001c0c1d010880d250362402c0c2c0d00140c5481041ea01c801d41800000d0300000c041d181801000c60111011800c8030341c0410041071034070707000324641c906007000805541c2d501d2820007141c2c12402c0c0ca151155100c42c8000c00f5142d20410144540d0748a00000ea40f401d00c0503045449003600062980c1888940e400986c421b51040c0c43e0a41c10f04003104a09861248200b410380c00c2d01c03c0f44006000000c0c0d02040b2600e80790406e4102810306480d005d000002080788441 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 777469379 1250 777468129 777468173
    0x31209150507030507090e070c020d0f120f0804060b0609192d031104020f0c070e07050715050a230103020414010e010b070203030d0e06060109150e010c0c03 69
    0x1002039511034090075601c03526501e0180f003541400040a030007a0303c80d001d04002407103d9070000d80d13081c0c860303001d001340d00e60018401c684011507402c00d91050300000500b540c1c21000c480b034004115005421018a40d00c0c20b950340540d665950316420700a001d065111071380a00e041190030600c1c2c3c0e8203010309242421310850400700c06c1c541507030410041c40204800215a590b21080c00d948084852020112074000d1400301c04442c4800000d0000d21407000c101d6614440800d50130307503042d0f000805409031580004420f130543c07034544050f101401040801099050514040e00c6401a0380d0440381d00100c11080100340c10f050195400034113400001c4010000340c4032001081585850301806041260300000c0180329410064150742d514014020900750000000f82481152410803c89040058452003000302d204181c40c0103448600c29906580024000440441c3d07140340a24941c00000701500c0d07130840b03030002c0b200640d070100c4103c20a95903400707502000030109032100c0d41d0b10a03183c070943d5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 777470629 1250 777469379 777469403
    0x14010203070f020d02070302040b31060501080f0a1503060c120b0f1f11011104230f010f11060c1c02030f01050103181a06010f0e03070e04031209 64
    0x80000c040100b00302041d41190b00034541c81429503004030383e440503650142c401042d07120001d0081036003607503040011041c501c0458061242800780c04503c0011b801c50010902c50156258011504800282d41d600e0f2180065004200d144845500c030541d2402c0c2d00b02c0802c0e03a1552910341500700c41082c0f1030000844c00c54002d004103402c1078030a809621130100c3e407801c81d0b02c0e90040132907182d0368030b100c0c103180764003e45801d42c0c1c1c403d018210348008410324030021f0164a0f040c3c1c64035106034219210f1240301d403c80d800b880003180916112110400301c0034003096401c0d036600d0011a40d50f48000031000a0056000034618407403400c0c050f0b01d105020101c1155640c0e12071100e01203211082086405010348107005005404803034800160446030240380110b00700610b4080c10100038048140201613403c02000d006940701c01820700c0e48694401d03254000040f002d190140c0709601c006c2034060745600680c0302440800003040c0c22980050092170000c601e9120381c1c80d15800c454181c0002e0741d501d40052 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 777471879 1250 777470629 777470641
    0x534030504090b010924020328030c08041703060612040f0507050a1508100b12190e03030c0d06030b04210504150c0203010e010204030813060503060105030c07020d14010203 76
    0x10044144410017840c050911074544001d4483c00c0c0f141d8015584400103c4a42085051003041a01c0b0340d10948440342ca040c11142c0840155aa000c10484000c0b90800720750b4a007450044101d01c1c4980c1d0007400d02e4492040381d011641d0b195100806142d03110b10240b0031244402034000f143c51050f07100701004007050155040251500079603500040c0314254480003030044444402400201d06100d080940041e20340d9440c2254895003900812004240455082c45035030380d803500740d80a030201c0d40e00162003a90b10007000c015141c0506441025030300400105549202410050031100c419901c00200151603a0781c0b07409168058a041d03815110500c090020b00600d9006a80390480c5070805520f1b040c904010100b4110480c445602840040e208002c1551400e41100400b64840d0000f150344544902e072241c50381d000b20450340b1002c2040c280c007184882c064000c0b28000e401c16110a82903650b00d580b00740407603211001c03c9030071004044550000910016152810008140c0050b071285011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 777473129 1250 777471879 777471881
    0x507030e0405072001021b010e0a03030513150c03150506040311040e0a12030c030513120215130c0806060f0d060b040c0302070308060d031b03020309060304080403020111010507053403050409 84
    0x808610807da900d8003e0640e451040024518030b400c1e81400c01203141e5030395198500180b00310301009010384204068914401e40550f00808002c0c2a0ba1420045000c03c042000d44d01e00c60350240c02d81103070081100b440441d4003101030049841008001281c504001c0311000c6c20301d4040c2000f00c038003030f100708001c1c50362170b4260081e02e004048070b1900b0002031a1500c0c407030310701c4104894043c240350044070121402c0d074800c1c001c1e04401d07504803003407000c2d5062420420310010000132050741c1c04840500081059400401d107503000f410014505500d0749000d03010885841d018810890b1400e6851440034a9607e841c06101d0301e1040c551030050300c4800d18180a4403141d4018001e40c1f050020144120000ea0080b20040300c031403060180e114010940d15040e4603500c640e604442e0301607000301c200310400407044003c1c400e8030301c00c1e030354010b041c030004031468207a030015968000412f80078011070204410f000c50780d035000f100c001400058080005a202c690088007207096002070400203050102001c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 777474379 1250 777473129 777473167
    0x518010602060a020c0a110f09090c0f040e2d0714040b09090d0503100e150a0807060e01140403021e0906011d061602031009030f0507030e040507200102 67
    0x801c141c02c0d03140990041d200c030b4803009541b00080c90300400304c03120010b944500c0c031845030703490f40a0b004100318141280416500c0f01601800c92144a28451078401418140900516900400010025650904c01c00c1d540341010700110a0f4504030f00c81150400356080049038002c100c00e0f51a050307542c50b02010301003690500000c5e5401072041e0814803504810002e441e04054000c0e152144d1240c1b110030074640071101980c4851001481d82080c0f00300d540e15940103099400c01103802400150781e03401d60944a42052052030081800004090030f01c0d4062401403003584911041c603460304d5100e9000826041641c280c1c0e4100d0500144146500e05280e03003059007100c0242400311045007038891000c40c41407200203842c003406e4003080c440325042102030f20421196004066440254894850b4401040d03590001c0d0005a800c1d141c41d08124060001c407983e036a01075481c40c03808034030350741800041c0c20081c04142c100840700401e0740700c1c142c5920000d03034404619000542e444442111720903103070784 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 777475629 1250 777474379 777474391
    0x606090303211b03160302091201060806070f0c080a12110901021614010e0a15080906010906030209040602031b19080901050c0301030f150c030506100c2a051801060206 74
    0xf202c0c61a84925405040035070b6400319076002c1c030030303800c008025084001e401781c141080c0c0c2290444c1d00d4140006019000f4500303560f201011a00c440d60780340011210149145804000300303a41422660100b18000010151001c00782401c0100700c01410851040b29403003c00d00103001e00c0072854140315a414860803c1102c80514400c007104d08011042c5515030300d82c98507034117000c40c0c0340007044d0f01c1d120107034203000611848120f00c4001c103e4180140009a0443e00302020703010b420000304083c182445201d0a4035000341082009540329914480250b00260040e10714040b01c65101907102e80203402041460007048003101c0e0307102119005025004050b0103201180d04200c101b1060341351070400c1e0790440f9040559900c0c202283c1c20000c48030340364401c03611800f50400b48103903510394040d00114010304058440c01c5429025410413114450700480003812104d0025400300a0710f121120b2a0034110022080362820341c1e207500041e039001c550700103801e03002c0b505c0d001049411f03010320035142c0c8a4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 777476879 1250 777475629 777475651
    0xc0327010914041802040e010204051908030a080a18080c07060201061203050702190f0e0109050f04060209010e0607060f0b19031b120f02031e070e060609030321 71
    0x82c2c2000c021118880700320340040c1c00b0f55038580748980c0d41e004541c60701c0703d219005481000a41405103115020b54071078003d45026a60803400c03203407407414411241080301c01c138601560500c001349108844602d0085e2070b90300317070351780315804000c40c50540744140084c68840c130a01541d0f0540c1554981c200941036010b0000d40e45400700400858400281920301d003941860015558243c610004a0703c0075801c2d001200e5070040300c07000c03406400752200c401c2075541e109108140c2daa6203108100541700c0c12200e6441121021020500041d0325401030030401030141030100c12a1401c402003140798000f86d105850454803040c60f500340030018803e112601e1810f68125402d034030f078000070103801c20141c070009000422880074062800a18a24080505500040740401ca80a410050096003400130f06171700c81d001d41e4000c903141c101e107044c10004401048015101d0f440c030b040342000280c0801071005400100c1007242012a44e000d000030a10354101ea02c20481ca281c034401000704107d00102400c20503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 777478129 1250 777476879 777476897
    0xe0907030503390604023c010201061a0306040f0c0c0f02040e0111070c09050108031606020d06080f0d180e091e0a05060601050a140a020703021c0b0f010e1b0c032701 73
    0x2c005010702103101f2250b10b175204801c80301c5c2d9030040b4010001c69000721500703a01c501d1201010a1048011070050030304943c00c0c011112503174245000c8a04601103000030038100c084650000344509032201c11180010000503d41c1c03a1109401d0940c0c0e142402c03144000f100003020f80401035032000b003401401200f070041005605010499a4a01c02c025140070102c0d407501c81c0d081001000c1d01100c1d2190010030f01801301c030343d03181c00340e998a6050308800942030203940078104122744208a4001c0324000c00d210001d030180341900c03800d0340e100054048040350080803500380b2015039500381515094441c00080661001c00d041075400c3c50b101908280c1041001c0080c032000b90361103858050303034110780e1000c16601d41c1c28010a034641201507000a401025400f00c4400317003d030b103464041116004000d002c0d07240d0b850323070000c681044c1d0902903809928540b40c007141000d02000c2d10060341c0c840f0300c402149400d0100c1c1403146103030480c01c00c0c80c5005141104d030414204140030900903084e4203003004008 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 777479379 1250 777478129 777478189
    0x40603060611030301030201020c1c0c0b0a11061005010e1f270602030702060901020f120d0b0d15091b0b03010614070c03060e070306060e010e090703050339060402 72
    0x3c460b50b41420078071030762940181e440b220034060302d900d941d163300038801d010041da070308100e18043d0040e0416001060034211004605980030842500c01c052030740c2c81c98200b6003000010741d101290310782c115403ca05043c0303503400090502c90700e406e9410010303101d102d00007003100300b182d00100700d000d09a20010444202080303c3d0b600001030382c84080d4100c4030a070700e40c3ca4100040b0314042ca2000001d600340b1503040700b507500040d10001032003e01c03034518080c018100c2c401c0c144500e40141c854000c2c0180000349107011111f04903886058098422104c003010369030080500050342c6001c0c0c12081c07000b18004010020300d034100c1c40d290070ba000b15424660514900c1c1d11641d04444451002505d000d84a000b24100c9010078422040035580c0308000300030041d01c8078074802c24240e003401021899140d410110b000120b00040300300407264001e008614204400766014100302000c40303000d41400c9601e02842034990003002c02948240118011b100c2071400b40104a04d20444e9400a40e40c10384000710300c08 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 777480629 1250 777479379 777479383
    0xd03050409020f0f16060c091409041a0901020405030610030b0a0c021c020309040506060c12132606060f030706110a080301170607020319030b011404060306061103030103020102 78
    0x2007141d10705a001621694a49031550b050b01c40c110010f120280c0c001180252007214200000049001301000c20032000c01980a880c0341496004100e12070307940c1038100b15145050080c035580140310300044105000c6828501c0380d0f1030816918030320355035000309041c001810108811b40d4006081e0610341d0000703203191640c9601410141c80e81500603101c04159100078020030801945281c080c0c9101c1a00d030400c540203480f90008421144107604107000301e40c003441c02d242940c44096014000e02039440214100d070701d003640124240348003c000b07442c2c0012038424480c080c40113592a0052143c000e505680b00508015000741810700c07581500b400301c1400c3d100024200d0565141c0d007003102400310044512440c2201c1c9100c02407201500100214610304c0401c2040c80d181059012107646032202d500581c0c407400b44032281000e030a030105030040c07121302c2a04125200841810030a19003144903030024800c0c3e0258205001090f120307603041280550045118000d4030350040550306550469000139 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 777481879 1250 777480629 777480637
    0xd081e070906030f0e030409061a03010b190c0b011502060a060614180909010b1534020415080c0609060412080c030a020d080708060f150f030a02090f0d0305 69
    0xb01096a5036000060402c103a0b40045030126420301140d4540e80d4544104018010900400c03008050012138603100c0400e2406507410b03540000c3c04141400b0312410301035000c14801510310100440c29500f6004100d20704da40a0181154042c446900c7e010410068903004000d484286010320701070080004603400303840c0d40c40050002c0c1c0c040341d41e081c441001c1c48a031640ea040581c3e000d81c60038284030b00800150300c0705000c200c098807810441100102184d07594090482000b20518071491000114040d010302200790f00b8030050131080301400c0341c0210341110040e17002400180d01c1e501d418000301c00d040160f03020140c82101c0e51860204030001040d4507008501c80c038844003030004180e030204032204080d101101c00d0708040300d0701c403e20070000039030b105420320200c4042004c110210340c003688110704240c80307803402600118624200d1424400e2200c6460b1500000900038400500e110000c0c0c001507000380f41c0c40102507200c0036078070100704003a40d803420140d00c07504503c1e12810019410070305503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 777483129 1250 777481879 777481889
    0x108060a031202070803210106091d0403030f0e071a0a12050a0605060d1407030e1b190608060f09040312200c031210051e120d081e0709 60
    0x10716420b031400c0d0582c9031074482d401c0407115000224400304040d2040021110b0b11205840300074641e40c5e0383c5010340362403400e40240c0c41e00c0341050140030340b96207051554603044ac1c460700d00010103640c41a80c0d10219145d401c080f9040e604890010080003440d01c07048161121506d240c030380f41c405400400381c030318003024100d03240080e01d40d000160420069804200208000f4100e260b40d0415a0704403c0100650340f602041e19040d0b10200311038520030304c150040e00c84900021324500d42c030054042440900e400c0610f034003155159180ca04a554044c1c40e200408139910340510605258041200c1d10310b4110324180035a040307408000c0801e0740f161000394090040c01d0009811055005c3c0c48151344003002105110080009502a144e08c0000c000c048110f451501984079480300401d00908081501c5038a070b05c8400e560403480080035400c110001224010055205d114042c81c2940c1800c2c0f0b0b0004040214503000300f04285803001d400b20700c01c10f510003240300c0f040780781c070740c4020f4801d084502074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 777484379 1250 777483129 777483143
    0x114030309010c020a03020603010806040c08191e06020f1803340b0304110f012d090e0403021c090f15020114090f0c01050304080f220e150108060a03 66
    0x21140640d05c030710005502854014142503665a12141542d5580009850440e0303424406d090006202d0004030315504441e17003030404581552003035201d9240d2800c0321505000c0d04c1c411480b1000001366544000d001902440351059161b106040d80440009074024102d0302230b130042020004000e0915810f0094212580031004003050b510380e1042c000b2a054000e00d1404000205110601030342c040b0075442d0705011601d500707010804100441d89500c2403001100c034940314642542d40341d0000d0100d2901030046240088003503a4546114072412010385d400d401582003115a1540c2c0c40c41250081d0714102117007840c3c519540390000500204041d0300c10f102c013800201c481210150720239080030140000010100300c46040c0003031000c1d103840c04c01660b01c110344903580110015501803810b5074070a941040c081030420790102280c0000b64010070314000d9040901071a021009081c103116405010354000c12652880e03d2082d00118030081e082142c10320149200700041641d070800042d00385c03a80504 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 777485629 1250 777484379 777484397
    0x3120c031404120c05030304082505070902030c212d150409060c0f12061a25050a150e0307020f010509030a05030d0606080105060d15031a0f011403030901 68
    0x500311351518a001c030080580c00f000003800240030701840903001aa02c008981203038211072000c440c101e081d81c10401071180d04000d404001000880c2e002d5584a00115482490400c080306044075402c4054010356182001d4014440300d000d00d09509035201c1c0e08458903010007038a602d100135503910010304440426003240b010b00020b8907640c0000e041c103603010005004035201035038081c3c5114001040100040c03d84030915120000c1400b441041300d50b021b0803128421141d034480111a84140202c42d0b04004200034100e041614805d803a20490140000c0c100e035060300d18080d9071079200200b1030811503052081008403c2310103c04c42e10003507030417121000d4254200d001038520380940600d482d414060000e45034113000d80400144050401c044013000019100e0500347d503094001e00801c3d0304032030140700f0001c081e60541d1008100081d12a520002c150b50395403054403159103014110303203214045003401410742e655154a40903000b10340d01c08603001e03401c0000c07a60b82d01501d40c030a07041101c075007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 777486879 1250 777485629 777485663
    0x60c090b03040f05282a0f080d0509010912060f0f0c0e2403280c110a0510020f04150816020a0206040303050d1803120c031404 56
    0xa02024000c01855500907101d2409040c0360841844802c0c1c20b44003401140307100c05401c541e4464200d8101c40c14202403440343d0040d03c8024002000c8401c42060b10325103900131400303042e400c00c01c40c014100c5034071609900341000e40084c1052207503404001440020f201c401c146a81024030142034a0760304054064804403402c02c1009410075451611444c8e16045200b0004246904000d003e060203403624858662040c00703110380341800001540c0c101180707805030b0102c4140c0000075904220950440031311418040200000019582501041955a4a15002c2c00350b000400b4840400701007010b850460001c1e2200381d25030080d01095a22248e002820030480b1a41c1000c0e200648240940d24801148000026100c0d41c030540b1a2038a00d8290000c00309501c1c030004100852076270182c4a2418a480e581d02a925900080a508400b9481758840c060030910380c0f01d4048ac450103030b40c81d00100d00071645000c0854201e28608808c042c00d00000c4001d9030307201605e15400035800f0041183d800707128 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 777488129 1250 777486879 777486887
    0x5150c0a0809031b061608012402030705030c0c0f01020f0714030102070606092301060c1502190c0b1e01050d081306030e010b040204080d1d030f06090721060c 70
    0xa152150191315501840390344d494800620203203e81541302c480902d21040100540d840203092040c0311341c2d080071004045070000350b5004000c0d401803500440e070410030559030f003a086400c01410710801d42d10070001c4406030f01e44517440c4d80800300d0a0024180c03d00f84c00c20415261701c050300076a01c600765074500d10052a1025170445500b5a0414010800240c84001ca28042c02c0703031440303a05400c00030910705424104841000fa04844030340e110000c0c019607507600c900c180d010005040078042d500388142c140080c084003140e80c0d040c0d2156601150300c001c511301a0f07030740c1101500910b0000624220742603841e086200d180c1c15500203d4040d4030701d0390a46031884a07403090b1401c0c0d03040180c0c11f01c1d001940036050303003080790902c24403c02800b04085030781c03d010880c01140f045010a034000c524020529001e0038001c1c0c88440480001001c004904012919100c1d0040156043d0b070f002c181044a120414080400036111401903095801015656680d01c803a5a0740d0241c81d603595180b6105683e402 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 777489379 1250 777488129 777488137
    0x3150303041205010e010b030c011205060a242a0b06032107150b0a090914060106020c01120c020d0f09122003210a03110d0905150c0a080903 62
    0xd041000d161040b800c2c5441c9018082e0001855100c5d1b00740443d4481e54034002c00d490003040d4045e034440030252042040840940000b91100342c108411030300c04114121103442241c800300d01881800d41d007031880c01c0010601003404000c2c09101c0c00c480840c440f0044580c4039518005c1d00407105ca0001d4032403000113410b05940c0e00600440764144180c6c50042001000030b844c01e00c1c005c914400c030480d5640300380b50a4401c02580c10380e00ca00918020300015882c0d070302880c1031601421092904101750440285480001e03045940940c0c400d0044519541c0c7c0071040b6000003862640a12030501d0000c2d000c0d40c0d07901c1c0718401ca01404032000707a8054451140303461800618202e40a02100021030401280c1c038107902020404108890a00001d00e00340024140e072001004401c10a01524860303606c02203400c038a5180b020151108905404100201e01411140d840d1120005050029180407440d00c1d946000184900080c401041a45110741003691240c00a904064501c1d540f908101411441 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 777490629 1250 777489379 777489389
    0x60f060409020711100f0207060503070206070c031107091d0f0a0f05190b0403030e0d080403030b1306031104201c18030c060c1112090f0901120203010f0c050315030304 74
    0x1407a1417001d001694420032419107940c07241c00381c404990b00e441c82102e05210845403400943e200f880400c05d618400e90094150900a1030600c010b108110909410141c880e8019910192900c01451445030804d0b00c0d0a02e08c4244001800580003001d880ea4903a809508042c0011070030b0580f060510009111503205071014041001084400e460b000452001c20380381540001e25105010491603000900910141b1031602ca600d469030741c03664120054402d07004005d40102903506801041e50103030207681c019501c6580c1c80745d00c0030650801d2200b15040c10607070407a00044aa01483c014406404aa13442104074142070640790011301400040c0c500000c2c41c030701424000110005042d4452078200805100c0c085c1444210441001111000000901e080981d000284020400115000241100500070b800c1c3e0507600e01c8038001a884d94070981c0001c44459100c0d40c2035045103800e22a00c800c10841d030b2803c004c0303244c000b4401003e90000038190402084000c81018841c0e80800c00d40740145 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 777491879 1250 777490629 777490639
    0xb0408090306010801020c100c1707090f170c010903031706060f0c062a0906180301111804020a0c0f030908010e07030501140115120603080a17060f060409020711 71
    0x150f913035903241d0b000f580014070442d51030040e501c0d1b02e2988166800780e41e8000003680d9582a023200300c2020740340d40b24400380005040c05400700002540d000f80c0300203440203020707154940c9000004000210304040100500303070304205480e003060002030780200d19042448041a4219a243c1c1c540d0080f400520a15104c03070848200407400c49100000080c015100302c0c203004119206150081e50002005c0e18103034009580d84041c48074811601b04140503050310a80c010078440c142c0000408282101c502c5132008440d4540042c440700c03011038090514010560a403421440d1241030a0000c185500070b0300c0c024034031400c800001c07041c14450a5040d020b00a142d008001c14075202c1c01982d603850360743c401100c0f13035402e10b4124010044260761180c102c8135800c60030200801d144a0842c1d480250100205000b0350713404000c00405c6c4002c1c09002140708684601c251614298041c24115200804507480b825501900d85038980b201011341e000c0f944030003000343c1c1380c41e901d01c0d00313410416000342516005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 777493129 1250 777491879 777491881
    0x1b0c0a0204151403010b090a091a090a0309080706020d141207031a031207080a0c08040605030406060509190c050d050c030601080106021504021905061b100213030b0408090306 77
    0x2250002c80c9039001c55241c0100b525038601084141801c0e12041c0710346640c04032000002961035a801e801821000f4030030f100b44800d599039030103e00d1641105840303000ac103510642040b003c140c4c1040b20341025050403401400c400f850424020b40c0e61000c851000c04200f25030500d54403088001051350010801d913158844c0e140b900781001001440c46008040c0c02c4100600241e205003400b1034040e0000c004c0386826840c02c080b80e240c0d0207607580100111010414159101808603003160302a0014240c10340c0c0d440d90b242018140340301942d07131b19040144140d0007101440080350a07000c0e4140712100740a4041031407103d2903420741d814002c104010703c04505213400c000c0c90700c4103035004610030300c026200c10140e070741c0311b24040b40c0d90300f030340001e491a900c0040302250240c64024040503070450f80710301140c411611440441c1c102c1d00850744180204e1959068800307110317018002c6481c80c0601d00011410007030341c000144200b407500c0c4405095600c2600100f0144003000b0708031142c098002c0c3c110788071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 777494379 1250 777493129 777493151
    0x60408070f05061f060f02030301030b04020a151101060e0702060610030b10030b030607020604030c110f0409060e010c110d03020c010905151014090106050d2a0e091b0c0a0204 77
    0x10307070014004500c0601d8201903012a045004400111b03100710309074000c50540e82982c0d00d200301580050803d1340d05c030880718000500e0f03090399851445440301d070b0f0f610310080044040c801070a4800c0b03600400c00c0351440001b0046515400140030394801e0040b80c0004007103d200006600400c40010040e0300401d1441040c0c1100b80c141d08082d0101c0020f404641d00c1e070f40c40380c0301240c070341005a600400045072401810086120041c011204640c0100f00450ba80070f002d0001d0212191754400b1210141c4411034268560004c0c442ca0321401110706014803012461800705860f615031030b21981c01d05a010802c0d001c0f03e4070035449203078803c0d030003001c40d00c40c16405070000141101c11100300302d103a1141b44000c50a0500c28519500268020305000910790905c5019a0316030002030507221640da551240113400003409011201d111003a00a1441b5030803800c90080c01c003140c902049006140c02c1c8140701c14100100c0d054400c900d0b100022585500c1e500500604101100c000a540310781810400300d9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 777495629 1250 777494379 777494401
    0x601060e01080c03090309060a11030a030615080405030a03090303091a09070f140f2e091208040909080f0f0a090630061a090405090708060408070f0506 67
    0x2100e600240c803408090360b59a1240302e8148000c5070840400e42003071240c2e8000741404400381c804828103050940400e0213120440740b55030811300320400000c2e2581420040c101c942d0300309001c841c0d90740c6000d004503e450344806583e8130809003070504240d9a0105003052501c40d91040e01901e41c0035485441c801e11121580100308021b41d204501c1e4098070038009400e0305030392a404116600b07031080904030300064081041001300c0b10a12a04280c2101e42c1106c3c03500c2c81401c654107a07501418010b11036415442c001c0140b604c68100102c1060445120000b10b10344101303031811508002c1c000b050030085482d08414a014000c542442c0c44008259450304068034401351405e41107581e942207106d542c0308403c031608004070308041080408821112196a40107050800d20401e0001c0818031541ea81421414806030503864600010701090502540c503050040350b030401101802040c000381000d461a4840707101030710023005038000183c0107080150a01e054000349400409413000e80c0390148480c6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 777496879 1250 777495629 777495647
    0x20105160c1202040b031507210f1b050f0412210302040911120714130e01030213060e0c0c010906020a081501031b080907050402131701020703050a050a030b03060106 73
    0xa21950900413040c003a8240080d250b1000c10080440c0c241236110076a044e00c0c078200702e40c105a4080304e05a480604403040b4000d13401003406118000844c01450600400c0c548152080380082120400c155040700c0140401c2d202a41c070706003012291840c413031801083c3c401d060f0700d601810305040b01011416540540c0604100c401c0003200b40506002c05107200303080d20608071400319100c01c0c1c0010030402403099080c0c400182e20142c4803850020300000c100b04050700ca0f400411004070090042c0218180780642c1d0107016400c45052020781e0501200c206000f800800030428202c021807805c02c007240940203044201e8210740210368070381e08000000d0698408a511a0500900146e00071140d40310b8400c103a034032800c3c1c040080f82c002c10100c04882101010300007540740d215000c4082281e0b691f61000345500d45032006c021402510305982410ba088001c0700c2c03412203034818440388003c2038100040700d807458079031300e0803603600d0200700c1040d80103200140e00a505440360390000710b20990000180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 777498129 1250 777496879 777496883
    0x50a0b0f0606311707170607050406080c1303120201200d0e120409020a1206060210020a120e06070e030318060f0d02120103030909051003020105160c12 67
    0xa081a5680e102070016510803ca410341800d007820910351a40100c9208145501d519004010030340340e95202e80422a44400c240c0c07240c3d9400081d4200b0a8038aa400c48a80c2c01c0c0003400641550b207001072000e0b0003405544034100a01c0070190014915001c00001c40f00345d0b44d0442c150440b07294603424400c1030031201c04d1010b0095031810340584584007036004410000200a18100d1518030300200304409441e500001c0500c0b441000041c2c4414110a070191010742031418006854070310204008198223440b000d0486402e03d0010107000c9603034081a200701c2c000e4003a2000d40c0d00e88001c402122018100f04001c44124940325488042d128042081e42c0581c00956855a10b4500b047c209900c82c4030380e644203c400001036080c41140d081201c003502e0b4103414001c01d0b50400c500d0281c010140e90100100c140c0003804200140200742e04462910050408010108042c0ca090030700095240d401c3c2c0006410310401146140c41c40f82240d403502c9500364071402401080b40d460312032014100c866035013 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 777499379 1250 777498129 777498151
    0x504050415110a03420b0c0d02120408030f090a1806060201060b040e062106090d0f0815091009021c050c12010306150e1602010c0206190b030a050a0b 66
    0x580000c40a440d43c00303031105d03c03030311206179040c0004501e0500580310305130aa108084000a00080689150f4060100c403900c44d006031003100350600e0001d040c01102d02030070350000820300c000d000ca100c00000740c07045280c1c0c10001903a00d403004000102c0c40041355100803812507910800303171134800c103d800075421200c50b500280075040e01c486c10081d25005034040d01d109070081e10001007291801191000c1951410f1150325120a84440700c142044002c49811140d60f02403003001c1011640703c1c00803244d0300c80038039151500d402c1c0124103c40814100314120710401803240403d840f450290f6201d0b0040c01c40c10b00c2155038029151b0420703011801c0c070690303800c50f03898600000c422146007400c58000b21044074091340581c0c20369446000400000b40c0d4032040c1026401c0214501c2003500129015030041600034200000902c402800d68144403010030440d0010418811030341e00610201d4080d515043d000b09000c9d0035040440c0c504490103001a04522800051100b405540c0310a03500602c3d003102 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 777500629 1250 777499379 777499391
    0xc030b3303010510030203041b0803041d0f010620060114040b040603030512190204090204091d0c013204300605090c040c08090c040b03070504050415110a03 69
    0x600c265060000b403080030382100d135980041c03071080d10950085500070321448003981d403508030300007001d00c0104d541c010030f00030392000809220b08034645011400c1c130080c2d44e04044092401d03000540d580b02041c4500014025601d41110f80e01513101c0b1100d840d000700404480b0550b0355400c00c600504202d050b03050042c2e241075280040e504050080c2000d43c0d425840f0f0794074009010049111a036401030110341000030301c0140a18201c60340c00100b00910340c1c5000541c07a941005c104c04215410215a80c44103208151214003038200031451800440302402d00740c2c86410b03902c5070750307141c041403501503802c01d0f418094040d1220020b0b406030041d1858544984c2121503030102800c41c0c014070142c0320203c5170102200400081c100e420003940038010701c00742c4074060403180102d001d85502c0f4107804040350942081084440d4108a82620900115000d0008000c1d40d80425100d0103607000b520700483d00d43d40000c0600c0a000c00003d1303c0c0c0102d94041040b03040c840e801d03035216080410107100181c1084 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 777501879 1250 777500629 777500719
    0xf06090615030f0d20011a0a060c0b040b09011401120308010f061b020d02030a030e010e10080c09181305060c0c100e01060909080d060503060106080403030c030b 71
    0x14050807840300781e90080182e640c60140c01d944508100041078070100520445c24600482805003040d00c04440c40224905041281040301107001c0b600404100288e2085d141c01103440c686074560016001151221151995000c1c40d024100b1000c1c0001185550000003c807260f6003c030540913903009985580d0f00d44d13242c007003041e41190144655400168902080411001001c40400205d0b10003800a0740c0181c0701da0119051000008042c0c01180800c0113402e040e58021107507504e5508121080b21007801c3d80030b8050142100a402c01c2d8000034081000c44091701e0728032043c4001c101442c11682c031481c0c070b0a01c2c51180b030030b200e5080b41d9a01900c404241c1022100040d15510181a0301034001300d0709a018800081200c1e0314011955900d5210001d40d03004103100f5500442d010b8400075a03211442008401551404d900550282c4d02902c0100489075100c0021074000c0c2d4140b40114145a140b2400c0340640000310010780e010403080c060890400c911030003205142244610340060740584 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 777503129 1250 777501879 777501883
    0x1e0301090f0b03030336031c020f160c0b03240a060e1003060306110a02010b030604050c01180b031603050a090302190302030d0614090c090619020f0609061503 70
    0x80c0b26400d81550080c40400c03440144040190404002400f0720312545190f001c40c0480340b822a0004403040d000004c900d06240541c2c0300612164480100651904c40b020700000e846209107490f4200c00040c0c49482e1003003089d0440c00c04020b000c030701050341d240e0401081603043c2e0340b42d5003840c0c010804e031160300d0441ca04212010740215482d070340703c105c440c03100c00092003e0210310245503020036507541c034007000140c810f05c40c60401c1c4024440d075540380c2c0c1030000c0103400c403010300030a02d21030352040d82000001400010307455006c080030710b03111407819210700d6070280c01d41580d000428040000700421842e0b510074482040c1c0309400383d4050195482e42c003a50002c40e11992809001038204020083c2118158080150518828812240740402204403e0219105500b291824144840c28003600389090380104d90003802d02c00c1030615040107100040e40c03910884036865036a0b98100d90005600b4001d0000c2012860184150f070400e00d40301d6944c90300c419044900071066081419055030500b40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 777504379 1250 777503129 777503141
    0x1103071110180905040f0c1512141602160603090b0105091302061606051546030602030f010302150901050304111504030b1e0402030c04090501021e0301090f 69
    0xc05400002c59420802d54101a2030b00810903a600145000ca2000142040301000c0040034444016404511035507402020700802075940043c05080c04036a206a0711a0084036401c901404145000c04100c003d050b801c0004020301003813854000c03913001505c00d4160b0090060644140a03450103681c82d10108400c1007000c2e1074002c400e958068501006042000040031160f42480c0d01e48007255156441d4070940b48200c486803091282d800290103103081c111214441c000200444075240c0458020018030440c45981a500e04080d41c503002e88003110740c01240c80a15001402959245490003142491a0b0280700490091454450135024581d1007000d540c0c034003105075280c61844c0c0b500c0d102c100d481c4000999482e8403035016040c260f000c8004d640184000c501c11590024180341454826040341c4140995507519100002080010390b000f18650805080860300011802e80c00c0c2056802401248489440020b501c955403a0401c7ca200c041c5041700c0c4502c4080c043d46154891100c2500c003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 777505629 1250 777504379 777504407
    0xa03210507050d0e01090f09141e1501030f05070e1002010216020f0f060304140c0a0e0f090c03060109060320061608070f1a06030c060a030c1103071110 67
    0xc030790f5180807442d114003100000608145002c840c1a5100c1c0d9500f1500c055036440300b401c1c01d645021503489481c1844145900100454205882080c526210306000d2070090880d003030540040c0010f00581e000b680b15400c03c1c90344000800c400d2800c030380043e00c1e000d4402c0d6503900c10801100c4e4800c3c924414007c50710501100c206422085090380d0a01a42841c21503001d5480440e1010390111034480c500034620942c0110503a076041d00d801c10b0b10307078208440254201d004400d101c40038064030503034560003604410844a07044265036100003260404014031203140d80340c0035580000030103284907001541a68010388a03d40980d1118810300500000484525002a002e000144401c5000c144c4040c100d80914036003850f00680e56607080d0540115901240c004618240d6010704070030a40e40581e01100030b6000f0810003502c40d00062a50154002c050200b58441401c000030a104d81c4414400425800840751102e5241c42c02000d003100d0201118002c00c2d12035074058070355106c1c92000910310 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 777506879 1250 777505629 777505633
    0xf0304142a0f09010807120c03080c2b021903020109020307080d020f0309030a030f020a08070b0f010501020d0c061a0a080106060e060703120c051204051608011413020f0a0321050705 80
    0x1914100e01c0a0401441c807c0603038003d14882000008039004030001d1001020400c042c0a450b0f032400807552000720b4250305007620b42020702100f40500d4000542c440e42c620700440c0464002c4e40c516049000d00314241000390580202c080c002041038000800102c1341c411a0207859010001008044d41d90080e580c0b025403641c00500302c0b00101e401600c011402803414815156410040c0e04d403546e180c0e01c5200c04458000e0100104403010011465003030140c1000d201901610b20142002403036070040ca4800b0301296919501e140182d403105030010040c15000e8040c29640365610185402401c00c4d01c1881c0100e822011411013030b181080498040681c1502d51030300d0982103004110042541041e07107024010200816540c01c0e2a01584c0307403107103104100a100c08140d082094020280b182c0c0302540701d80c1000c1c5050503002c5c2e8841040c2e84201a000900f40c07c2d0264000038200901610520b5002444424040300b032055a541c01c00c50f507040c501c080b043c030803800441141c0a104109c405440381d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 777508129 1250 777506879 777506893
    0x905032a0d0204021b06011d040f0b0c0c0106080313090606050f0c070f03051c090b0706150e04120806030c0109060503060a091505040f020f0304142a0f090108 70
    0x9103003611812107410700280c401414240c8116020f00401c17058401100c20f944040010042051112940412003100303a85050141c1029580c05041030001a002000d4207910000140e42629460580d52a01510b00003401416610014103449900480300c2d9008400204400300b01403100e03004030021034000703607940c500d4071010780c0303209055410020900340c0380d0007030f81c5e00022000703882e4001002460040015045910505100b204030f202101d442a042c000c440340d04118100891040d5403040e50040d802140c04a140c2a550b8140356035500401d940c2002c0d841840300b07000316449081c44100081d00d91741c049460b0601055507070421280c440340012802d001c20b00009115001440d0000c40141a414005840300650002e07240c0c040030075100400c0010041050f450a40142a5440c1d4822011031422816000c0d5140a110007407002e00211601400b41c20041403c019413240d4003244001600c8c10000d50002c20501c0c0081c81d409032040c095400c020f0000d1a11008039812503c2e01001420741c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 777509379 1250 777508129 777508213
    0x209060607170c010905070b1909050a120303110a1709060402060307030902030a12120b0909030429030a090308070203090102060406231009060b130501080a06090c090503 75
    0x8541c80f980d003d100340e540310141100011010000e04014020003040c05031502e0404e0b0740204004803400540c8200704105004102130780f1000c0b14002030310200c18001c03070a006141800d5024082e6515030902c100f00000e04003c40329070140c0d00b003c8120304401c800c80f00e500d4a0300e030160786250036033f03020303501080070401305070054000d91220701c01c1c604c0981550021203984d118031000094000d01d80b008100311018648075490f0034441e845600c40c1c01c50748482d5504080203150381c0c070302507405400c052002c946000781002c40d9400d40c000200500d4010123940c0d151402c285405030a203030104034042819100410109800441a40c1c15084182d005111a07911074075494081c12520b040980d6210030410038840e00c41c0200348251092243c0c440d144001481c1c446428101d4220b40c1c040c9a0305e80092240a0740901e500d0154422503009181c0642c1a4554562290040420360301041b5443e1a01d031701000c001d0f800540541c21a10118240c0e0f8a0402c0c01c0c09450f8230114038000342920b200742d030781340c414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 777510629 1250 777509379 777509423
    0xa0b1003050c0d1a0a06171e010e060103171201121b1d06063009150c131d160503090c061e0a02070305070603020a0f050d0b09010f030209060607 64
    0x40e2015444001041d003640d0b400701c7c100e9400d01d102034440309400511003ca011030030310700c00303000c9040c0010007000f400701c0381c0280540783e041c103000007080e079030560340b0428458082d14152030141032221900c41c2503582d105031114a40c0d1001d030b02203a1045a4031000104000f091883c10101d5136107082402c0c81b50f000305d07814a81c0e0b580041949510010074800031105c4428106110a43c860b0074417040c94120090018100008004200b000c0c01d500081c0901d40d4075580c800819040510261a01e44030f40c00310800c03261181681c0c100c608801c440c0c0324048004000c500010b0300500c10044000d422243c543c2d0200c480303110407145100144e0200c0042c2c407170790a01c0d400401101801c090483c0d441748400040081c0c039031001000c00f00592040405209210003803004500600303082c01d08600d06420050301074207002c81e20b52240d041c00340c04900290040801c0d0800001120010120b44043d0b84440d54103407a207034903020590003580032400180480c14018100c502c22600403c0e28480c1410b008000a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 777511879 1250 777510629 777510631
    0xb0a05041205011509020c01061401020307030f03060803030f0f090d020d0c1a011508090c09041707050109030206011a160f020d0605070201050610030c0801030b06030a0b1003050c0d1a 81
    0x9038590350310710704102c008109210800280600c0c1030056900c03284280d4490035a0110340040d1380112001c1c2c80325156030780000c00c03109c0ea5641401c0250320402d03d614305900a00160344a600c2c540400820807901c9040403a1041c4280103456401949840e04440340703903134500344400040542c3c00845c0c2d03a00e06a0080a81400b500e00ca218000581881c040e12940071003020707840710b10a43e1101030100086904000104d0b4403c0c3c50500501070407034010300090714188042c3c0048d101440412201c01c4080404c4c00300c8503110b800c84c00030707c0460f5407850001c0d6600c44c00d1082d01c400c0c0c80c007202c0e03407005a680c29046a004030030096070140008042d0301d404001d241144022a4041d0946402c3c2002501038014544181c1c1c8640000486180040034800c8680701e0583c1c640405281c0300128240c50703088216903041d41d402c01c0d0420b6841e942e180c0820714081880c2070282c07001809008001c05c1c2030b5203200480550780306201707a85c40c0480d80b6091280c071200c0300310018404054901016141c043c104212 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 777513129 1250 777511879 777511883
    0x203190c20011d030a08010602060415020708090d0c170c0901151e0513050a1512020c15150909030f0d11030a09110f18041a130501060b0a050412 64
    0x1010003621590f5040e200d0b00c0091210150404520f0800c0a504211a1030061841d4005040301d481e01b03549405c0e50020000c4400030b55580803554000b44003204094030316880e40603140c03640d0000241081c151102040c4207506a038a292030302110300c10700200e02c0c4904610090b0030248682d00b40300d11401c0030b610700c0d983c10082101b6502901d242c0c3c900340b030001001000035102c0c1996865004060501d05940e130b080a40210b860390010881358040e940032254070000c1345001d80d0069680c82c44072010b0b00c16554412a0741c428940600083d660b60350680d8014200300301820044900141813256000742100c03c0c401c0303504240102d600803030410700142001c03080c0100014141d5602480b606954005840740807120b0355924404d4204049002d002280500c11256060601a80c2c40091032508903114036940d070014142c0480c08014440701c17142819030035540c50100c58a81102e00396100c140040b020348003507081100016800d104001103461003003096550f10b24040c00c18038035511442e005c11003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 777514379 1250 777513129 777513131
    0x3020c0d2a080a0810050109171e01020a0908010504020604032a0f05131b0c030c0c0305060f100501080609070c061406270604090c08100203190c2001 66
    0x14030340840301c161800007112489020309a4880000440c02010800001c20801008821140900c903680e00180c00b42c04031145d0220015134032040758640341c203110718050b41c0e64851800036503070b0300300c500103401a01040046541e0003400c40d685e04441c3e400c0c1e40c0f041e075000c0d410003000c020500118a034545040050b140c014542e40d01d040d4582400b211882480d400206820a03428040c021450070f140d000346075005451092121424038600100c1c0750410400700024030a030301c0d42410402d40121001c0c480c0c00c0d0010120301c4100d9480c182a07494030300072036100003601825000541e8024110141c8801d4410607915a4015aa0042444003100025011200b4000c0944450b00050214010018441000200111a4104603041c040d080e140404410824101a2a10410301041c6035450303500070030803900402d040160b81408800d903100e0383c12450310780c000c80142440c3d02615400441c010407024000c24a0b80c0c0d800d6a045c011240902c042c2d5002a902075640c03280704d03204442040030461340e800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 777515629 1250 777514379 777514427
    0x90602091801051f050c030c06040201030b060a0f0e030a0203010612032c1314040c03030905180c09120a0506150a0312030507050c0d020604061b05041a210f060103020c0d 75
    0x2c9140345030001c0723a0380c40710f45e4400d00800086507030501070301c00707403640c1500d840b410113594400c0533240d03110781c0040d0403c1100c6550101e019540401a68050a8024008001c503540760004a100c24170070a605401040d0a245400c8510000d50260321906c0304910380b000440e001c2e0002c000020740300380e4075070012644508201240a031021521070107140700d448403004145c40c520b27003d00701000b554085403281021240d685001c1000b0501035178400050400c070307952581d800700051815004840118400e02c6450740d424100036002030001d01810060035201d840d0400c490030095010580d020052820a6008920303900b80c2c0207400c050b40110890074594200025402120f15110700f141c4540c006a11000510091101520514000c1e55a02c42c0859803e800000701903c80e200350f100f03150409040003901c4840424090603904000a4800411003000c43d649100f5032004096a036040d0b0307001c00304040fa080358000e10840b0503004101001d440345889904050380d4441d50903044e40c000880d400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 777516879 1250 777515629 777515647
    0xf16020402031501020c0f060a0c08130b0a09050f060706020d1d0d080603070f030314071b06030f1a0d0c1802030709090603110d15090602091801051f05 67
    0x70014521454080800d00d040c1442031000a1a00c035046000707501807110b06901c512961291411034810381c10b01c0c10841e4904142d403500e100da5100f00d080b81c0309494000344020554203954801050510b04994035051010307110000c00038205c0076040e09039400003003044501c001541c05d40280100c99032401000401001c03488030182410034141d1001007a4011000c04040c076500701224540000081d401002810300b40540c001d5400c03501c8c08040c091000701c0a4501d0032031101d03002c48d04010380c0314141144038150a6030100002d1664000c0d00c020a084c545c0707500e40c47d1024818202c4008090344980c03607080799841407000c103108100041d240340c81c0c0c003400400e080d50000c82c0546190600100166640381c074807001080040150000f0321400d00741041000810548544150f0380340048504c00f100c3c24023841c100c20360148010410014900701b014400034800607030301034008684165495843c20404000c440303d41c040034044d15511400d1b081a950109150360100140414282026840c040c820 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 777517985 1106 777516879 777516881
    0x1014090606040b22090b01050103090506010e1003050708060103021c0b0703050618090c040f0c02031812120c070609050f0d020102190501090c0b0306060f160204 71
    0x14105454481d5188040030304013040400c0c842c000d0381c1c00c5148450207070800038800e5035041c0c4c000e800042e8550003070180c0c44299a00001405c820381c00c000d20040f48107005016071440084003103000c00020300c10000d08024010020013424150300d5403041003c8103070000c10441040d84c600760310200003045003125580242d001c1c100403500d651000045145410540c090400601c2420203201b0003007000300745030040120a8900b480409154004141503603a004280c0005034020040343d0800c460082c800b41c02100f0003070030021140a007a0f002440d02030201162074905000180e220003403c801c02171100100101c3c2440d450340d0b8617101c001076107110104629401469813445441c02c40e1f101380040900c081000c1c0144000c06c1e80c6044c018000c040d0310380121040015007501180c1e6200442c2580c1c0304100083c40d1600e810888040c004054000d0301d0a03801b10894880002c0060b92a = true := by decide +kernel

theorem cover : BRFrame.Cov 777338129 777517985 := by
  have h0 := BRFrame.cov_init 777338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 777338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 777338129 ≤ n) (h2 : n < 777517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
