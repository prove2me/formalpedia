-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2309
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:19:04.958983+00:00
-- url     : https://prove2.me/submissions/6ee6dc46-0532-46e9-b4d0-9c451f1e01de

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 415107913 ≤ n < 415287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 415109163 1250 415107913 415107919
    0x601030521072a061110060305030403110d05070603060306110307080f092103010915080604081b030d0b0f0d02090a051b0a090513020708030f0c0415051201060519140702 75
    0x3940d03103400185c801c1103681c049a215000c4e600071016200c0c501e01c9040c0540340c0042c011402e060540e80c4840c84204080c00356607120000d441040c00044042100b203020b00495600464103500c1c51800740c065510341940c3c1650058180100071035a41d1041c0080c0e030001941c1034408550700d50074000da0034102281114040205070f003406c103a80400d01c00082d81200c84498003005040110150021441c62600960702c2c1c0360000000700700811025009020b21000b020303118a980e00c0f03020a8203180d40d111560404413161124030b9840203151010440c48003210513201b0120100742d0f40e00140202c0300082481046503654004204005d2000711007003000f40e0314002d4290b41e03450180340640b0340790040c41000d00c10b080e070b0700c2c0120b22a06140262013045600001481c15034894050050105100500c040800e25040c0000541480500e01e200303000076258458540e6000d80b16040c80141805800002c180001081841c06031424820a03180d04c01641c608560100092440001107200e04c90307000c2d40c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 415110413 1250 415109163 415109243
    0x6031c12020d051e0921120a1505090601020a030305041401050f0406150b0711010c0813031b030b0c0304030e09161803020a050411130305060103052107 67
    0x103801000c1d41c850350240c80d0680010254440062040d02c0d13010045400c0c403030a40101800c14400b240308084a07061081c00e0513400d0034020000104035280c2c0c0116288120b40b900e82140c0c1c902e001400b41507101401060300c0244191034074000103980c0e104410720040815548900280c1403050f86080000010246070082c481e070709042c034030000001c2081d1404d4403038500d040c264001c491130b103030340900445103c0d070f941c00d05000c031a403200c082c081070902032241444180d035124000140d0401c01024092412644040700900354181010035050250200310a0f80300c0c040e051002c50382c521070255001d070100810303a940e0b55803031030110360884130629036075013281e450000d000001c1d83c0b9483d0904911903690740c4121700b02d01401083c5c2c8000d0b862002a4003c07076000c0042c00b180c1096084211000266510303cbc2c502541010600e094680c3e50340156070903002540103008016040c0030903002c01481821040c10104032140c00184d0340324004000300700803103400c00368036030081004001c0960341318031450130 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 415111663 1250 415110413 415110427
    0x6030507060c051b010e0d03020a140d200a061e0c03021215090117030c190c0605070b0c091c05070501080903041206110c07120203120306031c1202 65
    0x1400885540e101165a0700884640d80116501030000c0b6507400c074160b4030002e5103030340481800707452800c0107c10340c118058040c001c00480e1040342c2081012030924003d00302c8401e2850018482c0d094258200d9445900d002c844c0d111500005000c1c0c0e42c0c581000780090103c010f00003140d003042001d000c0b00c0134203081a0104035225055030281500800fa0785071086c5941d00c030005a40b5025140c2060340c0d0099821005001080020306040103446402381280c2c54011404411032604046250400c0f03515041c082d400208442030110b000189290f09089082c075100c2c5e9100820030303034018508a003414000c100f8890701ea0f1007400c480000041e080d20110f0310900c80c14420b8440c2124003880f808160a0408200e14036400421981180c050341c80f8030403417060550300e00000c0c110111010044010a2041960406040c080f140040c811114040c80c1c1041a00c10f160800520407000c0d4800e001c28820054507807002b00d00140081440700c09240b100a00f0703842a01c02c103211000d901380700e034400302d210 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 415112913 1250 415111663 415111667
    0x5120c09090102030403080a090302031b0304080f0f1605060a030207020a0302060d050915012303071e060305090111070b13060f0f060b0901020a1e05010203070923030319030603050706 81
    0xa43c0218007e55034403200f07986155a0038141c5000180081c0180c0c8200f2001301401034040300c660000705582d040d2032905039a4580300786854204612030040350031a0a02d0202d1200c10080001c510200308801c13030604c0d16040000b600380c0103d0080d00c09050300010707200115511840c0290196038000e00080d119001200300c0d0b002410125881c1038988034410880b403075100d02074001070488243d8040c2000912400c0a180c6c0040d4641d00e130301e5014884d800b07020424045200b00c051b03c40e44114682e0801c00c1c98510001c00741c40000c1d1009c842e5900d08500b1400c428180300c02c0344c41c242c1d0001760701040c2d51100c40d42407480d1803040102406d10340c6840300088450300700d030300100c014282c0b003001801142d0b01d85003100d40d50700c182024180582c2c480050b1200140341100840c554680608400c8100c80c1c01d0345415099a20484601c800201c07001014400d0800405501c03910b1400244481d8005030014007282d0307079109400c400902c00b07824584c603414542c460b41040d009160f200099550f201c0d512440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 415114163 1250 415112913 415112917
    0x41d0402040b0409170702040e0109121806051603050904060801020c0d090509011203051608130b030609220c0f05030c01050705030406050f0910021c090f05120c09090102 75
    0x400c80c440e9060050b05211031420b0b000340c110b280d400050200b50480f070b003900e8a013242c5c0840012070700543c49004042d00054203215100f08140a43c8840340c21074000c00000b46032005044c040001d040490400780b06c039540c03080503580c6400440e2001c101c260564207081d2098025004170650240c00d14501084048042d00a411a5031401e0121250b1010f800000d8540480c1c0d8000ea5400c40340040040005008080780d44c0b41d00c03806070400600d08000300c2581c1c1600604044142c0e100b8038001480034450304c0c03900750003000306242c02d1114210700308140080c1c00c5900160445104030b411100c02c0d040d402e000031480d218507902103041c1d142c141d5100c03c603030310081c0c0703a200c1c1910034080e150855200b5409034040710341e0b1950003c0594582810140e00f954140c000004c10031603203100340520025903da00b010440000616002014481d440041c200481d440c801c849108200c4044000c0003401c15000c00d0b0400c0d11800c480046034100c2d920106494002c2461009912081c0c140a04c8980031043d40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 415115413 1250 415114163 415114171
    0x50301051006140a0e190b0703090e06010305010602100906110403051506010f0c0f110a0b12071b0303051302090f0a0e07032f0a141905010c17041d 65
    0x210f11155611a038a00c540034000c040900c804649400094811450031200b00980c0c4160b40340300340c03546915031050344e01681000e042100803c0a038a000d01c40c0034070b880001a030042d42440d00340001e6050500c025103c061400083d014a500c40b41d40c1030030040250002d151000c0008265515559207080c07450faa0402d84c020041042419000702e20a544036689502d226000e41e1650514030610f0b81d00c90a0010300c81405407024100c1c8250349900317136103d0405400410041c00699101c0e0b03c81c1540503941803001d0103400501417541740d801824002d14192400c05034041c28009040e43d904840181d0381d12041600950050705d550802802c001d001104a024058010080180000100503503030340381c9050002074101c07000c0e854484298400100000407001e5600000355659108502281540740310390014007103c4214010005903041400c82c2c5541400c503a40c081e41000d141c1000030b005480040c002400c8121000020025000710404680c0281864900b07422001c12141c0380f60042001a2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 415116663 1250 415115413 415115417
    0x607020307021806061c1104090204080f070311040f320108060c0f030a020706060b0910090510080612060106031407181701110c2503030e060306040204050301051006 73
    0x80c1c85103207280090f000c03e0310441024002d0f07441c0226500708070b181a124403158890242c0c0350f03002180900050700c0a44010083c200000d40c44504040100d804d210b400070030803030582c0c840082000810307119404001b14a04c260740c002480b180790b810140c094080000004646420800808050b07502d60340e550300c52240c0454045000c0e42c071840c0c19929480166452f0070410f000b0f0107665141c81d007000056800414080c2c1c010300c1d02409507107060544d81c0076803181c05150700c0801c40ba80d46003040c1134162030340d5190786050320000e410000041d0820007907800c6a4100080e501c0011060f490b500200d0600c00c0c164001c60343c4643c0c0d90000103002e06008000d1301c00c1c40c2c85210100d40083d00542c00808982c4189200248160030900002c000001172030090001d50340fa680580c7d00c1000e004001c1c903c91454038090305031400c02c00100e1002610314054141c403000303841e508002181c0d0110040316160803c0f912546d80b40c45960024001e402140c02c0b19615510780014000f540003040d954004641e81c82d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 415117913 1250 415116663 415116679
    0x90406030602030426190e04091506090605010c020310090206121501090902030c1e0f07030e0907090f090f0f0f02090405060f010c0201120f061206060503010635060702030702 77
    0x18a050178458041c011400c6803945259200403000c0d0b0150702c52805d4008003030000559000e07d81c0351048011f18030000060007582d2080c00f4811001e15025620103450b0070300380b03d0b15980242d404280c1e59614108594440c1d681c0362111000c56070b030041141c803e0141480c00b40080d0a1901005401021850441c1d000c5188884000b494500c01e00960384180f940140190a0a00e550208803030646c82004900c4003e20801c01060555455000b81c88070034003c1d41c0d00c000040b040e00038003c86a00142008040c810b25000030081d40480d4202d14099440090021820760b05130380ca1900580040628428014240305003501c2c440e26680c040c0446850482d010700c00c1c0e4640c981409041e4810383d80c03040c0040c40c8a5103150255000d924900030348a0b0b0040d0014041030503220820840b28540c04c01078001380d01e000110207100d00c40c0908000b03410200c0081100c1c500d00004005c0c1000c0d000111008410101c00702110011141902c042214a04007681e40910b480305000f5201c0d8000c1d0000c1344a5101307 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 415119163 1250 415117913 415117973
    0x9050c0c1504020603041209030b0702101a090c0f040f0b0a1d090a09020f04150303090605190e01261806010b04031103031608090a090b0a09020904060306020304 71
    0xa546001c0c0e00464001d0191895900c894403110458040c0d85401e4050100301c107800400078201400d6284503031046d902404401700300e00d20000640381c0d007440b012140c600c0b012103081b0700e41d200030506030052504c4070038950b94041908a481c40703001e0b03584100158011888000782070010354005040b102407903560759500101d15481c0800a038012015141c200c01c1160004408040d29409038000c41e00042c600060101d4041c00507082d11180c06c1c0d406404602590704008264001e0030301c41c0034000e03a0034454101000502800400c5044c542080c080100780070045030164020004042d007592684041018112003144041c800101910300d00c002c901020103081c01c40d5004a8490f042e500c4600445192030b155171100780081d03c03a9001c41c1c0d80341c00304004a0740f1b90a50040c200e805144191505c0d61146410f03002c0014510942d070240e08002c1c200003c000e090780d01c0489071800c1ea005e0880050f2981100e030b01050007082d0540008002920001c144400e02000d401c040508035001034180303c1d040f02c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 415120413 1250 415119163 415119193
    0x11070602030403060605100c12020a06060f14010f08061c0f0b0117030f040308030604020408060103121b0b1609080f0610050105090312030405011e050a1505030a0807060609050c0c 79
    0x3080e000403500189000123402d002804003001803d184030540304886866042c3d8880700225a00b41c2d00030702c0d0ba801100c10400816030b00040e030f42141a0709003403030b8400021004019203142c000030100d030b101d4805000800c50003e170075001c00d24446d42140700c4042503145032405903800002806044034240038841d0310005c81c5000030840e032241500c00303c21404c041c55a0740307001842e0801340a20745e00540900c00403c0024081041074029400b46c142904008a481c80261042e000c2000510900840070070050104180f04900ea81115075900e44007000e00940030116075040c034941150059019141e024442444001891070140b031001403000810750355030740191820310a801d01d0a8168102800313903031a504054015543c0075008000124501104100c1d407060038103000108020143d91700c05104007044207100e4000c1e03000c40a020f59003901e06020000780e44d604115801001c032800064a04108001c0742c200400500c000c01c030611103070070710014a81c0c040d00100c1d002c140341e118680952702ea041e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 415121663 1250 415120413 415120429
    0x31703040b0c040b2205121b010801050907080a0b0a1202130c0927050109021206100e150c0a0503090907021506100c0209070e0f09060f0d0311070602030403060605 72
    0x1800d000d07542441e10124802c9000000f02117006180800d40500f00080c281d282c80e200405040415009003041c0300500352031008070120030000d00e0420000e100140216210342c140142c0040c41400c044200c1d50781c0c004c00c00050311800398440d0b0400118000081d03800325404041c0c10f003620841d180c001d800c0705040d04e0310441e11003516100c001514104d040101c0c1c00032802820140342c0c200401156220400c10070400e50f4000e07444170059590000702c0c0ca80f0203c244031110b801c107004070b941403894035203510018582005815080d120f0880030080d14405200c5000301c0340320380d05c40c405440f10414a4280720340c50341c03c04d40080d4041c04075180001c15a0384089003250030245018045c041035100d4000b4040d14911020030801880360308083c9002503510003009a10900300c80e528084c20421001c2400181c54030386090b6401f1711004424000342d030f603d10068194114041d10f0300910500c0301d0170101d5040007111200e416a006071640440c01d01e5012000304240ca000e07a6040c01580da803102032148003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 415122913 1250 415121663 415121669
    0x4022a0d0e0f0d020a030c030503090f011d0f042004090b030601030b010e0711010212090c060723030f0705030d200d1d0f01060807270c09031703040b0c04 68
    0x103101c0d820114640f8000580c004400d0010706080e401c1da03200c0c3e0f11004c200410750030507507150707001040026003850700131440719060b2001c0c41d1442d07002c02644820a032a0f81004007061041400780079110303890715103a00503d81c18003005000040d0008080c0d1048459000340550301069084c09480480c40c100002c01e141220750144d203c2201e0780c43d000001c098000c020382581d08110000300710850040d024005420824a03000c0402202e003032080d006481c10380c20000c043d0103a0414040301c4082401c1d070b160051074018203c03203d84a103440e182c1080c11841011011424404081140e005001c1c0000c0034003041000b0007010400000d508140941a0220346244400c1039010031400c5075881c600c0d00004c68007000404841441704105d6a101c0c2099194030313034502035a540701c00c1040710070000c2002c60000c26200c0c0c1c2110000a0700d0030081c0f00b0241d86181c1c01c0710591500030300c070a41d511596442c001035810041c1119201c010b00c1c540302d02c99109072802d48542aa40c400710f9960702c1c0880407135080b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 415124163 1250 415122913 415122919
    0x3030f060f0b0703230d050603250501080903040e0106020d12111602041401080d031a09010303140705010c110f070605090103151703040e010902070f030e04022a0d0e 73
    0x404240c1d50b01103443c03104148801c44105d10b1101d4080101305210b014280e160300c2c1c505d001c01e480c40c01c1014545491400402c955085d80601c0c024100000c440c030066060b00c80a00e4505060343c0d03801c0103940f40d417207141d0001c078002c1c002000008015501151170490f1b841990790b202807414140541f41c003902c500ca140c000c2021070402100800b03038072071400d00080d0b0344044e2020405191230710720816500800d0340101e6950700f145050100250341032213040c5800740c030250799418651410010a01a40d0140002401d12084881414034101c0040076a81303441ea01c140248121300079500001c1c029009030800703002ea4403528000b86038500b070104869050300d026985450a0042d950011806040300352103401010001c0c1002040e490070300c1e075808203101010402569513500c0c0071701c3c1e02c4544d80140c0c0300d01402c0f4030602c000c40014046071340e0340c071600750180751011032000400300040003441034111814409aa1031840380751405c1400b1000b00341d61000040e6000c0468075081921005410100c1c558 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 415125413 1250 415124163 415124167
    0x132405040e130f020405040c14010809070b030c0c030d0f0c0e18150901140a0611060403030906020f0a0c03020610030213050405150703090b061c0b06150703030f060f0b 74
    0x1020904066a82e0b218030300903c44102d5401050300860116501590241c8410541c5001400103880d80865803032442800c2c40c00c0100c030700e4500d0b03c054681c84240107086038101c00001186c03000d0703000f0064407422503692007980c1d5603217815400362000305621705070322050a091910000c0000e020b202060486103000d4400122880c41d61701c21062400020300d035454411021508074502c1d210b40940c50b0181440940717400307081c0301c03d000300070305040c0c10b40c0540e04004800030a00155400495040d03000b5174142008502c0c841e4514007807010b8000e0800075148403001013a840c02159001c201c03a02403d02940940d013241d111445e454039800c0c92400003075080b001c0c82a6001c2816083d50107903134018040c0d03080d40d1407440d070011b150100410603944400000e480e0901c80d01880f80380c0c2d90a0340c0200d4100c4001c0f03101c10b00b8443e074a009035258a4040d02401c20900000c03551740358131403d0319812880700c400555030483c5150140c000c100711800003d80318078012001c10030320f403903460803403d56080c00203442c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 415126663 1250 415125413 415125421
    0x30c070510031b03052a0d050a0501030203070605071a16170c040b0d020d06170106050402210403090302330301050d1203140f0103021e01081506132405040e 69
    0x24002c0d105c082d0810000c0492540f00030000361900009058601043c10120396401e10004208180c40028004030001e61914004100590300001d42c24202d5966040c2145c40d1003460404006510224809402041010041160030f01c0d9207070b2800703101034158480440b0140c007600c0c0042c8025080301c0c5103403810170821050000c096020090601069480000f40c901a81500c2540a03a02c1da948580c88001500c60540b41a20b030071f001e107074050031054900710706205a00d6191104a41c507101d05200c030f486554080780034184111010400366401034404801c05d00790400f90b009030540146500408085e101420049404000440e410cc0d0130090110410503071685810b0407600600c101d075400d05035561421180c1c030144c0d88100740b10b10002c0760420883d61542c014454041c8107048860300b00f1004d0011006280c0e002014141c00003890b03410501d10031020400306059119880410241140a8000040302c3e81d02c03041e6a6440081d08044299a042090099070180940c1c090f40d030440641c80002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 415127913 1250 415126663 415126667
    0x40b160e0f060c16030512130308030603010219050c0c12030f0a050d0e011b030b0d0803060a0b03150a060c0506010315182a03050312040f0203030c070510031b 70
    0x494154900148560f150100e082e800304e00d004083c1c0440030154400c14410020701c0024400d0344115600e0104d00c034580500c190945a5400040c0801000d004000c000300b080741e1000d40c1035842c4c09407800e00e800a0380c00207403009801d0750000e2a181e0880d05c2100341091590601d9600c406d01e40401c48000d5007000102c0c0340c1a2070580007103d5600402400f800b100c01d001420380125041c0c81c0c5034000010702c19103c411401c140c2d12400302c2000a040c2403a030500307025212100710403031030740c0c0140041da2282c444e43d00017007200d5010390004040402c08414400c403000150109282e00340119142d02d2081c0c0e55103004d1b5500c0e03455040107840d6400010040011074281c0e60700c08180a0045000a441020401101c188182103201680c3c00e22890025040103821118441c440511510141010071f1640c2c0d01d03180e903407040000d218807001a10010504200f04880b01d01c50440d801801d6030340f03500900c0c400c50b03500c0001e4816a0700c00d045200b21141c96074045d121f10301d80c1103003520140181101c88081 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 415129163 1250 415127913 415127929
    0x30a060f0504020903121803160303030f18110102010b1815040603051002160b01030303090b06011404061107030b010e24060306040b01180603020a09050301020a1707051c05040b160e 80
    0x12000c0181d1f5086480a8203540a00c82c50300100c441c00ca0082126045041c01411a000036524459031850681680c10140908031300324651544540251494407040c00101d015001095000760811200450800c046000c41c00d014403d0050140c510000c508610820054800c54403001d08a40c014203010f40301004681c0007807480240c07500c074601d1031040540d910030801e9000d80c41035000a03900c1840030208880000714a0300402c0034a400e000044405e8814503151149d4402c081c00d01c800c104100040318004d000441c021608890040c026694a51164041c11011111401402c6404004868414500e560440782c00d9000c5e0219056607a03200501000b420501e040c0c6050090708604501d03107400050011028000301c0d94007680b140039100d0090003021b00d50300300d280f20f81d006021841c90503a001c2407600d0701030742410341104503440e001410b982070711071a02e075441e84c10300e5680f9445110403540c02480c081d0b031003094100002da4925078012107120b00214040000364018820040c54500056 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 415130413 1250 415129163 415129177
    0x20d14120d2406052a030a030b03160f06200709060e13111e10030c0906090b03220f210c0b0711011d0609060606180d03050f030a060f050402090312 65
    0x180c200c40f00017030886210f241d50030025521001275260341d024550340c1414000c3c5a210300c940c41c81403014074140310b618018040c0d00d000e014100180d1102c444050703213007400150b07030102e00700055844e81c42d140d800110150055000315886002c0c5c0c00302003980c2d035a0901a5001481d00050400c0e940e01d250401c200c1a0111003040460300006050103860554031064000414000340d01d00040e1540c1c80d18010305003201030b5111300140008408100700c1111030400700e80d4130218034036000841c242000d540080408000c84058801d10700d04c2c0110741040090542208200390711503403d030880300310000854010004800090640b0510008222203501403060410101400b0f000411084505002c41c41c464215044d003d159911110038000b1616040c0f1806400074410360341c0d1407801403c030744002300c10001c00e000140a03030943c4070700c002030610810650b00c0142810340f0013580ca0030100c0e03c440c0504080c2c0916050358050100000c2c0764038040c400c5624802010b0007421512100141450b03013600011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 415131663 1250 415130413 415130467
    0x30414060408030a0c050d0509150a0201090c060c0c091803030e07050d050a06060b070c0e04020307030b04050c0906030c0a030b04060605040207081207030207020d14120d240605 78
    0x4070002c02c00b500103001410041c81d103969880241016420076528280c0000720340014080104544001c1d03489034142c40c8020b4082c002d5240e0354168101e400c13030041c050008041e1007590220408203200e54008444020103018442d18480191561900710448400c081ca0f51040e8a921550300c001901075000819609250301c10380e03007202d0751000071132800745109504580c15000302c1410020031406104200c094048200e1460400310183d50314010804503000701c181c030001480005085641c2000b00e035026580c400110380c014101850950703599a51071040c1d5208403901b100154860900150308144202c009048406a91071500c03a900d9170315001d84241e80030307621820042510740b1140028505503125100f2241e46218003e20b80301054000340019080500400460300540e07180302e01d4400c410382001c5a2400c1d5086540c03228541091100c40000100f000309210420b9074443d444250340381c9020307119440c0c00e0381072800b04403040058040d8030301099060120103a5035100d1910450f2450302c40b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 415132913 1250 415131663 415131667
    0x70515030403230f130b04050105040506181c12140a0e03070305010e0c010f030926071506060e0303040b030f04020111060103051006080a0f0602090604120b010303020f060903041406 80
    0x201400843c60b07442400c0d4144403150019410322024500d964290041203a52416030500b0300b0030300001d00503c5030384505445040045a004046213038030350b0440c0c042000416800c2e0400c4904142ca00e0003052100540d6100800c203800c51a842c01480c0030403426410049240c41c00781340083c00c0d103501c2c56001c40c082d014480d66401100062092043d9a04442c0304c80c010240b12054000050100c0d80f840f889070101401d000080c0d0026550003041024460341404009201c05030315840c0f406401034580140c800950700400c0b54000b072042d8014000d0b645d1981d1285001006002807603035034851880343c02c5906104200051000040d4250160414030501d08421086440030b8110300d0030b4004e80044c1c0d030b990807000c606118200ca40c8202c000134051100a8001100e051301d40c840007016112014054a03000078034841c06070764031012a0043c00101059006403911400c1081c903240e400d01048015100d1107880c881d54040001d800e80c031814000d40110700d41030900010048008480c03003039507082042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 415134163 1250 415132913 415132967
    0x703080402010f0215010e01080f120703031a0409060920010207030b0c04050307150315270b0409030809060601030b090411041b020c011404050102030a0305130204050106020f070515030403 83
    0x545c000c0b060003081d00e051341000e1541040ea24a0500600352003c0300d0640c0841c01c0d2140d4420300c1c0b001c0c0d50807103405007000a01458008048400c8540100005030711501c0e21040c002084074a03840b00f030400c1d00511084401c0c0745070203500c540e84254a01c0a5003da4000031703082001452a6030041d03800301010000b00d0805580302d01180c41c294282e000348880880c080710325104154548110031040140c6166110b1040c034041040d81d59104103515130000e003014480244c41940940c22032504041c0207002008012502d040041c070541090311b4500b02d50180f2004035801d58841d004465404200406141030b50b1100da0320034210001d0609842c0d0056110105101d180000e48100d42801843da009042c0c1c141e0010001401c195509800f10711029003808184941e99001056625890050a0000715511a042200344c04004044020f40c0b181c00c0100120b00c0b1640400c41d030251240c0c0038103c0f004a6103400070001d89418500084a0a0720280300040c04244208c0c804201140020440010180 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 415135413 1250 415134163 415134193
    0x21b0609221409010c0203090a09020d1e06030c1d1914010e010302180709090c020102070f0501150b19080705070605010609052e1110021615020703080402010f02 71
    0x7000b042d0702d4403940044410003000d8a000e0080a80b09506440a50b2400c030500000958155580c0900705281d503010600300d11022540d4040c46907520340b000c45a000844900072000508a6070008440c442b006850015011880000c86a10b4140f200c0748446c65544419405c5000c49104500c0031b030302ca4880d0714447c405008120300d14060a940200c14100d503046005110080b9001007403e41e09105440401604a074807402e00303000d607000f2100115544090724001c85c068014a00054900c40101c003004042000540c01945842d01c1c2c0408920000c0c1d540030781c0c0c409070080c2001c5880501520f010808000e205100b45a403000e0b441c00c12504008a07604c2d080c0442e0b0b400d030401c40100e1500d850510030f92130203072084d448181d0f0070325072199405060740c40d400c4949140300701c12090000b0718100a102c10000e020790781451a450f442103480700180000480241014581a82c0700c0300b4503e11110100c03018003c8030900e0707400d80c4cc0c20895813282c1d40112108070030842d40b101180181f080d500042d0f4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 415136663 1250 415135413 415135421
    0x8011503090f0819080705090f3003032a030613090b161b051e0a080a02010906060e0402211603061a0a050d08130e04030c03021b060922 60
    0x4d40f400c0824403900702c0c980f0040c003a0b14003c0c000205014081c81320100d540d4400c05000b2107070f40140d520078687d0507241000d40400803454401003107640c0343e59080340202c00000246204982100e00f400c1c0d500d01d40c200a00000c02020002021a8400c00001e030950816022941034100c1070300001482142d940c1355010313141806c0e280350440380300304c0f149180660f41c0000e101803415000c2c111000800c0c0a9900d0703c0e640e001c000c03040d5450002c3e06400e0340b15030105003e09562a41c00c001c2450f55040e000c00028024440960101c030100e10700240455003c401c403400c0c030f106943c0682211920641e48850200341d02c100015040284207903055103041c01001520040118416040800c1030304600d8503084205400c601e2207405100f41500c10403031580c5034601c445446400030802c541d40d12a0005400c1d0400c2140c11244070304500300144020154000e04250b0028000e6098134084502d640240a1a298002d40658081c02c288590703c070a282058100b51a418040003c3e120f4545000c2454151 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 415137913 1250 415136663 415136677
    0x304030819020d0b0a170a060f1401300803010b03131401150509041101180504051e07020f0d120609050c07020306100303080f041a0406020d0c08011503090f08 70
    0x45403211350040c0e2034100314101a003d449180340c90561800c030300c00c06590301c140201002d400a030300d17081504849a0726a2040c000d041d0040455000c039038485400700b00b004465a98a00004141c6030310455078100c01c004144140d41c00032545103981d2038a07480001c1500702500e140e601d8010300c070306040007812116840c060f00722194004035214085c40582d0003e00c4c0164002c42c011440102044000f980715134900380b5498090038604000c0d20041700404e60782d609608210b811500d00300a10542182881d0408164517541d604508241d030b5400040b80c0314106803102c0d0141e94409000c0c02c00d0306000f4040d03100c1203003400c100004c82c20340d14008081590310641d02042d150000148590644c2001d22586510074140c05c8044009440c59400034030054000b061882145014408a0300708407900c10030403406128803420014500f02420540000d500201c0b00110b0f01c0e250000103504035001d4901d15040f10342c1022480c400548805054000d80403005003101e541026444800000340b4101c090061 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 415139163 1250 415137913 415137937
    0x603100c1e030509010b010309081e0408010c05090f06090f090a0e030d06050a0605070c060503040809130b040513030903060903050c10140a06030f0f08090301090803090d080705030403081902 84
    0x2a414a41c0c3e20900316119461047e04040c00c001c254004030704010100c600c4420000500c0320701c180d940700545101d00507a0000d148550a00b8000d080050f8400302400d500a0103c41c00e540c525510010007401b441000d44054101440030f10302e064602d4064222680240505c83c01b0a1842407c08a18207542c0640340e050f10ba1961424140403034200045081c7c060f180c6030800f5440d01c411502c9408034040603100b8581000b034004006000c01100e00140d0f5410754016000d001c00f00c01c01250785018090b180001070241d0b103444000340305e441441399000301c0d507901502c541c01c1c513a0460300c40901801d00c5000586c20301004208840d08c00000700030f181c900300c032084000140003400074090081004040c003120405400c0420610202e10f001391445055940305a90f0349480d070a5240242c118040c0c21030040d419482d09000005104c1c503000294402d8414906031003049411080a03110344d4029684400000e00a0001a0000c0d0045540c1c07a0000310f159014a14a1903514810040c1c8e4003007122401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 415140413 1250 415139163 415139171
    0x9150a0909050c0a180e120f1b03160b040203071e1503060614130e01061101050903121305010b0d12030515060a0507060609050a06080f060603100c1e03 67
    0x81848000c1c40f00c04070f5000c0c116000380ca00c40c60320f110fa400710151012083d11540d5221082d040100041000b640b0100c0402420391710703105103050381e00307050304442800c000c58a0701c4080240901c0d00442190481001c2019640000803140c442c81c001500062049800d48503528020910400d09020f04c100e540309480780c40020390038481e19413603800c00d03003152034285824240d09000e06500710305500c4140c0000a00306440d007035000100d086440c00c82c1d002c003003940540710000c160075074082ca00e5200340106900038015070300c6900310700390f0b28881d9044043e03043e140c48021800c0c00c40f020416102403409900081440700c0600300055000302c85210842e103910b180042c00180711b8048c0038250f4000d07488204d0003c00c052000c0881e1252040d81c1074041040f100003200c404101569000038068520004100440c0c6400301c4801c00030415400344001600c1030b12139040e210349002030f815100d000050003515a00400c00781c4803018011440840052081511080d0040151090b00e084800310b030740c2e0003003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 415141663 1250 415140413 415140431
    0x1506090605072a0513020a090e060415060f02071208030a0b0a080304080c010801091a040f0f0203090f0c15070609020d0203010c0801090507050702060301031e080a0305070311030f0609150a09 84
    0x101701c610881c11000d040340d00601c030a010403500b01404030b085407030029804106a84400010f40240140016224014020100851039641c030820261460381150211590301c2d4407680c800941c400c1c0442c009264400400024411100503048942c51031400b43c2440c1002c1d460700302841c1960440d82090700f556000c1c0c0e0140f0960369001e01180d004005006041020720b01c1e40aa00001d0081c09034241d00454840120341d11400c00d50344410540340c0d040400719100e0501002083d143d8201354065030f03c501c1100481040780c0340001c07902d003680701501c400381c1c0350211942d030300b001810303156006aa220b00508400809a01c0031300403114000c10694450400e9810800048200c1b400a000c200400106100810041e105c41c000c0f681500d030800402d0703800202001c0c03400c2c03805100c40b07802411168041500c0301c003242c150308920301900617600c082c4500009207500d0005404121500000040450b001c500c4a007041c00b14a0380041080202014901e441800704004000c25072010114507030f03a101c0e407 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 415142913 1250 415141663 415141669
    0x303090c0901090212150a1e05030d17150301110d020304060501090b010507030e120d050705010e0c150d0f110c06130210141903020306041506090605072a05 69
    0x94090040c100007142403840e4075031201c5c00c50708001c0a203502c03465200c000f48502e176600100c1c800140002509000200035001842c0d2400d410352050030f00900c030f100c801451060007800d80c0481114008065030a5039104410f0a45100340e404d00250155a62001204d2402d0b881000300030310407401c2000745c2e69050a2810342c00710340050b0710081d4101c0c90121f152086a13402021101aa174143c40d01d01e40b0440100c000504051012000e04c0301d42c0714001051400382d0700440a800814041e10013040460f10440c0a00e8071407100302d4426901c095080261340d5400703004009002c200c0c54100b00083c140c0240760151007140e50b940c00c48060360401140f0500554030812032594800d16141049c074200d04141d000c1404090b402e20f0750030030b00000c04c51121190130b8071400d07070b4031070f008541c812102d01e01085000340080d481079902c58055801c1550b040200204078860b041151403a59400703031981c4c900071048942d6080480100c4501d55500000219a01030785e00030f40046c1020403150403850310340010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 415144163 1250 415142913 415142929
    0xa082505030607052808180f1b1f0206160c03020309090a18140c0301021215032103070318050a23010e0601081e0303010303080a1107060902010801230d050f0303090c 73
    0x140e100c042c0c0c041b01c0e1403148208c010a01e94007802a141d40c03201051150000158031040d003911011448403040000c00380b4070342c00100c0e940140e621105480c0005060039044540103140030000c3c02592040000030203a041107440c8542c0503641e001c2c0020823000070200840d001c03001c0101070b2030007004010700b0404503e044c0200c44803240224000c503e8220680c42c000e00c44140200080b103c2e80c9002e0401d15683c8007406050b0b01c00c208580001c1d560503100c44a02030940059884d9400285880e55103041880c0b0079041802080e0440b000704040c0c001661420030740c54030b02c11f1000105214980303050016400340140d0404070851805032a9942c1046209440c1c070f101c0b1015880310203590a040110300780e0100c1202d05507501440c10100c0782c1c1d10001030a000d050184005444940005031200c103000159001d6020717681b00b66076003480d030303640c551034a256807080085002c0d80d11103106d103022807071420402c000300303891161050382c6400e03141010302d034110382084030003642c660400001c0001900e05114 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 415145413 1250 415144163 415144201
    0x31d060406060819110117070302250b1503010b120a1101020a0f1e0c030609031d010e01260c04140d0b060603040f020a082505030607052808 62
    0x401003a044d881100e003418542480d0384082d1500a0020415409902c100307603103030702030b0a2051001e0b4141440302d070003002940701c2040014010a2040342040301014240203a00c40303900844445d8454481006803003a1000c1d98404951540d83c4051052460325620440d8100c14807a40c0a0702c0341c00c1041c00c203c0c00c2114000300885c1150081560b0000050000c40e411840e190040c07240d036505040d07081c070065402e026200c040c0c01650000030010030020a0780298a003544256520242808103036034948548201400d030328045411206c0442c05075204010445080c400300c6990f126a9000186080d501103040d03c2d01c0f00035120016060014041c0280300000c0b408082e115030890902c2e9855580c40030a003d46403d1050000201240500020822110b115a0018200c10013a6510745000380d98003040b1380403501c0041460341c00ba14003a0384610280480350050007074949a036801808403019070014004003101c40240d14080c80d04454024500f21448103600e817640d4906000e01101c842c0701d2441 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 415146663 1250 415145413 415145429
    0xd030f1a2416060c031a1f020a02120120030403050f09040b0411030907270b1309060c110f07060e0325030303180b060603040201031d06040606 63
    0x8598010207031605403142071a4803050101c000e40e50000301485903503115095803440c20502520510062040030380c099503411450b503c041241c4070011400d80c40d0b003c0d00f9007805501c11440c605d185491358038481a80b00f01070305807040c2c5201d07a07065400a0441010400d1090041c0c4d51900000212100c55001100c0e840b603420320141140303000e5070010494410703150050320689012414039001d803119000700d130512500500a200701c5c5524244860240c10480d0701504a10404e0400900014074240ca290510404c081c1041109610420503001d0040c10908680052102e00c1d8000380d03411511468124621940010509800d00c15006007110b5080540e80d140740c01c645144041c0e01c800180100440e08281004c10fa104a420000703400c20188001d4a0380035600c540070711a01e900c94190940549210351010045070a000079090003221003c60010f0580c84000c02141e26440c1c144040d6600c940305241c00702c0c0e0070b01440c25074500c1c0c00306021f601e042e55000c24188002c0164900680010303003201 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 415147913 1250 415146663 415146701
    0x303040b01090513081c0b09070804060b0d0302030d110403021c110f240405040212090d020102094b090c1306180b0c0d0906030902010e040f0b030d030f 67
    0x144c441201c54456a84ca03ea00c24003000442c0c0f045046c0340c0c1181813a41030003414078416240414001d0f00e0494101e030210b41807884c2238080f6105213469140e1400d0590140d0040d41045a85c40508001f084c0d40392000103040402d100001c01030f80e54a10480f581d48410050b410344460f64601062100e003840070091080a207480701c07411b95103138903280b031003101140841303002c101d014038401d02c8241c419131300010b822900000e034101c100d141600c05070380600310b0760080303a16901c003104c0120b00b00e0240d034030b20960216070542041c61143d0084101d1084020070b00c8241207813056242002025107541034211800388010313414503001d2500c42502c69114043c44960743c90007604d40c3c03502c4071100a500540d0300b40030509018a5455007503002c044082c0000c001840c0d41d400420320303039650320b80d801d01c88400021420003020458500c2401410b510503810703160446803160307107410480a88190103021080c90360b55196000c5554040040300308014540d1000680340341c0d4140d48405a48007442e40247d41050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 415149163 1250 415147913 415147951
    0x4081b1c0602090a0302040e0a030206130507273308060a0917070b010e071404090f0f060b1b01060b071212060f0f150f140c0303040b010905 62
    0xd086500d500d5446040180e44003040800030781850300700c0c0c20207034110346400080c4084a030000b442500c0070740070f5001c40e0000d0350750000c603841c049416000207115400c0042d080101642584c1184290041100d0b002103106182c1108021550340004001001c50000075682d010355081444582d00d06103801802806800d08114541d0b0380c001400306264266a210464240441e00d1000b50598031141c812580d1200c00f800e1252a0303110130f02072110700b82c44c0d00000c244c00364080d0b401a00c5d85410b0044503070030305260186810003030803241401c0d01201d03100d241c1c138100d86080344103080181014070381003521038160035600b24000704107144013611f5078074200d4144018a000720981c1c0239254081580141403ca14804070391040d11001142d42590800801194511110101307030280e41144104420081d52000b40b041d014056501410101c0e40c001901840300c2d220b0507a0660600d00304010f18941000d5020040c6141c3c0102d800343d940425110040c403a8403028019103400500a584c0b00443e40a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 415150413 1250 415149163 415149199
    0x21905092b031b23101d011103040507030f020a050909010c0e011404030b070302160507030203060705030f070c02061c060f0b2a011e0c0206060a0f09110f04081b 71
    0x4c501058400084d0b655101010f400c0800c03401c44032100d010000c0c05089916081c080724480308940300001542018440d090007502d640a59208070340050040100380e140d51125407180b8180b890903608080000000b2840b41c0f600381c01d0a010b5100907000040d280c0000c0720003400302141708052410043c8180384a1800346d01d031401e403400c0c1d80c0c0010100480780c0350b041e029002032045018481c8420301148019003030101c085210740480380250260b4120b96245c540440f5244812911040465420310100761003d11885010700c00906c003800440c5418805a9054024158100440485516031100b4490307403030084000030041645042403810030800c030140c10003070f07450403042020b003110070409507001c8203094004401e429004c00c440100740c0c144150000180030303280214809072183c00d000c61161704110308910f003254500c0c46900c2c0a58240000c2c41c0140000682c07040c01080203105035103600003050000c0c0000d0141c00e00030103241070032030071404803d0780f0a80028410b4901c80304811750740c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 415151663 1250 415150413 415150433
    0x90c0c02031b0102031c09020307060206072304030b06010c06020c010e1014010b030a111224030c0d030315060f0206160221070f06061404021905092b031b 68
    0x102d002007090180381c6c0505424001401d0040000c0d60501c100c41000414580200e0001d00401701965907103034120f407004d902c0c10440c500c6034140300e9006003080100080303819440070a401803030514003c0b00010058071041c1c26a00110300481d4165910a0920148402007143c14001d0304202418481d4000d600d04101c4408014414480c420710000700054000445a0000c074007407020524442e280c1030a90302d066000040cc4659034a003a0020721122a01c043c0d401038000aa00014020201c43e01c0341c8050000c0300d038180200314141511103001c090790f021800c400030003414907a070344c00c2040c0c100090000d01e01140580000785004001c0074a0003419404544070501380ca48a200141e40c1104c099560344620a41c4806401e000380410903008120603504200122180c2851a202801c0a903080100b20302c5010340041107003500c90a0100d1142c041d07000f9000b085c00050501d002c42451901580083d81c43c0080150380c40c140450300c41c200342d0040118540d101c5085c215529018150b030341d600e204 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 415152913 1250 415151663 415151677
    0xd06060f1706010e07020a0b07050a08011212050a0e0a090e25121a161e0e09040501060e0f0f10032307080102040b090901060201050c041707090c0c02031b010203 71
    0x1340086600258155000304200031540e07a01480c44c40c0b05160850009055401038101c0f5030004070020700000d032441c29006484115600007003111801c080900d810f0300c031a48002a41c9081c80184070b0080344070340e1144025801058421400b040360400080030500b0408504190717407050008002801a40084c0344d00072003a14090b20088111407803504040305801c140e0820200d1500d0241c0030040c8440c4201c1111843d072003141c03200000b140300c8214180340000c03244041d20005101c03a640090707914004c22001c0d08940600000030b41c440e03e170b86880e80e654030200d5620180d06002c1d0300740426070010f0150706602005000011100c1411581c80714002008185212244c441040510407171a0303092000d0001001400021991103a90300c50300142c981000e000c60744104100c81c0002445401070080c644210100d6100518141c10040000b6000203040c0d00c83c00644250741e80810304042501c600c1c2c0389a03413141c42d502141e8000340b040503e05017000c0c3e000000001c01c840100601d0f41c00105079280 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 415154163 1250 415152913 415152929
    0xb09040b010b07110901060c0c090219180b0703021f020711120c09100512030f0a0c050703020a090f0e010b01080c07022b0302061501020a1103010b0d06060f170601 72
    0x20f100000d060140341000c84a9000d07a002e81031000026015400400c440b410302d02c580300315a185656006c0000403402604507200e41c4020303040a001030b0b83e100d10022419241050903580e031043e00c481501c0d900360441c0134201c002d64001c1d0f41c0c0e550190780401c0c11281c4004071000a602e0700e2115500c071452503007203031802c030300403c40040801914217043c0080080600040d050081502c0c04282000210500344120f500810f40a0040c0d00c41100c00300445000840c840110703450b00300820001c45014183c64001d88960060031808401a81d40600748001040f00c2e070390214001002841c0300040361211030414801d6890481c00a074280d030420321182c0e00c008186141500c80121f400400c00b60707080d07000c1402c4030244e0000000303800440b00814562040c000e9003140d030103560380801080c10303000309041580940e100c0e500d0000083d180c00c1042c92071000190010440c0340040300854910280c0e014102c501c151201c4052101c1460700000714010304101b9071a01c084407c0c00708240d00d865043c028000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 415155413 1250 415154163 415154167
    0x5220b040303030203061206040809100912030f0c0b0f01090c030b010801030209090f120a02011518020304080f1306020d02150105040c02030405031c1d1305060118030602030a0b09040b010b 83
    0x20b517106405c66903555031f1082507894030703e41450312210a902c4004078074414181049405100c3c0d110303c0461094440640041c0c46004150300c1c15205910754840c0c2c03100b0000944c5075070f0001049514114040d91a8584100c600e50510b4010000d07900e20b08444810145800d1607111240c1c0c1c00801541102d4050728840784c4ad895034000c071410400f440e0614440c0d403003400030300c46450400350000c00d0020760035030080015105e0606c100f2104642c17403080d500041484011100422103550007035401611480c0003900c4c060320000d202034580c200c028480c400705144081002070035014810004c1d01121071000e2f041c6040f071440420640034042c024980070781c1e60703405080300560080007202c01901e402412180585141700420603000854a0070700c001030000c0c032401249902c120004980c42d80b004107628101c46101c00913000038540103001c01c1c100200e101c520981c9010740d01ca1000034501901015a0320b00d00b811114054402215010380038070310500401c8003007000c4c0c01c80941901c05000c80e081e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 415156663 1250 415155413 415155421
    0x30203220c1505030a06050303090904030e01020c0a0e0603010e0d1d0d02150c010b090103030807260709092f130e01170d0e10030c120c05220b040303030203 69
    0x882898481e4000700c1c4950484032031202c80030303000400b462161601040c148841910350707040c1a01da00400c9900e07500001088080b0300040d01504100c4003000c41071045071100d050b420001203240c1d000758045450f082007030701440072508082c003404290400708402000f00e059400402014089058103210440c054070f11020302c0c603501c1a11460541c1e0300205080341c003091490b1115030700d0740302031207030141c47d860121402c9140c241098a241200d0301512000003d83d81d07100165000c00c02d50300302262508540789008400c20090315110702884441e40c0c1c900c0c03c0c82c03c141d01d020880300c07980300c1040d840d00003000319140d00c6000000102c0602395081815103803242c144d070780d0901088507002101526038100021034692031030360711900070032582c4084a4110182100983e0200c0b0341590300ca810518194100740040c0c069084041c0d00340103413502c0f64110101001010848641c000e000d00000c03400585200504d0070030140c0303881c4c1140200100d001a140800c50141482180310088c207142d0080005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 415157913 1250 415156663 415156673
    0x20c010806150d110406120c05030612010e0106180b010c05060a0e1f0906050f0f010506030712020c0304030302070f120323192003030109090f0c230103020322 70
    0x80c1c1c602c0000594284a0700e0131010303c0791259082405180005800c6c811000100c407a5401031250045450310b07081d10350313111708080c4040c40300b590528000c59900c40c3d0210300070b81300911405004104c607070800d02e640240503800b074050300e5544c3e810341d040203c1d110324030022500109065401205e401400900d605140d1903540c00e065031701c1000201d0359a200d1326514004180c0d01314a0926100300420420341d42c4400c00210740b100291070442081000e6001840176080140055800601c242000c403a00140708400005076030100c038540115070000315040042580400140c0302500a103084c0581071420b000e82c10300a6246140c0c00790400c40b446401c44070040a030314030b040c9240003c105c215500c000c10001203040c840080008400501e40c0038250003a07881c94921440c40f8803250b03001c0c40c0f450b4600714001000d80110300050780c0c10000c14000a000543d060440710080407451b00100101d00d90b544011880303880c800c0040e06042c01001003001025a0350704125402c07011242d0041250103034100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 415159163 1250 415157913 415157917
    0x15060806090a18080a090905150f01030f0606090e0c040513090303060f030506070908030301060e010e0a0506070b1030030c0204060b040515360306010f030210020c01080615 76
    0x40103207042c50f884003a018001500014142c503081d507110000000da50b042a94102c6104a84040820000c82d002c54014607001e02a0003c90505240100d030500c002a0000201d0300070380e102e0800703c2c0c5030345010088601000d1000382c0c0000d14101880c01c0c03078540800f241d00d8007024588a0159036230740303008408140c000d0380300300302600210136134a01054880c584150303106070585403400818043c80000448420000441b0f0503655640e413040182c0b0481001903541e461500e900660040c0e10100200342603d900c0701415005004079a00c210350f00b0146c2e143d801c1d0790f04540000c2104a8102065866401007008000d4011500e5451000c940a141422140050040341c02540681000000511039400f6800742c002d03148100d40c51402c840003084a0040c520548910001030700000e030b2403d59003159030690304d0006400740c1e070711125602d000380000e042030000d800285c0390b40d0b407190f0103100f542807052407007000030136030700043c0300300501c20001170020203000700f41510400d21050650740100701801 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 415160413 1250 415159163 415159181
    0x50703060f020a0e030a030509060a02010b090a060e010e04030c15140c03100b0910030b0a080a05060411010804050c040c020312040b01140102071503050a0204050607030c030315060806090a 83
    0x104000c880381e144000c0001e90710035030303a100001e000203905042c58035000c210f006c1e1240e41612103d1400c42c500c814010a90000d0b100481955a9a070201206031120300f51241700360b04482d40001d2850915152080d003910682050100310b024408001c00660800b24480200343c1100343c1464103120403034101e002d0300e02d18020203101d4041400380034075000448061801948092654030400d602d074a0a00035078040c2100030f59015400b0001071030018002d0f441986e200341c0c0513292181551b00e070480c2e689840151102141d460303000c0c04c200401e1140513103a0b00306005013482e00e610b11707081c10307161650354101c91460710b1310440c4c3d02c0d025948414020811950300c40c1f00da2500f0740c846e1a26003082c0144903424130a081140722000c0f481060756202080030320070303036070b1481801000380b1740444200c004100040200101c01e508001c04103172607840d40301620b038552083e940c014460007e89801006d4415040a00703008202803102800a0f40d0000d20f901e90000741070781c0c4509181e0303c03072510f00064804c407a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 415161663 1250 415160413 415160423
    0x1208090d0b0103020f01050711120a02031213090615030b01030f0f1506030213030b090c0409110a08010e0a020f42090907080405010e0607030603020f031603030c050703 74
    0xc0303208001c211549909074101c1c1e008458401e40715291200540b09442103010080115031185000004ca01d412401458550113400440b0195484ca80c00320b03150404d500ca039841c80c11008541101e49140301043c0c0f20103403000a000b444030902d0308203010b1100140d02800780a05407035001e180d00c103910a502000403031034542e02c28083c0642404524005010108014a01e003521040201c3d120303019000b214181d4250628400c0c40318510b803100343c103c1002034400341e200c1c0922091182c241d40c07580a0703101480e0082000781c158a8082d010400c4100f101c0e030000001d0b9060000e681c145001c0858a040c8141d0155080a868100c64002030300d00410401c0c180028034080c5420307440f04035551140340060507d980b010322070340304028441c070303540c060340c0d44a90f444200c0708000b038502486034240f150080d20440000c42c510541c0e4038185c5c01e2000848410000950354041081580340c42c0d440700d80d4441c1c05401408801c0a81558052603802600018040c405800c4400080010400c40d00c030040d6000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 415162913 1250 415161663 415161679
    0xb0f0a03031110050705070b0a0c092112050c060618010b18060a0302040e011a0a1b14010b0a0905040803060d021504031505150108040b070c0b010b04080706050f04120809 75
    0x240345d0150054000140c16070b80c1402c3d07400000d45d4400e040c4034400c00d45066460f464901440d0a0002d511501503070182100356aa50801c80c0c0040e07a14040b244030804039458090303d41c202001c1681c030f041e0000308980d1054030102c0f24070b200041c170f4030051810f4491820404d80d44250400401605008100c041a004480003580610320b1b40e0542c0600280c90aa0030708a2803666660054080030344040d4038000401000c02c600450140074180c1c0500045a606615100031890744882c003075070b050683d0f500c400c0e9444042550551911201000207821414410090750405499040050100604450151a0300c030a1582555a0a6590507140414000c8103503600e40368035100d101480e0341000c100c80b1324100000300750304501142451541840680d101407a40d56161030b42554140c01409150a02c11540811030110325036404840c0641000e03140b02e551949018005445c00400380e00800400009000e00401c0030290011101207981c00c40d240424540e41c0d040c0b02d5900d2041c00a02e60340000e003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 415164163 1250 415162913 415162921
    0x180f05090c15210f07020706021c0804030c02041a0906010f1707210b0f1008040b0a021b03120603061e0907150e010306050316060c140118060b0f0a0303111005 70
    0x1304e41031081c1c80e02c1d425502e035165100016a903a022052040c5c8190181c1031a05203170b9482491403c0d0300901138030703240e00c0340190b54011804441795030003040400521104c0d80c00c06801c04000c81c42e088170742880d1021440c0403449000f4881d0780e15110038000f03070403114046031455100310203540c890450004036500c0300741c07040706250081a850680c5401820042070030ba1040c580300200c0300301850326482c0c0740f2099403960388080302124014030900d00c2c80d500303100d652140c030511920510a030126800650f0b8480501030300040012004144600c6a8000c104001218012240c3e03900c800045500031405a00d4590320380382481c820342c103c001a51001c0300e0321040541c1c4609107a00640c02038901b005085d46480c01c0c1a110b140c1c0010424a03141c00140410450b445038010740a141d01070480c5e01056810380c020f05080d15503c0c00382c2020303c0540c140900c107020721841042016041100c600c00c1a80c96000031883c0301c2c02c5444040d040c0000110031154085007849894811901c2850400103481c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 415165413 1250 415164163 415164181
    0x260a0603050d11070b0301030305040e09070f080708060a110a08090f060406140a09050c0f030109080f030117010203060913051908031b04050604150504180f05090c1521 74
    0xf901c16141140304201d030000d006484182101e0680f50513070350312880c00d0b042004141030160080c03c02c1c0c24071b100f00100014420b219020795405403807100b0141c4000303460b00b41d6817890304502803c060034007880c0c000003000c841c0540c0201c401484070b600b041425a51074583c80f90500c280e8a40104035800b500c0100005c100d5a50310001160700c58107801400f9494142c4460201c9158060003812035004e603803c01918a0000451489400004d0010035203103001c0d5540d200a420584c030039070707407100084010300080890141015000207220300860451800340e0002e100d240001d424598800f00e4802da680032300009102c03c942032140106441c200c44098900f1110f1a0320444241d0500314006800c400818109802c03241192402401c1d103040c281803450350000c07003414640004c103100e0208030024800c085000c9020181c040e1040000d030b42c44642c06a0000e40e50010013110454000c080326030840c0c0c0e6249003003841c0e10800b07035115480700d041c2e0610302c155aa90001c0000c0e030460b64810000c0140c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 415166663 1250 415165413 415165427
    0x90a06060f05130213030b130606030809010305070f020d0e01110a0f020f0f010e1203120a020c070b0705030d09060b04060b1902010e06010b0c16080f010b01260a0603050d 75
    0x51060320f81102da5080c000b0514102c2c06140f40c01d40400c2086801040414240086c80e5080390313003140030568880f015039031201144c6240d40115034854000c80c29000303e41c1c1602c240b80e800b40301410f100100c1c0b4141e190003502c4020b55418401407020304001c0d15000d92007039645100c00c0198204507504d4105a0612801c81500071508901c1100c01426200c603034100483d40c04807074101030719076410f1807507494108040c0154980c182e214611080c01910411442d130910140150a0604010395580441c9081802d20045401c0440601410071100000400000890304c0b41050f41d0400103c1c2c0741b0618240b40504141c0c40e900d80e0181c00d111001c02c01d590300d2002801054149054076501c503600c02d100f0f9080c0c450785900100c41d600084010040044150000c200956446055640c169000e009682030b035420b5802012490307000528555188900344140710300303030000b400c0c40b0301100c11a0140300f089038000461402e4852001001c90500200b42e04000007030765018003511808521203030014650 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 415167913 1250 415166663 415166669
    0x19020102121f03060e120a11060606070b060f03010608010203010618080705010207030818090f04030f080f070c17070f0b1006080402061b15011a040b04030605090a06060f 75
    0x70a041d4002c40e0651200c007014645041c5032400780c80c000e520719110113004088a695040040c081c0503440d050a02e241c5000304124400d036100d130440d0311b1403c1d40032880d1000082855020f000100801404500490009036101d041102c2c009011941c1034040790141c0180c3c0c0c4014490f40c00400040340301508a41c8210740c4440182d0010800d079641d04600e969030034984600c1e405600642005c0c0f011803540801052916020380c0460040106400030a206903000c6170303c0312080e0440c400340801c0580c401154004510b1a2805080900703009410103000540a0514024004000701540030048038076a4082c5448542e10825124112400c3c19610500070040444101c03140c080041c0716940300d0442c6006440c02e66640c2d01c40d55940340e0030b00042d5071000622a00040102c0c07440702448604001c0c041c04281050311a00f440d5142a40704223803048803107425420024140018002032644d0003d49007101d40007200031540380c6501006074107260200e40d0140c0782d0b030308268020840300c807150120f00031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 415169163 1250 415167913 415167937
    0xa0c080c13180206090a0806012913450e210d060302031c121a0d080408030a0324050603040f060b0409050f01060503060112140319020102 61
    0x81048000c1065040740c51901851201800c2c4810000250500c80080e00c1440c1024040300b1010340c4030542d20785030aa00743c0c4284420010114480d501c20707500345102d407089902280160800e503100581a81403200f07801010740c1094040d00c01080442d8001650100b4004681501191500c9489c1074003d0743c480f403040e041207414024513098400001032454010300783c01c04002c881c10a0740140300300342e510190030007034119200c4001201694003031010a1500b2403d410300b00fa503170416036000c2c000c0340e0900403a454013441e145e1210110380c0c084a0b81984481c04a80c00e80c40342c6450324014809005680202403580300c00f1a05e00300d003039016800103000b81921140355250303a50b441015540501c06018141d048207051021500003541c46044c0055907228060201d5107030741400124045504140b41034072941e00c040f070b00003408071003842102c000d88400d1b0090f02c001e60600256011344150680000e15a15040030112503180003441550917607070402c001940d880d1600720340203020350001d0107107001c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 415170413 1250 415169163 415169179
    0xe01081c0302070203210307030f020307020c0402070602041a040e09010c0e0609040e1b0a151b05010608060a0e011503030207060311040e0f0907060c0818030a0c080c 73
    0x425150025154454001a2060000610184004a0194001c514200e0b0948100302c504510503500c60700c440c2d828403404030079940b40d240542d801401d94803a013100c44110303441041440900d690200d051a0189029100543d461030f041c03404200910480d0701000c0000440d00d2184400d2500e14000c100710f0354800c2c407150340d94031140b0341103088800c1030b0248000310f627080c1421402030030814043e00c0c3c4490020000540312014110060820608000001c00e0081e5181c3e0515645411840b00000e040e01d151004065100f1000103803450b2081c3c0c034030180b0044003c65030001c100007500000040d0801c44143d82081c1045510400601003031040d040041d401c0c07040c840583c20003200b204044035050340c0149180c518003c0705400030446d005114039803440801011844620081e1100d00031841e43c602208a854001c0e011030818600d81c200b80300700080241c401010030769034000d5407091014450018203a040c01c5000030310300b10b42c0c10310042c000209240c2c000741007140410441c000001c15200e1030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 415171663 1250 415170413 415170419
    0x9050d0306050f010c060207170c01061e06050702030f030c0105150405060a0306050709080105130c050a0311040b01050c060906010503060105030a0209040605060303090a031b0504051512160f0e01 86
    0x160a545881c01501c1c2c2010070300403c5402d540c461208104141e006013801403921381d25413591320031741075001c0d101c15040d007001800e41801c810900c40c0301e00520b540e504108018180144546c090f80c590700c1000108100815100150f60f400c1c8440c4040400c0344c01183d58402c0c0390b01c02c0038041c007800c50f5a800624a86a50480703a030a090050500c00c0d0710040c845004036003540d851900410000d4484030801c0402400891026000d01c17425005000c903401162918416117414001c1092070382115000c0d0f05041d030104001043d10141c680384000440c0c01240c0c8040c81001200ca030302035008440340600c01c443c2032101d0b01c0e00101e101c82c181d840603030036246141c0e01c40c000e05550780f20210000b500b02200600140120306694800d9800c40c1d8010183c0b450520300100180c00d95806810503201245513145115015030180c5a080080800fa50203100c1464082342c020740c0000b403140b01d80e00901440035203101c41c5005001a50909902400803c016501e802140440b83e03202e00500702a810410004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 415172913 1250 415171663 415171667
    0x21142a0c010f150e0708070228060f0c0c080703030209060417010f0e100906060b040b04140a150e040917070605010503010203151207030203120c012a14091309050d 72
    0x740903508a2542c8840c0358031080d00807580e11b00c008003c60218007451240040201c10400c00e074100e41c210041d502072a5215003024000c455480c044440302600e002c181907081500700110003002c4d83c000020540302c00c032606080e8040e10910f400036a100c4000200440e100c80e18400010350000c40c00000c000b03c07019480488101d41c420348100459600c081c8900f03c1503c01600842241d902c51a00400c2c0340e9640d01d410340d105c5e081600a805000c4001c07500780003901600c99601c40300c6108a031340c1031600d0701d81b070300c81ca603001e080c1c030b2044c02044248124400140c40d40d400c8503402551099a1542e9112146400794154000d0042154980d041c08000180e03450140250b03802002e00030010b1101c1e0190b20708110b80200800c0403002c803405031540010250354140700380c4407402c50800b8059070b140c80d0400c0c1f0900310390f10b601030340d0304c600810700b50800030701c1024511030100d12003800c10078260490351031208400c3c000c1103403260b44400880b4940384412226040010036522420449449046507902 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 415174163 1250 415172913 415172951
    0xb04031413181a060913020705062a030402062206030209040c02010908030609090712062a080109020c03270f010813170708030721142a0c010f 63
    0xa40c03609482c0f0380d2150721481c03901c0300080c0505000205146a1140000781c0070081e030304030074001e540700c0d00b01004128a50280c10101c0d03d100581e440c10005264552088031b005020182003e8024807010a4950041590059810081008140301580690303038100040295000480050045003001c05000e8918014010417235140c1d0703c070040e0b9045030b40e40c4050142800c0006c01310030943c801c0600020b488c500078001c43c130105010702c1c1c0206099902031010590f4403038002032503140c04803580902460590001c5198155144401c2c00340e0b440c006401041e1850141903002c80b000700904440d014020f07040201c0c162100016282d00c1040c0881d2001500d01c02d90481d055080100701089000c0082e44202d50303404908050241e080c20000152581444da410446c0c0e100085420344102a4a0349030001c1400c2a9a0b402c103818041060400000c07603d21030b010340400e41400140344c031040705010108150001c5a03002103801d4503120201c911700d010302500b01c0100c03021450044911049400d07255 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 415175413 1250 415174163 415174181
    0xd09320c01080a0c031107060905070605090607020907032c01050a0606051c090f0f0b060609061e040302100504060809032b0b0303030a0b01020c09070c0b0403141318 73
    0x41d104210360f1800c01c00c030060100421514101645c07002e080365645116405844214003600000a403541c49141052611045030401014040b007032200190a80e9008102c4800d55419034500e4015201c006050300501140705102c4107224001e48607101040c1054100c4c1d40d1169103a000740010b031190040e04084801c075008040020703008000040b1904a02e90304954418404072000600c03140329102c2c00002d00044008864440001c900c00303081c05078201e81c0c41d0b0000c00c100e8041d4580866a800207015206540d28200d190241d90003036000b49844005460043d90043c040d1810b0420080c802003543d4072070b00507600418041c02c0441c40c0c088000040d19603100ca55041c140304441844140404018094102441c650705d03401440d030941c6061018500981c8846008100d10340c540001a0625000901040c0103041c1c000410501c991301c100d0303e030b125541100600b51107846038141210452800c19821554804c0002c9034440c43c2d10045144c400c4071942051444200603011009069540b040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 415176663 1250 415175413 415175417
    0x1e03080601050307090e0a0c110106140d051c0e01180503030f0d0902190603060b030c0a0c0302100203010305061501210509010b040e060402041103010e07050d09320c01 74
    0x20001a4441d4040c0e0000d54000c40d05003407205031281ea070000340000044c11156a641c803600c0c1c03038180f1045900030041541701c5000c500240030882c1418a800b280c6904000927038842c0e1342c40400394089c00f01c280148504c48000403165084c034030485101800d5000320205070307800035841a6030301c0c0c1c403003a00c1d2618030260740c001030203180380c81c030b840d070b0b8500b01600603444100e080c036a940314400c010b079114088024451600144545021324190001e01280d451360310046907807030208104411030b0440c10495111070b8890424402010712828120f14185c04000d85940d038510010010003400000200c01e88a40f010720802084009400300448aa02000e40b100040ca014403858041415554110940c0100032000000b40c041811000405440c813281c5200e500c5d800c000c05010540c03d290042c1950341701c035401e0040ca1075151070070024901c04001c202c0e00c01c103c8080380c4191521038641006100a40240811160040181c0503681c4d0f0016265410780040c1d0303507520480c07603020120320401260416 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 415177913 1250 415176663 415176677
    0x30313020409060e0607030606090b0403210302091806032406010f0e03010f020d0b0a0f0e1e07030c1d0f09100801060f080d021204061215060203071e03 67
    0x56400c1c04003409440c1802c8540b10744602c3c040d0000c810412a0501c03540740355030701260080c034000c03010704408619040624160750402007071000c6000b404808503a42c40c00d40e480c0307101a9001c48228000d0040b103d16942c441d0341514520195428468614040e64040b42501d000b419003c00e4a20071803a48400c07160004040790024249600901d4925a0324006089c0082c9140880d0006802c4407026501080303140c0d404200f059454003a0310981c060350000742e5505440c2810007855401444051040344212291400082d040484060040410310102c1911065901b060007024002c0c1c1801042e003400200e1828042c06030407400c4815600316580907001801e65141042449499600100790341c190982035100014a40002d11544008000403000402400e0030302500074101040d15041c002158400214445034420307120454080321154200f000b0040030b10000200908002e0009038410040700400089c29900403008108180c45040804200e079686005548048000c3e031011b0000703090 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 415179163 1250 415177913 415177951
    0x30f040f1401082509150c05070b04050108040b0903041208030f060a031e020303160303060807081f090f050a0309140909120c070f0b09090108030309120a050409020304230303 77
    0x3504c2e1202044070030310704908090303180c40c4401481702101e640f0748000303800d1215407400d005013402248090000b8065951034145410f0008000c400041c0c80178000100010110382c1c0e0490070000c5030000c00280c1d09031010742040d8100190305130000c84050301090103031070000e10030780b034403d550f001680d0380104036020342d003020366810680e1240101c003260144001c02001800400360f00880054510942e00820b400381451045130402205500003600b80c0d04c204603800c0008840b415040c652100c0c3c10000a50081609220040141c0f02802a0080c00f811100006055100c9178940c19a01c401c3d0b00008035035401401d005e04100100c0c0e04089941048101c01041c2203070100502c14901c055040ba801c5a032602566680d6240a80c04101c04000c0040c4005460401451007401004100c020f5415481c0050209072201c0742e01c6e031034048414001400c01c050a0003441624040d041e0443c086499140501c0c0004600308058110301d000054003142d0460800000202c0b842040760000e445c515900c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 415180413 1250 415179163 415179211
    0xb0a09020c0703020612160c031d06040b3f13110303040902030405010c0309020d02220c020c1201060803040618090e10050105120d11030f040f140108 66
    0xe081c01c480395016054000002d6544c100c0503101c0420200d142508a00784268104503181c48000448148501c0707100d5100404c7e0442a441c2040c1a24161200e43c0c440c0b69000074000c0c0f0441e0440380c9040000b0400c036441c1110100016503006000d807004c694910040c4800312003100c1001c500c2c02c071100c0c040000305c181c03d41b0180c0c00715003442039a048081c403810781c000a0654000d40c01054281d6404400c100505c0b409000c0d032407130006030303080c20010140c6031b4010491020018078080e024121088402800030003c0303c1043c640d09080301c00b08000d100801009441e001c0c400300720380c450600780c0c5001b8a681c50600c580f408851503c0011890903140c81130507910803861040b04103a1003c46400003498101600032200f0043e0404c0c0179000d000c0b90900380900f1200c040e000b503400303001d0342400c44040c0c4600003469012125582448400c560401c141c403450761081425032401e6503000310380058080002c0c007130541510b05d80b201070101510030800464568200b1500c1407841c0003040c24505102c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 415181663 1250 415180413 415180417
    0xc0203161b2106110913020702030a05060106170c1216123b0303070e0a050a1502061503102301030b01090e030412060203130b0901060f06030b0a0902 66
    0x85008070103100300d541e1840c400401070300402e807009441041c0c2c2070784020041c4601c14650f840646803141424040b00c50041403001c508562a036142640c00240681503541c100400c0101c558824100d803015070f140d00700200f2807501141e844084d041d80c1d50100d2035480000017603031310800710b06090018943c0c846455440114040340803209100c01c0b075800c2940d20100e800307056291120f10541100090000b00089000d2200d842e01442c894000c100409681c5000300849800040e203142000ca075000042c0000d0644265600c040da01c150034020004504840c03c0d5001a0110700790252070040e9107070840e1480f506482d5003815419000110016016401c55020f000400039148101904007020500b22074600340c05c1e002074a9a07031044004101c185500c1c060201641c04410295007054a0101f074114900c441d46802041147c0202c00100c4009442c09403401d1590410f031032010500344055031038002c01c02805810203030702000300f0208129000340101c1504040180c40710100d40c0c900121f04001f5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 415182913 1250 415181663 415181693
    0x1109011b021021020403080a08070f0c171b0f01140405071505040b1204050708010e0a080306030c130e0c090601050a0c0302120406090503070e0403090b1305090c0702040c020316 78
    0x104101500b0418443c8510191010350300c5402441d985401c294009002c46000900c50400c0202044012000315440710908a049074485400c103050a03480c04c403400d0368021984100d140c0718a122004449900006180015003000c0000700861040b04103621142d160469003d080e0358000c04041000506410603250f515603103207005410161104e070511880e41c455011483c41d44800710a00c401e002c4117110210080408200030044800b0702c045140c0c954090400c00340c01e410300800040d20b151018010030649150003880c0e0f007406017481c0410002080408640809481203801c858898103010080c64001c0c04142c4079039042c141e440f034045807400c0c0b402104a00714041c80300c60544515081c0c000e0070140c070480d200e00020754100300601d481c0141d40e80c840003044410b1403d00020a401408000941d010030300700030b45d03840c1c2c40c40c4214122100340c2e101c250800c06003420024070341c401d003000d06450b920894080c45450100302080f42c2d0780c0984013542c10045120b618000c005108440c0381c0f000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 415184163 1250 415182913 415182947
    0x515030406060512300c010c0807030c090b090604050909030d0f0603030c061802040608241506070303060e0a05090606152a030705030a09090c0e040c020c041109011b0210 75
    0x2104800c001585200d810020701c06c400d9039116601071109581200c241a401105450304010641800c6070041050046104a030b003107042c0000c401f00180c0382c12040300e014001c003a224440d94204021059a2580300c40018282103145c04110145101a40540022643c15075a21140002c050725100c0040c400200520403900d04402083d0050300c0307d000b084000e0507480301071b21030107030b4070545c062210081000001111640104202403902c1141162580141c15100c141d1185801e03c1c0c15801800c3c07c0d006200030202000c100b0214ac107540c0c210a224003062810340352076450b0401400119131040442c1c0381424010303c4003400062805444c40010660040e187d41c090501c00c00041c25070f031010340d0075200e03604009041c0e0f00190300400554000e0030640b90801205c10000c4005100812000d03055200c2c03602c800141301824070810540010800040041000381c58908100700329030f200403803032404500241c400c10742e00b0820f2200d10070480e801400910366482140c1c011243c41c46a000d000e41c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 415185413 1250 415184163 415184233
    0x19120318020a0611010b030a1a07020f07090501060f050909010504020306030a020a180b100e040f0b040f140a0908340302101d0a060509070515030406060512 69
    0x302603600c0c010840014010f40e1600f00300f2440c01c8150b01c1c00d403000b040a65020394031482403040014407203600c802c0c0d0001c41d4110584291240039049040c4400010303260281d204607a400f10b40e00c0f0b410f0380b1550490340b0a4880d660034a480c0002601c641c066201a15170061402d0300400850400782c009561181f80181a1001700315150b00207042e41c403031030f048081c4450040c2080e42010718103106940c55188212010b100d190f0040c04002c2545800c1201c0b00d01442e10758030803212803038841e0003402e800400140b080c0030a01c1110f04920050800014010304200ca031404242981140e200c0c10307254a4201050ba0728010321400e030140e4000c640310800303030f101c6c1d081d0170000800595030044501d201d120b80c0c09010074900110380501035804070b282e180042e00704c444a04400742c10002e0140b9407998451400700b03596036021050390170071010380d000f00d40199000c040d4401e102c4500c001148107500c1400100111621403080c01184d0600034046002540b2929001801100e58140c0040c0c01d500b5082c010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 415186663 1250 415185413 415185461
    0x60a091a04090503190801050a08011404030e060409090f020108070503062103130b0d201911061602070b0705031611060417100b0a1514030f0603191203 67
    0x1105204105229000041b030080052040340385c411000c070014418178000b1b0010340c92890152039140c401801c000c00b408801038508000340c85035402e407001004006c00070010b01c120790508844d51541a5401c9000540d45000211810300841c00d0328010500036220b40ca5070190300807101c4030b0014504078100179101c1400700500a000032161000609078005181d41c4603040c0c5100c03403040e9441002c40026220180b145152002500710170795184584403804110000540e100c16544041c002d0407a00c13050190030100500641000c00c81841d0180356801c42d680c180d61210030402034060b0780802041070308200048100f606e50300000c406030a000d944094a820f01c0382000403000c7d442588103103244001a0001c41c0b241c1c40a01c4103048440d4440f10600c0026000d00004074000d1403400740004c0c5441340c0b03402c510300612a401810740800405002c0b0f40c0c81c14005685c40c2c0c403000840e02988217200302840c01d2a10561505505c1303607aa807100d03140784c0d00c02114a0030340281880201030000000107205003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 415187913 1250 415186663 415186687
    0xb0906070605010902071205040605180409060e0606030c040516140c16030c060503130b1305100510061106070e01030905010c031415060d05061512060a091a04090503 73
    0xb4a00912904000503583d40041c0b03000b209100003c1281c6062001c144820403c80d0340100459050000e8400380740c000112600002d0001c4c2107118005e4003282c80c2c0140c0028214000484902407281202101c24900e081c00c208001d0f207104981644041074217400b841c00d01f50244903c00c07061340c8043c0c1103d0407d9400071000d071900d014024410050045041c1c10818400120794920143c84c4500e085451450400c07400d6214080b24117000f092411071800280b8083e00700d141100c3c1055010041e249140415810395002d000c041c0da414035a0450490000340d141e0042d5444284c3d8000540640921794031048142c500800b1050382d40c0c11b058440d04100001407081c450a4811002da4400041403c0d0b2a1132508020600400ca20300c129401031030400320790345440a60300c040d005003201160310b13070301c800101745c1655908102c0b03184800045200b00044c000c0000d81c40c81620196154050b803951004040280c40da080303100442000d1920200003181081e0300460301c01030040d41140d01d0f090391380700d070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 415189163 1250 415187913 415187921
    0x312040b0103120302030f1315020d0905150123151204171809150a030803040618020a15020a050d1812050d18050a03060606110601030506010b09060706 67
    0x4200c810508010040c010400c00d611404003001503440c0450851600150b581c03021103001c2d0080b041003079950740c0348082050081040207810a100740030764641d03203c52400300c098000c42800315518000d510040c14840d1038180150304030f45510f40603030310015018a003802144034010513076800c021301034002481440c201c070003003240c2c0c075448461724924581410610b0721501d107030096500c01181000010511100c210302038108007800c44035000d49440c0c66004070031089510310115081014041c2c00414440c3e00000345201e540a6101880780030082200240d84048a00c0020b50210a10300d061141554850050142000a004030344401c0d40e69142c8a203004540810313040040c2c1c1180c10b1164a001c403003281d600a210104040c1c0782e1884a135142c64413000080300c00000c0001d148040c042d002d06c2640b4202c02024060601c1ca0711686908102001d40114016500440e0100030303891250140010a18100c9400c5006000c4c0ca0342445265803085e8000820603070702c01424800c1d400400c5840c49 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 415190413 1250 415189163 415189171
    0x30215210717090601090e0c0d03090305100903050f090f030a05010507030605012c010c12091d0402030a1202012406080c04181503120c1104020a0518030312 69
    0x510201919110100602d00c0350316152180500000e0382c1480612440024403605407180108080307508002042050710380500c803140c00d5407100e070a0301f011701499084218a000c1e20b0083c81a2024900b5038600398098404034030300240003800410070090000100784c041c05140c1d80081104140104040000b80381074491103003640d50317035502c00c144040a03800d40b1891008080c2030074031080101c840c81d05422552040241d1030042e00c203500d2214840ea100f1081080e421b0362258004c0240b5464401c01418000030b070181c10811200c00311624194918141c1141c803480e030080007880b0780c80840c0ea40c5001d90420703100c0c0e441550f480d042041c41c1c050515600f0034a09401c3c05540395514035004009017200c00c050401c1d40b001908100c140b0210000030250409200c2015002c2509410503090034401e84643d8400b074031032140d52004102e030070707030011a01c3d005134000c252080c2480200400c002c100d2082d19002d00c00718074204004a08581c03a400301d41103030200102600c0c18841d0190101d0340406c8111 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 415191663 1250 415190413 415190467
    0x6051f1d0a12020a0602031815122403010b060d0b0a030c030b0109060b040311100306120501020702100e0603160e1e100f05070303180c0e07020f060f180109080c0c010e09060901030215 81
    0x190bc040c400741c12040c0c420008a0103c000b40140c1140a011500c20300ca5180c42e0761005880e04080347c3c0c1611260044001107a00540740190980e40e800c1140d1111428054840341c1400c04800055026860b0103980c1a80e030043c1c41d824049008130300b001084143c0b205c0e83c2040c151128000105042c50040000105000300c001603a04c00d085e204003c0c18105c4540d014041c0981c140c00c14140745c0764001a00d52020701d00140c020200f034410000ea808078118202c00741d11044140300340341590840c602980c0341160a44049044005007041602c7c3c03203443e040035000043c4148807100210740303c1d4020081149401044602c2d00e0700707603101c01031200060703000380c0d10399820441403040c100d50402115081c0d056410280c1700c1c9042a00940414807006010110b802d84107580001d000c81080d400000141d9210041c0c642d240b122402c601d8440391a440028041010040741c12070070704102c0c0001d4410840142100442c0e0300b103508110481c032840c421018408804d00840d49448502102c00781600641 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 415192913 1250 415191663 415191691
    0x6050d0e010608010228052a0604030905011d10050d020903070909020102061003050304050d0206090a0f080708060411040c180303030b0406051f1d0a12020a060203181512 75
    0x400f0510286014012050030400104038114030300c80d60100544440300035a6000c041c8230400317007003240110921203140c00007500481c1306000415401940d44011142e003030300c1d034118803410340550b010307450842900c140e08044e003591101200b078450001001d02c81e070910300060401c10340e440802e20780461a08800c1401d907469600c1c10a541c3c0402c6071b00d50000e46c040d05020400c0c11a66040d499014500c900c43c0503011499010046589420550740c2d40c4ea000340101c0c142641c0e80900e40358801b017900c2a0605030141400104429001088645c0b080380c12440c010f881064400034000104a003c030031070300b040115203800b901c0d81d04440006c070066000c5c0d41c02180700340c5040104030840b00e00d50b005500c40c410300101403568000b001c0c07040d166540c45051018903d00240100b02815417808241580480c0411000c9100b120310030240c401c007402503514010f1182c4603041a80d0f41d1081d080f514441c00d01c1d500040642d8580707201c0380d095a950b40040306052820455000c900068261120a8179140b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 415194163 1250 415192913 415192927
    0x102460606050a120609020a0b031003020f1e0d030c02030601060f1b02241e0417030403020108150409060501180f020f040608040204060503030c06071101110406050d0e0106080102 79
    0x854020140908011903c0110075413400b200c601c41c404200200518031502c6000c464159941c40780445c0061030f0711140d041e0f491520a94000c802d842500040340720301c031440c1d002903041c2426007010943c10700703c680c0106018507d9080111030f40103003604030b08119002001b01c006803020b2007424024219a101c0e008508140c10029000300001e408841c20812500c1c0304401596400003080707240e0402ca0f241e880c004034010388010b6148243d41c5d070200b4125603548044545003245006000b1101c02003403000e00303071407011002e586911441c8806400600075402003031060104a8001c031000ca0003e00c0006c24450581d111425a1000d0b44a9124042d6900180802c81d40501800050b1450142d0451800365040345420040c0150f004070707010052900000b8085444a40c07004e00940300050450340c4605680d060a50f43d003c007107450340c0004015040803416600140a1040072500c0007010303e05003410201c0880e92074200340e8204207200c0c0c40d000c82051041c420710500028062540016030343d04030b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 415195413 1250 415194163 415194173
    0x140106081213050603070c0318080d050a0e0609090601081e040b040209060a060801090b0411072d0b01050609041d06011e0f03020103090c1805010f0b0702010246 71
    0x4843d400203000c1c501c1003081000c03095106000301d4100f83c1c14280329a2400c26501521800d0b116504030002c148a4a00000d034801c0c0c005001d0500b25a050f03031400160284070080c008a40901c035441ea40151421001c01e0346903014440c40f55004846002c0a504580e1690080f004c01d070054030180c0b035001c4130800740300a5081511455a1200003601c1c408041c038900311000b494881c0510400c140d9558417022a01582c6d15038103c0302c1c0e07842e00f2401d42c80d12903040781001b400990451021500030b01550700700407220781d0004803001c60140c02a1050030b076030707181205103c0103510040509034801e41c3d40345401d9022000110b190f80f102c0c0010003e00066040001c2c140d01200341c1040ca2060b88540c0c1020010308401e019484196542843c3c041a408403d2810303260780c032547d40160054074241030108145041c258003c2e812140c2c13205404508583c2c0d0b1581501c940301c3c040700680160000c2c12500b11591140d42140f6601c01040c0f01c004d40d04d204100c1c6031030502211403050240c55884462201401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 415196663 1250 415195413 415195447
    0xe24040302040c08040b071805060705010c020730021809060910090b1909120c11011b02013b031e100c030b060307020f060a0204121401060812 63
    0x166181c04c0c0312405060640740c031020201d0003407050301000100203084407400000c004100081c800030f00b0b0305881e4909413610340e0180c80c1d08100d4100510944100041414010426509201e07070500000705c40115200a072609041c4004140d8101c1d072190903c140064021245500c80e41800000e8116030900c41c00b0a070901040540c010307100c0d03042121500101d5030301c006007a0000341070036242009004a42a00c00940042d200281c00a214a240060325603000314611004c0d0344500140c040d040c0c04500156214080c102c030302c11404480c01c0a540c01035001d403016207420b101e21b404000110b98241c9040304135111070348000206081c0d142e140b18440c1002c000c44141103008800080c5070007070582c134083c0c1d900030310b4007100704c560384840710000050f001ea0700c5520f440b030001e04155600e00d050b10300a9510054440308034014805e00c4c0007d220308140f482680c040d542d01403004105200f05444030580c200c210b18104009542e210800168501c0401c9503100901c3c5001d1542e0f00c03030190000c629114 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 415197913 1250 415196663 415196681
    0x111c020f0f18040617072330071805070908010615090b040302010e0d0f0506011212030b0618010504181b020a17160c180609060305030403030e2404030204 68
    0x144444417132103045510101e81c02d0192030362003041109082c2c000c00320368910030480c0c0d030188e00840b90080c1525002155241c41141c2105d0410601002066040c40d907520720a62207101c190b925144c034480c10000c0b150b000300741c001c0c0f598503060304c886490302001c0c0c0c21107030640c0c03119600345000e4854840051304006404028001045403900301441c6400180400180319485807003a601f0800341d00c00c000e41102c0541c1d0341d541000450346d5568407401c1d400d8032a03503449400d4521444c6044040b400302c1c0b090080c04582a400b820b09400d0040740030501003907000031990700f4140582804045500c4143c1164102c1020001001080340d2032240030f504080082c4804040c2150003d41400000c06c0c040e01050117600000041340e6607507410300400326412451201d008040340c40f04200000c23052011004210050b124003c208800e070350312859031085500c540b00003452500148000c001103806424420665007000e000001040718140541405000110051300121008541401981082c1c880c042071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 415199163 1250 415197913 415197929
    0x60e060405090a090c0305010e0d0e0d0c0e10080f03031b0301030302060f0408070f1b06020c0f090a11040308040608130209180f01140109111c020f0f180406 69
    0x50a42450301041d0000b100900e0004441d0300c4034003401c00c01281d078200400544d00f1000811040c9554900c5c203880d80600c8480000040e011303d80301e02c82d442d00d01300b4104410360000480c5070369807500d40c41c2811488001c08100c000f500e10400003944450900c00c030f20183e014407014603501d140c40c4580ca219010024084040000207000500029400040150300304000545040d46a81e070b61610805a107e400070080844141081c440c041003070003461104206010050140c54a49503040cc9070340c0c20031141c1c441c1d03000d010307640001c4440c144200c41c03941104903400b000c103618a82c10fa25100c1e40e4040e80c012148103600140800031341c2d60042d212908044030143c80c02c0a544a0307000108445c5002e4103591541c03034018213080000c6010402403145020100013031001201c550951603460009100351401d40e03003403000d504148052442103c0c3c0f80b00e4003800700700702c1d1040032505400a400515071303561500001c02000740c200001201400441c401c0c1c00c02064901e40d44014001511110340c04425 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 415200413 1250 415199163 415199167
    0x20403120c02040b1e010806032103090309090403020307050708010612110315100f050603040201020a14011104090905010b010c0201050a05070501180614090c03060a0902060c010e010501060e06 85
    0x3400c0d84005226400d19032800304524109030000400900c0d20241c025800040c800c0400e2591607030982882074420240ca4001113542d136501495281d8070821642c002b070071040210788074010310380c001564204171074400b00ea00f010140320100e8940c0c1da00341c2d001d802590020400c07038200801005488080c08604000f4484c030791804800f00c01da042c01c01d4000701080c64512648486840c10095041e0000b40c0f00300c81d0616090451110400a5030743c0100d04102100102c00b00e130b1420300c442201d01a55041c0c2c0201034181d42038480e2801c50b151034110000c555282e0080c4104400500082c10160650f400005000c03c542d140c02c0b421217150000c020b050204201500000d41e81010946600310550300700301e550b919003441c0890052131010f6154030450790f0a000c0d01c0610a0030781c0300740c4458080e40c10341407064131803240c0c043d03949202119955050380140c000035a100c0c0144c200c0c0c540e142c4060045030130703c02c849450500f980c1c062580141140c1d9914010451700340e1011501070403c0060318014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 415201663 1250 415200413 415200419
    0x270a05160e0907080c071502130b090303180d05061e0601020118150209030a060c0e011d19090e0c09071403041124030103060b0f060304060f0209060a170a0204 70
    0x500b02c8180100700c1802d2180020000f00e0b20881c080c201d40f60310764400300703492502d000d020700e210094101d42d000400c031800551011951100c0102103d00c1060010000d45c20700791590101004a80c00501103a003159062022000059041018030301401004409040b01c0060081c2c6210708000106042c0c11a03060602490401344005d00c007440c8203801c1203c034000c01054101000203445003504880d00340c45603035911010702245030300c1803c0104466444184a844901c011940c0041441c41480d180c0c488100d00089490601001d901e0300b2805a05003030401c0d51550048100c4040981d40710359600070060301c0075145031100b0150351090710303400c102e500d600c58005440c01d1404000c01c000c0c0216600100004541da83e180d90300481008030700380240c6910802c0005499400a10085643c1c0d4148842d0125914009010350f00590010740f419007180d40d10f80728a400f50408400d0300030415800c00c0b1480f20fa8484130014088044a5203440240315810041821321041c0100400803052041c8014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 415202913 1250 415201663 415201669
    0x2120a020a1b06080601120e0a0506180111030a0915060b091819022514010b0103020304080a180521060a0e21040b04030b010e070c030905270a05160e 66
    0x4c5400080030718110818440342407041c4003c113a80c01d04c1d540700b07101700c0241c40b0411000141a43c07140b2000d07003113400d020098062150a80d05030b05c0981c40004410310000d00000d20b81c1d070003421081e014a0040c14800740c5c1601410841e001a0440c0d4010b490000354a10306003081200d00be222102030f442c0300c5462030501010818001c5d0483c807001c0725900000c06d84440c000c580210503980a0b111a0110404102d103005000407050401d602e01e00d5080408034800c83d80a442924401c68005d00303103178074041030314400b1075800c036420000198040c1d0b1000040382a443e01d944451a5031075011541781d21817000c1d0002450850b00410050f441400e2404002c115940441e40003580f140300514003560840d209010350b06406250841054450080b4001082c002050042412a00700b603107100d0700745e2140a01128203101e00d40340540451080c0da4100540c4c182908500c5203d030310003000c0710850710085411048414143c4285051070740743c00600082060030080c40c050714a0341c0c10150843c2c17080c6008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 415204163 1250 415202913 415202927
    0x709060e24011d0303070605010b03040302070f030c171c020f100207171309020307120b0f09040803180304030f030305010e0f012606182a09040302120a020a1b06 71
    0x10f2100d070300000b45a1402030780b4104182ca510743d46c0618144455a121210003041e900b04440580041c03007001d5001650440b14100d4600381d039040400b132100c1c1410304040e48100700340700c1001c3c00c0d18400c0000c845440c81c0040c04403203e00007181e015048208042c68158a04002e03c1c1d00da00c3c0c5a803042003070000041c80e03610b908050480401400d42c90f0b929101502001c09284d41c000c00045000104010034154824417840da08042c00508105441404040c000d400c00410000ea4021011501180c04a90324102541d4840700302444c7c0041815071020250843e0010740c8202c0780308524408100c101900743c001c003400740c04031100071041860b110000707000802040c40360007020031a500005100c41c0814070102021003c0500b12880b40c20884002d010402c24a064900240031302e400c2d5070742904902d6003a0b0341c00290010b041c1501c00c800401c01a808070702402c21010b40c8a01c500105890303903820042c0c00340c0717100ca40291484202608200d0300c90500c000d02488091154501441415000b600b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 415205413 1250 415204163 415204187
    0x80304050d03110d0809060f01120312180501060f140102120310090e030a020f01020901020304050f0609030607020709061d0112060b06130303171303050a020709060e2401 75
    0x710120240201d040a840070507203508544124064421034501503a041044035002d805502e0440390680d0303960040c3c181c0d0004c00c1c094003030001307200c0b41080f021a108002c007003c55006a08002104100c0f01c040d41d00c203981503582222581d444030400c10509200c002d008008207104600c0e40c02d2140e0702e40c0000d4588140900ca0400c507540800818007144030040b585014005800c81001902c85240c00c02c1d55903002208418010700c225103840c00340d190306009461808206800440c1050704003010051014110903c1c0743d00180140b10a000c1507404000c03a0b401103220350050040541030080341405d4482d1608020910510f6600c00b0f070110170100d0486045480704c1c4002407030b041140c5020409800700c41c0780a9071080010815280604840d40150122407003900c40014401025820807169030084034440812000d01200c08003081c0a14014010001a441a992b04589a60200e81100c180b0b4003c7c242c00c401c9034081011044203000c43d40084422486035900360320703c010000304565a80781c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 415206663 1250 415205413 415205419
    0x201080f090a021201060b070c170a02090109021b060a060f080705060714100c0908151501030c11011a1507050c0f0607020406090b01080117060105040510080f0a1b08030405 76
    0x88800c04442c4c801e5110501901003801601d5407a0103a0800c522800501d0040c010f0384040100e140784a0b60001500c0e4100b03550240c001d401c40d83ca48001c2c03100a421a043c12081c02c2161400201d4080c820301071310b4820028040300254040c280305060303411041c8ca410001c4554044001408165611010382c0c017a6a071101d58131221a40841c003090a12208060510302141403e50a803540c0d80c004c0d9503001942e0500e0100c2d40e011420a00f0807407100c1080d20704002c00c1d00f11041a042d994441e8200c100d10320b24070300308400405880e0701c41500715042564041e0040a202508414074640002d4a449000e955582d030b80c01c0c1406901e8990701c0300c0340071611511800840340051926280c0f2415503c800d5001001080b001382d480e502031003d040030f040010f0000384100000b04040c40b902c5c480750822800c040003030405d80c2c207100601009000281055100b4040f544001030091400c001c5841d100f084000030b092a0082498540b061440e440700d1640d482c00c03c030400344401a000029602290022 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 415207913 1250 415206663 415206679
    0x301030b060f1c050114090a0f080c070b030115030b040b030303060d050f300f030a0f110703020a020f030106121b0b0309300d05041a130201080f090a02 67
    0x518001070700d0040c00401c00380e00b500f02200380c4060200c194007154035807040c17003400340321640d03480c911540b64802218014011a116445440420124000340c00b8503d101c20468200796160030f6106115002640f0038900307801e4804001c0000c44c1c3c0b5000d10a0315080540e020311800da10000040c1c0c803801700800981c014845260301e4820f10101300940c011803c064000c2e18084031528004051403070340103021041c5030b1582d00031413a959855904840c020303002040c01c1d0313007140c4078958481c020700702d641d40044601c0e440d00c00b01104000c540c030041041d64481e0b00104400149841440840c031a65000d03144681d00d8800c040240040b134241c81145075900441e40c1c14544081c641ca0b540e0b1101e83e030403210080c070b000b008101d400080042c3d4070208403e42550f6406005800c604500c0031040c500c0340b411859070078815110721034100d40002e500030703129202c0e08a40031580110503054000480d40d50901c204480642815540c01000d81508140b09940b5a892490301002c070036550301c514403000303000d8003034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 415209163 1250 415207913 415207939
    0x40c090e25052b120507050609060408030708090a02060f0904051503030913020c010504050606090a0219110c0d241107241404030906170711070b040f03060b01050301030b06 76
    0x5880180883c181d02848410707507442e40c404010669044104115598420000441d1450800003a40b510482e40850300c01d01c1e655440c0c004a0385070401510060b01e07885440098001039940c01c01410130020540c00c41e640380d8101c7c204200c2900d0000d0080f90300803110041803c680d840100442c0c1c0309200507608031414450990144000344141c0d9252001540781c803091104000c004224035015010440e82d0b4481c5490b0103680034100c1c840e910802c5658503400c0c201d181418003820800012030b0049090714103500001c000b2804105242e41c003160308510015501080b0707040c903000180b001d4903a000407c1070714900104903905209000e4064810382d103500801007030020190031074040080c035000c01c0c4145461401c2e14840204269000c8010614101002c5212071150211400341070b0b406400702d081d900c070b201d010350b01703103030b2012000041c0c1c040e401c00442d8116100000704001d041340d100c40d50b1040e01c0d5051101c03c541600c0412410040104010000300e0200c0c040c0f1078209030304075098404014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 415210413 1250 415209163 415209229
    0x5120c03040b0301140406061107090c1b0b07260a1116060203040203100c08040308100b041e0f060203030f060607060f02090f0102010b011205040c090e2505 69
    0x110b90180c91665000000031580640000404c0c2c00d81d05d00351024080c45e52104c02c16910690111500320b1198814001040003510780e8002ca1280f14041c2403420f10a0385421441c603c0c100a01016a00c0c156950144520694040b070f91801d0720007056040000b940c06111060108000580141041e030348540c80032034080302e440103c2c1c000c43d0002c140350300724640c0703840d0181c0650000c8900364800e01440300220010140c1c0e000c1c000c00315100d669143c202da80d2f1580d058840038030140610f18284014030300483c50040c108000d10290840044168901204005565086c01560017100101806413420800d0a400009983c0c1080c1c2c95000e802e070369912040842d0341d038099070401034820360914000d458034191a9008010041c801d5401301c0c2d00080000c01a400e82c0c07503280031940051181e410324110f001150b80300d103801c1881403aa0b5a00c0300d030786111510503289a2014250700b80c10502c0f0040140c043c0d109900c42078210304000304070321031030007001400c1c1d8010f401c4040c109003142c541461001b4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 415211663 1250 415210413 415210417
    0x3030105010f2106062a08090919051003140304030305040b0a0509181e190c0c0506070915140a03020702010512150a05090903031f1203020d030506040905120c03 71
    0xf403180c2c58108070b565500c59006140940c06880140040b41502d1401e9040910b92010340805410050b401e1a0901100500400002c014202c403a01081c00b010f11001c24207a00600b4015a12886450302d054110704200f84a0303810810103140f140e208100400001c1d0704801518201c1702c91800c019210703941e0741001e80b150b204040149901145201c100304000c4144814540110400040c4940d1603c0403080c030140c014080c2c40c031400b4040a00c2a8090383c04550b0040240304003286000c15070240c1c96500e0915092040c0c4035000822031441e81809103c0b40700008103040d009500c1d005500302c03124903c000079071059801513400c041e0000745c8181564000e600f2140701400210a064052030940402407441d40d000c48000d1080f031040c034001800b49808035941d0b0047c00c121014601c0c41d1143c2c00c0c580035215103000048185040f107003001410003644002d44541c54020340207040034031040e030001801c0f00c400501031841140b0300b035000000700707030700103800c4c0401d910520300769a441d4100c40c0718510718 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 415212913 1250 415211663 415211717
    0x901030b09070b0c1b0102010218040b04020d14070e0d0b01120303090515010302040c091a0d1419060f0803090108091f0e1903050f07030e06070609050c0303030105010f 74
    0x10000180c2d4441d501c0c00011080750046a0420300d1701d449405034012401e03441340f141d00c013070000758502b540c45040c03806500011061100400040c40d24460a0610042e1081e00844402d5400760108100c10650040b008030740800040310005110748255644904140040c0500c0101c11115035110782054017a51161103d103800100712900e404d002c60400e8603c44007404200e00450a082001c20800d0045c172504058410000440200300d00c0041c0c09080b0341c000350040c00717203552180e19003844521480380c92406103003505143c02e4900341c4146030300d095410390750080c007820007820410080b1070350100c00d5602c6d4103024a012201c1b5203450340502c1c6045010641e0328140a0900314281650351180d22000b04141910107450b103515800d0355408210000c4900030740810340404c031030b1805406074030090a8651007810a81c0310702c680c03040400c200e504503100c103c1d40a55290404003d02008010205e0100c804400440c80c1d5810f150000741f01c2d11061440c0720600901b621022444c100142d040700364 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 415214163 1250 415212913 415212929
    0x130c020a020603012304020309030d09060f090c03060b030606060703030b040b0346120201090602030a0209040e010b060910020c030a050a0b01060504120b060f090907150c020901030b0907 82
    0x2d03541c5443e420030703031744202c1403070724035032101d005442d0710a030900340240d0f485101c1e130201460030301c440807103803201a064011084170215031768014049110070f103201380380c0c0050040300c4030712546040d45410411504c0c4030501c5403081e4041400c220b03982c1c0e40c0d18210351289505103004550a80c404020602800341d81001c0766140c001d2803450030344500b5030f0a504412000710fa00e40710988140743c85000015010300301c03600328a800c03000e451011486004580c031540c0050320000032460b180d9115541241c00546003072030a00c1c0c00148042252a0a0086c1000c04c40c07114001c002d048109400102c8921440c1051400fa07080e503005a10341a0007484a99420840901911002070140c44c01d21385842c05824101d440481c1080003192962040054030305840541e1605030181d9141c2d00c0b80000148020080d075400402984c00000940300e0041d0b03140542d545100600500c6d0030321030340c00c06070040b0185081c20400c1110150000d80c1d20101002d045941281d2201c40700c0e22882b0f0042d0415880e5004022 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 415215413 1250 415214163 415214167
    0x10050927010e010c17150114040e10050a0e0601020a060e011e050601080709060807050f0f130602010c050a08060d1e05030c060601110a15060801060303110d0e130c020a0206 76
    0x80d508019003004e0034114165540c00c1c0c9900ca407035540500c001098480100c02d84000440000d6035011381c882030654405110020b0419540720403124207030300e040b2800a111078024204002ca410720303040b0103001d07103400ca0441c4024501040002d56800d180c41001d080f054071641d048142c52000e41c17103003854491070010218041c00c150840c50251405079400d41c0000e401c000052030140c07190f201e2206480315940c0d488000d0300c7e0f1800c00c4415810160300c00d41090420842400300002c000010a2040503050792500d103d8606080a030843d075042010409000c400c00c030103820709034401c2c4aa03601400858660520246504020040c00721010115403c100c02410070000e101c0c0000103050110421030884d03006039209001100d40e155204101c46040e840002000c0004405041ca440d90600c844000030328150b40d0820b103400d480890f0700503800700e4541020400e03401c40c10b2020240309400d41c20310152602100c0c01107290482080a0704508965901d91038903024402d1200440b086c0e0003d052039 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 415216663 1250 415215413 415215431
    0x3030203030613020f0f030c2502030706020712021306080102030112121706040f0902060307050705100e070524030a05010504052410020703080c0607081005092701 72
    0x19669030310a40b62544203005842001d280f070041802294407400020a9050030550a0410850f0a0704080d204600c1d5001c14060701078002c841c200c0454030b54040000500c1d02140c0ba0052604211a82d00480b0443d00150410700040865019610f0466819262050145c80c909a14001080e15410600d002d5000000024135a0181c0301b203440090700455428002003440c0303406490f450100030407290036a030b903000003809078a420750183c030502c40030400104a143d016400035825070300807520a0081080400c0700c00c00c1c8042000802e4018840c3c184c2080249844032886030b40e041184241071040d1080407002208a10110132741c44032043c0031705070035103d091130085031014010034040c40740203038500400186100104002c0400d059510749a00004c84000014041c80340c5441c000704041d441118400030000307490030000d1403095044c1020342000c1c20042001411b0001c05060070b04520f06003682842140d85a190403500301c400041e69560003040c48090b10b0020015020115407940b07009000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 415217913 1250 415216663 415216667
    0x42d0219020a020109060206060306220c060216060201151217070602040603050c090a090b06040e150103050105010810060e01030b03010207060b0316030c090e0a050d0c0c05121c0e0a0303 82
    0x4041150f2007601d40c0034069444074000ca030b85080c200c5015505901a40c04903070315090301486d40c7d00ca0b25440310780040492036515401d06000d41c550103000140c1c4400d4013000c0d1412005075882c00f03000035200034030007180c440c07001c0000b1443d50f00030001034050031152801040708242403030101c2524072150b9602c0d01c0c01814a60001d40140c41400e02007410040011030120510040380d802800040c0b508102d903007081c42040040c000b0007082c0d81c100e1400c002c045448841802c0840c480c549a003643d0901d410a1800101510810303803000d81408084030521400c004151184000c2d500b680c6401110014081c0048010b0841c0f05041b03900b5500c001126002d100712500311800840054040700c8800800026403103841040e44809041d400015105201e581015009a445010800102c49401c2619254517081c1103060902c0404a0180c0d1103100c01c001e071080b8440d00910b01240c0e02c2c0f81400030106c05586500c84c1d155920440707283c44a10158290003024241c5085401a2165011540b24540 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 415219163 1250 415217913 415217923
    0x9050a080f0d0f080a09020406090216050d0804022b170a0908070b091909111b030304020d06090f0b190501050328080403080d0504020f042d021902 65
    0x81c07004034019469000003641c09000b2038041101d4030364804540d82e0303c400840c0018080c4440c101d81c4903403240e4002a90144a001a1016031509000350309405001d02d0054a000d182c4001501404010303400c003c09a6101c000104240c0d142041118070300d0311140849143c01c0811030004c0c0120802282004030804c1180540b200000c20340f6000160b54960940c241e55902520650f0340180007044455802c1c100101440e54200c0d088187c0d0010503100c5608106451413218800040f04012808034840310841810314001000c00010391b286090a40119007005507095026017100c4d101c9000b80300300a64829416040f940003d01300100c0e0500c2c0c50742c0140803038084189018941000004165403601040b16109050343c92141181d1050405003201c2c1c0d06501001912001d60920001000c501141c0c0146246c1064032070006061820f88104121900201c2025019034034011158860054600e0001e2110702c10f014a01480c04510344448082e00c80c1d0b90380c0e544c40700d030480f003141803503900024 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 415220413 1250 415219163 415219183
    0xf06060c1204180b0915040c0905150a0216121707060f1d0f070e0603160905040b150f01050f07050a0501050105090c030f0610050708030906010e0c0f07021009050a08 73
    0x160a1040c1a0713080c040101e1050262070400a004800070324640d41e1400da4865a004149410480300031070b59440000d040310011403003412490300005a000541d907040c0419103511a000c003030070a50908003030407040544c1ca030b071800074a414221030104081503030f80e0098440741c0781c0c040400e0103201041d20401c1c0103422005416240ca079010b003440b0a103e000890000b6464440c1c00007015010701d004100e1040843c0640440d0300342c003c11a007600000038941c2503070050103002e200400e49091910301050541001007071082c3c001c01c07148091715540d41d8007484a8034a43d003440d010b510b500c290700c0c42e007115100e0124020a2441098156400c0200c19040ba41c1220300c1154025031943e140c2152451501c8111fa0000c02e00343d0402c0003945a00d000880240042d519260150400000769680b0f401d690041d141070a59030b02280042024000300341031941e01c101003154041c285a000b80c0c1d01c414500443c1c00081c4100744a6007007415261082c080f500c000d1900915844509a88001d6544c84103c1c0107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 415221663 1250 415220413 415220459
    0x30b070e030d02120f090a1208041a0f160204061706042a060c0f0b01140f0411070201050306060d0501180b0306100608060409061a01030609050f06060c1204 69
    0x41e610000d0f0700104c1c0d00040c0000380c1c0d982601c0c10b154200c804402d03600403125281d00c088007120104c3c00c00700e40030413403e010703101d801415034450078001280c7c2c840300e0b52101100030510800408502444020a0b520050042c0e40460125000b41c0300082c05405580c01075804038924240c40c00308040001091030042d40200742d1440d040307a44c5060445e8150490b448505512600b50303040040511600c4609240b0307000c2c07070801c0d230109aa9582c0020108080c1d201020700500c1510000b09803404520300d514441c0101c40030000307060300d28450181e138028030f40043c1c10701c0004400100d99440d40e200301d030342401c20001d0400085da19480880c20249102d10b81c078607107070f14000c28100349013000140d050044d00c000710000d420741c1c60404212a580c400a0003031741c101d0389407140c00000079024082c04110400c407040c2030000d00c3c40000010100c940c640e01080c4503074201004c1c040b114100512007038000400703480342c80d81c5000201400d0f1070b000000032551031406001400082c54407000340301c8130040740781c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 415222913 1250 415221663 415221673
    0xf0e121f06030b061306030605040f02040e0a170d0207020312270901090207030507052a0307030818010c150c09140a0902090f0411070308090607020601090c0306030b070e03 76
    0x45500e840071a0380c540801006004a1004a121490084140ea40400d00180041030441c2c0b40e5460030240e030b405907022910304101011075011850240104012071194100034607070358499840e80801c1c22600c0d000c030020041d00084d50b401c2c0070556011558455000303030454061031154101e428a55010003000b07490300729503058650b034460448048580445004240c01c0c40e690030306d030b28080294031414040341480380401100c00000d909000070080b01020705511214461800c0c0040501c01402a1580c805e4116481c00e100040b41c49096495400941702020750300c0c100745005070385551100c2c2c0081e26890784492400000c8405030050110300c00c02c0e90350b610000f952803840381041c400e0070b866158031404900041c03004052650140a04c1a402449d03144000190300c0468129074034540e501e100000c1c00038943c4c1c241600014529004115040105510f10f4840d5000751540b0f03047c094018803070740300d455032800144284c0003a0051604080c02505034100b20402401103020900664000c5c050b0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 415224163 1250 415222913 415222963
    0x11102d030b031212070c021f03060515030f04050a020a0f08010b04020c0c09060a0909110306061c030503091e01020a090f360c020a060b041a010f0e12 66
    0x11407030a0680403080301c507a0031302186248a10090300c00500c22010480600c1c081c4026954490b00d16900517240082c8841640314600001d05031215904003078010741001101410481400c42265440390140002d60b03110f171604e10741141060b40c0c203040070b0f600a60348031010880d980000ca0340000c88507810000c2002c4e02107002400241e00460300d49401581003409044006d08145030311542c0102d005101011079521808440d080710903d090a9800340c0401e5840165424100a482e40200307048a00043d42c1448820f1007500c2d280c141d500808100004c8045002d48108101411142030442d26081c090704010340c000b4000e4100e08400700014000316000201554040003140540d151110040305a501c0c04c02d552800c02949404c51f408000d00c00b04c070342c001720110b2040c0801c0c448241c0c040c110511003070030204191110b0034207079889549420140b000302c480d240030214003090300707003400c40c405150240280c03280c800d21a031041c0c0110003600304031611400030604400941120f0301351144110307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 415225413 1250 415224163 415224169
    0x1207060e0f01080703051302040f0b1512010b0a03020903100c08180d2a0302010902090108030903151f03080406030c051305060c030c0304060305040c050d11102d030b 73
    0x441c0900c0d00c1e020904500119004c244260080742c0e04c0380c900145c0c039120281940c0490221a0081c00020740c00b5940e18000140e031a1100444010a20041045040400d64500c0c20a203a4045c4a0004019000503844d0344240c020707010396540c0302005040e9034855501d52203640142841401a80010f800300300051140c0c092807801c0305060000c10b0040c002c22000c0f24003075030b00151040442c21000d004003201140502d08500d0480828480c0c0d001245648503441030014842060300000e0580e0403d100526003074900061089100d14482e04082c41616011201116003151030340b15411080c1040010091001c1200144111851a64100012444150212094007031240140204400d111041000c3c1c50410007a200300c0905c542034903e40384e0024515840d5070311503030005020a4039441000306111003030b07041c0c500601080c0c40764940100d01d540c45042c0e52000c02c04845c450f60481c084140041d1003410341a004d05c1401c0060302c5182c0c0340403016500c420801d016440000d0800509600d542 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 415226663 1250 415225413 415225429
    0xa06060b07030804060b0102101109090702030408120a1101091a0a0204030201090e0c0c060a05040507090504111e0a0b0702091806041203022811010c0c02040902030703021207060e 79
    0x55010740e01c0f40e5040c1c69681d60b40004c0e0403d00b40e020304610840d03402034080a018400c0040500042e0034550f42c0e402038400340284060000e2442d01550001d08c8100589039021403690041040c04540e103035902c00515094a00304090035100740d0301d6203050000d42c02c06c40c807030002d10000c00c030294030346106980c4c1c5966042688154000280040c4580d84200034007c07800c040d854012200c0c26140e4240311090300142c0c581001210348002607500c40c0144010300c28180001c2c0040c21524000780064038041e00e55131086c171400d644590260032007480c020000400c2c4910a0507840d002800480080e0362900300701502d030001c40c8107a201c0c009040208810300c9410b0b06107544846800060901c07036866403500d024a014a4902005154003006003441c2010b1001c540071900c41c0f0241e02c04035440000c88000c208824000c1c07058401ea15058120b003101d030300521240c1a41c0d034100c5000c01c88840910100b8180041c0b0303400207400c0032042c8420700c3e0703416003c95514159903182d5181c520700030030441000160 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 415227913 1250 415226663 415226677
    0x140115210807060c0c11100e010806010e030f0c0f041b0503040c031b03050d0e0603010506070503160807260a05030a0e061f0f05031005040c030605090a06060b 70
    0xd500c00316854895008200911004640200c10345820144540c031440281e40c0106101000079070410601c8040100d886400b4000d9401601c0c41c2c180228038907000350103407285202460601038401d0025405070f20a0750608030284002d800c3d201c3d441403a05045656000d0003100501c105425181c034011030405d4825140f501c0c103000c16010a179421002e040d0741d203034005041900e03120b6040d60040080b82259011081d40031020002c1c80c0d041c1e1075400e0007070504e0342010b071480811040400301c240b255100800e82e41590f1045425903540d5885180c070910b140709440300720300b07440d0342030150704240300a0001412405000f407000c2ca0600c9d8a51400ba600c8003940d6040b0000448248821034089100310007542d03000000c6000040c00c1c03040c0320b16080c0b91030012904403400b000c1743c0c4110403d403080408204009c107260980404207904100009440d1a03210762041002c80e585c0001500748480000d440e001181c00240c00c001605080c1031880c0caa400f201c00945400c7d06010300010294000d000325001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 415229163 1250 415227913 415227929
    0xa0605041b030b0117070801031514040201080c2a0c060c030a03091716140f06130303060510030c0f1403061009080d050306030f060c0706020f1303140115 68
    0x38814140301c0c00e400400340300034000d041000c034507407001c9061216840e1034000c0750f15483d042d0841d0301d546010700c2d00588034a944000f180c10086a4080204e00d040000d42040d0309007050b404954800c400043c1d0390152481c030f414141c0c500c082c54103001a10821400c0d20700f8844003500d0842c2d030601c05002180c425005903d03010fa00030051803901c20320a074001044203116182030b0324886040b0030302120780c2d000b100075035038204610441c22080181540c25096080b002c080a0081f03503c020b80e88d161242c80041814801c006014811020140300303501032000ba203c024001c1c0300001c0401f500030f005286414005010400007222044070a0090701052902854401c80b80c0c503503038400090161616104000c04107000d071084020a41d84014041842106455943c2540704d140c8101010319100d4400c041841c550000e80601030317800e008404903500240c0015015075a031203000d0400030107101d0b910042c80b241c0007400d07000c0100140e1030989812103519600a11912540001c200d40000051050041c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 415230413 1250 415229163 415229201
    0x102060f010614040e1e10150302071b06020d02060f061e13050106030e070504052e0b040306052523040b03100509070e01020d0c050307020d06050a060504 68
    0x140c248203280801030700c2e0000f01880d00f09640d81c03410100c64031003513400a00302c4003005440b0f400c0c2440e403501d155000460a03601c8450768601a40000c040340c810b00c00c1d02c01c040d000103400003403000c804251240c00c0021251003a02d9035135040c00940b642c964506080040c080c4101003405031428800c0580501001440100110410031804102060000e12240c210980e0a01520303181954400c00d4001c2035292404610b054201c03d036182025004d0b000300d07106074940f03801c0c000c02614591400c0705100b6004200788401100840f00001c3e540c2a906c0499503a070002804003c014154010500420046206026041030281c040f5004001d6080c00c00004e10792000f080d00310703441c0300e149802e0818015805880c040d1190101400d90703008480481c0c65400c028020000c40c1007030340c540c40c0d1100c402d00d488264400c1d0b01c40001e4a03141e194400301c04100c100c81828003402030500859040b82e0b801440c2510554851800301c021b40030444209a000f49005400100c5041500030b46100d5101140c00c10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 415231663 1250 415230413 415230419
    0x6090509070503280e061816030b070302031e01120309080a0312020f0c0a05030a091d0609180f0703030212040605030117160807140d0f020f0310020a0e0f0102060f01 73
    0x54070080e400d29244d901e10f620340b500b00c9859030b001e010282c0901e01301108441590030319100540360856030002d084001c250718004101245030b140007aa0016610715001d6038a4890b6400981c156604890000d0105a4500006110105291183c1415200b500c0b0130004950305d140310360315032014031000b9010034403109108812140c203a0040c11001c103460481400c040003044090b103068003454045900364000180411030940140c0404024a8034002c0d0a0500b1140c4081d4845004090999401420b5410204003450420000d107600c400e070a00c00c503148160702d0b03100701d640c6400394403040c0c0c09030041c031015007240d9400600f118281c8281d42c40303c030314503480c1c0030305c5504071040a603001d0361900800b13246454000f8620301e680c00406244000700100d80c108005269840c0522109510580c1c4031b0741480c00080d05613071020b42564040324122044807000700468107140d11071551124540c80020146001c41d040050203003158401d890a15403465008011782c0c2c0d840080c0ca41e1000001004010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 415232913 1250 415231663 415231711
    0x50301061d240c07030c050909030a091a0d0c030207060f0e0c1201140c030403141c0209041103090a0303050105030c01023007030f0e2407060905030406090509070503 73
    0x2800040c0d18041c801494282d50f07456103410400ca07508100e40c86040c51400b0026443c2c010395941d001042e480c081d600d0240c0411025050780e1091150300c551400c02000d49028026900a40b041c110b01c1002c14404188941d0005000350300c241800c64049140980b280b400d081e0074070414101455480082220a8583d801c2180704c16102480100941d00c4000d2004a50100c02c010b0380941002c00d0480d03240d00345031070064416020021b5918549005105546508030405405190380302c200d000166100d080702d000c680501680101c10858540000a1004c00c1078001520b20b0000e019030390400440e62118105a1a1640c94071542e005900c4400c043c204200410f407a40c0120a609400172150039641500202c81e41003204d0075404248443c1c20030080603040092407081c614103d45815080c03c0241c100091100d590701020812200440e013242000b000b680848080c9030000d044075115075544200410a0311180103281c000c049400c0482c0c80f49000b02c00340e0b40100d0840c1068500c01541000e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 415234163 1250 415232913 415232959
    0x6081909200a031e050613050a150f060612290907090812041a071212090602070501020903010b010c05060a0f09020d111002030414090408040312050301061d 69
    0x80c01c2d4080c1509000000281180e100040c01100c0410014460b0640782405800c0c007500a01c000b051100d901d502c80001a008100010141e82c0400c03940300950341000401c2c002c01004210060042c549200850881d4010001580700e1000313400c140035041c04401c15001c0509001d00c0074020003c5400c0661080c40e00d003d92a45c0301683e841c2072025641d403000703007601d4004944581e0115030070000d401d00a012640613000f548503050100f0518088031980d404044000d4031144c0b208101010701801c0102072940c03c2000700300d4001809540310140b0b030904034001d41c8900002ca00c41c3d07182c01601c08665028044101e40c1c0c90300b14001c1e04c02561211213844c0603010401c050b60b1b2043d510003081005a96814595082d680501d40d40e840d064035a030217010305078100c40e0000c1d00b950300038001000552a01904902c1d030700025111409551510714113103245000b581c00051a4600f07a18402035821740c03100165048503801c1d0f865403004411380d40041d00c050100c4013001d41202307152180400154001e04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 415235413 1250 415234163 415234223
    0x110d1407021003110324060304020d020d050c0a0905150a05010c0308090c060309030a0201051f17030403050d05130501030c050f030421120506120604140a080406081909 74
    0xd000c955a140010540340c203910884144a00014001a94100d42e00c401b02d032841c0c0340002e4440502c3c40c240360700041c0c413006000c01e00030711840c03828000d030040200910502e5040c843c042d000e02c0c03c031034690300c5e4071015010854011a80004800300302c0001e241c800f40340303011280180c44559100580361022210f40714004c241d901070f482640c20814041e102c0a008621420020006d16210305181000900f901c40c0500043c00001e40c3c206002200070400e90090304450f0000140031003154128500341c258000d40d8000790088c02404100e103440c0c3d4100c002440300d16000b0007078000454440c00150122642c450b03d4400007242400003c000c0d0301c82c8401950000e00802070041c442480c0c4100302c042c643c040381c0000011f81d100c0442c20841625009503508050111404040c07100710345c3c0c41c16a14940288050100c02c0a06110040510f05005804005821925650703035a82c03100c0300030305000026079000c840320703070203141e46408580c1c0d40c81840c2c68140d0102c079900310440000341c80300c9914243c1e6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 415236663 1250 415235413 415235417
    0x201020f070f02040c0305010b030606070501090203030310030c080f03040303110f070807140108010b070b04020117130210110705060306210c0a0b040810110702030d110d14070210 79
    0x30401211011540151041a20840d05092884039030720510041d501080320b071900317150400c001404403092460a581d4080010385006440d00c1c52400c185000d0701c00500041d4140c0400000d1026100d0080c0c3d288054038056194002c0b1141e43d0710250b80d41d00100c0b030500b120b5410034041840060f110b11542030105060314110b4120000300c0e1000350510f02a41d100030b52a5009810070006855100c903980c101719000d01384111250b141c035120808500c50720b0300c003c0005400a00080440e8040d041000391035550002070020340c030305141d051041001107402030b0300c200704a040c80c06449104507280024042c100000c0c00c02a0700e040f081c41042d03000541999805486070a868020780701a8108400d50f500c0e0200130003249001000f070000141c45030b00a0086a0700400050042d10710010714260450102980028442c0c41c0e25001036843c01803c0300250301d40207803c0d9034000645d02c201001c8003610741da0b041e2a4070007610603003035030b544e4081c000f02c03450043c05101880161034810f12440c072150b894 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 415237913 1250 415236663 415236667
    0xc06040e04150b180108120a0e0906040908040b3f09120d050f0c0f0a0f090504060e0f0c041412010603060615020c06070201090306020304060b1c051504030f0807020102 74
    0x90801c0b000b00b01c01c0602ea01403070303004000f140c0e410841e89911f01a420046481d0220845004000f0b00c0080381507402100d0800104400e6241d0703a12031040c030790708090820340312034407007103004210703404415000c203107610494508000c8c03002140d0441c28005006065903100000c003004003420076008151000070300072074410341080d007043c2005005060301c6078000901761500007020048010f0240034410180ca040c44043d0031074110b4405c9501150072801c10314209400000115441c518035008550850f0402c480000c0022400034a280110795100202c40e0a541c0e401c44943c0c680514403890155401c03041c50350b2491700346140742103002d0700b602e000820b070581ca13600d07600d096400381e601c280408600c00d08035031001da0303060007980005c000490788149401d005e0703000200041d030b1502024140641c0080840c0400100c1d038406141c0000107454110300c1e40e00c00c0e500d8901c4445225042d03030715000c2e6a002e0442006464140c40c802c2e0ba0648510038000e6480400b1510349000500500c01e640d42 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 415239163 1250 415237913 415237931
    0x71403160605090a050607030903141e03090703020d0b0105010f08090d03270308010e010b130e06060c0a080904111312031209080a03060605030f01062105180c06040e0415 75
    0x5c14400300c1e01c9a0025200440c50310164036009240302040c405403004e0400610140201510814001c1c941c500c1c01d01140761207845082d541b85c108156030748000d61140100760280d042040b4941424101c03002604d5124501251010907640c0d10402c40d101c9000b43c0240e40c00c079020501903404042c403110745205c980c64565400000c074031070f108007080543c0807454003401080641080361100f809451001502800c1104d41e400010240841d80200b0020081c450006000d544484040c0d5040c0558201251070901c02c42c1010300f255442010307820301450a1220125961280c1001c5400c50310920480d280c01a1811000804030074140c0412070030000d600d80c1d094075101e424090f0001c6140210045c070364440c603081002e41290706581c1701006101c0c05000308255000750300c56140c115010740c10001031030451000a0010310076000d01400c5010321b0a810b010b4403502d16100a00e00e010b030a411103910b8030300380341001004d00840c402e4100703100c085800540010f440d0003000c110103d600384042801c40b4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 415240413 1250 415239163 415239173
    0x91508160509100f030f02032e0c121b020105070e0d060207020402120f0a0b100e1003060f080a050c010201022b06030b0a0506010e010e0a050d08130308071403160605090a 75
    0x44c5904c26102c500c4c0a41014065103410700140d98a0003003014112660300000082c3c10445610003a1000c074240d4946c043c03030013103000e8a035926600040500800105644031052215641281241d600540c64103000843e42030051890050300c11000b0a00305030300005a40701000380d8410401260000c2e002d0029a0fa103014074518280601a121440b400782e24000d0076010468030409240c85c800e18405140301d00b2203800211800f032161094907510000c0b17142c3c0c4019006442640d001050744c0d0211700c40003030359030004600c0e4901c0320701c120141c4071410003107001242070303000e0030001c3c0a40680044600031f0f484182d096101e180071072004045010381d602d49a40b110340ca011a03400180c0f68482c000c101207507074801441c2c4801c0c442402c1c01550603818001103035000040f4050130b03014080018031117041c071643c00c064a22340400244000801910381c82d10301419004600112184103070302d40e440120744e80100503210001581107500e02117000944513403000d044090003013562401000c8412001c58 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 415241663 1250 415240413 415240439
    0xc0309030d0213171507180303030b04240311060721090e0a0c11011505060d020d0608030712030e03090d060905070308190507020d02120f060109150816050910 70
    0x102d8400301918406039441c42c43c0021010050680e1b0401041124010190f1440400a400e4070b8041ca00094482011404540101039662002c043d40d281c0308032300061203d40a41c0c1c4000c0d28402c00c0850010f41c0c1c91820f1090074000c0440c000d00d00245940b07030b101c5104125804e02da4141c2c883c50500402c81c1d80c0e003190340c848001903138101710060b100c10f08040005c1d04084000c0d02403030b0302c0000700a5085042e020b25040c01d100e00074030b407151070001030900d50340880b501941c10703007413420400300900740d17540c80f6459996114510844400f045050f25105060083c80741022410210b4095840d00120508200d20010100702c2200c0e003c0e9910442d0300428002c000d410080d52240f054566a4a41c0b03c1d171401030320580300e44140410104004200041e21000d0441402c141d040c1c4803450700701400d4807854200603080444c2c0f105ca03c6001e00000780250181c00c801e0380c0e01451002541103940b2441d54540310015000d03440b01d10000c1000400845c141402420340c07040030052103122040e141c0f0b125074402 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 415242913 1250 415241663 415241699
    0x30c0f08030a0b09010b0909010623030f0a0c18030b04030c060f0509100608150a110a030902040612020d030c21030f06150804110f12150c0309030d0213 67
    0x82d83e140001c2c1a142032900c856409010079403425800c045c18000010440c0782c0502034801003040c42d528800c1d94071500040e031100780488402e40340e05c070301c1c0004524101c044104c914800080c03c00c81e02d540c0142c05000500d82c00c903945507040c0c02a9045480d0340179002809442181085060724032500414840d1007040c00860340c0180104040c01c1240f81145040002c1c0e5105201c0703803400c00e04020841001900f011140510303000400e19a035400e03002e000030316000300a4001d004000664031085585540001c8001e44200d90401205848a4002c0245080c6a1000b900301080001c0f800c0070034000c210006405208441c0800b07951021a009210300134045061780100c2d0301c1d199070b000d150550b40964dc000e800c02c1000309110f030041c0000181410b4018201034205803000c1c00c2500141c80d00319001e007034000c002e840101c1e0700b2410068259202155002603040e0002600031900d03941416080340c0c0178202c104029030901200d851001c00a41c05000c9010b0a050805000070304414840e02640031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 415244163 1250 415242913 415242931
    0x10e0601140a03120c0c0e0f070f022112040f15050403050a0809010912051b01020f07080d0204030c120605090601030b07050a110d0201020703090609030c090c200607020f0613030c0f0803 82
    0x10500340000d0303600f848c1c140600340388184000345182000083e40061072184d428511518a400da40366040000c00c05e1042840450341036107480101b009010044401e000054440d400401040070248124400c80340c054a00400060b02000088501446600341c01c0c1c010882c800000b0f140741e02c0d031b075504810121207050400816000b055000c442c041c0c202103214400c40c190300039881d040302081c032542184542a03004002c40300208408000012950690300515480f0700c111444a80700d20340405000380942c4121081c50400001a0f00890702080c0603049a0340303c081e004440d150290140c07180d0304401c480300300700300c1c41d10303079101046008110a03a03000010707800069446800b41001444404650044424414031840400000d00141601d1040710909240099a0121000d046408482d1102007250010503a41001041180455100d000d031303400780c080318050703071b04207500c40d4440c4800c40d03481891091992040d40480c0c003a10340020481e100c0e146084d0400c11544d202c003020380080d0b0702440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 415245413 1250 415244163 415244189
    0x304060f0e0f1b0307030506070c051e060415020703080a0e0309040f05060f152a010e010b0a050a120221030f040306051b0307030c051308010e0601140a03120c0c 71
    0x4804001c20f541040c004080c0c003c0c0c100b440c150340b034180c1d5415015282a00700700714003c405003400b105001c0c01106400600c112043c024604021130359644060704d06032006040d403515030f005110b40b0b10881d4085940340c0c031440d5499030b034010148004e0042c482210741501040101000395035070b52180c00c1e0200c20101000420342014014820308481408403603011b4010900c00799030301408001503c0e04014680d200c501007808159414410045070032030804150f00f00ba0064407001c1c410341107a03000d40426502810041e9544040010301324041c802d0307240c0b0401c00b486890241c02c22168043c90201c91081c0d003c1d55844100c0c010303203150300007032400c0c12240001c6810f00c20030605002c0c00d40c012104007403e610801480040c0d501a10000e84940c052554031a00340034241e01403401d449142c0400300c41a03124030365a5081070b010381120b0a541039140100e000114a1080441070035407001005807864450604654801c41c0e86650514400240105000d204001034041000c18000e0403003841c3c200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 415246663 1250 415245413 415245433
    0x20a05120c091e240c060a02040609260307150e031c0b030a080a03060905010b2a01110d0b120604020f04111606050117120304060f0e0f 60
    0x1404100c09071501085210410092415030f0b90800343c00b100040c00c40010030b524143d04001001e00114103811501d626502500f1801d003422840501050b00540043d2122907035000c000e0320403486603004d5880880e00e0300000f8801480d4544410040c036000610310355400c80007842e0945103070020035040707031030800400048200c0c11807405940350700d8070034100950409190003d1900c50030700c3d0301a1a0441c0c2c1c1d071402c04610700c0e5010003110384280d401640b510f41d18444050010040c0503d0701440f480182404000600d00700203078100c40d00440000d0600013002c100c0111001c458a644400345040d640720b01b040080d410000005004000a00c0c000003a001c68440502c030105049041101090308130004110240c1c5640b544001c403c18201d030b001903c0c004540000c1d8803801900343c0e1420450010703502d41c0400101c0c2d80454103035030102c40ba003414008500c5045540d00c10070501d5114880e428408100010703025007080307a01500000c4041002d41c2840910f41c80c108440c104100d00f944031440c20707 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 415247913 1250 415246663 415246687
    0x10302030d0e040f05091f0e0d0c050a0f05060610020c060405060307110d1e0f140c030705010219031506140a0504031a04110f1507050a02030f0d08070f0e0d080d020a05 74
    0x400c1c000f801d02c7e400c2c011000305800c0c141e00c5030307810340d0210300744001002440b08001007401141400340d4440050020400300d41860b582d550b100302d506a00900601d44000d001600016107602c41d800018440740c0b400d4140401e014481d04050310300c0041c0940c15401d09400c01c02441104443c079441c0d41d0b2040100042c0e80320016080a48050400340000e0442800860b507112605100036951456000c0e60f4220810041d0b156102d0390502400e20b5201107002d000800344012210a086c146940501c804162001905500207aa00c04c180114001000141018035424050310f12445142452420103550b030f142e03c8401030a03070081d0340c0400700c88401c110030002c403c4e03002e083d02d0405480b000b1104102d00c001c9401241c0298000c50349131004110b41b020010b0400034219625070160a84d0259445281c1d031036581ea82c142c544001007120040040c8107540314000c0924404556034072015021400001c0c4114070089003010344401c1e000304951a5620500c0c0000c000403151a0b0343e0700c0e5210014401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 415249163 1250 415247913 415247953
    0xd02101103070f0c0203160b04080607080910090c0f0611101a1c06020415030605010f0c1e080310080c1804020616020405010b0702090609010302030d0e040f0509 71
    0xc0a034510424000d0207040b503440311900b00320350040d0600000c0036402c0d00000e46052a40074110180c04802600440d5000c0c01001030400c5035401c40031a482515481d000b61000b0303400300c40c0c4200c1c0d9406140000c011200c3c03500107100320742c020400310801948804040c49558070303540110000c240b0a9060540f1850108a120300d41601340004100801d4841d4906855209074200c1c00c7c07060001011040c01540181100100317182e00030801c5540303c1d5030340580301203400301100e8000468908075000403294025010340117a03c900c2c0e6200c6e91903070010350381d55555a261550340354502d55400c146200003240c940045008508030103900392a180b500084a140c6419603036650702030340b03498010013900040104026040b940c100e85003501c03220f41806004c0c80c0f011290019500c1410a030000a00343c95040050500302d00030340e01c1c21101d070303115030501c03219120a2000a401d54460b800f030450403449450700b0b00385820003c00115071040d41003001d2040c0c03442503503220b0203900480301b80f40d010501000c0d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 415250413 1250 415249163 415249181
    0x7020607020a050d030c02030c0102030406090512031b03070e1009081605030615010203210103120e0d03080a0b0307030b0609070c320316020915030601091d0d0210 72
    0xc0207000001a0f03680e80c2d40c0f681e0300d41c48807000b030548400e01e08910500a1050350780031f1140700300840d01c0e45000c0c10801c010700800c42050f100303401940030015000e50b0310310840740300d6020358144500a6101c1118540a580000c200204010710140c0c02c0045036290010361b2803880e0700f036580b02069810078084908040d02d044000180b290000070400c410b440c0802c1c8158401000e818007001001c00c0310042c2d09610441802d400f5a103100c240900c0640486403240341643c0c090382c1c0603409200c41b400709032030005078600290703448a02d1030b9100000030301c0f80e803085034440c03540403000c2041151040440d01e03003d441c0c0c2040341e80038150020400d4900349080a0b56024200b85480820304613540c0700c40525080344c80c0c20070415058404d01e425a10340d411101c00c1000080d03400c403a0340320062080b0552243e90003204070701c1200b061010480800e59580d401c2c000c994010040c3c840c0d0b03460000c82500400e0149200d410b07400880d095829215000d1041c201503519035006403681e10440c1d0548000c13a40c00d42 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 415251663 1250 415250413 415250417
    0x151303020406060f0c02090604060305150a140c1b0c06070503190c0b01120c030b0405010c030c030e030a12110c060106020c060414062a25030201080c0706110f0307020607 75
    0x10308181c03442c1d40d00005e40c030304064041d6a6540b031500c444010801038110383e003002d0a14424418010304c203100880b8032131322071000002c0811030941e441d00d904960010a46074081c20820070300c580f6065018400c8901c00b03e0b02c074075003202e403e0326005000c00c0c401e4120010581c0c01d0341001c00d0302040200c106003109030041843c94030f074142080d207a51b6450000383c1070189000b402c4002500f5070801c5255550203000c2c540101c2e5080300352a00380b074210b0292080888100010b418442154102ca0280c0a8000302940c05405141040200c901c00c898068035007406d220402d4540c5014000d5805c0c9100503d0b070301c00318030003920141d07042000282c80c0004240c2c400c3c0c0107490400007040f4210401c0c2c140341102104035109555a040d541d900c110740310302c210041c02486c0f00520016005400021003e400c10040205058180400d05102315240c0041c8006070100b402d810000e9605035a400003044500d1182400240b0881c03130b040071200b10707000100b1821108400000b40101a0340402170140d01081034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 415252913 1250 415251663 415251677
    0xf030516031a0c070204021b16060531031101080f0103050a02040c0203120f01051002010e0303010e0910060609050405090d0e0405070314040804031b06051815130302040606 76
    0x503036a090440514031030701590400b4034201240420700341c0b10465402c80d4004006540f2002c0c52100b200401c0c259020a4005114007000700b09606c031840702e82811121291581801c1c00164103078040c8820102100c081c0348a12400f0300203504c07210058a10296001d41012403a404100001420a000150089002007403001c01000015000038140300308a038162004145043c07902000c2e8954062040703044100c070004400c0100104441c2c3c0f1160481c1e00440b8802513940c00d5081c281d08031009201000300a0300104014054102c2c3c41078503035000a00107040701e035100c9400b04154121801c9801070070000d100e170041000949418014540c00c19180c80260580f0340b26a50007416080d02000b4090007183c452002580240c040d601001c2800c00d0000085001d02d000d00c0c1c00d4450303070302c00d00003102d22030712015500104403403540302003060b50700300c0c0c544034548a518001290110b0103000e800b03038440c0d00301000f190880b0200015000021692800d0180a8103520401043e40c0640d00184108052 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 415254163 1250 415252913 415252919
    0x12060108011514040e0a05150409050703110a0e0408040608070509104b050c070308070c0b160203010b10020322050a03200a030f0303020a180f030516 66
    0xb440880320316081e508004110151002c20001d081c091a072280c940750820f02d040003260380d0aa04054461007080c014942c03a2a0000100011100d00100107405544120b005000180c2d010800c140d501d00010406014695270710a46d001c4550100c5048404000104041210a23041042c0035004407680c1001d44c1842c4014012031000342a1104003000c024281c904100c01841d00f00942e80e40744c0850000c030301d143c10381140720112010710302c03401c4010781007005290012034464800d803083d40300d48101030840c103851750f03ca035001034000490079200710002a50005076540e0400042200b80d100d01b200007a50710702401010f084880c02d0f8801405645000000000c26501108a5a1501003034410f00d00b034900307002c0706007480425074000303d400120400010050041030f102540d8004980303a00103404501c42c00601c50607460034030008011060008542c0c0000e4040c1d000f0b004810485d00d032070407048030004141425014198401c440558a00310180181f0900b8002610725070928400c40c41601e00e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 415255413 1250 415254163 415254179
    0x607080106210e0304060201020403110913080d1b1e080c030105060c0a080c0604021f050f03040f17040503120408060a20071b060c1106091c06021206010801 69
    0x240d00106900704a07a4038103910b034000651010400c250100b08980d2610340700e200180c000d52081c00b065401202c155030252031445c10407541880b0b0302c4c3d01000c0604402081d92401c1c2580c120310f40c0704c19031640700c01c032000300d1000381e081000c2d0701e41c40707039842144003624800c2c80082d0342c101c09a4101000104010440d0180140e0102e0341120001d4400c81e541d038001840c0242003d604190041030b00d0f8001031160b400050000e00140158022199103030140345280b00c072400c0400e0208a1008508140700b03443d4924045000345da4401c1c011992448040f80940d20b100e03070740c41e0861034001780c0c00011a0a10541c1000c218203920003011684807032802e400c2c04000c03503503a10010142c00312540c4660264800501a8607140c0c80280c895a00c7c03520307010301c0e15281070008100c0d490040b01d00d410f2900011243d1062003094080303500103882d200035884060602071194800302506800807d4200381380a40300c159511007070042c1c028800103803691281d29902d04121409094141001441d00040c40201c07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 415256663 1250 415255413 415255427
    0x30c0305100e0c131d130309050103020d0902030a26160807030306031e12030c0c030804113001150608040c0e1e09010204060903230307050f0607080106 67
    0x2010740d6100c0005554180040e02c0702d04c207200003920004455400041e9079204102c409280c025843c0b50494566112402404400c00c448006000523040baa0200a25402513000300980030308088003007603581c820b401292903c41d00110442d00700c911850503030007a00c80318114084c21800078000600e0110007843e0800170040c1e0031006040e420780098034508141c040e42c800c41c000c6a1040300c0c10503880c610514103071071035030060066400b1000810007041e00746c0700707118070350005056894004510304d0a8900f192800c800400c100c54010303c944508002d0358500542d6004403281e52804201d41006000180b0440c1d001008640107078113080060302c491070952291400e48000346068071b00740c0d07568240100c14040c0b552220004142e11018441da03984000302c02500e4052081e195801c81c2c5480072118201c2c41544507903070008080c03440c24000104420040340f10b111040c4942c2104042c0800554111340c89103808988913407042021220450040c00034661115150900e80ca896260440203003030300f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 415257913 1250 415256663 415256669
    0x1b0212030903160f06050f06210c0406031a0105010c122609030703090b030103020109062616030e1605060a05040306060b190201022503110d08010807140a0902030405070e16030c030510 81
    0x9d50040003031809490401424100718801003090008035520305140000141110f2105000362a880001c102940509602c0e52855403003c0030300720480741304004481c03405003045150728122280d8040580e050401091300d0148280c0009076a460381c03d0320300078004440c56804801900790030720041000d41c3e0800d00700012101d0354141400510010341d11408003440007000c07049440d5120307050140c0c1002d101004041c101d04d40d1800c10855041c202e8a549e501695601c5030000110725400380b202d41440000384c136003e01107080181c1003130b4407599840180e41498000303641d94900850141821420382d4140d00d40c4900038002185012400020f0780bd100460b00404196404941d180780300b09449100200c41c80300303100041c0c540c030050185008101400a1203815100e11801601051003c1150029154400c0040ca0a14020300e003258000294100400c02e44140c02288000104150070151070b6200750703400030043c400395070000c0d0040e0840d00300300344203c00c1600e04010080000000309106082e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 415259163 1250 415257913 415257949
    0x2709010b0136030807080702181308090d060e0115050a150e0d1406091006060206010510020f0a030302120c12151c060501091b0212030903160f06050f06 67
    0xc42c49820550340c1d80c40507103034001450448002071034014001148042c0222070303c02c45024035101c0c0c10050340404031703405441c5804840d414000410015100c2e4008000e81000a000012401c520741c661604a45220b20701881603515500d1800da60118200040040d100440c2c8610046040c40280214807062400ca082445206070074403000350b82e03411b8190880740d07101c3c800a02e00c603a080350035511180b080d80e010f4a5803061090005079420213010301c0081e201f15a00078050341e8a030a003000f6911841032110400d41c001d00350b00385140d03c7e050110f0302829000e034401587c6c40c40760b40820210500d000b40f0300b11140806001440d003042d00c20300802e401948550720908881144000901a00000d42629403038165a000d10b10070010580c0106040360300000040140c14002041040308040e894022401a001600450381d050159000795410500d440101c0b403c00e036162504c030b50941800c0e0342c140d031002c058a286408208550140a0f40016002e80101c1d107410400301040d000f081a940c01c0503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 415260413 1250 415259163 415259237
    0x102030f0f040602130b07031403011406070204061d07090e01060c20060a120b040507140313020316090b0a06090501030b01021014010302090703090201020303070e2709010b01 77
    0xb0f002694050340c501340e540007006900350b0b0740c0c1d4280070f6156104c0d070011804502c00d01540243c0003250000e880c1220310885c200110350010008000c1c43d41c3c07103514120780c0143d0703812001c6141040c1c4442947d155042d00c00c1988903041480f006050f40c4400d0b07000c480c522910030014809107500010701c1512a0f8030102c0704030f110410954686480c030a000d0800c1d041240440d5501056600c00412194860021000c000c1080c29006100035114115140004212110944d05040994800542c1d014040350f1000b800110580d0000e81000c1941021550034005c0e14014030100c846480b90380251441101c00401061038410701030600c2c080e0b44100b5041c10b03500c01c100d01459009000040b2000c600e84000c0041c0158006400d850384000c0c08164001c60b1a540020703480c600a1040a84a80d01600118116556005c0c11206500d03500791954100c1122100d80103484e10351601c4100c0401c110b04625000e252a50301203084500c1401824104540c00e0070400741419548440c1c0c54404040349068 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 415261663 1250 415260413 415260421
    0x10f080c1e0415030509250801020f070b0a141609090608011401050303070807113f191106072f0a08061302190906050907020102030f0f 60
    0x1080d8000c60401d80d400301000c00140701900d481d040144155124007070000808030007410110102c8030200d0390811181e01201c5224030100d03031050740a01501c0c2180c1c200c20f544d40c45652090990300400301d0031207090340126070301302040807507000140d012a19070410003803111164961465500094203481444055101c040c40842c46014003401500c58880140080c1d561815801d0081116400507010f90010f50004a42850701000301d1701c8994201400509041c0561078841e0412900b110141e0b002550016000c003075078280c00e80c800101c8441c188040402d4004035949003032505c002803069190424908400d1420034450980e0800741c12040b8044241c4645001c61112310030160080d00c0e49483c200150580b03208840404821011082c1c0f52445849440a0144d035801d80e00641500d034211074000341e4000c1c20460031302c1c0c02500003020064030380703411480480d0701900707a040301141c291510020f020300d0400000c07107904210188001c40c5103281480c1c010004442c00703801c0700c01002c0450081 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 415262913 1250 415261663 415261681
    0x311010b040e0f060c0c030f0c010204030609030c0c081908090406051908010c030203070c080901020a080310050a14010c030f1e20010b1f030204080a0506061e010f08 73
    0x25003060050410400d0b002150025982c8100c108070a00c110b2203000001600540c910050741e500d4000310008500380403454004160a0704540785002c55513500388400400b0030088c1c024941074074080c5d26054142c04031800c14035004c103000d8021034060303030004941004030140380d04002c01c0503800c002550340b83c9c86040300203405021281e21813940440600d00f42c6807410280850f213002c68a00400170010514000400d400b680000c44001d80421a0302e42c581000c111038400520050300140305458000d00c075685d400090b60130031340340210110404841801142000442c0e28098420840412049900240001c12661804200070300300a10210342140c1e00380030b00065031070308564182c0c4281a032044130f402000844c00200c0d502d00b08500003106a800d51062080000034030024203100e650011141c0e0f4142402c05800c98801095405c10001554210074410070617418030520140c0003d041042c10080351011500b04d20440140c0c0400c400016a04042c00c0031038161141030400c07030f81e602c4042c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 415264163 1250 415262913 415262921
    0x10b07110603090c01020d113a03021824090619050d0b0609031b030309190602210306041d031201060f140409020c1f2901020604031101 60
    0x15802001c040b00740a01554080388218101400780c2c2211301c044260401120004041e000c151699084500760500b0700b00391260385140e20b198842e180c0c904400c200c001c4a005203600c1701c0c0c1d800081e8041110b651200004030910701245003107032154655007030888010400b61094100715558400024095000d40300d0b80b040d1945000c03a02e441200c0d041c14400058080c0d07000e11140c22034180b40c640c0b0019146411020341d40700c410b0281c002c0408000503850406095519480260700d0300c000d102c850201e9490b4401c5940d201051034186d45910301d4040c010b403404105001c18007000c22200003034050750002c101500e41c00082240c0101c0c0d1011078585844042d840304140a4041c0000aa040347c0d0400840d0114100ca410740e54000c2141c20141c41114800301e500d543c8589180d00f0041000020b105402504501032440c0036174452015010b440080e806002543d01a4151070343c5060703011594100b8600144000c20910540380c50369440001d4455900903c010184016100705080030202540 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 415265413 1250 415264163 415264193
    0x9090c03011109030318150f03060a05010306030506071d0d030215090a03050f0702010306090f0b0a050301020a05090409050c060a180609061e1e030b040b041503080d020c10020d0b0a0e010b07 84
    0x100e0955984200000d01006510844030140a40010712f0300041a5101e48607e0f002c4a412802420350f07625048000c843c1103500280344c4211940450741846559a0a8a04010340380f00790010003800540d540c1c501d101d10001009810103400400b100da0111b074220048489005041e40d0b841d5642c0454801a0014807882e0000300126107000b4130f801c0c1c240f07401d5120003002d800885150083c00c0d42c0d10300b01400d034850201c507035000034418010b028590400da00952a041e1055050740d580707500d00030124080d9080141c042c400202030031045030303800b03080440782806400303075262807003078039041c008064100d040e210300c44c0d0400b0050400320404144aa0000d0901d400a24000d5588d1400010010080d11903040030303606c141e24041c0040b0341441c140c0318002c284085143d00c4c000035481e585846100b0b1b08040001d0300d100e9000c00c00c0c840d51003418090001895130210006031500c103180314004c111402081c01d0fa001d401201800d12480050050017070454411a8861340e68114601d811840b60980071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 415266663 1250 415265413 415265449
    0x11803050433090603140705250f06060609290307051903050105030c040504020a0308070f0c06081510020705060a0318050304091103070807120b09090c03011109030318 74
    0x407a0b42d94000d500c003146100b280d07510ba0341808105c51452404910b010305a070b210300403032020010340010244415a10700c4580070088429420f01443d141c150b01080c400008550742e40c2e8400041c00004d420682403006801e100102d050404405994072a048411000c0c5030614540800010602d501c25011109558040029815040034080015015220a0013201d1203405074403101c803040e00741445118855500208032007411803070351301c0b07141c40c50303000c18010340e188081e130015003000c1001034540e50000c1c030035a500c2003081d10384007070800c040035a000710b80341c8035100300c1300208521b55002498005490301200d80a03a24400d01009600404d41d00d20f0711850030400080301414410088003a0080b500d0121091058004140d0000c00034071084404001281c00d100210340042c0c4108003960010041c010009400c20030003001034001d9504a56070326095000b00c80030003040c2401c0c0548128030b505006180c0c10152100006034480c0100100900c3c03480280c2400e80d42542c554a8161000c1050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 415267913 1250 415266663 415266749
    0x5062706240c0a030809161211060c0a1a06030c040b031f141006050d020901031e0524030a020d05030d050f010f1a030a020304021201020a050901020118030504 70
    0x80b08060b5100c440d40102500414242000500c0d03a04000c210130241d01c0d0300c03142c5400310a00b00035401c0038840134506e041c1d480046012001019481e2140103000c3c1d884c101c801031408a900345070498110945010303420b807000b4910107102042d1400501c40d541c840c01102c0101e5648070310310109181c030100700c0c1040985848200350f40c0c0c1209859100b004038403d101c030f0a81c43c541d9078032441d81c4114a548642d1001450030414042c1b03001c801e501415180e50145000f040c0079113500012084d00c0240740c0f82d410a0340ea510288111105000c540c85003514140c0c100300c29805030140080d0300d03029070080c003900440c41100704c01c08204042c4111a51003ca408080006003459000030a01c01024003c0300350381c400d580004540714031444c40c41c480f0901d40f2180c051031130381c41e60b1a0301c019400292089801a81010034003042402c280003808141159603251030b2030b403400400083c2034802c1e940494031103840307401414012a9001e4116401da8038000c00b00184204da01605181402040403541c0150b008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 415269163 1250 415267913 415267927
    0x9060f020a14040608010b0f0403050d2106080709020c010b03010221100b09101205090607170903030406020a09030b07120f0e0c0f0d05100506270624 66
    0x8658040c0c50701c0195030b0381d0307441440750090041c08248142e024400c04212804010060907036403030010078020391072060003400d03d9540d503501c6103010680080100412001d012001000c40100c01c000103103100e07144180030031450050f400385c071213032140592a41c0540026101184107406d400aa0340500040c00842d80c8410841540503600741c611004c00d00d15240f00b0224000f117000b5143d081c2600c190740d51701032400e2500000c100d0120080c030f4151003070010b001043d184c01220b41c0700d4940f094403810003a0055151200004005107400030040b403a10841c501448000c080c00400e03260b010f540504010313959000c00e0015561056550300003451a2004403c01030520f0b406000c00308901c150030000c0c030500f03800806142c1a9241401070380c0d61035210b401c1c540d07501d140c80340034090700e90b9010b0800510001c403515854201500c085100807015154424081e0604109a540300b0a00c2040350f00c1c02c21381210360003c6d1603c1005082c4600c51450100d101a081490400440481b15410f070b420740d940403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 415270413 1250 415269163 415269191
    0x40f0b0904050903132106051e1008150411091023031b04151e050d050316020a1d0f010e07020d14090316090e0a21030906 54
    0x8850000c460145007000040303210000d000043c1c07640e1094104061891a0a1032200d42c001122501009441840c824028022504600c102401200e4020214425082d044007210482c034024002d48500100a031040241140c003113001850404041307903080b03080d11682070090400311402c3c42d580c1d100d0081c01c1400201d00502d0180d80482e554140913242e8603130b41d014041c0781102202e83c800d42540000341031444140c2400095101c40a00800010710050000003456080040c8d40040014940071951660110000e40c0380c00024002101c21040443c8255030b025240d000e650380c0074100d40b080d002083c0c2159282031040c0040c02c5041c1d80c248803000440ca40815201c4140c88500068804a001255800c0d074082424072410301500280380100212600b1616000515004488014113108100c42580d0900c4040d08006108541501590410703c08070102c401c00b031910360350359000e4402c840c0014281c242c2c80d00141440b081c1084110380c1d085040d0081c020a003401000146000f1001c1c400304 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 415271663 1250 415270413 415270417
    0xf0f031704090222140d0b09100609060e0903031006260f0403080f04111002010603020a060c0201140a0909020a0e0d060e0106050109050f09071803080315040203060f060f040f0b 78
    0x340c0060611300700d950740c000001c21203400d08506600301ca0b030048841c010403020b10240e0341101140e4110750f03001003407245110440711541c00840c41162940c030104500c1c8014007400303401105c854051032950a160510030107114030313440340c0f405100c1120944662010644242d2009a014180302005c510701686d00c03041c550000c860440103d00c1140c085040c3e00341aa50a9100b00c0d0700440c404140040ca40030001200e016641e9141159291200480141c5804103000c004041c0d9440f21408035500e44005850010079004161126409008608201c1e61000c0000c040703d0343c9880040e034a00e503c00c012912040c4d81c10003260010050541841000820b5122003a803d5160008204045e1100011100d00ca10351146a034440301c000c030900e03900d250039032105412210398104040c04100780c00e88240300f041d45a001b511090404803c00a5602440500d88035521048508502c0c1d0b00e000c0d40002d0400d018440e0141c0140360100b0029401074032841150041d180450f44034004955814609400b5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 415272913 1250 415271663 415271707
    0xa0905070906260105011d0301020c010207122d031b0810050a030507330c0203010518100515030f1605030109020d06020f070b0c0706060f0f0317040902 67
    0x1031101c25000c210361550124890034080030b10080ea144d034600001111400040c07004803a01c240481000e0089075002d2004015035016a000540c0310007050604014511081d64180c0074041803c04501078031182c800c583c050903041885109420282070b10480040a2020190343c42026500a2100d841d401c841114030070502c820350250700585030002d0204040040c403006100d90300c1000c0c10f11641020150b100b030441c204004c0e401c40743c0801103120151351502e008040c04148800d43c0c10b01941020700819502105181209050750354406280b6a03554501006c1200d4641e21000f11310312100d02410035024103c01000c5131081040c02013903c0d1206800352466401c60610100054141010700442c0c541f107800800d06c030101d642989030f100203540000c000c60900001003150500090212801c5030280400800b8241c1f10f4001e450240200c5840b074101082e01c10300d0060030004004045072910a80c1e41c40243c900c0c807600070b280740840c3c90146400201d41d407400031502c40981e000d0401d1314085 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 415274163 1250 415272913 415272917
    0x903080402090108010213060503060d0501110d0509030703050405120c030f07091b0203070807060213060c1e080d230c0c1c021e0309090f090d030510050f0a0905070906 74
    0x200f80d90b00c5003554200c0c400c03003502100c1503126003000c00c482da000394095503020102074a031080e1882c00355195421514840106d810003030300828110302b044844c0c490780d076201e090346000314a841c070151005000c41c000d86c030425100d003404200801c48880306204a4481c604040c0031500640f010241050329200c507070085a0080e4607003501c43c20901e000b070300c0c0c04c040742d44550051490105661140c03201580122401c1d28026020402404c0c0f03400c151407803c000b88030f0f55803540509822460003a00e081c160b2545010004006031b500004074140c13108940f06001c1c02e0700009002d40066103160410100c3c1203004045102c0d440c10064103100c400001c0c9901310700401540c3c08000380300c17141c642030072030b40708401b005030f01462a20000110008042803485402c60440e414601040001034082c01f0490b18416880400c1040c4280700004206544000d060b0382414000b03860000c4140c0000801842450300c120760301c1d804001f050b01c4a04113032010b00032400041c8914130f040712002d8900c180e24402c0c1e40c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 415275413 1250 415274163 415274179
    0x221010b0c0c150c07090c110625051902031e120703180506090a030e0a06050a0f0e090405010c02070b07030c02040c230909010e060d060515061c0501050d0c270903080402 75
    0x484a0022034203521400c04803200440400400896100b00c4410882c41012f00c18200310802c06009440c23105c0080140380d03402580d9030001442401400c49940e84100c1c4442418070280070586411a407070340d8410414078000480c0740d1031261111581c2240c0f83c0260450180100b88101840f000c680c0d009180c2c0a52100c1d101d56814a00b44202d07031b4118401c000c000340d8103002034100180300b10070040b500600351501a404c40c1d07810000641314442528202c0b4169580c0074025842d0b80c05104190040c51a0b00e0703503500745000c0740c40c06003801c2c0c00071900030320442e43c032030f01020741c01d000745400040485140070510f8000c0c1d0320a844442603108625040c802c01e850b00c0001400511020414400c92019240c80c500390079035038518010b02000381c110250300d000d00050985c40d0f1030360341c050400500e0072007400307441401ca942d1680403500180c02245c02030802440a0000c1410700100c1c01c00c071006050101c16946a40c81d200ca140203440c08200c1281d0300f88051402419070220107240100c7c02210241 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 415276663 1250 415275413 415275437
    0x120602091903082506050906180106060509062203143003060406150302040311030606060f0f071e030323060d050703060221010b0c0c150c07090c 64
    0xc20202441d102c0100b000408000e00030441101c22021001444019403251460501d03a8451007a84d10440e5840f609a2052040181c250000e00e1200420a0003400030040203040500c010b001d880341c07115850142600192260a007040a0303801c1003181d0a0201d070108141c3c483c43d00086014421020001501c21410b51801c2100790181000e908440c00854602c403c0190b40e0307420704c54200800781507009130b60b90400105842c4000001c03071605400c0d500103035210308624150504d100500c0801d4005d52002c000c00c601900c401c0c0072030b100029211901601e51a003c0c0400400307100d0345400038009002d038070241038114003501300d0410030b0b44242c801340800700710440d46004410800902c1344140a8020120740c96052100700d48458a02071000c0d10f2506407261208030590b44400e401c0400354190000031300d802313504a00c4540c00340c6194800b19141c1354184c0b0402e6070b601000c0c0d580a204daa070102c0c080e0894503080040307445148111054840f6a6540e080100c0100b0a06200001054004900c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 415277913 1250 415276663 415276699
    0x30703020424080601030e010b030a060c120504020907180f03031e050319050903070209160806010519050319091103010c0e090a0c030e100b1f0813080412060209 71
    0x640802d400395940340300380d40e40c034401180030704181c2c40440182d540e0f400e0150b209407014041d600d041c0d4002c21000c142c80c1c05003603004005039030031503d14000520f040c06010050b51108111782c1c00c508d0902d494050343d904005c200d0401411648240d00c9544840400000c00d40c009062090040e094944104440008c8a0070340d140d210850b100003044007a400440c045c01e285030300060308400e00c0f10807139041c0f40941d408511100c00c1a02c030002080070b000900d4034010303803050350168007140a1074010308002c44940742042e4002c6140c10001400004400188000c120219072010082203131014051900c543c2000c10640d415505030034043d500f0407007545412400f841d0390100f00c10f0050042462640ca110360b041c000d00ca1b000308c517801c2644a0b160f000654070100851001d54641c902c000409010240400c244003003802103082a01303541c0400e4280e081c2e04819200d600141076400f04034295914a4421024031407030300226100f0b90440400020b12200d40e020742404842030329000c00c0b0184500d60 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 415279163 1250 415277913 415277969
    0x90601020f330c190212040b0c011104120f06090215070c0608010b0d09050a0c03150c02010507050412032d122f07050106090209130b031e03040801020307030204 71
    0x100400040303041006050601e500010720903c000c1c1171050707451422401c4980400d80d807003035024883d0908003060001074000300303109a041580400e00c0241c40c0074a044201402134034078450103003401440c0146401130004c0c5030004503010354001c000e103100c12500310740100c4c150400c42040d1901c0d40d8000012629031301504003107059030107040d400b07800c2c4a02140710310043c01017454221a0341c000c0c0091a40065a40500d60000d1442404134114112400c081718048540c2146c00324110381c1884140b02010350440200d4087d6014a4035200c10307000c2a0400342d803440800d4031241c5421401da80c0d919003d010503d601c2c14016019514202d405428200b00c10a0320700011004082c4450b4601c01ca81120700c0c40c005001003911451003d00f400500d84405084518036401850300607000903e400207860090442c84002a0601d02080310b1081103020a55070010f814080902d441c1070a80018600010403e0714018466032000755985e02e003464005010790814820404d0f02e01c8481c801940013000610 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 415280413 1250 415279163 415279171
    0x1508250c1e08030a0e030c0a0f02090c04051e01170c300c2805120705030906010311060d0e160509090c0913080a3506090601020f33 58
    0x400d50f04544614120f00024030814201d02030701e200400020000903018008042410f025805008201006c2e0040c031812402c010b10050840d1b90400092113559640c02c06d480041310603910860480c1e00b0f582c0140c0b6a1182040d01c01c004021141c100701480b07800800620308400303401c00341041350b445406078400d1400100c070345561035820080011414a00b62010341105049150400621034100d070300c171b013911501d045194000600014120140c50786840880342c205c034107442d0040c90341c44c3c0301100c15190001808001c0408000350181c002540d9000192162110a07600c10005d0b00910384080e9694004690500200b5038a80e100103010b181001c00c1ca0320811000b07026051442c07811041040c88200245441b0403440c0004004000c10f442402503d44622140c854403260005496070000800d034549103051500340203100c40e448540e10103883d54014009130b421900680342c940c010b0b03045c54007041d0703000f800b846404880e522244c0e01e0740070814204103c4607000003c001c10800d015000750201c3d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 415281663 1250 415280413 415280423
    0x70503010b0f09071403010906030b0f06030a03030b0321040305010b030312130305070606080f0705060f0904110403061b0e090f181c0c17041508250c1e 67
    0x6042c0002c900b411001c407540b1204a1a14030780c80a00707070401000c150800c0e040446482ea81784010700030000d0300d9000039040f010303582202c20340d03103000340000341d55003841a402010541c6568000c049a2010400c41619810810000c0440c1000180d0102170b41c01c04d200c26107256080c1201116071341000b0080351080c5165020b1652681d031451010050001141340843c208a420400718010802600c540f00c0502881d8001d80805001e0811481c5400325a420140c891101005061804401202111000c4500351004501203000d580c034404540583d81c0042d01244c01d0004650380b0100c0c40b158403103414015247d0b484151940780500c0140706e800c4070010001040c03d00812051020150210341c002115030803600c032915481011420441e01c480c2071008150203059100c2000328650044454541980320036050503d401c6a41021150b40b9101e40103006601001c603840340c0416081910f00c003030019060354070702ca007160001c110780c1c0185400e803000b09000d00c50002900c100103440c0c020581203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 415282913 1250 415281663 415281679
    0xe120903070b0f09120c03031201031b0e1602010f0c0c05120301080703170d0906061805100b0c10051501030b100206011401020c09100617070c030302210a0e070503010b 74
    0x80c1c405c0c8018030284142c424000e10951091114940c0c7c1040248000c1040c130b1a07100c0c040d40b46203459000618040200e441c680400c0310207010106e10b10001d242d111130610000f036254402503005030b00506a01e0501705246080445081200e0380200c008890706100d14100d80d400d0388400340d80d007150f000078000e250264010b400c007040840c070211410044000b503c08210310b404604c1c401c0302c2c00c40e16000e00c01c6131050707100e01c3d04100d4103146482c4070703a544400b80740c24415840c1c0b5203002e201040b098040c00c1c5100f40040348520421408000200f41d051034481c081180e803d080100c252200101c000f0240041d0038004450028208007058103034a51043d0014030142e428819042d004041c80d28141e411885401d02c80b0031999107a2005074003811b0210001012142000e00c018140c0780340c0440103034407201d40822300c074201e540400541c04098152a0040e150580754554041448030340ea6145020740a1b2400d105900c03490358000303030802c03110b48226001281d482c000e0500b1fa4066490b815440294 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 415284163 1250 415282913 415282927
    0xf061207050f010323012603030604050c040b07050f10060e040b070e060d020c10051308030702011b03050a0b221d01050f0a0c020705090a0e010e120903070b0f 70
    0x7002046160642e0305040128106202400540c02011000d503180085400f40004002034901c0d4454480c4140591492002217444c603440c465407440098030b098007540d51507002805005001c0c0a440281c80070030342c13036551076095042c81750340d942030302042e40148e000d0a1006c901c50140e0703100d208102e48048080c0040e50f900c03500d480f40561801005001445146402c1c20559980c44004000c0d0703403280d25005132645199881d06103460784450f942040181b502d400e10484500a039240054550b0002101e650399690090490141c081032070b10841543c01801c076034550b985c05402052060304442010001c000c2e801c42000030101c90044046143c1015610f00c00740c0c0022600070b4010711140e10724580002013192169400c44204a903000d0003c2c04003400c0c40030403004c501910008401e184001c00b0014201800684c0e0144050f02c1c60003400e0796404001c21081080d0072050864450509650641e08914005aa10b40c001b0314490f20078042c403280415890781d454203031100c405030000c4640c20710403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 415285413 1250 415284163 415284169
    0x1501080106081f4e06140a051f0f050d050114070201021b01140601030f0914070512061005040c05070b100311100c03180509010305060f06120705 64
    0x8064550600c4400c0a40c1e480b41a60480c00c4540007031000ea01d5011360004803000f80040e18421445250510079828400c0ca000901d9143c088140030081e41801200340c410300e0a84001d00345107065207040750381e5008000c41414151301581c070940c207072a01c076020403100052004144016000350284203190a1050140d418101d420304140352040e000000c000c2118070035481020307811661800142c0d00040c2020325200b02c0e0102611400000e8028052840510b4244003031440040c180ba0400d50346400540070742019400c4031447c2e5802640c403404034500000816201c1089004080c050b1407900303c0310300180790000d403091103185540c01f118603080c18201008060806072420b00c0422206018160200e0340410020f0300503d880c0000c00070103031440c43e045010108034030740548100203840780781c2d001580246074650300b00d42c035243c6002c0c801c5800020403103010b055001550450126000031040080014015001e40020f03000100c45a490104011903070245d000c03d242150040b00c01003226003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 415286663 1250 415285413 415285427
    0x609120515071b0c08120403031d060912010b09061009030809062206030606050406020d2f030c0c0409080a1202040504020c100f0c09030f140a0311061501080106 71
    0x60101d2414021221074140d01080d00030f83d550080d81da0b214050400c00c140482003081c0c800b6034103000700b00340c142480c589016240150381d01020202950503a0b2500985d0b4441045546045005000380795600030702c1d85181c02031001c0481c0500814070080410054034242c1904840c0e08913554403081d042d4210360b20414030380c1102012541050003407040104a5081090445401c151b2044900310305190000090503100380740d00000c02d2002c01c020512945030f022602e011074000c50b0920400e0301c80080020715405503006100b000c403003200815040c114502100030a00368021400b15421098031000300701c201c07002410020320500f0100891200c15001d050088040c010075040142400d0f40c40c004201a03034040c4070744448540200d56214001c00f8148980580c02100c89002c1141200038140034044040c02e010150042100400c4002000803078410150004072030760a8840c410309614024046402d1099085420b02480d400501c50011883d0715164105050750b4603401c0303034640001665a4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 415287769 1106 415286663 415286671
    0x207050109060f0806120f03120a050c040612061211091509241005040e0f0402060a200717070b0405030307060213090504050303010609120515 63
    0x35901140b019003003406401e0401d0192142d01c0050594a440f190302d10341c500ca200d421f41c21648000c800f8115034003a03042c071845640c9600000f001510821210081c007104240820402c50340314000100740c5440304800001c03025165540003814120205054401103407142c06180c690820100055000251116890100d21180b0006401c0c0d00081c12100b1008007032000c050040c140402075050010004151981c0a07404480142080e00240708201504d14000001111072865501d03061165034002c00e4907140001110090304e04420001e40a6a61403861425908a0310200840405050f0b18801c280031200c12405080c60104d4503001803003120028001006161000820ba44149a01c128003588820b00100f40d4000000c1a5001844035820b000501080c42800300c0203605948003607030340005140d199040e400014440d804020300039030001900d00c40b00c8000034242500 = true := by decide +kernel

theorem cover : BRFrame.Cov 415107913 415287769 := by
  have h0 := BRFrame.cov_init 415107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 415107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 415107913 ≤ n) (h2 : n < 415287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
