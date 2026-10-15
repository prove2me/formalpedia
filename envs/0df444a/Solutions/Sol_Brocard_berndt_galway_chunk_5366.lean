-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5366
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:38:04.185076+00:00
-- url     : https://prove2.me/submissions/7b40b947-e747-4d98-9f83-42090a872ea5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 964928057 ≤ n < 965107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 964929307 1250 964928057 964928077
    0xf0603090203012307080c0315061c0630111c02300619091703100608071106180f060412110c09010605070309080706050304170a14 58
    0x80c0c0c0709080401341840c0841442c1201c2c882c008105072034284002404580e01800004041c0b00510501003024201c0050f100c1c40319064034030301d8580180c240c462000d0360000761030907400d920303010021a5041f123500c54a40d451840c1d0f242120000c1600540b02000f040b100d00140410042c2d40c000c00840c607010504108400580b041942c2c0c1c0e0280e500003c46554079140c04080000f80c68400d4980c02408001d1452005c0288015000c10302e00b02940e06400c0110740d1001203415036446000c82041019081e503014401c15a8a0070348a1034100c411048450b8140035003004544d10307600040740d2600c02c80d10004400c000c180a8a2280c41d945000002001c4680c0c2d024918040c150581c14500010882d43d48034502030070180d1000403400f00702514181902c41320021540001c901c1e031440d5110290300da41181c009203803030b40c0c3c0c41e0348508040310a034110742c00449040c02000d030001410365100d4055030140d0300030924103401041462288113944075041ca21000310310760031064044107008c6000342c038800070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 964930557 1250 964929307 964929311
    0x181106090303040b040605070614090a32160506070c05060d060b0a17010b090307030b06030a240b01032c1009230a031e0210062c010f060309020301 65
    0xf0300d554104c24160015044013000a00208084c0184500381c00f0b5000c0488031043c0640300380c00c0a0465944a41c2480809400c80c0c845038001c2d1300300c850131014009030650300d07082e03286080c0c5103890311a11410170750b0030451080400072003c54103103420401c0307480e0a5031100d050000103103400180031850300241c200100c440c0c0c2e15240041c0380d440341002044901410f5440301c440c102c50420504d018081a080100c0d0000f0038072500e90261030000d549801d49402880c44a00342c1d0352a400240381816440e0010a4140220768552035810700580391649082084428071044101e003004500300e0765080c15440c500e4800002c03426100ea09000c0d001c40140230001695003484440c41c1c40801d60710081d400700c40c45200303890100441052801d0090f080d40e0303490040c1200c1c00c19031720001c01c517141c1c0f400c0c0c0b0115005801c4441080c10300070040d848600c0c00300c070b0f03080c0b003103070b5460b0355000c0054010342440b03400c6c0020030407844540a007400c07160b060780c0000030300328001030501c48100c004190006c0201e07003640d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 964931807 1250 964930557 964930559
    0x12030908030a0902030106090e10020702031e03030912031509040201120204171c2c030109140d030b0603010612090b040f031b02010e01081f0807050418110609030304 73
    0x48403140118071440c150000421041d006105142c01c4402c0c50740540303180740c03400e05042c0104102140500d1108220400540c03550020b000290901070f55000c0380f0707801c40c201402c0541900021020350300c0341c1049010741d18405c00040c40d840c410711003182c6949840f1001070151602c1e00e4400c04058100d0b0040c90000c00003000c008003102242c0c8260400d1132103c1d42e1103141000685d0800c4094040c071302e9030901600700a4800001b400c0c400d0411040350300143c440c82d0040180900720b859201c0500020000c0c4440040350078407200f4a401468101d44500403c0405040b141c00703800340c2c4501e9800030b850607146070720303004040b80e85200c10b410343c0150741c4e1940e4044020030308141b0110300490191002c814a1a0540340240a4640d440c1d0320341c070313241511000140540e800040740340855a00303003070204243c0e840c910b60001300c010400415884031400240801d01800000fa0304007035a400b0303613040244421400041d040c2011600000340108103c0c40000c4443c102000901032010014085034205 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 964933057 1250 964931807 964931813
    0x60c0219030f26090f250312020f1b011103070b011509051305060a0608090a0308041e03020c01320702040209060301030f060f1b08060a0801060f0e100b0403120309 72
    0x402804e40c0d8061055000d0404a50140f605120404c00318011480150001c02078580209460700e840c800a884240c940c400c2c1c1010b180240000c81045030070a050b9901240341d4000950b081101120399030002c1c0610312143e480034400001c407581103070040c0b42805d07168a4151140304503000b41550104108a03c2d80000362620360150b100000ac85148011403039141003010f0100c40842540104200280310080c4a4100000309034149059010701c5d048e0416516414140064150740540e034190075020070103181070540c0807414103e03842090b41e403c5c4d503c402c5880030b0740010801484040102222049055020b542c0c038000309010b40c80a400903083c401705000050064109074800d4460b400c40030004401c100085c410001c25003001e84040040c004610340c40000c140760460150140320240c40421900d66540703941c44000e0001000030302c1140c0c1c440503030030a4002c1520603401d954112502264102c046003014400740c1d20091704603401c083c555124070310b0782d0030a08204003c0c9940d0301803030408 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 964934307 1250 964933057 964933127
    0x6190c080411280b070b07030603031407050111040b120f07090e13050609060906130b012112021e070501020a1704150309021f081503010b030604060c0219030f 70
    0x4c0984003075064807a800c50400c2e9030f602000a103044209445c1030424800241c100b10070706101045000010307103602c82c51808900504141351481d110b480e010600060401c0b5040003803614100015207601c050302e81040700c8869800588144012604012080c0075003004040c840b940211104443c0b841a550303a203078035041c0703001030352a900319402840030070800c40750402007190081200c0000b0a203014464451408800c0103000300001c8006010300c008400c0c41060300d16640740d810208219080001d851f010756a04e01c544050b903100c1c5602c0b4906000d02d0804034000d8122031041c0c016028022a5580e01120054507d2900c410780c00103000110700c0a080d011906006055a1000600308041d80100a00040321070a13035005078902020292007260b01611700342c2c0110180041d001c2800c00b010001c4d000d400b0700441a038040c42440c08200a1241c00d4201d036190515540a5880390007400c2d00400c41c0041120000d80072412034410f207400288103036290340b682c1c2030040200c00748110b04403001d44 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 964935557 1250 964934307 964934309
    0x1e11040312030c0f18180209031614040204031106030612010906151211010806030a05060415060b0a020303040213090519020102010f0213150c0506190c08041128 71
    0x70000ba912528421103d0300905590340c4801c00381414042260001000c1104403160b01aa0311080310f08401444e01d54481d070142c84c03d5090060913540766208a07071010b5010300c414408c1e10a0384085107048405400d0a02c07c5a042d42d40140d0008140c00882e0144091a400980000c1e049a040f1503180d02c83e69080c41048000c51003140041b505000c030880303041040c0d565402c4082d4440e0b02e2400400021613803d095600280c00b070030200344a5035140c2c0081c1c00c02014160217031580c00303030a0030081003040c0303010001e00c41c5500ca4010000d854032142200784901032240f100015902c03c002080252503c03038141c0305401951200071904011642c0c83e5410300014103401d02c10389882800c075508568082c0a002211450721404609000502c00c5e03e00358001d02c1c1c070030b21515100f00300343c81c0b4403d48588046088550001c040300e507142080449243d041081003a00c4042030b10304045640310074410350700c0394001d50b041158001d0000c10340d01000580340030a00f12038104084c5580303c240d0842c1c080c00c400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 964936807 1250 964935557 964935593
    0x70c03060c03050711210918160207030209010b161e150507200304080304170705041407081302041a01080f0105030a03230f040503101e110403 63
    0x21840100107800901510710140801d01030000b119103104028070002a00c488070888104150350514aa011039411840b07002e250703941260288001c101c02c01e1107107598500442041c1c0e40800a0b18452030b0898844c482404020b5000c101c43c1c0040169261020280500000c00a04410801003a503100c147d6842846510855241401270310800d1000a4403450701d00d040000040c090f503c0d02c548024813135030340714218841030a685c1d4220a16940c0800a85000c1d2601d1030480c0e07503468a5803882500c204031b443d061001840f864002040a041a0254034908030b003070000d03d461500c91580035200010028816a50420384242c4840540c1d20741c003500307900118200110380300350521800100010703802005a00404c24900c0104925240000d0450800e50180751a24846c80203c030600c0b103001099444002c06240402c02e202d00d4144000240b0480e28110200d46d0322080301c030400c5050b01c0e00c00780000700c40340400d40750b07199010580c0c00c18072101c2101c0c080b542c90140c4070b59401418201490202d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 964938057 1250 964936807 964936811
    0xf0f03020405041d010b150a0f021009050a0209070201020f031506191206080c0a09180f080318010b130c020a0813080606090903030411010306120f051b010c17070c0306 74
    0x70144080d03003807103a414031b038100b581c0410341c0d051070b001440750510031403c3c4a000c00542c03d8110860038406d1102e014180e4003140140311041031828841c0c2c1d01d041080e000c1e0701c2400240c0100f205a40144202c80e405c413492409581542c0e03540c110440703042215090282c0103401089810401890003c02e0351b0384c000c65071290703403402c19003a0401d403c40701c0301d4100030421741c060f00040410756a255010303001c688160202180c40c0019000300044c1c4107000e9401007104004100c401d04021080c03000e0342c4150120b13895010940c030b00043d80e0303090b034800a0406401c07812030078070421400070741e401070340c1c180c8420700403902b20448940d1010029449880c150014107000481403004000030700c0740542052007186d405042d820406040c40d164800604020042004000c1801c0142d01a800100007071010703070b00c15541a8150300342201424140c00b0216124000c1d0a000b0744030b480300301c0307046d0818101a51528450711556440d8030019000b40c984180c40c5206010700780009907828ac6640243d40b0903200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 964939307 1250 964938057 964938101
    0x9040b090606040c0801090b1c110117040f0b0a020f0409050604060e04050d1b0206040305030904152105010f020a05071b050f04020702010c080a091d04030f0f0302040504 75
    0x559418450040e10440c800c1c0d040060900d010b80e40580d01c43d05491045500140311101c00c800540c120902c1c0300daa00c40042002601020b0011f08ac02000c0100020b8946007000c20410601044a500445d00248604144002d8030003050004010030790150401c40010b18052101030411600c2c0c02a500404040e9103840422060b818180038510040c0010146102103040c60f0303640030b03125103203c080c403801c104041c19a00c0d50040b010304000c0300d058000e801e0030b0340c868403030900b03580302e6000b106054000d82c207160307412064141c0303400a00100c030030304442c0ea0744210b02c00a070003081c1047c4140640b019901e410010312803007443d200030020b000b134039242c0907030311040d51030103660545240d0103030701050811490402054a80714007603286001c045070016a601041e02c0160b5420992203800b0f880302402081c0707121500d4002c3d510106642d80200d5200c034a5250361802c090b0500f003201d004000a20748000211218046c2c5600e003080010f50030054106526900401c040300c980303881d01c083e11010090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 964940557 1250 964939307 964939321
    0x6030c0801020307090b0a050409023106140901020705090906010812090102060a0f0912050c010609200a020712080d05091b090c2709090a030e1e09040b 67
    0x12401802648025800c520703040300c000e000c06030b41344100c440b0fa07603000955440c0c051140342200c01034500c0c0042191107049004811002030031043d403034260410114004000f0f1041e2001e54003c0b02c0c12a6a10305905400700d80f180042c1e00613480d02810f520505c0400305079a40d4101c00c291084004c00e00600c110343c5041030a03441c0c640d50b600083ea80c40e00412208800c1e0b64081107080c2c0c4101c001c40c0118011403000302e8a8001c21080e10090040c2c900000d02c40005580140207201c50b1859000a12040f611054200b0403100000c94404c1036603843c10048040d54100e0000e0400380322140191580c0c10b42c0d8101c0c3d50301c000e100c10012a00050006800408100103100b000e4000e81240c005050010440340450540301d05c066040d449400312000044103610410200e803190114111011414030030380464041400002420a2150742e980c000512880800584661095055030b6040041d403060b000b070004030311907200d401c031200064006178a1503444412800d40610b00c5526182c480f86840e00c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 964941807 1250 964940557 964940573
    0x2030601090b180702060c07080d0509251d040f021507030f0f0c0219210b1315050603010603080703080a0c020304080304180e012d0b10080a15090603 66
    0x140f114110a00704001d000e40e060b40001c079103901c114126201d590740c0e41c05040640700d5002d590b05511001d030404041240c031500204034bd0300c00c4940c84034811a00349603180500c074400b5403030082e1250589514083e06000b840080059040b50180001040750080d0341c010442c4040d6011080d0785041e40000d04108041d4082c0d03019074010b40620780640f00c40250324004080361468000680300c3c95008400c0302601e00618840ca00810303d1100030a100300805000320305c002c50092065550a130510002213050211150f0140d00c142d100c185003003007030b645120703020040401500c4daa826658840e00480040e44c44401403401c40e000b42c44800c054039001e21007806641d0510044001c6420604c0100040440001034400390746004500c008644800c403900b80007040e80c4116030451b9800c1c521103e4010705c640440d0b2a4100403c81c3c56500095004080ca05681c94040102d40000414000210061007140c003182c000b05008008941c6a032110600000900d4540000c2c00840e641c1d40e08208100c1c0700 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 964943057 1250 964941807 964941829
    0x414100f1b230a031d0901050f040b040c02210c0303042d0303050f070e030c1c0503030a14010e01080a080a03140a0e0d03090b060d170f120c090f06090d02030601090b 73
    0x342c1c030340903243c205d41c004601d180c20103100312400b41c014203101d040c0310f96460b00440e03110a8047c2042003190b1001038000d40c3c1c2d0501c83c0010b06034104400440034103020325030031102241002402585107844980e07039044400c50107607210901e101c1669060544110019a00d11740c18042e039400b041d40d0a00703014091881401034816001d001340c189062420b514045619040c0c1d0310111023020401900300c0038484050680007000742180800801c00c103030020399a01c0010038006062000505a0b00c400c2c00c0603902c4400c0c001d456075580300c1901480014070b03000081000902920b0b0200703000742d0810501102484c2600c12541c0d481c1c0301e0921300a4880b0421117224100910315062200c0b488d240c03101d11100d10b018291034003c1443d820010700b800044a00b030001c00d07001c0b103240d6a4078403184d1000440f9801c6a00c2c400c4264405401281c1d000b03158106a503040040200f00342c5001c807182e000c00c20b103940840002c0f0f8011030720010003000760342d091041078001d0400c0c0e000481c401c004141000a86641 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 964944307 1250 964943057 964943087
    0x2070f09050f0c0d020906041d0f090c150909071205160c080306061e030609070e03100f0e070b131208030a0515060414100f1b230a03 59
    0x1400003000300100400b10229041450500f100b80d4a01026409501034460300c3c02c00358028200040004200e16107000b680c1101107440c035403190076260034244502c5a901074031502c1c041e40c8008528000703460034401000900341c802c0700740f6241001050104103401c4085441c100450104d42a20360f4800060182d240d12120b40d242c2030308100034180001d012490362400c041d2420b10040001011a2504421240602c40c0141c0041c9182c545402c08856079100700c031024001c1c902d40c40070940e558061414a070480d80020040e0482194030803403c0010300a403800900321548450008000d42800e002c0c403000707480c01c0801107640307140940c0740c80c0d0060782a612400f00f00d041c80d040503010814110a898203d10818804138068070b0f41034006044403010000300b0343c0081c0c00600005c8000030115454030304007003619802c0d0700410428058880341182c0c9045408906034440c00c964086000b500b10324528441e1108030128100c2e40507051a00a40740e1804040c1d500140300f0340181600000c40e00e61b4141 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 964945557 1250 964944307 964944311
    0xc11010c0203090307090f02040f0f1404020a21062106060e1312032009120604110f0a2408150a0608190504080a0f0504050306130c09050702070f09 65
    0x584200425074171001440350000d4541c2e034400b0040c1441440d0119001891074031280c0085d10f858980380c0101e002d0500c2030305c02000008036860140d05240c02500c20701c114946130074080c040a038584009202c00e841d03030b201d8420b554020124100c811041d480800d05104003164580d02d445290900c100c8a45412100064401b441041403c0792100586010107901000010754540602015070180c0012250001022040e12008d01400061800b034500f09800b1110029000c1640d1141900d80009480182410f0105260026142007003005010b03084000f8040c0f80d1030f10703902c0b014a8a04045401c98030b0108000802400340240d01c503200340c0d00050106211a000000000010102c1c24240b10703a506210a07040010710307424501d107116086074041e40741849035107170501e007450b551790141100c2808240c2c20f1100440e035074410f4080d01d058450180c028905d03034030b900501d20304400c4d0010045600349095800402d001f0301301e00a0500030b10f4550028419681000c1c10800017203655004450320354 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 964946807 1250 964945557 964945567
    0xf0301090519140703051f1e020c0a02060c0309010905010906020a11060d020a11061b040b0702030307020607031d011103090f010905060a1205250f020c040c11010c0203 74
    0x22004603100c0c0300040c019500351844107040c500360100e4200200748035003d004001c000000d020000c1034040c500c1e50442c00112402030f41c00030320402c940308d01042e1b0000c200841c2c190070307142d0000ea00400c11602c614044070a103000c9603001480640c000923a101045e000461b4203001960850352000c0603080900300407214070f0801d10029641d840d48803018200101c5d542d0750b0599501d400c01114400c40c07100409541e00c00342144082c1100480c50700b00501c81c400c00300041c03041440c01d1582200c2800c500c00716480c041c5800004401604440070690f8036001c01c05c03001d030042c0d44010041c840355201c1d450348409003240d8030000c1804e011a0b441c1a06000000c0301c1d00124030b401004640c3c80841c1190000010018200120b0750181a5007060760401e000180b5084c1031078000320304600d40342030401d05208a80d1a0f0920200c50a000d008410a0a100743c00500c4450b002c0d1112496a1025204035115124510001002d442c1c1045244010400300d1021452440087c0070f0345e0b94201d4180011b601d49 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 964948057 1250 964946807 964946813
    0x30d061a19030218060a030c0f020c18100f150906031505120c09011403010b100c260301171524031509010c1116061b0215090f030109 59
    0x1d41002441c0104250340041e0729661007520300155010054043e20041d125480c100300a401017803c80900e00101e07400001d422035107440020031000b444805040c3c51080942c12050080003200505072000981c80b0300c0c40815100d08000035907008200a000d03a81c130342940540054503580180e049002058100401c02140c020002000030803500305031010604882c0000c00541000c1c41c90061300c5d84015030100002d00381e50040006206508214001c04c222440e240400c03801c5031061940340003241c2c101001e240810100b0381d0043e180b15140c10520b25503d0300c008003244170752090300b182c9082000742c40c6005040104108590720301c1c050b2044194a81040307040050b0341100540080083e0001c8040c5145a450900200b010308620040315142c070308002c0069401380c8252000030700000c40305007800e1000a400504100306003640299240d42c5401c0a034100c0344058400440303081c40381007508100c01078982c04010500c040100e4900c6845000d82c4003080380802400c1c0c2428801c1e0b061506c07030408 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 964949307 1250 964948057 964948087
    0xd0201061a090924040c26040b04081c090f150e06010e0903090a14011107140904030302040503160302040e070b220e0f0a0f0e030904110c030d061a 65
    0x4c00c5091400c100100e071102c0002d426103001c00c4c0102c2c1c1107801c11041c800ca4980100d410101022024030075800b00021445c6144003050483e0007500c802c031041c001c50040380100c4002c015456a40210410b00c00982190000361a9041000c0b5a001c584a02d44400c0c0425801800c42c61200000700b40711a04200b00b1080d0b0b07801060088216040f00b1202259802a0800840344c2e69103001d06801c4d101030341d85a410800130902c1021602041c6000e01e503910600d404119036040d5400d02d00344c600707920400130512242840080044041c95070802001c201e9503070402c03250982001400700040c3e440e055106000503a003c01e68084600e41c0810000d002e640c81503802c1d1401c88800740800940001c603d462600d107490315a00801101099006002c0c00d500207101461043c102080140040510003e0b01011100b112400d481207800a000b07510007442c080d0445103048440c1c240e03117414841c206149600b164040c3d008003180f55070302c0104108400d001c1d25414218401c110080d41054181040550703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 964950557 1250 964949307 964949311
    0x6090f01080603070f08060411090c19021e0f010b0618060d020d0608030403060e070609210c0f06170103020a0605030a0906061d250c0809030d0201061a0909 69
    0xc140034804002a465071030401c009401010048210b141c0380707695080903901c402c0282c0d01030b5040c00300340401e1040c070300b00020700e00e000d1181451103a2400040042001c40c080044500300c0450140308032400c1d1402c55200c0b9001305400d514064100c186000d4000350856407040040ea01a91050203120444600701c0d46843c14940d0550320390355207980d0801e68100078880c6c0c1111200e041c1c43d1207004500340a0000291003235034810300040102c15602480e4551f141064420040000c6a980041c031419441c0745000540c04040c25036501c2401d2a5038910101449a4100580b0031030b51407030400c074541c2d00c2001d0303200103010344242c000d5030350558021400c010954014401030060000200c3c415161550044a0564010761b0800c0442d48500b000c141200e000c4c41e4520440c00f600002c14642c00c49854907181c900c1d40b1b0b80005804488450090b00c605a0b076840039940e00f00e043c841c003165900d050190461000056000061241c2009054603481170456801441c4000a10030380319030b40c90b0703801d00c55 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 964951807 1250 964950557 964950559
    0x3030f030b040e0109050303040302060a020403120f030e0706020c0a050619080741120403110f1609060602060c0d1e02120a0e0a030c08030714031303080606090f 71
    0x1003038481d10319000c034014005100004259610742075060080c40320120103035001da4825400d640b09600c031110500260700070760102901859001c0400401c0a014030002c01c10344071a41401b140c03a10720050240e0404076203a101e400941c200d85a41c94041c540740400d18041e210840341541071480070b030702801c40c0c0441c400b0030006005841000c649554020181c00b00341c040c1c500a2526441c0c0940d29010181107000002041c608072216208081c02098061700d112100d00c004c50345030756449072401c81e10690b0303980c1400c240e4010040191340100f014080e0b16020b00101010441e035a18241155084400d1903101e90b00b190007520a000818056270100c1d8030302c410350100410744400807a020003103c0e20340c0c140a03811502c000b6000320b0384100402c8561003861581d004000002c0c00000d41c64070380c40e04820040000f40069007050010b42e01c0300185070030017a9442c24040e00455480288544e50041c1d800c60441004100e0344020198840200c42c0e0000080d0fa110381401c1107040800c2481041542c49 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 964953057 1250 964951807 964951811
    0xb040b16050a200703140c03011b0215190903051b21070317011502070504020910080907050301020406020f07051c0f151803090e06090c130b0d05011e03030f03 70
    0x225140350080000c0750146801c036600f0310304072000746c000f10399806000710103d000b54203010700081c203103440d403540410500103070b0041c002401c4082c002c0001010014513000240002071008800340d1080d1081403035540c801e46403142c1d200c041e0743c81c03040301c6101c841c044181c562002c2c081901c0d090415030a0003a0f9510020040d0b250445031400380c0e0018142c0600002021580c03000180031403010980b04000782c4a5000d43c0c014a8a039030501041e8444c442c80a60004a0f03140360300e044511840e0540d40c05909401900d0250341c0b5080080d00b664081d91028005a015808124192900317010a00050000b22000c020300008110032211b01c1042c108080c0652045100000c10b01001140c210421114000108000f014241c0390005550804400360001a690f020104904421910f160b010b488014018071140d940c1d550440055484006090002d4554203400250a070340a0050000030644800200f002c0d03050907030700c15042103010000740d50704600d0f61040000c642c0188a01e50480254a40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 964954307 1250 964953057 964953107
    0x50d0f03051602090a0507110601030c060c1b0905060a0b030106020c041107050f06090f010b090a11070606030f060e190b06150301030b090f0f0705060a03090b040b16050a 75
    0x2803180c0c2c481c030181d8041d400c02000001c020700030b0000e41c04144110b503691101c451000b409040c403940c9003404d0200a03e4200b07210380070306c0428044e41800214911840c042c0411010200c921300c21240039500c65000c140d02c0310103000981c81d0050824000d003400110741170070744d031414078000d580e00c040c07500c494062079807034402d000701070300003400c46a4040d0440c044130785040601e0380b02c694070b40c8200c500800d14003034400030440404060086400000006180a4031342d01c5540108006086803824480c5000c0f0030003212000034120300035080114095052109008154280101a280022002d003002e4101c14908204000c1c1089000d101e0350701308245040035603581c0302040c881018050b04240e041c1021000000300184012100d10840c40740c41a2843d080c407224006032384401d507132000b143c20b401c402410320107810100301400821490303240114841805440e0b840c41030105450503200ba080c6e18040002d03061205000d95480c0c0300c00d19005140841c5e42100406004500e0641d0b1041d8842d000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 964955557 1250 964954307 964954327
    0x2a0c05010e0d0c3b091228050c0f0c01020d0305091506030712150c03061d041b0303030c0f18050402030408090303120108010b0d17030603010e0106060c020406050d0f0305 75
    0x2414000c581d03134100f8041d410100651040c210b00c04580d0b034407080c81440604d400d00c4002c841a50080041c0d413401c0250202110079120320521000716410401c0320500c1003060004003003000e41401c140260282c450000100002400c04660f4400c500c180b5041c0401e2001c168000103002d00c03056a42010b90b1890380741d020000e42003071030780e500803240c0903c040c5505041c4040800f00d00d145010a00c400c02550400c6c140580c2914a20304c038801c901450000c2008145200080701c5a000c2e108240e1081c00b0020302c00000e000c14556002038002075902d281c144c081640018140e1114291030403c96000e42d4500280c202c0030805005441c00380e5008004281002161016600c0c0000010182da8646100300340d03001c0224001d2244a0f081d600300304e681031081c01c151580c0b11106412400010075213490000203003481e8000f52066405641c2c0e0b50070170707550800a00c10000500000d1b40c0303101c250155801004152341a0703800551080009070121000610001d0f004007100e80c1c035080c07050b282e0382d140c8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 964956807 1250 964955557 964955609
    0x60a0c0918110c15160c03110f060c0c0d020114150114040603140c0306030a08093c03010b0f01142701080f06010206072a0c05010e0d0c 60
    0x8500034100d407000c43d40120501c0c02042c1c00f80d4a00d05440d89512a5540101c2d041c18510340c00740040c00f28082e101070300e021174412000c20807000c1c3c030b503030886100007080e4401c01d18048044584003086000401d941031040018005880d8440b80f91000f030200000305142000483c5000d4540f660b200c3d2251a80c22407640610f04a400e0044241c807503903251079071042c0c0a40a0150060194074101804001510b0794016034145d03070041e10003400404840165942d00300099003c8402e240c0e1040d6444d0510210914440c0c0d10950000c0320003926882105010010b9107401910f500305119905124184602c1e40341d6035000107103920246807450100600e0305000c00b840c070605c850542c2042141d00310080d55445400c01103503480003030340c403424580d0350f40c4101686408141c440600581008000c10b14891041c0312050308400c507650030070704452240c1844042c612101c1c00441d0108007076581007043e984c00c10b54815441d002558664101e030f0095440003440034a60042d0b18094480e42c0c1c103186651201 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 964958057 1250 964956807 964956821
    0xe040b0f130c1e0b030a09060c0807020a061107020913020f030c0f13020c0307050a03020d0801030b42041506050a230c0c0307090e0a0b060d0c1502060a0c0918 70
    0x4613502d42d640c1c14024480c801800000806903941c50510199608442c0326956181c8101207590140040c2201c03aa03c0e80003500c20507000b01c10480e814002c0c074016903294490300e4050405042c0a0030701d840d07188144410501031400051190700b001200100640ba246041c0840910403946074420315000d0700040c000740540504191144000f06040d030030030900003160055640650210b4083c942c1840007100d002500b40001824089080c012800008060296049a10116001c62600c00e10b5489190030f60f0402c1c18404201101030784004510305180c032413180040301d5003440504071800c004014029100340110201023000001d101c2021504e505a00c0c62007641c0580c500b60b03034400300d0302007036650204032800d80d110340103641000540521a21500d021009400007070140c046030b607252258081801000b031074002c96801e8000340007034010001c46010b80429203801985210310031000303141200003400e010031130307282402c40c1c00030399048500d110813034014100c1c0c4480c401e10225040301030442 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 964959307 1250 964958057 964958069
    0x1912110307030b090706090b031005060d0908030a06030c050406140d053a080907090e0c060f04030308011715090c1206012c13020a0e040b0f130c1e 65
    0x30f03400500c040c01d04085a00402c45840d507680d4850b0a03100c4100c1e2010384415200c20074445010b030820000b42c28034402400f510b404114000030000d03130756241c400480c0c2c0304644021180c0c0d0b45400620030800e80303240c11805800c080c5d0b01086240c2c14280704036194070b04100c5062280784505c5041007081000c000042c0350b542c00c00502c1c01611000030000504107900502042d0003031140d80001d5845228600c4248a0306010b00100801031810700310b00300408401d620f130302d01c1c0d000703074421071405460748802003081d552400381032551146103040c010100c100603008061803941006610782c4c4901e001595186411112081e503009841c0d02000600c0c2c071141d0031b80c0341d80060000000c1d090703003940820031504848442e154481c080401c0b1040c60101180780a1b00b9054402e550046001e810711300e0b15110b0981e1018210103009915080d00346110402280c0490380611132408000c2100380c207003e000d07000031528080b00f00c00ca0081e0b540c05c0070084079001e032103d00480ba0300c44a41c8000507055034801408 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 964960557 1250 964959307 964959323
    0x1030513081206280303031a060f0403020411030c03011e0806071715061206151c0c08010e041101031e0e0d020a030f080405010615050702191211030703 67
    0x2c4810691044000d0486103648101482078420301c050f80d0741c15100c1342480e03800015149250841d5400d0b00207110040d540d00000c064032001c80d080d51500001030501806030030b491a08c95140d841004180c0390f092801c040e41c11003e01c00e101d01d4078003070b400fa00d054540c180103401490806078410402c102d1641d00045c4184528401c8c046460f0304200e9019040f15072516903245c5640303003141061901c1c45640c001e90825800c000800921800e250825080480100b050161346034040d000401130700804025440f07014544209141d0880c244140714058940341410501c075132400500055824000b00083c003145440e4841e403120368440d80c0700104050010024940480d01d0080810080c003410801b010b80b403050300b50740c41065000090f0b81ea0043d5040d9699448002030400403901203401510454840d174984801245402c0308608010003a070395941c509854a0041c010800ba45201e442151021560010144200c00d240510300c0c0c1001d0700400703c0e0241c0b91065000c80c0c0380250541c40581801 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 964961807 1250 964960557 964960567
    0x10c170f040612050a0203130303020d1404030f02070f050a060c240b0a050603060a120510020a110606041506050a0c06090b010806101d04150c08060a0b0412020103051308 75
    0x26030800e101c244501c5002d1000c000c140d580c0c0c81405c049200556228190700c00c82c402850000e8440e8004203403010942c000400e1a20001082d00d000c00001e881c100d008c103212800f10400107504005980091400300322100d43c203440e10003c103204240c1800303072004100600404000380100d006061014103013084000c0110381741401d1840041110f003560a10800b04240000740780d140000503280246001080d813001689045d120b0b00c0c040030130b01c4048485001d408000811084688042d1401c072200b522014500b20440d24042d0038500003c145610451800781d0400c43c5085054104040d1a06c85c1041661034a0420050301c1c0d4445200000b071089051102c4031b0b04001e81100c01c2d41c12243d260003142c0c040d0703c88516800003010240505841c1014034001c070203c076842c0b06006038106000d203060081011a00c0400d1058038000081c2c1c80c0072490b040e00b4099141010350b81c21000f4040b481c1000d00306420204440d100601c00c800180c1010740300e001007001c4c0c00e00a8440c011080d80f000140740c0e95 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 964963057 1250 964961807 964961819
    0xc0a03080405040c03050c090f030a140102030a0b01020f252705101818060e0105010501120614060d11031005040f0c1704030e12070314010b010c170f04 67
    0x355209000d0240614206601c0e41d0210b802401014015044890403078140000202400242e40c0214010380d030520820340500041108050542c00710368100d400980e40c0e14044600c00181e81d008a81c240c115400060345114400c0041500c1107181c001d00c41405551400c038041070f0100400d90051030044a004004100001000c10804403000790050107001a40d50304128070078174139a511862400d010b25504005c402d0803503601204040601e0f86c0c11002d0148503444200c112030301d01031640e00580d0741c3d0b40140141d60f044102000c40d1800e40074144010740c03d00300005c00140300346140c5405107402042c405c81c150360076041140404020410240c980c54101c0c06a03070b8500103031041c0c60040d80741080328a4800c1c40c0380160240a4402d895070502a503c41c1110510903400070801c0c3c041005903840d1842565424840c03207569404000141b00182c2141045030380104a11140072641e071601d0040d05440c0d0b000701c00b220500d50480403040a40c4209060350000e482407200501c06c0c404005408120 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 964964307 1250 964963057 964963073
    0x20f06040801140903090618011404080105072d0309080d05040b19060b03060d030c0212070e15220f060b0304060c2102301915090e0c0a03 61
    0xb05015075060f102e000d8031000d0040d0307203c1c840c48401c141c0108080046081848207001400a0703103a040c50406268404a070028000d90001e4101c0d40480c3d45850520031902c0e4000703509094440c5240a0481111028440810860841d00c0720002d25444203c1c1d0000d04c054441642d5a010b40e90409200600e0207107000700d8451821039402c110110b105505103c00b121134480e400c255400003981d10304c2e50300d07800208101201c3c5954100d0400c0350200325800183c941d0381e40f012000451030010b02c070742c2d410201342c0c40c0c01250003014900d0f141e00c0d94000e40c81956606004842c8080f405101c030706c2b20500300055402910701c2c1030340101040d050402c0020100c60800085100398010102080a020300040444882c00c2030040701d0046209404041001c0e0340c281e0040c4650b00210200703000e104110002d44d9042c1d1900c42d600c082803c0d1071410000d12016081d180000104442d03000c001003c80c0b800b903034003034414a000308101c3c50340d100380880240360108890a01c0c2e160041410030304903a64605481 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 964965557 1250 964964307 964964321
    0x5010204051207031a10360c0f1b060b1f0807081609050f1c08070c1a0d11070204150503010c0f0206060f01020a1b0e0c090603040f020f06040801 64
    0x149062103501e501200c131611242036800765500d0508003000e10f103403041510740f960301020101058400d960307e4110b0303c2c3c0003218002c810802c1841c0811078001102001d8111500c140340c400074001050441036480340450080030741c50f0f5020030001110080d600224000c0d22280740c10360981c00b8025030305040d042e0490b802c103124149035070312010b099031915440844400d807410b0315000700711071140a010a1600441c1c85d0100c500241c1031009251741072070504004881c2d004180e544d400006540018494028491000743c210360616140a000d0b00958100a00c54102405206669000903c4450040d80f04039241d0340e40080040c40840a8114030918100315072290500c03961a0401e2003500d940180000c10307050390a5009070a07140e40b1442448034210740d034100a81103000c0e554200d400926803404441c511250b10041c940349500707007103c6803181003018141a48001041c0002c02d0580e840c20100ca0340190300403030142040d070051002c43c149000d041d044950000b400f0502052040741580a40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 964966807 1250 964965557 964965563
    0x3090c100e2d06310b0703080c070b010e150a121103160b1b01091e14030a0201090203010f051e090309041506111f090501020405120703 60
    0x191140c0c003010594030310980040039600500c0c1d85008110901c40c0406410615107108880c041c40000800040e5250b44589070303412800805401d84580303062000a100d4034440440c0131078405a090410405640c000c02a00404228002c0000351080d2400c0090b61040e560150000d141035840e25101d4480c0c4d90304a038414140e03a0000d1581200b80360141c01e113012217504009a90071081180c841c22011603244503036076003600c035030891806105000d4007800000c0c40050202c1c0d40700c844090028814a1040c00000d40716030420288102040c01007294274107485078503c42144c58019031070710100d04145865203024600011131264041074041d003088001c0742c421402044203507056078134401100c1c02603554600d402c60300347e1110005c00155002d2504002ca11046a0902d90503900140540301e28000200c40c000040f4800c11940f80c101041611202102014049014400120100c1800b40700700380f06240b51940501c1052020a504a802410003c0d02007010804892025980c480d0184070172 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 964968057 1250 964966807 964966819
    0x3050402030607030b0a0506160209010305010c0210020c1b01201b04060b040504020a02030d09081905030f19090f060e060108060108030702060d1107030c2003030d0f09020603090c 79
    0x4490502c00d1140c4171160f0720040c40883c000381008203010b0581c0000006c10348400040e5459000342c2d0395600c0140c0250722900c00402c990880b800c0080c1854000c0c0c0030244868014840c0400f440d00114103908155400b5041c3c5890100707442c01258180c044022000c801d050400030144450008100b9140000c01010305002220b400c4d82884121103152154403e502424001405180380a4006084da942980704903410881044244800c484461104842680300046c03140014002c00815450800060505a086240c01c48041140400092020008000700c800825015084d5070260301003a4200701e505d41100c04924080c0010001c00200d00454030548000003002c10000842c0fa05071403c55020314105070060382071200d503401908070040800e403104450a401c2e03c0140c050b01215000e030ba0f0320407141d4014106420a00b10f40248003884207002c10840c0c6203914000100c60071500819000910a5001303100c0400034019244020b521040020a01014900c00200550028000c0b204c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 964969307 1250 964968057 964968061
    0x30a030e240601141821150403030e0d0807020d0806011e021c08010305010b0901061b05070b0d0b0405181e0f0717010b03031e0306121c02010501151e090f0303030504020306 76
    0x1c00c0c00d031b404120400500d603100c2076a500c5036210144030f99402900c81d04003c180c0d101d500c000c0c0c0b420301e011809100700181401d0100001e07140c0c10040c6810341a03040c1480c0c1410304108000030b010301c10705070041c0c120020083d10329000718420800d160712840c814203d9500071010107401000c80030280700a075407a60919401104078a84110f40604841d1b1540b5900440c4060904440702c00c0d54841e02030700c1c18010003e000404040c004e008182d800584000096010419810081200e802500081c00141c40c080c21007160302c0b001900045a04a1007450407041c4800440c8519240044103034445a0040410001e90f42c040d814020015002d207034001d0105020800915559020b85d0524101d840c1440682e40f046816003001035400504c0030313111001c00f403008821145400c20811201d8105803030550414002642881202d000d85503000389941240c0c000d03e4021b20000803208141001010010400c0c4203500440c1000001e190740100000f003981d030790801038001c04048030b05900902070580 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 964970557 1250 964969307 964969339
    0xe0d0822060c051002120f0709090212011d191a0d05030403050d0206070e1002010f111902010e0a030e0d0c0806071413140310020c030a030e2406011418 67
    0x2658141d8a2801c462074030747c1e8405141c20120710015106800380074548c0c00104c0c0301c034203e00080c82502070081d0000f0b1039500d041c2070401c4151100e4000310101d2404400d2280c09a481c4a000e07003444000640400c0303107500101c1e9860701588200c141c0e03034000541c5034900104040400544100e0707001d502038411004040302d041c3d8a07a0070481d550300004241c071850000a29001c140c07015000c849100005020f4a00d01d031400441d1039654003850102c00125542c0e400d8101c00a50004503c520300c0280851260742001541e80c1e00c9070310b00107050000b000c00b01c036040c2e16192068512160400480004982c0d1144100d03105c11007a1045400240c00b506008008120041165480c007400c1c55240f42092401090380c20461407801c14070351500803602c119007240303124000307017004040c51405160786100112000d4110f600c0c005000d010303034010354850380703941d412581071501c2c402c46a40f202000d5075a8000403140340075000c0d00d1001c40a030126041e401c1070a6580071441401050ba070610400782040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 964971807 1250 964970557 964970561
    0xa0915061e0c080a09090e06041b0b030a1112010603020702040b04180311030d060807140f09011205031b1606081014030a0c06120501060e0d0822060c0510 68
    0xd00a00110303000c240c1d15000140028014811005a0b00e8501c00641c0c640f46e484013590072804814000e5803001e018442800010341c1d049110300040b1003010b50581c03402c48a58a14007000b40f4098089035a9602c1c01c0c00050005c045509404a00c0c0c0100c00a42e144d91024000b50070a040c180e01561070240b00c409a4100b0344a6500e075054110b03c880f0b00c02607141c0c1c0841d4110210421200180828050306016000501034100035000c1140a084600d00700b90001c408004042e21862090494400c0c0107160780700d00415506440d50507142c3c49001c4028142940341d485000d03060030040484054100c20628081104d014002e11004001601c5a6501c81120806405d5504003011159140704008940454101e03a0401c0c5024058072070280190301d1354040d100da158003200115200e000000c0703c450303031440f95902410503418184140d0280d04080380d9001140e00d80103140c00800141140403801000d080803c0c4448102c0c3c807444c154072030700024000401a075048802e80300d01e440346015800c4074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 964973057 1250 964971807 964971857
    0x10b09060405060307170709090e010501050901032a171b01020c010c020103061a04030320190503090a1502010b030a050c0d1505040302011a1c03030b0a091506 70
    0x20011810141082c0400c4103c0d0300160121051101c01150050115806a6024400c0c07056480e4424a540f0b491007402c15650010108002640342c031005015036624101550306480d000102030000003045901c2001c0828405d02110740009580d41c0040d036220800346815407a0b18202c181d88120302101c40200d040045d00c61f80c103025030000017030000c0c154410307000942c0c13003401450013040340340c0d070340f20780342c2140060048186110000107024410715400540032140d0103130140062119481c86030b41c0f241c0344c0201140441203010b0792400c50051110400a45107922002030050700d07200c0d603590f40d040d0449200448003001d942040c08a03c01c9181c04a403004101d81c11101070411148a1420060844c024560844000382101405d1040841911801e13100740e03c01c1d000080c00800843c0c1c903e0a030312104600318484d4404500c0da84100101e8a80c00412680c1400d0100320031090030b000650a02c610703001036041510300010042c46901e030b848000229a40c0344c540c3c454146108400142c2e2000c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 964974307 1250 964973057 964973059
    0xc04060f030c0e280305010c03050f010321030609021605070b0f19111b0f0a15030b0319060f1d0a0807060207060509011a01050a090e220305040905010b09 68
    0x1038200d0081c90f070705000704004440c10301c0202d1001800b40e680d441c0741d14081250000d507200e80d902c610001e0000d400d03202d402e404c5045026048119851503032640c100075410040804074079502070100b4178440c000d03085103000e000700721815903c1d101d42e2030f8000c0c0c41c0079429000b60f9580c49002000202100020b0172192041016403906281c01d21500024070b00e203014542d1a001c04c00c0b0454400c540a0307042c089440700d507079421240345072070040c034007004002885400240e10400704085d0822011007e203512907074800841c1000709400c001d40c40004e051a0750810041202841d001c4080100078841c0e000340f42080d0902401c0000740a0501040d24801030024500340c0b940c003072507841c001300d00c0c2c5a000d4403407684149400340c075120329070351104260707102982c80c02000e0703450301c00030b0511340340c0114407041d107038401e00e0003604040c6070020003850b0b0b40f950311498030120280c2010843e400480d050068080c0c1ea200c111407030300811450010250b42c054070481160515000001c201d54102000726216020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 964975557 1250 964974307 964974317
    0xf0b04060e0604080109030c120512151908070e0f09120c0a0611040e06010f0f0e15210709120b0a0e06011404110408070b0702060d050c04060f030c 65
    0xc28100140ca4540000340e4032640404280000110060240a4844214429992103040c1c084030310b08500e602c0071444402c7d090040610022280080703050445900803206c0300714041e0b1400c1007020461489a41d084038002029051002c11b5041002503880210f138000200d4900300e81d01c00f101c0c08010b8009503100045504191804401d00041c40c02501500f02120b040d07c1002020340d4031002103500010f04411226804202040740b040703015885e540c00842030074405416100d403240107109071200200202440b03843c120020f2680c070b600283c602c1c410250500241e644109c007500e00300d290748503807000324015400340000e00b5040c81006404100c1d902c60f8a0103148140d03d544074100503000901803101c141c0e40b04121b12001c04200030f0f0900904209541c1c80400b644042071000f03036100c0003061400c9440070403080048900014070502250301c5084000d031603189500c00100240f0481018180b610304000c1408201c111900041045451a0302c0303000d5040c80c210001d406881000d580b1501083c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 964976807 1250 964975557 964975559
    0x5010e2e1214010e100b010c0f0b07170a020408060610020703060c1b0c0e01051509041d06151011101d010f05012d0308090f0d1b0f0b04 60
    0x2450701c01912a039144640725000052000103106030031503208007000f1215174407142c1c514450001e43d1140c50a5001b0070f103420403180303060380ca81c00a4160355560007411224000000b40350a885003901c10802007600f000c101c0c1d58181075001202030340060151030240d0180d000442c405291521000c08e9182158010706891861901d8a900034100c40130824248044900c4030080c1d12601c3e45400328503846010a5007289080010110b20010141c011900645900c030744100d4548248080d034603000030031500403070102014008a02c1c03640401d28171f40c8442c8103181c2802010040750740d10301c0380035505940700320700401c0c40030080740c9020341450016107541000d4502009006a5082040c514803014511100321020b100c110b07003160400c0c1420000321750b5880041c41000f05501c40d1902c041c2d00c3c3d1403510082c603824004402081c1d102c0c407000b4400440010183d05a84480380d026100900c000d00381800b500c040d08103030810605075064071180101c28040030a0030008d40807620151034050307410034141 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 964978057 1250 964976807 964976819
    0x909061f0c0215030108030d05360a0618110108040804230a0801021e070822050301020406090602010b03150c09011403100f060c0b070309060f05010e2e 67
    0x412624142a80c02c00b070f81011009001c0d181200a500905a90b402507070f40b00142c103100300407104081c0a0b849802150a400041c0c1c00d203d618040526a08219a1402050068006140c104240300040074941408190309100307419a0601c40c081d4042c01c90f500c450114400116401c0c10115402014440b0a200600c020354407040601406251600c4a85e4252086000910312004035030100030545c0d0006280e414140c1945914120b0f050800f0056007070106076035404403213008160103010a54080b101017016071019401c032500400024008550703468a4880050451841e40180c40156007881064001e82c200001c41d90f56440780c17603036503490607240d404004030203a10540805040000c2c2c201c01800301501d103c019070040386d16101c4164414601085404496600d902640620428401140114003040341d6194072010914000075000e8151810100510000c64681c0507079140400100c0d282c0980c0c5a45030040900140a004c00715030a085051001072038110341c0c2c80c03401801810051 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 964979307 1250 964978057 964978067
    0xe07090b030a2003061504030b040314070602070302031801080f0103020906030f0f06040b10080c04050c0f070b190b060d0203070c0b130c0e06010c14030f0d020909061f 74
    0x20382401c011500f0201ca021460b200c031040c0608420145000003804114a840c51502c0181e2a009100b141014a10b48601a40410040c0041c00384041d040c5074070050500c2c030003100e42c800e0744210219124041c80c18029a00d80240c1c482c0d020006080c88007154560046140074840c0000308104915030f0b003140d003402400b01024000e0364042c460200e050300100070074400341340640b8419005025915140c02c1c142000040608141184900d05605000045000c07a00c00b80c2040280ea01050544420600d0300c180c1c894840d80348000c07540402d9420800c03842d4504a4014584100400801c0760ad06408400710b4a00c100102ea01c00020043d490f9585a507402459002101c0e08104c000d0003010784800c4000704080f6003104100000494100403c04196131030780103420300c0e02202960303203070140000e0701610081ca000380000b070f522507100107215803c02c02c403132460600750403c03900c070340b000000d85002c2c0d04000c0d0028130036013410002480c0750602c45540740c4950340c07116001d102801e2500051b24 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 964980557 1250 964979307 964979311
    0x203070e0f0c0702330d1a06090108010909051507020d030f0204081b040e01060308070308090102031315150602010e120a090b0c01060302030318040c09050f011808010501030302010e070e07090b03 86
    0x4170b80740408182c8900d007080d401502c440038012402081e00c070344031040500c0e100e00418000d442002c0030303c02d40e007603a40c0c44010181920724072480000c00c1012824411f01d032038003811556180b03800503002c001400360701142440c520183c0340c500b440100307000389107007041c0d0241d800b0380f607140e40c00600803e5901858803482e0b00030200c007a20000d050600152140d00303554880c1c009541c0417000086120406038400340440d03002d41104d008500310f06004c20030a6085a9150000c0c00e45a4607060101911300d02d80c4c0030390400103824442c8500c065940401038040c01e01c1c0382210f002401004c0840f00385034646002c5601c440710a90382c03076600f141081e50045503900a0b0050501c55076881001000607201000280a403820f18255044010516001c210656400ea04440d0400400303030401c0005807211060400070a80908100682e14201d01c210208030312583c0c4101e009608000001040c1030f01980421403d180700004c0e02d0a16031520004113101718151028000541401030400c000c5010710061a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 964981807 1250 964980557 964980619
    0xd09030e0f031f020d020c030d060e0a05041a04081204050f070803070c05010516080a020606040e0c0904061d120a09150f03090c030818040c030c12020310030203070e0f0c0702 77
    0x107040c00b1540b84024a96001421080e9036292b0ba10404c0c8440511300d04201d9201035245014801c51601c1d03603504d002c60040703034043c440100320f80300460100900c040070340d07091a503118800700d41c51400b8100282d890300105404d84041c0545900481d10b004080100e03084075030860003044172103280400445456003e030f00151601e40003428890006803c07580100200c20300d603030081034607080a2082000311100e41c65000c20690100c0000e50140e1100e251281c0e02503001304c00021207500880d9940c41000000c01e080d503490007401075440e0460744c0b520103000910b000d50b0314115159250b01840b003c4040d00900000483c1840d5080d5651a100740c014200d2148555294004180d4940e030365001d54000100507410f4000402c0300811030308141c8500c44610320140b6050041003c0c020b03011f04441d42c449440d0030119000000a040e61690341e0444005580c0502226201c6564500d0440c0000083d144a0f40c1d9004e014041598001c4503010781d068160010080a1a282c0c03000c4200b02c0c0c200744080c04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 964983057 1250 964981807 964981811
    0x2030a020f060c030703020705044a010c2c01090b0f040b16031211070605100f2403060501210b040218010908032a01020d09030e0f031f020d 62
    0x400300c40074000342405c070b03201e17400901c052801d2604200a0b2103030b650070085903019207130440d80c201c080807805070540c10105040c0a01521018803100c00c080b0401d5540b096907003011041c501c00c1c0c6c1c0c004880680704100503240900c402442385403a454000501d0f040d800900c102109000500c83d9074004c18041c4440100c49240a55a0100f120181c200d0341410443c0d0340c2d400c101c1414180c12544a41c0900a42c800c10880e030101c0c0710b0708103400e005105019002680c1c603000514103c403409c0c0c04402400c064081102015039030005d4001140c0c2c58104007d56000600c1d0030701c84036000340104415a10140c4440110650400c00b901114160021f942a059110301e1840c0594840c2d00c000c01c04018510003404860361450000341c144060381e4032103910380d44100080414180d072051136140c0403500958905a1a01c0c541e5850301a00174034056070700051030002c94030109070300118500780603a8143c55012a520b40c140070162a0b1030095a03059000e0680c040904401000d03078000c00758082a8080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 964984307 1250 964983057 964983067
    0x120b0414100f0501030312050f13021801090207150507050a0f0302090d142a010e03031e04031101050c061801090c080f0708060c09010e0d06181e02030a020f06 70
    0x40314042e650321080791041c10740da810062040c55444001d4014441c000030040c0040d00340000c0d1740c1d6500c1002020244411aa44298070465880c60001e15580d0710340b2016a042d540c403581040000e41c04400d049401c1e00000040d80789072140c5008280c0f16032019100e03642400b83e100c4058640107080c2d0001003c03d9403c000c44082d07992886511a045400b8180a11312030701101c040307070714052800d41c6c000c8410406120105404e20b0b801421494035a080ca8010000d050f41001301c0e1071070103a0040c41d005221328170100c01ba51000100940100c032701540a00303c041d1407030300040d5650701c192031800f100f43d0803200006448080100103034070f001031203400001d00d180701611048004425600851440d801c00e4111141074031041003014083d0420b000601788604001141d24120f107d02e00a0a062202000e00301000c2c0d95146103401c3c6d200d8001c8003e200f280d00ca8a1940480700b85440116082c58000441814441c0d824007072001c06a409801030084012a401b00608215a4068a41e11401c2080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 964985557 1250 964984307 964984333
    0x4080303040b0103030f110a08131d0402030c04050c03071121030f07091d191a0307060302090f040b04020c030f19020d14180415050901120b0414 64
    0x214071403801210307030071515411482c004000381480c0c014034042045146902592160100e0000202c036400300000755144154203d00c11000e42075441070307006084800c603e42c24103a40c1c074003080c0b00790710072025202072655103001c210840f40c0038bc42020704c0980900000e41030a01801c201d5140805000846051340d0b900807080c18000003600303020f140454048140172102d01520f029940000c410300308075039054201043c0d01c202c1c8200241740e407118041c00340800c0c229041e05131501820301071194140004001c1c3c1e250f042c410000d4482e054084e2195010000d00300d486482550800e030070040c501c0d0311100c04d1408000c040c0c04c404103c00d0344140c1c2001160090320003040204424031000302c2480e00c903100343c480c55094500b0b00702000d066410510701c8091282e40011031048549442a40c55120149034404492100f80d002c40d00d80c20030b141c01410029110201b883c00201c0d5001c0303801421603a26284214541c41340c00d0b0004120350728050200740020449505505071040c9035040342d10381d0000c0c0d1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 964986807 1250 964985557 964985563
    0x120e1207060518040501060509060a110d111e061305100507180f030206030703270b1f0b0f0306030a170405131a0108090307060f060819110103020a050408 68
    0x1510410106600150649040070f507201125042c040440b010003080d0b1600d10041d10601c1108902c52085000003030030252103002c2d00b044c000d1580c7c404215203040350113120251800702e03110500b982e40d200320004525003080d40d00c1c40035028800f14000d0071154071081045699110312403003c640e6801b901d00140d030050154030510340704501c10784d60040b4040c0c800b80c0d500c0c0310b0704050f004030200003c40344007400580c03116421650840260320b8006080b12800747c01e030750201c034680a04101c7d408051142c03000c0c05a008401c50088503410700c0e0101c80c1c0f20255201c034400c44548180034441409010f41c0d020300a000c4080d540c448000b41c1030b00c407c41e01c19aa019802c0b01030301c20780c030008071010a051029080c0451b608441e4440d9403001c1001d2101c8401c4500154121403c2d981040720383e1002a81404040c0259511142c0c4010140710388010280b221004d01510300440031030b8440c0f2130031b22401d13884114100b110329412141a4400c04817510044010b036000034000420701c0360410000070018010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 964988057 1250 964986807 964986809
    0x303190e0d1206170309010f050a0e1903080c0c0a09091104240f030605060105040b030f040204020c0f0a1a060a06030b0102120705031806090a0b0c011b0c0b0c07120e1207 75
    0x1c0000b541e51800d01b00005061280070a4a034401c02000780310400c295a004420801040011100000c40500079158552200340d00e8200034800d000109040460401c0004d400e200304d081260390104858131400948100e9106a001400011800e40d0f40d607da0b090942c40b070030001180000c80d1460101c140c640c0d5142c080d0030343c00030a0100354a44104240480d6106141e00890f0901c0d01a150501d0851441424040501301c11100c0c4516000304046580e0b81d070407110102202406c2d03640300200750341802e4480700310040540300e11748802c41e001801c4514000f0a4403c080080014680c82e040500480c0141003401d1301c241940309104405440807204005000c05038800c00095a8030480b90388050421140032441c103004180c18049841e4598401c2c1c0f16905a400340702082e9240c046507204180580035141e4000302c0403008201e1000c6050740119034940d080d014004800d105c0e00c404648030541e02c00c589000c0c0c80340d0044401407003c0c500c41c00340c501c03036240c0042282d003601ca02081d41d04c1c00c041c02 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 964989307 1250 964988057 964988099
    0x30d140d230712020a0801060e0d0b1f140d080a110303010f21050304120606030f121e0801061b0c0b0a0e0d0b0406110c0d020303190e0d1206 62
    0x20380001c001c14107500142101c030805110f0410340c03c0c401251409800d941040c0244400d2006d45008071001340c4031020303111f041c140c00c81c2580c0c0480c102810303104158001d01c115200d007a484c180020450b458114a034000e004405400703104c100300c4036252444190818035501c020040103203d043c441c4402000034501900b9000c4904481d5881d00001d40d81819550000c1c0b0a9035900303603201c00100c0d1001c4107032811074500d081010894103591910400a1429420040100c40b5034402c0005104020b40035100303800954441841030385001e0007010384c0040300d40da40c40000b03c00740e005100036881401c0c072104c40300d400100000180000d41e07803010150002d1f00060001036002c0342e1440d099a0013411001e014200f0790700e5503003448154031850b070b0141004101510b100c2d280d42d502c0728144140b0f0120b40c58111140300f601e035030f4440d407900207440b54020f54440801c03903c0311014050311a00d80c440d443c1c1a190140041009121250b4180c52040c920b034001c00d811a80c84000056410035204103001a0b03c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 964990557 1250 964989307 964989371
    0x1300c0e0a0c08041a1e0a02121b16170d0b0102060c1611120304030602030103020f091323070303090e182a0d05011406030d140d 57
    0x60310290401c00c4445921044041200300000d000c00308120030792034021811008069411551008101c000c1180b0050b00d0014101e003c0b820001703c0c03441540500216480e0360381800310b54503203009014102d481291503d00e01e4004002e2881d2010320701c0e00032010039201e02c0001c00d49411000500310315400082c034200c841a240c01c0703507151569040c45420740c4440506c0a841c200410078150a10401e00307100010200c08892000407500e680e95800300501c082d940c01180c0d61289c4924041010750000c0c4002ca000d0b010b03000640c42ca03440d06498070b910035001d0890050040c289a120303c1100c0e030301c03a4007204a0304545a540320b8107910030300c45040914000e440d502c00071071801442c0305c002c510040a88100e080e50000b11401030001007003603502040214418100300030000191035002051345040ca41c0719590303813141820480103410941c840900d51100407d250360340400c0c5615050b809200d41c0008014841c040d149495070000b0308034122540c900000c1c0f211513800015a8840031038250b0004030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 964991807 1250 964990557 964990561
    0x8151804030c021801060f03020c0c190e3102131a01080105040207210509040213170a0803010504091103012d0218010c060e0d0e0f040501300c0e 64
    0x1003880041200c1c000130318030202c2e032650714089006050810320700264013003540008084048110070014030000003001010b15034542c1b103100390484417545031700c02c01ca00d900f1100b0002c0c400180c20b0203036071a42021401c44d20420702c441c4805400c00d81c4109012a8000c125500c8008148210310440009400e401075004450016100140640c041640315521840c0108541c1001900f01740d5041c0b0b1014440d15458840f42d0202800e032814011800c080350064030104004114900715004101220400030800c00c60010a004290316500840d9016005440400040000d82410f50100c0207190255054080f00c0e01d40c02c00007400d6510600380b0240c1803079000c1507a40400080c072442402e50301415411450034101501e03000c80c40050880980c140680d010484041c40743e030ba003081c1f010394001c8080d01d80500d9004800350040b0042c00c04075000310902656041705060910416040e1036580b11045104450120019403030f80a0841c8801820201c40860000591300c80385030014100f0309014905034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 964993057 1250 964991807 964991809
    0x90715020f340b12040213020a02060f010518010b091311090f01080415090321050f06010c1a0408070f0b060411070f12020f07061101060806060108151804030c02 71
    0x1891014141c0d030324585101d410044400d803041150062003404c9883c90007580c83d4000105c41b08070362030784040e01a0000445a1500e540421001d101d0140015000c11590701c50081c418148070072018042907404807001800b9020301400942a2000000c0c03952032903460601c0000250b0b04c0c101c9008005100100f86204145001019004a84000e2802d0307100c9180c5525030032401205c1028507a00c1d1941c560700c0070145440b40428142003048424100c0e1f2240700c52902c00d0040008584148004100344040f641961048203c2d0345450f40008825041d6142c0100340003500301e0162088038014020800c1c20300040c150030540490f9805020421003a1601c0018442561000340218080c000d04008400024203100d0103148000d4101041031101a007041c4280e10b409603801071007406116100e4000741e910341c8007048880404c01340000340a01c0e03945044031980c41c40c054901c1e501248402c0c00055174054401503211048a00500b52003541031a82c1c50845035402c1550198002215040d110b825 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 964994307 1250 964993057 964993123
    0x1413061502011407020c0310050703061212081620030d05180706030204030c3f060b0906180712020d0e1c0504090b0a0807060c020a0806090715020f 65
    0x44441c80340003801b00300a10100203070b202c020074080281070f03076524408103440724441c0d40004d010744407a1800c88207034410b40c10810404102080070741d00003085000001d840c80c000c1c04000055000320345655a050300f0114190000101040d034501d0f19100a03c01d100082e229070191324011200300c41c0c0303d00308002c0348101c0d80c104400d0b90001c1d0103040c01003104000088109168104071462510403070b221241f00d1005004051304941741d00e03858902c095850481c81c45040c00340c241daa104040030040d400c601800d2241c000002c4440380d40c004044641c1e00b400e900c001c1855503102c04240b602c0c031008806040070800f2a01b010100c1c404142c0d503486450362a0f07900300800c07505842500a030924138480300ca001001e078031890243e41c0280340c0f0b81610300c4a6071038480c0b242001d0300521040e0780c255511424020a850000c0c0b505078403a200c81c00000404c2e460104400c2c0c000e1106102811095091500810072041a20320802c114410107103035802e84002408181d9980308100c80c0785c400e0410780c0c101105 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 964995557 1250 964994307 964994311
    0x32a0512071403070203070b030601050d06090203160309120507140f0d0f030218040213080318041d0303040204090809090906010e090c0102061803041a0903011514130615020114 78
    0xc2c159008102150250b40c1c0004d03840110360310051003d660365034040c01200c1ca4010b00d0f1801010a04148000c12102c0e01c1d0340245104034044c2148a4089a000c0011001d80b2001c442c09007000e0447c0c040c44440318031480007402464000c02500c44c01da00301401c40c5103003280c00d07085510140c0089140007603140c0e011008161840d498901507003031100f524403030300d04030304c118075070510aa030300107a01032103e8102991500100904e80075039071144030071000319125000a00c84c2a20503407801c50540400510812003140d9070480c14001c60641c1d65603402d010041c6110030b410380381401c040c408001c29a451051480c4505c110b803000e01915490100850081c1d5800b511582c01c1d0b8000032103080451340c0c0003c401c1c0d0b0240070301c4210070112a00a00f11030039480740b50440034080c6401104d1890200b0400700800781a10300340d0013000030903102c40b04100b2101450096a01005030412002e01300c2ca40703140006828207207104001485030f991250303401c501d201c60f00d540000d0307512112044681120040a01e03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 964996807 1250 964995557 964995593
    0x1908070201140319091401060b0d0e01140c0310090504060f1a031209151215030a080901030b2101270f0209041b09020d05090703032a051207 62
    0x9411400d00da41503a13403a04800360042d520700d60303c851050070700c070400a0b0740c0840c44032400200b00c11620f545203240c80740d1242100031300060810b6003890300081c05201d014500000500c1d140e14a0b10b40d1510500164030203020032414500d115000320354000a48a014003640c412000080e002400128100a4ad0b4121103540b650208031a0001d003251130206051200380a00c0440071783e958400380014180c01d06c4880443c2c800c0340c020409140a6001230116030042151003814400c44aa080415a4548690900900050048c03040030b0941d40690000800260000c0a6102c2d03801001000e01c1542d0140344420656910354010301c1040d80f148102003d4406c104c5105d50806040741c40f41d2003160a4814000d0040c510b190025080c440c900c1c601c00d044c40c01c0c610640a2583d80d5002c400041e400c8861300c0034009103054042400d01100007140c03800c40307038035032180403120f1650b004c0c2d00c50900002110014881882c0c21440008006102d4840e00c80300801c200d41e21400301e400e0842428480d8a540 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 964998057 1250 964996807 964996847
    0x3060907110c0d0201020f19050709110d0e0a050f1f02030903030402010c030203040e011503111905130806132108060d020d02030f0604030206061c06020702031908070201 75
    0x300051100802e586005500507188510544820b10040345881d18048007000140101e042904002d945041c450340d0300341c0510100e401050302d40385420201c0720030340c1070944000400c20003c009003001f600251614180302d41903902400068444130305001098240340d00a0b0044120900e21a91402300340e209402000f108600310702c0c16154282c0c1d03a00c8007820190500144400c0d12003018401c00865000c1c04c4803180d8000b055075a003280200e142a54a280c07400703e81040a03500c40051105d0650f40d180c952840e040c1042c2d09002c0c020f84840c0d000c00c5030705a4200480f40041154641000303000c0c040d5201d00f01803405078a850915010340d0882d000c03868141042c3c6403a42012550210080e40c02c144221100040050280f0014070200d0a42c05c001307403d4010322070140c01e03009000c6242445940a602941c880303586160810462050f030b001d511100000d03201045011807a207a014116035480a41150349407200c00105001030061441c0403240c2180018801c411543d011042009548004040c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 964999307 1250 964998057 964998077
    0x212150903130e101a1810170612030408030c010606030e0d11030702040516030b101b1e050a151512020f060307020102130510050a082a03060907 64
    0x84102c1c06031054080034402c040208084a1a8220000c010252103541d548242c3c45240c020036560080314403003400410595804945080000344103060350f20590b118080001071000300d0840f01d102411180d00140d2100a03142d0400d802c1000b8005017501400954840100303141960a40e5002e8000303004050a110102c0740908000504002403c140c1c1031004c45c3d00070701c04d2040d183d40070340000130350310038241001e2151510017128240d901e140c046d0f03410311103000b01d002440009a0b04074004400550201d80003044804011203c0c41c1f4184141044244000040901ca00000001400b544c13603801c400304034810012031007a50003203060142070a00c41d5045403004040c03450b40c1882003030203002200180604566800c0f03a000a04000141215204d042c071500080c002e4115500400b0071540512008c60b81c0d10b403500d4500e2940d0318076075030a80f4050540e4000c032106040600200104840c9d0000c0300081c0e40c1040160b0994540380c46040d486c5d00d4442c0070414241c0014100304144160081 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 965000557 1250 964999307 964999327
    0x1f0f050f03012703020f0d090303110d0206070309021926070e0414100609050117030702100315080616080112020f010e0a03020a0905091e06060108040f0212150903 72
    0x602601800c03e0280e503041101d49410140d0504240c980481100e000b94021495010b0f0003201d07202c01c0d81e029580d105010015072286a6495051800d21405640700c41d001400840c400c1c3c00150b00544003030f11403100000035420b48a400d440c160409105e140c820215580c101165034407404000c00f66100414001e4905881d00700b2083c80503001a021741101c20500c0c1701c280c810002c403104800e00c02001c004107031359030403401c0091000307000e80352640e0b81c200000005010000262120140c0041007000b101d0b4074001c05130000e04603a04400f40122a4030300008100c541031041a104803031140c00640c51400460000308588416040444032001c1d602c90240940c6610340400022002820f20300944889100003136002000c0e90310095001003c2130010071041040d41103907014000c10340442e034000014040c1d902c0d6050b4103410b041c130329134403c5002495541c4648000754126000e0300c1c01c0d10408203940c0204d00c004044190445d0b85a002d50106035004030396100e00d582c4000000091403c003c0841 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 965001807 1250 965000557 965000591
    0x315241d0f0a0b030f01050411250f02100302070308160507060e01180c05030c060a0c060c260603061005010c080d020c0d0c110901030c0504051f0f050f0301 69
    0x21115005007241c01c1e1004850b2150780100c00600b24000b01541c0383d1a10f002d001a8600d001d0044038084c500b00051004544048000d540c1da107145902d08421601d44d50b01003110803d15040c00b59030307001c1c1440b022000b43c1c86041000da40c00c403e5a60240c0c1d01e104505010340045006050000125420199448440d9104050300d80603036200c82c0106034071640300c1059024190f401d0060b242c58640320220310820841c421142c003140c00940c140c0d20300c4141380c82085018028101010045581c110010300040e140358080032078035007a410560030701d8581441d2603d00c4883c0c00c900a500c1d40300c007011b201035450f0411055501800140803802440d0400000802070480900c004000250201d40262a0000364058407a107140b1081290302980700d00d00000d0451071040001e40d48200a0765454026003012802c80f41a2500320316015102c519041c1071000921004149202c00b2001002802c0070003490705824000f026505104000d1070b081104201c00c08401200092081c1c0c0341c0000319804520350 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 965003057 1250 965001807 965001857
    0xb1509040b0a0f06060207090f020a05091c0609030804060b0907021c030e060708010f0603050c0a050f091503060f01111c140d140a150302060a031524 66
    0x412201d51521114200e0b00908a03011540c1c12541c20700501040c0664005600001c0302c6860000780000e44e0710301c180361b00701c2c42001070742c44c001201000540520708201d1021910880c2030304020304210481c2d00c0d820115460300d203080b0006420141803000380305a9004091428000b06c410045900301000040e58990b409900c5400c000b410140b012440e500a60201c8a05c0d803401c0d00b552054a04410b004041c407809020304e0703c003104030460100b03085100e8480c0c9882068501074807071a00b00c5100040d14103801a4003100300c200c00c1004914801c0d102c84881c0290112282002074a1b810400c4c20804510600c0041c0d90401c1806001000e640d000000c6051107911030140c02416002e040300110740d04400e0321500c0c0291080010107515902e965842000301d000503210b84070359500c8640b01941035444030040d49510354030194081c405894140c0040100401a0070002520500780400402c42c101c40c0c2e001c0107098951210007000100e80b400c0e054490403e900d0030061a1412480307045198185c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 965004307 1250 965003057 965003063
    0x2040b0a030b03030c280605040506060405090a0b070320070309060201200d090c080f0a02010810051011010609060f09050c0c1002030901021c0b0a050306070f03150515070b150904 79
    0x80b09a40207401c040e0011b10b001540d00010240681c1c0f501d810116511602030310725078000e9142400160800b80302043e40c0000981c404441c05c1030b40c55641c4220060400c01c0c62419030070002c0f940701d1540c2c0c003482d001400a940b00f601c9500c6141c3c0307802d078080c1c00c5406e1b07010340c0a501007052100c15400161070b012205000d044d40c000164104080c10042600440380d08901b12500c25210302c84882c1744002094400d0354400d030f07102c10169480d5031a40b00105100d114454000011810148180c5d004060421219441e40000503034244d55078014000d803449a0301040084040340e0090001220300d002d815801810b8801107841c0503009070841d55503a00310120919816804000300b00c20610070340440d08070b1185900c50344e00010007040080000c14052030b01c50b21070580c41d040041d0b60b080100758144904020380712581c4943e42c1050a50181241050800040c0310882c00030980f0754883d84c0c4a8244041c00122948903422447e010300140000b03810a50101108405180d181d611180b9040c2d01c164 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 965005557 1250 965004307 965004343
    0x14030a0903020d110402040e0411010c0809040506041e020408012901050a0e1908060610080112170403050d090b0903030315011e0e0f010915200102040b0a030b03030c 73
    0x43c0500b0600c44070400180070715403080c00010000386401c50380e501c1c613000d20b01440c102e0651406080040da2401c2c80b081e030042a00c1401d00c005641c600d040e6002c0c542c420005000803c829010044102d401c0c06011020100c0c16400300f42409151301c01d01c1801d0f04803812144100c00d03030a00300401c0041e41c000440a40c1008000540c00340c100d0310070400791010310005070030710450f00c2078000401480d1905001d01c032401e100d03840000e22245045060070b42d007801c0540310308489901300001403800c84a024000d442c0b9105802c06c11010183d04402040154040c2000e08801c00340c05d04010b0030001c40358440e5040003428410305515a0f0003204503900000c2c0c0f01180562200d9507401680d14011141420325008488285142001d80001c0d205041640031a065a9403101200042d940441c160040030740c600c06400f101c501d200d000300c2c031000143ca02e0840e08501c00c4030850b410750981e8015041000811383c085010052682c06020b82801d554080b000341d8200003160003800d41d070b0309a0281c9207800030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 965006807 1250 965005557 965005579
    0x14090a05071202131a092407081b190503030f340f170a020307171503070b041d0411030111120a0207020d060e101814030a090302 57
    0x940151018501c40301c2c00e04003592141c000701500351580b50603120701c20450382d44882114402e0003840c00c8034240c440c01040c02d0103024a03812001c0d01c0300c0051302506e015260420152002c114408040e20608070f45c00c014071840008501c040c2d0038032250000110100ca9040344400000e400401038030b41c0154040034000040e43c54030b80e400c590301079401c502c01c52807000004080345108074441c800304003081c0b51283c0c81d20042c0d2030340844200c1c0040a11417111400c54010a0301010f50b6002550800740ca8648000f02c9451044000031048082c0c6160f84611030000b042d0211381000e00205000b00b0228090b18201442c100600300030310114140710510308142e000007000c01ca9807680301c59030000058020046011b90b04000840b541c85840421441c103000000107509030340d2070003250540b56015018965208099460344054900d10000d45914003c002101c0884071542c45210a01501040d403901400190f00780000fa19030650500711a5030401c2101000868004000f80c08495060b20080200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 965008057 1250 965006807 965006821
    0x15050102030f18180708070203090a05060306040f0203090709050a0212060d14030f0901120903020c010c1e03030b1903020a12051509030a180f06080612060a021314090a05 75
    0x20500e0f4000e07070224045400000c401c41d003680c21803241e0590746450840b915030400c140d91324096074094980c02520a8000c1c072850802401030f40e002800030380301160000d00940d080c820390300110303803107503803684000c0d0100150b4005010703040c3c2144075610700f1483c0809010442e050500c0c010a1140200d004540d0002080512041000c0790415542500e13120302412031400c00540c0884400c80c006041d680c1009240d1800e4030030140d81541c10307001030001c12221401901c0304400a0019038004c410104281c03100f292480055498620a23035000641e04491402c01c038001500000c2030380315030500d040620050301e072462140c065074480c61601c0c06140c046d103090751411486000801902d80c003a024026450800000382251400e15191643c46ca44000000c4d0340d00d0300c5a00c50000e20001071b1000300041070042c42c0d171035089000a041c001c1c5041009075a107207000c5055800341c09140d800a120031544148a000001800414007200e011001e000e0004c3c94076080a8507000c0007039036030700c080303404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 965009307 1250 965008057 965008087
    0x30103031e050c0f032d07140f030a0503040c09051314190b0402010f08040c090c0302040b0c070f1d152b060c140d0e190c0915050102030f 61
    0x3003003407014202c4111107507a00d1310540725002446001020918443c3d10103442c0c906400c0d030348110303503840e04603420300ca195115072501000b140880e01a130b0150002400c2d41c0e1805000414418680762299680d1b1705191a04419070010796200b5150180303440c003800485805140051a080d0304801c12000948107880a141451a0400c0b0f003280b0b03e262442190030072503041c0c01103100394002d803250755100c1e0001c2c03015a600c05040b01d00600380a180d0b0400d001c3c207000355000e0325208800b8980107041a4850301c08040342d5000c4d05007440154841c02d0708201081c0c040001e40b018040344a03824460036201525024845401341c0f52503003180c95007900390b0030f9458040140340e88540004410881c084103507000051001200411384016081420403030072180075a01d403e840740c031419816840c0c860031000010040c03080c016038a0031406100c0b6030910040300c809030704c07003024051096140050324068a00c070850701c46100c42143d9140c200c00c10441c507030300481940d5180090f08400b60b507a0101c0905206 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 965010557 1250 965009307 965009317
    0x1d0f121c0f0c03140f0c01050613051918060204330e0108040609020603310f0b0403090305010c030b04141308031005060409091103010603230304080106060c0512030103031e05 77
    0x200c00c090201b02e8002d6030b441500094082d030002d030340d85550400740c18807120681f034045504004200a01c440d40211103071542c04410310b1200449007100d00a80d603501c100680c2d02c10f0b0b0000550451407540110703105007200421043faa0b00c00030300d524250380810060314031030381300031410b0500c144e4400060501009801040500ba8018107040c1d803494290240485c0140140c1c000c41e240c0c44c0c160440e00d1800500f50b800c213010740c2000301c01020030000d035240c070b500d510002c008601b004804000040005e00900900004a20640b0086203005408080c0070440c2d401c2148020b100038041d0500800040030080b0a1166400c1407000b9501d68a14600c400018466800240c02000004002801004e20f40c408820140b0846101511540d10000c0500b40c0308240005001d840d064414681c01840703018401104151070020760b810260303150105400c64400740c1c09032000c03c80c81540034040040c280140b464401c11028601d00799411503e0080505170094040c455075144411181050360081e03040e60 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 965011807 1250 965010557 965010577
    0x6020f0c2803081b07060309021509190905011502150a0207031707050d0e060f06040f0605040e06040b010b0a0207141807031406060a1d0f121c0f0c0314 67
    0x340d5144c504402601e0850045443c40134030b40103030600410118407034025403030223603001030061158a124251041e010761008802c641d0000d01504000010301ba0b0b08582c400805c000d00d000601c540c9020700e14264074219103d0a41150048141c0f00d80c800c1501c4034050f00002a01c03c0180c8031069031900382c62255003040c202400f01c010030700704014150700c28014503050402082c24001c0548030a840d82d6690307802d9485c1e500140304000040c0d41410700703502982201c0032006012515503550000704040303420200090720310340c011030100410300031030000090040c040321201c10318110b519070009494421501400e6100e03c0718401842a80c3e03a00d10003071131010140c0b0802c8e40c140c00d00400140c01400302000c1d40b244010500006a05840d00605503120081c0d1a240c074950720251074942d00c000c210b034500d80781e40310b00c07003500b819090345a2110141c07a107900d1a005001030b0300c0064401a0704a1103094490421510080034880c0503400a2501c0d0f40301d90504001040058282d248a5035008884100d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 965013057 1250 965011807 965011823
    0x40e04050f0a120e010c020d151d0307020f030303040302060c07020105071505070e0103021c110c15070207050f0a090903020c0303030c0a1101061a0c0f060406050106020f0c2803 78
    0x8414091035401411143c1925218a84010807110041d40c210007544030103944503126006000200d00c818a6024110404c203400103500390b2580d001918101c3d2000b142611a030002c5500030840c00e0000f07440c143c0b40c03c11401181107141558009542e801d00078400c1001c414041800f10459018405a4619541c0055071300011030040740050000c0c841102c490001903414040390a0550091013100c01c01c8903144501034401d45040201303005844000c138091607240301000401105c44091203201c400ca001814401403500348528002d160a030141c1005101d8210202c16901d90303680d0003002070480301e040d4000710781d400c081d05080c1d040586006040c0e0701800004100001c7c0c100e00d0000303042040303403030b140d0301900000344c24218202c42c160f00802007181140e50a10098481c0c00d00585010300ea01021110381c0b498640001c0c0c00c20400b07607002c950362600c0f003006020490b0140300d070080d40c1001e40010002d800121b40014a101303500c00d40a015207013810034601d0260040e03807042c03002e50b40200035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 965014307 1250 965013057 965013073
    0x1106070c271b08060117060103020a090e0906060112050123040b2e0302040f1e03061505041109010c1b030503040e0f0610090b031009051609060311040e04050f 70
    0x2c038031100803110303840c100041d00c0c040001c440f903001d1190f1540340080402511841e548110056000f035000e500043e06100d24100c0010f40108184a05031140d1a10340180800d41004400901070301800304c0c44205503401c0c44014002d503840004e2454840407403002e011412101c840c0424024040b0707500c4c003034000716000104070701d00b20720314070150f01d803114030f11101302c1c0d80b039510012000c0380100d01075040d942600304401c02145071406400c082c0301c40760106400950796642d0b03c0d00c3c100c5421580d0441c04e9403002c981003041c6c1c5481d104070071030500340703600e014680500d00b80000c2c80003451482c010251200e01c60085c0e0046401d00d508805140c0c001c003200c0d55a9141d0050071516403044450000c0310080000003105810000303a00c1700d0721039481d25800000c50a004055200c3d810061032601040c460100008810000d4003405020700c0040000702c0138482030360002820750300503411010501d42050140340808121104440c21100d920212210303d4545240c10740c02c0c00c5040c0c1c41d00344a4803038408 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 965015557 1250 965014307 965014331
    0x3030c050f030906192904020c060106030e01060b1c15120311161a1e0412200a050d080c0a0c092307110c0a0902071106070c27 56
    0x1411314001e104004080c108008018145401d0711003d5014101200003501094100490019030b22941d0000400250500c1001d103200f41c039200e000d03400440000c0c6ca0302c03004910180280714400190910150140c0b40c40c010703008400070804060072410110356511003a404103000841c404018000e00c0000c800700c00058200104604480f600f8402c1c20b0242c40300e00c6548100d00c2240c0801c450103031030307117981620100c150790645800c140c22022112142d208030364a150200001480074007401c030302c03005483c507a500b00000c01c20302615004a1b407034126103034401d0ba076450140c40300466504960401003100b55141009180c00742154810042c46016400010891483c5c1a20305032032000c8400c20a14a0442c00c050442807401e20002145243d280800d0400e481000360a05402c00c002c2158098a611030204190603c03990209800d0769021a10380c040040c3d001c01001452000c8500508091154641c101c2801d41446444001002c0a03001558110000c0d08050f0041d5085001c200c1c1c1c400c104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 965016807 1250 965015557 965015563
    0x12041b080304060e040203010305150709030f0308090f01050f15030102090613180209101b02030f06010f1202060a0320030405070504060918020f010c021e01140f0703030c050f0309 79
    0x4081d00000c102e00e120181d84c0c41c10580f0980f41202c1e0400000c00240400c400d401001d0f210181040040000616020020400c0e50040d0208540309a07074510442c075121400030308003520113503102100c0e4140402e20681840740ca86240d0030240c0d41301517226001c0c0c40300000740240306501c5040d4105901082800c036102580810100300d444015800840107401c00510007240310b00301c003103070780000700c0d2101d880274134800c6001d0140a0030503a131009080b942c540000b881c045164145c138802c0e500020050103000c0c4280c0d840c4000b0038800100b08400d807000d500050329030046590040c01c141d9200841c100344036104540e5a24201c0c80f1007802d50364106070900507103c1c110307802058003450400000154100c4503203d100300c514104400007140911507800c00c0909080c1540d41810082c0c0d0003543c0d005a501d0a03038811545400005d609059844000050609002c1040312240c00d4010b02410302c1500e050310440707090304e50510f40010782c00035142c020748260003600c5a4210800001c41048a104000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 965018057 1250 965016807 965016809
    0x1c0609051503390409111c080706200a0201060302100905010c0b0403021e0a120804031e0903140c04060e1501111009050d0905010c0812041b080304 65
    0x11050012001038031024540e0b00c1905010304901c100d400c594080f610b42c00320700c001c0c21001152220801030550b40d0000340a580491400b640c114050b014540940d14003180c0c890725150306d050040d4038010040d294043c4034098144060806a100c000387c081010102404400c59140400c01a03155484104024020501d90204030301034100c455010406038040ca05010440f60143d60380640c40c0107541d0341a40246000d04100d0a501c520036042021103007511294803004080030003072000142038203200704284c0030b001404041c882c1c10401c0c031001c41e52100c0001c9400800c1105036030b4000902c0f034106e4840351144c0c00540390006080464507146004205684859003c54003030140d40d441e658201c3c02401c09175248003a4484018009221354000c509100390f20b020b007130a5a081c4a000390310101a2803a0b071034101c8854100034103a030403c1e50031008400183c842807a004958504039981d01c0d8130b9100300a0b6000080e20000001030805c038000c4101540c030a14a8050f074041a90740729840ea4903005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 965019307 1250 965018057 965018071
    0x4061706010b03010b03070e0a0e0a0e120c060718180617011b031a06040e100e04150e030c0f060712110a030209061e0306010f0815061c060905 63
    0x195400002e02014074425070307040c1c4110800f100d195407203541c02951f44410406441d40c01c140410400038100010900d050b100d0312194601040015020940f035003400d0020244a40c60201030010343c1c0c00d01c20009041c8d6111980e4108414001010b0140f00c8003044c05070b203c2e001b82c84031036581d142c07440358a4010b072080759040e03540100400c0c2075292903801d0f00c0715201c0104c0c030300140c580c446001a119401c664035803a03074842010b0f040802940450b406070301a401050b1003a0030b440038000c0c0d01041007102802401504001c0c17030103040503900c1c810030a2401c0744440d0a59200c101e00040c0000c1441101c000207070400883d55000141e0321200c0d119182200c126000c0390401e80a000141000d004000355240c02000c450700e421810300041d0000d422080f00a070304500103102e410a407144086010001d054a02d0030142c83c3d107401c5000400030300100482030300b049020006d10420002c40c03800c541c02c982e411600710762241180000c00300840b951944c000701e180d041c4840000c61131f1560b40301c0c07805007031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 965020557 1250 965019307 965019313
    0x15181403011d191b03061d0c01320301091b182c1509060a03051f0b0d152a1d0a0915090203090304060309030905092e051c11040617 58
    0x1c00004001d40306c00780c1400103404540c1c0c1c4500f01045000c04000442c402d610002b111000380408248444190001d8001d4032a0940c3c0ea100d403840c1c44100328920200c203159240503c009503a000301d040c0d211006125140c03003440c40469180d06803010f01c21003102402104c00c51610741c6000d5038800d014011801c0001c2c01071103007502240c11806d01029a205803a0800e0060008414909152020080346884404940e544082003180f80e80c1e040104d00a403400380c188191007014001002088401c040216600742c60300c541100341103000d540d400590745005060030310381d14000139290340c404801d0105050b4000300c0c00f0000b14610100e64481d0b8000c0c002203031059131480e200d4065800300d20054130700c6c00f4642d00911040100d1031080d0802070202c0d201c0d02e410001180d50b0000f103540e9a4050311945582c0c40303030142070385e0700d01d12504030189000181e8101e6585145400042518180e0004504100c00c0001c1010300c241300e005280b6441c4800302420800c002907803005027120482008000540e240 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 965021807 1250 965020557 965020601
    0x160f060e0609030a08090705030604030f08070f1407050703150f050c09030601031e08030a0507020f0d08060f0a08032b02031015181403011d191b0306 66
    0x440e00148007845022010021442c080400b1815119090000c1200c2c0302071044641c0820541c41c2442507500a500c03e8440440d103603c1e0302005030036044010145801c02682000300d499480e4441c200d100707441003982c0c049950b4401418200c3c2440025007014003200c01e260303422504c0031034580c051140107404203020401a2a03110304080d16105941509500d50b11050041c00410360800f418854007814002182510342c2c25074030800340707401c1100c040c02c0c0d0507a50000c0080e2541c060200c40000303200500600043c3c40c1c2c1c444050004980501021b000c0c2c1c00c1000c9110f0075490700b0041c0005809058200c0740c549946c65090000004130007031360f07904182c200128401c203c3d214001e4a00070010008100c203100d0a00c00340042800701034242104106241c4610588a00e80c04541005082001c0480500403203841c1070600751002c01405e40c0040009262681c0199000708211415810034004130090240b42d080003404400300341e407604180040100000100f01e06940010b9030000c1c1e06130889051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 965023057 1250 965021807 965021831
    0x30c070504140f06030a050a05030d05090c01080106030b01030e07030c1d1308161b150c05250509071d180f190603030801030605010b04060504031106160f06 69
    0x51400040b002c19169807841c04646455016803d07294048006002c4508900c5551103aa1421200f1030064915030000039503201c05801a0042507805200c01005103984000880000c003002c1c8140f18060800d99510030740c02d80317688240c101c01003c05603481192800c0d9101d0824042c2c00b0580d1292014401c1d012200c0383c0001600d000c03240c401c0710258000000105641c03141c1100c0e911185104120610302c040c1d030030002e0b002060091502400d45401051a0b082c1050007181005140f41034060101c52142100000c03400a00c2d91014030540d1003003000c0c164107000701c010720141900000e90248100041000b490750200c41500c424800e000700d003c10001d031400384807441c072030705050381a05440400000d8040e644440060b400c51034605016151519801c800800c03590942c00441c005550f0f00c0c0100107101443c080c1c0c5015000c184804d510303042c90808040c00610851000500c12152400340c81007903662801501d03d0064110628003d50f20b15250546040c0750b1403004a4845140000c40200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 965024307 1250 965023057 965023061
    0x60807030602041d060102071719060203060102060117030d1a040e1606030c050316090b1902123a0f0525020303011403070810020c06010905040b010e0720030c070504 73
    0x911781a000f42002030300300540050310302000a010100f522507862107000d440000c00300c05600e640100c000688074103018000904101060b8062110410b0903290b10317154040100444400b0180e410300004c90040c0240f01c5006003240c0141903070f0262421031180b5034107102081400100c50722082c8001c025455010a408480c0f41118040008806100141500358515030714042c00070103003418200c86954840c1114541d00c04804400700c448600c4e0a10426501003054608a90000101c1030500c103249a481c401c3ca0b4401d003000101c081140c031081c1031f010084600c2c0244c0d660400041c004403503110382c1c24015020698503420b0a080101c40c0c01150408084200c3d40384010354042d518503440c00980481030301504104590501500400081602041043d007090f00f080e500c015848015440080e030400205074490354010f0b05207400c1000041c41d1881d06070546903c0700c0340800e6a2240c400460310000c061b20091071000b00c054940920341c4d4000013a018040f00300003280c1071075450b9424001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 965025557 1250 965024307 965024311
    0x140307030c11130e030d14010312080402060c01090c031406100605131205060709050d050307061d0a05070302120c01051602030c0604240e13050a060807030602041d 72
    0x100003004003200000080036895042038940c0700401414407411003000f110111200b02109594561000400d2507160f4442c1c000d07074261507401412560f29624580305d1501d545400400c0e08100541d03000000c00b1555098151140c2500041c0200301303024180c03610680648840c00161400401c90f080710010381d030b000818621408a0f0420342d2001d40c40d11130103889035003005002c0b8071183d50252002c00c41c0041601d0f44080d46009030020302090078180030107480d9032400d402090042d120034900002050f0008100c42e111603000d44006020310003409400d04960414542041c24001c1c500620140300e00051044143c0c0c4c02183d071030045070b440007a4241c2c2c404032070b0405404a981442409402002c04210b00c01c524009400c0d0307806540c20f900014a507600c26084910b01d00c503014801e40e480d07000405c2d21100010305040c00070200e07003a28001417460200b50f485004440d12500000e03811112500100024055401201d5000b0386916013071019400c40c3c0200410700321901418420311040d00c40c914 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 965026807 1250 965025557 965025563
    0x606040216020409020102030c0f010605090a09020d0803070306030c060e0f01020c150d14090d120b060d02130302060f0a1b08340c0510020a1104020c01090b070c140307 74
    0x1803961400c2c0d402c0c00094040c03007105038154002401952545031080c010020f480c0f00328000042c005003003004010f81c0e98400307400541c1140c680380540005864110700307020003039004903c4c80e841c0d945040c0214090541608028210701400c440012105d40054200031035000c200e070301c50301518914004907554003400d80400d6120221001b007040e00c1540d00000c004400310b40c803011075070400c1310a9400103010151007000803641b1500601c204c0d03980c0881c11300401c243d424402d1004107035400c0021b030107008481c510f02800340d00040040c0da44414441c40001117071b000d040b094076503484410420460700918010030100d181010701e1150071004101004103140d204000900f00b00120b0708009240018200790345004146001c5084020355140c42c003140c19206d142c0441400381048140304000e05c580d2020010741d40f111700b582d00041c0c1c4800540c88030701c4040d5401629081c40c80501405060040b01c00b07403501c42c0c0c220900918662000c0c40c515468042c106501804c0c0c00354600390307a6486164405 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 965028057 1250 965026807 965026837
    0x928290c0f041806031509020f24071a090105040b010501051809090607030f0203090a080a2a200102060105100c0f0b09150717040c08060a0c080606040b09040b04092306060402 77
    0x7020703c80c0303002c07440001e0b04464a000d10f02e48020141c40c3c050681e1110f00190703040603000330038a0b4040715402d00c00b540030007000002d226909059454070462541802514180b0070041010340c0c01c01914808407900c200010301d0f04500e07081210039244c03514000d80b01a00081d0501202c030170b40c0c0045008403406007100780c4c02440885156203a0b0580e51308880203980070000311400c406403c80c030810403008407030810820400142030501d05510031030544818112119883d080ca4402a038002c00c1d1b50f41103960503641c90000d1580300c0d8003142d0010301440d009200c4071000b10480c092103200c0c0b070041c0c4180300601c100c510040d4501442003900100302d404c140040c4a8411007074003c42180c2403030390003921841d9082032050301c2d807030035904001c0c04a13841e0054030f03990504d03e8001c40e0f000404a4000d4820340c0c405180038100b0780011118490390b000b041c010790712024030311500d84899101c441d8080d04810750240d4800c5030b940403e9410250786000140e4807500000c9032880c9898421035601c042200c0340c0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 965029307 1250 965028057 965028079
    0x100f0b030d0c0b130507030507080c1807080702011b03020405044b050403110c191703041a120108030405180928290c0f04180603150902 60
    0x34201000c40c0100000c4d41c026496109a0000c4c404020343c9001c2c601c01d40141c40002c2c1411030351441d141006220600c60303010b0ba148094407544c00c1c02601e4001c800c0d840d10f6090740d40c80450583c0545600d058500c08403034820502602c1c0d640c50342c0a4030980b0f204482c14010800704c1d80144040d0704148641003040c000c00c03910000c0340d0822111280c080d18072040c44031403104c400460041116000c840660218000c9103051500480c18030038009045400c4558062400980f92113043d070781c0960044d508404400b81070400c40841c2041600d0080c201c100b144400a59803d00c99452508590240c401c03100602001085030100803041e00d0940c1c801419544954800180c8003e901c6000781040d84030f0300601c102c02a031710f0341c100c1166518a03c2c244880c02543c0300c5107094000d0041282180803000d401004641310134191200c0c40c3d4205240041d00f5481c2e2403800d101e20043c2c41590b101e50b040c9400d10010342e40e0044103402083c1164047c0c0c0c089018502826200c2003991251a0000d51200350124 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 965030557 1250 965029307 965029313
    0x318140a15022505010908190318050309040f0f05150a08061306240f0807050a080312100806040c03110108070903020108070c06090b010e18031218100f0b030d0c 71
    0x2001c1e03c85000300008074613559580c46990710365202100d0041203008160401414541602845000c414a40302d00c0d890b101607038a896469005140c2514400d40d103400c280c0205d444242c00c20003074000d8645042080c0c0c00c00c000c80d41c1d0003e855840007030046401e000c0000701c00401051103446140c0b1100d4140182d503090303403110020030b00b54600004003c0000c04600740c4444c080c24060140018082c0342c8126801d120360b0130318258441d4440303403043c40c103c0b80c10300c000c0c80080150340c004042d040101d1010740314200c550002103403d800c80c0820344200c0040009110301164944c040741d008141804048400c0c01c011511084100e8402c40402c00071401000154403450300550321007241d10700720122020550b282e8040d40c81110b4151440c0c2900d0340140441d15405461a1300802000d402046071604064003d0310b1703000e1421500f00d030b03800d10000030303890104804000c1c41c3c400e080c1e003d649c81d0200d070140d000c008001040e070041480f450700c0d0440c00340f0b007000180380d8240e410340d4980340c0c4207104543e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 965031807 1250 965030557 965030617
    0xb0609150a170c0306090610020a290702010e011107020d0b041127100303081f050406170d170a0b06040302090a0221010803120c0f07050d020c0d020d030318140a1502 73
    0x5240003040b0f030841c0d000d081d412f080090740301d000d50516800032440126140303901d401d5401058034039801010030840c500060b95040350804450b41d000030f00310503517561400c0007a6500c0f50000d400d0b820148104080ba5a84003441015542c80c2203418500c2c42511030400d0040480641d010050200700c1c204049408122290b02080c000c880019191003400d45410224065800035405603400d40400000103000c0ca00074000751030070148030302c0c080c5e680c500d1000602d600c98402030505015259a4840d10065840700c0c011170300615005040c100351410590303040c00c000d42c0300c6914070900c0f400f601c40900e141840c0c002c1d894100e851140c0150304041106540e8184854042c01240c0e40000401c078401c843c42c800000381c84041d00410252241a41c2030b840a402d00c0114101c19100310849580c080050740c0341c0b1410141160185000a1b0840c0c411819008088102c0c00260084800603c4c0b074010380e200080142a441c807540b42c400e4546002d441190903070040d24030348020204148600c9030030305114 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 965033057 1250 965031807 965031833
    0x109050405180111040320030c010f03020f04060c05010f061818020a030303061e0f0317160606061205060a090b060d0507050307030b0609150a170c0306090610020a 72
    0x500d803001594000d42c8502821207100082074034a09001003420001c0c05010200782c0401003045030780398000b03401034000a440d14082000241844080114440c000d0320a5040d03e9060740710745d07140d65507940c5460001d0701249591104a959608001c3c2140e0407401d9402520708554110b45c149603030300c8110310044c000d849510004100e10150045440c0035030380ea00340c0a00218007944000980a051480687c907a441c5011b41d504a008009020442c4000190b031200c110f94101d900301c1e00c9904040c443c65424841c40003100740c007030304d14800c81d030610203290700c540112421610b554030b10401361040401563303002c94000b980312014403c100000c40140c2c228020b0104000d002c113150049030300c000d80482c0e0007070310904000fa4000c0704011904d901403042c4c00c400c1e01c0c2190101d04040820000401a20391005491300d03828000c9408001030780070740c02c1d400c1292850086440e0501d07041304000c96507002141c0241c07003810301d0004640141440d0429013150004c59015004202003601c2d004098203403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 965034307 1250 965033057 965033071
    0x1170c18060d020405160e01020604110d031e1d011427030d090e0c030c07060f0e011e0f0e06071407020a0303030504051c230d1107031107050109050405 67
    0x7010030400b0041c0e85900ca002d00c0341e45065000650800700d190000c0c03404400156150665002d0030a1101240070340c448030f403406c00f040310300030502d070340610701207400b80301c0f0141914030380c680d01c44c80e890f075141c00c05407400466401440051015503050b00442c2c4803484098207002c1c00c4000c02c41c0f0448070b00004400d40c445446c0d5170300b030741c040c1c1c0540000c0b902e02281d15031460005151180144030032400c14084075080307507018894600310f0404c2c0700000014410b40b0001080c0a6540e004020720840719000420180d14000007003040c4030010450182001e90039a018001c3c0b85843c200c40c03010031141c842c000c4036080c4500102030036520702c10191121018002503030b500402c01c0c030280b00140d42c0c01c944c3d8000b5610076030300032510303040601d405464142200d0080a0340c04072031401c074110b294401e50700c8040444288818200c01c44002c0038080744c1c0b144142d82481241004510861012444010440548242d48512400580720507843e11455107028850005200395000c0140c0d1400b0740040c1c1e00024 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 965035557 1250 965034307 965034319
    0xa0612080d02070c0f03050d020d12020304030c050607121407091806030204110c190809011b0210030b1f080a05070302090a0602070519081c110d0801170c1806 70
    0xc0548507207100d40c426030312002c2024403405e000c0c800c1010a000c2011a1349040c002041200703001c490250821260440104000d0b60110010b010716209443c40c103019a040400d0302e010741001d0300001d00f000070b9182c891038100e0924924402620440740c41c0c2d0b1181005998014150341440551140341d000075000903185600c446010001d80d0f250f20070860b00c802421815035890b05030f031100b142410710044483c100b8640c0081400301040e40c08040360300c180384c240f803c07103500020501b049218402e6008065000140100c01c1c2180d00e030035501030014103004440154914800e0309290445660525000340001c0076000820381c90981c0f40c04c5190030031483e05015051004140100700048043c0c0e0200006a011840801440c24001004c0c0781c030360384407980d1041540c102103505680384000749003610329006207920074021510501041110392a90b0f4243d60004800610050284100b8080d9140300341d401480408400d200203880e454152014240d0716500703451010b011607110005052640102c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 965036807 1250 965035557 965035567
    0x8090a020d05030423100e0d06050628060207080304031a06060f07120e190e0405240402011b1101032d1a090601091e150c0b0a0612080d02 61
    0x80e5000003401c43c0f044170400c801c48110011810008007004211011051240e00c1c0e40f0000c06403142001020080e40014003c82c181d210307030001c6000d44c0d40444810040f845140000ca201e04c1c0300e00807071011a403169003242c9690b03480c0c04401d501e0748900d110040c01414030000310040b0aa2085d40603902c0b010040c0400d0814944200008456100ea4000c945400c003a4140e08034150304003c161094000c180e400c8040b1296078808842d08400e01e00503410640c030681e000030200710042001010a0417548546046110a0f8044010280d0252403c80c0072460f0041004d100360300e03c0325208021504101410714802c82000190001c04d42c14084a541e820380c6001510307036031400340c103040d08020700c004c002030700700c140b02c1d907141084441601c100d100c0d2840d0810300200d680e01c0302c48542641c0102003460800f441c03031902070038084059400030f0f514240d5500e00407041500003107509500390207000700c0b1030707030b0754410549030103c0c0d007035000d48441010100c4010001c80c6440e400b900030000c0f82da200514007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 965038057 1250 965036807 965036819
    0xc0307081003020a0620011107110f1c060606031b1b0803071110020405030c090a060522050f010509011401030617031306020303090a2d03020f010b0108090a020d050304 74
    0x1003420f5001400443d44511040b40080380c3c0e01c4108241c044058000c00c030300c942c01c4000b00d207584114000035000d6581e030341d2b496903a541d82c0541e501a899000300001d2105078080351492a4103c0b8260a40e545441c2082c0024142c0c003030700481c140c6420035851001c08a41440c81030703c2038641d0800010b6803119000070030340010b40d000011401010661640054030101c0c2e2000342c42c02c0b083e2000480c1d0203005100c10820f44d00c00248941000d03408492040302030b6150050500101459401301d030b80101c81034040a10006201114945080c070010300380919900c00d41110300b449401c0c8035054100001000401c01c1d000ba0384104905420149000700301e03141d4400c04601240018104064070b500f0010b070909800000400d281c0c014422070001c0c505515001c402580c5171100000d0280031508001c84099200c90f6400000180c8442e11401c07203201c65840c20000d56480f144010808213610f850750034407681d03000c2c860b02441140410001c004140c940d5080c000c14854954040f2540e22062101043c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 965039307 1250 965038057 965038069
    0x91c06050408031803090603010e061f0c1a13021203121e07083601020a02010f0617030313060902090f06041a090a09021201060b030901060503060c030708100302 71
    0x51400b40c840d46469080803040b00c46440240d81074100a5402002441a40d848182c1900c3c112a00b8090310802c230760325003002c6091302003500310340c0c0c0c0c3e143c11010001403d650411911900d207401100c1c41d203405060558148075800f01600d41080e0300300e145501900503e820f400d00c2e41aa940f4070180c0782450190214041c05500c16180c110525030f81210f1f404201c0b44030240c1652086d4030380340c084001e041c00c00e0058182c821802c440b08080600142c1881442c140340b640d103500c540200000c555951515100074000c01c154524a200036051510014082c2c4103a000008161039101c00b9500c0e41d21086101d40c80c0411301c00003116110340b602c000101507910b501449128580444010400d0702c0d10004120442d0480000b0005540b50002c07105400c1d124005000d511441c4400002074050050001a6040061611001140d80ae0200c0814110b2042000c2c40c010a4200000d009094903401015190b2030101c40c02d515803041400010000d074801d00c600c036000341c5540a090a040d49035004904 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 965040557 1250 965039307 965039311
    0x90510170a06170601150c021003051012060f0501060327260c010e1b010f0201140903040302010e0d1205031b07031106161e2007050306070f05091c0605 67
    0xa82e00800c0040040085450240c2e00c606d00b20718145448008640c0042d00007420000b0000805594100146610200000b10300c003900360b0800c00c0790300d0003107440d10360013403c110701440030034604110001881900030300550a016410360642c0300c0007081a03da072940200c2c000350a6590000d0b1410144464102c1c201400c502c2400c010082e0f45e81c0b498681590944402500001e480d910404021540001038181d85948010920b007510465a4280c8100d01600b10302c1c3d00b904c0342500b00c40901c104041c2c000700820449100380c952080d0706029a0800c809802174040107880c80c1460141c0d1440300d4400e100542d401695003107800c054400b00410b1440603045080c08a020500000148030f2200041001c19400302402502000307010034100c00800c0e14082c10122030341680c0411582c000c66014001020085d64020b21081c00701e260110f0303c1c6c0c1e03200428446c90b402401807101081c0007500c280596602c0711000e869082ca04901e0070b0a10200320241c012043c5400e03080c550301c200180301406514 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 965041807 1250 965040557 965040599
    0x70b0a051306020a05160b04050112020c0607081f140103090f06060816080d0c14101b1e05160c050306150a0f05090a020c07080601060f090510170a06 66
    0xb071304c4920f40c9860307407074004004204105405219420401c00040b4070854040c4c400c203117400000d040c018800c45000c1c0c0100d404000300343c0a09410031000a1344242018854040c61840030500903290344610b600da0b0300b5010f480310f8100004408103a6501981004001c035218440d03000899601780c942e10203c034044d030010030168000f48000c1d403003189012102c1c0d018142c0341014100701e0001020140c0042e000c0398004007081241c1107440d0b074120301840f00b0310b8864107420b0180501741f0780803010b64403010702c0751624002c40c1820600e030440d010350381851b18100c0602c2d2141031520796801c1c1c0d81801e030a4009412030300245641800314030341c2c80a0000034003502c0030880501183e403000041210b241059040b40120840a41d0204003d58420742d1954210901e80c80c01640c8000c0342101702d05050b42504510341622410000183c00b5a10160341d0849041544e108850141c0350410043c010140c0500900028140031400071912109075481d0b8204048610000310540d50b4031103a503414111032901c0b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 965043057 1250 965041807 965041813
    0x40215130f0e0601050a0203270d0602121e010e130804090902180907090e070b0a020a1505041205130503100f050a05010614070501061a071a0108070b0a05130602 71
    0x4000710400c071244280c0180003404c00505200718503100070355070301500304042244a85548017251921542c440b040402d036000cae047c0d80c544115410040040d60280d000c421a40360710398000341208002c4410341c1114280c0d07814104840e480c10f6000820208003074084444005440e0040c40000c10800c004d20003400005008030303404565004002c1034940e505940b40509594504102c0040800b041c030b00265001e10200050806000002c14034090680c0c0058114080008030028110b40025020706028410b550701e0401940d1340340c404007680e4003982c00801582041e021101c0f00c5000300c002e0410310901424400d4102d95036000240703019032440301d0140039555240901520400d40c059940c0c00107041c1c4052006500d0f01e00010840e415000b007030b104465020900c075040140a41002000309000c803400700e01c8109440480380d80d5030041034119250403030405031352031502c080350b1098100c0d4860302c09840d4141c1350402110440d448954030f0401c10004000e01c0d24042c100203110f40140c00170b5402 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 965044307 1250 965043057 965043059
    0x2601180e010525080712020a0903050a030309020a2301120f06030804060314060f060a14130f12170904090206070c0603060f030c06031503021f0f030212040215130f 72
    0x8003421020b400d180c103c1c00c0110503803c000b000c503044400301e0303c500e444000040e80d6034006c400446807400d450b000140070f40201c0d00f032181450b50640005168038000c07614404c80326526940e08800c2103055010072079511140311780c45020b40c0a40c0d600700d4160100e50000c00c07c003e10f44080f40484007030740c00450301c01c07a010400340310b01079040c80303081c0d5200ca81c0c20344a4982d0801400050031290f07178011040c801c3d540040e1050085201c0c1a9a0300f144e005281c003103456900c00c40c28061b0100c0140500e440702042084c002a200c00d2030303210290f599800072228008841603019184165010f0f005050b001780c2c41c0e07400c070801601c41d0300003050090b006010210195003080b0300201529140c1e4420020442ea40000b800070031101403a01c8110f03245400d0010741c0000354449401220002c0e48040d600a0700048a6a10411605005113a86c50541d5503204102d407080c100f5400c0780540c68034446a0304100c030000d801818001c1c01389400c0000e2081c450304060142e54108118403031500070305064110508 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 965045557 1250 965044307 965044351
    0x50907060c2a0302031c080c0705070506073311041d0a110403031e031b0c150203090a02150f0f09030a0506160e0d031d2404062601180e0105 62
    0x440c7c00d800461242c9110320301f2041c1d0b200c60396031300518000d0078410100003851204000d03842c4984200040500c1550b50a184d2000c1c800c50b40302c0c4403401c03c01d0101c0c00c1030b4a4a40e1441c1200c01c070b078195074181180c02e030074510214081d040e40500522881490b541c866150401200c50005080114442c3d40c41454501000b14a041800480d540c0c00090500300141d00e0060490640d8175844080c1920f40395903010085d052050b6140c1c8100f80e50350100f07200106104004001003604a142c41c001d0302c61141640d24040300341983d100d480c2032040700f8036051094000c000c4561005040b0341d500207044070254180c6448150030b00e482994030b2036491040c0d00300403942c46c5d0051362812140c00c046460010312012914060039034860704194805241c151891941190744d62082c031803843d1101032442101071050082100385038014000c1e0000b04082c0303800142e5103081e60080c0d1080001d0103e018810307034038180050001c410301441061300591111840400c0210034130074588510001c0700702e0070344078036504 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 965046807 1250 965045557 965045567
    0x912030d0b121615020c1e040e1c051623120711010e01021608030c0f07050f010507030c060e06010306060509041a060303040803030406050907060c2a0302031c 70
    0x8880d01071904140c04202d40d01449000e042c1c12140384135030b0005050412031040f402c0500385d140c0e1075070000c0d4003e0034501d5a0040c0941940c5188255000c10404420b4048581e4412200c41d42040104141d2408000b1600c9140604004102401c030700d1014040c03966004105003da00000d824032241d65942012640b08102000308501c503510030714a45621600d4102c2d5484d048542c5d181800151042e81030300340d00c01c11500c200f5006046940409070740b20890142c4940c002c0280034150b128015000b40088001310780c600441c0c0c0000c01c041951240310005460580080b03c0580a210b0340014001c0031515601843c0701c44480c000140000d58110b1522004035030894001d903000d9450701081000180c124001602045040700311003070780360343c1d22000078035501ca190030011050201100f0b00040140c150402400303801c070703602078400c030390b403102411104507027021806051102d1621001e2084184c041050f00d01201c6006504103480c6c0f00d4001ca4501001303842c04c3c042c0701340000b81000f00d451b400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 965048057 1250 965046807 965046829
    0x132606090120190c14060a090b090111070b0a0219090f06030504021c050c0613140303090105040608060109050a0e1b04050a06080a2301080f03120109020912030d0b 72
    0x904560304121105819040c06091008081e0030f101c56841484e061013800800608031a8102e021603041e440c00b01d4000002d0045030400b2680c000040c0045150090180a080300d2505100750140c00c00d0441c0d02c40c2103240b10040d0260841070b40c02c00c142c014081c40008019402c0c40396445a94049261002d84a02d4810950084041503d44024080141d40b50765000340f00d40f071380c4e441c2440c00300024200a420a80c46034041e41c1d000c00001070030600103441200400448a0f4980280080c240d601c017407585034440c440705940080c07401c03c001c0c0406c034000c04081d40c0042e018504a00b1440d2100d001c104452902d8011001c021001000c12003295031000500b42d00608002040d41440d24103800b086130080380e4080c0b40c0600001d02c00044184400394070039600d02510401c60494002c1300307014000c4560085c042c1c036800d4000c44551010040780002152580403a45811040ca6032070080d0120080d009200e000350f00c5058031f0041140c1c9101080035182c122403c4400099030310170401002101030710 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 965049307 1250 965048057 965048111
    0x80d23030408090406051c060b040501061713021507050d030b0a1a0f040b07170306010519050c012d061203140d020415030c03021326060901 62
    0x90088880405461141681e030010380c40300019032502c0c4518002805082160003554014a4600c0064450145800c0c0d6543c6640121410400045200c1c28041550000d00501010030410521a0017000312568800c0d841282c2c240c00921034103113580010141c5458026801c494100440c0120038000188640c3e0b04502c0b03c0d00b42000b84218820100359158054880e440e42c070007a0515440c550180d4800b210410400c00210f16036494482e5000c40c0d66420158080d51034000d00e1260f0519040c3c80d85c00c0324004d0304142c50b0030303003010b05c0b07501c842d4030190301403849804008041c0040800d41c0824059100349401c0ba0068400c035480b01c2450000c400460800c4800c4141000700410081c01d01d004041714003501450310000042155100641511601040c15003062000030005010030b513280b004111651b00c3d41d010300000000741406c400fa409880400c0c038000080c00b400304101640030a82c100c2d9401d038202101e4001048000310b03030400500301d030b000c8140c0c2d440e41141901652910032521000c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 965050557 1250 965049307 965049347
    0x5211e0f0a060f06150903080d020c0f010204030519080f091807091410120e011d010203090c0402040e16110a030c02090714040b030919030201140f191a0901080d 71
    0x140c10140200484107520012300502000212000010115011210f540700c5020445444600410010703000750b009100c00d482d130b4065420985c0d02e006071003c002490642061400d804d080141c40c1740e502c10f1303011001c100d074800c07041ca140b060780c0006020410b10502003610b034040300302d10b041a400c0d50226041c00082c424103825110880031908000203099481d40802c0008120190010250040084203050181e42c0e501d241409003110741500114461340481041c2d900d000100c4083c442603028038000c28400b1181040051201c0b6a0603e10700e007070303400300d241000c00302044c4141c0b2030802d203000205070009000c94680005509041300096000b080500d00855040701c4078940309001d024078010b030010408000041007240a0800c4100c002132a0000281d2211410b8903000e402000300b41441040301006400040e490501883d62070310585040b04034074503180041a0700e030020440710707600300701c11801d01c40c0c0a1480d8854040050182805000034103800c0c10011001d00280c01540024500035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 965051807 1250 965050557 965050589
    0xc1207020316030305102706090207080403020105090d0b0c07020405150108010e0709150807030507020d0e061606090f0312060609060809010e061005211e0f0a060f06 73
    0x50951465801c02ca805140008a0761201e80200c2016031060307000881a407041c0820440c0091080ca80000a45115204001103643da041c00d4080c0d02a40d03030060105c207414002000994040c1c0e005001522004104095280d016518000310710303c15a40055800701c0841c4000442c1805d119203604030120710381000725152030f900005e00c8810140a0788800440d000041905035019500d00170190020b105407c40d80820781d20024800c0b202100d00500082c100404070760901d0000c40ca0114203d81d503519441c0b451800014030045905c0300030000c040380c4d054407000003c600f01e445a048c82500c11116800c41c50542e080080030001c112212070000c604e030002c101b0100381c001c5900030890b219800e0400356552884440d030f0040c010b00c2c0d1104a00e002d06801c20110b01042500001a81c41c11100820b22880483d01596840c1003d0040310072540283d203000e201c0d04400d1002d840f46032405045a01420a00a20a0804e00101000c8034030903110800e0381e494440381d000b818040c080152100c0429 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 965053057 1250 965051807 965051827
    0x40605060403060903020a08030a020a0f0804020102072601090f030e0a14090627060a560a08060d051005040c08011103101502030304060c170c12070203 67
    0x181c422444000c05581d0ba8480241c2014024811414613a801040c09600d03440c000b15440301075880407440c4d800044d102600500c1403070140c100507002d5034042c0d005100050519080003151140c0e20101d440c1042600c40780c1e203400e8030900030301075494800c1010f640500c40d1460064219019500124852000c0d10410300441001880f0130303440760011aa100104e85554021034241a0042d9001c640308081e0400b0000d11300186c1c03821400350344280c5252000a6880500c400301800c54504004400c9900c5241c500104c69200700c081102c030140d401003ca24012030482b0016250b00c1c0c0c9040a62401140001856400694440c2e00400556031740348080340e15926162124840001110740ca5500c00c046020300c01d030108008040e11703000d8000c00c41004801040b0301c040d081125018001c91810101280405056100814000558008500b103491b07a0b681c00c4050007403000c0d0f480c00c010180d1010455684070003605401043d10540103540da856a52046812841c000d10110665004000001071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 965054307 1250 965053057 965053069
    0x30d110f072412021204020a141e030304050d0506010e0901020a081f050901080106030204050c0724110a0e01021c02060105220e010c0807180302060a05090a081b040605 74
    0x542d950640d40c000d4062690080c0d44920b985032010300180d201040722021400321640140c000c40c001c0301c1c0494015503800000c50001416204036401440d510046143d110001d801ca00805000409803401e2640f1071000c9860741c0000d44094420354400c0300100000c445003400503030800c40341402035140a40e91603001d090450041c01d100c60301d56404a40010001a205031407000c0d200007002e41e800d95945c1c0280074044c14160109900c2a0b03c0c00011401c1e9032a8003044406156010428450b1a003500316204214048112004041c0e078680907220b110f07405160003081200d801c0d813220031010101c0b200084c070700785040101c03528070ba260502e0060410b0300020024112141128135900108001c256540004103001158828508107a480d000c1440190040c25010382c19580d40c405caa0b40316213027240c4000c11a0608400760010301d100b4070150506400404036030a039814118a0b02c172494011070000c858950240403190895000e100415007200700d07100c94454112030030301000b8145400a11 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 965055557 1250 965054307 965054339
    0x70602130609060f0f050706060b040812070209161214070806180f07050706050a0b120d09090527070503100b0102030301091a03030f0706060504020403110907020c030d110f07 77
    0x18005c2200e01054040d00c22021110520384c4403505000c0e46a45201c0000d140d0494014a0706501030495080c400221480030350300941e40003001d1a00940b00d800c0408900c0c6240c0e600c0a00708121503100801700d038200d00800721240c00c0c040902d286864901e500411441025041d10320401c1600c214101c0e081c41d80ca9155044407401060061603103482070152a103100d81440201014103003802c01405141f1507001c211000c0e0141c0360011440c10280c5955161659641914081b40c0f0040c030511200300a54003941d404000d40780000040d07080d507000c0c140000840381451070503a02000c0e091105040600c260960440900740c01c0c040410034034000303034980c00705000700700e81705a541101c001c11141c8103a11020702680582901c0d82d407021503034110565031103003c3c1070b90690f050410000d9281400e00c2180c0403a80c20100ea2980d04044030100b0070085030107040c00e41144264500941555014440c500542a00703850710780f42d2801082e0f000d424070382c019810900903088100c041188580c0054101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 965056807 1250 965055557 965055587
    0x1a160203030f2221050f041202040f090b390717220e10030809130219020c0301090c060c080d020406050405040b101e0309060207060213060906 63
    0x301c016600c0018100c0c4080000300a01d944880d0400300d00103216064540b055184404c6142d282d80b95800c1c0c00c103803401c0c8900342d07940010071400c110401c58000865802907960303100a01c0070401d170405006241c2994240441641c05103503100c14030a80442c4400c920400200c03100102c890451070b00c04031011f4822685002c45410760008009007003002c110390544402480c0308005841d0030005a00580d5014030315594040c82c2d02022000c0307051540d0681b680c1c03248070f107810444452800e42d80c84602e1500b01711001d42c4c2000481c2440d200401c0c450015103000681c0c603040340c00004044600914000c0c8185055009925201640700440c22010080058074010306000c09001e00501d0b100380c41b44503034a20158101e02c0414086001baa000d4002c00c1116021038090003640c0ca0300c0100005260a100902c000c01d24201014240c644c258100d000c0040d2a410300054848076500c507241a079020210464409900280c3d401c90056803105100c054222032415001250500901601c2c107050f1a0003d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 965058057 1250 965056807 965056831
    0x120302070201021005180d0c170d0902030703031d04110f0309030403050d0e130e0606040c0210060f170715050904060302060a020708010c020c060403020405060103181a16020303 78
    0x100c0a59008000302d21074440d120804108514000d40089042d008010226100d40900d0540071180c2d03104d000700804680c4c0080380518611020074000301980e11000080d042c0c9604e54900202507035040c0305110046000303441e0304100c000507090109031040e150f210f42d4462407420341d2503070003850003606031003d424488502e41d95030780310141024558043d503030004203a8403031740344507107800c5030310541e0030b10303135001c252400b030440d00c0d0901c210002c0c0c0710303d881e058500d079102d88006902032800c0d40229058034241d0040d128239002031404501a50f1480d00450300c2c03006082d0082103060399010f20083c1030030801c0040d10540d818050b16814550400100b039040202c0030840c0d56450b90349900c0f0300011b40c1e008090075034034400d54601070b454605500c15140c855181c460ba0b40002800801d1151011070010900c1d0b1030310b4210703400c22009280c082c0840307040599039030040c0405013a42424500c0280202802180390f01c0c83e400d02d41d81810002d082c0184040380a00f0a0101d54000090340d401048000e00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 965059307 1250 965058057 965058067
    0x2041a0918010b0a081005100c290910050105210106090e0a140708030d0e010e03041d011d010e09010b09180c0d0203071716060f020d0804120302 64
    0xa06808541a6202140c2006100004450100c10010206130a036034644c120a40d503558036008010005128050300102100d0104c2da00b244220246165184240d41041c5144d1061610741d150f003102090323607120710360b007041400300d040e504101c914100300048206005941c10a008100c0c0e40741031080c00c24010810040e03001e258070303080d000400608040501005070b540039400b4140e0385c04e4103600c151040004040c0400407400042082000ea8a00324010b600e41a6120703031900081c0840554940c5555850703004001a5030306000030402007a4242401008191604510328100300692021403486047d0601140b12083c41c00f002d41112040d0707030012160740e034904240b030242c103000c0004c681c4910f0505c2041070550744600d1600c4250040c8044418440300c11040c030209540c0404045d601d548202410005604000511502400004180ea00d48442204480e8016075141c0000c1b0101c0d050400d00e0070120350400556580300130b641362041160409071604107003c201c89009000300368000803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 965060557 1250 965059307 965059309
    0x1112131802041508010e13030206011401030e0d0e0a14031e0a05073f022707081e0712050a02090d0602041d0f01050103231014030102041a09 62
    0x7058800810f01e00940344040100703104001e0681c1c00034020442c508551101241d000c07000800403510003585a002407843c0e07420111040da580c0c00102401e4105611041440c80110341403040e481124015112003c10000314410003c01501680198500b42e201184800c060351740081c2d5103040c03084140100000d007822850f0340b0b007040e10a010161840c0b041c89c8000800d003804000040e1061000050690002c4911009120003609d2500306006600d84910f80009860002070010040d2581040c030a8403408000e10b0301c44413007044880a0114041c1800c010b505101890041580100c403000d074495894000302c050700c1c1100d00d5004070320881d40d480000d04d107109160b04517803220070300801390760b0464021718001c0040e43c82402200d00040404032901c4080131110107150091034100e10900d41c1c1e0303080c100110f0007041c10210045100c501c1003000141ea0110790416801100702160790509103040c104003840403103480e2900350080c1c0c8108020040c7c0051100388042d562404010165240ca86c44 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 965061807 1250 965060557 965060561
    0x302060906041d0907150903060b03010e0d020c030c1002060f0a0b04060b0c12030415050907030f050a0212070f030b1323010c03060f0303120f0c11121318 68
    0x1070814084800c3c01c41e03281020459041c1920721418180040700c00150f100c181d40c8069003080015140400d02c480824400511341c1d82054556800c05000050800301001c60355180c10750003150300d000360b040051040002c0c1024420100401d0040e61120b44044a10388000d5a80d4801400d007844100380d00003141580d104e07a00044c280d500020414440241c941c2c1c80c101050340503841d41130759841003803460008148140d00303403403040740c22003a88004000420480409418018030410590298034004000520705d11800444680140b0090480c1801803060006810080e1b1140045501c00c8000300080c3c1c00c0c00b031f40142070340e510020705034440d03d0b05c8010500142144134010030f26900c1c4030250780826403040303900b602994484001e002d0302619010070342c200d4046004004400c1351600c000c2c00840d005105903a03601030310800c0014032020300c8041008840c0c0c0f0340304102c0080c0070066a03d4020300700b041541043c20400d00214034101088a546084800c0b91040307244100212408902e1000c0b15 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 965063057 1250 965061807 965061809
    0x310804060f0207230108090d080402011211030a0204030605070201050f07032415080106031a0114070b0a2c0309010e030319032a02060703050604022803140f01030206090604 76
    0x910130310312a440c1c00c1c1c00705454404513402083d00140781c040000f14a05d4001804502250b03054983d4041916103800450b507000c0384030b0100000c4ca8030341d05264584002c0b580114400e0a03680d10050f10389046147c41e0040d0b55024001c070b0210380c10181448902001d00503541e40010503400d0000740c8008002001c040001220300310800c881d2035950003d88401840b00e4412640c0c081d82d55605640e8840c802034045030b46080c420480183c03240060000365001e026440c002e461a19045800c0c5030035503481c90001041258042c1030319403508034038411b444440c4548407409103000701052120444000c0301c3d40d2800740c401c010b07041001c111140c0d03143c0c0c1c50601c21180ca07000e03168110030f2441c032584006000b40c11504191a220000625040740c515050020103c000205901514298035901e40c124043c007000780c0317120350095003001a41f010b00c400701c00c0e020030607401209000f00040c900f40d0103400c0703440451190354070078600c0b010004070010749450340703064940c1118841c2d1130b1040140410130034001c03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 965064307 1250 965063057 965063069
    0x14060121170c1036030c1b181e110d020901050903030d021315121a030d0305010504060b0906031306141326090402071a310804060f0207 60
    0x80c01070480c201c0c64410031400300000e8070700c0810b40c078404440701010303c25200c4c04001d00002c80f0100c4040c0025070a1902402441601d14455602c42e2206903441703584020f40007003162540d43c0c00f06600d4503881614194149940303d1010800c4420300c411800480c0316401006d8603081e400540f1880c280e00a4098440000c1d014040b6910707000e49940600080d480481d030950003c06c0e4000015840041d0750099540881c00d9036044856444e40034204060983c0d072801e14000355406400e04040e031003c00001c640042560f40c0802c0c5035140c9001d02c03088031016008003000c90000c00c054550392b11010103c0750060400c1c0d130a900c1c0305c844d80c00c4c0000101041114a030310044010144a00c1320210280c07000064020307010902160080803000603e182e1424140000c07200c00d11007a0301c3d0f8035095003c3c04219000d40d9010300b0300b511100c09845a0340048420141c0c18402c909040c16076101c41c1306806008038213a0341c0c2c4070000c00030b440d00142402144164010805101c21000015109100d22401411 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 965065557 1250 965064307 965064311
    0xf0414061306091703030618100806070302130b0c07060c0809091005121501121e06052d0411010c05070e060411071a07050714060121170c10 62
    0x81c44140052182c0b90912811001481d418881300c1264404800c5901401c2c000300305141e00300c00305100d541c000c60018002c00301000b616800143c0c81c4424440300d4800e00e00c2d9a00103a4403489015549240030ba580c00c5018040000d0004131504680051284251400f40c28442c2e065002450b0021942c45103814541e00131014030244107012148202410a40f40115680c800385101c0004070b954072164000b07d5016080740f240100820942800d0590000707014154034482e60350313040404480d01d0f025140c102c0703109503140108104a24980c007401c0d02400388100c620b891401440504101100180000e0840310805820041a0303020b0100420310030760090682d240036503104100d0451800450305540110b052420b500c1403001603004803031610f94001000303d02036407003c0034030220000042200040c0042000001c000c15500c0003e01800e0503450005e100a60400c0440b00c1c078004d0070720b480640901083d82c06c074001405e074207039208196061010f641d11058280f000310302d000e401000840c4494 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 965066807 1250 965065557 965065559
    0xc04090c020c1833030118060b030a1205030a090f05010510120b01090e010b21100501180504061d06060f03150c0921030c0d0201020f04140613 63
    0x41d802044150700a81e0031500c80196441c40002c11620020496640d0042d10807182e4040c540111100e64040c11503c010041c82c044892401090031a8401101c40c440c591070448040204201406040c50311102138002c0d01c7c042042d43c2d900d13101141040c3c00c003418460003000044a65085910803402603422400c42095440103040403402030000b42c42c41e89805d4645c1c5e2002c100c00c04506203107000340c0d1f40400518810707880d20202900903c14001020f481d07540703410600c5010364815101c00c003e0340090004848014100c3e94562030440c00c4912000741c03d06003401013005104143c04103a180d8012032003c139980d907803031402000402c0b800b003201026003e1b09410814018000560600c50541518416040742d503003420959280002e2603900502d015940019195141401c040c00f0344032006404e039050204070483e01081020052091007881e40041800450719000304080001c807021350008600d4229a0308603d5a5442103001e0f109600410031401807075522038000300c07800119035507400107002e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 965068057 1250 965066807 965066831
    0x311190803090105060906010c0303090206090d1419080d05060d06060b0a091a09060d1808180409021e030f0111190504140f240a090603110f030c0409 66
    0x1d4006403401652980ba0000040807402d100840501404058458044c407540e15681140030b0b104000049810810901007240303107440b400700103281d480c41072030707040c01720034a080c016450055102d0040e8048980c00580c4000320b001c61040360a01c01d01c280005c03034aa5030b4040441d0300c01c0c403040002040c081c40d0210014803141200083c14580a080c0e40f485920780c2e45052101c0088483d9a16a803101030400504510b89080300c0141030b501c44035032010420500000b800e103a40b07401044103131103082e0002806d02c610724521020000d030700780c102e07820002a04140c012404c188400f048800d4207800c20b66140c0c88a0703070308000343c010551039031009104445605003e50215001340f2101c0950500c62840d1b0400240200b003914251540290f0b030b2902061594100b002c60450412965082554074035141d81c41c00d100164201c4054020381081e5a0304410600200060000e03441b2400700341c0790050343c683e03aa04d030340215000500d144030025100e44544234101d241c1d1280d58004100c451400b42d0303000c02 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 965069307 1250 965068057 965068073
    0x604051c02090709090e060105030709020a02071e180509120d11180118211a1f1d0604020304020f0a031109151f0207050312030a0b0d0f031119 63
    0x50350700c402010300858855031b08156450380207008280e070540180d2401e01c00400154042c0150660501c101c1c0c80c61551458440b0380d0f1813407211030506860f0300d803005002c0c900d24010107026a0b034544504001a240000c1801c0d1039201c2074500030720b682000115900d207040d0710b0300710034000c40340c410074123503144001500116880c3d00701003454085404d40e1004039100a08541a600b00c581c4041e401081c031821100c1080c2c020a4039000310f860443d17400359445200c040b84003045c07141c80c00020305d400b0711085c0414115404441e41c00000d0f01c031006061010040000d0303617440e0708108150350150722500c4a100095001c4841c540c55a001982c7c0300000050020444040703002900503150011191194003a1851111100c2d0176641c2004032050804510881841f1400184c04584150742e1000d032a40d002070704105006c84900e92403a070110500c9250301280c0f0940360944004c40303c905c0742c210960ba0350980705030048000f406006120301a01e840500038000d0b0204146a4101d4080182d81c914100c1c02d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 965070557 1250 965069307 965069309
    0xf0b07081206010e2d0d021f05160302030318030f0f0706020d0c0f0e012a1506140406050303070b130c030b072a050304091518090201110304050604051c02090709 71
    0x5c41d071901d00000b0452420072022914a503a00640f202420300300d18448010001c800302e1041d03003001310070400214418041e00752940c1c3c0340d02c00c2c1d0282d40d9a042c9401309814500c2e00b024540c1c0190001c0017044046088081240c104640e20055980c5802003410a68001d01400b91813081d02c508050201d42000d511070f8034030790808a15201d40340c01c0e4000000444110402d05850003001860109440401c04000c50100c5414403032450000e036405640312650507907295a104040700340042c4400a803514080c0648009000260011070400b4802d44803a60325840c041c0110448226aa050f0401d115a8160703c0000d140c0000e1400410708280d10010b03e0491030003101e4180c040c2031000d6861020300c440c1d085140076007000085007403a0808281c14001d0040e60041080171262040004000c203002070141d07444407014000152100980c00050072035000103000d0480f540040105120310b83c0ca45098400ba15425613240403010040f0390b800c0c2002e01d0080000e94840720450401181070b500160f100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 965071807 1250 965070557 965070619
    0x1e010824030d020a15050f0402090c090a0303090515030c0d02130e040c0e090307170d0f060b19021609021e0d06030c0f03020918070b0409060f0b07081206010e 70
    0x1740711a104203900022140103035a00c091405200c00405c002d45803050361241c026081c0503040e23140181e220005401b007220303a8411030101c1c0f000d1504110518060640710000c02c4681072003443c3d45000f5000c401c3e20f2254040408100750301081c0341100d12407030420360014000339040c40c2241d050909000031083c51a200d400709110400c00000c0311090084103032104503500c42065403000c0c0b003a50703100030640c0104199044c0169034031400d030254541406010000c20904031903507034403902e10961102c031181c0c0020b070000f5035102d0f00214014984d00d59040c0100c0da0345000051304c0301186015910858520041522441408207200c4c03030798a0181d00c480d04880c0704100a00c40c40d5a036000989075031400348006075203c880400001c120001c0072205455905038034081d1440542c03100f034000e981e5000360300300010059540005118210b0b0307070942d10003d8401241400c1c10301c48655648001c51040a451892000c4043d0200b0501d9018010703030240248000c042842c2e9100d1500d5030084015204030b01 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 965073057 1250 965071807 965071823
    0x1a1512062a0702040911030d0905150301050108070c060204031a0a0f1e020304050c031f050f04110607050c060301060e030106121a0711100501051e010824030d020a 72
    0x91449812020584180d1041c1c1e88000d041c00d0705074080000400010b4010303203480d02d00b1280304986640600c2034a44840d0701e6110b0404050800042c001d0b07040160a515155000400062205a8115440b1903001c3e4103407804082c55401c40c40c02c074000e80260b5100a01e060b149140101c40540e508201e1881600d5070b103000c0103c10030b110f8080080d1442528420850401140e01c0c40d01d0250940055078420b008004884c420b000d42c1010a141804141ca4401000e80080d808191651103015898000e4000c0308140d07410700b840e03169260780c86a01d03101d0510680c000100b070810484e041c1b0110a0a00c0000d2841c0e45070f41c1c2d2000c000c0c06d0004841d0308907109500c0d0200103d92030392004004000c40d41c2140c0d00400d2070030780030800300c01420043d00e541c061060b501488042e9034402c024050313101e5000b00700465254544020720500310601c09111919050380405201ea0380d074003500860340141e450100d070a851170320921141030954222911074050140d4072111564940008010925901c101d04d5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 965074307 1250 965073057 965073091
    0x50d0303020c2b092103020a14031c060303050909072d090f080d110304030c0b1201080a02030a11040914011a0907020a0f11040e010e07050d1a151206 66
    0x2044900342040d00480480d8450101032960004219140d090726071b00c280111100b0092540f070300071081c0b11075075030708080303920008600840060f5004000030304290b501c6c080c400d6500f16a000b500c14050740a07110702410800700040d007000d1043c03500f140d04100890b00c00c0034101c400503611a10600221003800402d030031590024626155000750f0045550003000380c11702d5865420120b84041070a17511030264031091201001289482002400030208400d030f840c0d89015080a02d42c10742d0050307101c075086401c20790044000d601c010440c1d48980703034488014404a682c8000003001455045005080442040e050300344030310056011410008002e890049083c14807801c0010418007102c008005070441c0d03250300001a00c0e034699076a5603100d01b40d025800701150010400320f843d080c00d901940e039140c000280403d1001e03c420000b40406590601c004100b60b1588400b44820b01c20b01c411418803103002611000741480e10f100b20410040100c10080440e100442e6200c0d82510114804200010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 965075557 1250 965074307 965074393
    0x3060504110a080402060c07030510050108160b1206030f010c05070b090a260909040503070b010504020a0903020906150a021b0316211506090b090c04050d0303020c 72
    0x420340d071080105076600c0143d035403140d00340240c0350891402900d66203c2c6100100014200340030640694841c00c400103015031402030341c149002e080f501140541940d21100b40420051902201c0d2148201d0031000243d0700c8244c0400c1c5840000c4919040e15480c2c0328025589542c03100c000c0254501030a811505e80d1100010b998071503d40100007031030313140c40e0860f003410300c044420f00540b2181e01d007007880d04054811000c6800b00c901110304031615080040c0c505d0800c45e4038110a400752006803011810000290341c0500303984802c2c04003030302c00e00c1200700054907541c071080104c0c500c64048210b682c1f5403d1001019546040d424034001c00e80648a880030700034100000c040300c0050300d1a0200355003515042c0e524007e01c0d614007052405050301d000000110388012900300640214034000114503240c03c0100d070884142591051094101406000a41d8100070503a81a110308684030140e070b01c0c4078542a00244a20300711110b031b901541540015152510b250708190302090104a44041c200756 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 965076807 1250 965075557 965075591
    0x30905091005040b0f132003090c3d03050a060b0d0914030f0c060c0910050703181509060509150c2103041e050703030e1c0828090302130212040303060504 68
    0xb1004015a4016101039a02d132a021082503642c8106e902000d0315031411840c400b80b112441d02a240c6003007000c1202c3ca100350b5051040b641d0ec0052440c2c1046294107204542c4e402c0c2c860001ca81c031005407940746213000e01c241c040740720142a544c04100c0360398601c0342e60640600e4000301c048001310f000307240000b5084c1404008135804400000d1110380380003003043d02560240c0041000303070200460001c1c80c6d01010b0040180d917010b401406207600300c60ba0b40b240003e00e118144d8000710100502400010802e442e048580f10324561018a03a80d201c004083c940c0c0e10705450f00d0601380c0c2d42c1d50440e1b00c28032951081001140650300840c150001c104554008801d840d0207040c000b81150300100c8208080f0784504003d00003880001c0c224505200c102d5024544240d0740842a54207200010707401e02d502c28400440c84502d00c4556441411001035103014201c10391520000c5c2c02180092908034200040e58103c54103422130702c910344c80c54145030030000c000b0701d401c0c090306008034540342e451003a101420f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 965078057 1250 965076807 965076811
    0x9062d08060403050d0f05090f06181903030b1018090515040b06210612070e010b030a09060608030a0905150d1a04020c0a030905091005040b0f132003 66
    0x1407280d91200d94013140c00b544960000d5048580e00e01e0640d0301e6588501400d40030b00d010078000c21440d0310001c440e41c00c10001618101121111048070240d851001c40d00c0d03c00342c040c000d4103003072080580c10300f03902904503800d0090f400f03c2c449049400042c2c114404059002c3e04002802001c0c1d00c8407010f0f0100e5800b61030304003003402d0009001c50185402c1c0c0090b030f05804080c00c0f0030700f0000c041403a0000700c080240c0740507000c04010200586030400c9914100a001448000c205541c03a0000c2c568045906010b6204011000000030b02c103601160000c0d00c071b0651003001004074641d1800300c2c984070703042081000d0005d1051480080d03285014011b5858a42c0c012a03110b21b0540350846070401841e02c04601c1c03400d0510642070112513a51440548501c40d03244001c1c00100c4590300c0c005001c5801c0d900b0641c41100d040007804050981c440e030800a480007540c0000d15189004005402002d00078a41c2e0303840f00f00e800c1c030300c5c0e0761807030703035002141c084540e003404c0707016070015038517105640c041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 965079307 1250 965078057 965078069
    0x70b040812091516151e0203040b0711010b030703080c15070f050913090602041802070b010306050618040c1401090803300c0403150e1b0a09062d 64
    0x1c00c0020507109040038000d10003001071000402038241980c0c5c9440900c54040050069a40e0b190b1810861002003a8031200410f400a0704528520303160342d6400b0501d030040c22440411020f1341003600ea0b01425408010403040050407a40e03060307580c1c0b078101c21940c850608203c040c020803074041c6000680d01c03805030203601030362242c0e000002c40610440b86500b000d481300d54025102ea4005081000b1446011002801600d000d44ea4500b000742c8110020b01d0400d02c682400d204001da08081031901640034103680c0e011001044c1074403600700240270703036800c0f41c03c0003007840400d81072104005400350000c0c00c41e0300303003641004021802c2d030044d15034009a201e0840603400400070070a000c1e100b1814818203901c8010404000440c8203c1c0705124441280e403a0481d0310001024403d02180d07080d000454140407200b400126020529552142d40d2038030402858480c54030314031503580d103010b03200c000b07040048420414142d5502c0101c410300c0901407400d5100d14802d456850001034403000030142c403c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 965080557 1250 965079307 965079319
    0x1204020a05010e130c140c0f010c05031003170c030a1206120503220b0408011a1203180103020f07030c0b1303051233010315061d030f070b04081209 65
    0x1203600c84044c05400b8504a04040102c0e80d4104041d40c480f10000c2d00f051141c610041000043c41c2c6034203400c65501c94040000e0040078030400009501c3c281c040c038240c0383e011554607500080400e0460b00c0f4011181c41900030b00000ca00310081300c0d4006454450b4292045051208907a43d0242c00466410403501900c0ca0700304100b10351025030350941e2007030150901c0d8008000d5540e07600c00b000d20384e0000d40128482d41d445031800ba0403003c2018903506c1039442129004054004003010396564070464a20740c1900c80c0c05140ba900e0b50303000358180e0340b081d801e03c40d140d070740c4070000d00d4002c004200c001d400700c03011220703800030461481511a60414140c1e15845071481c000f0390aa40c80600d0384002e007001201c01c030800d0140c903103600c115401c10000e0b44a40c140d0241001010003d0244c40140b40c5540000c001c0c00c20400503264841048000803841c006051503104094011904004040500310147e00c2024000644a58000020011240d80400b5202c0161300b140d100d400303a104000000c0e40c809 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 965081807 1250 965080557 965080579
    0x20f10021c140910051b0c120f042d052701090b090c090303120405072c0601020a0804140402160c0302130501050108071b051501060e0603040b130c0b1204020a05010e 73
    0x105020001301311f161042c004440900303a030480d0003d40e0380d004640b050b11700700021408005c00d2549914441007039030362481064071202ca44600d40d541c14410704c1030381c1c80340d6058490700700050580d800a110080910241d00400d684400102c00680945005030f0b01a944030000500000740c010281d520f6000c0040240d80303442090180c501040340050400d81d964020701030f002a910b441d00b10f840ca0507400d03c230ba90000c0306550149100c01d00a00808070b90543d007200d0101c80c0020760490495040e01c2400d4103019440d039044e4003090003800340060078900c96260121940900c1122052035085900c22142d005a441c0c5815070300040e01c0c028810940403034244400f046055001340c0d00300001c01110414401d400007641c039030301c1c40c1c1928010101d4401c0101e40051000c0c0d9800010350400080943d003003403541c00d09944000300214020104003124022148200c200500341050100500c0008070340741d1514140ca074510442c2d503013074030101d10440c04100300251950103400b410001c0328000302404900 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 965083057 1250 965081807 965081851
    0x100e0f0718150e101d0609040312020d020c0f070f03111e0607060903120e03031b0c060703020d05220311010204171c020f10021c14091005 61
    0x2800d04038042e220081410302c0e001c28403451002c1c1d81d5208a4080e10314544a40c64110302c5c490f039440b2500350303194051500303042080c1911030386140c0d80c206605d1b02e040002c0c0300310010284000d01502d881412441e000140c5036240075030008410180c90b0014095903a0300d503031360a6420070f2402511008100c031411a8000c0003916001198141d600340c8a441d640314803404070000b5007290700c00700c821a2116a44c0f0062010700d507010180c031100d240715a1080104104a400030b6030340b070100500da0b46418502c5040009120714070816107883c0c40d021000c031a65401c00f420058042c4d0040785030b911b145403528000070100710310b010040000369051000e5004041294404030384400d5003100c0b0486c5503408010002e6407001d80c85009030041200000f07409000901c4000607030480d03203504108115400b0400d4682d401c01e02088030980c500100400507507070358611506800c0c0c0c10b80c0800c4078204925000080080d02c1a0088652080c0901e034140c0b00b0a42802e01a0760444900341c5030303d0040b4510317800480d44 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 965084307 1250 965083057 965083061
    0x819060203092e05060102030c0a0f150213140f010503011e05030d0507150203250908030a030644010b0604153207060e100e0f0718 58
    0x2400c0801c0d200c0d8880c850080009000c81420210503c1d03004030701c01c0000030501c0c0305454201e54248050f505d00381101c6074040da104940f100141008903082040c10410101010940654200354003d54413012400340c5c1c0c03440c0e640b0b54454088003c1c00061101441d1424000315926140140c49160459003407008a104000f0800580c0d00031740c4070000045105e503010041ca02c0d00c03880070790314030f985d03400607150554000800781c6415201500601c00d0006070101284050107a1280f20b4410728017900780340084070b417104540d10042c068003002074107003005545900100f056a00b0300c604589a040a440400180e10904c030150b8002942d83c0c008852240c00b8042c1071404a002c2130000c10070500403800620f05a001d5400000a210080c01019000e5001395a51200451090060700842d15040001c0d00c600c18200403a0b046ca000080d900c82042415809160340c66010011a007066441c040140e00405074000300d401c0a2050411011100b00700003201025504420f0203030001181e00445900 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 965085557 1250 965084307 965084311
    0x207090c02010e0a060b1306030c05040e03130f0e1303020607030b010908120301061107060504061b12080714090a18090807032a020108130c1502030c070819060203 72
    0x45540350001143d1400c81040a0380d0000d00440001900c610a08100f103840344010036407008183c1056410400700341c0381e68034002124426940481c000c161528168150310414001e130f44412200000882e15060040da5807041d1000c6400410f92601c0759070350000b00300c1d150000180141e000000103508203120342c01107c1003a606061005160b5252407429091075201c60310303420251004001040410b62100381c2e0955920210b019014032410020010524412030203890284070807010440c5408820610981c480e64024440340881c6818000041c1381d91001e440c00f80015a1407141d924840c00d032001200d000c5403004041440751031911030402c50540c40c091140702c0641d62010703050041500c240007456481e00c01d6a654200140e0810304070380c0903201c1c1d881d502d0380010414130440180d8000d10056003004410894001c010000e10748003442d600716400079490075274a956042019038001010702111400c0c241929102d903250911071303598400020844810100508200c0f02045060b4000c603 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 965086807 1250 965085557 965085581
    0x4020a14061b2109040c03021611060d0504030f03050c0415141306230708030105040e0a020a0b0a03181109070e0d030504090506011706061606050f16020c01020709 72
    0x4103c03481c01507944104220004003c840350303000040c480101e03e8144650fa0184d040d6003403c40c14110312a0100fa1b444003290b800030441890790030504c04c1d50340c42e50b040e51011020301006201515040c9001440441d11014034408a8180008119110014800e80d000e552b081e240240c149100000c04030340c420401812100c45101c1040b000302646481c052000140031642c840318018074500c1d0100d620402e02c043e60200c522070034000740c000a080072048a044401c200c07004580207880784078450805020381c0c0000c0d804030300c101c80003e0b034900e4103019241034600c80e1401c0103003000e0204004c44054460b480140002d0407030404504510b841030b581500543c0d10b01d8000306c07050045e4040794020400004c19008614085010000020180030b051b41c810020f10340841039503950114010341c1d5202030b000f02e10440012844004050710031005120b1107411070018081424059880c50008009880000d20024145000e204043c0002135505807004107a0017002082e01d4190203c00405c0c2d0b8200710b03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 965088057 1250 965086807 965086813
    0x1e1d010e0a1d010501120c08060705031602030c06010e07120212010302370e0a0b010f031802060304080309060105030f0c0108130b07021606090506070605090c0a030b04020a14061b 79
    0x3064000b00074031a05000c0c12a46e01c100708003500500700302c07064100d1035020503002c0d4010710410040e1684002541d03040700d4112039039814084424016421400340340c4230060f09110f030360300004100d94880b116501a60142c2c5030028100e08084007031041c2d10815103801e48034103030300c80104014107141083d00a2404e070004041c09844e49096041030045031050040425851458280418079002c01010780000701c12404001c00101d80c00003030140310315400b4000034965140c19064018040500c4602c44c144e0007410380740da0303142500d00070b4040d40040e00c03034080c9e03481200000b080b00c1c240040c1820350a0b16000040442500c8a001100c151800a1018040c0d402c60581c1e00c00060740a0b900d1030240e101ca40180c0b28120394480c081d88038110f5503101c81e0400405200c1001992151401c9524264114801040382d1ba05c00480714500011008080d4104141c00b80000c14407070a003040c640118421100f03041d6240e070b200b180501030a10141106d03405101084086a2020148150641d0840715016 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 965089307 1250 965088057 965088101
    0x60d020604051003051f151101061502060117010605151602060a020102030603010b0a120213111b0f0d0801172a0a1d0c131e1d010e0a 59
    0x4181005003420110380840c3d1035406112442220306e8500b4800343c0000803001049181803400049419640442c1050108280300300b0641c1c2c3c000c0d0820340c080c03d4040710030091a900d805000350b49040c00d04c92035510300c40400c00c0800c4160103005100483d00010488a114242006416155881004a0852043d00b00d030130f000181c03504400b078907441a83d40c0006840e40340203401c1c0750a40710f50402c0c60344031b88800802805800101c01c000c42000303405a0f8107035555001e0b440030500905041d0b242c01044030001c24414800882c61240c111402402429201d003001440441a07540039001030180200c0e9004006001075182c1405c059400301580d0119010034017200e150340c51420340d00100c584500501c0300c501c00c55007064031011005291a440014060b03a8102086800880c06000721b03203030400014500a11004d510981f00c042d0803440301c0121900b8070414800e000c1c61045c4146000c2c0782c48030820212242c0c421301d03401d0480da180e090800391903644a000170001c00f10782010030000d0700103000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 965090557 1250 965089307 965089309
    0x9090d08191b03060e0610020d0c03030603051b0102101803030902130c030608070e010e07260109060f050913020907030603080f0c01050906070f210f0c030f0c08060d02060405 77
    0x403034801d2000e89000600da820207007840c14861004111301d006914103007c80307400d103500059503100e408161030041040390303084c502100500080e5002a01701e1140440400b6440040706c0ba41807032090903000c4904550f4070403046420394170b0750746055102d082310349400d8010a000c0d0f00403078406071000308103240c00b000e0305450008540f07140c07411302d0001341c2d03035001401282d800b00040c3c0c0103072010110741315481d8580013520480720720050010f41000f51310901030901804070207071044590320031410f201003581c40e621614003c20f0144240806100064000141420000d404500844008600000e10765171502072140c41c403c05000b150401d555118000b000c903046002034004460b13710080c90b81d82c10380c014002d09440300a0000740c403a030080e0307041c450745980141d02c280030040142044001240d040504c811100070042c80740001504010344006000100c2d4070540740004035480030802020746018003400c594124000c01c012845400c0402c0040c90240e0304003034000d20044c0340340d280580f104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 965091807 1250 965090557 965090591
    0x160e0f01050c0f0d031a0a05040906020405060705031c090812100906120c0f0b160302010b040c0f020724030e071706040b0105090c0a120902031b09090d0819 69
    0x120312a4816000b41c512404e100b0741c1030190078400106000c0ca00e04044018002400150552003000e21172a034a845403000c004003a0140c800811004150382d03103500290400940302d500111600b0112401080c0605082c10380e442907030425030b0040d180c40c0c00c02c441580c1003036101c00d02030104411410b080c00c2c0022400c84600822000d4281400c0b40e104010003031610003d0603074213070800140d02c14810801e200c4100c1100a0300c20491903100060100ca18504007070307006084c02420660024201036480d0585900110000100b41c1c0036402c03101e5007a03840c088000d01d04455001d000c0c0c00000c01d03010104442c400d03000b841026030000c003910b030a070780d40d05080280401c0c0d45501a0664000c50204030502524110f1113006200070b42d41c0e0141c5103841c404030401445008500402e0010305000300c0c1641c401e55000d115901c0d405011110001e00425200c00044c140b044031610840d80180007910413040428a13044441c42074940c1c103503680780c2c40e19080281c82c1414006182c956295221203801d141c0c0c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 965093057 1250 965091807 965091823
    0xc110a03050f0703021509010206071b06090b04110409050c0f0a0b070506090d0206060d0602070f02150d0605192c010f151707081503060a050906160e0f01050c 70
    0x801c0052180c0f615510612050110300e48000310742c100300780280c0100d6600802c1c5540d00c142903241c201003c01c43c00c0b03403406a500b44643d000d0451460f041c084000c000440900a010318014510440e80342c4020040006a514aa0001740150444a581001c41c1041c91501e40c2c103480c018458031200d07031140300c0305181c0e8212000c143c07065841441441071111040c03040c2c044840b02440a02424601040400d80c480780901c0f008042c41c0e800541203050020382c6060880b2154010b040260002e80b0103280b1006400c8031424015003480c10038002880d113003441d6040701801c0c140e420b07049000d00e007080a504014400c0c4401031070760035240b281111119503441e068003810780f0020382101282404c021041c4607451000940c01e0200b1003c8c0c84408442c61290fa542c0106146000100790751040000d03200b110720900c1542c1c1600c00c8005224800e5850f411580c421150032003100c03100d07a140c02204c8200c03146444004003080c0c0d0a40950000c1c01c1a49002503241c1c01810b20f40d00c4c100c13074000d42c9443c1c000c4c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 965094307 1250 965093057 965093083
    0x203150303070f061d210f0d09020a050103091509020402041a040e0c0a051905040503150a1503020d03030507031e0e060a05010f0512010b031f0509030301060c110a0305 74
    0x107540f11810030045540b00f0780f0440440d2801c60703106801c80d40382d07080d51050201001c8080b0080c044003203460310075110440d54038040d007a00c4541c807a180a004140a010085012171141e0000800405d15500c00d2245518045d0480c20702041c400d010211280140407048007071b43c015070200700101d41903c40702040800400444400c1d42d481cae20300324030b101070514060050501c0180070820306c0c841d141d003c1d05a8070041001444100001100242911300c0c0c42070307034001501801081c1c151000340c032001940d02d1003102c00b00e00c240100340b2817140d585c071200d900c1e0000a5000d04c0016004000c2403003607000c1a0b00055030305002078032035003046042050301040700107016829203d0740000041c032810300a03070340c100309006028006035050101c03108100c00b16014081c0520125580481048401d4111604200010701500e80d2041c04268101020784009240c011550409000c94010107001003101d04846c4142da40e41c2004c0655554101007002800306680e001051060100100b8414410381c600c511f8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 965095557 1250 965094307 965094323
    0x606120f0d05091801170d021b040209040605150a020f0102071a04030e042c0d05180a0509010b0a081807120f060507110c0a0e06090402030a050318151c020315030307 73
    0x12582c401c500e01f42e5040240030442d00036014030310b1030030100ca00c4519403580c1100c02613146c9000310003080080c000f81c1c0c415640300a61125a10305c0300c1c40340c0010003100300790b6800c1e03844d19214207010f42d00340e110351301b001400855120440900311040500890b00107110740340624000c038170b5078005000c0d41c1c6c4040c60b103214030020b00070200c1050b0250307039110b0b40c44405101410410000b10720203412030183c016229100c428121500c0c0c600d42e42e0440c02c201030325009144c01c42c01d5845090000c1c00c0d8000c06210800704410402042c854000d00d803c0a02e030041880040085030f0078200c503a0290680380c0b0088483d2006c0e00c034204002a031900965108201580e2207601005140d240c0038a860b0111280794028210403030107010508004038450342c8064280ca5000c201d0311544080b07442c0c80c0c14944041c01b2800f02180c984d441c05102a0604040c04040703858002c1c84407c03a0102d4014484c0744c01e80c845e44560405185000c444680266900031050368001d123070048039501103130642e0301003801241c1b841 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 965096807 1250 965095557 965095589
    0x20a030605042403081b1207050c0306010e0c09041d0f0d030605030a062021010501031e09020310090f02090a020c0a060209040f0c020606120f0d05091801 68
    0x2080a2080d0b4580560031900e1000d1030120810690f20712000c0d000103400041c00280e030032007107030920020440e00346503002201c2480b506094000d42a4210300310444490040260007503a84c40c1c0016014140d4045001d800313959201c00c20700c40846c1e84107289580d00241c448a00e84655480c0794001e55404030820023900c4110700c540700701c504240c05014176409251501c0b0080c40300b511300082c1280031aa208900040d400c81c3c0d1011142e450002e101d8216039000d00044546050302e080c14940b5090826068051099880304015402ea6103420701030741d40c8026014210800c2501030b001074000d01c0c006016504226024034011003983c5110a00b51510003041130240b04500744082c1540d4001030b6464214208000e02e5100354842e90b150300040c141ca6000306044aaa69684c4d110026614008a0401c0407030040500a034941108503042e51164076802c0c400d9054500c081202c243e070741e1940d4080c1c041001c8140c030070b40341c5801883c01140c001100c84000c2d50803501c4614414041d128018030990b443c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 965098057 1250 965096807 965096809
    0x10309120f0f030e15130b1e07031b0e010c0206180a080a0309030201140903010911120a0203120a030e100203091b0109030204020705031903020901171006051c020a030605 75
    0x34064034880b8004061801114105010000c40c54500300ca070703e06400325075612060f00d050910644002c020f002900345005018030011403250b40c11850300320440d01c0140384d5806400f80e08032185101e000458010100808031030602c584a03480d40d0050505054001070f80301d0300496295046040103d884101c0f10654500a25201c1c021070b00030a408002000c3d0111160b5000302281046e00c40281849a803000c90307240c5075a11401c0c0c0b8000f01003e0000c2200041c18201052030301c002c2c021150141c000000900d02001e000724036821450303006001010134840142440d0529030000070910100759880401030500f840500c0900004944200d016840c0c1c180000003e0034600d03402404023114944120050150341c10800381000c481c2c041b9401038403a00c55080c000d04520074035003011031100003d000070003055016406840740c0c1d08c1c02c0ea20b1324500c0f00d1112002c068400203030350140f1401c820301010841d5510800081590031000015000410108003030b090690300004211000701e5240c58083c001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 965099307 1250 965098057 965098067
    0xf091515010318051225051b010507111c0503030103050721050606010c111207030c0b0403030c02122401090c080106080601031d030f07231506010309120f 68
    0x3110403d80c410f60700d10503035035125a83c1d1075810710103441c1588082810010380514a04042c00d0f4001100d00004a440c249445612910340700e107142c0d00c0000845210781254807441c155981a40e0010b04a90b030300a000c0104541c2c610320085004200c030fa51f03c40f0100060003440554000e52040b002080650b05290520031441c1c0c064030205241c030180711208001c2500007032015007218003030030030f000b03400b000b410003584901480d1540c981082c58441c83c803402e8140090548102c0c0d0041d840207298540f1006070500c644103512000d40000e604100350302c09407074940540d0209a68500032038607003d1810f9600356001951140d00b0900c8484100100100e004a000303252481c0c0740d901e8001400e41c14418082c01800000d0031840c10140d9510340402d5481c914010254104c503288122900c0700605a4400030791f80c01590103d40c0654007901008400e070041541c3d0055092040142a4108a000a0301c1c103103c0c00404150400d43c039845284086036a00445615410703040d0ba604040c601d1002000d81 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 965100557 1250 965099307 965099321
    0x2220e03090915012a0f110109170c0f0d060c1106070221160b0108030a020c03010605030a3008160806010e15040806151306050105030f0915150103 65
    0x2080ca030400380c03840706130785c03000d440240c420f180810703101e031800b603010541440d20121000070840003080c180b0700107001104205045009003680c0344c5d1041500c038401c6121101502000c03186560040c43d070314800d898900c1d10310075400c8016003941011196500e03804141ea54a00c40314004c17801d2045d8240f00d0a1051002d5540a09980000d010840300001c4000070b800d900741e00f01915900101c4e4400b804910f484a2402054011a001c0c80d41d5071545499a100d910000101000d4400d401108446083c103000f010100c5900502800d902d500f941c07038045802408510350440b61a140d8070511a0455454161801c50102d40e01e180a5182c52041140c284521044ca103080c00180d02c00c0210340cac0c0c0d109140c244505402d03100e00410014101003408a4056500300700614000c1e001040401001c80480707a5245004035480d10b803d201114a03041256400d0188600149082000400400f9030b2003c045d00208150111010701140701640c6a04100543e048007641035440d030800055a07150207100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 965101807 1250 965100557 965100571
    0x2030f0a0e060114010201020c010507030b102105190c020706030b1206041506051c05060c0f0a0f270f090209360c03160c020d02220e030909 62
    0x1040074600100c1d03544000510a019041c0c1c807005560209901c00c0d0103450140310f11a0090080b8100780901801800c2104400d90040b6031030300c040c01c0028865004140d21402812100a0458141c0d407400301900c0c008080000d180036600c1d03c210407603400d12403d00d64650315405406542e04040b402000d45214031b8210b031280c59040d100560142021600302d400c203912a801104880d4400114405840b0b264440e07940403041c24000c501002d81d004214900d144a401504c48556800b0703084035460150503000c0319620424071081003418001c0b5541e44e4410721a04100400795500540f003200f0304903141d030158015046601c1005100c405140c410003429807050103605060091011500e11107800030740c107405061040d400e28a99803201441518122a401c18a4851a0284202c00594001c1c0d41d84509540f5000c00c07140c4061141000d2490307c1e500420303242801c8246e0f020041c4e2050140d010340501e512480c0510551031662041c0c1d0403142c00b100141d40c40f8032441080103402403000f8044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 965103057 1250 965101807 965101811
    0x120c03071202061909080d03052205121e040602010b0f060a02031206240a170402060301090c03140106020c0307090203061c0501060302040f09021f080a0c03091502030f0a 75
    0x44070060b0b85507029240c5046214521450200340010120307040c213401d520003d20303409080c002c0c00d0000d902d9003107070b803150036030710304141c2e824000e550f030310105c401d8984d400341090300400c0c0d1030302a40700030100a2442d01c20540d103c8000141c0d0352100c41060340944e000d400541c0d51041c1032100c44c100000c00a81c21113003142d0690900f94802c0019440e4403a00c0e00f521040c103c00d600040d12940e6409104140c41d40c08282d009528000b5580403031558030008901010812442c8181a4600c1c40d00c00f240c4a03560140c102c80c196440c0030444400790140c403507110245070f119440300c5e00014001d100c0d9402424550300501040d114181170508001503a0000300400d4010410451592649c05058041e0071740741400c2c41d28081182010350051100782c10080d030040c00c1050000c041c0b00d40340c00c0840e030580220780703040c0e50031001548040300f1070703201055001043d41c0750000f4020b400542c0c86071a41d00418180400c2001080d42d4603140d4201c19500d909a21f9400f1040c812802d0407101c1c1143d01039024402 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 965104307 1250 965103057 965103089
    0x101206023906150616050a060b18130303020306030a140c1503090309010e060409060e040b0702060721060e0115180b0d0f0f1505100f080a0b0f120c0307 67
    0x150308500d0100d0080c01340a502e001583c492001d076408041c0c3d40141c0c00606507002c004603843d11601510684105a1003030700c5070655110010005030f50310b03014070400c0ea0301302e000e400c50b079174140d02039080144410b07814050450003030f0205000500c0f00b96040a40809040244c00c50010807032900c001c542c0740e000b1644180b04000307488000204841c05501d09007400c00c04038140000150301c510079904400c0364a800d01c800010248030842c4007900481c411501803c103991384040c01c1340d807103104984240000d10b11a151100c42e002850740c0920108420b000411002c1e00c1d01d945098841c3c00f0fa00440118801c811989195980142c41584554a40340c0407881c00349410032005c144d0258807194001507581e00d220003048107940c0c1c82420350b191024000c0c8103810b40b032861840a1000340c42058090225a5103441142c0d1281d110700b15194120741303404025442d0b4030007250040144100701500716002010340310b00d90303841e483c2170385006011000500c45415400141801c0000d1a0310800c030740482125 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 965105557 1250 965104307 965104321
    0x50901060503210403150501090b01030207030503061e030109080c0f0c0a060f090f03050309040605010201020a09031509082205010c0c03060b0310060b040e0609101206023906 77
    0x64592054100781c3c040c1c5400c0ea0300405081158403880d80000d100720000000b000c80325100d50040c1d41200d0381000b04000a42c5014011350a030b1060150080001d20f0400004043c1d10348045845169250040e001103801081000f0a0840e0060300080c0c80c0f5441c04541130300f03505001c00a2841108009010340000940c44005c1107004650780103150500940028402c915031160700180010903080305036840741036880c11b083d501c950142c1c2d0f51038000e07400d004001c500395005000b05c07104190b00399030750600a0b2071030300c4080a00410000c4a03040e190ac4400b031402040c0c091014040200c10a20b4080d0701142c81c644000300d40c400d40d48003070f0510032040307940750126110b01d05002c1200c0c0c2092001c20180c000781d00090074001c042906500d09480d2500110b1805460000b402c00e41d181402d0104568507040308200c000c0c10100c0d104020341c03068200074404c0160a0b40103146061083e200941000214513060200c20204040d112009000c001c0760070400700c201c0000c9901101a5002d0322036410180 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 965106807 1250 965105557 965105563
    0x90f050f01080105090415050408220f12060b03030a080612120a050a0c0f03120e010b0d080703092706060f1e020703140d02060705160308040204020409090b0a050901060503 76
    0x40305052080c403105d00010709000661245c4183c061b107048003003006191901d0071015640219140710844200c0011a10310000024800c809850b48600c00880701860b0036058030400030882c60803103405454132080000d9440400c050030034200c2c5500d402d0349070307c0c00304184801c0201c0d002c414104d550110040e910603164040c02c5900e28059483c001d80e0740c0706084002c0e103a135840c3c24001003007008440959400c1c5503205281c5007084002d41418441c0c480711215503030a0f21903121086a00c040d203c1249000111417400800c03c99109041c000c0c01256a08010031b5802100c040e203d8145241c0c8055150340030741c51280700c1c040c290034204141c486043c00e50003440c070344204890025030320283e01c5c00210a40200690001581e01c203400c181000300b1024015143d03031140f41a00050301c1040c003c5502c003401303001074071f0b6000b10304000d50800b4860390300c003240d0140025100b6a003159003000081154200e41c082c20b503c45005040d00281801c1005130801280c01c01071400c08942d15014081c00747e87c0d008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 965107913 1106 965106807 965106809
    0xa0f020301050112020306012603030a0c0813112e1214090a0b06131b02100b03120304291005030a08040519080706090f050f010801 58
    0x10744c1d0500c020303070000740d002541504020300501202d0528850590104002c00b0740c26000c01000ea980d5055500542e2140c0001c0d440b450110341058100301801e800101c01000ca0b00c0301d56041c1c441184420300d062005102c0d9485006004c1c494014801607548803068000040c00c4001c8981d01811500f55a80008566030a20100d1410100503d05440c030643c0c0c1200a01182c0009994400450708010041c2c0e6110784510483e0103109400e100750050031002c200c2c040342c0a00c0c001800b03842d0925061310300500c24200400c2c0d5195482c003144000e45041c041003482d840c0d485034540541050103c1c41014000803031a9404110341354451640350160f6124449820215182e02c01d042e12406d0342070000e048403800704400c00c1641804c0c0640a81c40c0d4220b0016401300c0e85412040c0e040c041203901250002c2c500e40030500144180c842c241008140c1150030304860484a07001a01c0c074601 = true := by decide +kernel

theorem cover : BRFrame.Cov 964928057 965107913 := by
  have h0 := BRFrame.cov_init 964928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 964928057 ≤ n) (h2 : n < 965107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
