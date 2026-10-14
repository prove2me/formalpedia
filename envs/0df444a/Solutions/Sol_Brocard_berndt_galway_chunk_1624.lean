-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1624
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:55:29.064993+00:00
-- url     : https://prove2.me/submissions/66e0bad8-2103-4440-9af7-3f29c607333f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 291906474 ≤ n < 292086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 291907724 1250 291906474 291906479
    0xf050c0a0609030507021e1806100503040f051504060e030a020d050a09050904050c18040b01031101050f0c0115120321060b0309060103051005060f010c0204060f08100b010306 77
    0xc8010045030400400101800c151406407518401e10400035049607104503490240750300c103802c546894105841250740c501218101080e044400c8071225844038980e100303c690903104401030346e88288030b044110700907500b58561a103442c001600c60015503910350100410804d4600401d03e03400d0b1000b0040d414482045400b0f51100700010300101040300100d50f039440d4074499002c0b14004c00303000e40703507440034203180c2841030301d402041d10700c280503000c560303055480c1c01401a01144601e4103e03060031216404d60ba20f0300045000c4940581c1000005d1201040c0c3c510b00070000c0080114200001071041d80c0c2030b450003c101c0140e0b012203031708036242030b000000c250003601c582010100c3d4050004101509124003001701003940058401c28404810041c020900244c218182c0b4098004c8803580c190350065001591012108141c0065041d4030b80d110a5000f81c0c0005541c51000b400801e50359143d001400303c2e5003c69000b04100e92013038142840c00302c5503100b1402c12a00070300c1c007404041e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 291908974 1250 291907724 291907747
    0x18041112040804090608010209041107080f0d020405100e01032403030503181e15060f0f010e280512060c0c190b06090a0603050712020d060501150f05 66
    0x401209840e0310803a80c000604001900080750040c10000000300011034440e80c1d228000e400601009018514004182e00b00e60104026225686e520004043c81c000368161501544c0d001f801005600d15020301001c01c41356a6a5405650364040e40c1d82c0a03811940340c000117056580b0300e00403c6450001007502d5806814080002c41500e825041140c1c5d41c1d00e85c00144184050003c19021160041c03180e2082506d102c56200c040d03a006038802c98403154101040c00d244800256000da03401000700c01000000c1c180f484528114060504224003418110008602000c5a039141030300c0f00c1244040c1c2c072568072144610030b0080c100580303440c151514004132a503500c0c080503201c13010035507021032843e05015081255501000034079010100300316851805002d230203802c0c0c072aa440b0301c24030000074040070340c28403511080740e802000a041e10707071414550040a400484081ea00003060a400304013050b054042e40340282175800e4451840c40030280300400400c9500185030803c2810003421503d030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 291910224 1250 291908974 291908977
    0x40c080915060609060c0a05060103120f02070f030618140c13020306030d2109060218040b010c08030a0b03030412020f09161407140705130920040b1203180411 70
    0x113400a036400b65036025a0304004e8900311500c44020001d01ca028000300800551015180c42d203503440d200d2182c03020350381a0507615a4003901030200c580031540400c00115655410035000d08401258403100324126880d282c0d1803100b00043c4912680c0803100d00c21041c107080c10880704108a0304000c60441c00e04800003a2506491001482000385540f400d1000c040345100c801c0c905840701504024281c1c240c0341260107904a00352000400011080541d4a410280103041000030305948a440c0410346a0380c4030131035000034203500d010a1f5650050906524100020300281011220b40d010b4506507104000c60102680f907254006d450f410144907480b10300700c1c4d100040240c1030901180c6501e80146020840c018014060801a030109400307083c1171020451100740d50b0160b808440090340c061103801516940d06005095101c1100118032140031030f0100403044800034404600d6070003140c0002c402000d81e8039058410b0308009403072944500d400d41e20036110081a2010720042c415004408000d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 291911474 1250 291910224 291910237
    0x1216050906031f0b0102010501051002060a3c0f020f0a140f0a080405060a1e050a0608060c040f0f03030e011d030f0a0606171903030b040c0809150606 66
    0xe900000082005960b0a000c40e5020b110f1030b5a00d44101244101510b01501c6102000380c0036528000c000310b11030070548080d201201c3c894000300402c1e12111060300082c070405265901c200c1c3c401030044c2c6c40a442c0500e1602002c6000c071f40200b40080100c0c00c5080301c19400307600c03800910400c0015420780700c1c0c1042c1c4495055034200005c0e09581200c1c8950386100d01410394546100008100107019040b240300c46c000c500420443e070701607460500005c2160325104985080b00301000c6081000070058002c26031080b1000c00204809035075089461034044142c80c070b41c442a43c0410f0602506100d80c20030001003a55080c0c0380c1c10704c1c2c6162400380005406103081410000381c4611542c0c3d41c1c0c0480c441d0149603c024040301c500c442c000700300c01e8850403041030881e02c0500340380340040d440804042850040c0314a202030140d24840c01c1600c03848500c040d5048080c9501d40b006122070f503440b03202d6100c404c00300340c460001500d0560b185c9420f18058050840fa020b83c2c0d001805101d0322440155040d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 291912724 1250 291911474 291911479
    0x30607030204080f071a0f04030812040b090604030203041a09090c0a081005090103030c0f120302030105040e07150f0c080a0201020306132d150314010522061a040218121605 76
    0x42d1031840e046c01f40c4852043c0d80000d4512000041c06a490516248001c2d00c030340c1c0918000c14150320b0315080a51655400d850150042e4070034007060200745c4c81d080e00f40e081114690360151411060303001042e0000012908504500d0300400c18040060f0019003665001c007900b60b490300b1031400d060004d000c0d0354043c04003a08114640e441141000300764000e0158181c0c219a004032000409e06009004c0c2d402406014060b90807e01d400744110b10029201c01a10590009401180400001101d103011044405010000c030708a44c000820400c500038003210203240d00259886c0b800c107081c0250b1013000301e660b610252800170b1804902c1a0030444071039501681c0d4081000d210b00307040660261070f908100400d013201d0f001c000400c2200c141c040b010000100c00080c8803565441060421200101040c01c504001d180c2e648030014140f0741c011341d120380858682c03100145489000c1002c9811055000300c103544201c86100c0246001c40c4862180d6181c0380007400c050303110b00b06150b000c540603c202030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 291913974 1250 291912724 291912727
    0x1a0603070c1104091b090c0c02030a15021b07030c0e07051603020321010302040e0105090a030507080d06140109080706051605070b1216020a0f03081302030607030204080f071a 77
    0xa143e8554001d02c00b5650071440d52000d2020201c501d0380c5044140c0300b0005664500700300da00c17106020700d800e000c8041d0002d0150035148a03c0e00c559602030355110312003544a40c2008005840c1c40c16000900c2d004402d4001041880e043d4504050f1600154006960000c00c070820052aa91320030200d9a201015400d102d405c086545800e0740b46005404060100900e0910f05640c1114004031440c1200c1c003c035000d1000002c036002a0342246c1003030710210f22a4015040080120780118014105203115a4181c1d1420b010741c0c200070200d400541280a14844284000d1750f117691119001d03000c0c042000c0901111403030540080d02a1140524044c140f208804e00c131004d10000784a03070b90007407132030707517040c0d03641e0b40400702200074500e0200c0718812003400350203041454510024071041b0040d40003504544030f0180e40c4080d11810801840401034182e801d40700801601c0512100d4002c0c0100d44000d601c5030308020b009418002801625036a40c0d108038400c00280041010750700c90b001d41405440d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 291915224 1250 291913974 291914003
    0x30c0316020c0303041e1d0423010218040507020c0901120614090106030c0b0a05030f0901020d0608060907050f10030c1b0f060501050306131101020309040f1a0603070c 74
    0x5034241000b012060364140801301d40042e4403209250170681da03c004c01c40346940c10b522041000e00300c900300701061844540703400008000807100710082d0641205803128160510284420500366407200c08a1200300308080030300da8031801d05006164001c0d40c580003405c11159050049607060300148507800c00c005a14104805201c030540c040b5102510402604445e480d08144441c0030700118403040303031071000f00040003a44d0a000400e9505005466640030f04d16114180e0702c03c40850061f0021200395030820800241d10001c2c03250f50f0041c13101c000a482c291504403002400c00c01c0c0e642c410340c09108407201c42e9103030303586a04a9100c414000e050000700071200c2c010448510b4080740f0041c035640c220000c4201806124555102014811081131000d03a03200e81c141626001c09640102100c86a1040e040015180c1c03d81900b003501c0600c100e909101c5148000b8007510f03058240c0e811815602c04000c882441c3c070480d40407040805032402461810002002441d40752003810160049043e031029 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 291916474 1250 291915224 291915227
    0x10020a0c05010e06010e0606070b01180609020a200d0e0d111809060c04080c040e03250b010506070213020306190303081801050714030406020909180105010506030c0316 74
    0x303082150050000c010100c0b0341e48074680e0b1000c2c2030185002540c0d00d840041c04031300d0640e04403141180d11864148059107080a040481c0000c8145032400310749894001c0307210302c018400740050783d00302d540341e40710000044103003e903421175a800303100b098200400071500d00b50065010141580c080c2e80c0180c6c48025414140100c20b40c0b0600a82d104882c5100e811140104e00c2c0413502441b06501034901c1d5445240c02281c440c400c0d0311450146030070900311414103113481d62000d000030011a054170300e0034030500d1403c60b06644004c010041400c07141b5504040c03100b4079504d540035101c203645291034001141c00041303080c000c0c01c0761420b20b40c5d00000010300c540c81d075845010280c0d044049441080c0d89924001c0e000c80c008aa24a050040b240b22000107035005000e002d001d038003c1d4482000b8500c0c2a0056910380c0e03c002c02c2560403580070801d0015607210401024400d41e081135a81c05881e000050803403e64006030301c050f20660040c42804a001800c00441f071300f11180c007109004010480a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 291917724 1250 291916474 291916487
    0x50a0e060c0601180b030304030218040c0e070201020705070803030606120a110f070605060102010b06191403011401091e0e071e03050a06060c050a06050603030c010204140108060f0310020a 83
    0x81c19440c2c0200400003e00c01d4842c0383c1092282c801320001e000d03407a01c0000b130503960b0141d0b201c007a5001c201c881202c0031044030008440d8003e401400940c10b160303101c01c40369154603416583c03180103070b44c0000c210301804000e114500180001d180030b9403030b60600b00002034450040d080d0300130380c2043c442c0c04680da00156900148580c500303da111500d40e1020340f00054150402d0406540c0a424000014021341c07040c46500d10910009000300c4c1010304003801107060041140c01c24060041030345080700008044c001560081034802e00c2e04180c0c0c1980000140800040d50060004000c00ca445032102800c1c0c010a0003601e440308807005860f85d4016045441611030320b00400e0448110f00100700d080e60580203144034180081041c42850346c2c441040360424a0340320003070000e4000340d100c0000250940c005507009071000f41140d04000c40c40c0a16422a405580080180e400c0341c00010f0303c950304035102580c0071780f084072100501c0c1ea10360003103500c5400035032064206076400a50003d80c00d00655 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 291918974 1250 291917724 291917737
    0x103020a02030c0a0303050105270a0c0905031b01020708070b0301060c020d080d090b1506220513050702010f09110909030f070f0c080c060d09020f0d0602120a0b01050a0e06 76
    0x20480d01c900f04c044c14040c0c0207203000e0085a00a0004009118141038031155407008008141b40019265071151041c0d001881d61040c1ea004110000d0f200054a0b5410010301e01d1425204d0303031002c1c212458100191030701603250721500310394110312400c100304a50541038174119803041c00d000c55100d40500c001005d205603004c000340203840100f901c105c0421203501403000c5900c038410318845900c1d0703e55038442000740b000c4103a601407410821807506940f03d400c09800348060248071611280c4482c00600c850000d42c4da1b00c01100e0742d400030044034660902604a001e66800c00800c01400700340ca071040d003041c0103441540104454008030b034803404200200c64424505600c45d03511461589090100c0310540041550303081503442c00802c440d04c012880740810607009045e24540307440401810084c0910314020b0b40d0204455118006a403a04240060128400e41c401662003d1010043c0115100500042101c91800c240d509142e6000300c201d0b00409103504000313182007603000c0022414440e08 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 291920224 1250 291918974 291918997
    0xf0b0c0f0d050412020f100b030a02060f030f010e060105043c0e010515070f110d03110d020604031d040902060708040602101104030308090a0b150a090504110103020a0203 75
    0x50108031100150b000d07a0280340306aa4101200c010702c40201d80d0384000034801c0d11660003000c001214416035602102c2259400b81c29540515aa0307000030b10035422001140d07811550000070000001000040c1e00d000d000a601c0c10358140c1401d0000038410b005602448010200c48030f00103c2e00c1e1020342c200b0241ca0542d40001c00419a41100d600001c1c129104000a49002034008519450301c05802801a00401045410515961100c0300340b46a07596080d40c81c92040600550213403030701001c81004130700a0704d84021000003603080528044ca000b8914003150084030034030001030740c49888000201800c2001c1103070320034513030001401000302c010000e601600000d00c41c0c04201c160006041114456003d031140705c90401c030280203403220440c115841100412007030002a01400d17400d034100c54400201c81d00201195112424000203542001c403116800c9044651031901c607100201030407a010317080c0454281640c03200c012065529000d41416008149407075154420000d43d009039a15 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 291921474 1250 291920224 291920227
    0x30c140c0904050706030606050c061b1c051501020606010804030809150f01080106080303090d050d0b1c0b090c03031e0705030d0c1209031209020118032d0f0b0c0f 72
    0xa20309195540c201740b1410380482e0800c0c00014801e4050410703a9035400180020304610b80e2060691040d01e000003d9030300035810144005c21098800140d03108400503000c0000542c0c2c01c14012249094044031074050455001400300003031640d200281c1900700e9458100341c501c645a00301818102070000700780c3c00c000c42d688400c02c03641188400c4c501c0d0482d50344000070020135495074039158907840100c64103201640004046880c05100310300500c3c80d011003003400141c1381590000124441361510301400030035580300341c0c03505100300810f0700f41c0c00800000082034a032020501083c3c03280603a80e814119a10151501d582440c0c40f40103c420103030b881400e40340e03140c414107102c0006155620000300001d000c0e0b030351440403000070700c514400a40c140c0c560401c18100c5038416009072030100000c81c1009408002548040740d18541003018520500b000700c079101c0070010121000362143c80103000400c000d60b0344004181c54001403050b2540180300034045a60310080041144640e4041c000034920 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 291922724 1250 291921474 291921481
    0xb061606052a090a0e0f0f090c040f020c073203010605030105070215090303040b0f0601020106051f0215010e010302150906041203020c0d0b0105012003040f0f0b07030c140c09 77
    0x44220003445003d404a0b6070301616a10b403008402d01e40c608544203d050901a000700380b070754820040d0217600c19621401c45196100c00030120b81510f0140214403c402e40204032a451904180000c4002d4900d00981c3c490017a00c401c1c40141d0034110700b5000c09030f40d440340c6407000141c4003074101c1800b42002a0081c017880c01c2c0420000d5483e0141e90364542000a040e003c25080d80e804401c5a02076034020035400710644800c17a101c094600c000c7d00b21390556584000002d410f0701c4150078142143d031070180c0c40b6030756034003103001034100081150032052035003841d0018402c80310071040003819a901919020307000c05980340c00070564420307151141c1c1d003e4404100042c4000c030300c50305e0100c103901ca942941d000303a030540103000001c030380e40e0340c014000710703507030005121651143c00c5480c96205007403403249050300b03444541801c59019400c00e0080e0b01c0107110902c070200b014500c5000404a042030a880c000403a10001d02c200c100703e2000f41440e03500714410b10403000c00c21120b11381040c0100074240508 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 291923974 1250 291922724 291922801
    0x10e0601140a0918021e010c032025050108040c09110d0f06091a0901030201031503021e030d1407030513091d010e0f06010515041a030106030b06160605 67
    0x130401d410403486412600fa05420800300e80c0201c10710345c10b040e107881000c08007554003075030154017998540f000089200050301022401b00080c41901c070b09100b22031110442daaa071002c040c0c0041d0803a0b414000141c06210010b5191103c040c1121104400080e0155800082d0005131050000c049140340c20000b440d400205103a01c200c007101e146810800c44034103520b01d1614007445041380075911902c20780040016501980104110100c0381c00c001d41e19940700d0b80083c2169020041504055212281d030b01f2403410100000d46041c900f03030520450311140c41604a0180c8513a0000800f008008240280c0e502c1e0134500341400352211880c14020500d661061600404444044841c0c030360034140020086140454505107510344503015120f076a003020240300180d140340c0d00d10003406800700000182102c40d919095030810603a03d807650389505d405c000505540e00b0445192159404008100003076442030048040558807050204039683c90314031075a04101d901c8400c1000040c900c022a0342c02 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 291925224 1250 291923974 291924011
    0xf110f07230a170d03060320060f0c01150f0b0406050a0c0213050411060f0a080613180308090318041d0d020a170406050307050d0207021e010f02010e0601140a09 71
    0x40c90703101201e4944c211000d04806864241c4400390440d19404060110504c44441420790420003070301880c64102403c2c1000c0d070b0b940c811842d81340b0503550ba01d8581e512450006000000302015800c05030b183e03040005880c041d1141e8403841e07051100001e59a6070150040120007400c079001010138003005c81003150b11001c1e000071102140d00a408020035400b17440c000d8141d030003000351101621b04140c40130f202925120006086503500a1b02800091a82c510750b0052041c07010742110701c0c04920b07016140c05840280d019080d83d1054206212507403414101246140c4801d00c00c48001c50f0414003c40e544006000b241602861030090141e0041c3c1c043d00014203020162103139a020071110f10040c2c18a08a001da40a20380028800f040420b030310300d10031809007051400d0180014a40044da50000d00b034210201400104140848e2604040750b03006540c1c03910b03540c418002030240c1d450301d1803155140c1c00305004210002c41043e918228640707071922440e000c1c1400d86001c000701c0d03c0b01c0c440481c1c01c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 291926474 1250 291925224 291925259
    0x2090a020a2142031101030b01090314160602010c120504150c030204140a030c05150f0c0c0108220311010e060a05180d020304030204050a090b070f110f07230a 70
    0x42c0c810386510b03004981c5006211004507904200c8a1200d8170840004402070940a5401ea041107400140170002c07852408845070144015002080940328021441c11045090f904c90400c0d6450103902e0300d0580d40042c04503414412480001650741d46074644803400c404038404c1099800d15103160750381c0300303505540108266041507212401a48565003045131007000360000030301a120f4000c0030403950a0800344088022200010300c3e0400b00710341d0001006822100e42200b00e68031a241504003542c208411681103412800545000c0126a02d20380c40d44403a01001404c0001000c40415400320a505c0b01d5102000b6030191152402d040348503401800d0180c6000300d602e06400d404610304480000c90554400d00c640180d0309040c5036408100c024080205040b0303516484060000c00210005020b901c281c42e1740e101c18000394110300c00103000b1980d00c070010700140c2c8604030101c071803c4006298022107101c00c0340403401c014041900154200b192080d55007003946200f0110300fa40c107500402c2d11 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 291927724 1250 291926474 291926561
    0x50304060b013b0f13020f07051501050f010e0d020d0615060e030c0d0c0608040305070c0315050f010506070809040221040302060c03160f0903120c02090a020a21 71
    0x75841d82a04104011009052a5a001011781841d415068a9401600c0c4081410301c01701c1c06c098568840d030b0301b000c02000d030740c03410400a42d00500c824076081c0311480d11842e084c07800081d1043d9410104041040c1c50038042c4c807504824265808100294000e6080491001040c503001543d80401500032003000040380d1003809842c3e1841c0e11810030000a000d100d41207210061a9458250b054581500151096042000800c80d460128581c210320100862064103502c241c10140400c01e01201d030b0242900503a042d0440040000b81e50348000e0341e401c00d0300b00803010340d0b171640340000400a1088481c0d12045001d102da210b0b15030044c00401c903228074002d4084d81c0980e42c5240ba543c03800d100841e9421224525401d00c145000d108a104c030300c060301ea41c2050403005032aa15041c0d801060400c00200140e4031101010442c1051070b88190007682c40102075003002900b01c5c024009c9452188000700c2c1c6400c12034044a07040c40d6810460020001000036945564401410919112020400e90 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 291928974 1250 291927724 291927827
    0x2090a20040302120102070b071419080a0c09060e040b060405190e0a0203271e16060e0306130c09050906070314091c020708010509030414060a050304060b01 69
    0x401c03113401070007103c45d2242d0001c02480d4580c0d0700c030819150040b89404d0700f0030114090250070782c0c29003c920440c0d905e03441078881034824a04019950159592541000200407821604100315500580b841ea0705840459000c2944480300c03001c64080d0003075900007a80400315040d5090035501c240d80c044d040d0b901d41407414001d0350f6400d41d802c05034882902e0358400d88130907900c03221509100300350040307020390284140d5200d1800006504d0860120304907804098020b04100814807840104500081005042118448001c0d80001e0340307400000f00307d03101c24a00b003004002002540400b40014040300a0100700300d0500c4c100c1680d5940b000c54207240401e14006180003201074107500710780308603811401004110a48081750300d08500c0b0312512020742c07081900c08940e030310080c0102d41c40f801c424801151140d1410080541d10000003581a000d248100072013400c69030b200003101d9021f03400500224480d4941e4004a5044001e1a80b600d0b00d9001c103901021a010906c8814018104005002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 291930224 1250 291928974 291928999
    0x4170714060c06010e0c1606051b1206010302180d110a0603060602030912030c160302010e040e0303151c1109010f06020a060e0a020d030503060306090316110d02060c060403080109050c0702090a20040302 89
    0x4414485c010104480d103854bc00040e6032580309400130500386482201100c6070403031100206140002c2d01108480115149082081c0740c20042040300080c80c00c0d150a10405140130800f0391240310304143c141c0902c48400c04061211001c00c200d804100d00002201c1c0036881010000301e0b03007061408202e0010311002865100303450240501129064060095403958030703200d141410182c5504501900000d00d40940c0300c40c4002e50175034100c5c090082e10b164200c040305804008150b501600480c0c40018240b00c24040c1583c0003402100c62903102c840001d00c000342803e0070b4a0251f8003080203511810900d101c008069110010b14014072042d0125a4640c41e4250980e4490241c2c1d200c0e80c082003004000d11010a03501c10300c1a80d440005062a1441c0c41c4c1d9402041d0b40b688034101c003861541c40a0144410035520212883c0107002100c41000310f800c1c602c0b0b152000780f2648102a10908011012404444007540000410000e00ca100e4420385140e10600210307402620003070744079080c541c00c038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 291931474 1250 291930224 291930271
    0x110705100f0804030309050709140c0c060121050115061d0303090f180a0e0d08090c06030705120403181a0306041104170714060c06010e0c160605 64
    0x55090315580da850310784541000710402c40b0500402001a410076446181e6440800c1051194002a0040b408041041c4240080c0d8501e1608060a000c01200040003850980100410002c3c191280006403248210502141007a080d8140c01d02400d55481d091200821548003114002210304d5a200c0b000c0343d081c505180100d2030280040300f40c25030000c00c007038542441d0040c030410490100a151030100c1031a07072a010403d00c1c4c22a5094000c56865610006c0044200a03031492408507142003100f918104a0191701c4206031050140500d801102151001e8020801c0d950380f1102d402c0c440c801840c207401d008003041c016120b80c0c1000e41541c003005c00c41440050a40b005d0036000044d807840d645070b04d1305120007007600c0585507410300070501c8003042e0840102c0040d050031440c070340104403060030300601518408001c6900c0740715041c00c10581c2c030394a90224203070703044400a45c0742c0b0000c2d69441d200c0d41d4035031282c10084842c942020035090204002c9601440c0120b8404200c0a06840c43c030386d5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 291932724 1250 291931474 291931489
    0x60c08040b060907020c04020306120f07210309090c05041205101d06060d0c0b040f0f141c05120c0708100903020a15230405010e16050d08040b0406110705 68
    0x2011320040e044142200b10b9130405400460b002140a4410030070540160030490904242481040ea15000305008002d0380310030506800180700005007002c0007e80c0e0341c0d400381810866210f0110500e4032150340b061001e008c0c50540e40186100481d5128240755031030515104c2d41049901c4500c3c1d4a0f040700c03203d05500040001960883c0c200050900c0e844140c10400c000304400b0b002c40b0000d40714400420741080c540301400081c0f000c030181c0c90482c1c5c10301045d0240710344242c010a501c0386850307004241c82c0c0d464500c10720305d98030344c0010b005201c1d00d242062418510044060821a0400500c4e0402c0c8100000e4034411207801c0d20954006040d80e0401c0d009071a03c050001e401030340809042c4000c84d12803010f0415070003c5640009200580c030000e60400d450591940d5086110031040205100080c05040000409103010300182150007001c00a0160107008150180000401c1c0004216102c0c0458025010b8a0001c070f450315aa80d2000f080c44281c0004004907000302d460000700c0381003404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 291933974 1250 291932724 291932731
    0x1031101140a080f090712170d0e0f0c030d0c0605090c040c05070209010801060506120a1415091b0d0b010908030f033106020a020c040906050714040b0702011b060c08040b0609 77
    0x1240c4040c40107071611988850450000301c0235007034404005100e076107419486a003040300aa80098040e0414000f4a94100761352000c040e806070b0460580c81c1c810991004c040c080c0d6540c000c80c00039083e100c0ea016035107420045080260401c0c0fa003290800e01c1500b0802400f11035200700c03801d502c160b0700c40400b9426079445119407604074000380400240c40030900d00c007035800007203140001441480c0050508102c982030782c071034221b0b50908000d9215400c00130243e5500011341c55405400d400013132852140da00c1110340d0072400e15518401c0d0301c61a8400e5038400005c00580040b0785e11241c50040e030b0b1071103074815212004090020000903142e4130100f105e80d0f4142c0c41d00300d01b2a040f04a5515a84040d60080080e0300c218002c2e6a028070302ca544520070852100d00592000500e80f81526020f420452002c120380e201c2c100070300c81000300d47c034040c0460300d40903428038112107000c907071440782e0100c203040ba40000c2c0400c0c00c00011420315544034001511590044000058544440303042c0010041d094 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 291935224 1250 291933974 291933989
    0x60403210e030a030209180c07020108091f0e070f031415041a070908030304060c0207080f03070204022214010f0f08070807110d080a05061801031101140a080f0907 72
    0x43c000e880b84540260b000d8840003501620442000003100000c2d404124101c41040090340046003000a550344000456440b4413a01c005108102c4502c0981130940e400d081c010030b2241d111110501034120900c1080b00520707a1244102c020746e00d0307240040c94460040c411280c5807180c01800000140101a034074040d40e00206244540c4010b2011000c040714000c0c81002400314040c0000381c8114200001c512540c02010006034500c40e2000003814244a036100300c00d9035010101501040702c01008840c3c880342d0485006980c3c40d00c1c004801c0035201040d20107140200250300005603068000004900b8400980e192160300c00c00b0081a521502008521000a41044001ba03806c0e4010f00c029500b000442c1491000c115117130420503c0c003000b84c18107000040fa40c0040c000201e40300c3c006c80d5040740e01100c46451804121a40b0852803205100c013609034190300da92240981d00032043e6082c10245a560b4550301d07070304d041c4081c0a5400550305840100e50b07080000705449008505907003564040c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 291936474 1250 291935224 291935227
    0x106150f1b020a0302060a030533090406060905090f0706030c05030a020a090308030c1314060304120302072f120303010b0705100e0d080906150120060403210e03 71
    0x7855005056564500d0003240c00208031900800960755071409003100148503075003c42c030340c6031401c03440c00040901007007112040959816016446416035409168400950306003241e135850381451790191410360f0050040c1c0c0d1034801404549800806d0104032480c1e02d070201d0f914180e0b1481e04804a034119649040010001d00226100c203e680c0c000746200486450071a03070064a94035051003941c803d031002c5407240e07000030302e641041208a58a00c01811407507030314180c0e8099803000c10103511004000038030003011403030320090044c02681a254041d8010360310900e8001031000c00850000d10900100380200042598816450003500e1701b08400e540034003850442e440d00642c0d840f540c00c1584201c070f0340e0251820740074121186204180703202003158010303e125100c10102408001000e04081c15039008102040003090340340442442040f0280303003041c64540961000552484044008180c82c05a18184000e060707002840d01c04140d07655000c0070002c05c90000e28412145002c24103080e40c0c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 291937724 1250 291936474 291936497
    0x3180f0b040911220512150708040f0b0403081b13051302040504050a05070e10170c040b12090f010e0703110d080301030302150703020301121b08010e0106150f 70
    0x2143d004192581e1000d8007050801d410380a16859031492688000d00140c0c1c000020441d51400301c0a1901d0304d18054041c012983e004c04821130444001072642040c0721817440814208003c0601e40c02d026504003191700d94074182441d00405010054030341c42e050394224a0418416218a003c80d452007090a5a003440b43c0c0c43c00b014009820500c3c01d5441c02180c0c00d200015540d1030b2401040d11500010600090a181412014200080d007010142c012103280c0f1000200c5a00070000603400402d900701010141d44031505620b4a10950300044000e240200303a280040d0140242d041c0280c0c0c8500c1a036003401030141c100c5089461080f5021481c3c7c0c0001e104001080300800c0031030380c0d848040e000c081114019250074900398820b07441240103900091003d88002c0007801e406030840280e18040d03103103501d4003c441380540184400a040000e240f0440114050302c08030702c80041540d980244070481d1100c0e1280d00804403440394410307072001c110329801c0c0d16108105903a9084c130152103a4101c00e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 291938974 1250 291937724 291937739
    0x509040201110705102a0b0c130b0c03090108090309030304090209372c09010e190201270611010209030601030804030318060206070e06070c0303180f0b04 68
    0x90004403400311a004401c008139180c1c4451040c088001c6494892541144070300c1c6500c1d03840d000c030b540c28245110074481107030001803450705902d03003180f200c1c1040354a500c10048440e82480140c0d1020301d030484000361807444504040040d00701080300362241d4009540d04800e55440e031244680080e403540040105102c07240813503002e0444d031070014210110740c100c800b1114100031128000c0e42013420031000d00303c1e084440e155030bc901505a6200c940b0b0b00c0c0d8020300b44038800c03075559a19110704001160009072071040941c081001c0c0c040a004842c7d000d5121101e00f040101d62540607400038050900c442509c4940b001e840701412200c03086d03010114034000045420b000c40f60b208414a54007002074007641d0b86c0c00c00034540030b18080d480c241c0d0358614520b030143c90507024240d5541018042c82040001c642c002c54900d50002d05410907034814042c50300050424447e07003100521030b544000300803050561082d480c0c40707000092801c14030483e44804950707055245921403903030620010403040c007600c1c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 291940224 1250 291938974 291938987
    0xe0306070f0e03030a080118060503030933030a0c1716120203160f020d080f0a02070203070e06090702070e0408090103020403050613061104120f081c020a0305100509040201 76
    0x6941510b00b18482410000010381154000c8181c0000282c089006110700c1c01d1b814083c50b1001000e84041040914020129840b40a101d034920320620445940311070005010045c050850042034481c2040d43d208a035210464205030759400d885840c0284940305a07010380720602a034402d501ca0b80380c0b10b41d0f03000742c0b03080c00c1c0070982086000c100101c4041600e590060002d1401030344001100c4003624100c031401049000304ca0803030700456121501031820385820030f07a01e0f60480481220541c0942d100481080a84296100250548a13503d00010b05042c0c40a86034003500084030055030302e48a0034800c80c5d0f600143d00610490f0006000441c000840d14801080329030303418180541025560703107500e030409900721111843d040840f1100001c001403845803203800c3c0140b2101d2410181017036070706000044e030040d0040038000f808000030180945d20060765603d940c110f00020189410310001006500441c031840c001c241004041405500d15044140640d2409085980031356920703001141c06 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 291941474 1250 291940224 291940247
    0x60e040207050114040302030306010810030206180a0b0c07050906040e0d03051906080109021201020309030a0e030a081309061a0f091f0c1b05010f050f0408010c08010305010c0e030607 81
    0xb15940c4000c43c540312481e01801c0da12031402500078548901d090b000150062600400100000030004004e10041ea907207426601844942402c0e0000c005881000c60306810300398201c407507200000310380c95580550001d084000c0e500f00b5116181c40b500d44030706200944181c4000c20f00b0a400c81405450500e110783c0c0550750090304110907541707089079006070700d01301c0d000da401c2030000b41d4680a001055081c0800840f0360640020002c600c2d6240910001c0e40368005c4002000c10040400d8140140b5a01048482003c1d5000002666103044e0b18121000304016889020009800c1080020741c03c03c181c22403d032424401c4403590716003c00c0000c40602ea41c0104420355010319140059400303c4e4900560614494250700d07580f481049905003001860b001c030a0001c40f52083c22020711640c0d13030002032107100346410300702940c0b105042413654245001c0ca07044002a98a0030b4041510aa8000e20442c100d9000710002c01081c0a00101115120f1015000f90b0b00759000001141c24a4440d0f03488035035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 291942724 1250 291941474 291941483
    0x30b06030c0f0a090b0d02030901140903041202010c0203030d0509120c070902070204020721020c030102090a06050c150718060c24060e0412030b0901060c0b04031407050109060b0a060e040207 84
    0x80d90f50302c45c41a8006504089400c1d00c4180d408001c01c80b00d04402d1265280c043c41c69000043d462603c400e605540344034500552803200c1c2000d060350b0469010755859284640d00506480c1c0f20001a890b840c028503085031481020b205144802c0e00100f41c4100310781c031f42d13600c01c1e005d081c1040c10706043c9800fa502186040760130580c01c00030800030640c69401c0221604401d440761b446240b5020b0000e183c13085d003201c0d0601c47c0e4810040ba094650742c035580b0404035402d60800d0781d120325900703880905001001c0b0551182154800421003103175440380c43c080c0c400c2e10b890740c8408100d1710b458044030b00f0781016000070010307482e00000000e00350842e2500c0100070040540031611645aaa00d03040189041d2030032611001c10100710401240c050080488410064419442c10f40c50040020440c0d0061280680381d400303000302190901d031040c58240c1c0d031000040380b1203681d51910314107a03008044c0f001040d500d051074002c41a02910306038100d00101e4100da03507005c01880240c0d041200941c0480d80884 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 291943974 1250 291942724 291942737
    0xf100302040903021b04020c0604020d06020c0a0b0f010905070215180d080609060621151819110f0c03090307030c03150605010f230c0d030b06030c0f0a 67
    0x180e6640c0900d409481c4658003400d019440d281c8917040f90102071144900c1980140119200f9001c00075010f80c0c4107030100d071807100140f82400e05a001384208521a4901d00800c4115414130280110550043c0030380741c00130516a076108003030f10854000b940c02c68010b070801084090703001e44e80010070b40c01800102c000b004c00000b510b411440d10103000c0a2801103a0f9010401609180c41784607aa440541239901b40d140414001903c00811000070b86100c1c00451500800c0c10b542c00b09a6402c01c2d802c020b4091400201ca18032200c1103560304840d103410402a0050351610103040e0b0261070b2808030182902418034001a0000a55411114450889100c2400f0100c040e039000c100505c000c5025500060049096050802020900d05051141142403603820080c690f030005104003442543d10b000099100c2d111a50004c21000f00295000284d01241c5840304000100b210b000e0b00400d1b40f13003000301504d68818002e007404102c2c0c002a05003410300c00e007410688004000c0c08c20b00880e18200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 291945224 1250 291943974 291943979
    0x16030f09050316050405010f12020105180a0308120907150509130f0e0706050711040b030a0b09010e0c01180b070c0b040f06080c09090610020f10021305100203030f10 73
    0x43d1408001d08061a2084551a410441400d00d4441c190141c801202c4c1080744500b48035000043c800c4841c0000e0400600242da02008a40038582e400001c00003481e480031107075070742400321f2150010005c5401c100711107008a480000b00107a02d02c1125100030802074845591802500c96402c02030b070580d0801050714000120080d41c0c41170300f00c45403115500041c01001220228904007080d04100203101040001c0000300c2c1131402010503180d030488010807803070309090200781001c01c8554001c0c48424040c0501030200c034103412a040f0740410204946030347c07030b44900455840c240242e8101c00c00302640390a0060900c000000e2042e10f02580203143e44907a0749410340c00b03640c4150300030040f4801050080c443d0076070110b2030580001e01103070700f00e041401c0c0ea800241c0000b00680345a00c54a0180550400c1ca1b0003480a05103024400080c2d0f605642c450100034060352003e070000c0500341d00b110020486282c422900d10390358406a0081d41141d039035018801444001a0071844000e00d0000f00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 291946474 1250 291945224 291945229
    0x308090109021914180109020906120a0903080a020a0504090506010302070210050a090e0c09040e070504060303090314030324041d0a1718090c2101170316030f0905 72
    0x7624801d0310401c0c2c10000c140f40429510301003006411062241d010b0155050b0103685d16a00f0381d041d00c450203030060780c81c1c2c40480007441c0c1e40300d0702c00d00c500d4101c1140c0810148010381d51240d080280640c807006145c5d1303038600f038110403417041c00d16480100704280014856000ba503402954801d00c11704005190005980014a020003070000784000114005900840958015201c400070218070100100c41d040c4110034612501441820b6402242c2c0e0f00518039402008000c2d4800420015104201e05500c03801d00a2030604180016034924007005001c08920400004880c071610081007805604e5035a520604a00e09045200c01d0388241c46140104200c00e03220001d052040300c080040603840c4051410810b040d84640b102411000d00b44550384004030340c51074580c002041160030030036a40c1c800800607114020318a84150031508918601000d058412134a0b041e0385506400d034010f040340048003035403842a49291840d080c410040f803800070340a8034290812660310b0a18021080c1c6a902 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 291947724 1250 291946474 291946489
    0xb0a02040f0807380d0609060b040f1d0408030a0908030705190201090506071119050c090901060302060f071e030806040608060c03071404080d09180203040f030809010902 75
    0x41802da8110300c07000c00040320b11140b40740e00443c0c1100d00080506201c911485070f100e01044090035141c00090082e081541c603030280b006040340c000100032054035010f446580b900f00780034983d020015000046081d00c10050301810201d0300c0c40003054103a0304e41c4d959070040c0d08045d1102410ba07880b41d0f04800000c080801440c4a00344070f540c0e082d00c5100e1101007070359040385007228100b5640340c9010380300031450205060798000075030b007013450401c2c41503040c503803400c0c0381c05a00c02d81c1c114070303003541c401040b07408607007600342c4501141c5440d555180e65030401c0c2241d0071f81c800290300c018100400c0034051901c41c007a05102d4040d600031298103201600355082c1e01008070084000410200422501d80342a200c0e0300e014240240040c1550714002c80490164030002c0c200c80203221452408904110780030040328064003401c070640b00400c600c0000582011b07400d0141600d400100340c2640014203003442601d00c100c4d00488107800702015038905990b18100640170712010354807a2218000341e01c07242e1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 291948974 1250 291947724 291947729
    0x9090f020d060519030803100504090507080f07060c02041802030d08040510090312020d0e0a03030c0318050d080702070f030804140103050c071e1205031603060b070b0a02040f 77
    0x26809070359115090100d204071452500014032907010050400d106610a1090fa01600c0d40b2420103580c80c0c40310391051807445030581c0215441420130380c503001001000300382c040c1220300560464803c180f006c00785903156241070141c540040d02c1e803c2d1140162900c0c1d0045000d13175040d911880e0440c900c640200f03003000170701100c6101007003908061200300601000f0140900c3c41c003100800c02d86401d81d0b4010080310104604650740c81d0003203148400304001e80c2c0940d50ba1106141200e180002614000e8041e194074944000807034074021745d0b00b080c00200c0c0740d0030321150780c0200a4a031801b80f060b000e0b9902c500c050051b60841c410210f0100c0c0c40c0e24448040c0000e140503c0d00c007900c0c0da1410b01001105006250380760304250904050003503640d020b10a071004690b00402020300800c00036040344155a0390003001e084550130005800e4016005401180140e407120881c1c4c540b0000c3e944144c3c15103100d0721070030740203500400145010036100c1c550340340c1084c6058000351416070303101a2254030202c141c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 291950224 1250 291948974 291949001
    0x21f0f0c020a0c0b0a0e01030b270f01050307060c03180f081501141807021510050f03070503060a0e0106180605010909050903030a020a020a0506090105070207090e1207030909 77
    0x1020b60043c00405514900102001d098551500c2408240201504445200380d8141500c2d2202340f0160350b00d030400984084d249440090102c050302481200110782620148103600a100020501d1304011030701c03030240c40740c90325a482100c00039641154110440318074002c1101d01c2620206d1000c007961000d100400103a00145170401954078007210007001079005440b2403201020340c4030f144d10f4504520004c0051a006010f96955041c002d03414010300c500300700c082940580420080302c82c124400b0058940c2a101e00620038590028196030707000601130030758168812000070f549010030b6080540420819000480c1ca00da8808a0300243c03002505548030080d121031082c082540d0006e100c10040c801c20380180000d060202c8a55168840034181c4540c80e5000a4603010181c020800c20b58102d90010465070725103042380543e4001c12050794042e0040c0601c0700c00044800940c003400c002080c0e60b1014103441401341c14a00055480103030118240182c2d84000200c807052440b03183d4800c00741 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 291951474 1250 291950224 291950233
    0x3030105030706030b0a0b0a020708070605040e09010b0904080901021e0304080c0a150c020a0e09010e0d1106012c04140118050604061a0406080c0f0a030201021f0f0c02 74
    0x100300030035060010030342008040501d483d5043c0402d03039880310154100d60a1045140d5256000030040f800c000305038001a04d140f25100c1e00068072130b84240203004542c100c2c2c40c03024990301c0742110346007a03c066402c080d6105000c1c0001c90301007002c000007007011610500444080c54203004401800c04100c906968140d040030404010091051003034500480e03088030403292842c141b0060060f810701e140807036001c0080e102440300441d01d43c41040c0c0040d000f10360f4107040c41c1c506100c02501901c150160308209024008503004400c0c021440200d407207454030040c090aa080804110000d01240004800003079240b007044868400c03040c495000743e00840480700c000000000460030746210307025000481d0031b90542c810219102186440c0c204c3e500400c0402c025220408266254058980c0c4c103501a1030400300155031a400241d280060005590f8070b00d50100090400290501d0303480088e001d038000a0040a80f40f003400e01060014007031900c005110000404410300301d0303a441145e000580d01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 291952724 1250 291951474 291951479
    0x703121d0604140d140f0409052503110d0b03030405061303110a030c030602090f04020a0e0112020f0f0c0a15050618010b0406210509030703080f040305070230030301 73
    0x124051500c0700445418000c2607412030b03004c802456060031600929807018081b80c00c115110601084500a0801c0300050199080c0700c2007402442c1c449085003120103001c2d414202c031040c000e014200001c05215403203810000b03054035072005005030108856142c00300b00300202c2c0c00c3c0e48590140410034812a41d01010505514040e10125142d22102c0d2140039120010070002d05569410002d50760b00c80005605e40700143c2c082640a0a12078a1590080c00894400440c6a11846a140000c4240e030346441d2004080e880c10104e100c3d14000400c451b404008803544900c0f0035004007072190000f0111414248552180d0201c41c811000135080d00f0380b030380240407103413500003506034803d0040a250b0f01654074201d10031205106d5442903400b4030052845402507000980380d03284c2c070540300e581b0500091610034862626a40005400c6000c14003150119044100942030144105c3d8151515860030f0425020001d041c95024035144002a9427400b1f04021022280f41144094086004540702d50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 291953974 1250 291952724 291952733
    0x15030103060608070b18010c0501090b04030f121b030506061b0a0b010501020c101805150d110c0d12020702040c02070302011b11060304030201090803070905010201061a0703121d0604 80
    0x4505d50141803011400d00480c40c01604215074440b0040c000d003800c0c010040c43e46031040c05010440e102030f1034400c0b518100070030f1640200c0700c4c3c4ea01c0445940c0301040884100d040d50201e44941099a010800310720141c0b1900380281d00042d0080d000504007030420b0011921041040140300c03c1c400c140d001088135004002001000601500c400d001500c05144c040b00030410240490041200f0041c5240311103880041c0803c60742c0103050050321203203111000c01000c4602d44e2002a40d242c00301d203004000f92182e20704000341c60081001a026201a0000420880e402000100703c424141d50801c5030340010b903168403600d0043c280b0341e0040d004451071800003500c070119a03022421900032000c08940003070700d1041c511500400c00c6440c5038407900ca0742030403401400c05480c000e00c0d8060000a03c00100d401201210031107009900034040c0b56203c0e1004400391440d2012000c0540d81405003400003405036142d034212224100002642d144242d20403420403c0c00210005031382c000310300340300510 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 291955224 1250 291953974 291953983
    0x302090f0103020616020a05040e0105091219050c1002070b0610030e030d09060216050616091d040501090507090c1418060307090e01060e10080c09060915030103060608 74
    0x182108080340c1585141c0101d46140301c0c0f002800440315551808004568030700040c08054031014001f000302e0241c0b002d456009150941e101c0e0300c1407040c0c002c844645080a41110200b9182030603c1400e600540b4090302e454000042c1140c06014541031090113000c5440601004c034020241c004042c1440343c1481103042800f00b801d01050300340114522415400401c41e40c600304100000a502800b5080c200c0081c0120490010b600c5000803003003042c050000f800c14000e50506050100e00460300070103076401116440350283c041206c80010307840b42d03084010301c1d51280c010000801e40c0002da03030b22a802c0440710b800c500c001603034401e00d40c8000b55001e160000036034021444130380340c9643c54250180d00702104000f03d1146100000180e80c0d41d10500e00003005105981094006503107a082c05040d00021901ea140903e000310541e07008039124408650141480300e000c14501103a920502200c0d500c503408450304800f20182d0000f403a01d1900055000754010000064241c2c20210302c0c030b040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 291956474 1250 291955224 291955231
    0x160b06090106140702010512040f0507080303070801090903120903050d0e0c030c0d021f0f0e090601080f06031608030a14040b041e03050f0f010609091a040813030c030209 75
    0x600d19080180300036074200380200720300103888a885403245078a10040303510740709000e0200301c5d03144010b050004011034aa28449880c1c0b050003940d4182c0d0700c4404881d0b41e130000f00c80501c002850360004009900890744a41a0701c1e01a103403d115103881441140107440d4000c0080b000114005401484a0440d00c0340c141816056070207062030750102d000090340e44500d0007155216452005c400310465403803510403002d40f82c08803605417400180540c00b4000c1c11054003441e01080340d110000e0418540302070f0705840b507030058607441d0951300c40c52141c5030088030080c14141c00d80301e04850502100e002d0b01c01d400051584200540c0d480b401d5040003050f407000c20400180742c0c4414001480984050403e603429100070f001075441c10103080f207011040a00c00d6101a01030b010b40301d01c1604180c0049000078884001600a0103065903130f07a00325084400038140030340703090182c0a0268240d1601120302e501300f03010788088d90802d0010f121b0f103045900140d00455508000c1c2c0000c100f141000f40ca003d50 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 291957724 1250 291956474 291956479
    0xf21140a0801230a030b061003050105031c030e0a0b01030c050a08030f03070302040306060b09040e0f0307080c01090c0f030515070c030c0507030501020d02090a0e04081209010b06160b06 82
    0x501580150207425075406000e140614400d075144000411040782003200d0010006011103401030350b90402c0f08851000391398150140141400c800c000500900605d8100c0b0f901600600c680107401e0116040380c01d003c01c0f1403003055194078900041900420070903203054041c0401d082c88d5455807900800e000c21651200e4066584404104903512010080d00d184540c900c20759956a510281c04a00a21403a000207090078680400410f000e200107000d462085400e070744c204040c2100000440d61090428007911f210b03401007000500140c1c03201d002d070545007d008004220a405941c0e245c548420a400c800916018101c0400034000708000441038401c0c0300350100340904002e240104007080901c40035085c049044001010044100b0120b001140c11400031501c8100240441300603600c4203d001d403050540020100d603488064004078011030344204907500e80792501c4a0300f16003440080c2808401e540c4d0380341e04140c03610b4003001400340c158152186490700c08240707400b590030302010305007d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 291958974 1250 291957724 291957727
    0x7170114010e0f04030c030908060117010c0c02130207020d02040e1c110a03210509011a01020c0907200a060b0a091e1a031b0a0e040c0509040f2114 65
    0x1410f034403a81d000b5600560180707404015013000c0e00381600c65050640c420100744c8209400000c040785100b42001c50030714130200a01c421101080101c1d90b80c2412100603602044100070410502001e50040c0b070150302c06010702039004c41300c0e000902180d01c0c2c12101507154120003050080c542c402c403108075640825003403034030f80743c2082c440c61641c40256450050610003034402100c0124107050b410008034100000c1070040d072410312030141c0642401c2d1810454501e1403104070007158004607060030801e0b03018044010513620348400b164402d188458140a90491b1310071142c1003142484a200400e000d45404600d04800f10140070344d801c8294855001d180c542881e91481e01d40c000100002a10842d00206240e11603c85a241c0c09094203c511390520402404d511180141c004800c0d401d48102c0f800d088241d13031044000d81e1503004490080c14921554001d0219207401113445402034050100e0202040b4645c1c2c0d80703681070704001c99003ca51010008a03120310b55100030032402d01d44103103918030b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 291960224 1250 291958974 291958981
    0x9060601110312180105090106030213060e0f0615161a040305120402061312060507020c0d38060a06020f0a0312150b120f0712090507170114010e 64
    0x4a48a001e44002c40d140043ca090206110348650b00c41070f07251121140c000c01c1581414880d040c003c10703003403000324002d044140a2042ca04100c0c0700e81811038a044140040d180c0e103450800d48823140050905501980000c0e0005203040c00102804d1060496405103600c0d000508101d030b18144811a0300240322004000c0100180e800800d450031050122441001c545461001403d41d02592100b000014007002001606008040c0c010080b940a858100031580318448200d0701d840340c1d561751580143d812801a800540d01195000c500b0050225010310b1540b1121070107008032024600c0300c040310500007030180e9440c104203404001c0800e40001c1600240003003440d500c9040d1488003800340a1000c0c0500f4110540380c119201540701821036030109604d4200308003071508000c0c98804019031400000d080d000100b001940120300a0f00e4000e00100000009c01c003801034030f8002c07284e5000302c820000303910f0302080c8403c0382000c0f20b40020403010600f9181d103002ea00140d00030066002c450091 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 291961474 1250 291960224 291960257
    0x30d0f0603111003060512010c030b030606030604020907030f020f04060f080405060c0d090609030503070216030f12021006090b0f01030605061e1207020a11100f1b0204021209060601 80
    0x202d2085202601d8500032102da4090640003410654001030700500c3c00604030209990650010602c011140c5080106812100905946070070840d8080d070542d2000001c50701516050000b10b81c010210714000c03481c80f91410398001a608a5458401c0006001c1f9040c40b0a40e00700b4000030201c1040c5c9000c070500e01c0c040d12a291349401c0980300003000340300000d095041c00c0403500032421640e080070301030203020190325000b05503510440310100140550b41d58031461180030340c0000112500304048089980d01074450f807450500c0700c04207105500c11b0f03011100c00307240c450283e100180400c01001620340c400d141800b504a20707103140319041502d814810302180d070b81c240540d10760742d42ea680c1e01000142079480035a480d104400000b1010300c00c1800300f00d00300c0d60020300c10900341c6c42800044a0b91901c0c0f030500c00740314064480707100494a819a0100080d1180024810a010b43e01990306040ca854000c40e00300e0340401c10300403a4401541c100800103004008054101c0c40a10700b00b243da4841100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 291962724 1250 291961474 291961493
    0xf090b1f1d09040c05040c200a23060411060d050405070602100204080303130804030b0a020d0c0e0d02010807031104030303022706040605071115090a090b030309040e0a080705030d0f0603 82
    0x1501d2003a907903854500c942034458908882080400f0b1b170075244235904c8995442d95030140c0401110340c001c21540c905401d9007103c403c010b0100c0c01800400f0140c965607600003a00d00300c10811030300b2110900c84260400900d00806024a024402422045003050002820300c4d408140300d9600710300400c410010400e00200300c80d4490b042c0035100200302540c1c906002c0744c0c4195130000c1d10018480d014400304940a5000b0030441c0787e0142c0410865801d150180c80c60b0f412071a81503481242c9040c21401b42d400b507801564011560320380042c50341c54404188503a40c01c2500705900007a03000c00e05e50b50b80e01d4070074142413107a40c0d0040018401c9144a00258a070b10807406036504100380880e160041000c004c188056600006203480405111060f081409070040c5d820244181c030b0414002483c44001d1090144210000d005949080021001d00018002c1c29450140521500310340c4c00124529030040e001e064401c001a50b40d42240d41d8522080e90301d1242d0540f416407134010100001840982d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 291963974 1250 291962724 291962729
    0x70212090109050f03010e030a02070807140d030509030a0501050c090102060907050a15090f0303030b010f080403120b030715080403090609050607060b130c05031f0f090b1f1d09040c 80
    0x65132940b1a00d840e9000c0303400b41100414100140c400460100281c1c3d030082656010f44144004441000343d03503071003440ca080540380601d508640318605000100344507000500c5c207c0310140807107510403900c0d130b41c1d40e0841d5800c03144a4600c010100c1c3c0b002c07503582d0511400e5000224070004040d040c6c00c0c40b00150908880d0f1080e440032404402e40c0c803081c1401000100d005105c0b201d4039034030169032070401030040c040d0417450900181820010030441406900001e0042e9099554084910310307443c40784c8010800c000c04c0a90621036504000b500c03814802c01407108520035551003141d03040916024086007487c0d0840410700004410911042c0c6a00741550b08443d00000b000c40d800403140007140b100803251102d031182a06090915010300d82200c0114042c0c030030791040408490a446c0c1c0000c64403041c1c02030001c91040e0140800c11992140c00c26030032028010854141400700038010060300b460031041c0c002054000d5070840100d40c51050300720071b64000365911031046c60700d6900d070340001c036450 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 291965224 1250 291963974 291963979
    0x80607030b0d050106061e172d041b05010206150d06110c0a0507060f022a0901270903320f0d0b01090302010804030c0809090f07021209010905 63
    0x6070464809035a95030240c03405190000000c010039501c0d460000d0010040030403188164034540c5030402101d2040040d801d200d0401c006002003621901e0030480350f129001c22400803000c2410885a6880c0001106070140b0311a442c0d031880c0307a0a100c1034a14401c4194045415500414204000301074118841c01100c80d040300c01e4402c400251510790014105040c440382c89200100b19180080400102a0480380c00341088880096940004803003150181c0384020046e040400706424421104503a40408120901d41e03281070720401d03010a02481c026030020662030100000085421000c06a840c08401c04150500088025840207040840e0b00400078100c1ca8040e11500e10f02c0c80c6184610094800071440030356100d0003400c03030568503000202c50313019040c40c1c400b40702025801451130b90210303507041c2c581110360b540d9070303d090703035100e00e107240c1a1030100341000080102d95420040314030590a20500803940e04040b080240b034000181904510014104890f00311683c00111171000c94904 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 291966474 1250 291965224 291965231
    0x30b0708041a150a080106180905030415050a08060301050c090f0f13020c060c03090a150204030606061205071805040b1c050d11121b03090306010e011e08060703 71
    0x1203142c14600e51007007405150300c0811807824807560003e1480c4000a500e01161041c0001d03407940700700ca00b01d4580703100c6c1c0c0400d00b007102c898150358030560b002455514000c4050342e04199a07404220040c001c0014000d0019100040f0701c0380c441d4002542c240c120700b090f8001c000c2c510300806010110b220b0f40c45020702c21254010801800d5542202c0f42d44608130103072400c15a14062030340c0f20065004205600f01600401c40010700b4020038505480c4541100c000030209942c50ba100e450082d00b4074101611103036020800403010a2003401108001c2c44169100003000c9942c541c03190403208040d156800300002c032614070350b201c110aa5040c1c02c0d507004403400540000c48000207108040342900e81d50346a04928107000c107119022610820010007522218924001e14100c1516a0395003117a400a0740f1092082c00d00f18040d8040882004145800712441c107003841000030f00d80750090f031020350030310124401400a52090021442c1014448440211030740c20309244940340c0303800901d071804241e40c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 291967724 1250 291966474 291966481
    0x50601020a08300108011d250305030c071a0717090f1504080f03030c07030f0509190501020106050607020f04020d110706020703021b1c060f060b0c070807030b0708 72
    0x814003440c201101e6401c200d0f8820354030280400d0301500c801d00c9440b00d02d5107032100c074040a03061001d04805888150014040c1c910202c0d00002d080c00702ca19600c0b204031280c000100014408200600d00e90141e0001444840e25207600d8111202d481e1035000091002807190400040d200c00c90011074101e40c0c5081503d908581d00860b80204210450035444461a0106410704c3c2224004006441d419425140f415140003030b40d5550b844150b500c180300101c02c01240d1b0100f845030380309180c6201d02d413404074688034207200003d45402c20500c1d071a0201000c480104400e60302449041c004002c250b80b02418401180c000031210101d000c0001c0c000c13a0009103031401a041a40070012000302034036580d0310b40f2014280400290400c0301c048015102d040c000c0c0715459400100c1d0242900002c01022454552400c10424010500002c60b00c01e44ca4030030306c18a004141c025400600f10340c403045a03da00803004400e2503c0d940340e01881d110b811810040c00440c42081e5180da004515080200c5a030700c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 291968974 1250 291967724 291967747
    0x31602010b04020f0c070b0717031b0a02010506041b1d030c1c051501030804120f02040501061d060a022a060f0d15081b0d02032509050601020a08 64
    0x2051071859802880000e10405404591028207003c0e032181048038840740c0c0b940e000100f50302c03812201408040340c10354602c00c101c0302c800003941e000b0400c80449005801010304010753350080071903031340580d458408020841c20706110300b504001c46070796021186e088808029100c2454118600404115003100e807007603840800000825038400f515420034005081c40240900781610021605401400119440500c10102d154140d030b400c40308242c0392a142c0b540019107401c000004031000e01d01102c101d00582c3d203620490340240007503222001c0e1002d5444454030780e403451029a5101c0d51082c401400705940c002143d141d1404039844002000980c1604a004143c0007401654030a80c00500d5104540d0290050b01d00030300c0d10300701400441000d40d403c503a842c880d401b90f503816038800b103030188a8581c045411296071202402640406c400c41c1c01003414a40341e401e403050300e20311840c2000c0488032640d41010080841041c00c00450801c0c0700001c0d01ced80e107040400f4107055008a00041c044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 291970224 1250 291968974 291968981
    0xb09010302090406150302030f0903090f09060f0901230319230106081507020312040308060f1801030212061b0d060b131802130314070b03071d10020303160201 70
    0x1800715002203100ca1789041c4005010754411501c088443c040100480c400841c0001502c115a0307009021010800c28107041c00100c10000340040c1e40850341100c0500c49440d4542c0c0c880c0a0980c549140f10581c120241850461000710070150207a48601102d02000f41000802c0b09820340c0700e944c610242180c08092101c1c0340c50903021060952800c00c00081a00c0006500111600c400648240558944505076101c1c000e0515a140700d59100b000500002e00c2a000198031580003012001000c48041c04520390702c0c0d4031102c81c001c903135900d8014815071602c070f10342e40c0900280d00e00030002480d001e8122140fa02c015000b91359500c0c40032a50040e00d0720150028000723400403a06803500d400d41e202c40d00e642d50842340300d4180988a9502c005500c1441b0303001b211010101e0840204105180d036503000c0080c02031603121301c031600600300d003c14000d550708000d500a45803035a0f141c440840f603c40c10018442c7c100300b058801c0303100440c92a001d030340200603654822132090100b06103810356441031b07024 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 291971474 1250 291970224 291970229
    0x50d0b090309130c03050f01061e020708030f040305010609091e03050f2709091209060906030103121d101d0901060f030f0209090105060f070501090b041b0b09010302090406 76
    0x40c0b003114008602841c0790b0310104c484d000b5681e06025946400c60000c031042005e004810001d040d0100c0d40420300d65640c034404c0c41124910440d824255030303110b81c41c1150480c0e0194290118001010002d014090103004081c00c00c0342c80c100032414a0b0790356080707100c000ca29458100a49034601070b080c5401a0165070800c0d0000c030505680b1110143d1b01d0078150180c40a05040e9000b5030b816401d00e040c800301140c81007002c070300117200c52440703080240446d40140783c0c80d070b40c0544200100d001545814024600075813044103026880f140750240900002e0041c4100b010045488603981f01c43c0d5110300180980340c090341420035859400048142d4045034a0500b40d8101e060100005610340c0d200e005490055915a8200204c0409044000591048030565a8041c0d454801444a481c00000528451501c02c052518051440c0d89443c00d595002c10103075904500c5408000600c068502d01c2d0002100c1c072461034080c5070034920180721601814016a04050340850030f0503150f1580d5001101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 291972724 1250 291971474 291971479
    0x90c120406050412020111091e0a06030b1003020906030402040519060b0301080114010e0c03091006080c0f0306070c110a09051824011818050705120304050d0b090309 73
    0x2500d418244000a040243c40c01c66206080d8000d4031501813061007250710070401290043c1c40c2140d00f0081000c81d4603921011820b1a00c1c42c4a0700c8190b580e090908030050050f901e01003261907080c41004510320500c2500c80c20315004002d0a10613503140d9046a51182d4104ca0014042c0c40d41517101040c1d00c1440007190050b81b81410109090341c680e0060742c120780240300240501c215900010300b84640a200701003014602c1c0d07010a5001c8481d001446c0d01010040032107030003858280035602030754510360200c44030790454101354042c0e05048040509816080e001807280382070454004098800c2103074041d10032658148400702c00d82c0c41c841c0d41c000074031014809101a051041c0b14000004441080d032246101c2d1101c080405920b00040d40e80c0c20940358520303401d50780b0703000b112a64810b40c450080119603892000d18041030701c010700e101615000300001d00e071060070300003408050024200d40d20b50719032007400100074550fa0342c1e4882d080c080e80038050074056241c1440e10752960003800144d55 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 291973974 1250 291972724 291972757
    0x5030a0c031b12140d0c02060405060c011b0c050705060403120f02010209060a21090201140304060b0a180501170a06021303170304150603020906090411060408150901020c0c090c 78
    0x2130003031202000b261040c242c0e060319541014090203460958103660002c1d0440c105000c1002685080409002404c01150000c03444074241d280391040401e078920440c000c2106085510140042008a54064042560000c0c0ba003070454035a102d02078005060f10081000200d00b40710214401e4060b60f0006a0160209480c0c02c900c400241080104c0c450070780754500b0702c864403030411020780120114035070180c4800c0c01144485015103026071008109481003912981d00341010b0b10380d0440300380185802100c00c040115000040801e0740c406901c001681905070b00110410744000c2802e0f03229030380c01072005a5400c0c03e085004ca42003404d13072020305451800111242c8102b512001544918452101d030b80d9449188900002280c4181c080650082c22440025442d8201443c03144e410234042c4580034045d45038400014419403181d000070344160800400301150031030f038003c4107803c8070741c000086d820241d1021110750303128490740700d2610688002c00800c0306105400c0486451248031440f81 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 291975224 1250 291973974 291974009
    0x4020906040504051617160605160323031f060206013501091202030a02150415091518080306061b061f090209090a0c0509120a030905030a0c031b 64
    0x140121b4901041c490301e4022458000b1020300c00101300c8080d00c0294681d203051905845480d109140126012001e0281c02c0c0c44400c40d4032494600121410105200e00e0f0740ca2a28880481c1e21611400c3e04d500d1841d000d560600205801062150540304400000104080025100c2c909020101c1d0407203400304e5885800071400b00d06411903c06d03e4019880302e140710304414012a0380744034021182d4016008619451000b500070031000c0e41141c002c070b880d54200c04603004a10700301d038041c2c0000c88010031040f2001c0b2214000c2c1c002d0661075010002d44c07030010806511006981c1c8401401c65108a0300021800c010454180381c000440d10908103d400a00d480b4003c41a0344108004807262286460030008150310799008850380e078640a003001e2055150140b021020702a0307190810f060060600030b50303070b09840b00f003004449041140d0080800c0c0c03545050240003094030f41c2001d4080d42080e4510004201c90103260011694004945900443c040350203e070381405607003000b840f5000481c4135 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 291976474 1250 291975224 291975239
    0x140a11094005061f08071b060c02010c1e05190302040e0f0103021e10030e0705060f120a020a08040308041b030b07090501022404080906040305030408010c020303040209060405040516 80
    0x15104400580764040040d40600c26480580c00030240200040c03070100006d9101403052042c2002d0000c0e100c28014202055507070700c2c064582e8440c141005030b40d01c4000c26049984011444501004e210464081c00110b42d002005417050390000d88842e9901d0801e0b103a00780c0701c0ea040320010144200c9040b81c1e4201024507107881c83c800c1c4001c0c2c0c4994043c503044214010f40c4002c00e00200e5004007110b00501c07410700c065010f4008000708270300a014001000481d512483c1c01407910040c003400c0e06654840d81c800c040d10070b920141221481070300c1880100300564100210541058040c104451542c1c1c0701e02d481507101401d00302444d8010102d00700007082141494800d4081c42041d140d1107041d58459004a940c1d800307400340c0c048010b010075010401c00c410b041e6038641143c020458245130690f50f50118603980d10036442201e195100250030171150b0310078030944014403e5032004c0d6155003029000030300d03203060140120348603907030b19008601081030800c0013440140069080e010102e544040303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 291977724 1250 291976474 291976481
    0x3100608101a3001050709050f12030d0b040e03130b030a180b04020f120c040903050d051018050402090a020a121104140d08071b030501140a110940 65
    0x21242c1d0345010320790100d0743c4100180141c5103e0007095a81d004414034020070041003104120250740c00c0410007035444400d030410b00045c840c240c10304801056560408040c001111340e05070311712406402c00d1100003003d000c403400d0b010480b800c5501d0207450381c03140030080c0c008014200e607090000701e62001c0d400c1000100317a601c510540c000c44034122009202e5040c04614070017540645031300d030401d0511003810310b000d500c03480849020f03140190814100f440c4d020102d4800381c488941070302d26140100258001856903c5040c03900354814016401d01d40e0104010000c0a810107412580215141c400f1501c100b6400d200045030010900141c594159103900980c481e01912412410314111110703503040c9021010344142d07100e02000d1030940c0c903444020a1004510ba403400c1645408800004201e090103269400b04140c0344c0c0345400d083c594a80012644071007076004000c030081c811300e0f0b40c5581d103034001d40711080301480c10f08540340c3c035900c14000c5910406500d9080d45000d134600300c40c00a03070390 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 291978974 1250 291977724 291977779
    0xc14151204021509100f03060801060e040b180c060f07050610150903050606060714030d050f01060e01050d0b0303041a070501050603062202030712060b03100608101a 73
    0x740d032800c1d42d1140c0300f020402413080010b0980c01003802d03020341a0061140305001c0c002000e52400190150300e4032011130a42c3c020f58003030764042c142d075402e0101340581021425040112186562000341151524a80711007802c0f10541c442c0401146400d800740d4004100c03500139600100b0f48840c0d29142802c048501420b020303004c1e40b64a10980c410b0342e180201024016a9044001801560303641410001e159202c038000310b900e402c00c241004a03d500402c050895401c0041008c1782070700e400f0903500c0580c0c5e0168400c4040003002840042e890340c20804907034802c0b0030514082407408001c000b09165104607400702c51b09000da42c3c1d10b1840c80c1108005004003502c268001e0086850341c4c000c03da60f4860540704c505031022010420301c1010710784010408c2991009e01a500d045503280302844000d41010400d49505464140c02c200c0f0b4170b0180704c8040c1c040102d80c1c0803c60b943c24910155074409210100c485090351f664481d90310720b941071403241012040106000c401d0022881c2d004808030541 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 291980224 1250 291978974 291978979
    0x60b0402210c1b21040f0b030402040f060602030c0d021603080a090e09030703090e040201080f100305010903080f070f0927060303020c0102073006090203011a0a06020a0c1415120402 80
    0x10400c140080c04130701c0c00c4408403080c0c00b0703181c001d0302e05004000c40d2690010308200d91183d0f0707a1442000300190781c0030303210040c8031940103142c54024213502e850810001404580441d08183d1200c10426148900d00e002d984e081000c8945403100f00c50141c8803500250005c0413008040004c02c01d50100000050141074403d560308640301d42e444448603022601030340c00070702180d008400904c0c50360611607400c0e031040305d07100018401d650700c2c1c0f111800c5a90100e42940020080790810003080c0001c420f0030703005000d514101690b81eaa0000041c068203041c0500c8c00004020059840e014801490b007001c5855050070400c0035583c0c0349001b942e11120700c8109030260280c061b001416242c0c5044a1032207012448071905041e07808954018002542c5900b01c0e0701e669100340d1500941c4003440748404542c0d58401c01c40c40300c1081404c002d585841903004408540c00392000000145118030004201c44181c0a1841c3d8907aa04000039032001c2080164900d20310b000c07404d02540150f80c44200c1c0118001d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 291981474 1250 291980224 291980263
    0x30b030a081e09150c0a12031b17151206011715090d030f110c01050a060b130311030c090a140c19200a030903060b0402210c1b 56
    0x9110410890084520303040c1e201d5003a1300e400f85003148040007440041114000c1d00c24603030315551a620200e5010328040700086e902e4449080512820080540742001400c000300d10704401c401c5001c0140b0000c0c030f140000201010084640c0e250a28800000c040c4041aa4195a1150603c1c1d00a07400701107564010320491f0f59500001c40c0c1280307082d010b15241380190030a2044850705a010301103144085050b659200a24114010f0260103041c815104500104003410302003602c00a880c010b4008514140040098040d03511040c1107000840794003841d40600f400603900000d08006456a803990031079014010094070140d10360140d01008541446c065840e110134106041d180034602d00e02c81024003401003140d4150003a6044070301000d21181c8100c1112411580608042440c03c040700880c02440302401004503078082c0800e00070040d501142800e0b040b07641400d0280341c10701206100000b03000410351900a9500b210300d8085048520100801048203403592100085910390701c0821 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 291982724 1250 291981474 291981517
    0x210a031805010305070203041505040e0108010c031a13050a0902040908030414070b25170a17040804060c030c060615111c120b090a140901020405030715030b030a08 72
    0x64440c4034001e2142d075009600f824104140040030011405540c012b0180602001510104102d4402d028184240001ca19124910800307030554900e0703c11302c4200d03034072070325410b0454840800540c010303c4c12910110300c60311501c192030000d02d0043e1010390414107040e181d60505c000e41c0000c50199100b0004108801d402c4000c458449080e402542011602048072545c80ca4040d40ca10b01d0507004643d81c403032602200e07590b0203254046490100000500460700015903504040380c0c0307580b81001501d55400b440c082d42d503c0b4951180380110018000e01400001c00c1c1442001c508240300d030303c01c0d41040069110342000904030000c6112100050000310020b03000c040104841e45020313078201c030b20400d1804d00103090b41c075025401c18988001c1c0d6503402a030103d50744c0084041c0556110300e0b0004030000580240001a0401040d0400701c1c2e004100c104250b4070300041c1401105e0941c0601d82031303460740760811409004d030070ba050b85d4548200300c24071080c003403840001c0451201400c81c0208029 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 291983974 1250 291982724 291982727
    0x6030c06031406090618162a0204020c071a0403110103020a0210050601050d0213080606010c050d0c14060f060907230a020708150105031911210a03180501 68
    0x180c200c882802101820b40200351182800c0c2c0c2180d8000500401140c581d5040d00e0300101c0d988402c442c2e1000110f40580070340c0f0a5034108003c000e0b51210441100c0a90542103111034100c0030f104402400f45600040503030b905081800072170040c1440c443e400c107010f14801d0f04d28080b034110f408140c8a0020304200310b900740d8081c3c800c55a65145503005403527500307804a94103004060007448581400820450821130200d540300070221700d48403042c0d481c0b18604105c5024600074005003107506001c015103044020400006015800456500d001a094000e84c9080002c030403140300f6101c11482908240080d520141110510510090718218641e5aa40e8000c03181440d40f40741d1503240000003068040000001d400516003144a80111805a83d483e01840d2406101d04039580803900c01600600c40c501e400e009030105482c114a060515500d0742d180e00c5071402c2d820304000c3c4913403e05404165140c0150340351b15035041d2918282d940e4010700e800c01070f1012040c042c403a10200d91121002c146507 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 291985224 1250 291983974 291983981
    0xd06060e090402130608030d020d0e2d1204030f0203121305060313080a0915030606140d1103070201060608060603070e06030a02071b06020624010e0109120606030c0603 74
    0x80060981c03540d40c40e55024842407010b5403483c0169961500d40c0803a2502080009041e4001010780c0180d65442a0b42890201c070301d000e14110032034228000d8501120304510100c40c1c00c603005215030300c01c8918500703a6442d00c0000380748894181004100001031000d089020244503001341c0035111200014004043c0a119070740c01c003030010410300800e0150741002c07805140e0107043d034031700e180000d41503440c2c608294100c56003810002d0400e210500c00b0100075010728841c4481c904013400080d00b000c10260004a4518850060f03031400700300804501c0003504107210a4445440342e80da68102050002c1c0070304018001c89002c0740c00c200120349107081c000d00b203278800c00544e43c07600d08800602e0100815540701801c240d6280d0340030700a01c00841c40200c00c242c0c02e030315104d43c1401e1013031030404040e041c203d004040070401082845a812403064640300300c070b030203042403078a400380030482801a912603c9540000c621041d140003408100280c0343e1050742528041e2800038242c0d542c0306802c5068 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 291986474 1250 291985224 291985247
    0xb0102030f21090c0a0b0a0815060706050103051b0109050f0613151e0201050411090c0c060a060611060403050703120902100f08010602070b0301030b0c040510050d0606 74
    0x140e0081001c003401400d810007030300e154909421a801014a2002c00c100d900310300380d801440b150010660080f8614005203070600411a05e0440750410000040281c280c4c80c004054103002d1040c2c0c81c2402c100d9503448216800350303a100c0410816561281001a0360320224010140c2c44110402400303015800ba400540450343c0003130420007109202d4043c08481d402241d581c05015641da10f002c903608040d820f1840408a035036880f03081c2a2001c009048140303d1200b821015649803205000100318000c20486680c0425a0b01d07028585403c003400d0401d01c1001d0301010710340981d1061000070641504504111403066039904642c1d0f418400399526210242d42c01000325504010a10000340254003411881e82e0b0b880000070f5941c00358010410a00d0351590410009504130060313002c01b0f4000d60800d016000b68402881c1e02d6042c0600300e012440180005400f0240400000c0e0502d95a8412600a1704025200c143c0000000d803025100703030003910075030721010704242001c11004e10880d0307001389 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 291987724 1250 291986474 291986477
    0xf050703090b0136060f03031812050c040b01020f0a0b060f06032404110304230708070b0c0a05070605040303091d01150215070504030204050136060510090602060702010b01 76
    0x18200c104c0d445030000140200d804039051030721504001441251740d10f00307000450098440080b1080480b13440030711070320150000d031403464040b45244003040f0005400c42c01c00380207070f600117000745504005034544a422468403140c0e04c500b0014904000d41902c810780a2001558006e11070740d1500c0030082e060208a81c3d04c040075601400440a0411094650070100c4024000180310711485109510b40e80c0300f22400d0302c02040c00c41401c03045000480200680301003032406010842d040000c019203581a030710508074050004a039001528405000314a000d80c1d02000b16042c0720b95480307000d00950030030311050b00400c0c100c240c0015212041d40038083c1440c48902401c145a0030505105400851488100110b2007514408001540c1c441c6a840c00f56113542c603040e0f20386d840c600c104070640c0c00507000b0b004c2c90071001d40859280510004a401c07038200c4081801c09100b0301c03c6110005003541c0d0b001c45da100800d09152203040c5d8000b000d2805807419582518210703510300300c0590984070821000c03030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 291988974 1250 291987724 291987779
    0x612030307140d020d05072c0f0109080604051e01060503120c1627020702060703030917070609031706130c09090e2401061707030f050703090b01 64
    0x98016200e50424103103040710042c1d25052107101d0480c03034100c1e000100d1500740c0555920038040b00c42d03000190421048280390340500884090920001e10042c100071171401044e06454036101030f80102000340140ca00c8004036a20f92a103400d0140c1e40305002c42850b1620785085442c1105050706000300d5050f1000a0001d1030079500c01441d60704998003880c2c605d2814081c04203035070f8a030050b05044a00500903441455009541c203501841c00808004803074441d00c1c41000600d0040c0c80d00c9003074942076038040c100000c03221600e0030001d1001e24401007401510743c2c00a00c0f1010000302d540a00c070014045e54480b80c0c48901c80c001800700500a641b003070351011103041c00004c441242c1d0410320401f2a18a0481d803255950300203441581c0a148044d0244d82101c0c921861040b03203e021050161000b4070802001d5142c041c01505038a100c0300c80e40c1440803280b00040a8902130f81041d000d23600400320402c410300d081d0740018010411030038100c0d081c040d10b6000054400140c05a41c100e40100c05061 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 291990224 1250 291988974 291988981
    0xb0607080412080903010e0c1002010c0e0d020a0506030108010519020319150f030f05150c030a0c0e0a0e040b06040515010c0c05031504030305090712150f050c0403030806120303 78
    0x482d80800145002c942d6810b04000402c41504c007800707196800c4034007100038a0207500d4030040000b40f8600c841b44d0000c43e85040200c241c41c81c0d018481c421074030310a6070222402c4040d030000c10f0390340308550051500014004000104000c0c15800345109907032103101807a00e41071031000b00050380f00581d6005411070100341c45414168865000303903841c03000004121a040c2c1e03661104c020303c000c281e00c01d0301d007210000110818800c040c000318028003d4081e0f40407042c600102c0301d0785540000307007082d0003040e0b0715444649161b0141023001002680140f41820b419510b00e541e01096038125000c44011081001240407405e050060501500b014246048854a0030004462205050a00307940c090290f06d800512500c0500c8060211002c0c81d203224401d180030300303020f429200d003e89030400715400b240040040007051145028180e0b400081921104215800c0c44050a5085000c0f0f282502d44000d2081c403070f1180000b80100d900c00c6d218600c040c0d883c5010031100150100d006030050b00200b000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 291991474 1250 291990224 291990239
    0x50604030213020d09021f0e2e03060306020d050405190506070c0c09050903030601021504030203030604241401020c0f15030c04030f0602090a1e150909090609060b06070804 76
    0x2900d500d0030855130005046a064002880080b075040c12006c1c2041480880141d00b6441804036104030000d48a420b491070580001034103509000b0544290000d0042d0812080c61080e00400025604480f0941d15015000c038400002d040c20303901115148070301c825145d42c4003c602035035012940c01001820041d5501c003015101242c04c4901200da4010750030011401710168401c160003110400b008580b20700d0710800280c07504548805400410982100b0000040e60000032039034420030983e00810b00c102075454440c50340b003801a5195200182150204403075840d403038030b01c8007000c00341d0071070b500e41261030309000d0720310468800d4a8004001c94423243d0800900e50003513421171926040507240070360b603445001d212060000d0807140c1640010f02c040e40b40c0f40c13014540015054410316202e90072080303028444038800c14800e043c2003541c0d00810b080218000c0f2600c2000b0b002ca03031401d2080700e01503d8541c00811009074121402c0303281c0b01c0082ca0905103842522016a8408051890542080c0c0c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 291992724 1250 291991474 291991477
    0xc0b0906040e01090213050d05100c0c0b090f01050c04051311040503070f0812091008040501110703080118020906070321180507060e01020a0f081b03030a0605060403021302 76
    0x64240c00100801c03002800c4022115414020f0041d07841c016103d49a44401d9031128125900441c8034009103003c0801264001c034100350141044000002c0c8003d0284040d1200040d980015160304030400410211190101d0014105141c2200802495541c18007903581401180281904001c01d4486a20307041010741c080f2814403500554103041594510002e4501056600148021200c9400c2000001c904014020355a400200140c0c1800300450200341410742040f0003108000542c0042800d0107001c1d40500c00b00e0800001407951261141405401c00600b813045a02100c040d50b11641101c9041c8203407402040024207907440c2a296031000c4842188c0007005c1620001401800009400c4a101d4480a800c074818401701c141041e080c03450402c0c0043c1e11003030500042015100030350b0703400300301610f13040d0780944603c05101842c2050100d0340104100108403111007200c03100ea00788000003861107680a91414807034140c031f1300c0c01d000d042d0055110003900142c0d00e10303019455186940 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 291993974 1250 291992724 291992737
    0x40906051e09070f0b1b190c05060708030411040b0406060203090307080a0302060106111501061d0906011b06020405121606021c050a020307120f020705151b0312040606060909090c0b 80
    0x15144520a1b402c2c0030340301c0c102049030100003e0100a10440320802800c80343c40d20041c401210340d1030420300191224a400d1000030002090810705071111101c1c0d60311f41d40038012422000c2d108112941c0c540e000696070345d101c480110302c82d2045180000d0301c2180000e141601039415405401c4507442d02400b41c03001d0003090441801c80c0a40e04070544090701045c1103d00070001d03940d034288000c0c1d500607030b050744040315011180520401c004101072a40c11040030b00c0e0010001c0b143d4040e40301541044070090140e42c0201703030322080150984100c00300000301c2203444040d1014031404985c1c1c0703581c20303030707442040128071222840342001c0507070300a000318040e01c0341d030310b090040c1e074689001c40d50b510f92940d210b01100c802246001d00440d80c8aa810400c500107040207450980c007019058401380c4982c0a010550242c400c1400b159400d10001030003501d840741c0b00703c2c1144419003090f1601c074016000c1c40c0210800940a110001051221801401d50035500b04100c040e405051801d144056070142 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 291995224 1250 291993974 291993997
    0xf0303050304050f060c0405012d1409031603060b1f05090a080d0206040c080d1706010c0c0e0702061e0609090c060f04050306010503011103070806040906051e09070f0b 74
    0x84c0c090812060051003210321985244801640e2035042030005000140c0c40c2c2031501481346000113410b0f90100d03c0381c044140454034100140400c2d00c4010402907403041049443d0503004000781c021410303802c489002c054a1160400b40404d20110080c01100003082402440201c03030304041c080031500030b200401c070005025111054240e280c2c001c003440c065017204c1440040e4000000c0100744251290140017600c0c80c6405800000f4014000420031100702003250410000000071a0840c0e0082900744c9030a0703030100030904159378802164102c0001214881c015000c2c0d00c00003025017040c00c81c810052043e01c80007401540300e81041c4140050010700c40b40070340c413404100056655550024040d045400105c4d03d56460901040c50304044d01030740300d9406607041c02081505103140f9019254000f1a0b03143c500750603680c45000401520748114080d0406180c1001d01c0301718240403407003040844215107146115115580c0041d503c0049220700d441c00100d400c02400240884030046c22405d022 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 291996474 1250 291995224 291995233
    0xd08061e031b0a05120615010305061011072411071214010915061d010e04080c0111070f051509030307050a05131d010e0708010b160f081809010f030305030405 70
    0x180c4e000704080c1d02c400c0c5140340c580d520950070400d000c015500780101118083c60140000e04007a40412030000c4034045c45824003101c0940401221f4041010100800c1c070303c0b040c201441d4820b2000b00060342c06421160000d8800030510f08140f4000400030100e58440c6010405805144c480c3c000c0002d1203a41c1e5011552180c180f0008104205003c454950014000045845c5840580040480100102c40400e41800c00400c000b41180e001c4660081d0001c100c180c0c1d40001e01c2009004085040420b5010500481c41d9030030300000d812148a618800ca041300d9404622001c00b400ca00b004071402c1d65540c1c1b08000140510b4400e001031b1000c10140d0600906101c105111440703404180d420a40150280503040403081002d01901030051564200b0002e003030920310750080c038000c014054242c060500049010350311130ba03626100d40050f0050707140c125542192900d00081d50189420b07801100703d81c3c0504140780740011b4002d04070b803810302c1c0621181e861a6002c0c1d4541d00000c005498501a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 291997724 1250 291996474 291996479
    0x903071701150f05121209011b050a05150601030b130c02011401080102030702011d0714010c0515070306090606020a02041a090703020901031d1f06080d08061e031b0a 73
    0x580d98107140c06072104a81c4500b1103410700d000c1c0121901d102c101460303d50b01c20711140c96410307210000c5601121080c40d0804440c00c5a50103225544110b000c01010b2f88558040801880808100c151030301d840e9408140311303900d070b450044094403403100865510482c181c58024000b42c8991011140358043d000100b070119200801d420440800d0b80b020b05565000010440a0303035083c81901d03d207117240003440010b005190150355a80b9602d000d40d80c0d03180e480482d42041a801100c05107541c55102041758062810040e0543e5441030580300c09000c07034186500810704c08001d00940c03007500c0c00780d40101051038160302004040d00402549801580f003a821964454403004445441409980c90250390b48108000040032200c2000144d6107480070445034160304a004504840c1009001c1c0c423442e50804a0740000300248800c2d40304050521a202124000d2a08806104c2c4624030444220304c0e20125050324010403081c1a4020341c2c0f44c0c0100544040010902e01c0700f200815015004045094 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 291998974 1250 291997724 291997751
    0x31311040c0c0b011509090903023a0f0c0305090d0c03120219080d0b03010e030c07060813030912050721260d0f2405030f030903071701 60
    0x140310005a00016084012090600000c1001c0130300400100c80c3c840c01e48114008024400001c03809440755054880781c0c1801451700c20007984182c44241e40d40400090010004d2050449096030700115590903103481c41401802410010301e52032182e107903907180c40443d036421a4241d20001d261944481884072220204054504150103144076500000030401480c002038500b448010484a110035007055440000e01290b06030784204410300f801084220780708000038007405520031411903900c4040391500d01048000b4400c02160f034103888103040d548580c80d840c441c040f105000a804501d00880800041c420075081904041c050002e0b1429262141100d01080c003500c11a840d00303000904050301441254820164604035072902120300c074440b40d42c3c41c4034034000d194442e16810f54590000611840c1600031030500030b0030b03856010166503461002c00e020f0000b80103090192144403040c5003124000003c849069000030018083d485c648682415010000f108181995403034030305401208 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 292000224 1250 291998974 291998981
    0x1b0f0f090c21040506040512040803090f13091b06050309030405010e01090b1c061401020606090601111e0c01110a08030406020c01020c010618020a080a0504050708031b1c0503131104 80
    0x907846135000d0007050900381403042c940003080003010440c4a04205c00c0100f88400801c54003215410303600f0011414a00300002c0215240c0582c1078010307418103c0040401400c052201002040094042c0000d501d8104c11200742c0401c45040405607c00c004c240034540c06a905000e5904051411600d1181c40d000e140b51950020071200040c18000103c040c2084900c0c0600070180448101c4282c2160a0400003546c8441c0034200500a40d903402c085240c991080ca15a40303a910b550044602030018901c0c032010b4040f003c4400443c0b03001d0420380e01082e612a101031500d00c00300100800b0b200c41181c0310903525502c040c204031601d6030708102803006881c080c0082c0505248800c00021240e140400200c0c0803030000e035112160510411460741e910b5005004103804c54142100042c03036503114500103203003007510f810070f290318070020038000e06001e1384041c505403c002420a035001c1070b4542e020311010003910715200b000301d001171000404060054000f2100d60780590500304101030780c200490200c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 292001474 1250 292000224 292000231
    0x80112080702061204120c0f0605090708070602160e060a060807020312130b100b0a080c0d050916080a0b041415071205010e0601050403150e1b0f0f090c21 68
    0x8800310340342000203000601b85042500d40b082c1c2041c1080e041c40f607030740c00035490b42c2c0c05000b440580d070340d804180c1d5500104103240160011100b11090680c4404029507203040d0030000d00d01041c140000407502c01d1000c0040360091001421382c05101d4104a81a603007c0002031500085110074414a0f00d0b081180c81818000c1114081500b00700d0301f1070a041c640402c00800071600400e83e0705041000700c0c0900200ea11200907494044410f803140c0031000000c1c811036840b041001e0521051100c044000300b910030007203000d065601c410a503585212130b111000325038081c0001d0384107000600420154052034280050302810f031150b41d001e0aa000180c20030a0b61024000707050000003041500c11445018058168591701444916001c0300081040c070a90200624800b20750322174003400075054006c055055000019601300aa44610341c0c101800060b038481c1c03148030742c1c80340d0300c2207410007582c0183c881c3c3c400b40400409580703400c607869455214811402962070000c8010401c0d10403103196502 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 292002724 1250 292001474 292001497
    0x30f170d06060206150f010c0813060509010f0e060f0307030b04062d080c0d020607050f0309040b0f01080a15080703050d0905031605090c0d050a0c020105070f08011208070206 77
    0x10326900742032000b0b180104c01440d01c134018410701081011562085000080d070182440c00306400c0c141d524041626004242c54030550b541507240201c0d4081e0440003030046017400f030343c0360745594081290480c0c489412200a0f60043d90401003007031b140542600a42e07000219040c003054440c81038012400312441031740901401d405e4031146000364412001180c0c002e80c1c0c0c1c12149080941040c806c07a445520840126100b801030306521402c5450b104143c0c0c15043d001403d480302035110560740350f229400b2600c0c5a01c01c41c0b6011100e40e10f440c0c08001072180c4a8103030341e85101656003103070b03540080c105000030398488245124000f0396038604000500166200e103024014101c00304a0160078a110340c1c00040c400d822619180315040702c20306c51482100c0341202e076030b060740d11800101e001a00c41c1c1400402e00d20b040c1010450240016009510300b000a54020020b039641c02134102c61625804080b8400a410b8a004001d00450444e215010b240201e021038a01210b96000a440794011101c10a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 292003974 1250 292002724 292002731
    0x901200105100609052b140607020c010306031a0403030213080c040501090b030a1203020405040c021e010e100f020f0313060c020105040b0a1a0a060c1119030f170d 72
    0x8142c25003658500080c04070342045842c0303e06100009504240340b03405200c00d615200c078104003100d5081340703540c8190b80003010a5038814050000540f80d15049038030502611034950010303d294824403a170400c40307421201c007055114000318041e2201303001a00603000c054080c0401440c0e8042d00307500e4801400810014058111200240401e80b401640b040c5500d03454440f128034540c0380070418040e60356000c2848261410702e030100390000d00a42e04401d40043c03909101808140e000145a115810404c85203101c0b10681c48145082e0740d90821503030100c2c1c000807500d12581d29980c00507226010a100d0240c10145108041003c0d81c004488050111080245034002c0c0909841801d11189982c4020f00c80b600e01901d84a401040c05808140000e9a030001e001440c5071208608010350002440081d103182d8031030004103120400c10087e43c500151400c03d0803d40750650070b006140ca4100400a01c291550b20754514090711f020081d13444440014140c00d020180e48010070020308843d0000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 292005224 1250 292003974 292003981
    0x100e0106021f020c0c01050304080706020a0e09060406060f050c0304090f0b1206010b03011404090215130e01054006090e03090a05060306010e0607051c05030705030a020901200105 79
    0x89100b000c1000140d269180704002d03c0f840401d010500300d107001c40a081091703072511603241c5505107203d6003c01500c06072022034150ba42d560303c0143c0d0b491540c0d04552010168403003038100070840b140c41c4600c901090340c405203240d40b41d01580140090250345000c0d40c0c01d040e0b640c46c8500544031161001482950354201d940d2141c6000c00242612605d5000248440c2d070524461621714441030181e6503101700030030140503440e0340755003000303846a40c040c008030402d510f000401505070300b04c040c00514429644602141901181030318a0480340010015000c10108120310203075500700300028103810310545440100d0b40d4022105c00030b0503805450000d401c0b403900c603001d01150b2000c0d048a505400c108500c0c02d10341e0b980d240c0c10b020b540089420b2035a90716581d0059407007070303d106011034000fa400309007042804004201c0705490100e84402c1e9800c01c04d211004c0304c0600c421240c07100421801d01c040390b8a44803e9001c4d26a810041c100344074608600349a04a207020015404c804581d100d5080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 292006474 1250 292005224 292005253
    0x606030b100b0406080604060803130302040515031509070e3306090f040b130902030706020c090c3a060b03100509040f0804031a0c070b010509100e010602 68
    0x3240d10004240da0080d40506218400541d446148614001c03c124035020400f40d030341321b5002e100142080c2c411070769600300c88c1036403a051102a22099124a161100081e81c6400080701700c140b06100401820a0840b0108180030030f002c05071148800d0320071020007007445068018000c0c0966003540758812803201020740c001c0d1482c450010045201021961320100b41c50300c0e1b082c0d40c0c1112044982c1400e981c0301c00082001000020030b02c0741c0c8000031300f541405904282d1b0101600d03500a40680b80340e6502c13081c05a0f51006040090368001000100251046005501804034025405400d066110102c0c0c0c02e140c44102da908201501045011406145080b6100303032402001c0d002086429031a012409107400e4070684940d030301480c0d00c90001001c100c407502c1c40014080d0301103106502e1359103e003094841000b543e20810000407481000caa20981010281c54403030350312101c000036a85c02d000038440ca90070060030003195901c0128001c42e07001c028104090290420340d00600e58240030292 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 292007724 1250 292006474 292006493
    0x3020306040503030f070e0f0607020d060c0c061109030705090405010605060a050306010e040606120f060504060b070b070203070804031122051b03012402120f0307030c051314060904020403060603 86
    0x4440244942105004048d4850008142084400703c0f0840d45503001070000c190310300600d82000300020b01c1c0441d1510320640203600894a940115030400402c03c8028000d1000d10071189034550690140c18200100e10b0441c80c000c3c0c2c40783c0314034004903131181c0c0c42000c00c01c1c9410105880d0040f80c000f10410075107581c400645007030440112002c3c0802c0d49890006001130410620300e081e010780b1461f0124070b41c2c400e0381150008000281003004100d543e0022110240c02c010811a03000081b82d021910f554400810f4501c41134104c00703924a030a10310380c2c0e2049480102941e103a00005041d00c1ea03009079a4681e00180801c41d01100401e0ba860641800c03400c1c05040601d00000280a100501240707400340d040604d842120300040440850822040c0e1038980030310b8014460042c0019003030401c0590f00d000c0c60142030191414401d1035100f140a851078010388004001c0d4a9540500300807075903609020781501c13030000d02030360300d4056043c0c04034003070740e210f6001540e080c2e45543c0104200003c80c1d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 292008974 1250 292007724 292007731
    0x9020306120a030804020603070903140307050f0601151b1e0203010c020a0f060c0309080a090e0601030b010c020f06090a03082508070b04170403050f0709020c120d0603020306040503030f 82
    0x1809045800c181c1d54001e49013080c0944080e003d00c401000068406004444600c061038000c000f04c292814500c2c0384507a60303807013920111a40d00038100c00405251000a0b0075059071403202c2100440800454100c0e8001030000802c5090f620700c00000001c00e120812507550110103c0e0386e840c00e039249006142c2540c002c010741354219030020000e2800300d0303a43c843d1204141e60100020483e4040c80d00c044010b000c004070003400307070040020481c95003600401c0e5082142d405800340b100ca075442c400103400301c810511005010560110140005250401150212900041210303003409100004500700110b01c0d04110780704140002d08844d01e608000d0304841e43c00340c020034824103c00998811401e8010014010f06020719a4041003c0201480d1900c0d0160800480580c84940e241861a03850181c0050300545014407400495002d07894000c4990005004000b400c3e10042c0b15440c1003140e01c41644112120354034240031005942c03d118481c001c5005000554407410801c80d103010380c00014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 292010224 1250 292008974 292009009
    0x40201021605060409050406061502150702060106080412140a110712111e030111040302090f0c0a0e041b03090308180604060203070309050d030e12040f0b03071809020306 75
    0x100030402141ea243c608036010342c0d0700d8090129854459207000703006410140c00101107106199511700c4503a030300095031400041c0e540c9000e40740d51100f450581e00c0f00000e001c1c0c1b4000880c0080080d02141000c40702418840c0f40340341000c0540c3d0303054501041c0d07800141451000680c002c145603184282040301d10b020309000002e40203031b80d105549550300407104c80c0019018001e4001c0e800120b41100031681d111450140082c001207442e040a0b540903401400120310502c09200800e01c484d01880d0001c7c0f2903441c000f20540340508402c0207481c40000c21314402da201d503d034240d0401e142a5551150b082403241e4401007210f40342490040c00340e00005001000c520f055808502e500180042c202d90001e0f042140180d880d04c1d650780c210041c040c2c00101a0062140780807062185616074410600c010101c070644010450311800d050343c0f0303c56031150442040108805100800b40030340219000400c504007408406004842c49841c0f04a40d400f4051540d4007008101c07903410044214280ca0620 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 292011474 1250 292010224 292010263
    0x102040e010521070902090a0603090b0406021b120a200d030c12051003020901090b0303031b041806061b030c1212020d0501080d0306080703030807050f030c0304020102 74
    0xe09480c214142414850544240841c080c041c3d601c0203180c0c0c107000f000c0c10080030ba4107402d48648004d0007075817009500e00c2c0500350440000825522a01ca281200c550004d4041c8003074450ba00c41e1341c041e4126101804840d151075818041c101c02c10030940002103101c3c0071142d19800601c1e00544503030300c1d21000c1070400d50410494000c6030004900c0702c01106803420300140c040c5030800c0c11103100741340f0000e07030320480d20305010b02203c0081075024108032442142e002c20540e0700d5040f480e0a5420405c04035401d544244081036092068018202c140000030404500b0160703103841940001c21215001c81d1038540c0e4071018403402e40c0c054100000748160183c44400c4402c07643d8024030780010010301034025101d034220720442510802c02080c0810105009545030440d0200c0180244800e10520343e651246203010b901c0c1c24000d008000032034045002610886195882c15101c100b00100881d0400c1001c1280325100c0340303580081d502400392004d02c6c680303e1805200282c90101c041c84e8404c1c01081d07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 292012724 1250 292011474 292011479
    0x2040b090c1c020f0a05092809021b0a0c1d1605030604111c1a030706050d020f0a08010501020c01031a0103090510050a05060a0f03050a020607020d0f0311010c02010204 74
    0xc282110b0090601c62625141102400c1c0d440009010340344244686040c0041c4101e04a075200c40070307000603a003c540c80d1401d50503412289007111980602070a21081c81d40c02040b00e41d403503501514400744110042207414000321541e5040000c41c2104031103403000035070244080a0180c0e80341640d005407403451901801c0a030784001d14010700406550800c41c00000044803910703141c00c0001c2c0808141c9845845038820340890201d1080244440505450040e0191307011600148801c031001c006000b4058031410001c00f05d8190b40244800c83c8201e40811101031003001980c018004403100d5035641180f035041200081c1002412000c2c1810903003401c2205850b507010707a880d215001c000742030000e0100428901380307052400ca01400c05542d031402040040034003468101e00c1c0f045100729010108551508580ca918299601000d407040c0c0c4107007000001410204020711500e0700080610078074004540e900500e41d11010001c500140c48548010b9550f4000d0080300f11042c090300003581841d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 292013974 1250 292012724 292012741
    0x305040b0f071b0203010b090405061905060d02040905160b09040f0209010818190b0105091b0304080d110a030c03050705041a090612100302010e01090303023c01050402040b09 77
    0x40540f07031407180c00c80d00000d20108664003540520b022400240c41c0304014038041c1005c2c0e8403460201d659902680300d106a1000100c020300c03d46100c0d101c003c0c041020105c680e02404003c1180d6003040381d00b031064603055490810b01031029001441c034568080da0f1400b9003824002070301c40300e808540400740140842ca10580e00160815880305802c08281c1e02c903060320070751340d00c0d04444101304620781c1c204000c46014030400481c032505171442070307840f01e83c075440f5211222140b0006822461202c0c0c001e101080000303044070024004022500804541e4444801c2c0003455503000c01c40400c0030030707620b401c010001038050080c0d03a071103103150074420309152510f420009803400d0048441d5210100281001d05903a41d070099441a5408401c0314107a1b00e010f45660406005034042a0b011070303071500700d03c800756110b01c0c0c058090700d0741603015041c080d046006a0b4100c44111000d1a03000c074401030400c804850340e803c5545c07003d028100120741424240180001c807030301c40b26180c0c0180c0e0b60004001d542c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 292015224 1250 292013974 292013987
    0x3090406211b05063c0417070f0602030703020610050a030807080c37150c140a0f030e0d02120a2303011509050a12050a02100305040b0f07 61
    0x358000d000c1407044200c00551410202e41c03500502d5000001080d6092002c0c21720101c0f80319200540707480a90303481c04003140901351824031621405a42d04201c2488415176010310810180501803c580d002d640b9000409505616500800016400411315105141d4100403141e0081c42d031440e00c000050900c80490070001071808081c00d030701c0d0001444000c0000030021a08000241000e0f034090080710380004064240303403114a5000c02c84a81004000c0444056001801e075010408a2850446410714000b603c01c0c0300c0c1040070b211a0b50180f5041140110080000e640e195981205c5031400b208082d01310b0f040503000505a0303110301e0700090059000201c1c4000c210f01d068103503849045d030301d1046948100710001d0500d01c0410303c4451540500c801d0103141a19011700e561070030520115003c40300440580f0941e588410201e07000c21100b110305102d032811600410607254000e0464009c5a12403c1750401c0c000081d58460411040c0045042c0c0c20b600118804001d04003403d140c50003c000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 292016474 1250 292015224 292015289
    0x3020a05040e0309040e06010501140f0d09020d0501090c080d0c1101080c04030c08010903110303310602120129030406050c04030b04120206070e03061803160503090406 74
    0x307280c0d1894a120000420015104040030041052050806c155802601c4500c02e10580740402c58410319141054080c5055510350540009000e0905141100c443c000e4403c0110aa03088440e681c040c80c080780b020301940c110700d40124180000c80b49040c00a070b180c08140541841003084a800c0d400000c0e04070482400c0b80c88092800c1c03041901d59403680140d901c5250710080c000a103085000030400019004164114000d40310840e50400700444982c483c401115100e40e14000340720300070202d0350042c60030610002101e40c2100100410340e6a601264404201202c40c001c2c100010000c9200314516084000d0700022480d43c078040c03501d941c0c25140400b50008118070740310000520bc0c140010107540082d0380001021607a0305042c1043c03405042c042c1035010060143d072002a440300e01419aa262011024008104540c4d070501502d00c0b01c2001481091140000c10080003025200c01c0c080c044c01c0e0081c0c0c003071a0340720360510030002100e0165000d400c000d08001d19918802c0b1810507000c25 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 292017724 1250 292016474 292016479
    0x2060103060f02040512010614011d0108070509040c0e0a1a04060f0c15020d0f0501050a0e06060c0609100509060601050d1e060b0408060105060408030f1803060708090d0903020a05 79
    0x102c1e00403181070784019024030780089411040c2440c50b0415040c05412480031a40d039928507554820080c001102d5a1002d850264543c08160304644100e5105519040e4070004d2490706a0400e08241e0000d0140c480b540d807001700040348522518201c0c54540000c038010034601d001e00207107841d00303240800180110f118070000c0c0138440d20310405a03030042c54503683d03255001941d04046110102007034000d40041c59012602413422078280c9104005205030790503604001d0040244a20700798003a8261140201250741102041c070860b41d0124003040014000c00050014002c14030382055410300b1250001d08240c035580c400424881c060740c0100803220324070085c10000c140040b00c95850040c0440103074480e400c40f40303006000154484003c019005032650034054a581d640d83e1805c120343da01880c0074001080c0c1041002c5c800c48051003005000c00103120f41c81103034810032100042d090000403501031010501e0b070f00401045c2c180500c0b0f0b00c0085039450038102d90160554012038001c00d01800350300d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 292018974 1250 292017724 292017731
    0x6090e040b1303020709060f080115030818060d060f230109030b1806090303060301060803030f31150b010309210201180f05070b03071202030a06030203060f011a04060206010306 78
    0x105141c424803500024010041b0140134207661000200e404101d03511810344c0d15441d0a4010082c3c0906881041c212178010300c1e014101011982889514141d010145a01401c100903041c02c0d40a94015070340181a4000b04000151501d80c0d03100f6003000e00715103607540480e51485540d640e85c010301c00c20700703a81e0002441d82840d6141c0b95206ca40c50820703881607070244601c004000b144000000214403c040917130080c046c550395611519581e00003619040640f4030710300300140e0880b00181e030301030400780503402c0c1c40d20503980300f0340918210388d4094056806030000d00560a841456004807694400280f0302009261215150f07060100c01d0040c440b910318464081d000c2d00140300f50441800000c0039200c2d8005010b40345450b600b400c7d034030541107035540a18480003a180c201f030001d40784140015101c403e038602d041c0c45180c00070b44c0010b04882480e584c9034808000f6031020010300c0e2180c17078640640745480d414050345048041061040f50a2501c0c200003c0c01031a602180f09811254020700c0030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 292020224 1250 292018974 292019011
    0x20304020f040f09050c060a020c0607020105120a06030303060506030601050d1d0f0604060609020a020a060e100501060507060b060307050702191d10050102071d0a0603061506090e040b 81
    0x1081c080110030601e901508150000410040c40d80c0300c0c00445100d80c00300d501c1103160350240b00d07060140f000603401503081425214801c1c1080c6e0001d104140c8145040d501d09208818068504e00b41680c0c001c1d1510b0741d0781c4051040541620a0a01a040485074281103103040780001b486407298240f043c2180c1c2d00d41c250301279814a4901592948480c860684032181c1100302303510782ea143c0c01c580558015082040000b04035496100320b8a5424040d405030200b102079442d03900180080b42c0c41d4200038440c01c1c14240c1915140c0c841c0901820300f03990b98940d180020306000d816100c42c41c4040380300e14400c00074003051681007001c0760b610070750540d520440c014005003040148541c5502650b20f14101000681c207905451540521540101c1c00180034980c840e40120395501060080f403040109001c009110b02104100f050b50240c88044045005902c036079410b02075680b4201075003840340c07081c1c00500851307411401c1180030b05020b101100d442e182a48648009080c090081e500b01580b02081 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 292021474 1250 292020224 292020229
    0x21005010f0b03071d04020309010207030806060403030912030c120818010b031e0715020c01092301030509010f09030f020c030610120c0e0910140402180a02300c040f03030302030402 80
    0x801d0171040184115202d2500d200035601039441030300100c0010300c2c80400645c181c60a601503e0a4980590b190008a070500511140018280e88160140700c2c03a9036a0000042c02580001d0540b103490b03681c200c0394203205c21440c05901ca113030322444141c0d041581d400b0490320002100901516003130050f88900303500800300c0e400d21100c1e1b0032490300c0181c8088102d00c0140c00080040902000381d0b1404e480a684040010000194846181020114500007500782d0b10940020742c01c12a56000040c44091031904241100e50201040740031590180110000e82e40603c5075a515110030307800741000d1319042202c074500c283c150281c4507130304c0c00401c0018280600d640030312002c0c0c9a0706c0102005400e221003419511098441007800c81303400d000580f054020040c00850180e0b9006d0009040b1584122026241d800010480309038150300b888034440b00c04500d01c0025181c0010b035030504940c05800a920000079000340910004072080100b003100380d400b0340885007140d4040c540161a519140700 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 292022724 1250 292021474 292021517
    0x21905210103060b0a1502070e060a050904152319110301030b01050405070f0219061b050d0e0c150708040b0309030307020751021005010f0b0307 64
    0x9480e200020514004020040d10b90b00c940040001200e214642558810803082c40d200c55010200050300990800c003c41c4035824182604002d005002807070098030b480c0819001c00d81294281d44a50a844008103800b82a1066080c00550071143d44801d04007100842c6000d44003030110165514416200d0000c0c00031680145002c10040e0f803940d5503075075a41444000301401b801094402c5282c4004203210300c0c02078050321a04451074002e04080f5617404107100e0001c110320001d985a43c1c4400b406401e07000520001e28454070715490701612079003001c2003d4200c484040c2c1020075503112405000342c50741c40c0440c04e22070040409245030380365424030b051080c03400303660f02c03a5811082c08010b0041c02d41000c0050740c4141c100e5030841d28120350714224038107418040f40c4048086132980012210321034152400100d409000c888820120b010314004c01c84c104905041c0c0d030300582058014250310111030084034010400ca003640f01d07200d42062845105880090180b20034400340740032407803d590705540b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 292023974 1250 292022724 292022767
    0x10e030a0b0106090807140f040203040c18020d15351e011a13090302011107050c100503040b0f060d0c03030f17090703030e210a0b0a021905 62
    0x120118a560764400241a0a850317006003441c1740110900491070302c0d003600e024031007101b006244580c4c50070400284002503002a2050341c0e80807c9840105184080c080d1008424913501c00050783c6582c400c407060304558012000030010361482008106002c3d6000b03503611000c051129605404502d04103401a41c411801c10445038050600701030514040100a407070482034440c020301100e0039a80004004000c0550155806000031f9000641c0004039441002c40c0c0e40300b0300000a5088000c440d0300c03102c8d0002241213456034010010501b080c1461440c2c0c0081d003c45091450541c2450303921603444900c010040503850001c000020490360303030416050440c980000030b0f4401c0700c1d10b03400e004240710059011140890614810300340c0c01c0d58034980032480340c1c0420300901405800c2d558102d03040307030540d00116070190040c0c2c8480501303500c00e11000c0071000000300421402003a4540102000d4005000d9001c0d28810700001400407094014030454843c94905141c0e104100ca02e01000c035007145 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 292025224 1250 292023974 292023983
    0x1020723190f060f0b09071d0402040b07110102060c0313020f0907021506012604030c08120603060a09080909060307080a0302010b0301050907080a0b10151205090607020c010e030a 79
    0x8002418401403400800145000d21014400d003100300d501001690b020b24151740c0c11034200c10010752901e100c0e0030301c04200c9584452071039800342850001801c0ea042600b000a01483c0062604200b201c0d00ea0422100c4400f800644041e2521151400c0d83d40030041c4030854000e60a50003030119070f10880068554a0b004003201003a044c40140295120381c0400d004811070f1080000c90b15644c0543c03c0c4500718800d442900e605540151203094081d103000d441101800074002a00e0006508000a0224485164000c6646150042c1010b241070000341c0320444051404070b511010548480442d12411410340312040d60f0b8a600700440d00c9e02d404d0341e0004056020380d105030020160706403c14603140c03004800900180d00c07051a1561605020310441c41c0a510071018000054940340107950302036044042001d10542d1299241e9a01d400000703007400040002009966001092080c01c2e00041c00c8401881503203401d0201a683da06800e00e0141400403500042c865564100210210103500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 292026474 1250 292025224 292025263
    0xc090d0803041104050702120901140c0105010308070b070c03140702030a02041802240a0f02190305190c1e0203010e01181a04050304050f0409021005180301020723 72
    0x30f07042076000c072080301c000244541d0070300340860f00c13940c80001e03001841c616011000b446c1c8402c0c4401940e40b800d8600c000001c001c03080c007880380b5005c002e101d0b0314002d60003115480d41c0d840c410311380a000340c00018181001d1050018510010a80c4040c402d0b00b41401c000c85640c0e03d00c40713400064601011840300940c01403c2c10040305e2075842c00711078210003e00c250b40e00d00d00b0980400f041074000c4114030820741d02c07403000d00400010034450410000b180c041070050301e0030740c4508a90052a6a50124141c0104078005142e90740480c008200c0c858103103051401c004903c070b240d56600b41d50001040c2c0300c3c2820450b00b1014055541c02e503c403040802030b440080001c000c1e60741c030030081410501000d80f8652035102d640b403002003036101e0003407250fa48807000d540303024106000c100146500010650708990340340c030f4840c0142c075004d01018801c43c0c00c0d180d040d280e11114810203003510301400c040e4003e07401400480005960039215800280c00b050401100222100300700740b40107940411200f15514 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 292027724 1250 292026474 292026481
    0x90903021c21110304020f1c030915020109020f060307260708071b0f14060f01080c0406050603010e13020a0902040501080f151009150e100201090b0c090d0803 70
    0x10031080d0a0450405200c41c00d00100c00940342d68200d80360300c008018140d1041000900600d800402e200658000070081c2c100c0802c010102460440c403850124003043d00f0a1092000300c0b00308a01d901020f029100030311540703c0d25404568200044400c5602411b004070202d42180c0c0644c202065440050410b20240c2000ca0310b0b00c4001e540682d0100085400c500114044512480b0300070602309205a085a40c8030140d9114841201c8014050f9610440d0206a800e44c007803c1c03040a003d4401c50500c00069410541302d01d017841c6240210a10035443c1003010440340d10f0b21003d60741120310f4410340750240d03582c4c0342e25610070300d0188034000c0d80000201c1010031056640e5005c0e100740c42080c1e1340c0c0380c410381d101e55600304000400e5480d4000d80f9240c00b41404d003864180302c0250a0000d0786080c48105940388100d0803202d0700a420300340807545c030044803c403c1c20000442c9504000d80d100a00030f580e1300d0f460f0303601c502c5800343c044241e040340014007514071703228414094011944665050399a00e0b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 292028974 1250 292027724 292027727
    0xc030204150513080105280f14070305010602030408150a0b04111c020403020a090b0d02060301081e011a10020102041d041406040203121c06030305130605030f01090903021c 76
    0x1403007956a012003c00209000c1020801440390920848104044882c02c41c08181c9425003240340d052890a440d0716440e0030091161280070b02e66511001460214560810440203001c0d580160020003c650041c08100034541c0000380e04050700300e40310b101d80c00949441c100c00c00a811011346c8150442d041103080c0295032010750007000d42c05461140c00b212644c6400e94070003a0b00c900e2101a41c41010404144450341040d480320081000080801180c0080c07a4082241c5070026445800290042c00326056124a80c40204040100c2400208000540b04040d4480344044030441e03030040010080d500070075030003541268090b041c0316540e544050583c0c0043e80c100481110304079400780161380c03424111180082c8a80c0600d5008014258603550802011041d4000d03021410a09000c1e09a07115a40c4091040341e0186000790782d1142d0358600c10032140314000980c0c0c06082088010010489007140401405040d03030f4010030042600f41e001e0808030b2519580b0740d01000c4445000b0903014465 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 292030224 1250 292028974 292028977
    0x60c0a0f0c0e090109080406030f0902090a050601030606050702090106081012061506031404112115070914010c03111006210c03080d060812090103060e0405100c0302041505 76
    0xc9030320755500e141c15520141e03114245d0307001c1a401002e110042c003040c40ba131030003600b00b040c201d4090b86000860712003a07000540c0c2d0250941c2d1802509540e40e080c007286503850702401c4040c1a450900d2403900c40940e01080c0e2900d0f0501c105d5081001c128003082018403503100200080198000e2078040c0d0040b410104010701080c0c550b14012100c6190008982d800ba020302a000d030640d180860f1141e039540c80b15499810301080a90384117007440740800388410758411100d404c5d9000300080500c3d684803004d010700c1c0500a0241414011141810002c104405c188051a000280f809040c225124502a50180da140c0c034011054040e031018460500ea0980c8000200c542c000c10020016964140004120707000e41009030603644001018008110418014179429005001c001100c075666401d40381801030b007600100c140724001600410741c2da41400f492000d042008110003940c1030565505d0b565920301c07800302e500e598071905248071240c080e03810780d4000d02c454100000800001034005089 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 292031474 1250 292030224 292030229
    0xf170c0d02070f05060706050c0903100608010b0607050a0f0503070213140a0c090905090705030a05031e03060d14010b150706050109050f04030507080c010f1b031a060c0a0f0c 77
    0x1440340c0ba0001540c1908680c20078110740c0040c00d11403600e040b94403510003030503001700740c01ca508504205d0841103032000c1020700e150886040c40054480d050089480c00d554114031114410103083c421607001c1240480d816102a602450000483c42070b803802c1411170244100c007035445681851004007c29880d00112606401c10500900b07998403007942000310348440784940009007a20303506022000380c0c3d5004680000c4a18100c40d5000d81c1c0f140001d2030440341c4117049449070404a4061290402611501007481c0c80e0b107851411840e014011620b6480038610240864a000703180f90380c0c00b80290321503803452102500ea000002a580c050083c1a840101c0c211134030352600700009000080c61003442d0041824001104040c1ca40351011184c44e0001b0300b0036552084200701c50034440d0310903c503c00070071604e1000032a00b0101000c0c00e00f030444501c51a0b80030700d42800e1451500c002b0809000801100403101d0903211405c0d1041c6614103040d10070300800401202101e4000d110a00b10035004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 292032724 1250 292031474 292031477
    0x218310b0f100e060f25030e0f0a080d020102090a0b09061e07050607021b01020102030919080d0510031a2e090608010e0706020706021c110313050405060f09040f170c0d 74
    0x440548000386101007100b030f450150000301b00c07404010231454035000c006400003000703180140035600d500405042007960502100581c1d40040d001c89907061a103441f800400442080078101450000418540d10503400c05100b00540c082c04010075a184105445030f8036000822106075140220001c0d65401e04c5c4c0706c841d800d03941100100c40c0c1c03d43c814003c4a224580729000f074040540002582c1810007500801114008820b000d200c00758001489218072561104004215980c5103051002d0020700c10002c4070321000d03c00081240080314061020703203140522904040d8602c040c03c60160046294001001cfc44e0300304a0000f41d40c000541150101080e175405880003c0d0755200181daa41d5501d102d800701581015401810104841d40751010403480c0d4101041c412084641150030b6a000c0c0051040004840005110a040a00c55075a11000c26950710015600184c00942c103280014030043c19020030746210000c00c100403100d800000381d58421145c44241c8001d2144c1c441d02e82592040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 292033974 1250 292032724 292032757
    0x1306090f030201150b16032d0e06040b1804060902070f0b010510090303030b19030b0f0901050709090e0a050304061706041e0218310b0f100e060f 64
    0xf00030303081d0504950803115140b011625180c00d440c100041600d0301c0405a0500c4664000740b00140e0085038649243c0d00b40482401c40d9511008c40507140114080300a4025a814001881140c0819048804803c83c13a804440da211001c40040d028010a4200b50681800803418004010001c03003501041c43c812103c600e880d030789403001d1200741004546144001080c207401000803a000398000c044400380904003925140701114034100e02d0f0342c03940c01240c51b140441d0400c4004541d400c41103800c5101d80000380000d0900102c0146018032500403044103542c1d41c08240c0390240d040000a0301c05e83e00c1400d0704d4480c2da944d040a0244d000d1007003400400c406031030020b1614501489041100c800151403101f5400790018170340001d401107070b240e8a804840e829030b80c005d036640e0b60b807898071070068041200007000d00b0b103000550713101c05145d51242c4a05080000301b0554810440000c0410b0030313107003000c0c8111a400200e8010a200d01c42035040800028045d0381c1650700300c001c01c0002480c10741d20 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 292035224 1250 292033974 292033991
    0x80601080309030d05070827040b09161412010e06120d1b081e0a020106060201050603030a0503100b04080a02010f0f1d24030103051917031306090f030201 68
    0x300c0e01c038468a0756040d850703000b44004034100c5000d8400791007124003490a55042000d0380d045400751001503000c3c8001000741c8501c0b8040c1e49420701455030301a000762203102182c181901c07450904c510b0400c0c0b05040c854110088136103440c4110549090744c1ccc1208458440e942d45001340e441e07407581502c1c2240a41c1c610001801c80810000345180c00700090340d0b40c0c56099066070080c2036072541d01001140d05440410002c00d83c0341ca5455004001c0207002e050a580760f9003000c1c080e0031a4440d0340154250b90400e020024156030110544400320782600300140c1d44c0c0e590401031030b8800c2d03041d08075003a1700c080810702181c008800036134008054400c1c0c90711420180454419180e040d01451540000f800310348030304a0868412021000d030007800707000392921000e00c1802c901144403120400000394804001003050000800c9513924035284103512122001080e124422110414134211303510340000004030302460044204503100a4000034100002c926515008840b011503c00540056082070b005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 292036474 1250 292035224 292035239
    0x6240503010b0919082406040605090408070f0b04030207080d170a090507050409030804110a0b1b1509010504030e0609030c220204080d03050a15031e0219080601 71
    0x840e03058580b0b0008560038005003008021030000300c0b0709a403554510040000555840800110110500945500c640007070a41c0141d000c44000800d401e10442c1400300801103900c42c03d4000781c0150b0003500156640360756003440445d19540c102c0050107243c4100410050580c0800c0c9081a00d91040c10380e03a0450b1600c400b1160a40d480c400c456031910b456001c1041e204055200d085280d12441c10364042e0390ba00d100040880710f8580e42a404110144204010003134500f91000e15030300c08851070a0120706041c1c6008aa018408211324001c076060b984e03034070b5828208500e1340410704045500341c0c546485000d00703028180c161411000300700010f0161a81e0700d0500c0644441100c00307001800d150048104114200903210304083c002034a2100c515030301003850008202405551005080600c0c1c5084003e0845000071310345c5001c01d160040d07204201e40401121011240c005140c000c0038442150b0403030340c541486500a5100c8480304284405aa20310314000480b0740308029110307241e0740c070b281 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 292037724 1250 292036474 292036477
    0x80c0403020f21010e010905070801060305030405120a0b040f211421040c030312020738090c030d0c02062b020d060306050703020c070324062405 64
    0x30007540708402c000c0d11106070501505505155115881a9211840c0c050b0282c3c21502c0d21203044c0c82c0d6035125a9034100380542000600c0041c46103000822070146503895141e164000c901407544a0041c0b0605407000c0d25080200c0e4600b150049c000a01314180792030404848042014203c4010502100c01314460048070310f1018260035903126a0004440050102c00c203600c20502c82d03040382012050311118810840c51148102e102e0381d210644282107081c0030300824502c101810706035004008030307000191003000380b04041d0610400121410407070602118916280c1c1200c01c0c803854600108030180a0001e09440c01003810350541d0300d06c8242c3c9030121806120f400d80a9044170041250700000d4225620280055000d582000b030f981380d04541c41c00236640040040d01c60580c0328081481444103d201d01500804141811454000c6d50300300107854640c03e10019045000008031201d0040303c1e4040703038064650304541042500c5c1c80e01c10001e0b4000c00520280d401031b50b0240c0300d412440c040e00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 292038974 1250 292037724 292037729
    0x6040507020a110d050f07060305100f12080c190605070f02030f13080d080108071202030d0807050f0706060e0a0b031902360903040f05040b0d050604030f080c04 71
    0x1030203004200543c0d02c400f00200150030a960300f02201e0383c1c2581c041801441110410720407000070f484000d20300030000b016a2409804010354040d485010044205041d174090215007424445005100082c200f035501d50086400968407806540058107401000410b00c0c4119441b44808000c0c5d501d0707403e0219003c1c405403010300c000d070b40100300c0e0558414000c0003414aa100b01c0709002c81441d25000103504082032803c504010554a0005005030315041c8100e4000d40301c00d1090b04242109074001a07950300001d4460b10070310403504040b1340342610403000c849104035500b241560f20078442c9084402005c2c1803142c41e00c0c00100401040114a8600440382c02d52001401016005050884044001e505c520101c5e40502c1c0d481b100450307141001c0c041e003010382d002c964024040034440000103150303034001e25401c01a041003005101c01c00804a0aa003036540554001a020542ca00800c04c500c07074542c009071507849614100820143d01101e0721400710b019955908450300d4208090505001d5030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 292040224 1250 292038974 292038977
    0x70804080a05210d15030501020a050c0f0d090b0307021e160504061d0a0605040c03050421020601060318080f04030201020d110c060919090b120304080c010309020a0b0d060e06040507 80
    0x1000070100b0304004e41c0240a03184c4400180c5120b140d034a968090072680500880f1003c40c6020840449030304c0f007800503d0702007400c48068188810f4820307000300090b6050090f803401035404030200c0c007410320070040d80c90188800c8417460300601c0041500d80c2d95039209a0202590000311601103840c2c14203016900c1180c0144031034141c00060041c0904204100a02e024660384e0f9600d0001100c2e41c41d401036200300f113482e0b1800141c0c0e00b01400c10103100e103140500c00c0b101d0700b00c03540e9402c0c402e540014800d04448103454001200d0820148141004049a90207045a00c0101d0101081d40c0c0341c10091085a10076000c54884d041c40000c182e8003d040310040104079082648104c805083c0320300285040d1800500b18228803201d507202401c0c401960700f2010041e5607514404035141081c0d0402c15440782410011409c061030207925a6485880311034440c100368403071501d2411500c400c00c807075026103a100c44032030715400c0348a42c0000812244c407640441e8030341d16001c941c0307906140c8203180c0211860b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 292041474 1250 292040224 292040227
    0xe1905030c07240309020105160602070b0f070f081b0d02030a051b04030303152601050601030b06030a110909040b070905011b1b090608010504050f06062202070804080a0521 76
    0x90fa100350000c000c60041603041c000c0400211000760074410540302010303c80d460058070341c0d140342010311094a00510080911001c41c0501a40300d0304001c404400d0f5405142c040401c0d944c0c0310814114039180654003c2001003c9280a4401415009140b280150354410042aa1707002c1c641095940400600c06030070404000a00110b4403e800007400d042c03916252040c459900c2c2d004050720908445034043c2c4004058620214810a019054000e1400d00e03051044000c943c0014107280b10203400d60501d10f5030b41ca0b481c00090746120a840046a005004906911341030406043c0c88000711940c600290700c01c0302c0070409600840c0c2e1400c50713480c0f40d07100580f00a041c0d65404100120301c2d05c2140078100c00d100c0010012424011a0017502c462000483c4070300380351601e02d1074150031070442c1c5c5a60300050100047c9895152409040c0786424600340042402450b8641c0244078444028240c00800a008154804005184810709200f48102c90000810030000308540842c0521071045580 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 292042724 1250 292041474 292041539
    0xd050703120204150c05010f0c1b170c030307030608120a08060127030b061212030a0e0d0c140a0c060309030915030902240405040e1905030c07 63
    0x45414520045040904010f2825032200810140061000c920100180155102c001004003c0c000e0b00d441d007408070030034400340340f1040c0040d1501d140310b006441c9a41c1141c09203024881c0c000c4400b5083d00315402055503600040e1955500d0741c1c004c03908400030a05040c40000d0f120740000340079504620307420b600e0f42000d00f024070460f044240a0200b80c10003203000c1c0c19505c1400c0e0b040006450301010f00b03440400503d1850403e5100d5401011319105400b00003400c4d00b005400704081c05012003d9000c15603030b58030001140000c0183c40760f08400ba21520b80e0040c1c0d0140c210340e01c3d01c14903010380584000c90160344140d40e030303d04210300000c00003c2460020407101740650400e80b000c0f84039080c0090706a845580e1603078150000940d8034000f9840e442800c0941c2410010125001c10383d0185ca06100d411080d100c80da07208601c120382c01507a6504519128504c1404062803c040440303039018040d4a60610301da0366003005404c91801c0c000c0840c0095892000c20034580e01c0b07a20745410301074401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 292043974 1250 292042724 292042727
    0x5060f07080f0601021629040b12101728020109151101020304050606041b210f0e01050114010e01170a0e0616140304021315090204030f060e0d050703 66
    0xc1d000d410107041d0b04c503103035586c04800290325506010307001010160070302030a802c4240f01e50f041c00c0802d1059555040109205408448044940c20800b05101e420140c031007011000511070158800f05501c0400c4400d40400840403500215000780360b01e0043c030082280c4800c00e58000c180600a003c19011039041101d5180900401c020030303e51304124094981031422079083e81d10454003250290130903000c004031854248920411100d80003a41858000c0b05a40a40001d0342000404c0c460a04003001240071a0282c100c50710300c00d810386050040022419802e40a4042030181c0c80c820000103215840b0755114840428101c0f2050390382d0014411410810702110b14041e0080103115107400700c000c07140b0420030045008038107101184181108200c03005120740c80c440e60b010741c1524100280300141e502c14440101d41c8028110010b850903442c6e09903c2c0c0c000c0c3d44c0e4046483e0a0001c68004180700c0390710071941645014000500c414040099400d44480d005610b03038000c142e00380034441c04203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 292045224 1250 292043974 292044001
    0x10030c05061809090f0a03030207140309030a060f090204020c0a020301050f061c020d0f051c02030301150516020301150302090f04021809070e0f09010e1b01030c030f02030a050405060f0708 83
    0x41c110b20958075444100e1105c80c0c00e0201d410030643c0442c1e0005410401c1210b0300d0006850000110007a45c100420308001980702e08959a014ac4026265800d071044003010f980a04802c0f40e004008541c0c440c40003001948030041941c01360301c207500c0e000c0028440411600b42c18400d85000701650a003040d415008440908055020383c1c1183c200c2c01c0a40005102c031070320170420350144009156048131100c0d12252417800e1040d1404642090004000700045400440d90300c0b106414080e80703030301400809202c0d041c480340300070b5411b41c00c058280c81220700d41080c2ca010742e4002d4034124001e41d00c9004c1a620040c0545000350000300850150318962109034005030004200301c242c0f00d81036950b03410981c46640680b219019009a44203100d03420a0034800c821a80ea40c490150020202c0c91115184940560340c00368141501c910410710600e102e94000e08404d000300004640724200f04201400500d0304036400c841c640708020104014074000507040e480b40c0803da0ba614030035a9100381400c1c11 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 292046474 1250 292045224 292045231
    0x3050a0f09090608070f0b0c0c0d050a0b0a0501061404030206220801050403030c0318020f0105031b03010f03050705061207030218060d0b01120b0d12050f0310030c05061809 76
    0x10020703070620100310b01e04140070350401044010700401a1504251011014444540c0421070105040001d81c0d5a80c0000c43c5a01a14108803007100c6a000d190800c6030034410300f2280149640924401c02400750a180c1c80541038405035031301d0044215503010000014400c500010394808414040690640c20901d5104083e914a00d1440c488581e034060850954409403800c801003500e4449c0c1d192801c1d45445071340e6481c0b81c40c80142c80c41072140e4012501c8140c42204d420304000d0004001814000c0c060461991000c00d0100c5994941e0b440781545000002e40c081181e46024140c0002281c4c9014416241c64a00302c111286660301e55050960080d40505580092003502c0750500300300eaa074105c0a001699070601c000b14140c200140010803020b60190540b803024071b02100040e098079034108140d03100754806407110451002ca80191918042c00258254900f0b0020401000180400c480c20450b1310a50508000d141c481c0e00b0840039000d4070f800743c0c1c481500c1040e010114a40304648940 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 292047724 1250 292046474 292046477
    0x1704060b120f0102040e0717040b0406020c0a140c09040b0a0209010e0612060a08161e080d0f030c0201060b1801090503030307050c070f05030309010c060b0307030f030201050a050403050a0f 83
    0x409a018010290801c07502d085207500c0c50f580881c1c2040a40c0e00b0520086d0b10001c9494580e161490144041003000300250020303080d41001710020b070400005504032341d0003048403000c0f83c03091101c0c2d142c06400400c40100c3c4040c00d000740b00100519042040d12240540d0703000402c1285551040c0c5080d00070341044c80c04504000c0c6201400c91140ca98400038030459a4411031091140760040500c038460442c1c1d130010142d41d100c8c07040c802092006194420607140034441502c1d0380c0304c40d408005040d0000350890b48081c020400d40d682c00c00e0b023009010280d50300548040c416028900001d0342260214452141030f0b000410140400c0c1e421180021409881410b01c0d0101648440210740703540c0048511902040e400030700d0880c189401c01c23840004100550300d50f0416814500841d0b181d00890202c00d041c8500040d40350100076094010900c0404050110b0300340554030f0510072485800820181c0143d40b1b0000810ac1300f02b0703203008042c171464040c0c49591400003003882c11a00100e140103a42e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 292048974 1250 292047724 292047739
    0xd0b090304031b050405070e01020d0e01051b03031b030702060c0a022d1005040c03110d05010f091208090d140c06101508041e020402040e090d020d1704060b 69
    0x1e0a020b1061405041183d641c80c01c141440140021504094420300501c109003114034030340d070b90015886091440c2450484050078510f80180d641d80280401c02070880f864102c0c000c525580040607521800c60030f030345650009504603240a40c0e12007550700b8801a0000f800161002101500428000074180b04440c0750109480c51340c00c110000d04003a5551400480c5c50042c183c0082048224407900764500700310604040d0743d0a000306401340310007000510007010783d40d103581c1c5500c07601d03042a420200030310a07400c1c81480000184400c0600300da14280750740548124502c24a826846460100028070380c0c511801030644c0c0c40e0400300000c84416104100404403100207110329401030310540c41d070840c41802e2041204400324025600010491106d08000100301c8103a03040007149a504c0107841503401b1030010502034070071504609040e04081e428030206480020f40c1c020440041e0742a502d5550100c001150300400007a62548103419280108020032031a5104007034590b00104080d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 292050224 1250 292048974 292048979
    0x405120708160b04020a1508060f010201020c1f0f0506010f030b0613080a15020f0307110703060914060a2d0b1210050105010806011b0302070308030114030f0109020d0b090304 77
    0x30400b050b07099800c58040119409210840c10800c0c280406000380480058510008500050400710002c14652182c14064468003183e4000c9d4100d03030750000c42005491400c0c41a035440c116075000c010080041c24600385005240c41514440c95000301e0051b5150b800b0b4036442d800c102c003c3c206078a01b180c2d100343e04000a27000d803d072400812000f4108400079010072003903030030081c80c00054404542c004500400c4248606d04802045941c00052030919803650300000d4074940c640811608010100cd00e030900000c24000c2d90640b0401d0041c00f407088a003140c3d10449000140c842442041c81c8468810310309607400072280c04034080441d071405002680407448000078881c030101c3c0150340c2130364016403411130284010b4081c0038017500c400e013001181810070800003002e150041c0940403134841005007000030940b00348800b000442d006400c4170380700e58640c0d95032096104103820041c030a110b00c0f0311005800c9018000d0114140c0c00600d640c1d0700003919120382e454008000c124091300e00040101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 292051474 1250 292050224 292050247
    0x207060f020a0c020910080a0210024306020c011b060501120b0115020607031d0601030302160806040f2402030f0403030606022e110f0306010f05030405120708 70
    0x60040d10b0103968804001102c6070040c0320038550003510007001000098418010014002240410315905480341c2c0e0701c056584104030304189281a000c00c2e4402c02c4010105d49040c6960711100b428032485c0c41c1c8116800a203000c15680710708c0d10031140540c000c880107042960140f80e25803804003c010700b4000354074065951104984c401d13004030b46003400001e51001800466a1594094540d0140c0780e011031002e128065669480200f4280803d52605600307081016162004000c0811503002c4903001d58581ca80603480329034a03208004101542c5a00040e00e08000600502030743d0000040c0e10a00d4082d100c0c0d609d948492801104100c2256001c0ae000d980648000c520440c15400e90700310310b0070217203001404e4400b103501c51f00855025000c803440080111143e800540c0c07451110003500f45506105002401c5901c5012802850100b18104204c0e008001107100342e000740d0300c184c882c0c01e1216054402d03004c00d660142c03150b4004001c40014441714402440280d000d0143c1c2400c01400408 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 292052724 1250 292051474 292051477
    0x2060910050a09140607140f041a04050d0b1602010612080a0504051903060b01081e06150c030c0105160f1206171b0405070c020405060a090504120206070e130207060f02 74
    0x14064117521080c10410300c55806000e40e00039010400c20b41d0710301120108000d603180654080d40211048040740180440000d00c200e50060030050400c108078070486c20843c505a004846d210f19201c907000c04c8072445441031098205403210f84400340046011603d41c00400d8103c04c1c50f44003801010080072883d50f030380324140d000c9040040c403450292070030340c0b4084045d164100d01b1241404030f844180a0060f410340c01c0300c43d00398200200e641c0c00707556480004450702000c0f00c000000034000580700443d51004402006e9213204640240182d444140b500d0030000c07600590b81000801c3d1900c1d003c1c3e11807040120300c1c080c012049021440c562100d00000c540d8501c030300e01030a141d110160001003000031030b104110403201100c0800030b6161060b4080c1034088240e0f0003c3c0324a90700e0300090495a0384c03961807409010114410000c5140510b412160301c1e20060804000d0308c5140c00085500e4824000303d490380b1005001c1129402c20134a50101940100c181100e03460707110360700036412040303a10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 292053974 1250 292052724 292052753
    0x90b1b120309010b0105030c0d1a1e030c03070302030c01050f0d0f0b010e0d030806040b130e01140f0105010f030509010209030a11190503030901050901020312090a1202060910050a09 80
    0x1203a80e556400c1101805003141e400c050114144001030003003280a0364a1130a4441c804180d45001c50034a0070203a46e090550982045540d200c0001c030301e10300e2408613080504d89000c0c01501154001d001c010708042d9075000d6480b000354990b01100102e036a952080003d0807018480203a041e05010442503000d003601c54030120544942e9442110345c09641e40031000303846109040c0c460410898568500900e800001882280116200c0d04a003030151500c141d07503c003a1511100c10042418844e42c4180a00fa8212a139041d205501010440f0b140d140441c20b81200c40503100d207400a4018007003600a400c0c0200b02099a5600f84080c01003500c0034000509414401c60a01d0107100b4000d08006940007101680721070309510b91800c1c8030a40300001114003002003420043d4581d0b03001c4c40102d141d8821400100740c20b29044d018480c00e000009113035646103205a01545031803414220480e550041110419155449142220b50f6444070742e0000f900621030304408125010703213843e0f1110308411003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 292055224 1250 292053974 292054003
    0xf02030703140d260606091513030b0c1c0518060703060f140d02040b0a05150310120b04060c110f0c03011a0306010b090109090f020909060103020a090b1b 68
    0x181110200d0b611040d04c0b580144c1c42c200c07800342d160340420001030450005049a00031140060b04948684d105c1d45142c1d20313444513070344681d41c4166000c05401072045901c000c441c4060880042090758007142c041d0f40c800f2022425030120307101c06000c00800f43c00090100041b28a1100324003540f4402808818031447d01030f00d01141462070706000c0c0403503803800d6000401d80d048049a0340307140d5840794500c6021301c1d0100d0700806c0121003640003400c0d1a0b11030780f0150307000c080c1802d08560001c414024612038824040004c00303c82d51101c660a43c2180700600401204018001600045041d8003841d15081c062030404070840c44207440518103da048a5a4402d5101c00f5074410540307001d0148000240000c2d12240742001d10201295070b030344060290303480100011403650200d0b440703044008010300c210101801441d49007960300f002544080423460040e011000000c1407075000380200c603400c0410b5907803184803500d407044181c91604000c001c441c4c01c41507079160b1800d21030700304100b01c00c01382e40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 292056474 1250 292055224 292055233
    0x150c080706020c15180a03030e0705060703090602011a0f1306050301111806160b09160e0a0c1106010b160b0711060a0c120c0c050a0c0501090b0c07030f0203070314 72
    0x680101c10007005000b0305907800f108a00c004205c401d800804d000740500d5160030041407101144148905080064205035001040440c0e61010f040d409a0040122081034000300720600120300314800c081c54010b41ca903040701c1901ea58941303a0a203410f10b03e00d22050700703000058954030f92000a094514120803440d144202064591440e030003a00d9a07010150120b8202d4a400c40802d2001c0c100e02c00800007500c200714913000901e40100600c90f240300c0b4007580c0740c2d41103003d4841c98601089101a114202c550380703030040256240d0300030a00e1036050300e12f4034010082a0301c2c210900785107500c4101c3c10445020000201000103100b128030600500e0b460702c50441d8170789189609813070413a000748526515800d003102c083c00c250f0401d80041082010f12004a0644800103041c1c0e010040b1100042107031080304140c0c01400850301c510300c1900c509a0b41c24a1982e5520000c0c005c40c01140a01c06060b04440e500b00006995240f02460440c03002e0142d4000c59a40d8680c603041d00c80118120146401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 292057724 1250 292056474 292056493
    0x5071e06050109231e060a24140306030c04050c070b010f03030e010206130201140f0706060618050a140f030f0d031401290f0a02010603120801150c080706020c 70
    0x159030030034a2a01e250700c107180110b89480000080340c1121742c40700444910f40c03c0d000c61051380300c011880d00a0884203620715000011745d00c00b0304044907622140780c00a03c0c0c0060743c1c501100340d803049074000c0380c0080040460445c10004c11000b08000f61120a5408c420007401e40090f07450302255000301804944040c4103469410003a1802a1000b481d5045401281c00c1000194288220742001034080c0f03800d0f4014031813000d501c29948101c0f86042542d00c00800c0072010000282c20180c145c0d01c00e51349080c0c8401c3c09500202c00c030500340c0100c0342d20103c00b250501ca8000301e554413080280c4020540c2044074500c0004c03a05183e95206a0a640d400c80a0700c4050140c16004449035103680a094902c1503150803400c441e0000308a00e4a0030800c0500b16070741c0c0824002c815902e029055400b615511300e40e103040a4024410303440119a103110041514034124000c0d90142d048595880000c0103907098143e0403a20101c8050084420103030520824004c40d80b00c6c40900064500d0b00700626101c00d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 292058974 1250 292057724 292057751
    0x1060911071403040b0d020f1b0d180b0406050c0115030506090712020a0b0d1b0c0b09150601050a030e060c1c0b010e041a0423010801020a05071e06050109 68
    0x140b440c04038440c070741d0042008011403c0c80f0b104580b036107000250b0058464201c00c070f40c42c0d841d00c00c0c0040184502810400503c6000c1301061004510300d060b181e45141011840c40d0041408482c440c5820800d4240400c0003e107000e0001420b100444600000d4041c0791998034442c0940b058205540c80e13406034007049403001080010390040e2850303030341c81c09113104103070f0006a884141c1d00925108910100300080c58034207a0b004295540c2c0c8194080d100d00a040d60001d05103d000101601d22041d0350003c40c5040401080a01c2800200d4480b50b0050782d641d001510301390f0245000c1ca080540e9114402c114130001d200341760054411740b00c2580c0d902810105900b0101c2000080309035149080004a52a84c01a05003606600203443c00b140d1108545002c0c414403e4024030160032504040324009108400110426070740c0c6010818200c990f01d8950321400c03405513074054070204d48100846004903125421100304401c210340c100f02603403415a500710607600f00380e002c504be10352988071940b00c60 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 292060224 1250 292058974 292058993
    0x304051c0c170f07061b09061103070f030c050703031e0216030321050c03011a030709030209040c1d0105030c0607051504020f100f03050f070806040e0106091107 71
    0xa450403885162590b01c881480c0011902d1001c0501800141c04825070f401c40c0035200882d40103441003000c15604000140c10114000072000000c002441c00b0600a026010503441c0001440c01103051508a95581c035850128610940c2449100c0200000280c810091040030303501c83d590724040d884000b0303140c140b0a030144000c8410764001079049114210317801640740440340c0510300003100800c0d9000c0c000034810a0303090001c0060410301005030b0706220200035412620340219203864911009030522076400203440890018104220403c05450a550801c2d0060b004000c03914045986181c10040c0542c1e440760981c50302c04190040060b03107010300480582d07040a59a80340742a6080d96440e450700f00740d0a01d9881c00414602140664840c2c40d07004a8604c005005030a0036400e4a03c013506c03041d9140342050000341000300103954550303004040d034062031070fa40302c89442d5102e441c104409005c00c0c1c0d045403004d40d642c2400068200560141180011003941295540d001a041c0132451 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 292061474 1250 292060224 292060273
    0x1e13170f040b07080c160308070b060429180c030412051b0d1101020c10021305030303010803030406051b0a030203040242031b0703020106030203010c0302030108010e0a12180b030405 80
    0x10146d03400c400b000800c07103100032211303150361020407070003103039585400180101100200e18401160101015030658002c08a00300881405c543e10001072050b0310144280410841d01000115070a00200b40007401c50851414070135810b040035070502c440c01068510341503400241c03600350350205116040c416044600d00410300c040e00002d501e00b64281425658504000034280402070340052990008030240032810080d110040589070b4070b5079180e0031a6541d42003030380c094a0f400e107000c01149131070b03402c18121081c40c3c83d540002400c1041d2680290700039003005105070380020f4900b101d59082040264441c0103040100310750340c0940b00954207503051413900c50904860503810020b208000f80c13000c05c0103000020b17040140b51381c2c01d40c502c1c040303000d0045980002e4040d801c150414140a406402850596032000c0c020809050707100003460351014014405056009511305072000d0130f1080c940084d580d400112804d650f03039a181c1d08294258411142036529801c24800c0d480a00840d1000c28032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 292062724 1250 292061474 292061503
    0x80736110d0e0c09060f0109050d03020f0d02031603050f0c0f0601080d111509070b0f0a12020a0e010503060a030b010905090d0c08030c211e13170f040b07080c 70
    0x42083d0900400d031070383e030f005d06568401c60343c0750b91000c49a881070480c44058100644240800d00300c0d442c0c084e60704c10350714020107480d001d485c0044002c14400001e84450480d03070300030180505444d0301d054500d03500542809600c003404020903544a041003041e05240b98400004015561400381046c1c200524036810303100700050148800d000c1d40001a19061041c03d48440d41050384030740082c24609441a40003a141070804100001c1d40d0720854094500d1a501d9150f814040b410400c407401244201140c00c000724000c28a000015440b03400616440240900048c8010b0344986441c4d0000c04240d010314101500c1d4020882003a80034021120340c54604d090424140c012a035072a06203020061060111000110b00308100d500850680200044044c0980e00c1b5410701d884071000a1a10403103071a59410341101041c48411682100e07120960040c041554240c0040d80360181940600311081500c9070a110110380400707040003c02c40d6503c95586550b8800c103a550041c1411104000c041d0b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 292063974 1250 292062724 292062733
    0xe010501090f14060c0d03050601201902031207051006090501080a030809011d0d03140c0405041505031204140904020f04020304020103141609080736110d0e 69
    0x10700881c8012580560f070302d40e69504464441c3c0c0002c01c01c28082c051611009105800e4540746940c0c2541c40b080c020034003a071380c4c1d00140c016011070003400c40b1842c03103c2c02030f688150f50700345500d1112304602192130b1004040c1c0e241446404000003c07500005410342d01030300079401c4103403444041d02c50f48009203281c031400d214039032401c107a803a1100004e61024061000900018460751000c1d03100000780c00e98440b4503058800e0350100c0d0b595401050040c0b101280c07820545804804400e0b85083c4162604c0050501d01420001804003600291207008850029503102140c039a070700b401064000c4821101c000c0d107542c5016207208002200d410701074020384120041c040543c60300b030604401f42ca410754001da40c07900c1c0d603c0100c1c002c00c0c4a10890141c0700c104424000541c50000c400301420807183d032580b201d07940300c0c42e2558850a071886828601d5503901044a03000300e046e25041d079100503d0703461100304090b101ba960280c070f402d0564050709510010703011405180e02e00c10140704582d43e80c002d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 292065224 1250 292063974 292063979
    0x90a0906060206010618120b01051305060f06091201020d09050d0f1b110406060f090e0f0f04080f0304110a0602030901170c0705100b040b1c081602060a090e01050109 73
    0x207500c40f081801100104403240c441c140c003001c0780c00700e0744004090041c4e900c85003006501f40260703c00d000307000f414441c002c43e40ba540190320030b5008180c05039130000c03c02c01410000b64100032403544182059034201181d049a0401c240080c0301811b0040401503010070282c40a10385107040c600d40c24a51401e000c5407501850303005034019055260b0000089840072902124200004501c0c00040b01070383c020705000c0301081c000d900c2000308000d90301545079110101d0310740381c0b500041e910859030701901034030640001c1c010320004580300d5001401145050315000c000d07045580103074001c50702510840004a00410701d0304108642d400106042c1c8050342c201071640e00002d103c92441c0d0f42c610050103400c00403602413110f11040341c62240d48038046851200c0c940c014540500044071a030b6125a03c0d1840840d02c03800c102c91401c0010102c0e0600d4158104980d075034000e40e030010a0100511020044000c0050b12400004c008000084d16080000b0380390500090b04075005030400340c1040200d0004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 292066474 1250 292065224 292065227
    0x1060e030f1b010c0203030a120e030f091005070203241602100c1e1d0604030f08180907110d0e060a032304120e09040210200d020102090a090606 64
    0x44059046061540c030042042c020012100c80c1100e1001075450301001800354107064010300c04000e070042900c4140031b040010900c00780c40b070080c80003141b0b0f0f8940420464015191110600c0218101401e181d800d0003000d401207860929002d10040d00613a1961000142e5002a400150700c0807443c1c040d003d071560384a000940360f170b00403c903181e50326450380003070f80416000d14121004840d509102c440300829a0000401ea0031110b1200a200055803071400803d040c00011101a650014000202c80c040c40d078440c012a405107030604071004000070300b02c07402d60742c3c881507034000c0e821561500844c0d201d05c1e19090070805240b43d01d2040c442d1008820310350b40c0301c40040e0740b00c0c80d03240e040010700b2980041c400345110945540110419508a04010400500c02c0c1d02200340031a96451040c504c41c4107080c0107002e48180c078003a600c103c45000c0400070620440042400a1101c040c04080f001c01554041c0f40035044001ca0f80580d4004c0352200e40d41c10410700140080c6100343c000e0250f580380010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 292067724 1250 292066474 292066483
    0x24042309061005072303180904030504052101050705090f01030515120705060c0304180605091527071704020a060f050c10050a0513120f021e0601060e030f 68
    0x1d03801031050103d45981030109403801c00d0000e08500348040d82c8405245260b548076840345100000711f40140d000b4108906200c02c006200d50f0b41522040d2400341010100710405c0c404e0405840c4e01c420121441c0d09401c020301440c1d01a140380d03115075858001c03860402c1044001d5414007810140b91004018080444a5000c80c2903007080d540120350040880f2000d081c46060780080d90401c2c4000f5582c004000c00100400495041d2800c1c52803105440d20407000391803152050b242c1c8802d8810200c1c101e244c18160908203980020500d00042007060203021035200d900c1d5184085003905000c008000c0e4003e03034940c52480001303036403c101c1d1030640c0c00a41940800d0103070400f08420961035110f218001c0702140c03106000070302240c040380c80001c00c00c0007401c001c45a0425160410020031a140c603840c01c1c010045a0003090340c160000c42c5082110703040c064000717440c01c52207456034810300250030500300d407a00030910010f0100e80d8140b07940a00400350859401d402540300d440050290000410b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 292068974 1250 292067724 292067749
    0x1140105010302030a060302040e030705150123011b140f0a030c120c02031e0d050705150a0b0d0b0a0c18232107050f06092404230906 59
    0x2c00680740c0c2c0b10464104020122600000c0d0014900b540e03804455000201604090780b0400c100e40464007066001c0ea40b82c0c00c01c0c45024244105600d41d00703905242011580701e500c4040c9440d010441c28011246280c1089003010b0b0b9000208103400d40c00200c040c81071005400daa2030007004554a00c0e40c0060041da80044041d08101229191310303c039038422003d201c070301e6400408444400c0740b031850320181e14441851a074a1f41c400c80c41b0301145603001e04251001613420402801c446e00d86421240405100200540030156541c6054045a5116141c0c045203a0260841b42c402e868596024800c40f03050003020f03024080c080c584980b2800310a900d80c001d03502002070003040603007450760740e04507015010b83c0079602c04034010101d81c200c0040c2e6a05540e2001180446560780d6a40702804488803900851580200042003082c0c1182441411404d4820040c05030b5061058060014080c54105420241660180f103c141c1d001c440e494007000944001141c0110090070403000040c4901c0000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 292070224 1250 292068974 292068977
    0x90307030f080d1b09060c020108060103021c180516030206030112050f0a060b0907140307050c071809020102100618050a0902040603050c1903080a051b0a05060f01080114010501 78
    0x32008142003000c0c2206443d402c3e0407900d4240050381101903580541d10800300d0b1000084e55032180003962905c915108001183c068613840d6607600d600740110b02942c8000b041440a803500b0800b00408081d620410020444020309410707031810514010b03082205030020745221a400017814005641c408040707a04551011203844491002841c000e800c105035008a95414050608010144106a0020301e00c0310000c580383c102c0b0740e82d500800d5038581600c1c900b041c0c10b01d1080c800503503c14000d6000b043e040d000e01e011640005c1d035440c003c10841580c4080b0456894507101540115601002003500c0244020020b010207810102d0b00c01032001c40c000312502103070300c0b40042030014003154000142e054024105002d41922801c015907103802e1407103ca070161100c0148040c00350300e4a14814140c03640000002d2504140800031141038014036021100703008409000382180300308004c0010b9081c4500090714075480d05002202ca2000140e1101605034180001d0390300d00701003850500e0548809 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 292071474 1250 292070224 292070243
    0x9070e0a0902040b22080102040e060f010201020a0e12010608030d0e07080303090a021017040b0709050d0503070b07090f1701110c06240604030f291501050d0501150f020309030703 79
    0x4a107485e01c80721050303030003040c20703520028000c9800e12255212a101d04001e4035000051003c1c4e0004a08034440c14401d80f0011b031008000e51800e00d0b240f081c2c2c200c800081c00000c03803035a460700c0c80c1c84d00b59031242019040d4140e54028180090030140407070f80c000c00c11030001c0c50841c61321101c4203858030b0560314001d1207100a03081071f00c13185000c3c540ca03903504071444620140c3d52502c3d103070003504030320140c0d400c0001c61200e000014103450301e00206117100e64050301450070f0900550340d068240002a01010a01c901c0303010200d400ba60b0003d500327000700840405c072550002603401d01030031109604107103500094100801119603400050554010300c01001070955600027410201c42c02500c02801c59000400082c0041880051840090524096480416071800d0340852024654404a104110140d054001030550034403000801c0308080605109243c086000031032811100c0c00d80005031103d034064510300b0b0f800d6002e1a8184a40003e000451402c0e0301500002e586c0c01d054403008000703401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 292072724 1250 292071474 292071517
    0x507031806021e030106030e060f1e0a14040f1e0c0e07030608011a1c0203070302010f020139230703050409060f0326040603051509070e0a0902040b 65
    0x703450100d100c0682c3c64549850307503101d0380000c01074420b00f00d40100510500000c542e0b514030901e0024014041249080e40640a11210511032030004054018071580c07104548919004a4840340c480e030301c604011041c01c245403405100544440108040104100c0c0100001643c80743c081c3e416541ca040011035150748880e011000380c805134002140d01d50030a101500084080803002e031394400202c03450100100d06940440401000900180d45a4400e102c1000954003030742c1240d1004641d4400801d4a0b4a035030307101220309a501c2030508400081c4040c8540390070700710111080303038085445d203051a00034000500400c400500c0071140000310008552040500540840f03000704a508024011503903201d140c104440360503c4261000700c0800d00c026003040214099140510454410a007001d09002080300288002407082c1642502804030b00465510801140d129000395030b20280040040014444084c519510003408680103000601084000e03c2c01d441045000407009051240f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 292073974 1250 292072724 292072747
    0x80609060d210921080702060d05010b0901301e0e03121609060c031101020706050403030c022d03040e0a02090f0a0b0306010c0c1d060301050703180602 67
    0x154101d030001c003512030003050303011000c2400a650b0031a2415403151902a55240c1c2c10075250345160000448003091300c100800000c1c022009444600d00161085007898211901c541c06c4540a0708610368101010480145a40e400004c03041000040244803c0350700c406c00c8410a84080161940203440e141d81400206180006042e4800b0105203420f12203201102c0001d616984641100840414000e0010306a180300c0d1080d410b107440c8541c0c170f40005038604003003164100c004c807508500b040909084c81c2881002400074000007030065500051605207840c001d0110b0b061031001c0400c3d5008444041c444002d0620031105140a0045000000b42e421317000c1800d5225907004402090010f4060003e191920b5001d42981d44044d260511044203200410044165034400c41c0034001d000c000003040c6500c2010081c9802d44102108180aa110b015034007804041e03c940f42d0011400c0010840b02c2c2c0380900440ba00200c8508040080342016030341c41006280c2c001c0302038003d83d00040c600b12043c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 292075224 1250 292073974 292073989
    0x12040302030910090f050307080d11011524030621050a120206010314060f13170307021501050910031b030c060c05010c090503030a18052e020d08060906 67
    0x1d02d00401458840c040d400014100b4001c90180c400c40ea54001004286030400003854429102548002c013480c8001a100300c40041400e00755800d40d5403031f80f55403003811051040b10381c090312400d00211046169109061060840c803001d00c400c042c00d01900300901200459403444000220341402d0030046541003c07498070900c5800100707010b1422000e070320320329804282c95060740c1c455014030203824148090707207175a00b0054904071012241700001ca40b03414203c800088440d40f0801c0c43d095200030100600509400844000d0050707008002c600001d03801440441e4050101110207a10320f050611001c00402140c0c040104032200c508425141454070302d00030002940d0014000305950b40760803005000102507074003102c0560a00a1202d8500e00070f4401c00d0941e000030b8025420614000012a290000c101d00950095560340d0041207548407603000082351954505484000f10300110030000c1c0c00c00300350101c0c1c11034000142d822005940103260350b030042c0301110b00090726115000020303100d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 292076474 1250 292075224 292075237
    0x305030133180b040801020c1b0303091c0f030e2b02040b0d060203070c2001020a1104060812090117090604020904110409050d03181a0a2408010c141204030203 70
    0x8000013043c0061603610540082011b003028600340d504014a880d149d01503005501105949034009000060040c103018440e80044c4200411425041c82d068403020310a075110001a07002504950b41080b06081c8203807840000e110181031509814940706903010f2100c1c101c080207101d00d44460801200717585000b10303840d207160480382c03c66403404c01d554007902006400508440d42d1207e88500080e460500408400c3d461042e0040c1c042c1c0b002c1d60b0b9400c1c90f102c118400003075004e0f50700c080c042000f520801103802c50300741da207100720ba5444100300017604d400c0a01124241c200201c0e02007010240d0003064080e04154140c41480c1c207603e0b5444c22546113071000000540062500304000184000043d0410003220940c27001c00100b20031030903409040c036a411010700f0f085101c05041c0e1404ca0b00121032640100000c2c2e002070040d00701a010081550741c0c0d4024410007480c01d4050000b20420f102d425840074044c10a04016151400b00c0f82140c024003c0d030340352140c030500000741494024402c07141c8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 292077724 1250 292076474 292076489
    0x304051e0a030210090609050402030405030307080a0e030406031406060a1b06180b060a051f2d08100f0e01051201060504060b04030606120503270d030503013318 71
    0x20702c004e0206004114280c144102c00005100074000a41070800c1d100b2640281c2d0041c014604d140d40b0408180d41c60300002d0301c05241c40da41c07514980e82c09041840a440680400d59011440764850701d0715603030444016015a106180821000000c25000300013424080960769205c0d0030080740d410580d000f4100c04400d038010014201c40b4004000030103220610401003180c407200d000d500c5034144400c0d48142da0328020540000402611500e0240c0c07240441c84501d00107080c000a140e0a0004080c6200ca86a0010805500034402c0c040144184800644212401d0100d00e51510740224513205040c801e0174001e4501c0d0016404c2c03881c0c04e4100304003502014006000203640c0d032001c061070354003502c01500d00078035169000c100031084505410f090740d0800021400d1407104040114103541c2c0148422500031040c0c10106252a01130811007290302980700c00340c0700d603d0040c6010075644403000e240c42c004140b08100403e17542e0700c0303048403044101d0725002e000041207040600211846401010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 292078974 1250 292077724 292077739
    0x110c01113a0c080712090b010b180d0308010512190201050703050c01141008030705030306010e060c190b0901150303030f1d010207060c0504030b01050f0409120c0b01080304051e0a0302 81
    0x1845802074480e034021000b85c2d0351106031810051400e4215014901c00034070b00203d1000400414407a5005003c91040013200303c5810f03000c0380c00050034406034600450210320203100407c4140f13400a503511001e02c01001426409044007800ca07600001c0d400000d040c40804101d60040c148900156186003460100070404051484a90b407400101140c25803121002c01d840030034098408001ea443c0542e110000714155110318005454a0101c00000b03500f0803400c0c499080d82601c03c0240e9110030b008030020906500703550600310401d6400500985084e810407290301d50034503030240100122501440d00089512420140c030000c0d0061211445d002d0180140140c03030010103600805010303100314010490f042c050381302035619008a110103400c882e40311004001e0b03801c1905440075420001840000c823050a50344031070707a00070807803551030020701032141840802c50509006400b405404004506040c681000102a001d044110485020015142c0c05003911030110030b0014650080a20 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 292080224 1250 292078974 292078991
    0x16060e06090607111005090a020a0f140f010503070e1207080303100801050f011401120212060312091003180b0c030712020a14090310110c01113a 64
    0x1540d403480203840c52100c07801a0404100c0071400342c07a40c02a09075504c80507203441d07018695644010311008140e00c400f409820503441c01a40c41082a10141501d0011210f1080c2480600704030308180d215500c2c0580280c3c0c80c42c030310700d03030b0000281c980c0440c003480d00840424500f000b180034102c44401c030400f948039122012070342c6800031024503c50340f62602480141035445900304c5c04e071181900c1529070000140c0040c0f0800251041c40074640780c040c10b10490081c0c0401d001c0c4c00300d03481608400d00b4aa280c1081c03140c0c600e002e0100440b031000d151030042c1090030070400140403222013401d207800d050703558661382040f481700c20301c22003060380000d00f42c00b2600d4200b4002602d94022180003002139005101064010381c2d40c425190700c4101d030354418142c00500d50714902c10340d1209019540c144030300751003801e240c0c645000360223400541002060f11800e4100f00c02d801d54080c8080b8000100050081c2150704507103201c5030141a00d42c0d5045480c0d00340e40c9440e2100d040c0c040e82000740c814140501d5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 292081474 1250 292080224 292080251
    0x1504020309072c130311071523040506070606050a0b03070801170c150c010f02130501020a0f060207031b030206010f05060a0807050a0201020c0102040e0f010f030c0306021606 77
    0x1801c080b2915891400080300c0c4803e00a051000644260042403d2842c0450300703034648110601482c07071183c00c016124003c2420840c0c5081581e03840b240c01d004001c041c003c01280d00410031000140304407980742641c01c0d00102d03c04240641c1c042d075030041d0b001250300d0b01800444e070044d0004100140c180c550540d1600041991f55008496150200c0c03560400001c51a0402d03120019a050fa540039100400c0400100100280e00482c4000c40243c1030100d070120b100c080c810702d01e0480207440d0060740d80042c80d11036102c50015600c018195013140810901241d402c16400c4c0000b0350143c0c00590b02c030800d03d01680d81d0741002e240181d06605c080010070401d81c0010719035040c6d8102034818015030365940c0030400c061040c5a0301c0000107003c1c4012800d114001c001421484c07006000260070140d007501c0850882c0c102d40d06c441c11583c0c030902484050000922400e015001301e1807190a00c904545600048288603c80107144580c0020160151541c000000480320783c03120307003404214244041d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 292082724 1250 292081474 292081483
    0x3070c020904060b011107061d01030219080912120105060a0302130324020403080d05060a050d150b0609010207120510050a0e010b1e010e06070209040b010611011a06031504020309 79
    0x100c0c0d0111b040b055250601c43c03000580c40e821150b40355200c0c0b1444029031007407404454039100150605400380072242c0d407004600b03200828040f003035503a59290f2400d9921039250059011580c0e400b454100854442d01c4040d034415415a8000e0b40d0b4a640c600326103400700c00030312480d102c0e540c0640184e4404002c01210710201c042006e841483e400052000e06018030880c80b079071100401d000d07400c2241400c0311030355401582d80280f008041c40192613580000c501c0b00070002100710b07000e0a00785051480d005080c441c40d488401d003030780d0b00c50500d241315001070b45d03135401c502a0100c8550400641c030100300e410003110740c0141018006200f142010281071019064000c01c50009500b4490701003050704000c120f1a0b19091500700264101800000541d1100f44400040c0c5c1c0112003004038101580310f080b032480c0524801c15556205615240700141600400c44c00305200364100351840c0c0400c40395070300c6100f80c1030084980f259a6101d220b45441144d08625201d5080340c0040100031040340d0125 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 292083974 1250 292082724 292082741
    0x17030703030b010f0c060b18090a02040e0601060c08253005041503060801110702031506010903060b01021609150906051e15040e1605071703070c02090406 68
    0x80301440442c1c101c00055540800350950040003410300c0959401090b46030300442500300d0090541200050f05500c0c1068103642103540c107410350300c5001c105086040500c100c42000c0303814009003001e5410404002c00c0d1420141014010f034202189460700500c03420702e0303580c80505880c5089039854040c64843c00701c2451000c0c001d14149003c4821251a9101e9819020401300e41c1d5100c0c9400c1c01c0641d03008008049074820010107980e600c020410900074404c42e502007051104494480d5103501c105031501003820f006d100e40c2c036202003d201c00ca0344c00070761a20039240c1c8406d012641c10320210040340342010500070003180c450301443c00120801b5543c84041d601603044600f62085403074200160a07200280314954200c6480c8400403403059402c0c55203003800d40010024004203003c140300c82000e0b0017030303084000300502c95020300010707821a07041c0e0070310700d1107d0801601b00f59407a02c84180580d80e500285091040c0040001d04543c031a09440f002c0941c000d0449189003840c4c01c01c03170020214070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 292085224 1250 292083974 292083977
    0x121617100302120c0904080a1103070c051014030705092707020c01020a0305070204020705031c050f0604230405030405060d020903011d0703150b04020d0b090c090a0e0402030717030703 81
    0x6114143d03602c40403544034a00c003000352544280d07868913a20701c4803d5001414100030803e4501e018169600f042c00148406401940110b00c49030130725080201403103003150300405101c08001c0c0d13141c016101d41c0c1901d030301031031509250b6100c0303a4a0340460710710411070b29066800711141000c0a0002c1450503494010f0509508940740601504016a03465130444405030104a0030f00403800107184c990000d084141c40f42042d2400c000a020a402c8010486046011110b4a5030100070200340e000403010361040342290140103440d807030711111390b0a00d03201d290038082c00b540c00c00180034008108200c9004140203040340740e4401039000210002e40200c80700340e129509207004c01883e2000283d0740b440030503800d0080d20381c44d4556599680001d4055400459803501c41c072420318070790b50b10320203400daa9682c2d890102e001314000c81004002c000080c420b00c6a1201800b02302d01984541140d517054a1202c00100c003130f5141c500000b4a4035440f6800a007402d8418910541003140100280c10034034802e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 292086330 1106 292085224 292085239
    0x1050a18022e020f0607020607050304020910210204110c1c020109020a1401020d08010b031303030207020a120b130809010c0609060609021c02121617100302 69
    0x80240b40809030b000b01c402e01a0004003030003032980c407000c64805041a49031240c8060050301000d00043e003c0c940b8074000808005240000d50f010300300251000b00c1c1d025074004040d00603565044200e000c5c500703000c0d01c0d03c42c0e801e15038141ca01d80c450b140d01034200900c032201c1c561004541c048425045640760340015016031104c80000c80904071400009500c44602000a071401201000103810803840c1401000281044002d4a4100002d843c0c59800088581011406400b820034041d52105000c44001141c1165044150005110303002d0784410ba51a10302101c2201520503010384021410030500c1802e606c00c611009481c3d108000c00500304890307440b44c40441c0c065801c5074408590000f541c24166500d50440c3c1c00100f01d012044d46001881100d410084502800345034100c03080841505942c0d004210303000f008a1403200ca00d00505d08807902c01c0c103041d00ca00c0140c2c01040ca = true := by decide +kernel

theorem cover : BRFrame.Cov 291906474 292086330 := by
  have h0 := BRFrame.cov_init 291906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 291906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 291906474 ≤ n) (h2 : n < 292086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
