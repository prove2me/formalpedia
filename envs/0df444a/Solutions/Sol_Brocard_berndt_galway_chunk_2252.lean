-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2252
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:08:03.170064+00:00
-- url     : https://prove2.me/submissions/350bf6e5-a5a1-4910-9a74-697b2629bb90

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 404856115 ≤ n < 405035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 404857365 1250 404856115 404856163
    0x50c030105010b0a0207060e15030c0409020f0714031c0507020c06070c08060f0708070e120a0b0105010207091406040209061605010b150a12051009020a08190204180b03 74
    0x3a40800500055800740e00ba039000580300c00381151102c0c02440000c0e403100c0000d90209609d0412401140c00000b92410185010b90b00c0c3d0b85102030ba0020f0f003c2070308000c40401c031b0a061007180e91403800c2143e580c001462425031a6200101311000440c275400d88266180c0004151900070401c1c030049a500030412a00c0d0b00d03017458641e079964981c1c050300034580244004903288546e1154031034094202604c5240c00c50761041d4085a610b0350340f40c030250f07014203410341c001305142e000c1c002c02da03441c0d005541c81210b070f6041800282c6841c403980c0c810400385290810030041c2c0700402040c03640160085a001d40c0d00d41d0fa6100107191400340d8604c0903079000040550f03400f046415800880c000a080e08e08080200c07052514801078021a03078880007162058140c104500c50903440180e00030907002c81002c4007922546110102d07000a43c540c0d011500050501c0030030352103074802c00019000d01c0b41c1035183c0360428103502070a20880120514507030300e031165200250f50a00102c03400e200041f0504403c52 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 404858615 1250 404857365 404857379
    0xc0301060b0714010608032d030c070b010e091e03040302060c061e0f0601180b0a030209030c0406030819030e030a0c0b0a060807063603032c010507050c03010501 71
    0x54810030003154500b100000101c240307901170041c001140c5500b00a1428904c500364041d880380e2907071030400001c205207407106128500e01d00c060b60180c4a4181c0c4217488407020720341b0b8298120103030000c900c200c040310304200100380e0024074180c41001049218021080707400800c1c2ca13501880d00000c0d4080c0d80880c2c0c602d1030b070f0b00000356584030300300740032820394540c0000d10303805910302d415201e0030324465040300000c126500441082a50305081304c0c1c51502141c0c1c840707580c1c2a54120a02110010381c000400d00607a150420000c0180f1000311802c0080a141d50b85030080340c404c00081200d4403403050b200c43c158501070780c0484041500d400030703a555060342c980020724282510001319812a84000402e1645003684a0a0180c0700240c00500c0d00d14100f50b41620fa52400442d001c2603840d54295103075201c842c0700a6035013960319840303003500c0240c11031501900c0c07494140410054084050f80741140081c42d040b802000f03c00c203082469032030443d07042660a1411400e4090303010f40c01d10f00001515 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 404859865 1250 404858615 404858617
    0x50c1c050c070b0702060702090c0c0a1101110c09010608060a031b150c240905100b090903070b01061b02062106030115051c0212070914060105030a0903020c0301060b 73
    0xc286808162003441d903d460204445014041d8081c1d04480d0912014006003454618540c00c40c0140c0b210b80d042c01071141855147c2481e0420458420701c07080c6407a501540c018040000d0a0010005001100b800501248079040c051149008019034071000c22255101c2d404120041d40d00441d4515004240340001c0400d42094810f2001c0e803c8001c010a11440c8507500003040d641c1d2141311410074810140d0080c0c480408000300c1d001c10342d6074003085030024000f0003120307100241c440c2011928100c200b00700940070100400e4080250800c0240340c0000303101c40d4100b81507a402d4184003461801c50060104202d183c01c1000f0740100d40025101e280c0700d1281310600c4c00b030020242140302540c7d1041450300703981c8039088016640c030030b425080c0014602101070400036000300310782101502043c4c00241c13020310200721035047c0340c100100c00d00c411059406160f0928040014401030303400d003800020841d1000078900b1802c40e41d2103801804040c400c0c081c032081884024000c0c8800c5484e02108141 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 404861115 1250 404859865 404859877
    0xa270b0103051507050d0902270a060501080402130c020304090c020616020309130207062004060e0901050f13090c15230a05030c130306050a05090c03060601050c1c05 73
    0x3143c42041c0314002c0719219081c1d01481a89a035554609050224070088094802d00004aa000d900798010480303158900300206070112420380c90b09941c1c02c003000c50707504880c2140c2040b03040120364820000540c40e414062204c0c0c4201010002d00c403600350004038114069500400c601c107082c036414034180d590015880707001d4800e400b2802d05103000703682d059070b40e4440c1c3d014003a00650140580600600303140e0240204038080e04002c81d00e01200b03040c01c40750a08030410048140c5002c102404000e50060440c1c0300c1550540710f141c41f95040000007030710420703a0160f103446140710b5001000301624507005803440799400b0240405858645e88200c1c0d03800ea8020262000503002c3e080c4a00f9450448240350046881030511071400590704c1c000c681550000f0150044404100072802a250103012031200844c0140c1c00083c132800c05c0789040c0c054440240601c0202d600070110000b8664005c90030f030b504200c09081c60341d91100580081e90900c4e55104485165020160403e8070440c3c02c4001061 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 404862365 1250 404861115 404861123
    0xd020c060a1a030f250801060b040e070903020603150f0d050106140108100b07140706020601091a0a0918060e070302101713020a05040203101403070e0a270b0103 71
    0x80c419a0700c410f041d40e4840d40b8008405645c4082081201c3c14225001c2509501c03500508078034079a1111115401d446007a0700c5690245000101040300b203180000150b000105483c1004006107940c000940c0c0340170140c18500406583c2c004c8012a03950519845d020360340140440640d00d0b0141021070081031a4803540d0014000704040348050b6101c3c0070361030f101d20755540150320700c542060f0308281a90005001200c04204281c00d00704218006c10605004080a60040826604000448003554402201c1e650b1080c0091401603045d51200218000e0768414140041d50002c00300e5000c01c0342e0085034020b04564900110688080008100b000580e03000b503c2409040c0223040d000c8a0010b01e4480302080c001015000c24185508080d410320f0300703400105440c200d07685803000201280e20a903516488003072580f1040002c8019400080c6400380218042c02180c2d2808580203a0b50500030080d00d00150b07221000e240300c00e01c4c1e00703e078005520768002c040850100c92410b290600000c0c00262 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 404863615 1250 404862365 404862401
    0x1605100e03090310050408120415061a0a08100906030b060907230a0903060203090c031c230705071d0a0506060712170705091806010c080d020c060a 65
    0x144800c000411074030100e42c064010b06030384a0200010300105006482240d000d42e0400590b0044030111008e540183e000e6944000c801a20f010f00758120b07000caa201648690801222444078801a0140c841c110490300f0a6a01603840b42e58203520401075400000b80c0328035013440402808240c0991601c1482c05942d81c031203903121400d00ba0b686904241d601e000100500d41800d80c021032103c081e01391020541051482a9201d9554500366081103c03080a258020f400310b010902c1d08000c900700e004000342c5904d0b884600c840d0300628441210124522800203a0883d01a803034200084070351082e00300003990700321a2502010981c1d0301d16143c46040516410300030815040d143c5c403a20f4040c03c0000c16041c540000717580c0d4038140500c41036070300040c0940c1203403c52110408030141c2c0e22520955a03590741d161031201c00c10030360051252061400780002010858546d07081000303000d1480d0440c201d9515011500c08080181c8101950000e85000314014080711005a401802d41d2410070302043c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 404864865 1250 404863615 404863631
    0x408030a1b02010c02010f02090307031202010912110d08040507210f0c1e060219020f09040809212e0c081503011b030f06080a1208070c030c1205160510 67
    0xc60927400355007085681600f00c05410400118030400c1c0d803a400c4554000400e881405485a0b01c10100640b032640c0451041001d40304c14031000d01042c1517110040c01d25142c80e040030f03182e09030703551414000c04400c2c43c40c400c40d070381c42d045181e6400400ba641c400340502c00d042461400d0708a0000a2140500c01000c4400640c2c91084a541d90020355130668000c10302d0407201084800f00145a09060380c1056004402084079101c031300b05e05100301d004018a41e03560108000307000d12010321840c01c40104080d140e000e8500200450800070301a00c40c0c5d19010300d034040251072610300340d4480b0200883c605d00108200d01a8001100c40c1c49201903041c0b003071a0031b030404203240c01c2c3c4020040c0340070040c180003070078885c0a010781c1c000b0340d1130000d0401c0001d0300303504c820030545456009041a03562620400d01f203800f040d804001d5951105092a26805001c81990301801003003442c2001040880400011007189208809565800800c44500100700a1a0400c0c9450300850004011554144000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 404866115 1250 404864865 404864891
    0x170a020106080f03030a0504020406050603070815010203040e0f0a061e0503100209010c03031d0a0b0421051b120a03020c010b0109140f0a03080325020606090408030a1b02010c0201 79
    0x18000b01c5146060242d41703581e8500c91136130300a000080049a0103541c40601285680700c84000c2d47c421030329500c9101290401450111044216100540c1194400c010611a45d1200c0000a400400740e081c031060584840862101410306a00718640403c800c440c8895540100051203085804c00c0d01070311a050000c203c40416407080e04842c5010880d800b5022000070b2099109411800c680c001c85044044044203041c100310b8104400e8884d000000c09100600c60700e01c0f66414400700503419180c1c031005030100503002c0c2c00307190901c520124680d06c44407000b04051107040142e500c021b070340640c0d54140c1d03a005802900080e01240302d561030108010095401135014200b501c10f500e0362690300d45020700030840c0f86a480b0725804e0300410199400400240c002002d580180903048101c00c915402c200840807612406c4100404c55103c030003806400c1d101c1804840d085a0400e0f4681c0c0d8a40e079582c011400340107440e20190244410710070311141a981075001c1030588902d64000e020094030065 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 404867365 1250 404866115 404866123
    0x13140604030c21021f030f0207021012021e0408100c02030d0f0207080307091502010501150f02010b0306190b0f130504051e010204060807180e090703170a02010608 72
    0xd0495410a03001c0c0215038403240025054003000302d0500c400e00f115030100c5d49500100242000070700340003001c03101e095054020b09003080c000c0d2008504200d030540025a031a16402e1030300c03041c0140d00f00100d410b8001e607012101c2c15010208a8081c9a1121440d544158058822260a0300525080c9030241200340100a22055998019410502140c82c0040109101291001425801c111490016442101652203102c1980710840c1035445c080e00104c040e2030b100e48040c116450407005101220324031401c58140c00c0d403803806584491204e070007030380140391440311150316104000400007a02c00c42c055222007100d4490042c0079004200b014450112042d108441d0300c60004441e8015800e03440c0c0c40980c0c010b00400c120340350205882000a5032402107500605103940015013441301d076400c0b03080c82d0381042e03540c030707202407038650890418607011a0f6004086080c0d000c2c5c1e01084600204001c2d002c007031034004150102c0c44100c054032800a07440903110300090350a003c000176500c00081 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 404868615 1250 404867365 404867369
    0x30a0311031308030702070f081c0216060302130e160f110a1b051905011b030507020d2103050a0606020a0b0a050a0f0204090903080a0515060706090813140604 70
    0x34208800750306403076841a0b00c50308005c00034070441c810034100244018000070b41500410340c400107000801e20340c1c0c060202c0c414421500c10203540c0030318608130394164414540011a0720500d0010f8540e1111250a51590741c02d900c1426120040b1007444240d061001d0010807001031525501a4080010401c4d19090400325020070690004100200850780038482102d0a900d0700780700c50a01c0f91a1400100c54404c83c1c210f020310b0302c0381704d41b051005507089000441002c0070082091240550b076a0018030754800c4074002800303411a03800c0c05c002c2210079104c240b141e40018569982e1140d040400500400e01100e81a5402c5d092200c0050803d002003102080c058100c41c6083c42581c03440c1024000e41005410302801658462040c078003201c4a10251003c0c2219840104500c14142802054544060024500c03145850300340030b0f040c850318035201900c0c01d041d80c001d5180d08440c14104024452048040d20300c0c60f0014030f40015030820198401a904190440400c5011030028411180118 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 404869865 1250 404868615 404868631
    0x3030f06091a09041b12060c020316061d030d0b030114010501020312100e0106081f0b18030307021906090b160f0f17040603180b0406050c12040302030a031103 70
    0xc2c10461031420500c07100b6511500a0b101c0e4400d44042911891501d065071748403581141142e5005e0702040280c3c000c1a484249034401181082c0b01605100f00412416400600701962480e21081c00c401c409210704021840d041503c0e128062411400080c007691340c42c5512079445e090b001142c80d0a1010308d141a10f5040e801541802900c041c006140e480282c0030b45103ca1884100240c03c10307000c04040d010b0401c1d6615250541040104044d682580070110841e5145101040c40100c00180c281d5292080c500b1a40618900010220b81548112000603400034107425400d030499001400700412a101503644002080ea0740c034050345580900d11b4048801d030050a40c100c0400c817030019400c1000e0184c6041c0060b080d50baa039403c4400e0040010200e2110046001c11040d03030103201d00f4500e0020401848100746a90303403003920144001b00002d017025a00e2000c030b0180711100054940c03d41c00c010740c000a40c14503003806980d0350807d80c5010300080c10080720787c2c9550001402d0f64001c40034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 404871115 1250 404869865 404869901
    0x20c0406030b061c05030408010b100f0e151e09100f050d0b040f05090703140f150a02040b0c03031f0e2a0a03060f060c05060c0a0c02040903030f0609 66
    0x18850804c03a420710b2103000c0c001c030b69405a045401150707040c00140005c049400000480003a440c1c05d2112101030020a0024401510302d0b0a184079000b8440c1d6402c1d441c02c8174030042c802880200b18010b030180d220704245920f400350310b141900c201c00c0c0060a805c1c07070445000300401c0c00104112601000c45440100048081c04107201c000e9841d04580d4500c1c600802c00700c0c44945200c041c01c1190012204240168850b083c10002e22110031050101071130707000060000440e10113000c0e0740d10381c2a0b4001c20f40ca0300c80748000a80241031681541d015014400e01e0b9070f910340c104d0b0165035503900241ea05907103082d46801d028840a0f12a40c0e42d108072090000c04a0040c0d60b5510034840004404115994501c02c5040004d52041c580c4001c2040802035100052050300b066544404001550001c00a00080204420220728006681d40e0301020041c140c030b0745d9444501d4100c0315400c131000c0c003e4100741003083c2036080503095000805408610001000b1443c4d44503118410349030412400c41a4000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 404872365 1250 404871115 404871121
    0x21f0501060c2004090812090105010b07110a050910030b0a18060c090b0d0c0e0907020a0f03090308042d06090603090204290909032b0f0c03020901020c0406030b 71
    0x10701d030040e60501211441c01c010911804101040680d01007004c100d400600014031002100c0c056161f0b04e4021034800000c004960504062100034412103001400420a00c154a891507032199801000345c403000d0070028107400c1c92904110400c0d2280070071103100750101d00282003140b4511a0503c52075000c54101e5802c981c98880d00c0082180b011f2540c03c03c1409540443d01d502d03d00020300110402d4503000034a080d01503401018000b2100106200e40020703418800050343c0020344144d01508180c06080b0301c034803842d00342e8480d06103034001000744901140c006600031102450709592101c117081a040d2000601041c03043c0c2c100303405243c0100f04607800c140207480c4207601c01d454551000d40002003822200d020034040c0340105440380d82d1080310404000150800d03c1600303400200c420025801d20303070f25a1111400a81040c274030000107947d40616a0001c9c2d1941213514907500c1441d042080309420311000300a50701041a0391b0251251410f14052810305114500441b0303005500d03044203803 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 404873615 1250 404872365 404872373
    0xc0d020a2a090c020c0405160212030123010c050f1b010c020a15030e01150305070b0f09132903062d0a0603140619050402010503190e0d021f0501060c 66
    0x70901c0035001c2184103217200545203885910502c1d0141c2c1244042240210041100a213441c4a81440c001c00b41000d00c01004007a40d10b01510324111f22030043c80056414003c0103c4850507082400381c040d21807500f81030445800420000c0b403400070300c40c000c208000010015101c8014103e0000e400442c400000c008641034508640c00c40e2195180c04118404070304282c900b9502140e045c01e0856128407400c0041040811049000708030200e445c9081080400e401c8045008490102e802150341c1030f1100c002d01c80640c00703160702011159080c880400500008203c04448011542c020710030140442c3ca900d080c0000c0907001803240840403841c05520a00100e1b07014054882c1c0c401070b4403402c5c0800080c0c078986c00305100114040c01440c0c186801c4203011120300c03290000d1a49140340c00c0c144000350342d20004980d4041d0800c89107900814403212020000c00e8114002d0406000f640308845401c1da020a00c3c1032034203c002810301901401c0700001d0101c6500303215100118a41c0071400e0005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 404874865 1250 404873615 404873621
    0x306010c060f150320100f0309020301152301180512070e010e07031808090402180604090207031107050d03080c040b0f032e0b0706020c0d020a2a09 65
    0x5103220b040200e4003603003220102440c910244c00465441600076605c281070051421301224891040b2502c146240151001418162802503000c0805894042450554409400c0070f1000c48900900c0710055030346180915404d501c554002200004000c80f000c43c0b0340c0706608958000e1100500600214504800c020050351403603401d81e114000c40e90300080146904460074000c05141e1400540b515014030000c04072403050340522131580d050540c5e6404244013109a8203202015100107035102c4110400c080d04648440d445580f00e6800100482c0414803078000d00b9245129454a40b00070860f100703403503110101c0d800f41c203410420b4190b018020070700c108801c54000342205803052506440d11201903c07a07100070440108154004144002242c9030b000307140e00ca1000d10040030284109020f1221028a80d00c2100d40e02c03c0f02180350300070b1041a50444040541c400215020a041240e01035268050100e0030f40300e90b208403c0d06c41c4080010484003540c000c0c480a420b03402d13400d0460301c03802 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 404876115 1250 404874865 404874881
    0x2130209010909020a0306030b0906070f320a0e01050f070609080f030702010b01090b1309110c0a32030405010503100905040f050f07051c03020f1002120601050306010c06 75
    0x10058200d0000500318018802417240d00302d20754002c0f90040c00c5041880c8070000240030700342d0950200d000c1080465101c400003611106500e002090a8003c180700d200300301100d1171b00c03101d4500b41d41209c0300d02d01000c0010729104280303403510111480c0c103030010f650500601041d084c4a00d0100083c10005801d40c0c45084002d21410515081007000c1c1c0d00c02249800c00c40301c41016030740d20340460b4501c0da0454400c40040071f540c6240c510b0b10f4800300d6030301601211031042e90f8140b0384404440080c598170501359a0060b1f0039004a911100241c101440e511000c0419142000000e03440d03a613240400303520362009801e0070b4008500c4c0c14603110044905610052511014821050000c5000011401903c1c09507004600e01200c02c1401d0400361300380000820b61034001d5006440420068403682c11030100f0341400092441825014181030303017401801c0c900220740340900240142a20a640c0c054013840404605042d2a556076100541d0248801c2d121300e4003140890702034100007441500030b095 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 404877365 1250 404876115 404876117
    0x3390c0f060f2c0c060a051b031c021c020c03030103030e040f0c02030702090c161502040305030307050304060b0603010303050d09060b0a1401020606030c01082406180f0301090213020901 82
    0x2000f401e850519507690900c1401c20080d150310300e91040d66040200003200107032004071200c514041401c4406400c92251950003400c0d0290540d8000203000188242c98090510103000007110b0039400c0c40000950100b07590580403c00c50600003007200c0d00f4401d56130351000e084020340c6143d0a50b20705460881da01075840e54041d458100b0342030340b5040ca000c2c40c040415a0740046440e10024810443c42c000000c0000c41c00010501c5000041c44041200f01e2125800181071452172120360440401ba1103140c002034854407002042c00034041e8010000c510030f80c0a01c5040051070405030070060726200c21710024000030703000e0002c0c0d81a400c0c542e0060f20501d22030280019011442000b0540742e500035404511003910300801d100340b0703507018060f0350f0b40b00000700d0107001102c041c03d0010300030000140210030420f14151400c4609060035540a5071220000c00194454405811840e11449580c9420b8000d03c071004030b8000c80d0070140a61078000382d0080c480004484201c038024001d400c8404924 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 404878615 1250 404877365 404877371
    0x21031a24090402190e010c170d0e060103050c120a1109060112060e070e030f0604060203060a1706071707080103030509030c04050c120c1603080703390c0f060f 70
    0x74105640c1c510080103400c03940c600201c105650307680c0181c095a156410305040c00501d450510024080c0400b20003c1c090344441141c80d00e4480d80d0000003400100c001400f64480c070000441402000601c101d4000802c56402c13500d0050030404549602c0840b200502d01d00315020f031101d043c941345401c81d82c801c4040c0b5000240c960310003601c0e0156900c07507001359418003000c0244100e003640205070304080c1c0d0041d80101025041159181d564403030050003e410180d021000c110b0940d40d82c40c40000609402c11040d44c403002c3c3d0a010360700d80c0c0d020b0b2858808103400611500c0301002100c200f507c20301030b075294220b05030b107152001e4420307500002c0d5441e494042c110000520340c1d65803065602484100045036100d4075a84d2454420b841c4c06000001d0202080c010420b80d080010740c03000c0d02540c1843d114280c3c0d22450001da0240207054800d04000003810b03c01c007034501071001c008030300d801525004900d01c0d01c0920280c4503803224280285c02501c1c04002d10010800c01c0e0400481c99600784000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 404879865 1250 404878615 404878627
    0xb15010e130f110903070306020a090b040608070305100501020a0b07121e1d0613110901080a03090f15050309120307110c030c010804140a21031a24 65
    0x1550804000105071486955040742d5803421a280f1481140030408203d01d481c00101c036001aa03900b60728400104201d0300014440300903403185020400424480d40c44503240c80d11810050500310040703410000003031400000600c58030702d1051210403038206030060254020b0680312680445c4004001c0000d1010301c1c84900c446007028030899041008082c014245903c0004d2180155070102c0246406224403400950562070082030342a080390501c1c03594000f400b81807506900010f251110b15a010382082c0000a1040740825080d042c03500c42c1d610450f4040d180c0d0102d102e1700c00c0078003810b429191401c0b00e015105000c1d030000c40e0045c1e0010111014551280a2010150310032150640000c081407542e1140c0c070001c008140211408038041c1213a040300700d000802c904030050000d0442104441002d84560052291813030300350300701c81c40d1000c0844054804072045141da044200181c0f8022000d90002080045484116001024030f0041588901c2a05d912061920780c0d1030441c01c20000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 404881115 1250 404879865 404879869
    0x91503020a05040b30100e2503060906060519060905060a03060e0108030c1506010c2003120903100b0f040c090806070f09140a0e1003060203100e06030a0b15010e 71
    0x2440d000d02c505026000380706103d0000c0e21b041800c41c8071703460b90a07801c040040d0111007004c00c01c0150b0325004035601e45010400c000070081c03c5071503403010300010700e040350303802c203011480e00014243e540986112480305c205050f078a0b101110ba01c50031300007034038102041c0464034020000b4121250030f45004035000e03444085440c02c0c402c083e0302035000790384000741200303420728217008540c00c04944a0044a45280140001c1c1c000711803100f0003054841100304181407030001ea02d1040c168440a82292902d06241c0d94040d403941c070000d01c82d4828806e450810494501741d000700301100c07401600c500c1d90f8410160510001d010390b0400c0506220b1079900100c1c100008010251082d60940c0d565221405c4005000e020f500031900008124000c03100b050f2900d841d010703804401c90fa001c0b207503102203070303106101c50342c410301e558000801c624000070a00016882c5100038400b902c104034641601e54884000f0141e50300c8107540020a43d000980c00510a07a104001c940c54024043c1440020b031640540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 404882365 1250 404881115 404881159
    0xc030b0913050f1915020c0d0329211504060b0f15090108180a060f0c03050103170a1b0f030f090f0306240e01091503020a05040b 57
    0x10309010000c0207191450a0040400c4510b0058440780302400000c0020700e06000c41c801c2d1500c011740109048101024041322a034120f6218058140c00d45103880f089080042c0a01440d0001000704540c1e403076110034400200d14481c584003001013001c50a90030702e50001c100c4802c11a0040c800c0d000b0940b03455449081450351a01c42c5106210015000c80e86004001e117044000e03012900400c504000e698600d0490821030700020002d003885401540e4001401103c940042203013a468020903032203004000a40d002031046400051003841790704000307141101110b1003407202500340400c0890a4415010300c100611030102c540c604242c0a06240b4010040717400e84100898030007030100114800d060b844403e102811500e4a0511001c5190841c03107400c05500d400040e0005503a08030f0150085114861306c3e10100d40442d0004407030756224402917564009116001071079003040210031306001c0404178401502c2c2c0c02000c221049003802d09000050050940305034001084907640d06121000207 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 404883615 1250 404882365 404882371
    0x1506060801090e0a030e0112060816090614060a050a02030705070b120f040803060f04090506040303090b090307020616080d09050304291209160303170705070c06030c030b09 76
    0x5154201103500d4410014103c9501034840340e490b03004400c2002c0000d50114140404c00c009203048591580841130740d000510541c0d11100444c0300d075803000010a020030700400200c64090b20300700801a6600320303544182031f0041c4820b03801401003001020140c042d00150620040030700c11070707042c03030f01030f98940b4a40038682d08450003140001c2050f00d4116a401e17012540046c150075040a00e080c07540e40c0d8241404058200d0f8821142030003c814552940c0c1d10000b610741c8c00070111200c608007410040c0041c440d07040141c4240d000c6100045500100100710b805d00c41d8003425462038107140c403100364504203003094201c80740002004038180c0d007032b040d0250490b490f0251b400f55960322b2900045c21340040d0311041026003003201c580c14021454131081502c0001514041440c200e0f075030742c0481410b1014902c1403d9204d14411008000d06520001da00d52418261114140c607441300c80081c2c5042c0900c1200402840f00000c0a0181e10f00c681c00501c0304a44505002c502844c402d40041c3e4071170422 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 404884865 1250 404883615 404883617
    0xf0a29100302130b01020c010806180f0403090608070503060d08090d05070806011d0c030a020913050f010e010302030303041103070503030c010b19030206030a0c1419020f060c040e04150606 83
    0x80c8092080d49040102200c01202c1d1180030001030341d90900103516056804420703418010140700003401611005050740b10401107049a1a071403400c00c82105003074105440c00e40029200c2d843c0420814002c603a400d0041d9940d844940c2150f56074402c0201c10103003902c3c211800d034428050b0000e4cd460303842100001e94491005080c2d480c1c18003003e00c1c83c01c041640103460b00d54407030401d0541001100101508240b400e00d030690380f640c0300f41c4844007a00c10600220380060a50782c0001194005030310080c0280c0c0c5100f80040d051741d8441c006c140601d0b083c00082d41c142c104101040000c1c0345401d007000070400c041c0507907039110f80c0c03180080d05540000c0c0c05490315944413500c100032407610740e08007891040c00d50455411039056402040c45408010640140389549000384cc51442c02030045410780c980da00034080ea42d00c01c640858585540c004501005485038008509280c60082071041c0301d039840201c29414503160402d008400c4002030000c1e500d00401265180064000d400b07070b040a000070f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 404886115 1250 404884865 404884891
    0x2130f060c0201020d1409011103070c060801030b0901051b0d110d09061103010303170c0d02180102010506100f0c08130b03090f0313090b060c060f0601110f0a29 71
    0x1c50700000e400d00c0700c40c180a00c10008034008030807100e1101800d4a000103000e00e0000710403071060381610b20754418140c0c040c2c07007040c0c0c0d0040096200c0d03122100d681a03030f20600380b031002c549078151040d0985009680c1650f00d01c021007031420180110401400940342400f9010610006900c4407100aa01544000c2c0249444091000900510380508a00e0002c0c80d005d09140d5859500c000b004c0715940a2280c18101145c0089035602c1401020f442221110340c80c1196500d0700341542c0010380100b00500c6015509080011300680b40c02d03980c032701011a503626000c58030003000608450800042108840803c0103001d08240444050380080c0901245003429607241080d110f000c0c9000d50802c0360020590040000070f0003080340181c0742003101d40c42080412900004030004034940980c417030480051254100b0003000c2d005035040325014000a80324012800f112800194a5100c507030780c1c68000d9840b41e84110000340030078441036540082106501c0c05d091524008280000040d030f000540d48bd0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 404887365 1250 404886115 404886137
    0xf0e030d06240c0804080105150108010e060f040b0a0b0c0109021206090a170702040e0a060b04180b0703020702030a06060f050a031505040c0f0303050d06080f060a02130f06 76
    0x8450300c074041c06041c16a02d0686000000c1c0401c2c0d03940b040d030b9001e2008200a0340c0c03250003005500b8064070050302902c8000d018500e030241c1c011a14020200d081e0b4000340781d00000150020250780407900420b4080c18000280e420403007808003500508070055044000d100700000c43d02200301c00341603a84001300c00410004200d0041041c09031500c4081807858210200340302082d035001070407074400b0398000301e100481914020709144502421001940007414012544201340010440d1001c003486500204405120342090008481f070070f804004000e081040001c0200e45040c2940d5032185c180d180251501c28150302203030a0074010b48048980c50b0310f03070405228144c00210b001c8040c140076140002c02514544a03418112015001a000a071341e0318081402e003d6800c840310003802f480d058010406940f40390061140e4068900c1794412460510045110301c8003060030f80c14000081c00a110300e13200c0c55070305402076010121700c2230604415900090060300c10205103004002c0d503107d03044846 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 404888615 1250 404887365 404887387
    0x121b03060603010501320d0b070201151202091306020415112b020703020406080304050f0a0f1a040806101502060402010906050a090902040909030f0c02060304080702040f0e03 77
    0x2003400380038030b84a6410302c401486594103040c1140c5408480c00d080b0526040580ca4440102514070000d6030041c82000c0d000c428040d04900c19401040594001c01201046d492800304000c000d01980701c0d100b20100b458005440e001b03c0098101051000e200707c1060603039525000c90784141c1c08003502906801100d04400c0e040700d00415000e0f909130181c04094800340c42d0290005501f40c0c0c0a11040c010a40c00344050700c01c2110501840e8040c104010203034644015907a260403d107e06803055200440c04119424062000021102d19008420700c080c1040d900e20301c0311541c045540444041448005a01e1030108030003030145c240e41a04000f00c6040c044e10804100c0c05e088cd0006540c84101480f0041c0d03030000305601110414901951945150b0f1b40c111400e0f41c040e8000011140003050205607040305a12849084e0321030344444103c1540100d090703904103580d040c081c2d8400814000100819100350080c5442840203000041d0102d142c55840c0490740d01210450007540089055000c00c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 404889865 1250 404888615 404888623
    0x91112160f06170f0c03070c05060a06210512090d05030a030b0f0405040f0803090c040203160207080a1109040303021204030903020a0801060b03060d0606120515011d0411121b03 78
    0x103e000d0340343c0020900d40300c080c0c508000f402428041404100200250b03815201e85440300c103981d4040d055400504010080f8005060203004400310907604580e0a000a001d5800c0300401550003409000404000a17001210750898001260400180d50005c4001407003480180700400742c0e80c800191011800c018481021100c02666024601e0301d0b061001240c0c01c030f0740420784154402c0d441c56403a51035845180c18411203030308603500701d03002005000f0a100410307490080c0881540c22504801d0340e480003240c0d40d03401000701401641140324407040784d0074031014440c0d00c1800703410050710b0089007158500410030121800e40000346000300034002c514005848500410f200e05c000d101c00390425207403904da0b02c0068001c034800c2e241001c04070100803803500040000c1c581c0402c3c0101d21a281e04046031207040000300c10710004c141400105680d0501844d000d01c05a1400645a0f01d0380d4995840a144805034045980194840e101c20502c3c401007110349402c203c03001e2103c10042c0c8040034107280c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 404891115 1250 404889865 404889887
    0x9030a030b0906010c022b081e0304030f0305090703020909150601050421020d020307030507031401050f040305070c1502100f09020303031b0408030a030203090f01091112160f06 78
    0x200e14140418480d03d40c2e4844031400075a9012520078586d030741c0900c080340000d00b9001300145444500014407040c0710002c40544085e03030201d40d040150042240005540d407004585c0180450120305e04640c0d41446503014550000c541c0341110986526030700014041e860455a07407007543d010801d00c2585643c005451034001600f030070070781d06047c100240c1c4c0c44501e040c06e056810564038070b2250740a41d61514195180ca94000d0b080e2085951a402c1071502c401040c08152202000a101503040101c140708180c400c40028036688016200d035a070490b026800702d9401d9443c5484e8440200d01e000e901c0324110313000b0001d6002409003d10034405c000a03106440c950011140c44c2441c40e0307000d0b803404012260b002d4040c002c4a00881c1040b075806019000d6508034240c1c0d8840400d8103050550145e00850080c40240c0c110744005c0075809515081ea0358254004002445d240c280c289503042103000b810511600d9800e44a142c0b0501500103146d41c0389501000031220f20f800100003454004502c020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 404892365 1250 404891115 404891119
    0x60f02060103030906141e0702031b09070c02132d021c0b1c0501021213150b0a0305061f0e0c03071808010f060906090614060901031409030a030b 64
    0xd8940c0345460103091000244100c00034803c505441c059581045800c5402802e814183e0301810200030b10320110320713005410204e01a220324408a40b992403840701907206250000c0c0011015070310218212400c11a40717a003203070803500d20f94051842c6840d078001d1000d10b800c15510203500700301c48600b012899084010000a0034410030800c4040e8040c030700d40c402c010f08081000b080c0315074a100400c0d056244500d0558101000d4002c26040100640091180c1c001e8104008150b0303c60340462140c6083c22030000f000307000306021883c2007100c2a0050010900001d11800101b6525110241031440480701d0f0210f00c00b0900d41c1c485e207540100c0c40d50025000212043c0c1d0149402c2c1c0a0b10030310f2201801800a0001c4240000040307081c81e503904016041d42002400a030b51000946400343c10f00740501400d0608006010508800a1050704101c3e26000c894a0324030251905105455120b291464101501c55011192440c40a03104c3c0c1d0003416514000c1d5580c00d410720b8020201c41103944001c1c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 404893615 1250 404892365 404892373
    0x5060a060309020a090b0f10031b1e03091e03031d0a02090117011506050c070b03090705010804021201021b0c0a1212032d1505060313060b03120301060f02 68
    0x140160304e999050360261303001c40d030340021030311500c200190007004001032403903205040340020f42000d681a00321440040e100c01000038441054a010340d004031803a4040340f102414400c100b041d143c80381d0804a41c82d8011100c021400d01c40480001d011002c0d4181600070035160820690584081040c141a040540020b058003911070741c0013441519062045004030000c045280010910030345c000303402c88140020300803010b5520103001c0c1181d04944025005402540000200b040b0420704481c418403003600645501c50406d401550769040252050780c03c82c200450340501c4510920040405000000080000001e104182850300f160300401c81e0158101000c104021484a17000219266100e000c000907186160130490040c42445400c0541d50484040c0992840d495401d0b0091000389240a111044144100403400c941d0361041c1074000104000240c00e200804803074020b0f80b40708140106140d0f0101001900c0d100e107120803100071a000000400c0b0180d007183d0600481c19580c0050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 404894865 1250 404893615 404893631
    0xa030519020c010212100f0e182b030c080a09060b0904060b0a0f050f040f0b030615040608010501080c010e03240a0b03060411060d14010b040f060801031110030603020603090105060a0603 82
    0x40e11f06010034031543c40605000d6002c0351205e00b040c0c64842c000c00130803080f00c0e4584d4403103001907a02c20361550243c030f540c0c0c10301d103402c54260300c070b801014a90403103a1108500c07900c1d012020001040d8002003900c12560b01e20212150755940e1940ca030041e0f00030140460492003000030412100820390151001d090900300c1081107403076542204605035421140003640164400c404c801814410802580c1030056070100aa66800228500e400c0c03441924100002c540720142c05080398400e004424041d070040101400d5907204a4421038448000307070540f4141c0b1120710004a061200405ea07441c0311034000300b0072420030394901c0756500c4200f0440c014405401c080e1911076280c2c45084565009a00000703a400485540350050382041140b142c54074810341e51420f002c4125080b40c0507040c10494010340010312207118460280c11789070012401c1c3c1c00c03a040902040070015801d00703400e090640b19480007026945610165116402c284000720351450454100700701d004a0303401880501d40b5100300c1d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 404896115 1250 404894865 404894879
    0xb03010905061c060c0903020d05010e06060d05060411120d020f0d03051303080406060b1206130e0616170108030c0d02011a04050405030d0c1815050a030519020c01021210 75
    0x10b038000f2607411480008035030400000c00c0300c080046410282d08240e80040081c2044415848a28030200040a0b0346c0240c4800c0d04024510b8010480548180d01c10408203000c150080e0424551401c018030b48213008030342245c4507003072842c09038000c80543c001040b40c01011500344a040b000b060f40e0710f0200300038500313110100300240c1c00600190400104800080400040d80d0007040981a9902013507240c444040781c801480340110303404c42c000c42070408908002e2075640a03c0d00305481d07000c09400f043e554484841e4104900e0341c400001c004410b0021152500040c0c140c902900c5010091343e503908945500c10300c1c00002300400c0c411a8507003180b240140d000d2140c0580c002000312b402150540343c50074210702d14014858440c6e00d881c0344c00e01e20980b00d074000143c25100442283d00420b0240d0368501c203000d5001070a10000030034401c104002036107219510855128100c800c1031060012820b051303c080341c00c030680301c14071a03500256051540d20b00441c1150b00c2102d60b190300d0355a80c140343d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 404897365 1250 404896115 404896159
    0x3031202072f0415030318080a0f110d0804030203010c0905100f02150a060f0b0a1b03180e01090e0f071707090905010c0806010503060d1e08040b0301090506 69
    0x11441e0341400800e000c0d5440c0c09850b11404140d00e0024000e000e014080e000c079907082c440300c1c401140421880101032441c115511108021a04008090020303070059442c0c01d91140c080f14400c03524442c4110354200c0316a40c00f2001100180510742d0503440b213003148141801c5030f6000510900340910120200724070b607a0229419000b080b24945408400e46a48061b071600c1112030b040c0901000c40d004010203820b21340e008404032184103c2d80d50b81503a85400104540c410b41c42c80c840024645440d0003c821815451075038030741d11030301e440b00340da52800c21849000c80b00c6030031600d103d40745c00004012080e0355014200d040c00101001d060143e1044003129955015882009503010b5004c11031200000280b050380020003c110f014448045540307042c5008010049101001c11074480108040d54860800c1d2485403030090035010514485403142002059200304062145081d04484400190148003130001802024417664803541020540c00030781d00c004203403601421801802c942c011985c01d07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 404898615 1250 404897365 404897393
    0x2e050706050a0e0c130207050708030904110304051207110306160801051e240a11071505160c051009050301060510021213030204060e0604050705090f01051606050702070303120207 79
    0xc4010b07080e2174076600540064050482e003c3c0141c015000001180c04012005048100044908010f0280c400c0e401301c5c218002514060b00750790202480c4000d041e40500200603840c0503e001401c07405004000914043c403c680c02c51140942481c1d840715940c00c049041e000d801b04035000d030340709103000706c40390b108001038414144a140e040d400c0c912884001500d58030400c11050741d9070f42d1905113080251100f00034490220003071040e100000790700350781c800005c1c04044203907544914101c41e11550f83c1001030003840540361010300d0700340012180c1e2441007031021881d264941c144aa440e003c10503003101e549501c181d01401c8204150b0100d40d901080c80081840084660f580f980141ca460040d642c2c0c2c80d800080d00285400e0010079104150078840d44611000c5400313120680c3d50f01800c42d454010000710b240c2140716007003170b40819801840a8444d0290381e00b5007180d44035084c0c907501c041c0c1c0d1081c2d5084000da0441801402415441480d4144a40d2003a40540c502092692202c1c0440700340 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 404899865 1250 404898615 404898619
    0xd080f15040b060904060605070312270309050a120b0901021206010c0302150a090b070e0a051201090c0e04032307032006070201050718050607022e050706050a0e0c 72
    0xb840d4281c05940e0724000d880480d0300c0500708111903a10703601c0c00313001613101080a4021500110800064500b54004e07c0d8948045035170700582e803610410303454081c0520142c01c40510044290108450321000b041c00c0062810b2802d490401d1810b00306540303e018003400a460503401000040c0f070a02140f108075401000a1920f080f840b4818241241868152060106080c0301e03003040c4184c140701901702c2c0301c4990194081607860780300c105081d607170700191122a036000f0500f100c042005c1d1030300c81c0c0b0010401c11090008103126170203680e0a1740880c8250000d06020300e036030080c0001d05610207a03550490b1040d4117001807440341c55506907581d0081c80310090030071801003116400b0380c2e50240d09180220300e540407511142080b0f04064040e040407031b408070001c0c5010402c14111207542144070300f16a00501101d02e4817600d9002c3c030607042c40324104580480621105048000d107d84080d052004150f45d4140e1500058a020b0068640c045c20a1142a06000665802540105100007440c00c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 404901115 1250 404899865 404899871
    0x515070906171b0d02040b1308060f0403030f0e0a060c0f09030c05090406020d02070309090b1008180106030f060506010207140f091b12060907020106030510090305040f080d080f1504 80
    0x88401c81e0f15503100780348000e640c2900115002941c5c1184c06c0180010074200c3c0c09020301203880d018600e603580e008840702407400340000c002c90017080c0a640100010040c4010200d04104074031219490500300d404201c80d1240e48440c0c0c46e0f000740e800056010038202d01c1c03409403200342c40d54440444120090055920070a0180d020804105c00c1e41d04a41c0b1a01e80450190f454410394180035000154903c11144060b09044d0802c4240c500080985810030454072124465103e0514140c00e10401e040c04824039980d42c0000300114141040c0006110310800011a0514200c800242448126800304010b00061141603070250b981d151031886041d42a02d0031140b9640c0d41c490b0240032180110307041144031000800032a50010201d0f260701c2500e0503282c5048903100c00030308034201d0f0704138807002d040c0ba004246954600f191a401003030303001d070081c82c14038101038440040c810203882c640e20518a130362107054210f070041e4121404c603034030040043e004640c1c1e01d4008071a020101d0340c0c0c82c0051007155 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 404902365 1250 404901115 404901151
    0x60f04080f04120b040606090e10090204150b031023010c0c0f080c18070915140d020c0f0703080904021b07080a02011b11060c0109051507090617 64
    0x201e80c2040c0d500600f59441c985200b54124206081c60030b109440940c0d101d81402408940c440d06802062000381c0c031000280544401d0341981c030001c1080841c1280d0242c1c0314040100c4020781103803a007001e4102c02c0c43c1555641071062003040416880c1e8130520102e8000d6a00070408138a81920314442d003001c5c20120510b1016183c4240c44100940001d014042c0001d8086000c0307500040403410380c503054440344a1055400200d45403808200e84080c000307000c6c448280f042c1d4102184511490001d0b0070030b56640300d90180c0e4501c0c6034106e0032004182c40e0740481c100200c20010014501e050081070090701e0002d00390381701e00d10944a01d135030503405030340c0004918180b07404126200081582c2131069911141c3c441301030f00e85401d03e0600690008945881d03032440c6121044441c01c40039444566a40e4501d000403e0200e990801d1080f5240703556210031120110b03500340b002d1140c50f8035030b1500f84860300d0580406008044190441c1c03042255801d800342c80c61081200850b088141000802c800c8a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 404903615 1250 404902365 404902387
    0x7060c060e01050702010c02010e03120a0b2e140910030209190305030901141c1e0f0c12150b090d020a030501020702150903100e190302070512060f0408 67
    0x1007a540016a072640c603140800c0310040e4191710507510307000301b81d00900c00c1c0110608826540d014030340d0030043c9607000c00f004c83c0c41120a40d10a54640350060810740c038500504c811603001c01d00e03c10f4810302401c610111045495880860351643c0606409454100804400441d110002e00607520b814940c5c0000d140646982f0301c2080038004454105a0400549910b82070791a60040724807540803809402440c201480e01c47e043d01d06c1c0025401d441117500d886204c03880c01400002055081051006c182c000c00081140185840440350000c045201220480010702802049140d821110710786581074459140b8501c158003211400c40c2c2143e01c07100c83c1400034644141d01c460080d0f20000103540042008019009028064000c8036a1503a075040b0410781c80e2284940b004c0603a15400c51010801d00307035401e40c4196003d182100c100d42079484419106042c41010400c00e6000d41d128030801c0109107030000b010604c1411a1001e429141002c5602e80306000c0c000e000200040004074150000c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 404904865 1250 404903615 404903621
    0x1a0603151e09120f070b01050d0201120c090f0b070308090d020a060e030f190f050403020913030e0301020d06090b030c0306070c05030721031b0210020f12010605030603150907060c06 80
    0x110080c3c2e010f89544032070440f46100c00d580039007030071514030b00400b000003018074000202c170f4200c64042c0c580c10721816482503088000c18090803003c041c00301131200464685a400b07030a00213440c2ea503002c2940c07000d81c0d00b400f80000500600210a41c0d01050740099110340c089070b00c041c2103600c17500c041902800c900c282825401815400c01c00c402d0003142c0c480814484011070b031001c5040d134030b40c00802c2c070134803404a070907104a00004e904201110041000c641e00c5043e6501054000d14011108560703400c006826a44240d134001076158440a084c0621200e078807411038610011002043c0030354400000c6522040010b11080520008005082c01e10406208440d03120341d0042201211006a004000403943c100303c6407000a85408043c140d103040c0d0300001003025080c0d800030518004c03400580e0004c0d61008141405a140900c0b228440d4040d40315202d010380b13a203450782601c0742f800e8030506180c0040500d080b0300181d483c405101d0025000300303141c029035a4a142001e0090864245840030f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 404906115 1250 404904865 404904883
    0xe181603150c092c10030302120f09040f0e010c170c030403170f010e070216050f0d05010612030311120406020703110a0f14030c03041701091a0603151e09 68
    0x19a99800202c1c0c85070840600300310640185040d144e070056151108000014519400001d015030300c0b00d140301c0051100103010707000d068943c01001e40313045480c50108044d03640081025502c180c03180e0b50305607851020300528403103074940d1810301003800c03024202c80200d5030040d00074010b001c5e000010805152040c005406488070312216035255050000c40300790120001d21502c42e03855662000b2491062010801c11000c903116040c4080d414142002c025014a1414400c1e61041d405480000001c1003809201c004041180503110344030b00340d0070042d003510b001c181504002e49007000644d060120754212650016004030005845020074581a5041038184c0b140e0411440381c5110700302000444450380e40007500c5280c24041c440e41d074048180d0350703001d800c040b001a5041030200b03001c03001810722810300904894001099034461600d9001c282c181100d0034a814620a82c200825800c04001d0710b205210103022801440c80e00d54603c440100d01252240f10300703a55040401e2291404001c0404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 404907365 1250 404906115 404906129
    0x102011413020906010f020309090c04080703081806041203120212040809030f06060d03110709020f0a020f06010b0a0c020316150809010c0807080a02040e181603150c09 74
    0x841d0a100408400c05192020100d10a84581d0005000c55101ea04c80007140c2403650000d50510341a83d00f04040400000d00b40000418140700000d41090200301010045000300d5041e41d0780c1d44a04d18420752200c000c10524002c281c1044100400701e40796120703c001503090f10301441d08454842d41d44010f4460307140c01c0c100c00700d022802c1c4814031400074000d02003031304d040b411280703440000d001050b00c50394110390050f8400c483d1042e40007c00e004824604aa001c00d030281e40155485c0d03000301e000ca8124210401c140d00300404c0070001349804011542da82c008500081c00d1035850a4110140d502c584840141004940a9020110740b41000001c0802440030003043c80103840c1c0aa007080748010040390800121014081030b141203062082e44e24406180d65001c0311941e62103070545400708043c046d621065400c110001d251072100010390b02420b07001e111102e50340e214019a9242060320b11618480c80540340d42000090030207250405022040d0f0000720303040059060603516001a90301c404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 404908615 1250 404907365 404907401
    0xc030c010c0809010f09020609060d09062d050103150c030b0307060513120507031235090303160e0a09021c05090312041509080d14070f1b02010201 65
    0x4407005030401c070154450140e20000300680c09905001741e0540d10040c0020707400410802c4844241d0404c400106a031020000d400b0440d2007195030b030881114a0030400259110100361155220b80f4a245004103651005d0401d0109505544994001080705900000e10540d030300c00302da5a180c040e410203102d04100606561044bd602d840152040e0f02036403004290480a403000f00b032503089001111141c54100004142085c296550307103c0407402d0108050070300440c1500403034000020880391010f0b0381501040c0c1c059840c1c081c806010410301601e400c241d500148104141026440e25941189005161012403c00501c0200c1c01840359134100c140c420380009039a8031103800b61444800b0506220300100400d685421020307459003e201c001e40941d04012010030003040d0340c903e40450083c81000001561011541ca1504030392011142c1c130040707a1580b10301c0414402201e00e0071790054040c00c0994201002e094001c0040c000001112241c0303c107031000c1d50959100754003600104c1c092140300c1e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 404909865 1250 404908615 404908631
    0x70815010e0f0d030f0f0c0b1f1802190903030e0f12010e07030203100c30091416080c12070e090313060f0503060d02010c021f021501050105040b0c030c01 68
    0x2090040011416004104d00c014206e111034803a241c1c3d0801d040e00180114659220841e02c0c8100c00c2d10101a01743c011440880411706007e41818103d05c04656400183c0d01c1c030301101c2c8500c00d006410301c800180401c00b581000840c0d04050035402c00b0200f203c084542d02d2000000034107401034208082015071034415608948500007070840b040d240200e0071103e43c4080540c1610542d80c01d05880382c0051070f03418003a24040404021507004140018036020b240c003e070702c021011190011826189002c17018540140f5250a205180791107001031500100503050400083da104503210207940900c0000001210001003400200d0282c003000e0030500785402d040c1102503a0750480340c09107441c104c10100000d0340a01801c80b054040390b2070b850b040d040d0742c0c0741c1d000c100c400b058400050f414080381410044c0180c0e150780d020002902c400d6100c07207440c210704070004d10f030100140000075000d0740000180002c5c3c0c3c000c41554211500b40d61520ba68080b13194541d42180502e000e494995800c000354 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 404911115 1250 404909865 404909867
    0x150703020a210e0405070e09040303061505030403120b010516050705100203130b120114030109020a180609050f0f07020a08070507030b06011803030302090a051302030f070815010e0f0d03 82
    0xe81c042d4441d555a4490b0310b61154100000c8640540d16000801d60300315000728a0304080f00c0c090ba0040c000d040018034a03503a0b0843c5034040b85055801c1000034400070800003055004521042000d005500c01c0281150301c1002038a64803480e14118150800d1250180421004010352400740c03034041c050550301984038030080c1d5282c2014041c0c81c010891083c0101d40150fa20702510007000000d403070700030180d103844410721360b401c1e10b01e056a8040d500c03a001d40c00562500c40e00f0b2030040907000c0281e1a03100c0240e1104c03086900d160403500d1003e08100900000d041840402138100c1983c0620524079219550281e00d0080c5030f8000802d40c0c50003060a13414860080380000c1101c4c02420b680c0500c0d520b07000112031403540c1d880b10745440910100305002003842503014003082517018000c0c0d00039507101c41c0081c1c6180e085c01c18240f034054000040003030b80380109108a40040450501001c41d05090407006080c0010740350140c1000003000c525011a91001102c120b21f0740c01401c0318001351290f00b8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 404912365 1250 404911115 404911163
    0x309180b1503070e03030304170307030207080a080103020a060207230a080a0807020109090b1309061e091208041a15130b09010608060612091e03180f150703020a 71
    0x4a500100b6609444c18183e0309000c4200c0b40301c2c2d58450000c0540c42d42d02c50000c40c1c280c001401403420960700303100d41000503003900e0003400c01311116121081150b01d540304000b101d0005401007000c43d0400c1d10100a0002c442504008e030300000303000c2d071070f4031a04040881d601441d04d80c041c2d50188202e10b2003005000500009044040c001c3c0d94800030151562410b10556590861168003c41d0380d0340c0106201880d541b01c13001e458410607020446160b862031100e0b0702c4110740049032480c0c1d0391300c1e4001e04012030510181540300d1141468046854540c41d01401d041980c0702201c0780b0a00c038800543ca2445480340f02055100c014508403d01c440200300d01c0042440c0c07980680a45200380c000b15006000e1585144200da005190740c2c41d12303107482c4800f0310001002d003032440580700381007003415640c0c98996540000c945540045890306c51461040d0500f103003d0f14418050032342d03a0391440264860144955940c1403104206998007840c0c98228540001d040340a45601c40e01ca10000c2c48015640c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 404913615 1250 404912365 404912371
    0x5010503060d05191103030310050405091e07081b0a0303050d02070f080c1501030503030a0b010e092a0c07030209191103072c01110f0303040516120309180b1503 71
    0x40c04c83c40c0218119046c0b50f03a1b484182c83c440e0050001441c01c002502d059000140c1c4007041c10306440c510040400c07042180b040b611940303440c44d040000144a1004100121005401c0b036034144003581c09400046503180d0000e0001404000c0009030312400d801c102d40489844d1640f0500100442d909420700788110381101c44403c10f540110050102403ca081400905030390f00304014501c0c42e1640c1c1d41c05001000c1c1514054140314240501c2100d035648d0720755252107800d900f46050803200c04003e54182600c07200c801040100c0f024011200d0031040000c1035800e0341e60684000c9030036281c10000303418546da032802c1e0403c8141001019100074803840040d40c016101038440e031a548178100100c02c036020b629030f81c4604044403050415a01e43c41600c140a520b030784041901d41100520001c02c1c10755000f294184c41d264800400900e002034038020200c01081c1501c82c0d024000702554000304600e270380c1c1c81400d00008050558205d510010b134414250f1880080007108405000070702d17500c00341c100b1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 404914865 1250 404913615 404913623
    0x305030403090b39100b19080c0a0501080702070306090311010c0e0103050108120708180303030705090a0617040b0702010e0102160c0f0b0d021602040204090e2505010503060d0519 79
    0x143c488454541004c40804400500d07074406803042280740748050700100003e0306820350250100c0303541c1845000760320545000d03140341d0000c0c0420303c0c1c1400030f101c544035a60f031240c1c2c104005c1604005400c0e40c0441d02005070796000001040150a5043c00c80d42c0201c40d1903494115480d040003410b509402c5070903030903c00e40a8030284800d03a1b803612801c0d06d07400c0c60304005070162000c00a510020f80010010420302c1c2007071005050140c068004603145030022a40307070010820003d100440d600c0c0c880c2d00500144214500182010007145040300200b20151000740080d4070b120104807a80e000b9042111000c050340d00031511b0302a001012000e4031003110060f941912624000f0405220510459090b112030300304081c5440200481c44000358810400110407494030601180143d0366400140000d01000d6800b0413a04e0044101c241040c02040e0b01d06040c21540004030701c005052000303681100c1c42400c11546a5940c030010411000032714100400d070b8000e620340c00329030a940b180e0700103032180a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 404916115 1250 404914865 404914927
    0x9060b03071121070206040b130305010b0904110112060519030b0105040b0607150b04090c03020112050702060a09110307092004080316080705010c030e150103020d0305030403090b 79
    0x20a501c080d255080d60a0720754030382c0f40c201c0750510410a40c500900005201404403841d0a6844208602d142c01c41140505080300d950402c200f070207000d00034041c00300c10807641542c190410740d60b130704091030343c0741452810f102c8c00c1030702e040849002e41d00c14402080060a51816182c50304c180344034540c07490004480004603e000415541401d00c10410004800f401a0b840c0c841c51380c90302c8100c0c45801e15000e042c1c0351210490f07100c0e40c41c1c50040010451284210a02e5642075200140403081c0d00c0103045000c40c502020020030640c0003e1240d0003a000d8900080c150425050903200d0816014600d42c041c429003c0c00a5200d00507440314207400076255041c00100003c50150340144034038482c104840c4d006100c2081d100340e0b40d00060803800c2c410a40746141650596509080d40c4c600f002c80300110ba91884403071380300030f01840100c0005e582200c1384402c07036042d0703400541c00400c07040b009400c020010001408160060400034042c1000384251600c0f42001551140c1205d007600e14030b014160 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 404917365 1250 404916115 404916137
    0x40219110d08090c120709090302070617100506130902131e08100203060a031a040c06170a02070219030506041104020a080a1e1a04060b030402031c030609060b0307 72
    0xb1148500c0e0f03020ba08000003411240f8000700c1081045038001c2d010300900c0c01092000100c42c082841369407100b500caa000b4183d200d1420502030590550700303a0040c00b00380003000f00411003124442400541d101203c0070750700ea000030019050010042e401541d14148009a17841c000c1c481200c3d85001c480d45615040a01006044803a0300b00850b4414400c940d4495500040107080a801661340614040d0010100503070b6615503608002d41101e1002c01c0c40e4003042031000b8880c1c005910000b0b00310a040c2580030120081000c1e0700c0100081c454003029a0204842c0300f199503c50580c524a440c00c14505406078072402d02ca6200d010075281140c45c0580b07224042c2d41414076000340c036802884c64645803025600c001604000d46141e00307040750607500d8a500039000c01c015100b10500141c4c8509000007805000f0107010445003950001000c4240c00e01c00c110041e80c00261262440740189603070380008445020a41c00392000b134010303080d5282881400311b0428901c40103144034155503a81c80d2040d00d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 404918615 1250 404917365 404917367
    0xc0d110d0614090a1208090c10170c0c0a0f080403020a15021b10030504020a03050105011508090712200a06030f0525050a1101020a0903021801060518040219110d 71
    0x14a00241c01000c00c01e400d170008041e40d01491289500075001e5090364400400c0c0340c0000c0480b03002001500c0030401c00c009108055007417440a0394440d8046154070700c0c00c20341080d00b603030721660b8460040504016a400c40200884403058500555014202072061502d07010011045074100d0b15120040c400e01100d031003030656641c495169410301178210600f0750000001200500360080040e070b003114403241c0010012704244a458002e01c405001040000d8260030000c02c1e41c000a0700e00c25896100180501800901e040300c10b14065100c101203041c40610580c80d8445101e905c6e0899014210800000d003c0d41c058108503c8000090010440e039030750340003000713400007018104a402c0c1941004001c0c2640c000c1c401410718040c1c508204012004030701e07000d0300f07a901c40c500c1840040c2203000c0030011400c02240c400010078056049141a604080300200280103542c1e81e189036500c1d00b05801d1680e01c2c1c170740c1140c1008807145202c3d03104170007400010f0300074040c00310205010310030103031214141 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 404919865 1250 404918615 404918623
    0x3030c010605090a0c0903150e060c0c070b0304150209010c05100903030606320c070305070302010e0d12050702010c0203011b080907061b0302010b1c1703090c0d110d061409 76
    0x26186030300c4128065045894492101d11000c000d802d0f0700ea6103600c3c0a0030240c040210307520400000c2d031800c2d60cc0401c8203d490500c11180d001c104c40e56428070500002410161700e000d48903800100c0180c03500a03240040301c6c000e00c9220094024020306030741c001c03880709079000010701c01d01030b40742805500c0d42c61400b02c50351442c801d2600610100004070083d000b085842038a5184403020110381402080c0660303c0c1405a9980102c1e03040c0e0180c00300308115600080c0d0b4600814040303c6600e44c3c0860f40c2c4403c64020560811318080010004c1c0c0d05045a0080200c800300e150041d008000038540780c15000344403030f6896010340106185e100000d03032450380019841c1c1556401e03912120342c00150705d00800481755801c022411741d501c0d0180d42c07544e07496003655240520320b24540d0209000c031508144d0b542514800c84604040c0b0100204881c4a500003841a0214000d46e0201d1003e0400e08020b60001009418160302042c070000c440280102600a80407100607084d00b45080c0c0c075000d0b0802c1d81d03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 404921115 1250 404919865 404919881
    0x1f05040c0b0f1c0209060c0102090a0e16080702070e040302060604150b09040207080d1107110409030e060c07080d0f020f0c010206010506220b120703050910110903030c010605090a 79
    0x1c03400100403429602c00d9210714180f0a0500c60000b43c18001c48100150140e044002100da0603940801d00800910706402c00b2030003421800c0d0508224140029041e9110a18140b45014000000c2c04200228420403480d0000c0184801d510514105450025100c01d426100c192040781010045010b102e0a410404202c5074000802c4c0d1400001c0418840079400024041d00e240e5828400109181414013504041c107620b0101c565652895107048603440c81d091a20a0240303240075800e00000e9002040608081c0040760216140c24074502d2141c5082c1c1c4035000107441c1e004100312444503513080038510460080075026107101030b10810545665a07070480340e050043c1c0c0950010082410701c200100822441108107107007820b40320104c503080200d5035000302c0c410500018000510100040c445800440500d0148031038105050f203280d40383c541045081d452940d88901028440301101100c054200107000d4980b503900180d2035500030812403044501a40500000800010041c0710b40d501e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 404922365 1250 404921115 404921137
    0x10e0708060603011a0c0d0206040b0c18010302070807050706261e040503040f080a0605130f03050d02070c030b040b0106020712060b0402041e080f0a0506060f031f05040c0b 76
    0x100f56840c000f80c070700200c2040d54180100070b40030049149600c40a21a0000c1a811900100301c2d600b464540145528070081440c1c803404001c0c405455000758101e42840010b80900c0c0250315180703542004032280c450080002e0084c4141d83c000107a41c7d40110030900c810001ca0207500000740030ba542400468000c41d110f0882a40d6001c0c1030045810208146820900410480742072586a644401500e19290000d082c186e101c4550f0504220706801100e40c40700390103501362007035007823644c0f04006503201d004000c0c01d02c08089081d244001c01c981c140c4403030a40182d1400c1c1303e669241840816a903045e2815070707000d0050400414194000207400b012918050034802d86e0400c180c8590004041d0700c80365980c4941c00700301c00281a1092001c0e07010404c02c480318000c4061030002d01a20b001c41c01c406550340c54000211460220300c000c180180d0101c07064403594100903413040024205100303890005418040c00201c074405029603400188a03a11603508600070b2500c5210031078150185440c461 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 404923615 1250 404922365 404922367
    0x91806031c020c0d0f0b0906100b04080a020904020112020f180a231f081006090b1b0a02031203150321071b08010f0501092f0c15010e07080606 63
    0x12407070138486030003000703140541c0325035541050540c1c405040d14829642c40040780c0c4103a007881100703200048980001c1009030122807509183c80380341a101e010154010703200d000c03c0c0000a00356401076410005020b0a100115a20054440e04002c1500074102d210f1112050b2250400241011400002921880350418548010340c40e9040868801c09280c15004028004204901c0c910b80030300780741d01c94141d1a48101840d086a0381424010190310000801c4400303002081894007540c12540d040021000010a48601c40c05051a005c10701100039090301c90002803101c0c0600c0f1001850261000c020800144d01d6141c1c00c15a0b22000f007c151008504110760308241007103844010248284542490302d000000c0203a50049803000d6480781c480c0303035128549008101b0742e0344540c60141908031000c119498010401e6608031107504a100201c450188090192600c00300039107407440445011511445e55001000141c0070003032103103840724040d05021a00b410300851038548a17010140400f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 404924865 1250 404923615 404923633
    0x5120421051203070c030206060a0f3507030c0b0f0412050c030f030306040c030203190207150908070c051c082a010c110a081e091806031c02 62
    0x4118a00004400c90700c5114925048103400d05800c055071140301030751102c126404c40c6040280c2412070003000d091252060072418814103289001714825070758402032552141d1a804102014500b14440034034241310120381c0c4036244040081c0c0340c010b0320f2180c0000c06a09a882d0682e8209004803401f4022519041c0002e011034801c2c1d07145081d40300d01034012219003140303900110742803820b00c16a00c2000d80001041060034109405121080700c890310f401c51652500008841c10113070010041d080081d000100321040c030601c00480007208002d003008001191580c6090112a840004102c41c64020000001003524245c0703040c548a11980501d000149115910b1801c40d038020036500d400040b44003100a800b250005900180304140d20002400e1028030401070309c0c62501200c0e0072801d41c0700d0740401000500801c2038400b000c09400d00c00c4060380220600d030703000e405410f8105801ca075611104480344401800e00394003c1d0020f0302a145c20464459285807a80212510040541e01c03240038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 404926115 1250 404924865 404924909
    0x30c05060a05070b07020604030f09050306040210171311060c150402190305010207020405010510021011360603130f060b0d0308070e101d0102010e0f010207051204 72
    0x1082824924a885890030f88680d4502400351000c2d10301e10016400081084201900800c90300342403982c1c1c0c1412007240b841d00d0006903980c48003e0000b800784103480c0382c460801c1e01507030030001c600d907007998100020715200481001e00004444103031100e007114409255a81066001c440d454a0007501800c0e0b0b05080816610a015000d4004c9800801401d603251600d40c1d1500d01501440c801d900142e0703a00c0e01c500400050300c0c01a08054030030720400305180b001e00d4001503041c6034100300c610040744156004d0340c04120340c0990032001038952120000e069640006110b084110260501d02d800c1d0381016901748261070204640300580034a028801c0e90100303a200899000e088c0c40f400c000716420b180003004c20260000310500300c01141860f01401840e41d04644a800003050a9900030403a44800d90010700c02694468170b8080110325405090240c3d1007034100d00341580a12044812100400703010314000d40c0f003e0f000740e9180c00344107842510000e10400310b80807a9070600010b900400701040c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 404927365 1250 404926115 404926117
    0x110c012a030c120e0c03070807032627090114010807090f140307050a030b0f0702010203041106091908070617010506040504240b0a26070318080408010605120304030c0506 75
    0x5004c039042c2c424980301700c59030794080010002800071784000d03050082c610300e840d00501c0d90a80d86501030b503521034107540741080500d0980304101d2801c40071880007444c22a024240c1c41840b8200c50304966014000301d00c4098015100b03041140030ba031192881e903140681110040e049001381550081c802c181040300c0149180c844040c0280141543c04060b5140005031840e02150b00031150b15000004102a40584009141d0b01002c240000c0d440c5180640c0c8220070401807079802071041001091000c459256040076601f02d0103040c0da00e03425540c803003c001d56602264400d000000701c42c0594142c00701c0c0c551003c0d0303040342d4010b480300d81400d062108000150122810034256035229282c00309030000d409001d50014440d0013245641d80d5220300000b80b03110030a00c161541c64100143d452114075232081d2550307001e03819150000360003030045404c01c00780c2c1009601401c20b0720017207004200c807803040d489070f0122041210200140c1600041182c4c0ba0302540c0703c050038603081004200f0550600704 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 404928615 1250 404927365 404927381
    0x9060103061e080118240f0207030e040513320a08070512040e0a05040804080a03170610090303030f061203110c040e030a03110c012a030c12 62
    0x41004900c080e1a81c03000184041c00c4040c8501a0400d07503030800210f0020310601c41801c00c410041c003204401c0392690f54a00d216140d1101080d0615041141c1c00c0c0d0256100481400e0186070940d03440c8480e0600034055002103045500c224030b0140482d01d00d0a030b45030346420065109012402514840c0382a50040c00b500450030312142500520301c4000806102a40e00b103071058000d103840f0680d0741802d520b8150307040d0f80f12458007401c01c01482038040003044540d110803000400f24a0380d4891030440f0b498040d0b507101c2c20305841307101180003c064001c1c19080d1040745500410300d03d0740d2080d0401030300d080c1d0340e811030b03004c81c1e407281082c4040707446904000b441e10b40003000860f0381992000c0c00d150a0300801001c1e00010040b6210302d41a420502070102e481c1005c807404c0c0203418620b080592684034059a141c285039440042101580c003100988058441c124000c0000c0c1e50424070119041d070403c0e40c6450b102e403408440390440b038002e114106801989650365540301a021104030001e00c1c101d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 404929865 1250 404928615 404928617
    0xa0602070213050103080a1e0c080903010906020a0c15181509050303071d0a0b0a0e1306031b080d170c0c070305100606030b090c1b100218010e030c090601 68
    0xc1c0ca002e0309141c40703802114021442040c020b50b880002810003800b05500000d4070703c0da691030902c1b440450f40c2c040004e0580c1c40d00400000c0c0d80d81c16903000030380100f20300d5000030107090000c031b10b010303040c0d4210303400c43c01e203600445054001c1922180032001700d42c0c03c140d10403605e240024a640100d00750381ca01007048416810700044060039600c0f51031460b00102c7c0c00e100091101e8000380c010809504c1903000c0c0d5503080e90081402030034084015114021030b2211810020382c041c85103040e583d618130500c920044600d0800802d0384070b00b820407100e103074010b00000c03001601600042c050800682185682e010341c0e200c80c003144c1000c604c4c0203070910107444404050b42c1407102c0f401405040c0032400c0103611800c0148003691508a006080d51801e40c007010a2500d005ea0030040d90300c0d01942c80c4c2d404845c0c07466403a40e90002050309408000c43d851003541d03a2040c00707100d00c86210203a00402e8084400031100088110880045599080e41d607400b5801d50081104079510f070910080c000c0c1c0002c01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 404931115 1250 404929865 404929879
    0x21305062403040c080c01090b030a060504050103052808070b04080d020a111b0a0314160303020c011706030309210f0c100306080601061d100c031701080a06020702 72
    0x782024203864503012030400203107158008180010030840c240c03884000e084090180400f6444100040d00c0c9112510619000c5940000020055621940b2120142c040144104540d507100d00b415503450b06c4041e100041000540c0803105075514461142440f260300c0041c1920704581596214103662000c0c1c801c6801e080c05020f55052201540081c15100006548410002514554680c604009180b25010044000c0b04400c86510340c1301094050729000a00c200c006035250403403c0c60300843c01c164100d01503070030341e010041640c045460072500300240ea030310081c0b040213010805000025512242d240e80104000e141500304400a1000c001281952060030a0344503440c5081c803e9884080c1500c0d0401c01d031000300da240148907041d0100903440c0800145040040042da5900103005071828492010303210951a80f10302c010360140d100240c500515110140c4015200c02900c00080b00880c8018840c0e01c08440c038010301a040385d415000400c10701ca0b0980725a8020341c031200c0f090707800683c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 404932365 1250 404931115 404931139
    0x1008060a1701060b0a05090f040221041b060903050f060105210a06020c07030b01231e03160e070c030807032403080903100203060108040312090c090209010e03030702130506 76
    0xd500c80078102114140c5c540542c5c7c1c45004c0e0400c403118420300344240c415803050140c0e20107004203c0c00c01d0320001c071403412400b16031564200007440181c61805906901c42c5a4808115660302040440440303218000b21544403043c0624180c903014240030b0160001d05862070427074406a00e90001c58562845400d440844049845020586c1d01045083d003140e4481f403130420801c4010181c1c5401440d50a400d03001d0459188685004014074206003440792901d01004194038805950510103010002e00705c5015030405900c1c42640103c62182c0c00c07945002c0b6001511090084a140e00401e074156640c1c8050b641d444000c1c1c0060921880702e1307042c10105800390002d044000c000c000650301540e07103a501c4118810400d845c0c19400039011001c00c2c014003c0c005641d0308046050b82281d41401c00303d07006407007400c0103002020b00310405000400a480b0006481d03000d5030003080340e69801e0f40e404001c0d03031114060680d03a1160b5100250099000c100340c8142c000260b12075504000f0081502000203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 404933615 1250 404932365 404932379
    0x92d021603022a06071202030c010e0a11030319050c0703050f03121b07030807050d0507180b130e07020a2021060411030f1b1008060a170106 62
    0x11280c500120090303400251101007078900c0c001c5145020b034065001c68425500e40b07004c5078160240346001171407007036000400c041103402030054458880c403400003004141d1800b440d0b6991101150801d82e8040c6009201002c1410003108035080311810300c80d44018001d20340c0d8221140d85c081403040452780554140440082c5040c400c0e207210100c0a00103540310110000d641d12401005000b501c039400f060f0b01d001c031070411084144ca10b044e8050802d44525960380c0c000340c03054030412120f01083c43c5003104210304560054030780fa9418044004080e03840303445115a00c11441112001203003422240720810a03007140c12013450b031004451040d80c005038800c0d6941404580070060703050148528a03010861410018a0b11440d0190b040b151180000700c40402525042e000c0c2c4042c00220210250604585080003a602c3d003900302000c407140c000f10181c15008452081070f54921580c81000c16507442d5100d1510796001c0d44005100c404014070b840840c600e28041d50140413099501c2d00704c00600f0f0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 404934865 1250 404933615 404933647
    0x150d0503031005040e07090203090115081509010b130b24030f06011e1b120207050112092310020a030e010e010509120d02090a0308090a092d02 63
    0x49108a0003507450b030030b01e19804105090142c00c4107000d80d1502c4080b40000c0d8002510504a0795003100045e9240c13038810806000d03004940d6880b1071546110800901c02400080c140845407a0b06000314141d01c0f03e00c0324030b0923900c0c09000203030302c8091904180f280100a07407000c1400030300282080103005e0800c0c2c4120340b6070982030007848000360210030008c003009581000380e402082440c101090728840f0307100c40605c4180210190810211b400341c072100e03c00d00240180f070b054101003074803890000004000e41e6088a80212400250b00c40d10b1716804204078000c14994030f0b030100104445554040b8041036141d0000c2c1c000c0c80921038800094007901d4540300030852001140c3c0e01080a074556102c4600b91a03030b015008245d81c1c5400c0400c0b00031580814204d64040c440c080d160780e504807030525500a40a90b802607a4442d9a844000040000040007007207604820784109022580d2003024078211001403044442120088601c0424080d0060940342c185485140040c18160b5840da07030415 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 404936115 1250 404934865 404934889
    0xa0209040e0a0c030309080a050601090e0a0f0c1809020d0602090102120a020601030b0c030906060402030c0705060a0204030b160e0f0a0801090b010303020f0f100e0a02150d0506040209010f0815 85
    0x801c803c0d200c1030007410303403004800029100d042c0040c600e0010b0ba540d90360355084144a0306030020782d00e160388445140c0502c07040380070f00d80000c4c200d0340c09901d41c01d007450300c5081440782884401342c1d50003c8100308064040d0a101130703002018039441c1d44044d03c9441c0070394021003c00381180036007809217100c20410340162800c0d091a0707005148540c1185040b441c200d001509108650b0014000c1040340500081d1080d4004410b4a02680303d40300e000d1503941c00d0048160041035030045030200710700180b1540c081e20880b800b40c0504401d5440b854000109181e4031000c000000e08408107001160a050054400701c0b040682140c0f07070590740c0c444283c01c6410384e5908481c1d42d01d03044010004c0c55810880100c1b440904d02c0035200b03001808500d43d59a895400500f840151248201c0504007130034070926050503000f52200b44641119458880310f64001070021406030714040104900d4101442138404520040e121180e009208c150242e8014000501610940d4807808282c81c064035050b4200038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 404937365 1250 404936115 404936123
    0x20901080714011706010c080921010b0109030305030c03133807020c0d021305070c050d0806100c051e0a0203071a03061003060f1410020706080a0209040e0a 69
    0x45407034203200181d0310560050071003604000b8900110049446003444164100c2e8090030024040d414500e00086940240d440c0d0a80c821782e0021424a020070101c01d260a07203c500e4000c2005000002c015261f504180c000a00069400d2000074800064040150f403c0714a1010005c580d620f2980c03003e01c6d10907a170800c00030036030f40e41c900803640600e0350300c2d10402030ac80c9920114091801b6507009590b01c0c0180400c1d403140002c0b01c05d1314259168103103c82031a4200c1003042c0b0a5281640c80640b401e12a00c2080315284141111448030610882e00f10740102302c014018903403688201411201145400826a098024601c21504010007903404202d600301440191022020500405081681681c810b14012641181854910200c0411030381d012a0886a0a01d6248034070380032401041c49802070410351070804004034410340406c503100f1010f941240ca1034040d40d080d87c0704a03159417081c49007178040f425038130114418900e150040e0550380d401820010304510800c04040c904000c254050b1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 404938615 1250 404937365 404937373
    0xd0812150a060f030b01080105030d1209020402030406060326030a02031e0a0c090f030507060f051213061d0604110d0204050a0f0e03030f0402271807050d0c180902090108 75
    0xf1034094050056801c0350100342000c1d003003580740c400460b0700ca119050141c82044515820900003240b5507000c908540d0b00a0800c44d00c9103881e1a10200030512400151240c080c007450680000c1482a0f8150202d110181140e0a40d00e515602002030340000c2c1005040980280081604181607504030740315034103000021800005041c8041d00c0070805400c00600d0601c112000d1020804c0015807508582103803034054008041d0030001c8030b030340c059854040d00c0c951982d130500101600c4e100c004050540a020b08121070410742040d0308111625025500792034000b1800940840c001c209840c601c007101070300701010700c1d0541e4000340448030110340c1445226070700d44111076100618800d500480d034807030006619504000000c00d41010004000901c960b02da10441000c02501c81d0007500c2c3c400740600c920a487c10961034002d08611046010509441075410000701440e050500740000c3d504080400c003094101110b000c0445601782a0004180e120400071005848080301103008003450300c050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 404939865 1250 404938615 404938637
    0x305030d0b0406151e030e0f100b0405090a031809061712040f0902070c0f030614100510030905150c0d050c0703090b0a020a050313060207050d0812150a06 68
    0x10045841c190040c0340e040e44003003142000036400445d0031601654115202c0b1000c8801c176411005030000a880382074500800d030000c1c0300d00c3c00010b00030030070100da0301090114504d82c005020894000700c4188043d0f9104144810100780119071102c12858030f181c000c205542c030b0319103410545803a40e00426161101c4034002d144038606101c004201940381c0c0c5410310385442c158141a880c03840c1e028480c0e1407980010b80104204808000c480103040ca881000030090303036820604018424505d050603914006400904035507900407820043e0b500c014100000384050b0507080b4003d100708841140c0e14407408401c131202042074001c0074030440100140366500c50459400c41d05691000e450340124400601040c4006604008104252410b100c41039488a4100078100d16008000348040d1242c0400a8902e1590081c250900181c0d0015000c503410540c1d15800d000c0d40501d13111000c0d1100c0e409101c0e0f81d586044030b60249400c2080d9802126a600600001841c0c0c0c10860b0310120115180c0800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 404941115 1250 404939865 404939869
    0xa11030108150c180613050a06120e07180903020705031504050d0f0c08070302031e19020a050606040b011419090e0403120b01051c09030e03061e0606040305030d0b 72
    0x40e4080e101c510b180b4200318040070a2180002814044e52203402c011520804a090003031140707009100041c440d80c0765035540d400141c003031228403014070301131400c0003480f8a00c4000003980c0b40c111000c140c40d070320701000f0005206c0010f0000c03000440c118094500b001a9a5800300085107282d10843d0003000a400c0c1840d0080c51300d495080024103004010340d8440405812140207180d2503001541c442d641e0003107140481c00c51081e01511490111840040760300d800092002d45500900b091052701000404642660b90301c800c0ca038006e0459103c40c000801904050704140c00c0c248060400c9401100310781103030207064000f64000f0707801910082044400c0d0303501c4141040104101c450090983c1842d0304d004003420303d64481140320325160688142203074410022a401d850a80d0110310003180004211405031843c81000c1e030000d480841001600d24011801c103015859000d030b81c100506d01925000c1101c2401000f00d175200c0414030000000c500184020401101d40f070700001a19452082 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 404942365 1250 404941115 404941153
    0xb0301290d110d1a090105041e0503040b0702030309060409020a02061e0414030f0f120f010608011202010201020d0e0a02040c0f050417070306090b07080a050c03010e0a11030108 78
    0x1014038801d8200301c2011000c94008044402030b001c00762926010b4942c1c5040038160071040343d40c0c1ca00f0444002007080312040c07041d40500d00851280022007000d030b8070300384c0d503094005c2e482001038044d410810040202f5492070004006051020302568100404140001e40e44d401941c825980c043d0000760560410760b06215403072780030746560401c200360461503450040c0240b000b0001032104085400f0000d0780c04081080d03600c442ca04405080d030740c04035001411032541040a0a200c040d103100045003014581c140b007681620380580c1d400007960701e000d0202c84503400c4a08240e055560811045940c4c0c3c84500402d14004080da0040510698030320611048504a401c0e0104120300703032120030b075201d9010045400301c805000440180301c1c190f4802d01c0c00c00b40c583c0c0c4001c003481e2501680344e080192a0b0080fa11543d0ba41d141c80115664141c2444155081110310201100040006204000700c000c07403941c1000800c040001c81944e1150b56440340d60080e004070a02e0303440490f11529642540e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 404943615 1250 404942365 404942441
    0x180f0411041719060507030b15040812030622060806040605061f0203030c0703111e07080a020604030f080912010b0a17060703181502090405010b1305040c030b0301 72
    0x402410200d022a900b0712080354940c40041100d5285c10200b450948250084e0820003001400144400200c00200384150b009100342e10480c0036400d10b000c000004c802c00d80c1d2040c58080c000e000d0300c080e015016020701207407002c842c8440c0d903202070216201070f00300f20280c850b038410100001e480c10000e00300001100d024030500448201d816a0710300c603590210540341c00c420350343d409688841c100d180603554440c200c0040c0320a44203264290502208110080d03544051407410f407045c0b40c1e100ca2600e5168405e00c20084c0d0010420001040040c03803c41c1031814582c01940b4050802e41c0000000d07010011108400003240c0d1a14a034040301e28010100b0001014058026220805d40600c0c0c076803180c1e401444030051541d1031944d031941201c10784484000a5010406008504850080500035000044854000d0b85840008a2101070074400c40c3c13903181a0b45e4101828920700000c01000e0710103000c10008142d1504440318103610300340541c522142c100b94010f816101c4955000340054181703 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 404944865 1250 404943615 404943659
    0xa02012009030c060c0703021f03181a1801050403020a29010509100321020106060804020d0b070e03010609020d0f0621020d0c090e0609060c180f041104 67
    0x108040070066600188203212075034295125034070340c2c0b9250700442c20940c4a038400794001110078482003a162000c414000c0201007910100040e411005400c2c515640340e11009040003902501503010512042c02c1c0c40e4061161400002850803082c0c1c100d00b900c1f002d990440c0540e010298403010003e5850100800d10900030089044500d2612038070b80341001849485c0c0101d10711004201180030000f070500107590005144880d010218100c4446603000c0814000194030b07100d000b08085204030100d034010350f001060041059400d40710b0480050020703007032105000e8003c0c0d0403840c1d91800c1c02208010b011440300161030320300288207142920446000c5010f07880c507010003808044000502401103d41505000710741d08031900c003203101029100c40282000d0310304000040c2c030820a4000102c0a103c08040d103000e40c44100da070b6560b400e000e864a41103810240b1187c600e0742340d402000c08080d40000c020400c140020701c04141140c4101c1041e58406100040034041210406101c503015054 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 404946115 1250 404944865 404944867
    0x305040807020a030321180201030b03010204270c09030b0630030c0c0405011d090102120f063d051303141b06030103030c0201030e073002030601050609150a020120 72
    0x380007c2c80b205401d105000b030605a540318100c480343c5096040d0380c041d2003143c1c04501c503048481884144a5112500c1ea51080d04142d4515200c1e44145140d0301101e621a6890500d030b00d403e0108042250306100d40c000c03a0021b400905440001100c2e10908814100040e43da900c80c88450a0f0810f550304000d240142d06001c010001e54600700000091a4641408000181c446e0300d4424060b202d40110303050340030184001d0120101c0583c4485004500458150100d4810f5480c42e4164450031110207803102d0359049428424103c0000c01082c40100e45813052500c41850090011002c03503400541c0c8603036a0980c066a0072004200c580014a0400c07100c1d840e828024001902d980301c1404000c003081644a980c10443e40607403c414000c102c0001624607890301c07464640e1010701c51400e0b00c07403002c0210208090501c40400c00250858000c0c0240c1040da080c081444056400800c2c0e558001036403222141e0800d200c100601003040d40d990003c03440035881c401308030401c00650b1001a07c100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 404947365 1250 404946115 404946131
    0xf0215060a05010f111213080a240906050c070c050306010b0a030c0e060a020c0a061704080f090303190f030204180b010e0402120a1a010f0305040807020a030321 71
    0x9a0710461404a41003403a1241d070a818030201181d00441d40810004d40c0e100303000b40741c60000b0403200500f000c4800b43d8100c0c1440c65544102c60303980d25000101400b030000d00b40c10700c3e9501f0640c021559840104d14000b1a0b000000e0362408101c51040700c211209142c081442e508000085070f0b0040107042c110001d25040d41402440c0300700f40701d0b80300c40c4810f2640c0c3c1c65031400300c58000d0b110b0180e4040014442034580281c180065225422240050301c03600c80c0c1840400e20500400d40074440144400842182d640d507a03503075000650003050b07039001c010814098020039a070100300504004454000c19221560b8592010b8041c41c513840070b2900b8103005010920150811204c0c1d8021400c02c400089082100c540050743c016510401c416040745c00010030308446994070b14440c0c01803007400400c00c0440380c080c0c4005039200325007070b040d03000404404c1510700c02c2e4469003003a90403074001c100311490414154001080000540e000f03e0104900c92800c0e02007104801c001070050340c6c62982809905 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 404948615 1250 404947365 404947369
    0x605040b0a0303201c02030a02010f0c090509040203010f09150c0c0b04060b0a09020d0c020c151e0c010501060c021e030d05071a01081c021606030b0409120f021506 72
    0x703618210700f06003013400755079042d03041010401d4043c0001e61107202c2c00c4034604124001e4407903014062100146d8206005946e05222034442c0103003400032503403031201550601c801c003e0641405402a0b034990f40314519001d000e251845a242600d100b45800215441c04002c00c1e02074032007440381c001c02d1108102e0140085801d00c00042e17845a07004000080901d034040005510000e26001520160702c00b00d100004c10b0300c140d10400243c08c0940031200115900c10800c4900702c00315100c00394481c424086440e0828120b0f850320303101c400745008282000014008142140d50036441300d80041d402c1300c04a0b0030340c01d0507035140f4400c0809206518640342d456000c40d035650340d60903818080140005070074081c8000c11820981c242070818014040d075940d11800c0380d54241d85484144001c038114550300556000180e00781d101c005009880742060328100c0c0503002800311403200c40e0000c0d11040c4040000310f101c00c01e44054422602c9031440302e0100300000703142a0340303400603100c4001030500340283c82e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 404949865 1250 404948615 404948627
    0x30c05210f1c02070617040602070f050706171317041502010b1804110108090a060e07080c01020304030b0105061c05040f0c1502070512070e1501020d03140610110d030605040b0a0303 80
    0x2d0302ea0f40c00f803211070387c80e189007880c000d10038000040d044d01c2e000c040c0103007017002c0800c646040342c459548800140015401100800805840b003850040008030001c00058150131202400041c074111981080da60b802041c0341c41c000c4c41c50580040c3d56600c0c1c0703c0354910301903181703000f0060303e1003104840d481c02c2d50701c4504520b0a42c81180c1030010f42c00c00140b44200030056107001541c044028040748031460304c00c56030740e4442d0103160040c0c01500c5004095500c00020b036021a508141c0200c00c036442d00c004d10440364490501048444a07030300d052840036115020382e902031480f441c0c050075402c80b1402e11b8a4440000c2e00440440990b119610728204c3e800603500003a034100302c80340080c9403070741440e0301e140c005540e10113420340c50888200708181014a01068130144281c080c1d41c00109040011004c0314825140003552405442c040381007800d10000030401b0140c0c6017810320201e40304c101054504120b10110800094032601e051165081500076460080e41c2690224030807419581c0161071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 404951115 1250 404949865 404949887
    0x40602190f021b030721050c01050a0503070f020a080c0c0108061207090b18100305100212070c03170112060e01110301051e06030403170907030c05210f1c020706 71
    0x4052980440d0f440719035018400c01c0004d0081b00000300e031107040c2c0282050840305819095402d400b0f109a00c201c594010b00031100c1d6041681c3e80d06195949002040d11091114031801017180300f000003000c0080c0d643c80040c580550020010140351600300001810003400400c4240030707080c80305149441c94030028000b001d40e106014045400d12080012556401c058600c8400740c1c0007a034240403031490682003c00a890080c003c1c3d640c0705500b60b2440081e4402c082c1403440c1d2604038130010b41c0da01d1040c81604412803003071400e80815100c640d01c000f1041c4003a0003070002c010603200076000300122031240d8280c1450790b0000344003680f818400b0f0f01c80750005104050146034052405440340181001da4075102c040100745a803a801c0c18140107044082c00c11a021010310703221f001c2024003c00044000499500c04001e4908038201814004000984095401145803142030301e07180400134041c08140302010802411070003d1608400181a03410f0214400c0d508030310414031a2583c0500f003140c0e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 404952365 1250 404951115 404951143
    0x510090308191101090605100b04120803060301230603370311010203090309120307050c041512080a17100501050a05090402031816080c0f01020f0303040602190f02 72
    0x800210044019105a2060441004030713518082c0030008006913a0b1000e8021400c001001d08640d40b581c42004882c440c5001d000e10111804c02900300041c940001503a0240b4050004142d003803c0d040c0b610418072010180c013913500c003150b080011078141000b610b20b01e010a241000c43e1114129881030a003981010040c10f20401c0702074210074140100001c19658081c1c1c4000c65a0f4940044910344a820901c542886520b1007013100610900000550303a0041d0090098007a41e174010f4100401030844404041d4010314122001441002c400600094240501a4241c1c1d07076203041001405054440659100c025041c0103000e004084140244113440081c28010390301e01d111700094403640242c032603d45d0b0050000040240189889080030001c0e0030180c1111800f441d5008a200c0da0010b0340240c1d84541d100358501d8496140545121000c0203060041c0c489080507400894150b40c0120b0b41603a4a46e0000713284a0807140300c1c40703028211003840c03070850415120740b80c0080d103810800d06808 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 404953615 1250 404952365 404952397
    0x60f05040611250201021903020312071d13150909140303040c1205010609060603020a030c020f030f030408041214150609010303120b3c0f13061d010510090308 70
    0x43c21640200b181050f80710301240d1144550342103280c0259070f68004500c1c51021908240800e607000e0113926261461100c080c5002007145001c400c1c03221640926600700d00752138580c08058070395400010348401a140e42076002c641c220103401c20044581d203603607400c840d40e0b004204001c085031106100784240e0b100050f580c02c042216082c400e002d0002034000c088441e207050300c0002e0fa03981550051104100c4ea4406120100c1002c0707080c0d86480d0100c6000c94560000c01c0502401d10b0b610005580c820300c2084114201900d80758600900842d20a040b2040a6001420211860200114104440e1820290f003135841c115000c602c00b11010310005061003500e000117501d10105410951800c0805007000e00f2410340707000180036683c202c044a0380451400c0302282d0589030000700e2414824000380a100f5145019400e000b07408074020449000d2035950140403401c0c910b0012898050301d0000b4003031615504000070040d18044620b072610510400d0801080041c0d04c1800340c4030b42d440510161 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 404954865 1250 404953615 404953687
    0x405010209030114070807031b0e1302030a2a0509040e01020702040c02071701060f051c051b0f0111060c03060a031b08010b09250c060f05040611 64
    0x4140607010345540580e040d420214412414110103038814841e0034030755a9041e5507194040260100d07108080c003004980c902e00329a1040d05d018415096003048081d00d1a1010f07100c00082e04101c2c0c006031079080540d521412845c40341002c0084100019006003103c3c14000f4a201c4082c0052040072100d034000d503100c0390302c2c080c04070003941592945500907100344011441d41400948411141c0030381e05060387e000b5000b4504400c148110b0007a9003d155440d24098140000c00810b010064a40746102e466040135400150043c41820f945400844604504121210402824030a10110b082c1001102c0403191018140001c0e481d41004040f042a556504c81d14042007060489800150413a082c0c501842500c1060310040343c1101e00306802005196141420403c40510584100e0811003003981c00301003c2c07200720111585c040c09400c0868803052030b60b43c1c446c182d0340301031b4190009036078031804c0000b0f03c90341e4010003d1280b0440c21f900d20b840c4400028040e0780500c8103000124840311104 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 404956115 1250 404954865 404954873
    0x706060f0b121f120b0108061e010b030c1b03030402030c0d031d0a05030307150f0c0534080c07060806010c0602030414030c06070f0c0c180f0e100b0a1d04 68
    0x14482c064101000034483c1d0041c0b80c100080d0f105c400b80310381c41d650701c600c600203589083c500703184600790900b00810305096480c1400000d040d0704040c001d5403040c403041080b403080c05a00d08002158030066000346407285084c0c01014144400448614040d91445503490000b035031180e11000d44198040c0244015191100490f1120029800454051100080e96410b011140000d038002843d0b200c01844510400150882a41c44600c0368801040c07081c030140c1b035034440d01964500354800850b044038801c02c24603040c00755070b1001c5000356000d00e00020466080601800710f00c01074041b6090444040c1401d80009119120482c4060070b115404004034080016886110b187d90388282d0459413182c0d8161141c50f1203200c25161540841d26094001c052240107040b0340345555009185003d0309407905444044011a01d0b00b00c4410954920900403243d030a0b01c910f00418032940018001c100e8416040402c51700c0c3c8240040c402d0020040412014140381c944d641a5a00100f10f80255151850 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 404957365 1250 404956115 404956171
    0xf0a110405091204091409030a090e0408130b040312020d0f030903030b030304030c08070e0106120506030a0f030908010c0815060705101a010e01030902130b030a0204020706060f0b12 80
    0x10042c0f26000290000302009107800403100f0340f00504d8550090788485d85400d98904ca2072020030302184103404100310820342c040400390b00034040c2288502e070601d040003019580340143c00403416107034040703024005d00c00d41d441e01c030320142024002040c820b01540d0018000803240c000200405444201c00d1003054820b4210140c0c0e400044c0449032505d86900c1c005400c80d40368011210700d48a0980c0009035290f480c0612412907009407030305444940300c4601c5c807010345030041c80f01d500340c0300700201c60002808065a100c042d60099036100300b0726081140302400e4424003000c200c204401402841442c0c51703030740e08035100e6034002c41d032080d030360101894000d00b000040800e002c00305140c00140c0c00b03400241c145800900e5003d98950703403000c5840c001501180c11680020303400003040c3d05200f100f41c03c50390001010180c0142124511485540010103980c0704081c120f03030190b00c58104002144a04031a00060045960620300304154040d004001c00001410004848003100c00e400748191020317 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 404958615 1250 404957365 404957383
    0x120b090612010e1b0102011512150e100c0807020d02120c150a060e010506210601120c02010e06010f080615060d0207111513030b0618040f050f0a11040509 68
    0x101c190341c022880d064103074000214044c0d00728095421700410340d01480718161341c042503030f02c40b0b8800c804074802c5440d40384049540c180c12000d541e0751a1000e00d08441b04005109602c0303015800404c4804d6a550010800d4001030b05a43c00d542c0140d640013070007600455241003007159601c400380c50f154000d00c4103107403903101410858208141e41c14804002019048a010b9a40703001c10b680859a03110f00740501ca00c40c40800c99040b00d01c00690b10785014140000a0308190140740c05452102080302807012140d9030030708100942c0d035a000402d40100c0600c012801028005003019440303141c85030341601d0f660b0003024149011140107058640303996200545c0c04480020008548802c400d1070a401c814030858130030380c400c031030041841a50401e81421031f201e0340c40301c5001c3c0c0d0301c0038030b10b0b92401210840604016440000010450640303c60b01c440c0e80d100345e01444000f10382e0261ba0500c5404e00e03c8800650300c10342c01c2a40c940001c18505489401c10301c40a42c0c0005050341e840c0d0030141011281 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 404959865 1250 404958615 404958641
    0xf110304030b0903030702011512060f1b2a0308310c09050f010b1c1805011b02010c0806090613050c030610020a0b010506161a0106120b09061201 64
    0x50340c280f11015000002845c49525280c00070040002d035201c2c015400d080c0352090b00c0b1500d400070b00c5000050f1154201d0700c14039800440110348919140038680c90b0b400006003800001e4a00e19042070b10591004080750b0101c20106840302420503520020031100004200c800e001441c5843c0300c00400700308005000004a01105203c905a107251006000703201e4465540918140004200c081c1603624019040f2185080704c1c0d450980c00500103800d24076100e1102c0480e641c0c4546954040c0701030800042114450000051441404010308000703c400c0d0388103070216031502a6200e5000d0300207503504e4019000312a05402e80d5103650004e2155505403c200c0d08640c101014000a011454003440c0140002c0340c0c400940a21030800301d030364005901c409806411101c1c010041d904081d0002c2c0300c07480071001180c00c0d8080700d84840760546095030b080d030f00f0114aa40100403030355011100c820784043c2c41900b4052040f140c000910300b40b101500f501c0c4a000300d09000f212045007588607003110380c04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 404961115 1250 404959865 404959883
    0x92412030c1b0303030c1d090103150b030102030c0409110a0e040207020a0b0a2c030604060507050c030a0801060306120206030604050c130f080f06010819030c0c03060203070e060a0f11030403 84
    0x101c4c43c0050150000c503150002007444400030f038100d0080d120100340b5480024000c1b440d141c0c41d544038910078181c9000b5000c410303a540c03062400b242c2c07000c1c001035200d43c40d0460030700c0d510340c6040c000608581820314000b03011034050104140b4503500041c0d50840c2681101d01589821031400000ca1903201c42c0d011044001d4001002402c0e1034001a0717100095a42401c11240c98904065945901071108003e1794035410540000300000c0060b03105640194982c03030081d080283d4815454590740c8210040740100d00e5001c010440030b5494000c00c0d0261034003810300d035202d4105901060281c0406894944625180c200240e211002c0c407040e02e9000001000fa020720503035808400e5041c031410302030000e81c2e00030051114064800000d00e0b50403210420002d00340030201c1d051100071211242011000c1080580301000494601880755020318000c010040c2e4905000d4409004100307402e1420b8041c03082400200105070304540e8082500c555403c00d05511210901000e04510035a000103205c240 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 404962365 1250 404961115 404961119
    0x30a0c05090405150f030102030c09012a030c0606060201020415030903030f021c0b040c02032706030c040e090d0504140409050f010504150912110f07092412030c1b 72
    0x10001c082c0c4c022003815030b0342c024006400014182130784000c03240c10410f80300070021840c065100d48039090404018114180d0302c03604d140302400041c0c41078002503000454800040083c05010310800d0f0003004940001c62401d49010381524008405240500526560b106079005050080c0c10140c002c0c440c012003156281c06c25000c41c0745400401c909059200d01e040d41c4129982010f1003a9445000350360001e41c181400400c0036894504480c0b10800d019400700c107402c0607610f81602560040f0342c010a000d4486084c80d003402c0280d0310042040800e81e210443c00d0001c280c0100442e01603801d082840240105004042006004440c10040c1107120700d0400340200e403010350040380503500c240301190302c1d040b110104109503000743c403014080d045801303807241d085030080802c6102250183e05031004580c1a07a0810b0038800654840d4410790344404001c070141d480c05a4040c1840e402d100003171300c01c80c140303e2160804580802c00400348007031060341c03c2c280403103640000380c031100c1c849142c1e8900e0703 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 404963615 1250 404962365 404962381
    0x120903080c1b07090e1b15131e170a0c0603050606130f05030d140301150c02030105040302060402190b18040b1002240c1819080f0f0f03030a0c05090405 67
    0x1005a00080240c001c003000c0061041c12010410381c80400204804201c12105080c0340d41c0390310500301230341d0990700c0a000040001c09543d1a01c141074510401d404030310310704181c0c1086000d6031243c8101c03507003040e014500021114440441034031203500d0006030390396918021503403c0c030514076280c11024004800056901607071244105640c001d80a8070b02e540301803d030a41c0da05400f00f42030a04500207100600400c0440c603410000f10310309103800d07140c0c40078a40100382154019074040e40140c10180400040d07040161600ea400310702c4170b0400d400e403450040010001c1c0039201e00c0580c0ca4164070218016581c07140c010742d1652000074401d0402003440100a5175a522485080201410b1484240414051508030703030b00c0744020b88102d81c60712490030400745031500448905075102040004000d100c018140d0341038083c100500040140300c540c400180d10704040c05010803540d070b01c00100c04540b0103000c8243c0350800001040410401d40910040c0ca05010b84820b2940051402080110627 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 404964865 1250 404963615 404963621
    0xb060706020d06060315090e1509060a050f06010504050f03030f031801061e03080306040e030d1a0a080a02010c0f12091e060503180307060608060403120903080c1b0709 74
    0x800b504240401040f41d842c48107506030b481541c10b03000e1002c007025040082c075000703420880901c030445007900e03860600100401c003005015a14204603034499410003030302a075107206668008000303098900f11441d000c0700003452441507000c5c0368001c100c103003401c0c90a52404c00959100c2080c41e4400350300ca10b03016141d0b1041d081c2c0b10038009565802d1901c000b078100c407410111601082214200900e06041d078580c440e00d640007520385a0440c1c0d40d400d103000d9840060000d442124010000401d40402c03500348070005540300c10300c503403050102d0103041000942c001000060180c1c28240255680c480d41046c1c9141c0a0501014003400605001500120b074004c03146825161141e0812070f11940081c19200084d0203402010003080d001c0002c10800c000b8481050724217501401180c0c9040f10658680381030300d46a46c0130105981c080317818401010740012459031030706240e060400c004406910000c19840000e00043d0001d0000038940240782226400380c80c00f2500354003264200c642c1e403590030000f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 404966115 1250 404964865 404964877
    0x5190b040b0a1419180e0109110903070e0601020c04110901030519020c0d08070f1d0301020705030d0501170607020a02042c0706022406130e1501080c090906040f05010b06070602 78
    0x40c3d4107642d00301c012400c0f241c401090746c002c9524011170340e007006000710060054100340a201c040501480c12075139420004040500880d00d0041c4c12820301c1000649003505071240140305504204281c0181c054031005d9a02802c000d190105143e00d800892500429800040d009401d000180144600f000009c1c01030114640c5c1d600e681d07941e035502a0884003150f01d510b81000040e02494100400444034510880d0b40304010001440c2c00360310361780d1030710b1940b100e481103110b19107034401000480c244444405518040001529213480d052000070346a10316102c0c0248070316628814103074680384c4a28800c2000b51041417822002d07005600c031a548030207910940c001482140340c907401d407840441c6444440f04680c03d503102242c44030810450300c50098180c81c85420b03519030781224401c50030450b081a810040f0160140ca5050810080c00c0403104c0c8215401110601300b801160b110004075594025000350b00700d001000705151542c0904004042140d0089000c01c01c142802070903401048 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 404967365 1250 404966115 404966117
    0x30609020901060309081e160c09240905040f17030f0702030a1d041b0503040c08070f05040905010e0601080c031b010503040210120c0905190b040b0a1419 68
    0x5050381d0f00d510031001e031a000f0800030a00344042c00141581e00c200c401c1c00070000700031840c0904080180030080f41180c2c00d43c2d01911000c2145004100c0e071042d61040ca9040c1031420045907903101d601d102c6c000c460b00c5500c0b541d5810b60780d0706c00103014410030102300302030aa03208221040c0d0161816902c40346030016580c100624140002284c03550340000229000d40342540c551494044039851007880c5603c142d07003581e07000b0707845110503035490030542c11a141c0c0c000d064444946034100307424400316400564222104035405410140409800340240074201c8104a801003412111072414a0140030310085803c054443c040c00442c1c100700100307520190000a5040340c0e030f021708208075085e05a00c442d19140c042a401c00124015060100c401c039034a5405042003010f207000300c0e00e1801280c1100001c3c200042d07511105000790f10b031070028065100782a4030814042d50600002e080340703124074821881119000260118401d020b21030391003c528504d844151120f0b078050702108005a4450010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 404968615 1250 404967365 404967379
    0xd03020301030201022a01110109061b0f02010e21090d0302010501090f05040c060507020d0c0f090f024e09060105060a0c0f060b130e101107060207031803060902 71
    0xc210110744441c9181c040030a12044044146c580064517070300039074010041c59540f02c418160118183c2d000308030701c50480b58110016008810002480c3c3c5003d900d0100031a41030038003248003100000380b061201c044d164203240071002c0d00f041025092040c0c015031130704a100c404400043c542c0640c002f81c102c0c0c140410603c824140d1030180300807a0710440300101070b040d80040601c003c1c0d2151019100043c4013801c1d600b1000c1e1552620348850015900ca0144800c0d02142442403003018001d5000b003800440b019820041110301c00038150a50303030b007903e0001c4082010030b06d801102042c3d03012101c00602d201b03082c1c5208821040210802213401001358401c590002039a810302200b110400481d90351103c810a00d00d03620400400c0120100366840c3d07841d03643c64030300c07903454034001e4620a200002c00151207004034809400d00300d98582025100d86010080c0e00000c5031081191030300c07648524010b907941c20178074003641e440c80c40c3c040e8810705840b808004010080503a000e4442c481c0219005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 404969865 1250 404968615 404968633
    0xc05011a090a060501080c160206030c0705010f06080a0f170d0207140705030d050309030f120601080a050702030708130905100e06062503020c13090c050a0f1502010e0d0302030103020102 82
    0x942d05440c1d0600c034080c00201c0b45800036110085250245c600711132110820030400e040c0d41c00251140d0001c0e07032140c03982800040d0000410501744a0108541c00030801030103179a151100580e29075001d00d1014101c00781d0720018008002c01c040742001240d2098050b1500c2d80c101c1c5001e40300035007104c03504540442ea02e00d40805071020004250003252030080041c0440c01e403108003207030704d6007000d40344040a100601c00140440d0fa601d010381282e140b840c3c9101494504600010140c1002074075a021583c501414080b94a46c040b0481e0109500262503036640c40c0184080c440c14240d50b440300c14018605401c1c48000c8402081c00401c44040e500c1d9100503840d070b80100082c0f44a0150780190340d00950032140700090440e6a0305038594000d00580d06099010b402041c1c00d0115800c0507480903545924a10402009e00c8451014000640b1b034425024203080420401c0344150003001604545020f054924520035001b07245000e01724401e84c1c3d43c4010304100600650001c0c00105c2c05406400c1e00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 404971115 1250 404969865 404969881
    0x321110303090a051011030606070f0501361518020301050408030402150a120b060712091a04030803070e1504090c0e010305040317091e030403020301050c16030f0c05011a09 76
    0x207a0b210044a416042d1071525040b08006065000400456a45440c6e10341c00b03010030420300c600c4004890420705101200389070100c6100701801e030441400248440e10f4ec103404a0104064400580c1d1801c2c40064032001c0c2c0303503040c84204a041e40c001d506600f05002c00081080c07000183d0f0081e0310035174003007010202103072a21246000782150100046c554540e6094040040c3c0c01c509140407029000a00d090b0759503c0d0a01da45a81210210102d2000c41040060f100c4200100b4200400c803401d0a041c2030450f65503003887c3c40301601e4081040f1092044550b070b59503251903802440c0001216564a540d12003152001d80000446400494076842010940e54068040d081c4a00d5059881054041c001004040480405011aa00344c812203800f25121028040b00c01c2e000703550000116103441c9544105420f40d140100201d11154091109011184c644a8840d0200386d050070000039180c40c5a204a03113031072841c0c40152556003044072040390807000d003100b4000f446007502d121209543d2902 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 404972365 1250 404971115 404971121
    0x17090105040f0f1e06020c21010f06080c0402040e190209090712050a0b01121a0a080c030714091b090d0605060a08030309070e0c09030706050a030507090321110303090a0510 76
    0x300e11700258101280b007410742c0c0741056003d18050403000c00c02d4005410108901e0171100414488102e15039120000d120111081050084090049402b54685410724070823201560f4007910400400c400d001103040028082c0c0c06880700c0a20150081c5842c0c945284000c1c02c9000100385c14004034a041c0100b003180b2114041d0880342d02c1306843d558524680680450001c0140d0f1181e01a0200702c41c1610385195100141c20f002400700c40010100400c500041504248551307101048a08070781c241e496007070301e9201410790700c007400d2642e11000c0080c0c04da900c4010b200d002010b41c0c2c8040e4600c641e10070800c081c1c0c05030b8040c14050311b801c03003800d44070b40d1816928403050ba008409940081002c000c80c41040203c1c65025415805481c1081d54000100b4a01640c40e040036011034004990310410540c14843d15511600c0340c50514843c51841c0c486a400c00d14065507407003510300303a401080b143c80c003441c0054801c40200080360b5903445d04201c1545c0b07411030310000311214010203c0911009020340 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 404973615 1250 404972365 404972369
    0x9090b040201050d0902040515120304080a021002010605061204050f060919061e0615021c080703021341040e1e010c09060c17090105040f0f1e 63
    0x1101000340c48540041d5000c3e000010036010980e1030385100070050301e0300c0c041c079405080c0380c8644064510703842040003200160303610a08543d41c4140010031502c07400144c0c40c940c5a8050310219824a00900128050f050903041160801000228071302c40101c60010507209501035010b440890030301400940e03c0782c906403807582d0540c5c8110301c13072050b0140c0740f141c50340c2d014401c1c9000681c0d4800c1c00980d5070b8901442c0c40c0108000e80e0340348200309455021114020540161000d0102002252040000300c510040301d00308000e01e410004401e10f0180e81101c10309004c0001d02500306540b20711000c20010412007000c41c525079402e4007040300742c02403211340d0056002c070a0076040407040c6060200a00c440483c2111380e20a0740141c151503040d8583c40055414001c00125299148110141c00b0850300e602207020400c04d9003442c400304030040c403119001c4070421100e560b5020060f004840a000300d40156500328841c0c0000514280c050240c4000c48442000b00a24021400e9000c1c8030700c40d0034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 404974865 1250 404973615 404973623
    0xf0f031905031308090f03011406031c12021c09050c100504030804050d02010e090907051e030a3e03060c1303060c020102121609080f120708070602030408130909 71
    0x16054100091241d4003801c17401802400300c882a904020001e0b0949400f08404184803c0c11410f208803810103111450540c2010010288960004e1000604440342c00c0101c4c2c0364503601040200c0c4544c400da40c040c848800b0000140100c5d605414041d440f880e9106d510340c4520a005409001c40b4081e4040d0340403242c0100f426804e0510300010711050711030155080781084466280c8001941c2c41d660210302440401d802820402c1c142024880c92461003c40014125480c001d11011130b40c5c00104003440d1580428201e115900300700e840303140b12780300070002c0034130303022980b61030311503481c040c01d41400d2007012000c50b1020307115507019402a01c104e110502c9030091004040c00481c1107034006242c042690300c00103141c50b494002c408010641550012140ca400c59510b1601c141c0c407500e080d018000400180c81550f40e04140c1e580d179408000078407a001000400c9a2060141e00815540226080070301035540740750a241031005544403907c807804191303104002040510080c440c200169900c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 404976115 1250 404974865 404974891
    0xa1503050a06050f0424121203110315010c08030c0a020717031605030d060f0503010b15041401090b0403030201050121020d110f0a0312030b0f0a060c050f0f03190503 73
    0x142c2400d10020744190481e40d00110f0418581c0c0c2064a41b100e07512000b00380020294100c011545000007070034545d40012400c26050640c0e8002e40c85040003201d8108065101108801c0d40d81d0005a800b1404000060b001d0b0002108001c1d21008650090214080c15420344441c036480701c141d03d02e50030000d0741c032203a15401405101c45100d000c0140c241040d0285040780d0030030341c0c1d803010581a81d2044e00a1340198075a1a410031042c28240942c441d82941200c0c07000e02d5540c0d02c0a40d0304280141d11030b02c0e0710017007620700745c00a59000e000003001602e10b08241c076684075220f080181c06040284101d28100d8202d00911486c070000b9110741c900300f9401846200913110381d0303d9250380c01c1c10840c03103968004041c2c105509540c1e2905515402540302d18000d03184140742c244098215614800d242d4010f003400d0050f598a83c0c0e888501c1400d0310f1181c2001000380030b10b070a2240c50412400f03801e150b2032098550000c400e5100202400a00c0402650340300f40140d007010886060106483e60003841030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 404977365 1250 404976115 404976139
    0x5180a0803040603361208060d020f010516080c0607050a08041b0518070207091116030c1a10050d081207120c0504090b0f01170606090a1503050a0605 66
    0x11298000c00d050700c50341603000c0c12025240c0120b40d0320040d901c42d043c4803001e04003604420480c0080c0040c40d641213a0511f600149400c1d0081503110703203a104028840c10b542690103016a001e40700b6115000080c1c04040609001441c010a180d8489900621a481840d00040c18244034204940303d01c00c1c199100c41e50ba45441d0788000c0000100101d25516101c9890041042c1c1c807803a240f030183c3c03040070441031914103043e07802900f0800300760898480d90b82481d01200c440714001e41100c180000b140c200104032003060500b1500c85505000c003c1c850000944100000903040c650745005502054042c40802e0f40d590800c07070041602903000b051002d0900007000b42c284020b1a0a60210711400d00e50900b80852250700103c0f082c1194044c08100041414032081c030052180604644003510415400700c0301d5000604a00144802414841681d000280041d1202000d5402e455006450040255203c10700d404407252010300780c1e8002490040094442e003400d016140440d000a000440d06417 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 404978615 1250 404977365 404977367
    0x1d0d050d020304021507060f0e0c22090b010e01061d1f09051314060301020421030c05010623100e061303170712020d0f08061306030305180a08030406 66
    0xb4100600503a40514800107103110101d900c001424003501c2800001034514000141c41c0885030102940007031540304101a140b01d4964060110a81504114541140c4054a146d4002e00760051005210203000b00000501c104950b100c24182d40043d25200310250b03d1901904800007500800d55111041030080e24032030395855040c0304020301d1490001760325a10740700401c2008601c524020100e0717a851000b01d107440c2c4001200c0ea00b040080300290315040ca80f000c0e407000c020f030b00b807040154405454200001c050148d540c0069140c3d001c0300911020b81d890040300e41c4c00e81480107421414500c010030b00300602e009414a42804115114059510112018482d4941082d81140b03075850203c8004000314a0501090543c800020030469441001d89404d6a0381062040f40b20103542c4641b00502c44503070001148a20f01070549040d0105076280340000e6000c00d10800c4807a201e81c40c003003010081c150302c2001080705060100d010480e80146006000109107640304500083d0014030040c4545 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 404979865 1250 404978615 404978617
    0x207080d1d1204060905060304050d051b010c0903110405041a060103270201090e010803090907050d021303030e0f0102070b0c01060e010e0603071a090f0316091d0d050d02 75
    0x8915644141d940c480107046009280480425001d0201e031008181080781c590b01449030805044140c50090440c10203544540ea24154510608144500810041c002952007020052003036224002031007403495110002d0403100c02804151103410035002d10f03d10134180b90043e51300895100301c4030f245101e945600c040241d40c0180c01c050400d61a00c0036600300f56250300b01c0c0005941d000080c1d110120981c03001401d5010260b202c80c030014589c2c0010013120780d000c02a201d4100c408d0707844205940d40c8040407649032061a035818010b80c80841d001203220030040342c04040d039100e900d5070261004038404010705203154000c0b0170300690050100b031203000c100102400c00413901c10008141103403684100d41030a0800d070420741000e810f00301005081d03d010400341006140000300342508200301c0c1d5055000307200c2c0c441124014848a9582e00540d20100494407004400d0240246015282d402c044007405031080d426910034806950310710514000301f00100c3c40d511a86585281050071021003010b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 404981115 1250 404979865 404979881
    0x22021225060e0a0303050d0e07090e03031e0405070626070206160e061804090f05031213020d14100e0c03011410030f50210f0406050903100207080d 65
    0x31801402c50001700100c0c603004bc01e0b80440140003454580c5440b504018002410405a10040c1144404d00000ca0b10100e13a00d42607402c140380107010302c020303040300e03210f00500c1400d1240328a030b03000200191581c1c0455028010132446071001c0c1e40501d60322084440b440042401584014200000e2003401003260342d54400483c05003000c035800845071594000010100740c217035040c6c3c00008550f100040d032002c545910030503c1d41070452440701e0742c000c120080940c802c0101802d8030303614a2101032078100003500c0f1060844000f441220080c0d10400c1c0c0703400c507c1101500941c24030300103c6420030161482803042e881e00280e00700091641c4c5071803c03d040950b8044e1008106a04441070071039140500c501c00100700321445002c208440001a0300120105290041042240815003214070104080e041003104100056800d03115540c2c42120f07101d40d811030841800d00242c0080c00d20780040c068500b4020071402d1740c400f82c1803102c40000b44c1c401c103000201019030801c00785018264603070118403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 404982365 1250 404981115 404981141
    0xd030c0e03030d0b09010f0f090c031503030e031203011503110f130314011b0e010e04140615040e0103022b0606090522021225060e0a0303050d 63
    0x151010452000c82e05582c006880c0441440e00d9940200075030900550341801840004001a81300b07140c46141901d01185006048000c1d45405110800301e1182d080140803200214580240c00d81e285409400c024207210310314000e00132401058540c421800669040700d8003440b010002200e51070f400c400424040b684c000b6444001e000984d0025448030240c0358040c0440780a600d41030850812211400f414200000d084c2e0400b9440400c03510120152290103c40b424017141c2d500f0030fa401a00c20b219003162481d0800c0c82d20303000800d6100f01c0d25009015103030a03035100b02c0300310460114500c3c0d849540114150500d80c0c10040006003044200010140702c026103c402c90740507000320a1001c18140c2c5e00343c598a45504c01842100103600c40d9540100400b031000c8060015008004012040018007901c150b80044508003000030a118028145840c12103c05162030182080803100321180944400900300340b580d03a071582420300320001541e4050703c17002d0918603601d0021018140380302c4118 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 404983615 1250 404982365 404982377
    0x507140708041e120803090601050f0f01030f0609090803040b0708040308010b071703010b0a032d0902040906050906040c120f06021803010507030614090c03040b0a020909070e01021504050d030c 85
    0x1403c45580d1142d004040e05c0750300015601e04140301c44a240a42c103030010303031040b080c0030301400c595610a103000e4030000c82800c0110340560b940320540020f00480e40088419801d10044104200040d030040d0710032803251a4145142e2504c8500711102d0f003044800034042840d400040c07101d404488042c000c0c05100e5840d0070561804070307100049070740084c1c0c0841601d140c007042c0d40d80c0f00c0d9013600a111541a645224241010246081c60254a108043c06680d2582c5503601c5007076480d1504043c4000ea040401032015007040780c1419a0342904940a07103440c001014041a0a1f402078007a29a086d00310705105070302034150b00c41c42e009501800300200c240c0920844505c0d01d031020b010300303441010b032a240040c4261402000c41c1e1444d111712901803003410f608040084901d44441601d4120b42c11002c10020355858a1701d020007441010340c6158800c0c00b150802c01801e501c2104c05d0040b8400303031309541c1c00351030301390071802c80d2134058400402c1500800341c03128002e8841c0d4456100300c4c040e0329001d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 404984865 1250 404983615 404983619
    0x6080408130e060f04151401020a05060403050a08010906030b040b0a090b07020616090506030a0c02160f05040c0e0f120a1e060b0913110a180507140708041e 69
    0x61501110142d002204080d840e0081006500c0d280c00c1603110b506041e2818004a020034004400041342c602822a55010030464840207901c20807800440d19031100495441d030800e030501400a42001e0300c000000b030354400011520b03000c42e000701421668020407148040d180ca507104052110002d04c203000315552607031000d0105e80c00c2d024250049905402070900b070305100d007030604280b00108008043c443c0040301003040d6294103040300da20101507880010407440b509812410310081010600030702c44800000300381d648641c0031307080403908119406c05c4a420380500a0f200100e901201551100c2c0000c002401400d10424200103164141c0540b00114480d0350ae04003041100c088014454540380280b01c1041054460848034420840d03005030a8a070840248411552040000340342c00c03040f0360020030507101d030a00107000d00034541950344846a07030164000184409c90300070001541518407050460501004c07200840d8200c141c0310320302414260b11002700e090540214480c0502e01c140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 404986115 1250 404984865 404984887
    0x305030408160b0a0b010c051b0102010608060a0b01030c03060617090c040e01050a0b030715140f0c0c04050c040b0403260c0604030f090b071407090e030c061503060106080408 77
    0x9107100c0103101d60f00a44043c00c0440404c3e04840c00e64880d1818412010007100c00300e03000282d07180d0804801d0704c0000b4284c3c800d80040b4003409081d8010210b510a1105016a0280c0764010102c00300003a6401c02100704055000c4082d41d24504c03c1d5404904c2c1c08004050114001e0310256010110764100d44440b000d2201280032a1001084040075035525418441600818062004c00040840040c913a860900080703920040c602403920052281c0c0d040c0860a00783c0380704c1541e6030410001d45890301c8144c0301c06456200c880350094142300313510b0300000a051040a00a640988694440c0340d4141400c507503a0b000080303d149411200881041507114624802c0001003c80d1000760001e45000d0400d0300c2e000c0c0201d03190440720001c5c402c6c40c070307414002030541e14107440040e42c01c8907803140442c0300389001c1801d121003078000086144c01c00e10802d1104100100070034440412800312a015510701508200380040080003a6054000342e004000701d6104004030b940060103004d100d4504002050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 404987365 1250 404986115 404986147
    0x9091302090a09140703030206010506031302040513021002010c0f030c0903020901120b07020615010e01030e0601090615030e0c0103050408040e15040507080f28020708041403190305030408 83
    0x107040c2030903502c900c10941004038130121100030103030201c004c0c00c1d89800c1d69006904e5800c14040d50f4083c10012001071808030600f0851110550003070000c00c5107040100d00030400b40c001002c103134003a0702010800d21580c1d01c14421221003403002d54490118820001089000c2c1010020101c100a0101c0010000d07070340350f0054500810019a019000071030500d850090224010089419504800108424040014101120701c0024600780c108100e01d000141c008084440d0341219502c550400401c2280701a0300c040251020040c48880d0300c280203c08400761207100074112455044003a402000d0750098128603040361241e441c03941044d40b0340e030703810529500031181e26800e8102090310340250309040c07203525006682840c040c01d051070000d40145c94040007500700540124042c071440340040c020349042c050f00c81c0d0340300c1c103541e110900c7c10102c0140c1c001c2d02801c60080c00b9050b07812828038000881940d0002c0550400040758615101941e00d0307000100151103040781084241800d809400c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 404988615 1250 404987365 404987371
    0x6090315150102010b1804020f04090602160b0603010e030d0c090816060807030515130b1306030c060906090e070e061b070e1302360f06040504080909130209 69
    0x401d001511a00000c00203003510000c2403501e00035000381030b001c14400101c0008aa0040c0c0640f40c10200010710000b0a0081078a90300184c031413032010940f40d83e01c01d6000c0307801c40418000c0600450545440302014207d410103950117249a000300400142c00805410000c1c618425003005025955900c86050810074035090400304101544000d101d965000300e19690450001d15040140e89805604941840800d20405114025841c9640d89900054204a198010282070003406c04507044007400900782da4041164036007030380c0501180c99403150b0900800c545840e501d00c48013501d488035182c5840005481d1800700841d01001401980750071009294145040400b004840f6410400d141420317040c1d00804e95005a600a2005002d0710360703240b87c000c40c1c044440c034070060684041d040c103c051486c180c540c80000b540055040c0000b41c03e2945c4102080d107a010007035500c0c1c008020450f0740440b001000320344244440c2c0040d040c01c409648c3d00c44ca80d0010b01250440700c1d00080c0b1901812 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 404989865 1250 404988615 404988631
    0x20901080d080a060b0714280203100c050f181507120e100f0203040e0a090302060f0609010303202a061602060f04031202030315031b06090315 63
    0xe0340200e820301e584250069441084048104030301410144160035602c0b0340c0002070004010400141d0340c207401403191181110407520316002034903030a0700882d5899950034042c1d109016524030300310501c100d4021002c0d01c9110b80e4945141807408410694249c20007024506c501c0022044400d454880c01118544c0c01b044600c1d542c3c407003a2a00d400034984020310400c0d41007001191111500c0c0c3c444442e2902d0780801401c1910284d00c0c5241c04a1840c0104e41c0000040c02c510420321443c60032aa000400990103582514400da45a040c40724940c0820ba9010360007441020040000c244141d071588000c4d0300c140e10345d41c0751946001c280380c540307012610808021595001c402d003103a42c0386011844840c20580b200c0b400c105240e908821041104400039010710320010308400d0a0044038116006150b02c03545804c05006c105500039034a400c01c80d2100c034220b040400c2000c1925000902c03224006024a000c0400d2203d44140718031500101c00003609445062000d80810344546211881100c0ea = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 404991115 1250 404989865 404989873
    0x60525052a090f0a0f0f0906060b070b011203050f07030f0908070501121104080a06090606091a0d020f132007150c200109060f050c0403030e04020702090108 69
    0x5241d0301901c00140c10403400c481c00004400d030300000d484103024a940180e00e210b09140c0b6950390402030000d008184500080103240890320749510500c0d0303000d080810b00a190402840d511140c00b59071522072040d02901803051400100320342c9083c40300c60704405119140150800742c5040d4044038a400002d001c40c041b400400a07a09881c1d4084601c00003002c54000802e943c42ca0b00c03001a18038a8880110800b8540b01c00480c00e100110380200d600400a800880301806400d05000d002881d1400b012a0510700306140001c4800f0503001d00c4400202d055a49146c200521041100d050985071040b6048011119440c103a0340d544025404210785000c0c0100d14040100042403601035511201e08041400740708a20200384200038110008900400c00580310304107007015a00421801003950201c85c144a41000c40141900b1403440d00d84126410b10210380c18500d4a419104229007038000000c0038402040400d105004840002101910042c505111a008030307071842d909801180c69980 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 404992365 1250 404991115 404991133
    0xb0a0c1208060910120609020a03050d050d1a0a050402030910050a0b040e12040312020a050a060c080a0b0609010c0206040504020c070810020c0c0907052b060b040e0106052505 77
    0x282220303001e42c070403004134034604094140414454024240c000140c1600d60300d110f10002c64540c643c1c680040c5400c01c00300c90321141140b20080c4107900c82d03000c844160b41011021032010a61881c56103032104010400b84445d0705040030301000350002405c07603500c0c0c46a007000d0719011055104440c00f8034100980410114100010322040e1403218085a450354014a807100d0703240180c5040e10296544541c2c2c01d180e4a9488d00c040317107003028403407016105016050100d000c01030598031105a010440d01d85120f1070381c601c860002100c00032001c0940182e81004244c44a6100d048501025031008020700e00701520348001c00c08a8000e0a00000345034807014007446030340d80c1002003550403000700310107504c1c14100161040e00e401c0082c4106005041c948041042c00303001d602a5020b81103a0044042e60f4005d100038206901007200c08148900d18100f0b01040c0c02c0c05040480381505c41041d503002290740380c81c40889803540200420034420744050354a5a821482d0b50a08000c076000e8030042440b05 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 404993615 1250 404992365 404992369
    0x90309080f0a0f020d03020703080a120501050916050d0920040b1906140c1507180b1e13060914060301080c101b260301060503010b0a0c120806 63
    0x66904001c1090a03403010140c200041e00c240c0f00046504e038141c841000e03001480c078099160100c40c4d000281034100101d100702c6240da2001c000b1004600c0101c00b800540d0340c40d0223001d907400702071b00d450082c0c2801c070a01210b040c1c080e5008181581c0c90b40070000300180c89880c2d00d40c2d56840100e0350901c8021030f1007034180c00c0c0f820380980602d481007142c4282d91029801c0c00b0081d0080c85219542c240000c050404040707102c00001e03070300d003185240b0540d4540340d00c82400d0782280c007003200d00c500861002c0d00d642c2400c05e580f100307000c285c9010341c0240d40340540558810a58520000c8a160028410022070b0001c0c0d4500703540360001d14194844142c558140340d091102c281740c03010054000c1c43d09000421860000213480d80c265038060b0356224028040302804c4071801c410a00c6419404810781e104410000321022400c0302c0f240c0c807441011600300c002c0103112503110030b02c203c0000420500040c003200581c074000381044a201c3c2402900036941c1c0c0d5038001d0508900e401c1501040e810020003040f4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 404994865 1250 404993615 404993623
    0x30f01090c0903031d040207060e0d020105070c06201c060b07030503070c1a070e091e0c0c030c070e0105102a050f03030f090706020609030703080a0f09030908 70
    0x9408005000d0040906a100080001c1c9440c0310240c01c000ca1142c00c0801080d07102903505c1d240a0141040d5661812424100701401d103280010201388a41082d1296280c070601c281030042199030380c0c0101c445125101c82e0060003031014501d01c4103200400b4480c450483c40000c6c00c00590494441051907181440729007243c0725544400d0702c0040c1000884000380d07120b0200c0b5444812400d00c1d400b244400d003841602d80701141086d00f8610006810300c081603800c6002d180c400c03e0221618a101d0b81c60168503401c2e1400c0d01003c944001621011404011450018210410090045070705245140086501e0181d10744e10211030500843c00500c56400c200b446c00d003d80400e4140704902d45034401104800e8414801c0d05c031152079801c010442000424000001c035560400100d85d01c0e8100700b0f5940030400410b544c506034a2095440c00078190f40081200f6105050b264081c50602408c0e890030b840b03117a0f004060040304e5598513014070701c01d0707828030504460b00e00035a18101150700345407809241c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 404996115 1250 404994865 404994869
    0xb0c100f29090a020f0c0d0503060a0603110304110310061d0f100b0c01020405090420121b010507050d020705130e0a02040b04060e0103080c0c123403030203030f01 72
    0x5141041c0d181c110540c4400c112150000380304000103948104c040707200700917070041c03804142540c010a007980c1c40095005d0090340c0107540807508401c289540e0641a0200d845008840c0516617003400018046664010029204800501a503c0e41c0c3c240e400d030f01013225040d410010000c1503118205590206c0840d03242d5101e016100140a24105401c003840c0c0300441d88240c0d180140009000b03502c2c0a029016600203007009007155156080c40e103808061482104d981c2460080c5408622009140c05400c80709076411000140000c0e00c0c4600c06600d2003a10308001c2c0d410701001704480b07400207800300130301e941c01e0900fa07005e40201c0e03007402c1c10011000c64003414110320600b096520350700c0c0d040102d1f01b480201c0e81142c0000340400300d103021074090080303548156103401e03035100004144070182d40202040d250708001d03034500d84610000c0080006040b40c003076131103a101890f84054695002d100d00300720380441d00603d5211002c2c6d20305881c0b5a00640003200160400b02c240900c4d46420b400b00b0f40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 404997365 1250 404996115 404996171
    0xa020706060614090f0109320d0b0a020708073002160b03061807090f15050906030402042702090a0e03220f030f0b070807090b0c100f 59
    0x100c60f020380000f1031060b0003080c0031240700f0000d00d003501c070141c1e000c0c2d211500101700f0784c7d2103085d501407814118082c0541540c100d21200c140f445480b1082d18010098103802948042c0000c80740d114841100000d421424003210408001c103c0e80380460355000e00c1a800320035409a5510782642220384200c0c1c0118045000103561090b030701c0048031166105640b050b500000107941e142e84d00c10000904d104408202014082411014010615030100756403042d01c000d0945600d0301503450f140804842c192304810030004906002c2c0400915000c001140c1190008001060340c40c511140302c10140300350401007050a2540e0f11600460501b04000c030391140c4604810400190302c900751603202e105903400506008064442e012104000758840c001410b02c44080f220020f80300c1c9440140c284020b8010394142d4548400291031a1003191080d01c01d004580c0d0f0300340594070709400044d0326080100c06000034010184482508a128414108080d051950204044110300c0c00b44c500302c0400c803a806 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 404998615 1250 404997365 404997377
    0x70221060114060706020a030c2d0e27070e06040f090203071704030203090a140f060a03020c15010f050d08090f0411030907090605030109170a0302070b0a0207060606 73
    0x509440440c6050440340070084699084000c14001950352040c110010310291011a031189055072603800040c03488416210700e1030b450956801d0601c900601d00c003410b072084c8242421014641305000141071018041d00c42c1c59a0303403c0c0107809003034019007980d580618441c030040102040d448210040e1034a8203807050b5182070306122880814040c607000350042c040d00007000c5100248503210000015012104100303607410302c3d140094499115a075624891580031101094136100f40400d1160580010004c0314800100c90500c010b40c1c010818071400d25174280441c6007042020300020b03001106481e4440d9441d0b0500006c1000303081c1941180c0d0140d4111022200058040002c07180220b60496042c519a250b1a00140103441c0001003211039480100510808010009d850b2040e0394108800b4007940781c68605050803202c4032440a44402440f070211515607100d0b50040c807900103c2d00d80545455516194490210300c15900c455501d40e000805405004c0d1a10811002d41120302d842 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 404999865 1250 404998615 404998669
    0x5040303090e06010c0807080405090606180d150e0a0204060e040816080d06030f061407051608121e0604151511060a1d0a08040e0c0903120702 63
    0x706085154041c90003810200c40119106a02601e18010b41e40d51200384a40da0301e54500c0c4c9422150414421640640c07403803400300d0101e04c0d00c030059480ca42d030761030100814100c0e400104264030188042c01c1e140c15004400184039030865011780600905128010300101d140c2d0310500044170020b92000e01504020410311001414032411a901c140c13004000200c550100d0801740702510030102403014180c40c2001c00002c020200c5211505140141010040e01000101c2d13003083c020708a5038080003a00c1004281001c2078184550084c4074040c16030f8a0078000c03102c03074801c04248186d40b01c408001c1e22411900c1c1564203030035a1a070102c1c00792401d000c45c0e00300b040c181510311810300580d0300400410b41c603141c50034801c21005901d4441c0004496070703030801a0340c94005000c4401840760400541d150828501e10004141e070003243d001111628240c41c2c00100100f040c005000b08a08800411059060f550100b08515035450588822640e9900d688100004016040000c02a8000d000c5070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 405001115 1250 404999865 404999867
    0xf1a03010f06110102040504140103030e030c010f030c1b23152d0a0e07060e03030304120c080703080f010806070c0809040b0a0b09012a02041d0105040312060605040303 74
    0x41c600446449007050140c41e81d2031402140a40180c0d0001600a841c0100d06c80c020355002200e0b60480e8007039102d0310710601d00c01051540300c0c0c1040f0300f014003148580d010984524801e501400c4069034910340342e0072482910f40e902c0c620064104d003d540000c18062100d40718900c80e02101691142c4000801c1f440342c44440780041c2c40001080100303082c8190703a140d01c48090401c2d004249102c0d0151002c070303d1616408100080c514200b0521080c450035a010036030740e000d0280c40d03c1e6094003d0085003580d60715651180783c149001d80010402c1500d0307890000155401c0003a00d45940302c0d854140303070361400300345a01d42c0c01e00590240c01e0301d5010b0f505208550f80c10180814111303800a484175643c1805d10f000c107010b00842006c0d1600071518071030001d2070b203074400054060003209a0725158694006512801e94540305480000c45040c15003454005240551104044441c1600002048080c220b070032400c4034011541500031940003420200901014442c0401038102070610604003411914 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 405002365 1250 405001115 405001139
    0x21602030c0109031a070507080c011b0f0207030b04050307172106180426180f01051204060f020304050a0c0e090706050c121b0d05030412080711070f1a0301 69
    0x10100030380e00c940411b106ca8454012651915004054607561314150840c0710300030a43d40d084080c803142010002c051452003404200d40d141d01641c000e091580c21074a0b0803100c2d070300c0030300210707501c2c03208114540000d20100079072001c0c2440030b4400b544508000864414141c0c4100301140c5900d1500100005580da0031500459543e40f0002011103a58500d0300b540c041ca00803059014801ca109240600780c400c0c0b000508601114250004480f002107003400303519480e251178640828014010301c0c00c2074200d40c500550160140c1c2d0045024035050140c0400c82e402a1016920342e004a4940300500ca00f003060407004004602d910070b42860071410403503c4039128050007040204c0041c00d6540e1040800100044003400303418643d0b200710501c42404000d0812912000d1405000c03d0f11031030500402c16a407042e5041178050039885080c0000310f9407a178000707103134000b400b907500000d8801580401880014000c50290700a0311820007401d910081491841c80a00c60003c0006000d20380e5406 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 405003615 1250 405002365 405002393
    0x10906050307180c12061205010e0f071a0927090c130b01030b1203030403080709081005091609020901020f010203040c0e040227060108010902130308090a0801021602030c010903 78
    0x1040c00030b611182d43c0400c03900150100000c0045601b400000b05420b000d1102801c2041d201e82c0081120840d030f00000b036111555000315410540120704104140c84006080c1c3d4643c0061a2a8070300e814001e50000b00d1031060251b10141c0025070819030050000000c180640290f840c0d0300602c160300070b100000700035044c07a95070050080c1d203910700201564001d80040801c000c1c010b003030450f202c12800702541d0301c1e08111004d0b0002440000464412809212040140c6004001030100c5031071a8a1a0300501005841e212203071203100a01e2144013940490b0304060002c2c1d4201582d03515400000914201100c002c909843e413040040c03000140e050440a802c07940c1d6100595a559141d0000480400c0300303000c00d80190102c2e0b03214400d0518000d00541c410f01003600e808401d83d0300c95940d202240148407422425840c5500c040c0080b89061000d083c000500400d0b00b070120b9101c1a40c5400c0ea007299075000e0f40c4062441c0418218501809801e051400a1134400c52840c0f46840e5060001404 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 405004865 1250 405003615 405003659
    0x1c0e0618040e030408010603080315100c02010c111012061a0304060c030908180108010f0b071b05060c01060504140f010303080604181142090405070503010906050307 73
    0x40b80040d4030040c00384282c0d0000c10360140200841c90b13803400c00f100c181d44100d41001da140d805460090342490100000c0140d40ca00313a841042450b070540c01500c55580301102915078110018445106580f1068000d036401c00a82d83d1803c00c40e18007910406440d42e42c0c204a045805060a00c8260b85003a02620351103504480c001c01e03048003003101a00102640100a0b040c1c0034001f5034420f03112050f2401c0701e0b12503403e80e500c0aa070ba0381c2e0b02c40c003410724440340503401014a017003004d4000b00f042010413a85128002502c039030400e59410024180e0350101d0800d1400d45d46805c1c1c10851490070f4440c0c24113209007030710400340900d80030009003211901404010144440c120120300c4980302c96104260511342c207200550610341608200101c0c141c0030380c00a10801940740d048048131184c0141441c00740346c0c42401580200c61003941e07246040303042540c00b500314040c0f180d5203480d1790724010f035409003600c0e0b210300da41d0b03504103a111400d0341c83c5508414000c0c2c4c040e01c0208410301174505501110303944 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 405006115 1250 405004865 405004871
    0x706051503032d041d010602150601120605120a0b0a09050d120f0203010906090e0a111e0303070b180d090509070c060f06140102060103020922051c0e061804 69
    0xc0c50108034503040400fa6262080100300419002d02d00c191001d0045842010071050b40c1e178a0030700302d96a100b41130084c504241d12002040b80b075401550103810412a26101154117501e580105900d4180343c000107002d94020b09010051200070360000343c0000111009006c07034400303511001d6440e01808000e0b010840c51800f400c00c7d01013294000031011100301c00540d5a56582d5044d44054412801451100c42c5011040442c501c1d000030000141ca5004180340307103201c5200304014881c0c01c00113007104100400002c08a540d5018402080b51910404940c8098140035020009050b58490140b4039540001c8020a1181d0091340c001e089580c110385000a41da03541c40111101541d20300000d094074180342299031099469002201038900c3c031080189515001001240d407414281320181d00300201d04040741d0407e800c4a00c2d031440e031100301000780c10b428150351034a140c0007450300e81c00a01c01802000e400c045500100942c9543d070112035850800c0d104842c44c1401d420008a06486660303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 405007365 1250 405006115 405006157
    0x105090703020d0c0b03041110050711061803060408070506101a0a12290f06030610030b03100e0c01110c0904020a051e0913080403030e0321070605150303 68
    0x641308004c201510242c00980c0d242d040c2840c0c44e081400d50b4659a51040e203001d0400c441040c401c0043d10501c42d0040c9904030550a09002c1c403045610500b81f0398840c01c0110418003ea031410410b442c001c6100e120a15615a0700e810502d081943c06011401c0b142c1d8000c0003003089111107201c2c206a2229039599035901c03c110882601e00100c0801004841c500f481d0b200c0c0558141c000326440581a104114005400e1341d40410101c201c2c1010950b610420520104043c0d0910b00d03000c1c43e8601d55401e00207056041c1d040041d00e0880000000c10401d905e4078090302c415101400a240343c1c010a00703102040a18010100f601d83d510902014050300c80c05e0006425076507060304510050001404840c801e42001c40a1200c01c60010309035801060007201140900c0307c4810191003103500030441904090031580c049030030f0070b800328106a0601c00c01c4040401c140450785592407160000c6030381030b07541c2114600001910700081c0813404003540b50103004100d480110407a00b90050013555110020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 405008615 1250 405007365 405007373
    0x1030605185101050d0b0402040e190b010e010c260c100e0a02090106080c0403020907033e0a022508070e07020706050c01181b05030105090703020d 65
    0x1104100740044000b010004941c0c4000c00c0118149559140740c044007488041e050b00d02e5141a1154501070004804200300014004d81d81d00034000494000e101526156440010780351007002681d40d05960005001c207901840c0035441103605061084c20100585e076213490011344a245010406801031201282103c801402080d100c244da080c40030001740c40e4100a120a50b80700781c20080902020b181420018442c00005040000158000c04402d1075030300b024005ca0716101c2c040d100da44001c400b440040010396a00e00300724465484c69400203114505001180101085410504540707048019214001c8801000c2800340d0300b00303890b42c0c0b50b541409a204070b203404070903e144c1003828020b1540320140f1030f402032aa001ca59600d01200c0c9025200c00070203480d184180d400401680c0003840800c1700b80d00030310190039075003d040000903480c5039502c030382141d00c0d0602508481030017500703103840503e0032060070700c1000d4a4268020821403400301c104039038400070b501000e1b2040c900802003100708 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 405009865 1250 405008615 405008641
    0x907150311040b03151305070306350307120503060112090c06050c030c0a051518030409050705120f0f090706020325051207120e010e0f24090f0103060518 68
    0xc1798024051800954024111000401c400e5644d5000a800c008001513007222034100030054001d074403140e001401e411402100000c650850020060205202c00000306001c0c050130020700b02c0603100d080c0d4a1a180000629100600e860418010f2901d1858400304200c604d4403800e072245c0d0300b04075540d40340101032213245000c3d4001d540203501c901d13044001007100210f02e59a154401e41c2036401951649410500f501da82812070000d9640103000401c648806a005260040c1e0a82440e030714044e042c02d084010b01404030b03444602c0050003410b0101028001d0350641c1d00c8805500038040050409000039100d11603800602648500c003e0041030030450038000e40142d95100c0d003120618115820a0800c80d041a241542e03490307031016100d00c009020342652040a40161b580554131040d032400c000014502d00e05c03141d0080a04410307441290b502c3d03000c1026060441d020f894407049140c0410000400d80011141014102301042085032181118103403000c501c17000b889103541d1500108501 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 405011115 1250 405009865 405009901
    0x11090d050c030c0f180c040f0e160201110702091005060c0d14090901030b0912040603061a0708040509130501020a0e12011a10170907150311040b03 65
    0x1004180804140410000190181001c5020360550b0007981d600001c21144500c0b0340380b03080d003140650402070343d40294070503944d52020a8080711400d190b2540014000c204080d002082d1042a40c01070101c542e1040464119101007440240303c1c4102b0243e01000900401000900a85000001c1160070380101c80c5600a4280030302002e40750400811510760340c11111240c03002261442d001140703030303003281c03022114441000b030164105a4a141e49007149d8207001809880706001d8003801002c5410751200420003040e0300c0c1d8020411034284180490590003542480c440b440c010040f020000322600107580481e003044030318079496601c102c24144662680c00d401000c5520010b40001100d8024006203204142694100180d000e06d040d060700f210512942500d0701009078104440510348072820003a03c183c5882c00e48000d10036a00f030406614000d03103550000d50004203060200300c100700b40100803c40c1625083c06a88210468000710348141c0c080d03204855000400103003403480302c0c8002c0036 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 405012365 1250 405011115 405011119
    0x21e0a090f0f1b090b090f060c010b1e190e1501020a08070c06030f0c021c020a061401030611030c030402102105041202010905060c0d0605060a09030b100b0d1109 71
    0x898400f01540000081c04003075010003003004c4500110301c00c446039040d120304920160810417072100080c10440d4039006030400d81034640d2206110040c640b1250f281850200c80060300b001c20381c02480030420019541c50984c501c60403027074000c01100209601147d0002a400c14911a0589490042382440d034030140140401600103007a204205d41545504104c44496500f081034071100c0840006481ea807444040c0103901c80042c1d0080395410706607080081c0306500480c0d04070356540e911582a01ca1000d12484025100310040081c030515000308003101d40342d011340c64518070b4154062246408087d02c0a4040e1541c1c240100f840c501440c01d82d20907503006400d1100074156144d4104c080c04007182c04440780d102460021440320f005004683c14103034050050402561030900e0102c5981000e02c2c00c51155840e040d00151a4444000074415018142c0e03c10240d20300358140440003c0000d040b009100c2c50426040040c40e2021040d61030401e11b420300450710000605d4070507114003400c1032040d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 405013615 1250 405012365 405012371
    0x2060702150d0c091422090305040302030606060703090311010c0804122a0303030f1808030405010c140304420f0515091909030c021e0a090f0f 63
    0x1080e07110480250a030700a00201c00e02c2103000c458012541064148203940090500540600d49403030b0103126900c451041041c00b007141029010744006076252600c0c150041100000c0034415404c05010700c2d54000340c140e484515008a0f9500204001e106200207071454807610302e603915587c8504001200c01e600503c0c0c150b250381c0c8030b0b5004080c5420002e002c031520260301600b071504442c43c8049401c51440340c0382d03041c000ca02c2c5071003e50280c04a5400045102d0fa2183e0300012000c600340c0da007800c2806000026202c1c903003490107900b1545101400024011145d111502d040094030071241e2103a4820248446000c500c080810000061000030304020084006c100d5040048504002850100c42c0140035080c19072490904a403800c2e950f010700c99400d891a40c0050500640301d54000c0400a00b40c46610302590070303141150b020040480000b450b907003455041d8030744000301c1e00e51108d041120144559054001030a0410a0304c50108034644030300d01007041c4982640b03c110300110080041c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 405014865 1250 405013615 405013639
    0x1a0d050c13020d1b0206060a1a0703050405090106080f0c090f12030d09120906180623040e040c060e0306070320030c04030c1e050420120402090105121902060702 71
    0x103440030415411310200180301d108002034161408640110494004124070700d1240741020702a4450341c400d034015800e100080000007083d803142c130040e60007410207507603c40107800c198480345007186014010306100501801094820350f00c0c4484c090005004841004451540744100307821405020f0180c410b5a02e013641c0c0105020a140c00781c5881d40807507880384d110340e84982d010f690300010240d0070b08d803c5a00410070301c030307440c0500811820480c8505151110341e2034550620003903840390304410004512002031204001e491140480500344500b020341d80d01b4688070100743d951030004d1070a4100342d10342c00c0d00a80c41140c1c0d0000700c0c1c100d507045003069803443c2c962181d8005600c10700c4112801108101c0000f01c0e5481d1140c186901040390401021443c6000d0410009c1e1420174411705070005d1249000c8014200a03008200e42008101c0c0c0404a180c41d00410500a5050384001e010744142c1010b01e201d582c0100f44030725072841d54025500c0b039403002d0011644a020701d17400290801010819 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 405016115 1250 405014865 405014891
    0x605120c030f03040f0b090d08041401090e0609070c0c050a140a120210051e0403062a050429120901061505030a1d010f1a0d050c13020d 60
    0xc128010305608481c101c004450469540344114031404500028201d030038000707030203450028181c00c60000c00321643c80d44140c44054690740a6409280e8a1a0829109145503048a0404014205c01081007060300d00840455040d4034014000800c1100240c2e04104208903480c1d003801402d805000441d002d03443d19510180d07500e020358030a200300c195290009166140080c101c510315800703031015001c1a50310b1800d0300c441d000310110400b403000d240444180e03848008068002540a09004164054090800c8212907140b01c14440300910400c41028055002411242202c40400d049040c82e1004018416424100c558459800c1000680200702112440034140545054402040002ea49403415901c2c503103041c0300100851010b000151400100d54040c0d4240e11140f9001c0403031501d40d110140c01c5900006014841994a160101c028000c52500100f0044191001d2034400d00c07a8039001d9a5401c5d41581900c5030a010110b0a403601441d01610380151110005200303003140c18031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 405017365 1250 405016115 405016123
    0xc05070915080304080a12020f06070903060c0201050708070e0f040507030e0708070302010c02042309070f1e0b090114131503020304020a030303050705040b191b03020705060304020103060512 84
    0x101d04840211804010a81210200c200e40c01c6410300401000e00075250b540300107160040300d1181041d8092034115040000092210318421401c136901c0340f00103411440c0c008100c031030001c2450f045a25000c20482d010744c024801c107804c041e07d828101140d0303042d080050407001202c3e150b40d030401d080105200c07411340c2542005041c00f80460664069540701e00c0321640d2184030f03100280c006100d0300100005424140d11110300d03d58007204d000c920350300d111401170480c80c1c20350703550800c2c0d44645000c000700c4c1c907181607200242444404c4850a80070b0707440000ca005030680a10f5514110000e8080d425a002d14200840c54034800b0b41d058480a02440d8011816141e115401c85801091400c0103410300c644200c0744920340c018a211007032030840e10308800038130303000b0025002d20100b000042008009a0040c109207881039090000b464a00382001b4501c3e0812050300c5c5140005e046400000b03034010a6410650342c054503260f807660f607503000480140c400d039070140b500290100c4911000300b50100d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 405018615 1250 405017365 405017381
    0x9170a06111b120d05060604030204021b010e010b01020a061116111e06031807180510060e03120c01060b04060e09060f0d030503040809060a020610050301060b190c050709 75
    0x203030502e5805155680050711450304801480c1c3c11542004070b506042d203154017040c0c00602c0035001509054407680402c00301e81c0808000c802d12040300c03452200e03e510901903800d0102c9480024418400d141001035603030003d044d002030070030740c4401480700d001c0100d2050703908000301a4074a0b96900418101145844849110070b4040c0303001ca0041c0350390602c03103104512901005000c05145944040c030319290788907001c507051040d014071640025048030003440e0b65040208001c0015403410144901c12455502c6e42c03021b07040c040306c0911109150f0780420408003402200c22038594480b84400200d0040c00300390071030b4580307010106001c9507080d40314050b9400f044059415038001c2e1504002c200c0103206a40c0f00503441013580d080c0d9000644503102540d04648181c601d40c0c24080340c10001449038100100d030a005034031580402c12440a4000c0701d07401480309800801030076040c9031805800d44903a030216544200300410262029110320000154140c01506641d41d0507140d40d540d5000d45610 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 405019865 1250 405018615 405018637
    0x22d0d090806071e0c020307030b0a1a0d0506040f170f030403121a0105160b090a050d05030c0909070509030708070f05060f03060120100507080a090309170a0611 71
    0x102000036041400f56020a02e20003070000c0b48001842011340c05c07200d40c04d03409000ca070140640400003000400200d980c9004481c080004281d28201c104460035144e442c3c0c5195108400c4100e809000c51008a00d83d5002a0440880300506401d81000042030135266400842c0c590700240e80320132803618401550042e0720075a90801ca0f40c0c8940900d50585c0c0d603c00302e00074580c07000032141c1c1ca01c0d03000c0d00003000b03804a010070248050400303440da100d02c1c50084980101c00d411a044080411406110802c800c04c8103041c5242503081c4110901c5607401a407d4a90181e2078900104003c01e02031010341d03051000c018108ea590300c1e2180a807a84034034540c401c00c2000d030b01c0e8400200306490100183d40c5031410100c4890705590b1140e0044486980142c01c0140303003190800104080901401900d280515049000c034450030700480c001e0030400000c0c2030b10100c500d01182d240c002603120b0b1501e021180858030040c866001440928100480e0b1640108203500e4048240c62005000028100070041 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 405021115 1250 405019865 405019873
    0x1807030f0209360111040b0406140a1205180f0a02030f0304053a050106030c06030905060f07030e0706020a1101080103051905010f0e0102030a050c040501022d0d0908 73
    0x90242c00006092030350f852504940c4a10002e107801c100d40c821100d980e10107020003c51154900c40544109034407a07007142001050000d800e11100b40c000340782220f142d04108d0000c2c41c1209802c4000c046142281810b003c082d21a400b0400210440398401c400481c0c14069480841412030110b90318809460124041c1c014801c00342c18603007012066804661024016420f514001070410140384007040c1142100c3d60b01740700740b160000c5010207400c000e501c41e400000d400c5e415400d103400320341c2581d4000000c050406108500107a004142c958000740c140c1481502a01c81d61001e03005480c4416a0314891302c81c401002684503030025016507040d001d110b960014100000045503600001d0002407d01d03800109040980400000d1000e0a58052000020350640f10108001910507000800065030b40200c02d11203081c05070b11805070010400142c8901c1c0070f10f003000103034440c58641c89405130100070258400b41d00c090103006803025032802055034400c82c041100074004103828010b600701482 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 405022365 1250 405021115 405021121
    0x40f020705100506030316140f0607030b0402090a0b0d11031924030b28050105101706040f0915020304051603030c0b0a020c06190b030304120b1807030f0209 69
    0x142903c255805000003a000d5031034040564146030f030000e9420401c980000380e00c5070420340020148551003e0305072000c06001e49040441c070007825151425070745e51040b44108075100e606e0751841100d50840e107015145940358040d90380d201005005800c01d118508000004011007041e40650a0383c01044590080011201001721940039600c4c44503c2c3c80c0c0141d1800d420b01c007003002504660f80c002e810782a0821820340512025118043e4510500c0e03050703440e10018001442c4c03d8052005000481c0380c11040420901c00c0541d4042010300030b1801699140b921070064045c54004103a52504006241d0000501d42100ba0082d401110240c525004040d0580c511440302d032030031000c580d0580d45000c1461011f03203c0c0c0100c2d40001d03201441c0c00740d08014034125007030284000e510550680780c80001d0000c19a403030600755240c071a1814881c2d041000140300c9049000c540e0030a032500042802b20b02c1d502d445503465481c00c800e581480d98454400008101b1040107000d01c0700c80e1090b6040c840c591 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 405023615 1250 405022365 405022393
    0x203160303020c3009030f1b0a080f06040308071202040b070201080106090308040e130b0f01060e03033f13060b0f060a0305060a0f0e0f011a0a050c0c040f020705 71
    0x40100480001c140c0c500d503e403030130f80c0c3c41000e00407299000302503e52039001c00344441d08e400c01c1003511240021000340d00000500e092150303000200104805130107060007641c000c9894100c010801014800440003050029124030a00c05007410700d41790455590781c586003c07840b240c004800890002c0c0d02c000000c2061841f9100d40d60440368003081e050706160030f01601d050b884000a040c2c801c51440c28004402203580721a02c01e00800044510546950401d02c1c0140001d4419074468040c0d030080005000389440d8ac0104800c0f01d1040e11665400708585d01c8a020950301d11884410148202d000c1c0003240f0521044030441510a0200700443d60742141404240d04079800038651081c0d041c4540c2504600a800041e8086030041030090015140e02369481d40200b142c000184d66410300c42000810000c0740b1400f40906034600c82d4901d0182c44030a12078891007001c0c0920100300c000b080c3c0c105240010001610707030fa00020800e111080039407640700002c0d0011003040c0c51512452076103c0d2702c0c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 405024865 1250 405023615 405023653
    0x2010b180f3304110f07110609010507020d050c04330e060402030403230702010212250804090c1223060105130b042606090312070203160303020c 64
    0x1c0c1000000c001002e92941000240180c80d9180d5504541c4440d52001200813101c000d107054242c55542c039071161114207240804e9200140f0890241000300a000d01c0760b80c1000c2500c424079412155030f09040140c0c070f016410301a503071034031036040740c148000540c0e03030310a40030030311042c00d002e040c43c011260300801c40c421f220390b03c2d00c0b510a510f100d0101255403400c01e5001950b005001381802c50311002103404072030800744e0700545000b00e03c82c0407038014110369060224058400c00c0c291001c0c00c1100c014914041c08944140c000d58540c602c030300c41c800b04a980c5080c1c80c014440c80300c6c200403044181d4006805140402d0703140c1405450030700e520741d9400407140002c0e414000d000002c140c0f65107060064442e40e1258030310514100c15041c000480724403120080002c1c010007403803130361241c00000505201d07400c14280e442d00c0d0b0300481e08211411000009443c42d540c020441308166403100482a4114800e1448016600c240c103007a102c18150180c0080070340860410480742e44002d4817944c8500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 405026115 1250 405024865 405024901
    0x1f0912080c0319020705070801050106022a010c0203150a0501030b090105090d0f0e0904050d140a02030a0804030c0b10080d030b010903020f0402090d060506090c03040203100c02010b180f 82
    0x6404144041104405044401900390f007000f100103240c580251103040c030300040791f845007442c0d079141c40040c8096032b4144100120203181c5c40c002d80310040401181040c85188203101e5042043c0c1104110555404010384003140805618100c000d0800311581409040240000d40e200320b01440401c43c40041407082c180319410420240ca9003030080c01d02103506ca408241e92508106042c540800310369540b00025005506c144010a0090344001026100300381e03003402c100d10310350103000d0401180d8000c4211070101040340380c5210140d60f0303490b05542d113460082002c4d04200c0a40d0030001031500310341d07401007500c0c1c4a808980a49004080407400c0d5803000310401e000595910040006041c46036408240303c0c4010800350400c2c80c510003050402d003801c042694405d07281d206010482c1821302d01039802c1280303401c2141ca186000d030082941e070684016005c046940e2191000c40380c51007036100c5441100c0080441d2040c40c001c2d480c1150011050b10040400c0e0405c2000c524030107040c0c1c40e50a9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 405027365 1250 405026115 405026131
    0x3242007030f0f0c1209091a03011503150b0d0b0901020c01050a02090a17010f14180111040b071b0602010209010e0a0503250b030c041409040206030a0e1f091208 71
    0x4d59002d50b12209800340da00566824071014032004656810103000f91503e91600c46141c170700c00300d24601003509440c0c80c448a1840c4082e01001403001c200840b1540b460092a40800300e00c0303449001c04544041000d0310050b08690341d05040c0300f43c1d0f92040d001050820040c1c0000d01003900d0340c480940072071140100142d480303c1280410020352002c400000e8a811a1100016201c007032840c0f0801540d0700341800f4050229100d08011081d855502d042d08000c030940020440d4034207080303010000c3d11071401140701c1c00f2004182201000403001c0c4254144810603015988580d0303454019010b0340000341c046020a1040710444100d0900001d8401100d000138002e080c000c80507810408800c4c4010300d103020b080300e184000300310007050701c0040d401400524041c55840d454401810041866040e409124142d650300f0300003d0f03070710301090702e402c14003071040045c01c0c00b83c4183c0b092418880a13201030640c2c85100110800d42c82c0d9900001e842409194440748101d8910b0302201d0300b12044a4900d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 405028615 1250 405027365 405027377
    0x60f011814010e04020c01091a070e0105070f2f1c170d111309050906181501030c08060c040e0a0218090f04140703242007030f0f 57
    0x20204000e060020340c00c18060420f512211000d00201c1d00346d0f032246c6601d4105a45410340301082000d078181920080110065625040c140b11000400007801c500b1a941044004a8144140300480c0c035021201503006240425066000c1500c490003024685580c2c0142030b00c03468802c0e181031a6403010702c40c08004000c0c000da5000e960342c110b03001055410024a064003031041040901462060300406150000050f40303420100c441e040041c04250400700c1000d08007001d10005030000141c258015000081e00c00a2009a42c2d039580391021072000c0c1e00600c00c0f418000000d1040c820100001d0b42c5500301500d200d50340d50316002a10344214413403807680c4504400002d1600c90140d020303161906040b1031000e0440103290008510a00c00d03644221202e20440030309c010060741c1e44152030415110800760051a1540d00e4891300d686c4075902c0284141c2c1c6c003a44070100050542d1003840c00000b555100c6c000309031340850301c01c039a400a40f0101d0206c3e0a2448480c640360040d18807000c003040c11b070741d49 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 405029865 1250 405028615 405028619
    0xd090e040f0804050a2301030e0c0d080d02040f08100905150402060702060703031b08100302041116031205070504270b13090605010e1006050a020304180203060f0118 73
    0x5400807400320030207841401c01844003141c5503440c12038600042007080c803c41001501002c1111026120006540c141440d1011210401c0c2020660040e10207088800c441c0d03004813403d2041c080e11481e20300402191001501144003207603031141800355441042221200803034400800c04440300c401c00a041c0350b0000c1072114125842c036807515032003032014143c1070070810983cac003007607198001050444c0030985950010b03005800da0301e0304444100b264a041c000c03030704100e04a0000101c0f50b0102030300564541c0b007440305041c620b00c100d84030395941da4010a00c000c89824001c06400b0b0f4030240c0340ea498244400b00c1c0e0481e00c104140d40545040380b2144401d030270101b020f088151240902c2c00352890b22140035101039582e02e01c000703083e0f007114800410721504600e40300b02200d90580090520180d14410b01c0154001c682021042d0f44041c14801d6540c98410016442c40c01650301640c401604503102c0d900074541c07500558050041510501040b000f411f00660743c200360f10707144411500c0725840c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 405031115 1250 405029865 405029873
    0x9011e0c14030703110706060e0603280503070221060705030601050301060c02030a020d080415020f030a0503091203090109030801060c1a0a0207021804030e010c0308130314030907080d090e04 84
    0x2c1d030308000d05040004010324185000e40d4030b034000850907100c295907010208510011403083c23030380c0b00b18224090018000d0240400c1800c0c40541c143c0903402ea01c441032030042040c00c10450340010307001401c004007120900b65022044566803051000c034029900411004d81c0107606581c090300c070584942c3e0560703081c20000c6890b8800000c0030307030b8184a1540c400c4056202c04c40ca2008060013020000ea0350f030304208040151400c1c44068904640c451726290284490110944a8015031032400c280c0c2c1ea1074150540d841d12918042c81c00090200000b0721601081c150301119000313102e5207500f8000e03aa04c42095610f058100d02c003a0000e010380c074142002b8807070800e0882c2c0c003c60018005040170000d40114810941401d640000d0143c90b1062006040d00311020b04404002441c1624284449a90080c16480060440584a82c0c016004c07030070540607100b1045820954240c0b00e0301c030b103851452555651aa446400307001d02415503200e01e180c0c4110f01103c02e07644001d038036200715200c59503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 405032365 1250 405031115 405031117
    0x10e1e0d0c0e070903020406080f100f11040b0d06050904030f0c060e0d03020904050a05100306020702010e0d0b101e1a0d0606050316050306090103240509011e0c14 72
    0x60101d526100e4800c010504101055206014000c141c1d5041c2e5503c1c1140706110881d07260350040e491603030164101100c1004009518949000d20034000b0602024030001d83c8080e040d83c1d200e40007000c10201340461b050340b403000a0f20301442c82250038405656644240146254281c4002c0c1c0080c2a004405d41064081c1082d103215a11a440000d8130090300c140c034908105494414100103600041c80a103980b07402d024003500481c500004106900304908901520b003041d202c01020a40c020407103000396030103126903160540700a050b600c2c00080601e0003915150040305c1c0d480c1018100c1e10003050b0402d40ca002e0008107440c1c2000c0143c100e00b131100000d4066510100701000c0c8078100b1916851400340d002d800c0043c146130312295201c1c1003468100c2580c1407282e1081c01000018010009107a031448503d9044982000341c0b00908100e4600d10404021344d00c40401c0020700700424480f854005510000448856100d044d01106c0e4030807898042e960110104c41c0000c0d25140001150502c0790 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 405033615 1250 405032365 405032389
    0x3090402070f0c0632031f03120f08010f080c1210050109090213060b2505150f0a1512020f040504050303150909030403030311070f03050a1d030d050d0b06070c0302010e1e 75
    0x2030403130303251f90303900c1d91110b103071002400500300019000c0e908541c0f4150019140c40c003400c000b10170110340c1c0f41414980c96a0b414550449403141491381d4580d142198140001c000807088080c3c144201d6864580403800340bc0081403c0f03020300c00c18114100411454420502558414030003503240c03443c034031070404405482c0c0042c01b0a00c0141f1310341c680003078010440d1042032000b440004045250154041d002d41000800c0d02400d02e0504400b081601443e0480708151403580401e8910794080b0b001085045000071240d07904503207800e060100344000040594480d43d031170a0075840f044030300b006110812509940c485001d074000d02052000034001d400401480541d6030396682000c4440e201c00e0310f2400d0301101540424000207100081c2640088642959180403030082501007031480825501c2d119840501c1c00c0100c04203011000000039003102c022190f00030700715500c48080e41050080340d9000d02c0228042030507d02c10304000e0134048101800940d01754442030303543c0d1404041c0684000f40ca = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 405034865 1250 405033615 405033661
    0x4241b02090109020327010b010f020706050d02030a020c1e070501030b0f09060303090d2a0501020d081f03050705040515030312070309020904060903090e0903090402070f0c063203 79
    0x6c0401d410b0184000c50705889461128004203000701484005400f00410a00e4070086421000d418401581c05c0012100c0d0005801d000680d00e980c0c04404800038080c0c103c0e803070b11038001c000003a00c10a0450381d900080900710070641c0c039034507915001035084600d114a0f580d000010344003144900d242281c01c80f580702d0400380907289030640c1007000032030084441d00b044502e1480035001c030900107220315021050510a0440c1c40400d4100070020b99104029a01001000412000120100c4c042c0008103071020010802c910a40d48a03e0255124080c2e4091980a0f514210020b40b180c0e03880d40401c415034501070050f610f01440c0c03101200c205d10300202410305054864a8203401038480f40407080c8075074081c54000440081500d4001c2003010b86610440300d03d403c620501c8012000481101d1100404a900584c0d86203a45440340c09007842d000f010348805020080096405e420030789040103c0d41c0d4052201d55006205103032007802420351001e51310000300340300064200325075203c220303c1c1001c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 405035971 1106 405034865 405034891
    0x140a1d0f24060d0902090c0408010506060a1b05151602060f0f160210020705011d12090108130c080304091404120507020604241b020901090203 63
    0x380c0c8600d03124090006065440f03244980c003468116901800751036451400e614013550640003441404065401d00300050014070b001002c5a00b02c0c88661075a0020f6420881c0d03080b0b10031070052046603144295003140925426100c2154460300c1c0d09108121604010034000f4103254002d003011440350100f9051000d01d07002d00d00301584c003003071000003505000c0034220304a00d428410081e00b441c4510008400c400d01006400c41c0e078492070101d40034606011603989595480e0003600307003007100316000d0005490b29849201c002d5080803003440449580800b585a1494201c02170b40f0070105c40c0c0c0002020441e0b0144d900031404100b0130903803544428134041d1078844209085280c000d0400030f00159500c115650a01543c0180c80811299008081080041c0c561100d2900708100402c04204481e00318103900488031100c998040e1940c40c039640382c444890044e400140c01101d2000d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 404856115 405035971 := by
  have h0 := BRFrame.cov_init 404856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 404856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 404856115 ≤ n) (h2 : n < 405035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
