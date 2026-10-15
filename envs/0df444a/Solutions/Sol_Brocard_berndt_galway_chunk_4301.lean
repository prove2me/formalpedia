-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4301
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:10:12.893641+00:00
-- url     : https://prove2.me/submissions/75dd8763-5bdf-4fab-9ce6-59c7f8bed66c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 773381294 ≤ n < 773561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 773382544 1250 773381294 773381311
    0xd2406030b030a1718060c01050a05060904081b0f010f0510050405040c09050a0207080a0309030807090b04050105030901110301060c03081e070305070207080d020a0c080f07033008 79
    0xe1412401498001201003ca55010240d00780c0005010001c80160300310041d05100110078003681c0c0003990750348000d06001b0081c40000181e030f28040c0c554030140c039400303843c0c14001e00302c10080c04041410b90f001c81d8907a18051507101c80e1000240704440c509420004c20290729483d2000410b050341d81c5805c024010f030f03800700154070620741315400c000882354103440080c641d0709200b500b081803a40c01c1d0005c0b540320064030001802c206068885c426668080c440304c00c0025940e03403401c0d00709070f01300082ca42c22030740d00d24280d4103050904000312202e114500030b550501c9401300010341009425041410000e071276200d41512075039615805814500643c034102c0109e802500020408000c0d203102201c800002e080040054880c0c28003640245005451401140100e0002059a02c0100140340391008070350b0040c00c03041124280301c9500b14564100e080d240d001010202101d4000080040959800c41c130188141343e4020000034640100d075079024004155505441101d42c2c10111080c802ca520 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 773383794 1250 773382544 773382551
    0xc180603060b04020a091e03060f02030f13030f0e0307120605010f0b0712030506040f0c0905030114130b0601020a060507031e0504050601090f0b121b09010806010b0d240603 76
    0x600b0400040c0e010b41c02c001d40000300c0041082004080145024481840e0307510200f101c1d42d04c9440d4081500d0300800c203004a160008107102c4002c00403140c2035030100c544034a500c0b400016543c01020500510f03550000c003c115401e009196600380b269000401920002d00b42203001e03071600d10050b1500b480341142c00286c00f000003820201141c12210a150b01128044000c070600005030000d02c40501000d400c259902c400122003110352043d41d040d907119449448005203003c08250a4403015440805007025900500455074480f2408050203541301e222454985d0740c0c00c0040b03151803003640b400740c48107080000b0701c0081c0d80c1650101c0c003001c6034005030070b9a810980303450000341c070b20546d0300070031585c4503000400c410549980903035028102400b01087c0d01c00c2c1200000d04d84626110040e05513089480d50110201c030756040c0c00c1103494242c561035203540c0b4100720f0743c1e115581485903030103130f55000800425800c0c0366400080220000560b13858a1410031040341c0201c001d500840d07020070310303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 773385044 1250 773383794 773383811
    0x9021b0f0a030306051206190605030a06050108010b010e18060303090a12020319030824030d02070e010f0308071b12050604030f08090706030218031905060a02190302070c18060306 79
    0x200909500006d40c441801403c56403900400e600f0f4400c0c9180568003420750740d010104890b5400d100312044035005150100b001c0d4184200103007150f003040b40c0d043c18401301c500c8885458480320786400079900001c1641c2207a0380c2d90800f090a61040c40c09030b03940b18a41e800086444e076810900f428542c2e00a80c02c55585140c60001216110300130311000d804141610005410444c1d2104801c1c80140101103040e402c00c8210701003464120711840c90760258014000c240401e0b815a2a240e004146001805074400d00d9520b80413003603c95103101400030303040344107030072041c9240350720120050071110780e1120309031143c0c144203440e070a054804034001074035000340700c440e2842a101c0c50b02030110303000a0032506180480a4009500902042d1030300c0615050a0b0010341e424482d0980c040100310b00081c0c4200d561070070f982044001044515110710600180c3c40901d43e82c828160b031000c03107040c01683c8500604110000303514940c4440074091310100400c100c01700580001086a10410052140e41c8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 773386294 1250 773385044 773385049
    0x7150f0c09050907090b2a0c010e061b03130e100302150d09050105010e1e0723070506040302010e302107090f05060a0909021b0f0a03030605 62
    0xc040031100d200207121407509205515144803480d41100003400c00c15441981c60300b00070015002918000c9108402c25466224190036030034031001b005038100030704481d5032086c001070545c0d0204442d85000340b00c080343d400641903404001400c5255110708603070b201c1901c040c90303449043e60380c007403611042100300100f4581543d41200105890780207000784200043e504c402c55480d040b01042554082d211101c0e100030031420710443d40078100000044c009483c0c40403544580b140c003d0200f44c60f820041d0101300c41e0b203501804003c9180501c00410300d145003990075144150243c0600907019000d00820b0000301501507100e80c000d003e406003500c0c8923844605040e0340d200030044100740364001d06121a4403080f800001031110303600f10030320410603c074a6244034a13185001c0380e100000c645106828440e0959032621407008240403a0306501c0c0c8400944000c04c14800c61251914042c2c002ca0407003141c2c0c10204189022070b0240d411a100a0040e4842540d55511401d040d8046031402c4000b06450 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 773387544 1250 773386294 773386301
    0x2210d1509060905060f040b0d150902040603050a0b01170c01030b0a08030c0c010e0a0b070b220b01180608100e0102160606090f0204210c0b0d0f0e01182607150f 71
    0x1400804500c46808a6114103070b0b2b0b88a4405802e080c0b665903c1c0c0340d00180d13100c0c1700e01c0d005980120010040401c3c503192a130080300068201c0240d1100710949883d4240001401585014081c0790102d0010400e001041800ba00c80e0454519408042605558000d00140448036174109980e0250f0000c654014041c1c07004107400769030402c40e000c000e1080480c116003417564000503291a140b180100e95100120680900201180c0070840d8200422480c40c051821010345240e9120801010b860000050f60f51a484459040c56540314800011900030a40c10b65224510720b01b030ba4058140e441c90a10024040c5000f40c0404034503003014803007101c21910940d800e40d400c0a9441a4010913121640e800c507055044c2141c550400c1880070030217400e5800540b40c3c2c030020b03603001300e13281088101e100d081c0d4964000e8140f140c0e1522110410f2100540d200c224100c0e00840410031900000710a94007103140b80b6524400000001542c0c010460708030b00300840c00b80400d100300544a024041c040a5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 773388794 1250 773387544 773387561
    0x1050405100e120607090e0f1012020d0602130f0902030103020a060c060608010207060506040c0f14071b0617012903070c140102030702210d1509060905060f04 70
    0x400304496800c41c038107015901480a4a01c01030442c00c01e02500031019180240071910500083e0304c10404200030703c143d4410b2504240d1146507021149800c01c0c00740b542c52a45c2c030442c0610b18000018a0940d12240102100c880d0009400c1d540d4186541d01100c3d15040c1c4e100d00c4604d2510003200280803004e51003900d0607298001c060009487c03422408948146a000302914955035852000540c080244020001d240c498000840c0c0d40c5012002c0004980e00802d1002c144015180d03001002c4d90b0000100d0f1035018140c0f500c039185d802070706280e00d203506c044444135100c082891001c81c8c050f4021401800180311207140d2401a038a03251180e1081d0965000381442e01c40340c1c4102e0710841158000f45030700c1000b5281100807030b84103441d1110b05121401d101501a5800014826210760610030007046400c0325080004512000f4001c0e98240b05500440061076913480e2801d02c130f02c4243c424100101141c82c008d00250742c03900b100c80002c21060b01c1a6116400d5440031326000c0c24103000d04c00c0d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 773390044 1250 773388794 773388799
    0x714101a0102071a0f0c0d030b1305192f03010306062102010c020f2d03031608130b0d2313030f120e030403151503060911130b03010b01050405 63
    0xf41d075134002d4101c1070740da0011468410700c0003060201d42046141003210382d00c001c1c0300399408120800203205205a01e440029201c120500f044d04015400c1c265600003600c000203007200103a96000000c102a00141c002840481c001d041003003006000c8d010340145040c2c03401004200541942c2d10100900c2c4a00000c0c01210b016903002514007641c01601120021030000e0105403801291200103821802d40000c80f2181040c140300d69804640c4401000c42c00c50000c0c1e00542c9003234030002000c225481c502c0c00041c402400022000c08901e50541400e00811034118216118030804001602a05041c01d40701042d400e1408003900c000350201c01540a008500904039411005403800c9400804145c0f1050521400d0b2089028105062165103900e1030040d0145464500310b26044040c44840746681c9900e8ac180704008034040112940e04bc1141d40c0140001044c1200e031500c0d8103140c44804c101c581c401242da818a402c13034016007200d5030040c0120003c00540d118080199010300481c0901da8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 773391294 1250 773390044 773390069
    0x6010e060405090d3f0b09070c0b061f0c120314040201081f06050703080906010f0510020c04020a080108061027021e0c070605031b0714101a010207 65
    0x40350601178850303601c5a00502044280841045d803440ea00e48100c07002c00c4005500c54902d031440129140b05d0414011001c1701e0000b10344c01d09400060088a00300006000b20040b40b02150711565091a140018812945a2a4050318a1308007600d0b2503440710080e00d00c040c10f94680c4503564407a00c5038903072004040055148944880e00111404079000f458400820703070004040c08070f0031409604100511141e942c65540f40759a1030000c0c01c140010f46102078030750001c401409034101259401d806e4403803d94160070701c004481c000f01c0c1380404034103e09400034400140050134551040302141030312144000ca98030f07a11080c00c101d4180c03500b80f140350545a004a038081e44152840342c2001031200000005d070600352000c81c0d040445d900c5441c54030152000060900d201c0c6e0052001c07000a01080c1001811480c011713030a12000c29121488000d040000152003040140206a07506d0006014045170308507540500c0d900010190b0407071002120f825600316580743c1d031001035000142c03542c82421a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 773392544 1250 773391294 773391313
    0x512031b090328061b110609192a05040501060206040b04020613030c1d180705010c02012109020306060607030905043207030b0a06170711010e06010e06040509 70
    0x9002104082003c400009291481d03040451950700400c10b511004000707515000c10340740405060035040d01c1c0c4002c060f4104a041102605c07022070901c941c030b01d80c0500031a070310040d0700e03080c400c4008400a1108081c2c4407131102e100314054045210548000f6101002180d80342c0f2001c2e60b48041c1110000c040c032900038001401800e00d00003400085007140310344185c0070f44980d41c400e02c62401d5080000541060351480d507920040d052016008100049285603120700101981e4a5189038090641440100089501103912071324940a42840c43c46004030000c1070969401c000d0601410240d20138800c00d004600d039460000200c440050307254544d42c8000f0329003c284030151045c2c030a10780d1135448203105000c011f01100100c140d00042e0304580546842c000384041c3c104c9098010301400303410810400d00540350080340c044a00741c0c10342d2441801e6501d8400440d00880a134000d01925400e002e1707849400d400000d840c5060307c00c5c80b1030300e800d0341c1e4030403040c40101c4030704036903a0f180c903404581130 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 773393794 1250 773392544 773392573
    0x61805060304200402042c01050102030706020307140301090f0c021209190302030a21080123032a0f060906041512141501020d12180512031b0903 64
    0x81141e0966841290f9103000000c0e000101280c000741c1c04549501d0b00141c800f40780a079113400720120001e009000e031100f03505080000b9641d0044020082449074004045440d09018840c2d4004040c40c042010b5501d60b101c8003400054640d2110b20045079003403407040440c1d1400407540c80c031164840b9100a00380004002003040f00c16482d0843c2e458942c4260010003da141070083c0c24800d4040d10341c40307800c811408040d40ea4a81c0280b00356080110700c5005001c01d19258a09585403a206c141c1c1c09110001c60001a0600204400804913402540c10310f8403026107002020480030310460741c0c26400d4440e04140216403244a410a40c481c00800c42445592440e422088041e0003924102864011912241044819190601c402c82561204001c00700740c9052110040090030701c007900111924074000751202e22a8146020301a0712803032241360076040011002e1840790048100c44007143c181d41c84040661041e962174850b10502c030a483e10f180d191008913118040c01074014064144070154 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 773395044 1250 773393794 773393813
    0x20d09231f09020f042f040308090108071107080f10020f04030314070803091b030f1513060f06050a06021902090406020d0203150418110f011701080601061805060304 73
    0x5049078403800c2d060119075035480380d104202441d00880c100030000d420301544506c090904032645c144040c0104010300014110f0403d4a40800081c00c0440e070685604005550350107074102c440c0301501c80c818001a003588000b41584421201000761914030140c3c0c8440801e9114151403203a40f07217030810003040040d03c41d69038100618441380c41d1905090080d69884015030003a00c4000e4a85d00c44040c02020310005401907c0d40d040460082c08403030141d1010035140d8010480c00c6005040700700002e17903c0c904454012402c0e5038000400c0051205c0801c0c1d000081240d8050070b40182e0300c082c1c0c045041070000540c0e025500b0346401840500f00d0380c0c2d003048029100140100d400c981c00b4001c0310000c011a001035402418844541c00ca8148103030b09100484841038040d110015070a035014003c658170900070305040e142543e040a5200c40000140c500c441d0b0140c00a000d49900e10000410f0107000c903407281030340d9580c0d0342c03161410349004220000c2a040e000d0360303078821030420105000401034003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 773396294 1250 773395044 773395061
    0xa050a0f0e1f0e030f0432090a0e0f010e011a030303010308091c0b0708150f0103051509011d071805010e150a200304060c15020d09231f 60
    0x140085820b01280d8140b90840e0002c81d17412080c180c010806002c407240c990408001c86038403500d510441c81d961039a00c000800c071a00020300411030303034011034090400e41d0001d02c040c2264008440c0c02039248030820303008007555541c2c0010740d440d00740d0804407610850b07030012003044000c4c02542180d00b5600d6810b040c4e0700c0450b281307a0106803580303440d0300d03120300e20081c034401802500e8546a901d00400e000c1d14081c00103006100031348203815881650740d00c00c113074000900c5003864001640e40d500d500d0440c2860007a12229406210039000150356015020301407103405400f54056a5a210101d0a549900b09480c0754440301c1020a0705000300c0d4840d441906084e080244219034414000b0711540071a805070743c0d450005600300980c104070214011840711030b401d40500461400c0d1801d03400a000307031440d19000702100700d488010580000030707030103554103611130140c2003060501900c1c01c01545000034412826039080030b605d0b0350f060300300418400580145031183c90910000854010024181c44 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 773397544 1250 773396294 773396353
    0x7121b141b0a08032406041e0506070b071202120f1e010e010501020706051e13080f0601090b040b01080f07050c160314120a030b06120a050a0f0e 64
    0x11864400c03000002c100b60300c1c0090245107510341d64140300d26561030540d191a920060481c05803150109600c0d5182203e04540440c0c8407040e90402c804055604441194042e90784040085110300c1449007018415025a0161701c4d030404d400d04262182c0c00341d000d0a4004010502410006441c0390290284940d2046000030700b80807000c1814245a003103c02030700104204288040180700651301007119502405550500500f40510b450200c6010741c254040720901510110708114068010000132010385190001d69401ca940c90181a81c1c42c1800d11446000c1c5040426010940c24144070ba1714228006a488103043d07900e0310120700a419010b0300403010400100124480380714240003400c03080c2004d030404e120140c41d40c1441d03d8024588c62010b89960000300c201809400c08204907101090741c2d08000c1103ca1075100010010702420310f104484045803420040582501c0c0e00c51807061071694802c214600e20071449a08842701c0b080740c4849230b4171441965000b144000e846e804043d220 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 773398794 1250 773397544 773397577
    0x60304080903031201050f03160b0a0915030c0813050a120216091b03230603100f0209040e0715050903030c010c0c290105010f02070504020307121b14 66
    0x200003003499035000d840b11544c106520f0005000f50b00d88190100d00b8144114000c2c10030045091250550051900c80d00064030000035290b400107004031001c0c001001c0044100606030485540500a042000001800103030240300088010610904495100b504440100507400b00c55440100c4010008010401e501c5440f0b048001102a48d482d98017400c205240440d10303121401800c40c5c2100055903042c2410300305446240061130100900c40d031110510500c0b415501c41d4400b00c0d0500114081e0b88050f02c0c1082c08000803460740e50010024200c0966080040c441d00000701d940700c400502808401642c15035100c100c1d41e1103140507040fa1039004090702d00d0005070031000c500b181d46103840780000c0384007480240c003403103c8030f2600500e0203e142c0e5042f045039180c1c074400c41c6241050081905200e0903002c1418901e00c2004103502504001e40708540d01d0908140241c44003103e0810302117118200701c5a060324640c030b511610760503030803511124860843c0703360b2002c4d240c00c81d81180200c1c082 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 773400044 1250 773398794 773398807
    0xb041811040f110a170c0a080c0903060a0e0d09050307050f01110a1a10060801030f080723070501170c07020616200906030705150f0f090f01180506030408 68
    0xc00c0c840c1003e510b109580c681e640755003060019083d000d1404801c0c1480300385030100f040c400008011201030350306600c0d00c48000d54551002c1c2032240105100d60760940304503401c1000003001c81d4400b008800424045803429038412508482d6642203000e61609508944003c00c1a0305140700c211094600504040292403900e80d4005d10f4035903020020ba400300c01d05001142c031201c41c0003105410126810400401d00c2c14480040c0c80210180b100a1070074203170320040c0080c07204840030fa0b0249580400d0705014185075006000000c0669070042e156030140000000b890f6003c2e2400840f0a0880c494641d610f548502c903444041e00312100c1a030f0041001c104028102d030f042e200b4000d60512030000003032583c9414090002040f61001543c3c015510340091102650300010b43c00d08a62081790b198010703120b203001d4822180111100c25150741404605450070415601c064110104140c030b403130024120010044030f80212550305c41201c0502c0300313070a2081c2e042c890000c542c01800369100380d28000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 773401294 1250 773400044 773400071
    0xa050f03073006240b04120206071b0e01120308010b0306270a0f0501060c0f0303061e0810060e130809060f0d060e010b220e0108060403030b04181104 66
    0xb030880360442c0d0300c554a410800302002e15000d0480e410f103810070a0480c0d6414240c00f242c1c14842e1303010303070050420b0200b0320404550740d00040b50900c0b60320400807a060002c08004c44c142140c02d00860183c0c420150011841c1da412031a00c22500340c1540e5014100d034078201400c1c90a42c00900420307040034096010104075810b08254088801c10030740002441d00d09203c14001325020340c2c014070b400900f42001000b45070350000583c1c0c5003d81110701d03210107a0701440c0940c0106a00d030302050081245441480329140700c25030f41000c5944034800d4a5520351603070000c0c0201ca8282c00b50000000f03008010410555042d2003002c00e407846105014070b042240300002d11960401141c00251003c0040e040b80e90b00145e000309002800780c4800a00e407075040103030059050080c00c001d5405007119000030b48100d0300c0c81d03000f45c1c024400350004c045196154960782d42c490700c08aa00f9004a03041050003200ea081601c00c1c01300d4505060b03408101443d5036500c1c454400c64100e02c03141c3c866102c00c00710b1800d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 773402544 1250 773401294 773401379
    0x123010c05030d230108070e040201050d0b0a0b040302010e041b081003150209100207063e0606100801030b0a02030c1225020a0c1a04030b13020a050f0307 68
    0x6002c072028002402110b13882442480701d0580050b0304a400c4800e01300318040070001035a4020343e09080450300c03180c090350290010200390220350381c020081c1c2d1000806403060401001a01c0c000e03078540050032281002c0c0000e03108000c5011101c0040070700c4a864580c070404889402c10818030358010280d07a6501d0b40c2e83c100507074180380ca400b50780c00203104c3c14901d4110400c103a200001d001915818ac903201c4090015041e5103446851101456468401d01c0c030810020b070010454200840b058046146c0215540c41d030481d1000d008600004c0300503012400b4451040c101c0750b2225440c64165a04221203003e90005002030400c400c0501c1001c03a2068a0300b04940b04880404103000f51b030203003018003482a050501c0d001c040d9040389640401180001000d8001d880c4044000b00c81860302407201f44c0f261150740d0000e00790000410500104031002c4c1884070f0720500132140324590544a1041104451640c00469890b0340800001c003e03111160307030301e1406602c1c0b417800103644000f04082c40845 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 773403794 1250 773402544 773402561
    0x20c010c080601030c02061915080615060310031101030e0f0a120512010302040b060909010320040c02100903020c0d060906110901020d080a0605150703080123010c05030d 75
    0x1140d4564040c00c1120780e00440c801e5101009183c00d019a03c3c8001000c0d488450203400c0760581040544c0012100045400c10341420b250100355840c09507072940001d441d100195205902145000104003031450948c0a8a01a12031800500c1d002850341d5201d2003018031040b1710038107050721220104820346040c00b0956026480c400545180b040916081c1e581603404031044060000074000b03c0001c0d5551000c89040d00c0c1c1c10784000078501c064100040b81409081101540030940d4000481040300c920a1200c0c0c00c3c07d4038110503071050780c07842000107641032420500c00681c4852020406040d09410500440d1b00074019a0903403118280440d2802816200c1960020f0322400c100341000803910521200107d481d8010342000c12442c0004c0d1507050f2a6180020401020701194031104a640094014200100110791603001c0022644c040c0d000340c6030940110b00340c5400000c0d161000d0043c841c040b115840072232101c4d402c0000560301185506401e40d0141f000340003050702888a403140b8283c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 773405044 1250 773403794 773403817
    0x90b0f06010e030706020c0909031b100f02090f0d02040605040c0e031507050f0310050604031a13170d14070e120d0504061202160b0a1d0613050a0602 66
    0x1949031a000141c440785580c184540660300281d004c0020541c0803401110700402100c141031240c95111000e49140242090401851105105040030740760000d00d00f1748e910001c940900c13050500d400d40301d04a01402ca1410317008140001d44402d9458102d602d41c0d8100e100400008900b42c95802141c02c44050341c0003580410705032602c080e410715003085590070100c2034040e030030801d280002c001003041c0039a09114000c4407001c8042050342d82c07218030b503001415018201c141c4aa13602e00b4081000b0503a07141c0d0f0310b40040d282d0081422003004610784c2000a820821840c0143c0e41540c4071a00c66000c10240e141c05559100c15501d10124030609030b0040101c0e9407140015a0407200300403000c119120b008903158030488010051316007000a4038111041420914081d941451445010b403041c4c0f400c913001c15216680100401c0422011203000705200e081c05c01260700d0f0074400000d82c2e0072514060415a0041000a10b10f4403801004480300f4840c20a0790b6140340c40d13540c1c410036070704002207074030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 773406294 1250 773405044 773405071
    0x4051f181104240e061311040f060516081c02041d090318090a0605030f0d02010b0604060e090903070b040c060f03020306010509011d06071a01050d0206120a090b 71
    0xc4600d000c1c043c1e416804400c440c1070040082c6000032400d582210f1040d1525100c0a40005205940b4520f944c00950706c8240280084881038401498903403040c0580001c890021002055003446002914001882540c114280b000c403502e400704940c00400c20032040160030025503501c1c00160000d00014081401410700300001a40354481c145d1005007440784a50042c4400d02e00400c0007414107200b544256900345580d100c400d040c00c00b4000c0c0d60807454043c031803a1171410310b110001402e03c040d0480e59001704001d2510324200421032007288500380000302c2c881c44080c071510b49110155001010310084074900816582d445403400030499059954040440e810015070f0303040b10100b005860145011031851400d03d001030458080d80d2000d80c10000018411661a036a141101c5c0d03070040000c0000d40c407901ca900e04152003071030f0f1f41080341e041141c9500008641c100001f8020f0110350041c04541000514150952041030041000c140f003526410300034003061042e90103c1c0101c00740390302c41 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 773407544 1250 773406294 773406323
    0xc0e0904062705010f020306100503040f2906030705030d051b0106081605010810150314090a1e02030a030f090b070309382b0b01110604051f18 63
    0x6038211441005e030110410700410811101e903980400038000f029003410055200c0e111401c0c042c210f4400381e01c0062950383d1040c0201e500c1c501c6240c1d807482c030600d6207609810700d98030001815140c1c89a8810700750154011100d5401450180010b0544100041556594850708000150a5070155030111085421256030010006008440000a400c0031300f002121801d084d400d05000074014414a101400d000c024008040d21a03000110100f189101b144514200340c0010380d00c030030341c411044400c00d44030140c0051032140010460a807640050250004810340d032016107420a555451000b040000c99000c20303000c0d0080e001d003151902a60301e249005080400c034180502003001c2003003c1c1e03070901c10000c1c1c00720300302038000c0c1c2001c0d0143c21581c0c542c0360800f07442c0c5e01400208000807118a6a560101d403052040d404070100c1300e42662440f0002d03035203c0c2c2040c0ca448056502030f000b9004043c801c03600c1d50480309542e800c03107a204000200454100c1381d01c8005101c140c411941c903540c42d45203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 773408794 1250 773407544 773407553
    0x90f02180108100c1e0c20030d0e0d0f0c120c180b03100f0f020d02130b070317100306050702060702010501060e010203220f0803070210030c0e09040627 67
    0x5415840e5040f001c10800e8044081d009041405620303175403010170a00c10f8081d09080e106202d414242c0d540141c400710703205010001a261140d130300e14018064484e003560280d035284200c445c2c000017440a07114200c065050f440c0e0b41c0a54480380400d40d00c0380e00d4203000180f01b05c0410009003d8034002c80e01c0f000d1542c244040c0c55295500c161018500c2403c100403126107039000703c0d00c00e0b0b40000e0010005034042109800001511540e03042894041c030103c1c4845c8142c41b90340041903005031010707210080740c0e19a80c0c1880a40503951300500010300c0507030901d414220300043d082d00501d5003c0e2110f4032698030f944d05c50a444084a5410050f08004103000d25260240500c502500281c1006110803502000007540ea00550009180640d10417840e29444d19540d02d0220103082c0758140c0450301c82d110182d880e56035210040490082d014900b920b40b501e8820310445088100542c0c40c400d0560800c010000f065401600a817112071351620411440740b00d01c900c80795000043c1c00460080d1006041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 773410044 1250 773408794 773408803
    0x602010e0706030c0f12060506180906330f0a0f02010c0807120209060706090503041a0405061b01110c070e16050f03220c0905100302090604090f02180108 68
    0x20080516040c121007084e00350704031000302041c0445141c039000724005486044040c014039480150844000101c81608518009510031201d000703480d1601145c40f40c00601810203840300d1040e4540d814801c04026150318020740c5806000481512802d15803a140c209030503600000001d00407030030748a0314803a801d4080c05403420444030350030308851524080c1009800700078405040440b60743d000941d2010ba40d6510291000d43d600800100180451490940c1e0781e980319000c4c61017040c030901602c0c0039581d0040e00310780a486000d0b004a050032440e0180e0200024241c00c3c503a2155294101c1420351021800901440b1004c0001040e80c0c0c1e26245807040c0303c003005000413080b010010103220350710f6040422180345034200d00105650703903074001c03200303030080803843c201017004411002c440700b4020081c0c82c410a452852904000c0d90700c51100c030803000010307440001d4000160500149044c54142d015842c2d05000d400b1045c4009103d41c0000d00000d040014862100c40e510010f00030400d0401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 773411294 1250 773410044 773410049
    0xc201009141002030306190806010303051c0507052719060e01080411010f020f101505030c030a061508060f07080601082404020706020c010e0c030106060818030c070602010e07 77
    0x382c0d800c07214a4400700094481c44000e180c14000c407450303441005c082036040c4103070000b401c011083d070301196142c3c913005160754020a40880000c3b40071414003000c511174807500740221001d44070b90b4948442c280402c410324500e034551031030501d0782c80c0041034a0303220b80aa26041042c00c808590181c1e06010003e016000303007880d00e50402c034002c820000007851920403c0010007013402d0240c4c4c00d8080300c108074a04200307001201046d0044a205070640c4416400085d41e50460007460041070341c0b1a800d042c3d9550050410f95459031040c2d801c44007007102a4066080503184885200c01e0b1501c800c035181c070b000000d45441c03104c11030764001c008145034440c42468200c0b60034030b440c0742e0700d0605090b4101c12070122003445a02c010100d413814800e5441307a0480310140c0c3d10240654a130030550386002c0c020003615400809502803e0781d01d00c06450b0600c100301c10348055450b01c5107142c44980c200c20092816520300a0284010803080080000400c8028001c120540c0080b40342503141406038240410faa = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 773412544 1250 773411294 773411299
    0x1709091611010b0d3e0307050607050a030f03060b040303050705150405030d020f070b0f060a090608120d06050402030f19090206030c07030903200306010e06010c20100914 75
    0x220518025036150030100e591035403c0385026245000c40b030300346041e4075aa40d51740311044c00461902d0459103008191564803090440c01c2c0c03981650380710148960780c441c44000034080d0304403010000020b4014440d01030000340e03e00e80021401e469485001041e4055002034020402c007050b02000c1000402c61100d030050307000c10b000d405007050364130182d032802100140d9070303070640208042140040800c01e440200360420400004c9003001603440243e50703c280c400c2030060780b000308080b07004a11801220100c03001c06004140f42c4103141d401c440a60031070b108041a003038a600000030b03c0d0b074440c0050b6004100d1044400064108032100749440364000b201c441c541d6040ca241c1d0809a5101e0003620b902907211072180e6502c090320700e8115101112074100400c5407905a4002d80303002480c02d11201c0840d4103604481440e62640e141420015088910a000406000f03601001480e100c0a02901001c0e8114000c00e074001800024141108550b02e04009204108100010002910400c40c0450b01b0b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 773413794 1250 773412544 773412551
    0xd0e1501062d0207210b01121a040b0a0c0c02030d0e031011070f11150c010b010804020a05061c0501060e040614011403090307060e0102030a14070804170909161101 72
    0x2080400780d2205914810f1800106400001418145c88610b17201e40d43c0394007100008003581c5810741407001c460f118506881c042e01c00303440c50500019490006d401190410b1204c100c540d901c1002002400d1905202e03c10444143c16001c010b85040040741286101602c4400810303c1c01e4042c189420741581039896818144038501c8451a4418202c440b090307004818002d0002c420300b007010341d980020102d540c0141c0e6454500304001410009014142c40810090186951650044803801003d5901039403004490500304502d01d000c40c028550300b8000e100200d170282c0c407044a403044032001d071311a001040c60f0030741c1880f061409204180c00385c1003000001d06d4070915500024101007004280103106138000010801f5501c082090b41c040a500003c2485980b10b0030180501030342055a06c3c011031802c0000f10080508441d80661141c21950307030703c0b1002d45e2a500e0b83c00c9180165951038034804000c07c0340c60f131395440d0313266150b20402d4092901e01400010303609c01804170b81243c3c0400150b074036 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 773415044 1250 773413794 773413877
    0x50114060114180411070b160c0b06121617211c0e0304181b020607050f040302270708071b05070806070908010509120d0e150106 57
    0xa0100640e030201c0081000040144480760114004044c48017000c100800702095680c04c0021b00c0d450381c0d00c602120801300001342c0c0d00781c1c804e450300a58504010130110306000042c3c0c040c20001c4100c40c02d4000441250310740b030060303402903070b40c1d203965080422031034504134011011040c2000a480160200349044070b4480180c0c40d0608035004800c195142d1850f45100c0400c0d000058004200c0c001c0070f0810f4941d1550358003003041d98528006003201d492170521070400400c500c04190000d000b5416009400030780c4d41c1e040308484c1d9501412828179012020303c030202c05602c94052072000301820b8840c2c0001540c0103844419031030740040001040040c010200000d6650100103402940c1800d41c0d40e8030f0b003c64070304d40641004a83e03045500184560f0b420030440c2640300032035200310345020008100c0791701e60003030308ca031078002c15180710000c480c04005002d500d601541c028941041c240b001d441c803c1c07a000c00d0144a541d030a0b8003c5000071410584001c070030300c00101844130301900f00100c04180d503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 773416294 1250 773415044 773415077
    0xf06060d030e12070806070302090f181b0f04030303020d15270f05090705010f031116060b09070525020d021018060315060305060f120703020405040501140601 70
    0xc014000c0c2d0340592a003441102ca100020401900078242c82415503d56140c5130100800a40143d1416849a0640785100c1002c2c140b01800b040e14203c0a0900d00c0d072680d5200021080380080e909442021008000401e5140718000c003030320180d84640c1d030150b95411042810030940c1c403034403008611103524050070000050b100c0da107054652144004011212170456000c002000007050f0703e03e10b1810178080042e5200c0100d02c12041d603c0c262240d00020002090480481e110b10b2495400c90608101d403211041600b100e01d40c109201f02c80104440160034081000c1505c00e50b411808900b02265001c1c8041203030b803282c40d1400030a86101501c00003078001403444000381002034001c03160740c0b0760f49000911401e03c6025284211401c0c0c5035040c2c2d2040014020700d02980c445111611011300454298885d000c1c02d40a40310040403c1c00140c9000104100b10044100031125442842d01c0000107032154041c00344243c1c054000040d9810104044c40c003800f00080209041040c070405980918 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 773417544 1250 773416294 773416307
    0x2030705250b34050303042604180506120a12031a030c040e03070b04030c05160501021b060408070b0c06060a0501021902150d1509060b0a030504150207050f06060d03 73
    0x1d155400626440590820300d480c600000c20005007135400b0000030002071000310302c003400079001c06220003115941100d81d021294001c0c1d0191700358030780450428910019268100c03680109006250040030a24508030038504214050308541a0700c1c0c0242070030784150948a0315601c0c01c00c030b1019842002d12000002d07214108140c48620070b41c0d88243d401c941441c20000c1c0c030070321580003410001505003420301800007005080121514440c42d20701604000d81502e04404460068000300f4641070351452030310340d4103400f042640c1c0241050000003503202040141500814a10628540e200310a03040181002e8000b03049034040c2ca030001c010002a680003403483c0818283d011900d50060303007480052200e0750a03138089901800d0100f851408003c0d80c2d40140c050b11a400c090b80801030391a031071101660010b101d500221242405030f055440e0094005561007032003145504a1060107101d0481240c119800550b80c41c0e1005041d00d404030020004550040401c40c0d03c14035903005550001c02a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 773418794 1250 773417544 773417587
    0x90c0521190c09030213060b07050f0c01030207110913060c030c0306090603080a08091006240903170c0304050901031a070206061e0f13050a0c05040b0a0f02030705250b 74
    0x1c000c035420307942420b11b880d408040607280810400e0740d00c003414148150b4600b000100c1003c0d40c00f41107181e07071044d80a407088601640d403001408002d403880c44100048120010306020407640100c80700340015070944245088030b40c8a4800084000e580d01c1c1c001c0858606030003c0c400c0724580744050002c03031203a00070340711402c03110b16109034503984180400d81003c003c41c698041c080d050100204200c070040d0200c0c181752100218005241f0244c44044402090510003c1c1095240c69810b101428420000301100b0b03001c031048a18155403100802c0d000f8800b64010340b100400e4241980580350b1808546420850b05c3c40204640e0504000041350007840310340e5040002c0c0d5403480d0103150744859001c2038900900411200c0c3d0840c0200031100034041c201c440c00b00c00c501d4590364255150091043c0d42c280c4c0e6680281d50700b4a000300000341e03070850b40c008e10603007584410f04c0b000e000a03400704440c1a14448030030840411510003449199000701c2900041c245803418420884404028044501c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 773420044 1250 773418794 773418799
    0x30f0414060714030304060e0a030f0f0e031b0306090706090b1615150602070b0d05070c0506010609030302060f070507060917220e07020601090c0521190c090302 71
    0x408000039000200c0c10b12498100510710040385500c42c00303d600100241d441680140010302060a2240d591512070040c084010f0200c1c84103c8074103049071180344075104408060808201034203003100061b140c250000d0100c0e81020a0313203181e45960400780007007500900715000402d0b02908044e4040c101718264094403400c1c0d030b808102da004080c2d5001d0441200fa0304109501d0101c68802c220030084d114600800b41004081080020603506c00100074007200da0104085040090300f02e078000243c2400350584003002000381800c008180140141802040300c0e48582030120310310f18000e0701b4100010048800035801c1010003207040e410100300c4d0703185540701100180c9918580b425580c0caa1051b058501110404200c140c8008101c80c00c081395081c2c1c56001c112119074034800320000e0310007110007400580181004100321107843d04603189580a40c04c0203401d1150704882c1c494064107403107070b28071b820050409000b554240080c501c41c0c0084481810b02540d0080c1c28060002420f6100090 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 773421294 1250 773420044 773420069
    0x140721091802190201050717060301060e07050c010605011b110312032d1b131707061103130b0d06080318010e030a08190210060605040816050307030f0201021606021b03030f04 77
    0xb09d244c0c6d000e500032001b03003255255a54460402d85002807040d00940b8031404903618048022030250b0050f10070b5040c40d00034602421040072941c1e00c0c04400c00352070b20015007501c5102c0c20182408000405103204600703104207218419181600510201c1d0b0001c0d5010198818905014030940300002104508a907000d41c1d50b96900c100d020809510480d41c05070080030a0f260796441d1010000ca00c40084034025658417a40c0c4c032050300e4031512440f51218030302d0505035046d030410015099002504140c0c140701d6000400c540e40b003501c03d0075680601d60360300b1088030040b0056000e44e000104a044000300b900103140130051551501501d00c07070792542d5045181e40740240300e0034034400c101c1c81140420081c000c3c01000e98405000c0c100345c10502544520b4020404801454400c05000703d003160f90040003440306901c0d507190b100e003007101c820050b4114001c1c0b00804021181d00c00240000b445642c2c01015503010150358402000990001d6600c240c000300b00c0016042c800348203807030650b0104007070301 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 773422544 1250 773421294 773421301
    0xb1f03080c0a050706120609060b0a0c050a0b01032907080c1605150103050c060724020f0c1b041404060b030a0f0b07140721091802190201050717 64
    0x140b824108080041403480b4101d008602c40740d01180416150b080c41e802400b2881d100d000100941c0d41c1b50140050102e000d1001000e40c81c4103009a0a402d800b40e015140c58040e251100e1000c54400d030010b03540300d004c1c0e241042402000e0800c0c0641200100220500e0f03060001000f002d980001c1d00e00129414041007039290000826180114158400e040f0303118010007000d044080c500910066a941c0070b40c00b903001081c24444200c80101d44d0001c0013048150009010700c2c82000c1e640a40d40d002642803012404501c0303254001c0070030115240041801c45c0c124009050703c090600038550103a070400100da034118044201c8a038106512071008540c0481d4000800d2800d2000341c070181c008a814401d030700500149400041c0152059a211080708280302d01b45074580c85017210062185142010b10039581ca0310007080040740005180c1000340303c0d56054260b502800794403402c00c20340d50000d035621a898150b0b013410b1801c500c50009000d149015200034200954400a0326086c01182c4000b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 773423794 1250 773422544 773422567
    0x519051506130f0b120a0c06182d0501030c093b0702061005060a0305060a0b04080102091c1a130606030b060f01032a05070506040303090b1f0308 64
    0x40b100759501c40c031801c025906150500c1c00242007440e09440c010464a850900852801b01e0801c024a070010302c0c0225407450594110349407002c02410b03503441c00b012000400c01001c4011003004000c103545100c450003e401700c180c2000407040e80700358181858554021261a007100c4d140049651501011803449007458440b0001c4405154102e000070400c9507030305140c40746400450280c4074582c22180c040d41e5130003041c51504403034003c042c0d1103207007408032680681c4240c00c07555000078041c050040850b030342e80c000422500b29412a04899402040b010880d060800c202007802514051460900c01d00740c58900380c06952003030320a560f41403800041c0e0350840d071055201c0c804e80e0001c4104086c43d940d045c41e8881d00e00c1520207d10a4180c55085802e541c42400b868800840b9080d81c2d0081410013405100d11003c1c2300c11007003c1c0281400318001041080c03200768402c1f4042d44000c550a109440c24071824000108542c454100032000d44051905010905054071351107a09540d0311381c4c0c40e40c031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 773425044 1250 773423794 773423809
    0x19060609021315050c0604230a0602030702010e0a0c03111c0f110303090a060e010e0d150e0a0b060103023403110f12090109170a0519051506 62
    0x400c15540002002119091090140c070200ca00caa40c540c58004400c4000300d03528811200200c40a6000c0804900440c910005405050507682c007480303a201d0141e050b07181441080389066924650100170028a02e0702809000d100b21043e6000c0c04040300681e841d4a110025400094202c112450441050792101c582a4071240d002000111806e00c0b60726044102c00f400c601c046450141f40341107814582400026203840c0c1400a01c4101303000d05000c022915848014006c504003d65003182c00c220b40c4541001c444071034003410591143d02c0c5241102c0c01928200025060554402c454020204e950349030311a400c18005d107405a0354501c400d50030301c080d40710040079624200840607041d900d010290182200107109449442010491030180d035281c0d101e03010024083d40043c1081c007410b001c170fa0000d0022240c141003420035291140c034104502940419030305000c1d4040b41080c010700a01b0000100340c003010341c452041c903099075642c02c7c0d00d4894680032a400341c0c81d1800451003554503480d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 773426294 1250 773425044 773425049
    0x6040605040519060f27020d08190302040806070804051b03071d0a1a06120c07080a020a1403071110360b03060303070305161a0403030f0e190606 64
    0x228015403c3c2241011001484892140310210b450300842840341c0b801c5040c164000e0310700f0090406c3e00d84181d0203200703011500d51000c48090008010405403001034403410171402c0b0080e42c0058403141030030722807490904090240001e000c0c0900c10000001e000007040021039a400c0d056400b035000c0200424900345250b0131240c9012005040315402c0340c444003c0a00c0b44a070072406222202c0201031000710780f14401c039810782100c030400c89065021500721060340c00c0107802507a94641100c42e12084542d8110a0400340180c0103410702806000c504084d5001c40b11041c0b002e1072801c3e1081d60b883c00d00c0e10f01100064080d8400301d20003012a80139928440682c401c50443c150500f240601d10000500a00308081c00c44503546004601400542c1c1500e10440300900203529000f10781d14252080d400001c10803144114500241d400180c201094400751702039110402003a05140c50085e05403590003500c1c4605529044240384500000507100081054400c6021a84000c0703041c10005080140c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 773427544 1250 773426294 773426323
    0x4060317280305071e0f0c0201050d0203010306091703060a030609111504062303060d1509080a031802010905011101060b040b03100506040b0901030203060a1706071b0203060406050405 81
    0x2807103290481d0b405402052150010f81e9a08880c2c480c0030600b100c0226802070800001b801580388611050b0044400c44812801410424201a540b80f400381c00e980c07098004a400a49664520041008014207030f41c034400f512918504500d480404546141c010f840081c240316150b2a00c00c05000400c0820341088901414184880b0300b00303014204140e10a12407000042e4101c000500d56941c4000542018001c400100c1d1030343e11100d00300000803800c2001500c402e4480e00c011007141a00348602015948101e003510380350b0074619005802c0b2000020070702d01e40410035003d200181e80c03005e0044181d0300242003010042e40e030302c600c0030700400c0c840c0c01c13402020030001004500c003c2603801541c40741c504000f1480c603c548800c18400c00380603510950104550501c036518040d80260003030750f40300c000a405c1c1b69809540d400c61111300480c06054114a811840a0080c181c1d40038003000180340d01c00560710300c0410140c0c04280d40c1e180c001e201400c00d55855010404100e0305210038500440348 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 773428794 1250 773427544 773427607
    0x3060103081e09060d0b090c040e04082b05070e06190305220615080a08030106050a02120403060b01080c030610031a120f060109050c0405010f030b03070b1804060317 73
    0x540145e0401480c40701140c9218080e00d40000d803a001200317049401341c841c840c12030b03946501c550341ca020f4140c100c01c80c3c0c03103045030103198000c1d0a082e500504a0300801d210101191506100b68081c01c0420442d128902480d010001185000b04890901ca00050185400120707641c0385e034000e0300c0950740d8045003060a8440c508050501c6841e8201700c0c1206a01a00f03011100d9030303000341b180d940c0384664000b854500c0501c010007100d405180685840d0450380156071040c40c1d898410005540075030030484440d41c0ea02064022942e1000143d0307071181120716a1455824080000744200b45a0f00580f002c25446028404041c1c1c400c4000b0f80c0003d60142c00b0101c020040265562a01c050b041700b04000c0c130415000260122082c00384600441010000c42c0c5000c2c140401129149150119001815116210744060351000c106400060a045685030f441302a18088200002c808081544c401c90411500b8004164a40303d040b114080c200d804542c0d640011030201c08000c84e504211140200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 773430044 1250 773428794 773428807
    0x120903061d06160c02090702120307030e1c05030a09030c05010c09080609030405150c0f0709050702240f1003060f0911090702071a0c0f0d090503060103081e0906 71
    0xc1d00c12040c81c2100ca00055680680c0e480d0090b00c04038150b144902c0020340100c0c8414054140110025040708007403041d01e104144000b54090700364400c6d10f0b281c0005e41d0700c1e600750034000010b100841d0646941203081c1d6283c20b0f0b02e0001405800f01a00c0115a03595034110003041601540a9465030340d03000c4001d10441ca905036014090f076203684981440c0380541d0b00091903415002c02294240c480041480f40c441640c206c040880b500300c0d05421649104520544a60030030400036000100b405600104081c64a284024107100039441d000081442c60040320101c401800641c4c0d51001000b000075450340c0d1030840d4008032141c2d9500190a15161007044000c5450f90741040c142e640c000c21a240c500410070041c40b0005030200c6101005030030200d010302650100080c045c511295001481d0305007001030342802d080c00003d02004020b58883d591000401340c01030143c0e03004142c210701400c950b40c50f40d200e61403640325003069900da659880014042045649056074503420000e404243c6448 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 773431294 1250 773430044 773430071
    0x20d1401031a01210206160c0515120604090201140703030203071d280f0e01090c140412030c0605010e0411090112151803080f130c0312090306 63
    0x8a0a010550380c8a14448641071011481c1c15003504881c0e40b01c0806041d500c00603050b4040e0000c24400701d0b40114200650101d220b0356058942803039002c5c2100301212860102005058640d44000041c141340030f0008400000b104004903610000c20740f8041442e5483d403004a400c544a01c200d144814400f01d007110515605601842c0701c0c807130b1502c4115a0030011801c1110500c06666000da120105003d00c1d10b0031f0f22102e8510054800ca20304da80720b8541c42c1c008000030091680c118680c03020320740c40108426000ca009805d130308903490800e030400711191811101d007032080d40514401c03c14101e40480c2050311400703207807030042d4026030f042100c1c2d40c50340d41c7d1b08500d10041e40c06451844940e122101c0760300e061810941240c02c54061015503c01d0342e5900985210045c01e80d288042c1d071824416400c90a06502040c4640719070b49d076020528207404030070040240074158580700121000107000083c00d030078540f070603030740c00ca01880005c801701d95044a00d015150401042d85081660444840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 773432544 1250 773431294 773431331
    0x91b04170c03070302060f1309020c010207030311090901030f030203041d0103110108070e0f0f060a020c0a06020c060a0809160902040602010f140f060a081506010906051606050a020d 80
    0x20180310301540c6240d8440001c060f624000c0b400040c3d8031072020000601c81c81320000040c88000460074600d000c01d50389200b840200e0700408a07500b000e94001a0510800d40e25204020001005880c2d0340d061020180129422080501000380b07080d18103050902490b0080080d20024001002d558040045017410221800403e12017100c0400c00400390042a6025408162103049590f031403a039400032600400000f406801c0e001500001d000a100c0090303261900106035441c09600180b000105c03100c18424541401c1e40184111740107000342c4606655080c045801c1c40c625807501c400036460300d40800d0704110400c1d890b40c4031000c84130740000d41340686401030011158690001c00205c07005100071415200031401280782400d84600042c0d261306103103907564002c2c5010b0190207690740c0b0b03050b0032880e2011403803001c0c1c400056141048000c0d80d10402182c090f00b0035207006810100000341060394180c61142c0148210b80f60000211460800d50548200540c0b006050003410790441140c6c070301 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 773433794 1250 773432544 773432579
    0x1211030d020409092906010e01050c0105130b01051203090103020913090f150b0f040e0106030f0b0f10060c1203150b03040606080601050a12020109090912110c0a05091b04 75
    0xc105401c41180507015803c07505c0300d17140b2150b410200d0706548100045032201d12005009040c0700c0c0902c0f40d0400c3c16400d20401b031040b4484c2e241c41000410300d041403400c146050388400d00c100e030b2900520403034400100966001000a00b030242c0c442c040900000d550802e080c2c643d500840c905040201401240c0c4030700012507000d44a00401c000c83c44451005a400c1c1d0003c25820586080d0f24885078141980056100030f035800c00003c0b003e440f907641074181c040842058400e43e41420038030901781c60301c503c3d507500b04c10740c8104042d0321803a29401405d0800d4034038018051045c07400e55030000501a410204a02403030429008015440c2c20300c2000d01e0700203a070280c079032615114001c20140c0d00041c116040e914001e01c284101840e00002d1113140f00340b008101d0400c40041d100203500c0c103046c0a075900b40784c450304481c000404401d2008103c004114200003807a0320044410550f80c542900030f9040d11410341b01e148a90b035030082c01c0c003040b0030341855404507014002000030b007418070b98404005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 773435044 1250 773433794 773433803
    0x50a0303051609050126070801060e010513060305090708031b01050603070302032d060a0617010c140904061a04030203060f100e06030a02121015031211030d02040909 73
    0x82d240d1035502c507a8041002015808161412810301a07503015800724402944c00b000d1901c0800004003010541003015294a004680d0000040c8a81d80d00410f1101d5501030a107030403418405c0502c10042d4041d201d10809042c5950380c40402d4400e44140040005004500c0442c0c0e520703c4a04000d09001605200a01e646d510380000709829180204000e01226001401010018880c0f007140040807000310400a04055000030f404414100b4010244582c10802001a02d640f6009942c0c00d20660005003d82c90392401801c079010682103000783c0001c105100c2c1698441c01031201107070050090f03030018450b2030641c0c1490345503014110020001c0c1c3e842078040d6010781d107450b500901401d009580f080852084c1c40710501400602c0381480782e0004005086802c09011900400d2a445a03141c1c3ca00311600200183c501650643c051002d0030b0a4960416080c2072950700c0304032030050301c00314880401c500b40c42d880d0404e2004009607003c03c08600760031542e0790390721540c442c01824400e8080302c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 773436294 1250 773435044 773435051
    0x1b1612050a0e1e04020f0415170919061107050a080d060b18040903091d01030615030201020c0f042003061e060307081b0a09290a0c06060b07050a0303 66
    0x4038103110084420f40d803000c0424060314004101048044e4010050060041c0400d1000107450b40480003401c074460f10035150056030580080001c89110700082ca000c1e1240c0c0000c841d0ba4000b001441990380558000c03000044407141000d0080c803507c6441c0c4054400d00c0f0780d030041c1c024006180c0c010000d03900d10000400020340d440d070b06d411650003603000107101c05000051000c5c10f41010782060110314840e15298403290346546441103881e0361a0300300c1c0030b19401400103008000c1f5501ca8420381c0c01c44051654aa079145900003907450302e400e0240703806030b0310800c003000c09070b200e5400403aa0b24038041e40c092a080f0310482221010f400484102d40304020100369002d00c8a6201c5404000050103000b0510310b541d0400c2c00d131840c91014084001c441650340511025450a0700500400102540c030300c41058070340368912107070300d56507012031050200d200740d00050605c05404507918040700f400c00c2c034501000c50400f240148139550000040c00310000d0f000c002c110b00850324408040c402e1f1403c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 773437544 1250 773436294 773436317
    0x30d0c050d2007090227220914010b03070504060b040612060909140d0305060f040903020a12021006050901050603011701020f0711031515120c0a03061407081b1612050a 74
    0x400b00b0103640f04100347c201440301c49100c0c601b0140c00c20503c00c0c3d01c440c0c102280c40301d266690070441c40240e010540483c2d558079600d03c2c9626048c8071f00802014122003d0140e1802c003201e5070a148582c3c4902c0d402d104484043c10b04007241a00a50002c00b26401c04000d100d92600780400f0f940d404002c041050700580c0c0180501c20300031b100300e81c02a00c001d402c01024541c007070240001010f600700250150320030018204009009421042d081410b280e01800301d030883c09280a080d5411034105611a1009600510264403070006481c1120740c0351840040140300c0c40b00480c0244904403010028600c0040c000e4284900c081d4007143c0904285d049449035107503034101d900d140030251135035a124801f1590181c42c40c40c101c403001450456510582c0c02e0b01c41440001124011260310868000307455540741d0440c06118a000b6034010b401d030400c0445450401d51144485100b5020074115810209821051039a990f05c3c031250950b1050700c2c000407100020001d003840d0014100c0d14001103401102 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 773438794 1250 773437544 773437597
    0x30c09070207061e051c02090d030e0a06110a0305070c0308030a14010501020607020a2406080c0405130c031205090306100f080a030509060307031811030d0c050d20070902 75
    0x250706440f200da82c841b400e00d05944079500304000280d00710001980c00b030182c0340d40740c0e90b01d80e04030300840d100342c580a000384c1c021005d01c00304542543c03100302446013841100c210804003041c610360042d450301e0701c2d03a5100e85a00d040c40d480203044c1c0000d424a00040100000c03140d10754400703680d030003800036070307601c0c5030ba80d04012aa00c1c4002c4503080e0040e04400f80410000384010206219003134030811400303a110710400c101044454030380c0544480c4c4c0c090302c5500e0040c24644501e44c0c01c6a800c0841c0b9113140046d880740c04c4640124440200300c0482d41a080240510510554100e040c004081e20582e04045056501d054241e002d03500c1044141040001d00130030004000c0d05496150b1104c03418000c0007420003c150b00000c03c1101856124041403074218004142c40f041d003881034440b003100c0d01d100c03c1410b2408c050b00c100d410510991800210100d08001910b907545000c5141015070400071008101c21035000c102c5860042c4030b4520b0218002d05903402500204519084074981d5488900c00f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 773440044 1250 773438794 773438837
    0xc240a052713091728020a0803010e0a090609080d0b0102071d06190b120604180f02010201150611060a060f23090a06031401050c030114030c0907020706 67
    0x300c1a8400e07502c0501d0610740d549078012141c0240102c0f0a0020200d0b580700141c0c4552050280f0034006503034a45030701e010450000e0140c000d8500d071008001c00c10044d500c6444520040c00780c0a440b00c1181c0010f02c001d4002c2d0401c0c0c00341c1380d00030801d001c4001c081c641403441d608000d46000b203032800c140c1e10020719440081c4110480321098030340d01c680d000c8550324010740301000e0216604100c1d80121941d0808100c6050001020444800d580e1071200444000f021000038010510a07030500d145151020040d03545880ea55400c8180d43c20080700c42d100503401030070700c041d10b443c400c01445000149140c000209050000001c0281c451603655400d0901c2100c0081c00303040081038105c1414401500070011501c0085880e20a01c00192015400513000840c2110111100c030340b900f8080c4101304003941c441e000020503000a00c064100702410880798041402405000301014000322041e54080164100d00080a864000141400d0310000c0d03c90075540140743c0480c0c2ca546d03098820b00d01ca640f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 773441294 1250 773440044 773440117
    0xf0510020f0d0516050f07031a070203040303030b0616051606020c03061b040911040f090c0225030f080d110c0d0c020607140c01110c030c240a05 64
    0x80180c5062540c0402c00c0d40c2c1600003010848100407041c00c002d0010391700b0000c01103814225402001e0302491351800081002d01c1c612a001c00c2000c180a01c1141a00041070328207695240c203022440100c1407021600710b02a4100c0d8600340d01c04109207078103000000c00d41e00100c0205803050519503468210583e5190030702c0000c075801d94001d4001940f104030b04d60032160070490b40035075a4a050341c1d4050708000d032071014200c0110081c002404000b8800700805440091080a60034000e040b50030101a490303401d54103c3c1080d51042441901d50049000811006103501c960220390041c194202019190000c0c0103400c512454a25004030750500381c000c2d01c2c031441212000340045030883c041100d07a00c07000c200498120744144115030000d40120320403030b4044024402082095540d00c00100301d084c2c4044440c455410606211805403004149882d000c0d10545441d400c0324031451102c40326102d004a401d201c040086003018800354842c005280c500c10030300d04a00c00d0348141c81c0c00c118502c6c019 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 773442544 1250 773441294 773441323
    0x3011401030605070c08030901020a02060f01322805240a0513060c110a06020c1207050409030c03030e0d120f0f05010803040f0803040e011e050a0f051002 68
    0x6600400024606800c400c3d80301010f46840560002680c4d240c45282c0c0064072080d0941e5000704204108550401803640e12803001940002d0b95490b1501010100714150030303800801e04554144000c03140440c6000b414008050020008042c2c504580810303c142d502034000185041000050680f41c402d01010b480404c88056081d480c114501066580d88504644814044240aa150102c00c000005c8000304000c0e12140350140b11072410055441c1001031030352251240e410f05025070741c1c1c0080c52010782d100642e0030454490401d011030b490100583d01142c3c0c4035082c003d202003050791140000841912a0700c080c0620302071110016107480c0300e0b0101100140c1886c0d82c06200d40d105800403450443c80a40020341009496040070a6807070136003124a261780002070810810014600704401044058099410070741022851f02103c80d06104107806c80c0c3c6115804070035102001d407000014000200100070346e070780c1d0f0828080500342074420940b09180518800000302d00200d04880b205c07408 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 773443794 1250 773442544 773442581
    0x909030504120303060e1e072d1b03051b1507031a0a2c091902030f1614060909060111121c06080a0305030402130219030b01020105060301 61
    0xc0100c0d4103064444404103508268645000148a06000c629680101f61041102201e00494220961100c002800c6a410842803804d681403a06440c04c8401110794031214a4513842c84000040303422144000c200309107920f003d0000801c26800400814120207908403031090590455041602e072104000c00000039501c44000807202442a888100101c01708a0710400284800f40824000d50540d0440c025000000c4640f241d0600c81401740203100d28143d01901e054540228a140c841d000848000e54a01c0c0c800c0c1210215901440030490100070700c0c00300c4011001106d2041d4100909204140c2ca440c103220200034036040210403101070400103452525140c5501004440111207072440a1240c0035400044040319403560045c480203c0103030368502c0f9064040340e401c00b21000c2e940048420b81c040034030080025003260030740c0d0b07110ba0101c50500b0510040201040a0322801280b1620150b80413402c2c07401f1030f0558041d415150003030b8020003503640d503d800d0500701d0b00d4064480c0300c0d82e0034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 773445044 1250 773443794 773443799
    0x15120406050703022b18200d0515061f080f0a1b050405090610080f100323061b09280605030103051912030207020d0c060f02070909030504 61
    0x301e030003141d080034003450014174000d0340780c00709070450703005001c810300b0080c4e18181910080c0e4103010f042101d01211840140c07506841d0b480e88200680c860300b03822008807095115070303240d8681ea400403080c2d070060305980c1244040d624003401664111005840b0300080c0c20036101498203108002d07090740d002e861f20390700d54456070100c0c22140070060544a4058072480050708800c1000c10303595200000b41c5510351143d08007403c1054041008101600861030080600c41255000c40c2640d04405a00c5240029071a5128506076600058002038140001070b00c448030404a12920100680c2c0c1c01c0b01510403035280d203800c0008442c07110340301c07440300729050061001a2901c00003502003070741010000308003060410112041300d481a4055000310300c0c084010020300c01c0074044066401200e265002c120f00050792a07100801903840203108156000c6511021900c0f13428000388807540021a48101554036080102310480c0d50708814010f01a0302000a09078905000f05d41e00c541d81911814200f50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 773446294 1250 773445044 773445053
    0x60206040b04140a080a09140d0b0115090308131401020106150f09080609010506120609031c0e0a0605070201290919060915140d060b0d0b090705151204 67
    0x400c820140c1400c1d0281340daa10f00000d942c40010400c414880c2c40c1c4030003961401c0d950b1246034807860780c560b0161071040c80d00d00000740181400344c15100c89140302051690300700c00c00c07100b080440e0001003412000040790a100d00c420340300c8000b19a810211030040e82005c000482c01d8500512403200740d20401d5580a454902600c48003220346000c2ca8103001746940c9a9165240400680d1400030907590f5606100700c0d030801d414403400c604420350041a840c10081a000d90360300c6500402400c21140c80b59005542a00c3d8000040d00f150316030440c0c0c40341290341000d4000341010340b4014095032030710344031030307080d40800d245108074068007280307611020001c0f03082c000340440007800444401d5004c1154a4000c069109010140502050000d0340c401e015659134180580360b0051810700c1440059101a0f55a0b000012481039004030046001c081100102e00641541c50006040c80ca2002c10000241070000d040c50440d64100c62103150309030400380303c3c152441032454851006100d0710002d00800d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 773447544 1250 773446294 773446313
    0x91e010c0501050a0c020613081204030e060304030e0109090e1009060603020909030904151401121112060a0605030105090a0207031b081c0203060f0d0804030822060206040b04 77
    0x445060400d110320403031a5650500315002294680e40c40fa50f90740c010a80c0341d0b030401001d40d00084039000e087c0c2c000c405803500c4d651030150001418132050303441d00041c101031141c02000c0c1110006000a51030742001d140180c101005103d0306400207400c240c0000780003441c0d004011302d21850102a0a511072080b038801c2c081e2034200030588480da1200c00000060301c508180d18031a00c8040051511291403404200565000c080c044030303526500d04051007403a0101d447c43d4440709090800f0307820917009013582005041c141120300c00840c800f01c2c0102c0400184152540316803411a8a005225160b00e4256464003080c01116000681d03100001c64101581e0f00a00c182030181c20800281c1d03c6581c1d0900780807001c0f043c00c407070403072000c29103540700d40e002031141c4420320004ca000e50461800ca400700d001554442c21507442014007c00c41400d208810017140c020b160000780039a03880441d4042c007503071b8202c00807452032100c2c00c402000642520205507a405654003503403100d865101c0344c6568001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 773448794 1250 773447544 773447599
    0x1403101407082d0c210f06030c0f090405070807090f060f03080f0c0f0d1101050a140a1a0604090c0207090902060910210e1e070902031f0e16030209 65
    0x2001000032144d1000303210b649401840c110071709030703800f46400c030100d41e00120090800c0b4003a03070203809028210307540d44c1564081070341c09031003c42d00303566036041c00c500d440761552003e0303868011484c1c08101020700d41c0104210048411050100680d82c09440c0c80c0d03030615200180003920f01740155114694200018200b42c8000e104a80e01e49081910b080d040c441000124804180c2880c8251441fa0007070040990000041038104680150704002e01c0140100800c101c1c4442c1c5d568480e01017600040400988101015198603112500c07514260001c005290800c0054412400c0008e1503036003d0090802c080e502510711030600c2d05070300a000f001e608850f112420301000696146071456009a07000e0101162400840c201c04000290380c185118100b0f03034000307a1402003503092688000519081210403c500050780ea55070000401c00540c0c010001c41c620109294001801642c000d01080c06001c5c603541d40848020940e105504a100d01c200c3c05170040040c0100407240c0a0224841c0f88 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 773450044 1250 773448794 773448811
    0x6040e071407050d18080c0d02012618120f0f0a050d090f1b061b0f020d030f120507212309070504050903041403101407082d 55
    0xd00402e036441d1801c09100504540000c0c0e0b0b001084101e014861224500030001003000d011000c40745800324642d5211000c02a0501500900c1554600086009100c2c1c0d09016922815181442d00307082c411400c03118002c60613880350000c81c00018503ea822140d0303408211413010301d02085103100400c19002410020240001800103940811081c0980e8941621880c1240b000c00900e00d0714129424800314020a200c05030001800041c0c0c100d4200c260b610a0100e1240a1003072903d0308801c43c0c038144000a402115108060080582100030301c294100b1340d0322105004e69038030700540704581e000c88000380029022109a4030190300c01c40301c0100190118808103016202d00d11080240e0b00000000303042c0d2000d0420000d00560901202024003c1103074144401c2c20150000360703030303802640580b410a840050513000c85507820059030304140703a02c1400b403210820f4043c0151002c48100c8800340441e059a0005080500c0c003180c24400d5030102020002004480d6407000e20b826000308202c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 773451294 1250 773450044 773450047
    0x6010f27090f051f080c0904020f100f110d0504060f1101110702040b0402040f05100903050a060c260a020c0c03030f09031915020702040902130c0e06040e0714 70
    0x51070325060300400300e440e15074940104090a00b03110b071005503508140740e090502280e007000d0007882408100c0c4450031600f10b0300080151254000521051480000b25500000c01421110200e401844840006100d511a984040c14484040392252040342800001840801050061601981c030150001143d40f030300440c000d4220b80b0081c01c491401d009240c2004020a1136411450240118080003e096900354102232901480d2542004680034007841100703c804400101c07031255203404019038100d401c85450900906085d40140901c0000b84002010381c0030b2800580028091640101d400201280701039030b400c0b91080003034018070711816a5000c2c919000029680070406040001100e00300c0342e58400c100d81c201403030458460318180700180d15803941400f1407001141001c41c480030fa140981c0c0c0f0141880000c006084e02d460083d031008a402034070364454125403224008066035258207412090403c04c02c005409244a51400c03101c1000004141500c07502001e600f0404008015 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 773452544 1250 773451294 773451299
    0x40f0b0a030804150e090a0b0613060801050a0b03150f1c0506071e1e050409090c050102060a02090904022709030a09170c101218050606010f27 63
    0x2030403020980d8000c1d60388040120701800500304a45502200d030074103003881181074000e01c01082d03403180010a80c5a03441d03038421140f0000d44510040b5125610288680c0c0c02540d00c0e10300c0036210ba0710030b00405d8000d41c46104c01081844071041221302502194006912403e00b003000c01c4050b48160484070b82215440d1604000170621500709500741d4400c50250201d483e00d0500203012300a0001120f4480301010045141700350050b8009688004846141031480e40d00701068540348543d90021568500d4500c1ca1428001c014200c132060388e00907030941d0407076200c042c605000d0b4007407030310555030042c0c0d101c011400515002101c3c0303220001181c001801104500e8001005840442c0c500170f990304001540130115901c08500c801078807448241900c122100031241e5910181c0070016805006c5040101025074000c404aa010508401d01400351005181340303000e070082001c0b804c550501c20703000440c155600546000c2e400309060f41c0da41c003200301c8490101d0032020841c88032201361f17024079001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 773453794 1250 773452544 773452549
    0xf0b0405240408010e100b1801030f080415050c0114270703050d050706060501170a020a020a080a0302070303230c03041b031112120301090b06040902130f080d0c02040f0b 75
    0xf480780c45c3c6901030103845e051461b1206041500e64140e0681d00c0f03000039076a541c40d030390201c11403203054a800030307041d0032000c05034908410303d4441d44c0c100e80c120201b54964504800d50040090029902040080c80100000504456803650070349000d0324040580901c40207042c4d00040800b80c10000c5000c03a01d0940e174070f4035440d0070b09031402550740c0042d90005849003409100c8c010040104428039090528119000c0e03407403400c2c0409480300d1403154002500f01c03411031003007000001c19901320400503910721001501500950041c1001c80c0484d0034003010102e64440f40140fa41c9205506010001d107594400d0703440700340d920050049810035485005c84268820411802015510801040e0f000307071140010440ca507400340b0101e403183e40c415051051030f009490252030443d0541840800c0d4a045400010903d00583c0c02043c0c402c0d10200d108694124103c01000c100c542c803210049070300d80c40700016922480060360b05008108425045d000504265021488a100c008000617800000c02c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 773455044 1250 773453794 773453801
    0x10c09060e03031c1d0606010c12031e15050a080304030f1b1509080313031e020402030f060906010215060f04060e04050604020f0402040303020606240f040f0b040524040801 76
    0x41016004c0e0340c90720400004403000404d030b6140e1404c1c00080460b854210700003004e04580c0500180649042e8a015101034000c0d04150324240780c9100b1a407600d0704ca04159401440c0a68441c451003520b0840040c0d02d080c440c5034441545d00c441c014601d81401c584520b007032182500740880d408190030f43e049410140c0641d8440103002c03000141c600c1c240c918000141051141d03001880e098204201103114290380038003070001c0b03a900000c85d075200b1040c042e21036100c424071400030b9042400007080003450a10b800c071841c071075503044803110465203600c00120ba0300e250082c540b9908540c042c000c50f06506c1d1141c682403a1880042011a52a4076440100b244040c142c07811102c43d8004070078001145000300303d15101103c103540850a0503c0d58030001cad61544050300c076038084c40620314a501c56002150740b5820040010240c00d54405002d0380440096005224500c2c0154001c94007140704a8030208407402ca8000401001085c000250441c0320018021117000d542c500c10400020225002e01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 773456294 1250 773455044 773455087
    0x140127050424021809070c120519050702031915180c06050d0f051003060b060904060f0f05060f0409020a090e07030f0e010501030209010e220b061002010c09060e0303 73
    0x41c0c0507072240314400011300c03189034000343d00c0c0c800e000c040304000010390312403c030b8041c0a803c150702041406031104159090710030b80d944030405002100c04450f6132504100200000e520030303000c42e404c400c411306014007407000c01c01000b0040a00603065102100c0c09402c03050385454500000548040b0680d031348542079840b0780c000030102d603001c50507004280b000d1052034003074440e20100740058a0207144c068411401c034040100076580c2ea17845140c0c00e45603081a0740c1c80b0400680208a032b262950086003091409100e07842040200400210b41410100107980c44902c0000800d4142814101e6650103500140120320410032069070004100c1940c00311503003d80ca080d1000102801c20303012050560740681000c8100c2ea04041c010801078440469007411148003200040b0789480c1e00311104c3c502030304050340080201e05010fa020501940e20201809140e049524064121804c0030036403e0700caa00400030046280040c04006050185040c100f0000e401010f42c2e1400500300b413074142208415 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 773457544 1250 773456294 773456363
    0x19180e1603021f030b2d100e04090302010209060d020912010c0c020f01170c03160306030c2918361b040803041508090613080c03030a1401270504 64
    0x41b211002d10709041d6890030450000c0d580305180c0082c1e01e10180820b418026440c0c0219692101001454400e6056800710700d001440143e48001030a0650069006074510a104100e40304d403c0591610510454180c1121929111031084068003085441e118007050b03075042c000041c02076140b200c203000380319100700e00884c8000d07104d0600c040c034070b18001800c104000500d4941034042c408a1815100c0380d044905e0108181055031950051007103620102c02400010710300170a601c2ca9881c801000184001020b1701c6040c1c084181d60301108c0325689848406a110b4041100c8440b580e03140381400d6409003040409107151b46022400d0b01c101c0d440341c0d0042016400128062160441c0140301030801080c078030b030041b89400c4c1070503240d4480c9400b405a401c40102d1306590010040d02c030094400301d041d00d0b01501e45926044017440054107000104080704030500002081703c4ca00b58040b61029091030f1180411030342031056a03801403a018009460403800603584222440120704840d4004070503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 773458794 1250 773457544 773457589
    0x71202060109050c0f0f1b0a060203040b0f040f030f0509031905061003150c090b07230f030403080c0703060c021515010e19180e1603021f030b 63
    0x516182d03400315800a0000e800c1041304100f80f040030070050041c0e5111100c104c03038003580c4c1c01401c045144072044030302039150f0310b000f14002e01041c4455540698810b83c0140d551000c966a640c003000301c0c402d012a0002d280307961001d441808680729003038400d610b0700242040781c40c0c03400b804000380c6015a0b80f00b00f4000e029100365607a04114040c04055080003154038403902d02403c595615503a8045151f507114000d80da0000c101e0785611078403811000f401c1c81582c0680c0c0e50714030700b41803c03040d2084507107080800ca1264401440c2100003581c0000e00b070030300040e43c1000e00b15a1184403652189503001e8107485580c40100100b015445440c81203105038005044024000b900302d81ea040c00103010039981c00103840c1d4404d00d642c10420350100a03204481600c040c0f48484241403544000b030b007000d0000c4d6441c02074003200045a6005006500d8940200c4068600389011808000b41600000350800a1024040b0f03d64910703a18044c9240840c1c213012503030700c10b002d000c03800c0009c0f9000c0c000801900e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 773460044 1250 773458794 773458799
    0x2180a1e05060306060d0305040909141b030304120206040902030c0c061f0e04050a061109010201060504050408070201052508250b07051b19020306060604061d060712020601 76
    0x1400c0031000c0e00509090040c0494981203000940f2603400800d85401b400301e85250300c0426106804841c0900101d40081100041d00e0500c025501002c29160b0424461040010b0f01c1c1036000143c1c1c82e041200800551400d400d00c82c404e10301d43c1d109001281c11078010700c00421a50900d00240d8410fa0032a40303042d444020050480b841d2690103440f07511095a050071501100102c3c14002007a90410301040000303485070300d0800d140005050024001600e840c070740840c00045c0500620001c10260b0003403180e680c8801c00c020441f01b0550b80100106004c1180600550003600502106c0381c01c040d00030b003061ba154444043d0616a900129040800003403000c4407260101d002b001c0062518045642c1079400d582e41042541001d0044024860003240100801c1c603282030103c403001103101922140316014140322242c9420030402c03482070199a00040503030411800340d03800c03695240d64000e103512080d0028034900d188145000c1d0405020043d401c0441c070031448407050619603a00400c882d61 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 773461294 1250 773460044 773460071
    0x30207060f0506010e0a0f060c1a0f0402190803090f0303070f0b0402090a1a0d1112030c07060e0d030c06090b0c12090309060a1805030601080a1109010605041202180a 73
    0x41260800d441030260750341c18000c81047d05003c40c1500c032139003040c140481c02406d0012040c40032003085a00d00540c2d0381040ba8403540203012030b014500c2918030260304509014050b285480600994825078010320288545180c000780032152080c0c060150f070725240544c0c8406d00006c8007240243c41552550041c0021824058015540107002d01d004000c8243c10011f500c41c0064040c0786548210081d284540c103002022481c0034000d42c00426040c4100d110040b0707070761660048001c00070700d4001c2010008249005407961081c2200003030845903280c0c6035540c00c1d17950440c0d090b410b690142c1e80d00b01c0c030760002d000708400e28083d40007001e00640310007004800e0314040000404a1032640c10620440c039280d2500015144010200e08044400340640e403d49081462241c0c00650b261013514000100a03e0100306024a1401002c102201a800c84107101c9400c0e070a2140b86d00007034040204000001c0580b03090001c481c0300800301600b04d0301d60103c140d4482c1040c0c45440e4550340c1ca05144c00c004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 773462544 1250 773461294 773461307
    0x250b0c0c060a02120403030504020406050a060c03110d02060f1b0f090f0103060e070509040219031e050115030c1101092405040c17150405011b0c0510020901030207060f050601 77
    0x1c2c0301d45070158a03282052042d01140180503000a090548a0020034115034880d04001c000c2e08018000c21841983d030075000f424440d500c00243c0c040380000e40c4d110090030000c16002d4990f4000e4000b0203203034407144580200210018640400c460102c00c145501c98220001000b03410b0100c2d00c0c21b900d51444030104996900b03e5101d403414185040750030000942c0440b1020f40c001080c1c1411900d426612001c20f0191042c40740300d411300c0310f10280881c8400d806500c00035000000e81e144606a11a0009250480b00280580310b0b032a9941640c1c052454443e03006812010010300d010f040c824212950a801d440032010210341101001d0184a1110140a0300008540c144c560600035410640c5a01c0320040c4c0340d0090400d441c410380098007171442c080000210200350f00340e000c20580b502d414601d001303080700407840d1000e00044d4000c01140f0f00c650700000521307400070b016007032651710740014400940c4614505030516801380b1612011550314801d0807141d400c03560303010500d032503e0300005105 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 773463794 1250 773462544 773462551
    0x80c0f0705130203091b0102010b0a1d0105030d081603020d1802011112190207080303070302031b120601031a0a060504080f070b0d0b190b0726250b0c0c06 68
    0xb074510500c200b058080307001170841258104011408000c01d901c0d00100d0141848070603c503004056400d0000f0800c1006a010712408620041046617980f680700300b541761407502d903103100011262030214007900c400d00203850b0140c00a00300186460707018101a07080e20340071300c1f418000b0f070881e400b07400a42d6009010ba010090030340014003048040c010401d012802840c55a00b22548411807282c40a0700800032000642485400c4a444c1d2410420041c00395000320f80440280e5800100e151340d2548100658078080075100206040c0c1d603850004600501c082c003064a660b0180c04102d0025031181e02c08800644155a07410342d64070b0400c600c0520b010340744200c0038555407042a0801c0510800c00c203807105610380900c08590b00d241000010303800c00d00ba003902c0c0c400303006240d0001100c510307034030062030b110b8800e00251416500d000d80c0c140c0c0d000c062926007622000c00b0015200d100040c01c01c031501c0b1350441a0702403e0b010b460f80301d120602c4011140759038204800100e5103682101000b51952 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 773465044 1250 773463794 773463829
    0xf0a08250e01140a23040308040b130602030702151c020a0f080f150d0606050402040f0306050a06180207051c03050417070210030f020c0a15060504020306030c0d080c0f0705 76
    0x4e80f2910b2107000784042c0341c0d0041c40000800f0f04032100082c14100782140c00464002d18110307222600d50f901c80c03406030300c070181a8068000e03070400001d80780c0c004010786040c160002e00f10750402c08000109a0035074407108607401904001c030040070f03100815101900c101c103419614100042484840a0081c030700142840c01d245206104004092501d20407038100050b00745d9100ca6031018515100010300246c0d044507522038004600030072106401c81301201201c2c000c420a214036162031401004441140c01011800100d90340714101c2d01b81190000c1010130b00c80c1c0101c0b50355014800303400790301c08055040240001e48402c140028008105440c030144d00d01140c100d45494207550006620560390500c560601d5202c9600e898071205d43d6060300e45082c0140d00341c58040c14030340b90107202c00d001041168140351030440041070500b010702c25a4881c51014006240f00402c007420800c4d03c10394403400300e03080603007000cd8401c1a00140070302c0d04180070100092110700d0a0408205402181c1c2c0b46960 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 773466294 1250 773465044 773465047
    0x91e0f040e030d020702010504030c120303050c03131b0e0c09040b030d020a1e0803040501050f10031a04111c1a04080315030c060703120e01020f0a08250e0114 70
    0x7444800d0100440d880246000d0006035168102c5c401030b2554019584040c0c0300040400303000490204801480040c288a55030802031071760b843c101385055010946905d5403440c40090100c001880c2c01800b001c0c840e007804a1003c40d00d46d14111040c1c0f0b040c048650002030a00891911000d0510340180421210704402500c49000c2150000350b0b50214100040e082d141d02c01c1144681c10030701d100f030024480c2c001888a0f030701e00e00b500300680600001e541c2d1600750041c0c480003070540d401101c4140156580220b00d502d55900d09041c030b1401da84050030551311800041303a01d4465541e440540c0003807200410305440c4003a803606000c546401c1207021221314900301070801000038a1360381100c1e4810390184034404a508000b001c40d28119a0608180d00030200141200505802542410440302034420a00c80300d00b4004165082c0d00981d100103c0d903200034046440c499000310286036004c0a801455401c0861852240c1c0428542000c420f0104008013403040440d680300f480d0030441030300c070310707506 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 773467544 1250 773466294 773466311
    0x70513020405031b06040e0a1b26041703040c0e07020303070c140109081b1902031f1b0801060e091b18030a050f060109060b03061203091e0f04 63
    0xd4031012803500b600042d914400351301c4810b5a0344025200503201e500c0c00c486546ca0300b401c10000a00030007002c18801030300c0111440705544903802403e20716541d043d41e0010340c1c0c5c1444034019244805401101c0f0428110154410f2448003005144142e00804100042503c3c1c881c3c190610580a029030045400410404c41220f8103d10380a5065030320407800680c01c5000d41901c1d004050b49400204001c80000d40100004078640030328424001c000140c40800c90404201422030751101d078000d4064022a24000d0051610141c14114442500020032075514403503420000003c0e507004400800d400c0720040c0110350f0700c407442c080340180a46500c40e507410900b40b1103150000700f02d050041400005000f95003036a050300171444202c1d0117821140c096640c0d140007500c84000c1807064040c3d11524000284680c994020041110106202c842c030b03645a4005100f00c034070020384100f8403031000b080003070260f407076900b091580c0102c011804200c18100304200240140d01c8590284101c0c18801b02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 773468794 1250 773467544 773467549
    0x1808120915060609010e040f15051c0803042a0303030f02031e1f080307060b0904031b0c17070501030c05090102060c070c0305030a03020a080a18030f03020c01020c070513020405 78
    0x209500407100b02d40703a40d1596044d100407900f00081401c1c554000742040c1220b4910b0f000c03604403c2e04042c0400e08c60104175120824804208400310215544444210415002c107074104000e5410a00032021040c1d6013400f00140103a15980104240205068800030401e166040c86840b106d03480d4008103519608202100030390300101c9a0110300708804580c04078021f0b0000641445460000c01120100c1581c0c070081c8503140d0700021810b845481c181701140a0520342074254038407036949034407910b46016000d1404008903404035411149010040e074007203100f0822002c0780c1420100e2200400105050000040c20344848111040070310400b03008281e010780c2c011070b400b60310100d81c103019a00c8800905000300a603450341e001411074000020660795042d85600284508025515640c6080e21b400d952402110030a0045104031120500c2080c0043d10844000c3c100309910301c1d015003840c001000942c220f074001d6078007050b560302101c800c100500b00044610f1503800d40607011800d06142001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 773470044 1250 773468794 773468833
    0x6050d0b0f091c020a0b0601090609031e02040e060601020f070f06080c0f07080c011808030c0a2c01091e060503070207080d0504140406031e050118081209 68
    0x80d000040c00c8002a01c6040403c2480146991407600c1d0011601000c0081e4840440c0c41040e0385100038180055151b501802c40d02045445d40c0d40d814185601d56240d42c00c40c40c480c42d4031000082100d50090001d40d0342c038020340030301039107a0003e01a24202440064642142107076402000d400284003081703c40c124100c454103c61039420100301540d203135401c08000c0d03c114203958034030b00000304040b000d004505000d08840d03041c900080080f404a1443e955035416540802411101c00300300088072040c01e1006402c0b4034015050203210b59241001c0b640e44242042249200d5080350901d000c05503a20080800c020000003085480003a4601e1b15035003004540d00881c0140440000407554940c402c01118005044220540c0c1001460010041c520f52003440390302151010310004241d245083d1048804603a8000d08141e02812840d800304520700d5800c42c1a10f1955036140a682074540310f501c64003c00d0b1190360000d540d0358018100000e000c00192040b04158409000e00301d04075054030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 773471294 1250 773470044 773470051
    0x706050d23150409050d091802090a090b06130306150b0f03071b1b050906030f0a06050703060803030f06100816050717120103050d020f2a18060406050d0b 68
    0x220300b48225100c40c004070703025015004005086204024421804591100d510381c02e40e0320380944040b082d0020104031080c0c4c000c0030540c60713101c0c045e80000c00500540d40e122400b8107002800c2581402006103a0420044055109480c80c1d0f4460400301041c0e90b08003a4500a05050790f90309003400e07504d4003800c000b400b0051440080c0a6288420721003803403580f40b41c01c581c40e0300080c42e803c034100c40f101407000c01000b40300d000d010700d40030004911646030104e41e040a039010380c0014001c5541d5600d03140040c0074080d10580c285a41c0d0315010420b01800d00055210f450320f5040c180080c2007000610240142640101e0300300074440e028414421040a95000c90181c14500180c480c0c000d8141581c541d480c2d01410b620421000600c404451380081146040700d00480580b603441c00303030075016a1129140820000350340c1040d0150584200c4401e0820300d00340c411040c050300c50725250045141c134a20f42c205040680d8000d0304010052130140102d101610301071b030f4060704904040e90750844540d40034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 773472544 1250 773471294 773471311
    0xc060203180a110109151d0a091107050c0909071203051201060f171618050a0305031e0a050d0f0e0610090501090605010e13020c0706050d23 62
    0x11410200c01424000c0d2019014002d0315400d0316946803406044690641103404540d0040d4002031900032031100400700812a20384002400005d039410800c402c0707288150f54011180c1c14041442c0d242d81c071403070040c9903112102554548241c04c080d071a1010442c03840f80304401c18810060700c18000710307000b801c4400c0540310a2900e0424501600daa024044074120343c0320100f8000074071140e001c40e0f01c84014a0700d484054030307590641281e1840860407141e4841c4280395030411072007107109000103004542034000e038100c800c1e141e00004804c00d0040e402594a40c0c03020511284002808420161752104154811b1401d0300c44403000c0c0940c050104a628100e03a5a034403011600210b411407584454490b041c0e038400d2401c0008000a80c28034080c000c0e40070700e09000496102094442c09040d200141c540c2040312406004011f1290120203040400d640c0038814981c41400401c280006846240c450b1078035105031440441c211410956040b600d01200480242e420303004543c0250080104d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 773473794 1250 773472544 773472547
    0x80601030302120d110d0b010305151e010903050307030216150804060911030105010e01060e0909060f04050a080f03012d06180f0305160e0106050d0c200c0301050c0a0c0602 76
    0x45140d0703004001a1311092005e0740000307608014100140c7c450341d45500241c0b01080f02c3e80742e48000d0f00007140300001207600642a214000504140c11200c8992018140f621800440d100d81d169030854200c0d820840140e4403840d000307215040f03080305d94400742a940c940018200c1c4500d400034011500941702600035561b8000712820b10681030708812040001400900055a440c201814280f5007440f0391000501044104001440c0014416000d00e500c400280707001d03180c0129401e0300b00b0024200302c41e0303486881d00402c005140a0041c0c0f502e955512202034580d0326002c90914104444140040b44140031452038440e00ca51440c01001c0d41e0b140d01e82413442c1000392a80f1094480c2640203c84e00e903005940000030000009400030070480c40788200c60302c1c2541e40ca901840c01401b17000d081c002c54003d024150381d602a5500881742c40d80240713044045802ca215410030a40d000c00072158403a004500c40810710705003405001d400070740c010b1070390b4641010554024086098071200801c1d4540 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 773475044 1250 773473794 773473807
    0x31b0e06100212091f23070c090506060913050609180d03200c070f08011107030f0c0b07021c0807020a1e02040507080405060105060f070206210a0e0708060103030212 73
    0x50b01030007542c1001707101c00b0283c3c81401c0c0f41806001c80e0750001054000c0420a4003108901c030080702550001503124007040b03251b50606041001814004141d1a00319100380032402d642e036101d0a50407000c621200d40010701c0d0411030280b207a5024010101d0482d41020740700b1280324400058605411070503803900284405004107190005911400190124a000300f10001202c0e0b0100341d29084494011007061500da46007a210701703a40346001118802c40f410300c2140b0209006110001180c0954039001c8036000245d590150b140d04180e82030801030340560500b540348404401001e0640c803240c20094254a007007240255510b080500050035482422809403c03c1e011825403000f00e64010700c00d122034501312800070102c48086a0175902c0784070303200001889003040700845106001d904009860f1480303c0d003c1c030000c4c1d07000256401c0d2101c44c2402803002c0d10b01c1580c106000380704034034003c10401080c0c00100c0c40c0440c1074005000c5a04070800410000307030001031622403503203282401500c0e400c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 773476294 1250 773475044 773475049
    0xb040b0906092b0c050105070905030106120503090d03030b0402040b0c0f280c1a0c0d0c020603150d0606080105090d031515051603050d05010e070c110406031b0e0610021209 76
    0x2072132001d00600315800c1100344142a0340109601c416188190000c004043d0381e603488880124000c42c000e00160030030040c0807141c7c107240d04080c1d0b00700c1c02402c0100c1d0710300301140860b089034490f40c458500b02c0c01c0440c0c0d40009800504c8006065251040184603001ca0313801644401c00c3c0d80c0e2240e0807000007003130816082000c00300480c80100006002128101c044003807140d1154001000d28041d401403c40c03031081e0f00d014a44040e003480d000380c600f030704540d80e01d0f24018030300c600905280c0d80304002c2c1700c20100051490040c1006051170200106880c103021028034030b0f00d402180407106045c180b80c110740341c13a1680c005400448225000c07002d007505a9500580d140d2080300b071140314011540014009040d08903008040c13200004c80f04010503a0307141c85d800c1c4400000e48003c00041c03400100c0d0340103d150050b010040d20320007000000c6d40c680d0781e81d802202c508a51110303203090320307200300400514400303010440c0d00800c1529440500c00506030020344403544280b01031200c40000c40c1450864 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 773477544 1250 773476294 773476307
    0x309020f10030e060f0f0906100909060e0d0c14072d080a030e101e200a150c080105010c08031b070b0a05010f0501020a0215070b040b0906092b 63
    0xf2640800c1c0d0b000340c1045000e02d82001c0086400a00206c001001300700445800128144905005065100d0311401e160f0180c02a040040c4161149900d912040b10705c1841408200342040c0e42d600c520450103000d14103c2c1042d80741402070921a040100d040017414500f285200c1552950040e030880c8407116500507080c000c80350050388807442214050300c20150060315141400c01c0031210409000c40d800c000305d07130703052152503171401d0b1103240394500d41814020075070b00510070402d4461052640d40c20600e640707040c04004040d20256522065210741c10954400c810b255005854884065810000041c00300c0d4582a8014402000003000408035045500d4404889c3c8103014000d940d510141001c04c1c0024080d81c0000d40c0350710703010002a640c05031030441d200b29001a0042c107a100d1080c4c0030007565011241d00020043c40c04c004000005405501e41da101d5031040d000c01c1d000d41000e400e41031801000500c01c1075940d22002108003000c42d50030540f24100104001032142543e9010121440d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 773478794 1250 773477544 773477561
    0x11070303090f05010501030b150406060e10030e1213050901080c010c050c030d0e040c08093a090e1b120606070219051002120f0c03160c0509070309020f1003 69
    0xf03946410000700422220b41085801442d94941da55601214041000121000c5220720350215100e142c4401da50b040541458140804505000034400c0384080014146410005080c8000b075000482c001402c014a28050180405413460b2002d581170180080d034800103083c585c7e040c00400703100c41c4204901001080c826000c0901070b9403440c0c0c5103403009000140e2007400140300e142000c58040f00c3c035100308209407084803042c0080c802c5c103180700821040d0102550030701e54503c660101c84001104102400050144690381759501c05180803000048400c024000302400c0c04801503400035650344100380c501c49401945016140d03240c10380040c2c1c8903c98070740d000790010110781103921101146030100302101c0e0155100445c8414404080f82c84800b034241200c0301c80001d0110160008a420103000304070240000c0b04e00d083d11859240000070350f810f03000c55080318010400d000700c1c2001004a80c00c1081402c003840031460560000da601c80000c0340c1140908036800c41440094403a80020a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 773480044 1250 773478794 773478803
    0xf0b030a111c0212010e100603020306181e010b03090d12090605041b0603020405060f0c0a0b09060a0c09061b020118090207020f09060315091002030106020c0f030111070303090f 78
    0xc454020b192120040e40214103007418240d20308000003600d81440d683c1d18840d10150050102d01828003100354025000a4401e81e0400c00d42d1003410003642d6903281482c020080c9403484050410070303800410100d90160400f40c01810b0500034440300f0880080e10105100c0c160401000c0401495082002404024000b07802c0320300b40300c240001d11041c102242049002d900300d440000e03444a800760240c1c40303680320751604400200070303107580030030014050020045110705450146400362203c5000d40410345181609421000a2040050182c4030700e00740820103082c0082017074070789500608014001804d06105580035018030086a1244100401ca585002040500f058170b50100c1d200940104030201d0090751960041d10040c54410803440c0304400050040c001074001c0740300c03203980880c094894507a5200724184502c0c0d072501d07070000d18041c004079401018131071204401c01441c1701c040c000042c0280d14054981e500056110201e4013003036010b04003c50214050301d04115810b4038900041c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 773481294 1250 773480044 773480077
    0x1140304032c01030b041109060c1e0607020c0a1401270b09040b04052707080d0809060f010303390303060e0f01050303040608040219080d02070f0b030a11 68
    0xa90b1107400951030142250a981c1000b01c541e0504c180400c0f503a2944036118903010510540c0c900f03240c000010410a55440165010303d01c43c1b610351003582c4900002d801258100c20200300304144d041205a090fa141200c1c5050414542803d0804584807600040e041090032400c2c2c41000c40e030810000b01da060b0f60b03064540e21a6030b41540e20030540086514a1080c0d040c4a1096108d241502519004500007091402441c03012402103280d001083c2c05505240980880000d070580180026261901180c65101341454014080d40c107051008212080d51a241c000510120343d01c00781001100850300412a00d81e440504840c0804032030f1840d40ea0603a569448400415130b01d904810129003a590085d400d5881d170303074286113080400740102600b43d84140f00c20807800e40319070349203600540054101c501c1d148a030410b20350300020755007040459910000d098008039034108041d00050802c0382c00400100d00300341c021195444003030003035070000b40c940c2c0d030380215010440205c81c0d03024030081603038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 773482544 1250 773481294 773481347
    0x30b0f180d18080c030c012105150f01020a170a02011409070e0705030106050a0c06090f050c030706410c0d02100e030304060c1b0b0f060d020114030403 67
    0x20880310b9030b03010010680c042580c0000798407100040e035420141004029184202408004464941e425040303000310766040c50703114011080354410140283c14950170210b4510111081c80031403001c1444082c115030011800c0c002080d00c40b0070091801c4100302c01e0543d1980c525101302e0152441c1c4224018889000d0180004604000344501c00c8840304011304e0340c25601c05400b580e03a40400d01c910320100320104003000308144900014030229100300780008211700192100703000e50001c410111442e500c0903191102c20710b000c1007450f00500300b0b4500301c10b2440ca810310310070f2851050f840a0384000c88504800240f01c00300300340050b00340e00002e0758a44400c42e220183c0d940340d454017101000740c001d04c9008503070f2402c940076099104010b18000c42c916100c17551003000a02030035142c00208090502c6605020380c814644a8009000f000c43c1500f60030070848400c0c0441014116500c18250300b0034032001070741c01c0034001d602503524058881c2c681c3d0701d41c1000c2e6035005a2000c09800181140b03081d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 773483794 1250 773482544 773482547
    0x5060a0c05100c0c06020a0311042310050d0513051213120209010b1803030a030c02060f090d1209080a0f1b1e1a010605030619030b0f180d 61
    0x256000d0602601c21540c2242e051210b0008980e03c210810000841115000c408103e00d5002082a02e50360301e0b00165005002d2002046030f002500500e103800031208003d00c1c008420030341c00000303144c100e0300f810030741e004404090528031546098801c0706441c0d00014141b15441c10000350904d40083c2942c0d022840c0740010a070981c06124044203140c054100443d089a441c42e000d1011070f4050f060303104c9642810383c000c0d40d981060301d444030b54900b1480001a85d840504c0609510505134901003201c09980b840603041040c0100865500850300701004002440002c20300521211410481d6441400040707040280010302e4000c0c0c01c2e9100000c0e400e8106602040a40ca25007907980d5549580b50401c040811000b030071100078000c2a0390000264030050760700ba01c10640ea00c1000e40302d40d290025400040040d00036402400072410110401a0a050003030064103400302c0400c088405904542d01c284440b440545260510342110300011f07036401c5901401604024150203c07900c2c1920314a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 773485044 1250 773483794 773483807
    0xe03070f05070b0a020a0209040203010905120c0d02010b030307020f01180f090c180e180a110111030f160201121e0b19052e090302041404110103090c05060a 69
    0x108880602c11003000003000d0034440140e801600c41c5034054082071819400304aa407090281003070381c2c0741d56107400b0070740040c60030400701c2403001540080e1600e03400040c5469003410341c40500a4196418405101c42c29030300402202c0059504980e0602c4205e4848012940d816035025003140c00d46030f00340301080605c5400031348000c03210180014444441140300072249110301854810004031b54550070b02c40901d6400480c0d61001c49000c0b80f0300c08018543d80f00380b61941c0b44100b9a840c00c103500d030300015541e20692403110025000025450801c04465525081c8940581d4200301d15009652408582c4500407000340c1943c07239007060000c0d000c16403540b1a441e10f070315041134400e46400484003980c00c2c1000305080c0322101c07007015100545402d0600021034944400f0101151f4000b0402540d4800c1c603032002d01c1d501c010b0380c0f01c1400b681188180700445581041014642e5040070030080000c00d128800c84200000b841c01188000040c6080080c0a05541003140d10a6020032418110b95107c403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 773486294 1250 773485044 773485073
    0x8010204050f100e1e0612060a33050417010b09010e0c07110d05161508270a02122409030301050603070516141501270e0307 55
    0x10b422900640c2a00e040110681a800c200c0e4045131042c40c58403801d02e80107008030500c480c1652180340302c0001c94002081503000d8068030750205003003004e2080c1d034100500450701520400c1c410804031005080d5a090b5144800d4580005440c03010700b0440c09031240064400400c1e00c1a07101200712043c0300e140d40a4010000200c0c01140d02d007000041e00589a00520701501c018850a45007803080d80340c84565119000d0b15030382203182a207a60b00050000c108803d84441e9480d0300d41ea0542c201401c03201c0300700c41c40c3d92000802c038841c000d120075130f4076100190203440f0507041ca0501a42d00e00803541d00300480048080c1d40541c2e2204242c1034030364049041d030801c0190100100349084102c103181568401600c031540c1651040c001131009003004001143c00580c1410094288201c1406100c41c0c4005103501f26250344050090320110001000028005285404035400640c10403442d94404400c1281d481e024500441032010038020b1584404113400c005000da907521007640c180b2480034801038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 773487544 1250 773486294 773486299
    0x3120703030b010221070615090b1002030901120e0a170c1905070603051902030106051206012c040e070b031602030403050d05180619021908040b0f090306010801020405 74
    0x142c03038105030341c40170818411444403000440e0440342c820100201340c0c1c01c0880200d0780d031130780e07041d00b07081d01c00b804546100104198100421419042c100303210301300c441d140264013554402d21200d07440d607811a040c1c4060382c0d5005000648242c2d4184950b02d00540088040d00e80c0310122020300302c5440321402000716114000442d1a80c0346881040d02c110400000c01030403e410415003405170502c26000390360820800c40c02825040380e0803882d00102d030700c00e9029102003100018484482488500b400e940001309080c584642040340c682000b254040241240c0062104607030107110b40ea41d0350024a03003da010040300c80e0381e52600e61903046a44140c5041518140b900c0d552003c16200104540c00d50303521502920004416000913250794022100340e5050079a010b031850170946500002d0071310070401015a4070040d0b1803801c0641081c1c4170b1121181c1d039016131801e0b0000b064503c0121811a04c0d815a2103580e011820b803116054068040e8056150161500000d003058054000d842035074001c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 773488794 1250 773487544 773487551
    0x603060504110f0f01140904060312030606120504021008060102010e0d030b0f0406060219150e030d060e090a0f080d0c0c14060709060507030c021507060612210e0312070303 76
    0xf188100301e01c4644100c078850000f0002c001442c0302d0440c10001d015039040140000c0341c83d90302c903600c20601e50358a00d4075a0020380d60f14801c0000325840050714103195040ba004102508240e004291000001e111020038002d0010204030264800d61099640c0c4050714269400025500b10041c080e0849010441c428841c203d140305461501e0700c901c80031600389400034884503111910004a50000310816111034258000e418000662030040485000c07c0710040c40e0b0300d09031f402101c021140f9642052260040c60010020f8244000580205141c2c11041403c200000ba01d0041d015106056a1400090030622000c410a41014010482d10721944894142080301e06203aa503400c8103c440c1ca001503000c403000c100142c0103500624508c1e010f4541420409400c0d00400c083e8803c62060512280c1c0018525050040ca44262805414904401d242c0204030380c440d85980100c10b00c0c151b8040002e00c40c0110b01c58081d20b00750f802550050180d40c80c0484400140f42960810314041c0d011a04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 773490044 1250 773488794 773488819
    0xe09091002190e12030702090403090506040321030902060d2007030c140102030708040206090d06060f090b01020a080a05162a0608091015090905010606020106050d200103060306050411 81
    0x51442601c44130680400c02541072060503020091045000791041d801c0c817092240c0031540c1d844d40d10003031020314082e8584080ba82d01e2960926001d401040da80e03001c043c0341600c0900103070307100c408440d865452a100455080d5000d038010b021821036084c0d03041805000140c0348200b40e000601000d085010300700703031021030310040c204a0a038841200c0b10f000051801c0005001031030000080c0c08981c202802d1400390541d0381c0c1c1c41c40100c81c0300740c01c0020b0242a08500b00311001482c0500d0300740c00030a1001d8a07002c070070740d5103000050017031510110920002286203508190b04051004c0300c2a001400d080c0c03c162400c044070201d04504c8614a00302c5041c440201e00d06008014580c0a0020480103041070003d84201800070aa015601d000e82d841503940011621745900600004601401c00003032014900a4040e0856402e83c1c0031f540600d0f0b02551110204401120246825401ca05001540207000c00101c1c0104040c1e000244101d01d003005000a03c07405601000c00b0b1a41940c14550044 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 773491294 1250 773490044 773490049
    0x1006120605010b13091d2a1503061309020a1514040302010e120115080c090702150703020f040506030a150e0114120109080a050d1401060e09091002190e 67
    0x20900e5250182454420000c00803202507901010226a60044040d035031001c18181604011000328407480f0b00742880509408012111915070f403e01e0106d9007807230718000210340d0079958003006140724412040f043c01d10052000c00e030030a8060b0b66004244610190b142d0041c2a825100d8901241c002103032800d019900b040240122810340c0d40584986e926a884d400030025140b601c5182404155242c03a2901d039040002d211f0030001d004a14007034040c44044400b800b0a00c04009c0c20481154801c10901e100c0c4200349417040d4200c1a00c2c68003690355030003512042590b20941d44255040000081005a0380910f0327030040090203c15454a10f40641d5042d4824442c00300b8091181e40c440d500c44500c400d07280106011608892080002c90141c3c600d80703440702150084100203010403030004103415228400e221307403d0020003140051615504101000b406070709541039042c0108980404154880c9042081c01202c0d2003501056544000b4505461045030102d040200400c482c07048148003071 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 773492544 1250 773491294 773491297
    0x15170415150906050d0c0e0601111606030b041407080705040e160e09070f0e030709060603140a1512031101090602130b070b1501050f0304050a1403090901060f021006120605010b 78
    0x98102c1d002c240d105040c18000c1c0007c55024042c4c6043c001c544449242020041c00141c4444410540070040b06240000c00780c00da540d604002032245140000c5034148010b00031030660040002e140110860352110340c140c541e072081760000e800700a0541c1c01c0004594080203024001e04550340c41920b90b4040c0c07010b01c014403100703940310400724004850008005200d203040070000a80203088602135980e50700302c04112410303504031400103600e0b1681001e507100c0d110390355500000031642c20407460001c000500e01c4205240500c0305c40d10070280c45002410b208860000303003488490b00030406807481d454840000c0d0b105c283c1c0c040c001c80313024200041408a07041a06c0341d0a030042c1981e40036944403c20190000c4c44c03a14000d0600034280050f4001c00401d10285110300d2003500100020103050810418160155501603170562040009100d19111114a141106d985041007800390f0303d50b07501039040808076076039400071354540140000c101c01003209409066000e904108a03d03600d402c0c031341046 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 773493794 1250 773492544 773492569
    0xa06050a090608070341040309050d03120c0903260d0914030412050705120c0d0201030b060d050a0f06080706050702061201120501061517041515090605 67
    0x2150060800300002c0e0b00032207400303a02c102d0707620b000220101c40d00c101e07060741220321254001450700000e140013204103004206084400c55400d80c90715142507a0000d003e207400e40120b074004d15031b07801d0200401d4061140203401d42c0700080c040c04843e039600301c020300381d941a2009a5403980b6400f008006e44280f48030340d06140d07200182661130080700e0894000580081c0d103007101e0f500708411850b90b1a9005201900182c61001914142a0141d050041c0b03000d00701e4019074420700403001035850395075000035042c04403201680d0301480b514140c00160000d112280300980c111400084c407844039007155211074030a5040f070100b00a0030810030b000c0000c40f511400381a0840e0300103901401418010700241c00000e00c001e29813881d1031001c5080c103401c0c01080c1d200d2a05400e40c112850200002801080054908000d000160030024400200300ca0074941c0b07665031840603580401c051141141c0741c1011205680410b000b164403c1801500072302c141d00c05c1200207443c00c03401050524010900780769 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 773495044 1250 773493794 773493797
    0xc031510051c1e031715040e0c0306090d03051b04031403040b0f090102010509121e070602030f01051f051801050d0617070509130803060612040b060a06050a 69
    0x1100c070309140911942590140300303418030480c100d05100004040301110034028900614048201c03800e843c018202e49189109010205d00d0503041100700b120040e08201610000c5501080380481c0200d03007410052852211768041c01801e04121944500042008085441d075030100220703030b00c0e00b00c410340c50740e00c0d03d01d52040c5603000c00003040890110f12109441c6480d1030b007520b280590326203140d6040e40c88561111700701580441c10b1881585c081c03082c030350700c0810030010f0403c20700081c2201115100c0d2401a0302122032049910483c0700d00c15040da2070150340000c046549040c40e0210719103401007445034611860040740d0441c0504103d84401414951588400e41000090310080c0e0a0700b1601d09503c0c1000303028812100054001c1c0039170001094008105030154a00b044001d0903c040c1d50450b6009410100500000c6440404084036240c1c0004401e0344985038900000c0c1d15100f440c04100081110307000780400e2100440705079020b080112040d031044d95a41200391b6240c0550442c400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 773496294 1250 773495044 773495071
    0x51c020a141312051923031e0a030b040504080408010c021f02072a030b01080c0307090207050c0a030b10060e060d05040809030d0e0418150f18050c0315 67
    0x2c04903e02e034504000c280325005441e01004007100088410140c81d1042e03414200c20a001104c01c1150200c6803d13403611003010358984412000141148900366168004214001941904d8a4130952100c403041c0b0f00103000b8041420a800c0803085a00113000d0001194a00000c0c2e01c49580000350611100640d14102201501e6a01d00c180c02504908400c2e6400f00422215120080d07920b828455880c9011001240302801c5040281e40d410050308145042c1c0d011070403000255600040d0390007110720809015980e1000c61500134101600101200c0e0003982a80c404010000c0f00c0c0d1520744181c41e41d0032a423112542e60002100c072802e080740c442d50001d500b040082e039000e410b40c10250344140503c0d0414035200c040801300c1d140c00c000e903031000c001500d10790340d031102840e09009101409406072409004103825803991032078084181c03500f02041e1f076203000c1d0402ca0313020f58000100d108200c50034194000b6482c1841a211080d021a0301e2184c06400030140b1001d8503000c04c0d0f80604034209040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 773497544 1250 773496294 773496299
    0x207020a0303120f1b0305091b2205040f1703070e060a09050907030b0109151e090306020406080601080a0501180e0f0714010f03091110051c020a1413 66
    0x589550804845a145080e203d1010108410581c02085641e04006000c5d00c100b1007584801401c841c00504001d07115041102c0c1c07080314611460f80a008021300304c8522800301410f0201a170001c882010940360f081c1004100030074080703040840d2400070301400b8200c450308128a0100c40c0c901c800c03120031000c5592040c0c000c101c0e0030140080c00100d0410f0a10b41c50281d1924000380d000d4800301d481c1c000003603d4000d0a0f4076541d00a041d040189213017000c0c206c0400740201c020304032066015002160007402e07443d44c07030714610444042c0c000710b4001c4000c650796911500010f09008088441e20702003455803000c241503110512030141240e941c2020144905941100c07080a40502084182c0c40d00c940b03410040c100009028100007401100985030b00503294100140146520003c28001d01d442d007c495004640d200d000d525007a1412182c40201061a020950b290f0282002420025400000b1211203441c0d65000313000102407070b1208514044118a210844d20540703405070300000d1450400c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 773498794 1250 773497544 773497547
    0xd02030c070614070b040606050420070609051603050d0813050a02010819050f0603190503161502070b0f0c04030309050906220b100309032001110408011b030207020a0303 75
    0x1c224142e0f101000041c0f5280c0305843d01141054259800c0c1ca2256840104211615103841121400200101c21464481740381d03c0300205409815000341c1402d4071402c190303081190030300c281c84072100c5184070510050b440e41442c0750b80356518104540814100404607504a8006514004840e0b02000400284e813140d07004492034403001d860b545d2035000c409141c0d011400785000301e0f13100d070700d003001c0030030030352401e281054506140c100c860940300000a50302e002290011046541c404c20b4042c0b4140c081d685c92600c21b01100da044118070085101180007030030010b81c000030b24010149501503040cac5480300b02e071180b442e01c558407004001c00c400000820103810014021580500700038100c1000b0381c05280d0700c40e140202c4450040300107070b46401010f40c620f410108800f61402c1c9140c10444240f0030f650140000385c0c410410100040c042031a025400000d421810605070744684032625503a50728001ca02070060f20006140b01e2030f400c4651440e4038480d2080d1094280c00500d0000d00d185507450 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 773500044 1250 773498794 773498807
    0xb0a0b061b2d060708060105030114010e13020904050f2806080f100f060b03270f0a0c08060c0909090a17071109040c06120605030607020f0d02030c0706 67
    0x424012901a05082000d02001e0450b042418a182140307565a0165050705a0428500421030400d110b104d2091081617640701e000e690540311000740102666641d40010f0300c0c0100d804190a5108803c02404001c00c8155009840741102c1a5818000c5d900c0d603641c0c484180c002100c04aa9520700c500105444d040c403800c0100c220f022004d80020340b03984401da21070030a05501034000b02580900e100c406200003078469030942803144541000300c181030141c0315009110285c20740c59100c0d00c904940f0210700741403685c1c404407550001181e1425200040194540e801907405a409070480c801c0058061800314481d40f141000364001441c0031504030800000d010082c0c80005284a64640035000401c0c819101c070b003007031040c6070b80d688441ca07a24002200d034603481140d0380240c4c0640103000002d285d400c020400d403041c905090313100343c00341000e9070010141070780100d615101f1041800030903500424000d400b9a200b90607510307140c10b889420ba13502d22035000115403c1c2e100010400c0694407441 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 773501294 1250 773500044 773500087
    0x80c0f1f20030108070f140307060509031e06060a1202100f0c05010606050d060603200f0d06140f0d0b0712090602120114040e1e150a090b0a0b06 64
    0x110380003469403002807100c046400980021009501c500024006011402440c00050800301c83e60150340340060f0100f500c0ea42240f1510302031107004140e8949680d000e00a003160300d800400600c8081100341600f655901e000ea50940c001c145920010031000660035803240318903000f4010310940c0401d42e1040314200386075005c501c100b280410380040025002c0c0194802081640c3e00e1070f4071900100f4048003142d4196000005240c03900141ca04a44410300f80703800c15941c0741c2c4800751102003112959980b8410b40c1000384800703150050224803020f0ba60b05074218050191142561403a0850078004d0180381c411029060104800000740383c00d20802002001c2c07098048003240314100c660361101070360007030728903070340c007403080e2801849401000f0000540c485012a0144101050302031502c3e207415203031031003a900751a0080c00424410040100c980d104000b07039940205071034615039400c0140017a05e0201c0340d801307a503000300f004044680501503d1942c01010245013613181c00070850200b8141 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 773502544 1250 773501294 773501321
    0x307020106080a06020705010507170a0b03010e12031f300804090c0e0301060f170319091406041511010b091501031b0801150c0609080c0f1f 62
    0x8075004141c0401c14845102d0346071003400c0140c2c42c2d013007602e00b5a01355100103000200300080030055500d1140f0203801c03184c01c0440b051000403410303034920100380500340c0c400201c4420300c210b0b80301c0315001e52502c0080d44200503d448454100c24410521035404040e40b05400c2c1c1c842049040c1c141050361040c5c500c041001019141070007108a5a520840d60425445820302c5680c030500b51f810305801140650108000314020001907042008080c0c034080c090145204058421107070390000c810400444480003064074a078805c400c200b0400030500e581e980a55451803601c1c0c0f4500d4a5400c00c8410343e0141c0d041c40a00a072000c10b0880102c40b05950801001c181b90b4039681308094070b4484041c414040c8140c0c0322007200c145102c2e400542940c03862540c91603424100340c08106060392022550b4196846414001c040c500140c8003182c0c03644900001401e924a400402c50411840300c004000d01401e1009940709080c58103441629461030680107910444030360101051002c055000b85031920300d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 773503794 1250 773502544 773502551
    0x30a0b150d0b0103031d0604060c0c030c0e180f070504050703091202240f06010f050c07091a03010c08041e050303150102010608161505120a150f030f0803070201 71
    0x105000550700020100c003038074a0440e1000520503d42d100c5c07195140b204600d0300c01706400c108036000c00c01c20b20403032140c80e00b00004000c06404200000411900440c0c110714a40c07500c64a031005180a41000d440c505803005e044443d01d02118404100c0001c0c02600d0300103011030701e00d00004d002c00f070000141a6400c055072200c0410002e1a107105a4401e00300503802081540450100c1038a090300791035500c2401c0300080308100034070712440c08080d4060820701c1e1603800d20601900594060103200007817082809070410100749102c4030340c0b200c0c0310b0030030744c415026288031040c0a05080b250442664000910084006070128a0b140d480c0042c2c06406206059000c1d800d4403024159002543c0c0300703d84050350580301003076690900601001d80700c4030011b051100c0c4210094110129103114225400c24140e04522200e4011400d0301d00800a51510000500d8900c4224000b02041e44020400e004c0700038001c10712205652103c401e8035400b24407442003ca0300d840356802c541000b04141c04564a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 773505044 1250 773503794 773503831
    0x607030c09031e050705040905030d020c030c0a0f0b07030908030a05060f04060e1801020a020601060c0201120603030804201309080919080f1506060a3e0a02030a0b 72
    0x101d92a403010300f40b60402c008a540040d43c6891030410107107610007031103541003071034100102e1404002c0300c103260030001e801642d6a07082d003019411401405154240c6014524200c41440611001100f200d88210b00c030000503612031609070202d40c0841409400744034240009202e40c1c44c198443c0350880002081700d031840b4070410000b8282d540b00e8011648101041703007408402141d0300b032540c683c035030b54000039818280c50041c000d56561051081e2010421025440c0040d03901801c1051052101201300f88195038803424043c1c15510280c40c01c07140d501d24000900402064a0102007181500400b101c212040b41c2060f8000380040c400182e071440c01c208040741050707862002142c5040d404001c103045180c07801c5500360038618048942c00390b40d0801621250401c18040c00664800801ca034515203034044000b0490311003400848110b140d203013290040c815240b000b2078580b064034039a0041400701c8001c00e901d43c0c80c1d01d000c4100075015406043c4003400260b02e031181a40c00000c102402c000510f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 773506294 1250 773505044 773505053
    0x21030806030f1204081009022206051302071e03080c0901021f0b1201050106120e0313090f0c140331080a08070f09030b090a0b191d0607030c0903 64
    0x2000c03600d000203000c00240070404408103000506c901881c0c10000c0040310b24039000306011a01c020084c040c2c0d5068841198805113490b031200c00602009040f10340c6010b289a64840254015003050383c1221603d0640e1841c09550b1101051055250340c034a040c81d00c0d1356070b592000b6040fa0408070f0540c054125048620400101c1c004000064440c0c0410300c40b14030410b00c00292038910444005904140042c001190000d081c00f2003420010740008400640d00c80071800c5008595400311511940040040c00d0724903500640c98260555004000780440404150b41c500c8010524400c481010300004a402d400220612581d04541c0e08074440e00c0c082c000d00c03888824a80004546030080030845148042c0d100192682c4a01c0328104602000e4441c0d102802180030740c4402400d08900d100001c0350030f142031041341220b81c0d10468030040703407c0c2104014076222131380440d50340d0f0900d802255a56541030244084800061901926040e110b4603022000f610300801c051080c0b10481c0800800607 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 773507544 1250 773506294 773506303
    0xa090e100510060e01140307140d0905010c03180c1a0c0616020d090506030a0b060d1514040b060a030509160801020703080606030601051204050705061308060121030806030f 76
    0x7145042504002e45051110203481001e004801c20b0401080103240154841c1550813617411072110f003028a1100e8451080d00100d211701d845085a2a003400031307134070070000c054100700c601143d0703514140442200407003001c6602c207000300c0107003180101030810015800800b969020800207480481d252200d0201420b145c4207007541d40c4060078102c1d80e42c200d409a130502c41e031051484d161500300001c03482e200008140e404013900b8a04466030300c960514440e5030310780840d00a00c06242045c007040c1c94249a540412155205a121901c0b81c54460710582c0303045d00c00c642002a00812480c1001c890074000c0340100801001c50100340301c0c600501d6924682150500010142040003590340c041c21b1400030231441000e41080e000c0d950a20a0005584e000015a680407200c81e04040050740c0d14140701d031402400c5d40c41550001700024860108145401408046d9110b00d01118203507680d440c3c98600400c56644100400000540344100181c494000143c128200034208d403d1103000c04c12190a1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 773508794 1250 773507544 773507551
    0xe0a03110d0c15030b1008010b09040f062304060f1a0d020412120e0604090c1205010803090109080a020a03020f01021e0303061509030a080306060d0e0303060406140a090e1005 77
    0x41c040f201c040701610725410b001c1c008640c2e01c02e4544e0080d515000b070000e006288103020790b5111000110351040c080e1610f84c0540f0b004412048180f00096886081820f0241244840c0c060641e007504020220f00740390203071104035040195100c40491814400d00c2e40051101144107401c5001c014080d90010540080c0000e8440c1c3e82d4420410b044034038000e50007050054010701400300c03840c1032141690f5110203031011070700d015a0100d800d0044460031030700d0000b030600c1e140a640c5424000b0401000010207015944c07402e8842031500c688542940e9074480c5411030095210b90681814401820041d480f0b1121071010700440d4060074003502c9d0f10402141c50700e5a40c503264404010020340d841c0002c1d40c101030302082178415103000c50306404243c640740d0341200941071210020200700c0d95200c45c02186c94038002c1c2d4104202c03e603d40310405480780d00c01c3c2d81d020f110b20b003080004108402d030032a45151102006151040207840c008802010700710407089110b50b40140112000502c0d007070b0003920f11 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 773510044 1250 773508794 773508809
    0x1207030207050f09100302010509011b0b06181006050f090d030809010c0c020d020d031b080c0c0a210206130306050405280b09101a040c0e0a03110d0c 66
    0x807480c14001448001400c3c002d61a00c140b0180c0b05209001302940d801e0b8050b02c3d028600503a4460145006a03003030741c142d0400c4c6851241894050702440180d41e180c81c06100110b9030261007403d201c40b40e04280340306885000310003100c140100840340c0914014041501e6001943e42844003a030005030042800d6002030340412100020030010510030322584002c0101410920504030094012424a446202000b405815400c24540500d80107185207196100c2500600f4280c4c1450314190640d9041900825010302c1014040511454080840c006a640d072048414100c3d114515a450640854000782e070003d01c10000840484000301e850006075000b0100860a4142072070714070314010071504241ba014401e0190402c00030307082d1030540600b40d0008541c3c0c01c10386a0404640c1021031001203041490718158a50743d0091422441c3c281d00401200d041000024036101502d07000c5a44560750741c040c0941c1414400101c0000c1c110031b002d00c2c050420200b102c602d5441405da070302c15412101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 773511294 1250 773510044 773510053
    0x905070206100503120d090c09020a0c050610060e010305040614090109020f0904021f271509030503041a0418060f09020715020c010b0307090b240a080912070302 71
    0x30441e100340b61050000c00040c1c00034441e41c400641100114003c1329048511241c40340380f4201480192650500500351004086544404180000c1d105009504c0100d61f140642d200003641c140241880c101101c00603100c6a00d02035131000110700410009108036030036540c074450640302043c034020680c880e103030140c00011610903500400a0880340d4159140c81181a0000c100050700e030a09240560600240380c865a0003913000180d0345213a440341c03100124000751f41c250b2802001c160f03282d07040f524400007030f40d80c0342c0c0d440c0412500002c80780806005940304210404c4581402092842d000e400c0c18151820320b5110f00454080241100d00a51b0581d25080140b00800104148100600c0070842c2140b0f0188950355894120b4500c21541d03010070f030301141504142c5001e400400c0c4044000741610300e082c1e126481d00b402016010542c7e0302800350340002420001e0060390702074080068400345800e003070418004542d440402030403007002d40141000c01c1b0050380303c00c015149161003600a007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 773512544 1250 773511294 773511301
    0x302030712080714090307120c0e0c04180c17090f06181903020a1106120406050103061a010503060f1c03210c051602040e07030503030a05070203130b090a0905070206 73
    0x40c41400c14000c4110401340400c07010000350340015001048451501061441104a007090140400c284d405104d0030500b0404000310207030664000c109845030100c8140a0060001050044411091800c0d010800001c000014520b89900f160b9110324280e0440e254004e43e0710b00c0c5810036030184c2c1c2c02002004503101c9800c0c2013400780003042142c640e14204108605803034600a54038199618094902081810300b1100c2d501e80c08111050820142d4421b402d6003070500d0201c004200911082d00c071039150001c0d01010f040c1c41c40c5000e8149505940e0642140c0795441046000100c150005d540703d110211800030310104c0099408007540640c45d8504242c14070322000c4241c0e404c083d4240e411510b0803500c40030b803030f070070505445043c201c0d4100d81d040c0703460500c0481c0051912015020061260000000801074000025441010a1201406107455090741603070740340103100c0010480c8044020500603000003038060107803140c00a200c2c100c001e689a400c00b0486000396001c200581048040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 773513794 1250 773512544 773512547
    0x3030e03010506121c050f2802010b0112020d0e060c0403050f0303070903030f090506042c09060121060f23040c0b0d0609020c030715020a0c080703020307120807 71
    0x18607034401420345400c40c1104c405110a0b0b11070002c048840039150054021205451040d02510030505902405641d200b0b980004ca10b4018010300352107030f408035203c8000c00024410300403080c140c001a1500310a1140d07125520700079410144508102c1030350341020204001c001c01400740103a120f00c086607a2281103050032030501e240c3c10750440c03a6900800070b008103590b1050f50740c0110b80d010b1414100307070050b00f44201c1d0a00f0030b40c4c1c840395200300042404507203002c8000c0d0030920a0700c04a911036843c00e40e0340c005104444100c500903c65080600100951800441410080900c4008600c03a44a07590b0300c2d4011207110f04815080150f84d41c803c0380c40f541200c2000c1031038000550003c040b80c9815518074407021040e00a0002d20703000460060030098840c3c100501600c10130740199150f20402d08015070382c0e00001d01c141c4003142c4500c0307440c81c88203c1d40b00301c43c101e104990700c03c0309000003034480b0113242d400554110114401000918003140b10132a4040480c42c55a40d18802402c00160 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 773515044 1250 773513794 773513801
    0x15040807050d0e06180d021306090b0904050709090305070c14010305010501050c0d1817010506040b0a1203050f04031407150f20030f1602190e070e060f0403030e0301 73
    0x2200e105002500f04103c00c584e8841d403e40d100103014110141441e00d0303c0c1c001c25060160054001e4001d1894214903182d072007250040b4042e50b9041404200110b81e140c10440b00080c180da01400b1a0401c2000340710b54552a040b44c0302940c06030a040d80307441c019580da80001d1605500501c89001003d07501802036905000c0e07140103180c246000d600340149688920f0703c0c0d510840008007405410004402403921011402009110000420a01403503201c4403501926040303c00c240304074580f09040889107850700c0440181c0380082005e5410482072340d41a902c0f503101c007602e03020080f03081c0000030005000c19200102100700d1805000454038000c030140341c3c0209407900500f40850f502c0c403c4d00491b8040d40c07403c694041400142400481c842c0c4203829482019400342000c60009099032010362144d030726400051095a01c400d200c1c52004d207000703002c0300d00d0141c054400e9404000c0f90040d403040900b1917448900034585807600880c860030100300e0703226500440120f601c124031070090389000e10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 773516294 1250 773515044 773515063
    0xa09061b0f02060601080c0d05090712061a0607080d02250f030e2d18010f031415010b0a091e0302150a0206010e070c050a0b06240f09031504080705 65
    0x80186d1541031000c009611400781d8034a1700100c9176903c2c0080c41c41001041504000c103418407003070340580c2d41803c24502800704c1039010184220700700b01124040c00c190040300c00f80c40c2c02c20812420701c0e41c5240320402039842181d42080d08079110028044182c401c461595a0510440748803102001c6403501800f030703040c000002482010f0381a000304080300e68800034230036410501403c41000c0d60703150029280740501c401c00340c190b07a0320300004076000004440c0c2c0d0003601d0041310b94054800010b00d13004d503604a140b001d844120726905c01005502050000b404020b242c60600e41e6441e43c40302a207082e1a19520703007401c5540c0c01000100150b08000c030301030b81d20f80403a1000c14503007103905c0d402a56590040c4200c594000500c070000301d00034404c100200c03e079a800402d945c240074503820251842a01543e0b5a0700c40d4104082100d4404c0c23041540316000d042000b072071030604049544211030394105101403500750051049401c41c00d96200d11151007580f0403141030780c07611170900b8124900071004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 773517544 1250 773516294 773516297
    0x1b0203190b150a050d020102191b0803160f0302030c100b040e0309032d03030705091c020f0f0402040f0e1b0403150b0d020d0510050a140a09061b0f02060601 69
    0x1500000d00710303101c0c2c01051013030300d20550782020b0110349440101d282c6560070721542a40c1491600b03c1003000354802c003001e0101d40e444012014035884110150300c0344101b120441042d80180001d20000c0c0d0040a0302c41010701a00540e41000044007100c1c0c248000d185095030349542d10440404685450f01c180e03007155154a006506004900c804699178201c00344400d2001c500703864456800c515482c201510055170102540d407a030030070342000b5099800402496108603610405400224251403404804640040140792040c3e0401f09020040900c030940981140d02040040340d44500b6822040060215003d01c8c03440d460720368921606010700c2c40020452110400003000419102c4c05560642005034400007221300b109400140700002514000703401146110740c285c00d02101040801101034858400d2007183c0d1a100804200c80c4024862240b0003400004540020010307405207501c2c030300c0340700e00280300d00403966031003070501c204e004900006041c2010007040913414401540c0046c000e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 773518794 1250 773517544 773517571
    0x60504050705070807150e0304060e0411030603150a020c0a030206150102060f0f1515070201110c013e030301150f0903033006080c03060c0a1b0203190b 67
    0x680e4601d59103114045016110040c0c1024100400100d6485400c02911f0b06044035591540c84401400c62007141d10f0061051707260400580010101030200c92040c10028080d209207041e0707881c441c200120190902c01c3c115400e01c02e00f002003908026a000d0540a81c000b0710142c0740441103035424410003490281150401402e121804041082c02c90304a41c52861300c081d0781e5202203005141c104020406680030402c2c200880e6907098020041035118000c2c0c4e00d1080a1400c0c421a0350750b9a03248080c107001a02c0d5100c040401c00b5000707020a54840181c0c120301100d41c801080f45044d0f402000050f0054000000401c620140d04180e100050214105403014540c106006400c1d840244400380502004a0710243e0303943d0006082d040d02d2400890070b650302400002c210004054038000c1101511a0703010f10480340ca0001626071051003540318032450003540001c221000d01200103180640c01000345054011390b0107109020038416606440e86c03d20150f82051486920301a000f030088624 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 773520044 1250 773518794 773518807
    0xc2a040608030702210c210c0103110904020702060412050622030e06220e090c030a0b15030709050106050901080a0b0112112208070515030406050a060b030406060504050705 76
    0x2101c0402607100b0780314510020080c03551213103841c140110084001c0e4400d01f400010400845100c1d0400f41070070302101100c41d402030820041d0111b8442400b41154813105214804151a0a03001840690f1020300518201307503035400706135038152601c40112201d030000303020002c041c034500040c040940302b0002150149482c641700a444603040f8030445024401c0020344100707041d080f54948120b1007030656480101a030f1080b030030103240400e603848012800750240300c40c200d25001403c800402d800c0880101103480d814107850903a044058a2601400385c4140051000018882e590003441039845142e82c400211000600c80d11000f800415114603019142041d66802000850b44080700a00003c040f002d071907540040e030080343c041c94090008141d50104002000e50308001b00d40010003241c1011792100100b1055550603040620458001d10000c0c02184c0340d41c02403a04075000d8040020700d240c48000002c1240d00890301952001e4031904108520b0402d0b21485910851a241290400c031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 773521294 1250 773520044 773520049
    0x207060507090f030204050a02120906010314030f0426030a0507030306090626031b100c02060c0717042606090106050f01110c03030a080a0605010903030c080c2a040608030702 77
    0x141c03d80000fa0141b6550800074101400c590b044543d01150b14500d03900d103180c85800303990703202d400f408101ea03203c4540b4040407000780b002056030307122442151081e052500700104000c200000003007124026007218900e80d84404140000d184c6038206642d2113607280c0c4541030107019034010f580914002440d1040c01c0090100011781880e148051148440c1c102000f04142460740c0034240c100e2030000c40040c00d030100520700050420305150b44031018418404600d109a840701811542140b0220040140c10001036100416480307204000145900706510340a9820207088103070203031070000c17440409040c080d110400c911a4401e6540000317211150030400452200b540845955050210240392184910380500003a94118000b50071642c5524141400034420301c801d962215210745444008266540b0a41c456429280c2585500d03000c900f80f0b90f1041119402003015080500520443d19880d1006000d201c5864803041e10324040c1448020411045030490760004801d0b5101308500401038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 773522544 1250 773521294 773521319
    0x803031b0f04061209020303030925030c06050a140a030903020c03010b011b060b060c0a0c06032d0b0415140d110405220515070503040b0a02090a03020301020409020706050709 77
    0x10385591410760100901e4a03221303c041d041068000f50315000c08800c0022180d00041d4600750002c03c100030038405169101441715202542c0000b40130580e002105110240c020401080210386a04c0d02d0003031140c0d80101280e1a4100580d07410002e84c8492a81040c10343c10803600103400c01c114020007581d04501e00280c40b48000b20ba406100c04548a840d5050010580c03003501014005000260340c3d1b10b0180e41c2640741c00318076208450600c01080d01042d0103100b0f03c41c00f0311020510703041580d1031304a681c2010052400c8440842d44d030b07481d0441d00c0b81e0ba41b218014200c8480c0301c0415610418100680300300701d6050745a01900035014a21300502145400e0b145190101041e00c1c00103141d15100781544440c8202c1c0b14120400c00050b11100800000041540c1c58803000924690300c1e0300c9505c4216030030300c01500c1c054500704100e80403030041000c3d64010b0420381e1000380640300d8156a6804a401ea03002907000c6144940e011070b8840922499002c1c440e400156440d01d40c0203d8180007201989 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 773523794 1250 773522544 773522549
    0x106050a020d08061201060305160b0316030f06050d1112031206060f0405031203041a06130b040b0d06060f06020a030518061c0e1e0304061b020603010803031b0f04 72
    0x100f1000b00040b030748503141d4501420704420288000d2040300d0b16418280e50311071001c404c140c0b4030309081100040c095040020750f8052140c1036000781c83c01910a4003203015003000f080041c813503030381c400d0002150f0356500005406244542194001d5255000c104040c07901c245111718620b4004000208410502c100700640c0402c04030f54036901c44030000940a2103001c0c3d6042640c051040b040c0846030600d0940103548140c0c410101034031005025801040a00015100280c2003031170a0000e20341e140342034100c5a088180a0800225011403030001340f03078000c9141040d19441c2e65030310144843d00c1032200103c09441140000c4c014031034507a400038224030940c580c1070075440140042070f000780c0e10141100d1103501c48501104880711010041c1700103298a00d03103600c0d6449040541040c42c000300d038210580d09401000b550802d0b00d081029100501c0c041d0b1580f5204107801103000040e544c01015501a1007100020b64891800c8510f051045110004c1404c1800d028072219071000161401c6605 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 773525044 1250 773523794 773523797
    0xc090302060d230103050c06070b07030f0f180203060a05100e040302120a110c030c011b0807051b1c0209010b1b150a150510140d02160b0106050a020d 66
    0x10780d411030b00280c2c0001e01e608071420604584500b956103404108010890580307000390290f45190561b0820400144601c403801000411580c0004120b80d0080d440003801220703450021580d40341b410b010400310341c12058407084411080c40302c002541410000c0d294081040c00d400c02103800e0020501070703400c01030b120304610703c0d00d04130008040502c2485141289070724501c41a464000804000c0d050170040b0b081010a4411200c0a5480d45400141320310000c2d8103841d001d00c0c221950425152042400c0000d460101d4100030350341c006030080210080308040a8040301c0000b0261003007089420041044454a04d20032110501590b182c5812038110b403a5001001e0755402002c1c611402080c182c5007455803030050814407030400000d48642c074484c828000042044500b0381d90035254040c018003074990004040c4900740e5000d406210081400c50360962003509201c801e8114030701b45e034042c100481020065003141c034100801135000502410031800d1070360400c41d4450f0001d40d1a03100542480 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 773526294 1250 773525044 773525047
    0x90c1d030c060304020d050d020a1a071d0301060b04030b0f0f070e011803080d0912110a06020a2a150506010e0103050c040801061e050a12031d0d20040c09030206 71
    0x80c00c5649001b095800c0c0c690000c00d071000f03241388003406500c0700c01401054036180d08081f400364100ca100103505100d18542d45680c030b9840340400c0c40c0300710b0000c450b010356099035aa440c0886e04100200203003000703500c00c240c0031203e1718045260301c00000f005446003405020b1078003840748180d084100c40c03405880030700c1d05c8110000104841303550800355500c060413540d000140d02e00c65081c0b0303400ac1005039000c2c0d43c13100503c901d85d40003159401440320103400d280e000b480b0a0b60001d05160000c1107401e10915000351525880700351a00d40c0e445280c010300002001342080c2040081c0e0036045800d08a4110040140d072611400207040042049882c078101990740001071410340c01082138401601c0b1300d1000b00312181e1a0704500004503d2059012940b1400000014180c90030391100d5007074451018180b140e06406503000e8030440d8400105000181c4070360b182215039201c07680c410003000e00031241c203848190f030850380300c0d50701340008070f4940181d00300885801c13980d821000e0f03030088940c1600c040e0b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 773527544 1250 773526294 773526301
    0xc2403050c0d0e0f011a03070509090309030d120513080409150b0a050909010503070b0417071e03020910080d0c050115090605010f050703023301090c1d030c0603 71
    0x16800c2c820101e060b040300745002c61610450b54001400707005000f9140007000705501000088903140c5c0050b46455055005039414002d600740307500901c4e00004010700320390800880100190901d8542d550350400502e1148014204040300d00500b500007858958420b078403103043e00c130b8075240d100354042d41e100301d03846807070800000718007102d000003c061300e100050300c891050381d00401a5102c0c40d0030311710409007000042583d03c1c0c0031809201701d5150211140c501443c09414981d1a043c844190700c00c0c3c0030328100002c414401200024101e07040d4012040031a0440c4108400004042c1a00000980240b4144409c41000502c400441000d0401c05025441c915000d030141c02d0303045400c01c0502482000103501e10081e0010420744100741c0392480e4200c55802c0445641c041c0720000340051740300c8070b43c0b0200380303803050001429402060180e015501c40590481e24103502a400319584566580e10340c60003070703480002180c0b04a020340c0150030b854503801c00280d42c4c40701c00024503c540b4000011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 773528794 1250 773527544 773527561
    0x60b0d0b011701140a05030105130f03140c06070906020a02010917070b2d0c0d08070908010c020f071d150f090403110105061c030f1101180c240305 65
    0x1112010b6440076400d5030660b12680015071000d60141114043c0c1c0f14250007255520741801030700e11401c030340460200c50801c3c544521802c030306841f40503801d1202c4400c04044261004006001c5920900003d05850030300c2d202c003c02c040400d40c404003c5400015980c0d006030381c4402c46504440003030701980c030031908080301c050810040340d00c0701c05208000101c8060025815030000c0806294440c00744061003a0050300c003a81c422511039810941020b030071404441e002d00c0c405604603406250403c00f043c1c89296840c03c4030710050081000d030f13100c0004802011420070a00e000781c00c0b90100b4914000c100d9030000011440078142e49025a40d1865200160f04c0e030708e49084ca5030350024113205148c200ba040281040b4141803000c4d1465091034001761560410306030380b060417184e0001040f1419a0358074211a0103030200e00380700130449007414610104509004225400701c926109000c4d44030781c1d10f0803210046980d4005005400c40382040c1c42140100740348001480414103020510359500c1c1c00303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 773530044 1250 773528794 773528807
    0x3080a0b060915041e030b0f0c04230d0501051f120305030a0f140118140103030c02030f1e06060a030309050d081c1d0601050f062d03090d03060b0d0b01 67
    0xc0240d0101100e444c517100e032070071941264200da00813110620561259184140518002c4603840202901004100b1480781c5080080c1201d0000b41c80590f0040601000a142500341e03220039601030391180d05000180c411010740105011001c03045038051031810b20440d0300d54032038580180c10b21031301000041001c1d407035800c03010380490a54020041504030000209811b1420301440d040860340300d10790811070750a80b1510742c07140c103002242c0005a2969900315030407030320300307600326090700400c045604210030400c00c0c51400c611004c100f130f800c0410b40c04e14500c1c15034002d003a14450082c2413030030000b00350041d0407482503540503075000d044c0d02030b142081c0d50309104031a400d175110043c0d201d103244030550342d0f8000b81803d1f03590340c4003802c0c0c1d0101c66641591040203000f03069105c4e004a0030034160b840c01d074005241041031b00c06203c0d140c0f01100802c0215400001c0718102080000041224600f8103005000c80b0301100c1c1410018103091a18681d59400341c071450620f2280d890101104981c081c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 773531294 1250 773530044 773530049
    0xa0207030507090905060702010c050403020f03010b0d0c1d041101110319050d06080c0a060f0c0606230105070b0402010c140f100e0102042304110d0903080a0b06091504 74
    0x1040b650b040d56243c08810050010700020340d140c0c010380c4003103100d1034130601880c0c0e10391429a4485041c14216001c1001a1464252440e8150b60f6038003045220348600c02c14141d20760083d030843c181d69103403510140d084c2020000341d0310b940c0100e0b02080005254401307100d150315803e1030311078108941201150300c0c40c406d030384070880c103520486035010ba000d42c060002e1107180b0442c242400f109944809140c0d03245414145258015848070b03007031048901c12820902d108150303242c4a203031503603a6240d2070201c0d80d0b1900108050450080201422640034800c004482401c3c48e2891601da49500c4203100b070040035100038108086000204240300302140d011108480c42020b80e040c0c040c00e140d441e0340d43da00186540c00398a0520a44441103581071080e2812100b2074200c1c04203039180b2500042841c0501f55896500642d2101014a2000c404020b0458902d00c010005140751403410041c0008100511542c4150f04140b46100310b501d0300020b81c0c0341c520054403060360150020310800e000d4015038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 773532544 1250 773531294 773531303
    0xa0201022106030705010801030f060507180b0316090f0b09150c060906010801021312080c120a0e090c0904090204140c130b190f020304030b010f090f1e020a020703 72
    0x503250608010118222402808100c1c04c5940b003a54500040d51203560034840500b54007a28a03480c0c0100b030040d0402907011040d8500744032405611000500024019004415640030200801c03c80500c04140d0714030342080c134241003000074038003110b20503203011601888105041c0841c49001c50b8070341c820f9050182580c17516032902c605602803460b035200c5d000c0340d40303000f1032203230000002d802e00041c400c03a1280003402c0d581e2509581010b0001c0044800705e80200c1f08414108a800071410041c403413205500082c0a90316900d03006000018100f20515030001d10400c8000c1c14004001d200c0000c40d81140b000f910045040c000d40c0c000200244000300c48100407020302420003000c207050a008001324500c01c2200880070762205641392180c0189414240904050314a40d541c55000e000f4401c400d05052048a180945035690786061000a034844007800803405400e20413505c04e400b81061142c1178101c100070f61410401868241e407200214121529400112490024401d02c4000c001e035412 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 773533794 1250 773532544 773532577
    0x70f080c0a3f0518030a0b07080708100f09180b09010623090f0606040906091d01050f0f130503030405060405060f0114060f19021b0402070201140a020102 68
    0x403061402d081005192855034180a1941808242a02c05044500c0414981e51030742030600680180344440441d80302e25616100d0241e6110000703080a0001d481400d855582c00018104450301604084000e00030300000a049407042c0480382c9030040f0300c0c0c105c0e007001c0c40100741d51101d0900b000e04d11910820280100500c0c408201020105400c039004a9401c1c1038000490005100c400c006a90f1218030300764008403a1002c11080d40c0b04048503600024010491171900783d03a80a800111107803640004609603c40c40c041a01801d28000300c2000d109107030080c0300c01e01d841465400301c140000c107640480c00701070010809074a000790210b404564414112079a80c24513080c0341d0364801c801c2f03038121070f1449410300090300454001c01c120b0485006a194034123441c80e22081000a0308000200c0c510044148001c1ca10800304001446a50945030080e02200522560400390850a48419801140108071487c0140d900041a460b10b5043e6400c01e520f50512881c2280a8840c842280d10100300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 773535044 1250 773533794 773533823
    0x1081312030b18061309170d0213030309050112022104080c07030501060e010b1c050403230702010216050d0f080904150e0a140c030411100302070512070f080c0a 71
    0x3d400c615140a080101d8070313095100341d0a204032041e103510700d03002001c1244c2030455030807000a080c050700070b40e01800b130098107050368001c030807203050059403003500012442c8200300881d5030060b0b60320722242480310095181490444181040d02e14030641d00d419041e010700058107000c40003040c1e9002001427015902d8250b81c0f8202580a0000350007000c01c1012a04c1c000140483d901c0101d880c0700f0600e4803542c1d824407100c288100100b0004209509000d2000e086030929146000b00c000f01c0c6841c03981141e11000783e030000900c0d0a0f8206400c0070041000001803080d40d0703400c0240258182c1c07007130f80c0310f040b90707046e00c1c000d10340380a12484640c00c2424500c1908200c0914541d03803083c0d8428500640d050741d9078001c01c005980755402d440c546841c1000200e180c1d20804401181e02901490341070041c0e03010800460540d11091003520002540800d485042003814040030030042401c3c104203040c900607460320400402c090b04014054400000c4002d01d030241406000790395070b0440b0358103c8004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 773536294 1250 773535044 773535079
    0x50f04020f01270f0503011422061e0b042c01200910080c0901030b180702010f060603060b0904152111030a0b01090b18190b01081312030b 61
    0x11413130003181000e41201a0202d542d04052241c6d10070700c0384106800710540c0714440881040344a42020200020003013080c50301064003401001a40d805c089101070f200160039180c0002c0b910358140f902d115034205543d42c000340c22034a85503090704103040740c00444810f1710b503c214010003190396103c0807800f0310151a1700e0205108064400c010741924400049040304004071043c0d0380841c2c5c10103c10105000700501540b103907000018032040640b124403c1e10340d141c00300301411011140c0c10010b030344428030144288014003802000304124101030110030f0812408040b20b01400350302e00d0040340d032015615070002c464100300e0020720100c00b10059484000f003000c100d0040c80d00060341c2403001030501110500340000c00e02900c640009142e221642401ca0302e0010300f036842003444c0c0c401c12024520f09210b050b00b5111340030721103a6159000444064003900c003920b00c540344c064188030b03040e010000440640d03404248500d5000c44400280742d607884003038000344803183e030f555000035641042c0e00095 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 773537544 1250 773536294 773536367
    0x2d030309031911150f0d0207060e010603111203070215040e0106020303011e0b0a110106050303221202130902041407081e060d0b0604181a0901050f04020f01 69
    0x80d00400da4001c0741041e01040c03042a064840d15943c213003104015042c0300345092406809111a50a000343c50000380c4e49580c42542c103903800258007070755104410410001c082d9800b10001360300b903894000c200307400d03d001500c81c05140c1c4068000e11182a860200b2918541160058003446030810095612058001d40d0703a082406203000342d24610320400840301d0b491483c1c000704c0c0c030380c0d51403549041c0c1c00143c1112013400045071420650340b00c05c1c000c0f8241d6800c0c0094004c0341d81c0008602103692203c090340c8005c0001d584400317800400c1440c460050384032000596006440c12101240100304c9102040040c0524010b6110f1505400140400c40b81d104d22603a00030011162401d0103007100200714070014030283c4442307900145103854a00003031159004030358003401c018000034101508044d02c001203161410101d5840502030005e500803a00c05181c142c0010281008204500c3c10000512901d403014001a01c20804145050082d80c4038040030701e0f04030700c1051203d4090480304c1801825 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 773538794 1250 773537544 773537593
    0x60207030903060b0a0f12170d150e07081b2b0c211104090501090c080f0615030408070f0302030d0b060304080316020304030c03050c040b2d03030903 66
    0x3e541042900b0369103240045039202a01c480314804440d461030040002c904520490048502d00070165a045040c81400d004d401a08152600491520241c1405c520200800c0e00103601c0703801d1084c1840102c030790003201c0032342c48502c09005e07101c00f012422642c02c0900408000320946444401e501c2c20300c0005400900b01038040312814009040000802e5686031810010251305454070503401020314803d802036084851131000b0645001d440707208810541d00c091300140f400540b03412280c80001c1c1e001c4103065115007000f41c048124108003001070484002075843d01990000130002c41c05001011045071034065100002c414440e2042c034019480707230040da000450091810764584030f00d041810880c1e104951068042d0700e10b41e500101c490700030380200d100e01c085100030f002c08030004150150351005180039400810412624038100419100d1181d91240640c15101d03d2025580c40d88030012000100c007070903540c0003007440d80424a94002c501c1c6182c1d07d84294035200d060303400000109000b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 773540044 1250 773538794 773538803
    0xd0c08010806250908070803030105240406050a030f0507110d110c100c0804080102030124020c0d0521070501050c090d0b130b0c03060901060207081207020409060207030903 76
    0x641e03a201105500c0b80000c603620714040035004400360032a84203014410015820381000ca0f00c8503100e401e1207107004040c0d0440b4882d030740000300610440ca03001c0032944020401c4191140048548024650f10340158481d00050110200d03010b41094000e4004003542510850f081000d850a281c2c02040c4008401c06400c050280700100035525100d5078a442c9200d8440c0020403540741d50105016000410400034010000251000e0001500300c000410081c00702900140e203c5d41044020050a8201c000c00d58159008406481143d600403c1204008030100c0e5200d8058481c2d043c4a0b0600c12040503d080045111449450600c122809002041c2c0100001c001ca5990241c06070309074400c0c8180f107507102078980040000100480909a8441e000d2000c01000c080c59903030701d004601d030079207250182950100c1001342c0f609100301014010041840100005441c102c01d898072214074000c1042000b0300040c0a105548641d0003101c24a9408082103682c0c00302420018211100d5000480d0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 773541294 1250 773540044 773540057
    0x11a0405010c03120f020a020a1407080309120a0b04150b030c090105041e0c0f08010506040f170a05060c1b0703150b01030e0a032303043201052a030108150613020d0c 73
    0x2b000600001d03090007a110420000c600d80700c0700000700003900c00ba03103080c0c81e481e2060701070550002d8610030155016620070038a072001031032194464020b80d011581084d019a0001c0581c400b9070303030781c1c2e90139504680d020340700010784445d00d148000c41c680d20b001c00030100b0342c1480c19510819a000d208108803190075525400203907201e904210043c0300c1c41c41005262416000c0030301c0140304075501100007a007140211801840c165072000e003441402c0341c118940300300c040b61418006030145104160907441c28041c040c0742d0b08683d200c01c62a400ca2000c81c01741039640d030b00507403142d001e40e00114050003440c049030140303411131800401c1e5000d07030f002c0704025445005841011103c0241a41d0080d80e01c03580c042685207117818003605004203035051200c1007982c1c0c001403114180a04c0765600500b2005450340e00084210b04a48400942200c050320030441040104200c20000c103c04d0b0f904c2c502014041801d4503250001001c0c09211076040c051540b0014074a03c401d282c9900c40f0315044030984402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 773542544 1250 773541294 773541323
    0x10060602010b0d0210051c1b03020c0d030216020303120717040822031e1103030c0a02101e0201020316050a021c05130905011a0405010c03120f020a020a 67
    0x40742600d0092581c1c41c0c000c403400c3c84400061600b12000080e402103171400504164028066580a003018905140c00658601558038001414801072070b005006040540c0f0304851036100c50b5560741041010010182d0104012401031001c0c0d000f50030701034004044070b860344034000d0040c9904c4000d03a00362012484d9015407507501200d981213140b0580e0000e820321700780076007400c580400b47c8002c1c001801141b0503e09c0800003d0062074420310f44a1005221030403d0014948040aa00d0910745644030b54070512480d04000b40001d01220501c3c1e064480d800059030340031043e204829600050000b1610202c50504542d50545c069031213400d6072600480c12410400040d00d01d03100741c0b016040103800040072100c0f641020302d95082c820300c0510f0000c0c5000d82c0c0d420800626a45038004042c41d903140d000400c816409203921a0510071415540381c80c25203000006052200421802800e01c452940142d008544a90000c24140e0030b108081d9074076000e00304003d4564010740c40841c2c01d0307081c0030100b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 773543794 1250 773542544 773542547
    0x12010f0b0a0e04031715100f0314010506071b0902190207121a3606010504020f03040b1308130501180608060409110301020c01090b090102030601080414010e010e100606 74
    0x9401182c154031521170b1261070070150030310460010111600c10180358241c031800d40b218200c0241d84401561140e80c05d80c0e5000004040c1e65107000d41000c0e103424100103100c1c1e552150f0446002e941c0c803e20142c41368002c00c8a500c903c00b207603440002c0240c80820b19401c5401c61000790851070759030f5802c2d41c25039a100ca0039100f10383c5101d10043c0070b40038800042c2c0d285c8581071080541003042c8040142003128589940e01c00a100c01c0c001d900303801e58254012220032001c000c1103002d007404880542c2404a01c1ca43e201031404014005015640841c002c43e84c0460461002e0420315008442e40d41e44459201c0c0456039400c0c203101340f50000d40031079401284003150101d0a8141c582c06e40c0c0d07924041d244d02e0b04100c00707030000140a4806d0034001010344447d5400f40f004200b650040000440c5414035130501015001000301000c8199004100300b02180c0c0e800384003554025400100050a1580006064011703c0c0c9644503088961030003840e83c1c5000340001b25541d80c03c0451100384429520354a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 773545044 1250 773543794 773543819
    0xe0d05010e01110408070b040e06010309060e0a03110d11030909040f0f051b01110c090907050a15080601111f09080a0c020f010f09211e1112190212010f0b0a 69
    0x403049c1d0092442c001c0346e840c0d0310a801000c0303003c4c0100d00114900305484196406c024907100b0890126110360740021200368184113010100341242800c0d80d1040c01d9505003a16442030100c054400c5070744200180c00c01c01280403c2d013542d80c0000141440d01210701e030640e902c040c130001080307416a800c407120a103988030308419614043c42c40c01070440b0068440178002408006001141a405009004280d6446000a03040140503e8115255150400030041c20000b00504110304001c0e1407041030760700c00e0000407440800c040032429171305803824150101008050100000b00045400070705020403981c0404501c0e100f40c0221035207118207050b4401582c403004801315000120b4080d03d2300700003400006403092284600ea11000100c0445076450004444e40040c070004000034a0100780706201041c5100b800f10401a80d105595501807000243e0340d4004001800901c48100d80d4002103445941581003c2c051180084c450303155401c0181c2d0141c81540b009500582050100140a04c2d000e031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 773546294 1250 773545044 773545049
    0x1e0915110d0c03080a29040621020414061809030f041d010504180b090a0503070311300d0605040f090312020412080a110703030f03050f070e0d05010e01110408070b04 73
    0x121040038180140c6800f406c2c850094031460307101d9502c400c0022140c2402807103001c0500c501e14001d64501d41ca10421044070360b401c0c80406408066010841c140e1039819540d007000000452500c801d42c1c846034002c1c40d51040500c131443d0180e012400007601c21420420303100c203034014409a480f6a880b4410b1004440096040c201c0c1d450491030154045103a406800d50049840c10a54100c601d8584170f0500d15030200804400080c1d009000a40d0204241b00d8480000000700c2d900804656502d801c00601c064202c00894003080003410810304034190344500000c02d4047d00a0000b0381050650f203004000c480d20690200f40040e142e0600705986100319003d441070002c0b2481d100302c4071b46602d403d90704500960320900c611040080e0140c0700810101c0b000b140320f6076444d00100040c4100605460f009404012701c07018610500540a40125402c1c40b52001070b10300480303600c01400c065003d401750308000c01940d440c0a005060b030a40b124010400d5a4090007210b0307440b607039403000d40401d20852 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 773547544 1250 773546294 773546321
    0xe0f0f040816030c08040323030f0423181b070c15051b0105060111030304050607080c0409110a030e070605181206090d1e0915110d0c03080a 62
    0x40144082c030b0303001c1c0701e05000c03514000d2070080001e6109990309041035000f0303041514050b0000304080901c440b2030411144400c29180071b54180843d5080d4100140502d000310042c545455494020035074026001410064000708011003100031a1418800c2c010156104040e0303100307200c0025100181c0c9000c4a803034036482032210741540d20b403107990801c0548000201d03041003c20009100320031174145425030380c0361a4000020743c60400100261080d0b101800800b5203400920812011440c0401c1c4640e1183c0710b03003012880e55840480c018110312450300f08042541c07a2030f90b49046035003280041c05854990f82c8040141c90101040c4c5940c910f418820b03031000031800c222000248007880d500c41981400078001d0100c0e20420002e950800c5811903074503680354080f2240c4014250310040740901d50104020310120800200001011203509001d969100c40a40750a40100c81c400e024030351030051601c0c10381c4c0c0340581c001d80003000702c0c01050301070340041d46440201e0038000043c8900485083c58 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 773548794 1250 773547544 773547547
    0x122c01021612060c020a210813021c06020d0603060b090c03041509020303070f0807060f05070f03020304110a0e0106020f1c0e031002030a0b03060a0c050a05070c050a0e0f0f0408 78
    0x11503403840003401d13403030301200304501811715800e0000340c810f10403540580e100442e500001901c400700074014500103021003c1b1644500d980070158540a048a8a0302035001c0d198082c0512410403902a01c80c00904040081c9896000010701516074441d03008004115604041603ca1011b07a120502055402a15003001103440f000130039810b9029480152007e001c3e0b90a00a075074039000c00c008461a01500c040d81c001a160081140c180700d440d006a105c01010406400c3c10300e4001c00004a601c120300034590b00002040038071003540c080c03078440040141024020340e1a0510928104001c0c4207910144c801c203803e864480700007050403841c3c100d0345100c0880c207800c03a41085404000210301d403500750003200c0404100440c0b030b000a510070881c404000caa922800c0007407625011001f448950b1480c07030007030f1014849601c40b003100c11506092404544828950400c0010707136601e40d00c42c2d98081d2210000080403500031003420301c03c403050508070f0b0083d650441142075245040b503004015040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 773550044 1250 773548794 773548829
    0xb13060b040e3003010f061e0f1d04150e070806100e040e0106082410090506061204032a0b07140c010216021219122c010216 55
    0x90341d05600c01c2004604031032280c1000c2c0e1003c1000d1a600a80007590054913608050000fa07810201d019807106110003600c03442590403000914180410300c403001009461184d000000300c524900c03034542d00e4021302c20802500301c00141e1500c160303148500001c200345040042c844500030b40709a0722992000d020705901c9031250f141199070203100c24480d035001c2c0d510f490410b40300f4800d1041ea409030072401e000b0000e4403200403028100c0d0103491a4051000c1c0044200200d20300300e00c880404440102c00f000ca0591681000140302c0c0c0511000b007034880c43d00c54208418198040014403591001e08640000c03a145480842c4031180c01010140c00f580c41c681c08260414800c241c9813006c05040c00a0074146561020814260303402005848444c2604440c56400d51404440e42d16503404604002c2c08528100740406048250120001d032444d5a00d6100d0001a40285003007100441b04843d18914803142510303040b8800c3c02858094014400c0941184126001960304c1e070035150300c944208017410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 773551294 1250 773550044 773550073
    0x90c01091d06130c030b13021806070203010204050607061e0204030317100f060c05010c02161a07020a0608040c0b0405180a061511060a0203160309030c0b13060b040e 73
    0x54080c04898010f16910038404196841c3e10401c01c00c14456540814448850401c000360700381c8020072400c082e4410425041c5481488645445140090b0342c0c6c0ca8031001c55000007170081c0900d0b40503681185e400100c5a0801c030716a40a0000d1401c0c081c10340120f10591a0003404138040d5000040115135000740100b10292035048540c0d1045810302900c852540302d182151986150340e02c0000407403c24218101001004e00540340281000d100814411903c408440045005e61065100820b888200c411040480c41d00f200e1100d0f801500d2801c01d0340d40c0c0d5000803c0003030100d81c05e03248081030400104240e40035204550444000510764080704e10647c095041c0d80c407000c1c00c04138805079100000941c03030b085070940302d60381c240c4c0d6111350707000e03032002403da40c200f40f0002c24152a444c4104100b00c0c0892200387c03020301c5500f881c5800036403c2c1603460141d90407200c0800203440d1004000802c00c0540428112405081c460f4200b401031a030b001040c0302c11b030394182c0000e840c02d07048101c3d580c0001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 773552544 1250 773551294 773551349
    0x5010203161218021908030d0b03061501140d11120601030f050f070311040302120f160e0a0e1509010218041118060706050a0603020103050705090112050714040e090c0109 75
    0xc0c10480652243c030381d81e481d05803541c8c0c001c0120b43c200540740c0702240c20700d290900045900c0b104440c8102580d074400000201444280e8010201d8864049038800401510358007800054480f00d0403203507101d28219280d01c00c04000c0703c1240c00641018030100b0420031500800d405100c69803882c07a1035445000c4240c02400301d041241ea000c0344140000800f580c0c1d600200b082d4000801e02502541269070925400c20340000700c420441c4400c00300401c040143c0e0035485502081400002640382840f03440c950410080014082502c00c02c1014000142d0065004060400b910241407402c20100411311003620404050325031000028401d103886040ba001069501244c0102980d140030304603030fa4601140c9050341c0441103159104010300855806204140c0c101116090072820140007500082c440787c0c080d0351001d000340c1c5800101d406103000304c41902c0d4600016401da0b0b21941c0b42c1200010b200021100410544148903a103032a41d40920311080c1594109800441004070700103005000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 773553794 1250 773552544 773552569
    0x606210a02090301050c070c080307050c060d020d05190507020c03060105100302070b0f091603050604110406080a03180f120b04030903140c31180501020316121802 72
    0x2440c0d0200000c450b595428400c403403250801c120310f141c0b91111810b01e8881810701b03400c80740c4a40e20820468004c0703880025094600d16080b0b9129949185030340e4000080e0264058002c181420003040c0708180d01082c0310300303517410b841103010403a60b0b950301703400caa4420b4682c0c105500768000800601950620310940101044203090142c0b40581c1507440c0300742e240c8215030080c10004030758280449650148110124071070101c12110f2205d0568407120b40301d680140c00102581780d50b142d00700894940b42c0008008000d28020f94100c003a1354203015000c200010300c50441c5030380c107401c08114101031542000c240c500d441080d00443c030165aa10054900c080c0c0290240012180000005002070012500c000001c40141040c02c07028130901c50444581a40b0081801030366008a200c1801c20550203905c45128001050b42488407205a402c1a200c440140c01ca5000204108212207801404410f80885a54142440c0e40c403a05100882d0410210300e40c00502a150758030152400c84c1030b0a01f03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 773555044 1250 773553794 773553811
    0xe18090a0503040f030516140d0c08100b030105010f030f0f0501020d0906020405100207141e060f03070f09030206040e18070e070e090402060a03050403021002071a060621 75
    0xc208095848191454101c1e40c080d0641c2803100310b05004100041c005524031900c05010b241180e41000303601c1014030080d41103a8000d45034520a5802e00034200c00b4040202003440039074001100e00f095403c09040703c0e82040c1d000350b0a11000142c040d4808a59004880e08040304903064065503460b110345520b481e0003503074159000e0040f14030361800342c8180099140705000041e034540c0f41105002c440d244e2042e4203025504216000c011001194070440070080c0704403050800381812030410810b03034082d00945600128041910121250803c004600408158540d42030f46c5001d40000c41d1071054500000b504144280410459043e54030740c8140c10030031070b01c441080b4010041030103160419543c01004d195018a040c07000780c941040b45a401142c00342d030001000c2c5842e0700401e020b03200300703000c000c00c050340c80d00024180b5209004002100d00a00301c2550350300a941028820740729030030300c0d608c1c80c01c4680010503401d00e0680116001001c445d2010700c0300e00784a81c5110700d4402c00030903994 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 773556294 1250 773555044 773555053
    0x60306010c0605010b120c0c071a0c15090f0a03021b28031e020105180609120105091005040b040605060105130b0d0509070612090602070b09010c08070e1809 69
    0x1001482c40c0c02002d0103080100b03a0701d606c8407115181c010b90990080c103031300702c0d8000411003034103841d8011800e0000e68000c8400564403204d01c1070001d01c00d214045429006c0d002e00c89140009000708190103009005d41d03000c0b108202c01d0801e41c26190600c0400050243c0d00049070402081400d140c2105040002000d84580095181e004003060700300c2503210081c500b8480090040000d0381054120744942da45402c06011020350000e045403080101010004d40c1840010196aa0305000c07500850405040e40482201d00206207020744415180c0d4510790007220300d92000300b00184200307481f42c1c0e0004000d00a54841e45c594900400b0007900460402400b001442c08403d001c0100400030301d0020840f55440200d08200001c40b81e0250040c1e140b500301210170031800c2d501007400c4900d0600010001150720040c036152009200790320004082071000401c01c41c9640c0194005070035000c2c035446641e4140d0b070302c80d401c40715011100d640c42c0d4403500c80d070040307030351000a016550f07404075104040701c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 773557544 1250 773556294 773556317
    0xc0c12030a1803060603031227060e030f0c2109130b01021e0703140f03040e13060c09030501050708011a1e0403050a41031306020105071106041106030601 68
    0x9070141c0d04941c000b64045034110003804800c0c1c230148925061003450040c440e985031a00d19980c0129040004060810780e212004015510010710803524214800020031b0b40c0d44502d004480c2c1c9540d4600c14548100c22406c424248640410007214a0714200625041c4da509000003200000d201c0c5001c40d50452180200394031410324040c4c610521039032800e0083c0a950300d18034022035600248010b041080c1c00450080301181800802e5a0544464203040c84075aa00c1075480701c0d4a040c1c000c4090400750a148154010300e03040428041541d014500a201e580d4130400192848082031003140184281c42801e010740280f210007906003a04203910b60880c21030443e00300311481c3c00603001581c954011840c403204114090822400e064985140307060615405070503944140c0d6525001600d1040d0010016034541040c41140d1910704401d86140180d030300da5070001e0081504441200c04260315403c0818030440001e401446030341e0004c4c28034030720481003043c080d5942024007107505000000944 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 773558794 1250 773557544 773557553
    0xc03090d11130b030f0102040503060402090702120703080114040e0705090703110d060801141005040c1e0807020d0c05120d060506030405011a01030227060f0c01020c0c12030a1803 79
    0x3480903100100c00d0108241c55103c081504001c9248680c5100d684100800c000945001c6101940290125012221503444090590420345084000814460b0003d801400c00d5040220030303050300c0150501c1402851800c1c148012628440c0302c046d03c03584190400c0110b0b140c020100b0b03038880114900403403610343d0003c8180c225040380c402310b910715071100c400380304140d800d104403080005403448804917401c2c80c0e03c41c60031190440c0903140c00766481c2d0b612100058000c09803001d04003c04c0c04010b504594404e802455020240c8880d0014062710003008019403180504002d03441d04030300030300001451501c482e405980b000d64040c2c03c00d510780b0340004860395800007942c8a14000c40000c00c04021314140c08852a80b1404924180b62061000e02140e8860001c0004444804110036110b040c504000402a002d07107078803101c4d110030014070445008010340142c02d800080c08110f0390001840c0d01040302c0f0005011040c0c03040d074400d02401d4800761060742ea041c5035034015288280c6450701c0786c0740e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 773560044 1250 773558794 773558809
    0x191b0f1403070f06050f070c080702030c101805100909050a1808040801060608130602093c03070b1c0e0703061a100503070c151d0f030c03090d11 64
    0x1c0da0083e56402e088024031043e40509688165121060100e6103070402e409481010b01c408083c055610200d425411514108041c0c40003210060124030b0000010300d00414141c02c042c1081420040b583c1e0018507030411420300801001d0b9a140d410105040010820003404000c0c000a400c5850388000801240e03488030b1481042e002d49400399480303040055445c252416644100701f0419980d04001181c100c80c0d14403241240e0081303000d40d49030002400541e00b81c02c441585005400c0016a04050000264002e14160788600695808034103442c01c160320b4103114811401090300410481c0800b6040715000300b42d0b0104d403000020075000345194070789031220a400440e81555500225076004000d0852081e41c078104807003224501c490a40028000d000c040c08032000e100807480010108442106400d240403241da001708a400300c070002003007540801e0610b001003802890076000c0490000f104660030b000c2e8210045191500080900040307030304c082c4051302c20300c000c0c00d801811030b41d0740321 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 773561151 1107 773560044 773560057
    0xe04030c20030709110a08090f0303090606011407050c01030b040e06090604111912171308012301140301090b010902191b0f1403 57
    0x116054400d0046548000c00718041000c00300e5000328041e5640e580c02004504440741d00740d4400300f09003120a07424920104031001c208022a081c0102640c0340c100a0740401c682140c6111160141190410703100450290041e405010486d0fa00603484003200304041500c903e0701016a0750680d0751790740c0c8092941490303100c1d0050b00d80e90341c9030f906c0444040031401c05c0d80d10a11304a040307551100300032036003110a06041c201894071401d1010703182d290721001c0c0189060b0b07503045c58200320450b01160001c40d03440c4403241c003810407050680b02420001780b22a02418041b801c141ca003500b902c0740c9400000b03031700114211030408500a00c010b40c0c115001064000c1c030042901c8007180c05003011081c0603001d000708200000b000c180aa0003000c40710380780303801c440a804110310308980040c00010a040070b0702041191201080c0052410807001d48605400080c8020000340642590003a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 773381294 773561151 := by
  have h0 := BRFrame.cov_init 773381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 773381294 ≤ n) (h2 : n < 773561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
