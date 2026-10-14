-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2826
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:51:49.627036+00:00
-- url     : https://prove2.me/submissions/484a11bd-0a1f-4feb-84b8-da1c133259aa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 508093525 ≤ n < 508273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 508094775 1250 508093525 508093559
    0xc07143c0c01050304080c0307020414070e10020a14240108070b03011206020913020d090b0a06060f0f020307060603030c030e040531021020010e100902040b0a0b04 72
    0x2000704280c00101c000280707140710060000700014404604019079030402c01c19581d910350300400c1840182042441c507141448215100d1000a001c0c030120725182c18800d503015560300250b4040c000c60a91526207900803030415003d10000e00c181d440c0d29030018040d40300040000094841c40c009545086a450b15110180c1c001c00c0700c00348200010402d04103144003140d5150390203040983c49903812030025400100d51000d0041d40350000803040f8401e0469409050200c0c8070f500011a40d894203107042003201d04900031800883d040c001002906800b03100c0c02980300c50a031044900d05030540c2d035200300f80d60440c0d00480219200424020805400140440150308252010845031610089003208240303860380c144801040c00805034100000b200001001a4001d40240d15640e0076a07130040c2520195010010202c03c101e8201c806460103010780c5140284445c003c0040f4141508c8800040031442012071f44142d40b0102c101046c1c40d10f402e40801401251051078496162480f0620303008610 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 508096025 1250 508094775 508094893
    0x320a0602070507090b100809013905190c1416060306050607050a02010509060403020405010f0303030c08010e0f060d060509010c03060503030c0a0807061401080f070603050c0714 78
    0x41400146075882c6e00041e10341d041c119161066007911a8110a80185803c4407190b030510a00901813501040d030103015003200648240b041c04442c0254000c803424020100000a0b0200705000041920702c511543e803503a50280c0d0840483e802e2098020340340410f000c0041440712402da40030000d594040c4500750040c2004d913025880d01007a40e5515031101101c0c1002414020003041031641501e940081c2c0b40655800340040040e942c4030302050741c102c035852004a00107400c015944243e0742c0300704d400718102e4058a8070003c00b501d030307010f0751244110010821500310309100442404602135000e114000e070811800001d4064070141e00074255451500007601a500400241140714000144805101c1e0007100140d00d5598038a80100070f8829450341c03003d800e581100200b62044045140704548010b43c3c111520035540e29815000d448013103179076070245038040c000000454043c1e14480390038103000003580e001500031100900c80381505854004014000001a240911105a841880503034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 508097275 1250 508096025 508096031
    0x31605030c09010e0712061d01030b0c0c030406050a0311031f0801200c03070803010f0f1a03012d06050c12030f0103030507050106180225320a060207050709 69
    0x400c040c01c00f09250141403201040760641b20500b448070503a000038054446500700180c1e1444514103081c4084c400e000039105042000c0200e082c1504840840d40d00b1600340b0041c60400d40780507016609900b02c0b840c0d00007810b86482407455101c0d1840c00562103800c80b24819603140d003083c00302c007010741015000340101e0ba2403c0c00032010b050101c04a102060060000d1036500c09101003210f085d070240e0940100100d03c048004120720003a00052401e642d02c00401c43da004d41e03503074a02c0007072905280041c00100810001442180940c042401d840c8520112a20705d410341200400a00c03050350380b00e180052404500c0a02c110010302141a50601004000e030441c10840010544150184002421b201000440a040003029081400102a604048006c00710124002000b95026030300b001c00d10085114154a405120202d8000c015000310789400d03108800c01d4102c0302017221044541003945003060415040c6030802103441281e00ca180c01507102d40141c41c1841c58034246070010011581 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 508098525 1250 508097275 508097279
    0x706021c1d0325050f1e030a0507020108060d12080115051801200304080319180b0d02091203130e0114060d02161101090f0303090b0711031605030c0901 67
    0x7400000c0d1036002c04030420b030090108901c01c02003180b500d1294010040d00a0301e0100f0614000030076107114030200b4000c0003904659651000d5100e204a00913403000c034505101c0c0d01c0155126010090303000b800600110929115910788107003010112880d400010754807801031041c6014807454140b0800607007040d07414550510007020a003000068001e0401c44500101c400c02c131850101801c1144032030090705e81d550b40b181c00c101e460768041084d5040f8007001503460ba40c058458442100c400c000c0c5001341a4a81c01d0140c05a02c40c2e03c0450422401074003802015815038800610490b108641401103a031080088080002100e0310381c41901018070110040000c8414141e030011030b030004840b850f60301c500b0a050b10000b8040e80000895160b80346184004000c044440c2c2c3c841404240ca601d00220794800d50103148180d2804003d00007aa03065041161001610241c15458815215105151148400f0914201000c0c222030180d555030042041a401c0a00c85500c2d03c03813003a40c80c030920b58 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 508099775 1250 508098525 508098581
    0x703061a030103020d1110020106140d261902240421020307061406090c030c0906130504022b020306010e01180e090d0e0a0302030712080706021c 64
    0x10005203c0030b401100101e04c04420031002c02c04450410300000c10f088020651100024003c4c0b10f140902c414002e81554009204d10304103280c464010360146090103104c0c011822030104070380b076201043c40b55406205003004208410520340e9441c10755401041004a080c501c00b500c02c081c1d5803001000060441880041007111032180740b140c244642103120320400380d008900d540314121010700100c0c98006421b04464805130403600400301201d015004da21900b075850564803068410b00c000740c0342080841c070141044c10192400768441c82c60300e45500d64170001b0505a81c000118244a1416000d5150a2044070b1402034191020142c0c210b0542c50000000b802c401c80015115060003c1d8035410014642043d1000025100090743c2d10200e08085130f02580d580c83c804014030204590800c0d2211f10f092480e2035100b12074005000b4054545000400c043c0782e001d01c5025144090104010004942d40c0d0000b04103c0700c04600c044002c20400000504840ba022070903407031158000842c407418 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 508101025 1250 508099775 508099777
    0xf0905030306090c07020a180e0c0108060111070b12010326030a0b030f1002090109091103040f1505040c03151415030709050c120919030f14070b0703061a 68
    0x400d40c283c410180d01c1e100c600c0084414016114020350001c440e600c045582203000b20b81100d0440b0680c02170000d000b00d40080e50300d0741d0840216074002035460f0000b030600d40c402e006400300c0c44036003c144c84074a9280c0e92440306540c880750100b9402e510020042041044540340c0340021085030503e01c0750199643c0e00c861961001400d41c0078955100c200712030503990b0170300105407540c082000721400310a862006c2d0010b900403043c3c060100300c60940c0028100d81c1c0e4066803c0710403e01c20918650350300d80e0350742d00c95211800f8064807803500041d800000401e561180c103011794007508070400158a5882c3c110f110106440cbc82040e003d0403e100028100e50b40305506030010100c0940c502c0e09035290011034604001607000e07a01c0d50b400c1c4414007415110b440000d00021200440d94880f59482e1301441795140c1c42d00c0700d00300a0596001088010901c07030780c9400f482005600e8414182c2d002030300c600415421a030001c0d517003864204103014039150588190002030240902420890340800c42a20f0a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 508102275 1250 508101025 508101031
    0x3030a02030403140a091a0f03010315020c07030b062103090d050c060a0305091009020d140c061b060106111b1302030112060f020f0a0315051f02010f09050303 70
    0x800340c020000c902011300840520226248445031309464045441004141e50058402d0405107000004c0c5c0d500c480a04004030381c543c0e0f4811060758903507469542c0d01c0100c2030380d50620b28012a0b090021410f6040240310650065000d0000303201c9900301901002440d0742100e4a0a60341d11a5405a08407800048190307250341c90100c170360308003100c0b203410464100540c8a0300300d0781c003010002d500184280c0680c4241e014048180071030f0144d110790b98002040320580317a13000e548250007050210004d15010b4400e64401080400d940310380c2c00100c0442c1d255040b810003d50b4440c3c04a04800a20208000d1740380180514909030112907210111683ca07030f000f1103542d4030300c10b6074840c0c0918141c5801c40d0b20190310a144204641e6582d40ba1506005156101c03170481d80142000100c062040c0b15000752401d240004d8112450300c800c042081d4001c04c1d2001d203d0690610440d40000c01da550050203040c10951104001204a40820000d00710783c4119034141080d49403503240404101c0010907258 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 508103525 1250 508102275 508102291
    0x1a090609040204060807091505030601080c190515070317010e1b0c0a11030715120b210c0118150e28030b060916080a0b0d0c15050c0303 60
    0x11562240e002080c0642042c0d008005d90b489032080019a000841e403100c90003440d01d003107160b8115145e82c1019220358080c4165027040d4026135881d02185000c001c0e01e582d000c444030102601603540c9020990503140200040d10806002c2103c6040c16001040c1d1412100c0c08002c2000e13a42c10322a1a008044024101c0640c2c2c0c1d106400502c3c8508034201140c842401d0401240c22400b00c80c03070141945881c54107018084d0140b07000004a94224840303120101065499075210410070250140050603910411580034040007802d90003c2e84042000300c1c44c9a100c0302501c8010100c0b0009400d0a087e03c04044485007070840070800d201c8011181d0f0080c2c1001c1c500a41e8000701440017402805c240640400d9107080c02183c0300044c1c440c410184100c912901602000d50f0f650410030508010071075400e0500084201005074092041e1061580201c4500c000149411135602055010080120840301d880013900300b0720410404150316402c0c40410300c1e185207070024076002c0940328000601025 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 508104775 1250 508103525 508103539
    0x7080703060317040f081614011e030e12120a050915010b03070f050903151b0c071d0402211005280c140d02090307030311011a0906 58
    0x2105144241c101c0c000554002c1c602e501051119207810b0041d44c0184a00c0f030f081c600303400c000500b4060104080140a40e2205001402840c00d80c0d0345200c2140e0048007070403c140e101c5425041194070040440d55283d41c1d50014200c0705000f245454040c1d89508400002c02c24020030306803640e1b002c50741d5841582201e010a654035031404091801d55000c2c02490441c200400200d842d13a403900103584030321030035922411003400d82042a501c42c4110400150150009280c0901c2e0100125603640c0012804191500c0400100d000b0b0006421100c0000b00c150043c400400030b42c820071350ba81c00342800009803000e140c00d2aa0010300c1200c03070f030011071501019140c41c00b03045801c14000101100603282c018007103854071102142080c030712003c03004101e21070b90701c406031031308014460921401050340760060908410334891000e42c0250070b5089105808001d0a41251405c2c002c28000303600c65211071000d0f03c04041031a09403074030203210082d407540d0000c01f2002a03850403001038018a0503030b0303c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 508106025 1250 508104775 508104781
    0x501030b0a03050102030403020d0207050d020f060c2b0305010806071709010207120e0414070f1d0607030903200609220504050c031218011b06050c09040f140708 71
    0xc15240120765001800d19480172042105040e00803580c40500311080e4280c40c03100b0749500400c1761404150f000a034021240c504070a44a00b0004000c1c1100e03e01074046a100c03454210610035450036002c00000440d88107d41011400d4140c000c1c1405054200043d0044e8540104018a030705100401c92550799000004142c00100030340c1100c601c00e4206051000c1150304030301c003030801111081c80d107028a140002d441804003030580c01502070741c226540c1c1c154501d09400c08545000b18088203100c1c0d04040c0b1900965562136100404003a0710903101c1070003003443c508000c09030902c00308a04001c034141481811150f07450808807540800e00325200e1725140c1ca241d4208403031192010901e4190fa18000038881404400140c07900c40520441c1100c58403594428044031341e000c0d04414403070b060440e1403122900d42c0250103030a40400d617464201c1c1c0011031520345a0580da025100000002400650254503051130b000f03c50541171180d105128840c0b03c0442071180b840010002400c11150b0808 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 508107275 1250 508106025 508106029
    0xc07030c030c06050c12010605031312170a0e01050c0c1c05090418050d0507020f09040f05030301030b0a05010b090102060a090204021b031c0606080106050c1212150a0f0501030b 78
    0x190002d000d400c54010401d07458142d544292660201d1401080c4c10000303400000d41512800c2100d12440680182800030409569a01d0420b40b00e181884140651070768102c00281102c40e24601c0741040610204060130f5080c951421124081e0840040310020403c480d860500002c040f000500404094810b840c3c3c0d10388100c415018100c3d60300d41c00303800d101560219910310407844100314000c0c1e06a0b0b80d05416240705550302d10400c40003c1d00f240503000600840d01e4128581d90340280541090443d0a0107a510345056905c01d8008803055020380c0d050083c0031005100707550140920a00c44c6103070024490010b59143c900900402345561100d030385400310f46481e0103a4090910b03d01c44504134092000929072a50000b8002c5004105803411b0b1941c45403413400750340300300c03080b40c0c841120503405d10108403165800328010388a148201d1031083c0160301c0b100c000304900074954422500d21304203640d8146280b420000c51030320480321040c0902c22490001c141030200d92007400c0002c0d81c0303111000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 508108525 1250 508107275 508107287
    0x50307030b121e0303370c0809060f1e06030703060f0e0c09041e060902060d05072c1c0c090b0109120b0f0415110c0706080c07030c03 59
    0x1103400e400088141c140c02c055080020120b030043c203100d9074115122800400c090780c84c0011a558409142445040c00034044007440c0300c00c00105914000e01d680c040c2c0280c41007681d2859042c1c200080b060000c005131103c0a00c0f00d150850340c01a01c0700400c0c145400c1c0b00990344c2c03481d8000780c103924520010856075601004020010340d4844010b11010381d45441c0070700148420325900ca05d50085a0f0240070901c1d103d0380707062180d50f2200c500f646c50345100b2240899080c0d03d4808451040d0764034031220141c0c0d19100500000016224003040514050400410504074950690380294845002d076550540300880b05424446c29a07500040348281c662a8200d107441c40f00240020121460102d12408640c014004904003a01ccd00b03040640d40d640911050821101c01030000200e40c400f0604a000b4510752640040c02610f00082d0a2560b900038403caa1800e00c0c0101c007000c0000f10310a103800140f080100500c0d107401d0036043d41c86c00d00346171610362046000040401803440c1c062010140141 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 508109775 1250 508108525 508108541
    0x423070317301b0403021806062104031202160b063006010807080307030f030204080d081b13051014040e0a110f0d09081e070605090706020d05030703 66
    0xb001e120200b002c14940c2c85240002562a80c0c8605554a040603200f5001c008960449a01526000c981b6039192848169039a025190f5540540304101030a0700f0910780140101a00c0480c1f188409400c0c035180103030541518201d44114140140802201071440f4080890303902e411000340d2501d0b50354400019407901121885000b01d181002c07100c2142c020a00c041d442110140c412980241d0300d940c0000e5445125110b4404158010420540024440e4880c0c4170744111909001d41010385540c0928208021400c6250000e10490200400140c120f86603a0805440400c3c2c0d0345440e001d81d05c000c1510140d070090f13034003903094201030700115445555003260881032031502a80700c545403244d014200c1700c10b588840d81c8500748854200780030500b0049450042001c84180e06d803034070050b01074024100c840010781c0c00b07240c103105219205440104410301600840c0a460340c0d0041483c00c001194000307403035880690b110980502010b500041d44521490090412948980e14000f04401034050380c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 508111025 1250 508109775 508109827
    0x807063e010b0324061210020c100c0f02210f0c0a020603040f0c0e01180903170703090204060f060917010b030a080702031b091512060423070317 64
    0x3901d500904030b0107048034130100c1d41961070080030070b0312030000300f020044410040c1c440540010031408540b002c0e42c0e0081182e540390405840c58011132925003000c441241c1100400710b509200159002541440030080c560f00d801903150014141c02400851070040510810380c190300012051280e000800210a12503402440c8541e01d08e464580021b0f03280c1c568408130760340c911100700407903c01000180107058072900007201590481c1c00c01d010b006400001c03419428810381c000c06103a04100c1b04800d92040c88640c80c007050407802e40c81400304861160780001601c030010a01400510740c44103034241110a603003103084034a00315000850041c200d400c00b80341c0c54401d150340c0008000c038810140c0355140c0200c040d075007024454200c4007696003074201040c0d0302c800f85400003440c80405204420103680042e21240280920440e00da107840300079102038420035014001c0041104c284409810804272a40c05483d507545180d4610310a1400300142c884440000b0800700410303100d8004421540001d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 508112275 1250 508111025 508111033
    0x3050c090d081606020703020f060601020a02011d130c0e0f060409113a020304030c0b1e0f09012003060d170a0e0103051503030d150f0807063e010b03 66
    0x80d10b0035134000d522000044026008802c0c2d8000040d0010032103501c28ac2c01a00a010341528580c01101c204429844080200d03a4105000007140c07a81540c10450402c45100040d40e03102c440006001c8a0034181e60a00c10641407100b040151283d00c10340d0300704e82102102144808526041d0f601a001d106041c420300d00c0300b031345031a9804604036a51072651074102d42000290403455059000d9120854024001c00e680180d00c0000075200f105071035000e00c4100c0c0841003a82400c0030742c00710310001d403a48103c1e900310905015548800707109880d0b4007090801801e203000d0b1074900102584c00000c1031180302c0c445d14110341050103091000c1020841070039600e10f40e5048219800303000f149150706424006860180002c0110444644550a00000500841c02d000003c5482e4001e81108400703521500c5203c1c4002910b0003001044074094115200500625030801d84010a42210100000c1c40c4038903078056072514402d41b0355030140c07010100380314410f50421040001e001d801043e400e9601417103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 508113525 1250 508112275 508112317
    0x201020f12040b010b040302091605090a090614030a0b190605060706020a110c060f07081b030a021002030613022b0617010c021203130b010608150103050c090d08 71
    0x4607a0040d403045201e981000010f0b601c0d0500d03d82c0d0741c007075800002c0d0000403030004500440d0341b80c08000800030103450250b05d00384404000c0340c00127185a2040d00d4054031480305116400d0000900408140143c00508141c2d80c940c03601c0075040c1c0082c144104511103a11212165440b54104202a1801501043c1e40b541740345406030003540a49002070000340c00c556109070181000c01d840c228103400034452410315195030461511548403003821074600c0810010b011b00b42c0c82c0d200144000001d0940030795299030300750401030306001102604610f4a0b10400c104501c90f600c8808800305200c400c1001601d8207815050300440d40a407003550103030001c40e440181120840303900400b09071400030500312100c003000c0c0d143c00d00340e80d06261041c0140e00410b41c0c0b50301c1ca0043e000610f521004006250754050b445443d81001d19400b80c12020000b2200f00801125510400d80262804002c0c13808001d286040510102e40d0b014400c0c11301e124618214081007445030a506465109120942c000034000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 508114775 1250 508113525 508113547
    0xd12200a200301060b1c02040315051b03010303080720010e0601061206050d030c0c1205010209040c1809021b030f1306050f0d05040602160c0f05120a0b06010201020f 73
    0x2035a0181d5021004003052000e0050906008072000c03160746003002410b0444000c04000c1c000d82014001d0714140d4248400004105686100f09100004410006403030501c285003840302d10f8503041050b0381c80030402c01000061341c41440303540d20460900c0d180e0010400c1589080815082c002800219801c041a003800d00b20301003240fa040b01c249465501050f140100c000e015a01280305607984400d680b0036090200b40110800450b042c854010000b51a4036100300c10440032103202d007900d0582d4041441072407410240b1515041c0400d6080000199000b0104008164824002c003807201d90081003140c030b07440d18001000d900784d201c0c10030f40c0d4442031074040342d402c80d40040081c225400c404010000c1d03454095421034070100c040f59400c034030300b1140042140160502a00440d01d1907400c0040c0c00348999003140702c03030700c8a10130342c02d07102c84c5442c1500703c8e200c548080e0005031240d13404003c45020403500040b0b1480d5617030b02c00510800daa450200503402405001c2000320b1240002800d20111 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 508116025 1250 508114775 508114793
    0x4120c06111908010618090c0314010b090114180d05010b0a0803070501060b040f270606051207110a03030902360c03010b0414040605130e0c0d12200a 66
    0xb803002540c8100240e80d031000b046602081d400c0120f1500b101c0b80500b0312208419420002d040c04003410041039030080d50142e2552104264040321100b0740108141820b1745e0b10400c81c112030684102e100b400e000380c8036075024a0000031186203100701c2030440c40b03100700305007900851b00042c002031035141c08560f00c0e444145c40e80d2003028100c8185d46080404a141c4a1400a81d01654103006034541c4544c1401e144008407468400011462007130b643c4680f071b1110003400707404050602a500c442d218000f082040e088401c000d40034000340000524a10010403001522624440c0c1610380401c41404a0022620850355400400d03035403a01d64030654000100442e00f0a1920200100c500480d035900c4412401d90100703000300368413a58200410040d030380da80100e19001c850010b02c0000c07445c0d40c2d100041d624240c0c0c00c10700f802c41600c4540407180e07440280990251184261200d4100e41c20035034400711190042c11074442405180a07103842040c113424004a801c3e00303590121411004a400d01e1091 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 508117275 1250 508116025 508116067
    0x5131e050619080a021615060b19030c030e03031504090605010608100609060207051002102a0c110402070807050105040302032718072a0b0105060304120c0611 70
    0xb064005001c11503084c928400c0703030b80450702c0b203140800100080d075608020115034501100010740740c0c0c00c0406c100c0d100000500c05088007a1210f2442108080c0241c00d9070020000c110a1502d00a03041111a80202c01c481d07100c14040aa0881843ca1400040c000c2c1030410002d006035281c0000840c00d03d400a0941d4010310700d2541003200d035940c2d5103003200d2850343d40c000c160051b0402d040410890401c042140c2d00001c0700e00590b0b90f4015015060400c507440702c03003402e420f16004142c420b410f6005001c5070320501c200d49041041c014541c1c84844221a05c2d00000d070085500181c082c06101c07a58090340c0b402d50b80407000344001e040a00f4029604d421888480c55461950100440c004200744001c41e0451400303080000504203071008140c04e180c0c003d10000a004008046560080c0307007000071b681c90342d0304104c0c5204585407810b0401e013484050300070350301902042003030001080224034400003442241c2f80c03030300742c2030801d291140140000c10424000600042600f14040c0304995400c04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 508118525 1250 508117275 508117277
    0x3070306050c0703112b050c1b011206061b020409080a090503060708090c0103150b12010905010f0815060d0212030306030d0201020a090909020f09040b070e0105131e050619 76
    0x510070414001740f0789070211106800050070101c5d03504c0000950a102d0f1880309040341c144582014011004103041c0860000440c00c9005503162104d90340d0b800041010101001030003c10050b8102880540301e00c4002030f490000002c0803141c1e4046540316040500f11940c00b580b2141c540d212890b01074103042045c0141d500c24054200014a00ca10a440a5204200c030800510100c0036650065001b803a103852400000d00d8582c1c004641041d00700c0046c21603a4070202c00395040d61610840b6800c840781a000600d902c0341c814010806000c001911040d0045041103942c0c168960700d0003d51150304069009410900318907076800300c1c10020000c3d52091009a0a9030418034001000728201e1286071543c401254401a05204000e038641c0408102c4d07101424050546048000107020401e0840d022290380148d50100200198400c41c480507900c000c1c00d2560070b0460030600c0302207013441402400403243c08500300d000350349450044030005050140007603079a0303201b074500c6204030001800480 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 508119775 1250 508118525 508118537
    0x130609060e030a08040501110a02060f1206090c09060c0114070c0b060906090a0b010509120a031404060c0b061c0305030a14040f0321060905060108070221030603070306050c0703 78
    0x4041d42c28041501540554001d43e6140781c01e00740340042d42d24504030454103855205030f50100c0d005841e22030040542c0e205500313241c0e49821068210306644d9070001e101c01d01409608091200108030003064a90740e860407100c240c3c030703607500440c940d00600366040b5101c0c00310302090070700800d0317a00048441091401821491025510141409840c0d28180c0c0d016070024041c100080d032403142648100c00003101458441e180044500015184404459406641c0e80200c0030007020180c0061111034203514110b501410700e454008040c01844a609002c0c145082d004005140c596076401e64000c41000c4145000307100005080c000e0542d041103820500c0300f0710b070101c0340100e83c08802565125540c0003081400b079401664040b103940343c448030081e44400396a5548440000c00303016100c0a0003a40400107100c7c50090001412100003520513420364216640709049c481c040108540484000c0d00c50136a2920b550000c42e10b401c0032984050101c80c6841c5c1803000f80390f0b8050062228034008e81d110f07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 508121025 1250 508119775 508119797
    0x901260a0c030b03210c060c0d27020f120f06010312030b0a1a04050a090c0905181f0b0708180102010e07140a03020915010210020a020d0809010213060906 68
    0xd804a6142807442641076000201d8454084540100301c100205c01100d55810309601a440c42e20717121082c1d460100c010004198041080403030700c24680b0141c8021f031800d400043d10007200d0366402d07aa110182c0180e450410f442c00039120000d80c60300b1104840104c83c0082011048142c07180c2c000e01044800400010450030701902c00c1c001c407005907a000f007100442d2440c1c481c4180505040d41c082000c012000c1c400000d00d517442c000481d0080c402e461021030780d068003100007041d029070782e00298440c0448045a2011840d501041c5900032035052840c00c0d05008444060901c101d030f0741c45540d00180020b0128204592400504000704000c0080d10300008442c0040e400e0790542c0d90b07640310305e902904081086544880003245400c0000d0004112140c8070b4002c1a80f00340c007150102c140484d90300c1654040d5034100310084800f10031940c1141001c080d1440203440d105005034810400c0a810085000c2d034100b035044a42000a22804900b0241c0d140c9001c2c0c81003c192082101180c070700703524 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 508122275 1250 508121025 508121027
    0x302010e0d020705010e01080405010b1c0312090b0c030a0f02030907080f0c0303030f1807030605011d090706030906180c0e0c040305120a180b220f0504020901260a0c 73
    0xc4141a24016110807021b100c1160045480400007841510150f4072024403c00949513242428110300007170f00f0001d804505404c0141000c0000c94280d0902031400d158100840d4174209003d400c01c160310a060307a03e44841442d0800752030b0305003011384681c1c80082030000c403da00140900899071000103481c400440c403208662900c1e42c1c00040391301904200002007a101783d060400d54050804600310b9644071103d51000c1c600030310340e00122442d942d40c10042c4090f030070042030202e989044650408403484d1030003001da15804580705034414162201856410000150810f01c1c01040112040041d48070500f001d249402c018810b0b41c00d0410880c011440c843c44010440e01501e07000002004c540f15000303c004100e5000131011000c122500341c011810303a00c0e03100040f00400da03007680561640d074030b5600a081c044807200d045440c081d0300c0d44200041d80061101d242180d10450740113848246800050703503a403000410444031941d0074008104420105070000f0302985e06104200252800084c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 508123525 1250 508122275 508122283
    0x9080909240306060907030902010c050f0d110a0f02010f030f020f210705180a0521010e0a05070b0f070c030c030302120405090612010e1002030103050114160e0612040302010e0d02 79
    0x4d181500b0802d01ca000940190103074000841c000e1040c904010800000e40740d2a0800302903180343c901c2a00306010040352130307074481d40582608000380090841e032501d542e102c2004508080c4001d05000c1c00005402c0e034103010350f2042288100b000310640d6503050404d02c8035120703800303040040c0b80078045410801d00e414802c40118400c69490312124948100d95805882404400da65541e200c009034502080c1c50320380303101032180911070304664260300d0184140d2500b9210368409121075036014214107004100700007200b0048495a07110f455554010b01080740d59441000303006001039590806c00800c2000560760081140d00a40c203031581c4084004c04032405109900c00e2680c0704802d80003040c11480c03e01081c1c9a01c4869900014074400603d0030305003030403d002e038021240f0f40e0110040080c080e0a005140400503a1030365400e20f4603001d040540408294014034080040700f14003200a80c445a04440002085889072805440c1c0b6140080c0130740b4120420340c00d00e021b2000b40c1c01059000003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 508124775 1250 508123525 508123531
    0xb01060306030c030b1b16020a060e13111608120f04020f040b0f03010527010507050a0c110a0b211006031806050f061801050f0409080909240306 64
    0x41210f41d082ca10b5511070712200701c00600406080c95400103000c400c1e803d444000c003044000c903070081c44483c80034010080e8100d940d5010740140444070040b68038650b14550604040e001c10440042c5051601121418a00170030030310300c2075400c2100107001840600c0014100c6654002d045038081d6580c4800581841c0054400a4000c4014040801a49450340043c0c4001c074016001112801d0400006825a00281caa03e04015421212021038400d000100200d800c1207400a011f00c7c10300007801000d40c401e40c3c0ea039104100f043d030304d45030410440d07140011403498020aa01003c6e42c5454039003095034400d030384012202c581b0134000303500c2d1031905a05c01c1c030641390b440d503400340c8524082c0300350042d10080b041c80f0384101c00894000e001503aa03120702c40c0100340b01e14100c105403900005100741d40000300004001030100000401c17007903440c0d062418005000f660085901201c070302e4a00d505009400c0407590003000300b001c008a641148031544403141482001000c02d080000c07c1c15207981c000c1d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 508126025 1250 508124775 508124783
    0x1603080412050307061506030e0105060303040302090c040b0a05030f01120c0b16080301120b071713150e0a060b04200705120711030607080606190905060403030302070b0106030603 79
    0x2800304000040440c521151070300d00a40c152444d200c01d40e5140021541c03c112008100c080000003481050391600c560034060030340d08002c0000e07041000c0007a54a0155100c0244103010180005210701003100035140103000703000a407a181e00441c0700213842c07a00102c40c2004e001c81100c0000502d4048803542100c140e80086e51603001d41d08000001c506a44810b8182621260b020007001c00142d2040c0158000d06481110b0910810107291021140e4005003445041203145203104603610005401240c011f14240c4c401d0210030ba9070300c0c0648016482c0400c1c01c92251034a1004050001c004c076030503840c28071401c01000700f00c04910403c011501c0a410b40d145141d41e14200b4545014000014411140504121014034881c000d1401e21544011000c071140009030902c480c03a42010010b02d90000d5490520401c18605200450100d01962188000e10a80c00f100c86580902503107441014000c05403080f030350340d5200d0038098041d50002c18101c80d0508900000038255129210341000c0d00d500c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 508127275 1250 508126025 508126027
    0x302091b1209070f090e0d0314011202030a022809110d050603011b091802031e1503120a1403090a030f05090607230d0e1306030503070c0305160308 65
    0x10300144201d0010040024215106803000840c0d401603084114004003c4408045012000150140d09140010035144149820020349013003a17031402d040103040d035548080e00f4ac010903003400081d1425141203030203504903c02d28030680c0403200410422480c000f99a000e440482e90b600c403040c0403150340e20450800d84805005900c8115503c1d00401e0708150010b00126120700c2801c0200545000600f41d01c0101c0c11500c401c1007048458222031100520002d4118151310b0100c5900000c8a6a40101c5514070802e00004104200c0d0002780c2102c41c0707011b01150341003440821505481c0e401600f504012a007409068030218003000c088034401c0d000000604a88286654140da003e18540803110a00c0300c2130107440003e4507010058203906029040480f1590740c0c2d0002c030781c3c0101ca100f0900c00325400c00c1011040c419000400203140741c000307584507a001c0c1901c1900c1c00c014002608020002c0c000020008148890203c41e903095038040ca0598444020000007980c01c40c0c000d110040101c44 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 508128525 1250 508127275 508127287
    0x506010f1d0d1b090e0f0c0609040f0f060f0501110f15090733080601080402300303041b03030206040602131e06020c0105040308030f0405071e0302091b 67
    0x80c80e640040000d4440c202000451aaa40d00e1848045440d081801103540d45d10000310090400c0080070751150307404002d04011204840400c2041c42010324041c000c030384454003001f076188507501c8100b00c54040c0604000844c0c6030501042c1c40d5440e03114040c00110804e00611940300b0110344060007002450081101d0102001101c00d5440020910b404a009d0350030005100c918081e50034100305001015480e505029140d6403e62040d5032000b0810480c00d0400c000481c2d0300b1428a40d0450b03011136003031001e20180d00c4040243d40d28030094081d680c080b03100c8035400302e60000c095400b6030710a00200d0314081e0460314074080d8015a11010700160302c12004180456004c1c1e000b00920080302c0700101d079041c0c1702c48400440c0700740140d00c43c442c84078407282044816414010399034614424a4501c0ca0a880d68480e80ca1501014140600161540d0041420008100000c100908185100001042078603018100908651100781d0252119034001989144850550078080b65403100140c2410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 508129775 1250 508128525 508128529
    0x10f02040e060d03030b060a080105032b031505030106060806120f0d05030c040f17010f0b030a140f1510050306070807030c090810020705070f08030f0f0d050a0506010f1d 75
    0xf401101042d400c1c1982d52811a10540350303c0c0003132408050b1601c038108254508003c0c10720f4500b483e030040c01114003449540055441e032207900c98500c00140303000b040703071101d207401e02907a030015138881a0b15601e406000079042d90040405032145d0000c6440c0c0e468804444103080d02c4038424154100c40b03030410b040c10180c550080c4003a41d00150f001208a040540311560580d000e0074a40001803034010b01503c01300d04c50380901946950784501c80f030074848a400d04001c00d031f581054035002007803074110012407100d0141c200140c1611038640350844100c00e20100341190b0b421800d513840070103026400004601401c00040c0b80f4010f1240750f41e168131544d141d081c110011300d82050400200107424500280c030304070800024940051204006a0f1030000d0300d062480c02000c0d901c11841004000300400c004000803064035105140c1903480f41e0ba42c05540c0c000740c0070303205d101c0d00401c0d058034020a2203218941507000c54400c0c00c2c2030300c0d08065620082004c0d00c00c0804200406010452400c0c0840f030740c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 508131025 1250 508129775 508129789
    0x8060f070e0d0b010306180c050f0102030f0318100608070303120902030a030809010c0c11090907080105070302040f290d11030a05060a0501050301030c0e061309110102010f02040e06 80
    0x4012450044100c4150100295042c240c044040d5081681e81c1c0050052000b1441083d5460040c41c514117421051681c03001d8810049105052107a80103003240c0761540d00910440355140007020000d0b03540d01e0100400743e800350205041c00f0030f5103d028880e0311030424910611060f95078010003001c050785169011141c84007c549581c00c8035031602c1504c40140c404201c241d0304075200b922007160070b00d44201c245086400e0403240b44100300101107414003040e9068502c80c1d21390411340b885091680c800b580c0c20320f064410340c0002461361a000400000ba54160701030000e85010040340c5102c181d0301c6400300a08217a441009504146140325000f018000100a10300031700c00c008042407413080303102040e840d9041103510310b81c99600c80003080824944207054802903c801d003400380c119410b680350601211500c0c041c14540700c0c8a000030502654510b411000501ca1070030041c0302d544014031302120401c0100c191580035608200310010943c40324002e0f80d041d1075080000301002d645000802800c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 508132275 1250 508131025 508131031
    0x94d040b04050d06060803032e120b041109161403150f1903060203010f0509010b030f1003080a0f0210110a030b04020403170a0f0f0503040212070e0a0f0b0a08060f 72
    0x40280c5d80c2c1c00010340c11b4414000ba5101d0403842c012164a0f00094021106000c42d9174030b09812481400d40c10301c031415042030189500e40d00140d26102a95852625902109146402641c451010010001501804102e840410000b0b5640a00c110300240c40b0100f44e000a5a070078480e8402c440e40801c86051180b411051400c00610851a00a155040318804603440d002031328260380010051040d0480c40400308020801500c1702c00b110340c500f89a001d040d0202030f00c04140210b400012072070202c40c0d1001f400240d5041406650303640f811700c8010b0030502007520032001500500030b0141807003441d4803405a0090511510350f241c40c01c0780780210300618081030702e15880303036007030001201007100f06030311410804032400034036950940b410020f090450307034050010410054884100b52154032109a81c2c0065068581c410300aa4200e002070030261140c03c4440344841020030055042d106800c000c0400070446000c00c980904601032001400c501c0c003030340d40c079680040040b408110083c104a58 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 508133525 1250 508132275 508132283
    0x3040f081507090b0306032109030118120503040f060f09060b030601060f0c03020f010c20160509040807120207061d0607030f0c0516260601094d040b04050d 69
    0x407a80708c55102e201c104007003806078040e100d20041040f03001c5050902c50a813800c00350404031000306d5140e41ea10801d11034a82149000c00c000030020508200f8102180c1140c1940704e81c052084001b020b448000411070504166541ca007041e500d1402420b020403420b06803800c50307441c410700e12343d000010740c0d510950f000114110f126001c01c0b00c10a400038400c0001c5500503940c0c0301803460114211100c800020100b85480f50494002e20000c4800e610402c2e0485030280c40c4d620310340d5a581021005401440c00151001c0c00111000d04025030100d49107054510039220303046a251000d400d00824101c11443c241c002c03e0400c00c01020900803400400300034140d04e040250031407550f0f2400c1c100707008a032540c1180001107030140b02160910981803070303102402d014140f0b4403c182c450300d6607449040c0b10328403c065031025014030050030901c5403003403010300c0d03101000c8907401114a03103c100c4141507050650740c030324220210341400c1c000c00c40c1d08403a45c842c3e0700c5042134244003c01a40d02e6101800321 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 508134775 1250 508133525 508133533
    0x60b092406070c1811030c07060c0e090403090e07020304050d020405100302060c0a030909020903150402150c100b0103020c1005070903120f02010501090b0112090c0803040f081507090b030603 84
    0xb00000c41021040001d0000d022650050500141c1c1e003809a075003512003883e02540c28400c10004002640580303840383d070080c4011918a2509100756100241c0e489840c6c1c0083c0b12030100818190008494400c035004a0a00d160954520383c04a840703006600420b940b01400c1c0400001520700341d00290f402400d0900401c9446507203a0001c2c0c680d40c080e0320360000d1030300b103241c010003807503080600070006160383c10043d072801c2914400a0b485400c2d00c017000c0525980c8602017420b546451107002c9000b10300e080d4442e0795000351700d2003507034914651403000c20f0320341040203803861035120b40282c901c0c095022000707040c0d0b1204000c2490182c07000618070401c000480c1400404218610106403d004080d101c04040c000304503002800e555058200e103072090300340749860400d664060040c1d100514403401c00101d1811601c0d00d4151a0026400345402d8031000c06c1c08100da100c4407188030b044601d0041100d258000d000800e41111400b03d8104001c070380000004c008100311034009680c05100141a1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 508136025 1250 508134775 508134787
    0x7090908090301050103051b0108190509010b04021809010801020a0e100309020d030806010806030609120f27130b060d091e0c0f0801060e2a030c0304060b092406 71
    0x11a085407001d070700c00d50f8544d220300415007004181408d40740105000303103050042c1d8031740034031940e09030b018089000c00e1507691000007900c0c511082d4426041d007503000307105650320980f055141c00c0c5551070b040500d00c100822000010341200500c02c5540407a0542c40385000004960304005211415440e400c05040c3c80e4400400141d0f0b8080c41c250b1828400c0d01c40400c170f03082080004018940041045009511500c188040b02d07900203a40b14050999031031260f40c980c600c0d1080809400b400c10a07048416800b600c03001c4615240201031207488060316034809034084091244250f40e80060402d40110040040c002d11640c20b400c1342c1c224a006810890340c8400d9160b071b503003940d4031000301901e5100c0a1841802100115807002c002011160700038045207003480c0e0170b0040320310080c1c40070402014010080d05200c965002560852200d041042c0c1c69242c02c1c0c0c0c403581150310444045540f20f250031807408243c80e0103040c1d80d0080b42c10900103400300390000d8128030326201944155601000c14000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 508137275 1250 508136025 508136029
    0x60c01050f01090506060a0c2306040c0627090b06160f030818070905090a0209010906061202071e0c17100b010f0c030f05070c090b10110709090809 65
    0x1400d005190a001c001100d614100c610340446001402040c400c01c0c04010101403141d00c0f40b6a03810342600403402d07455855080014640c030980d1802c05c00f415005030801c1200784900ca040500c200c0b103558a50f801200b003200ba800040c141d141c44408a6880b1540b401d00048100341d203c86110880600b01c940351035422208080034000d802001c81d01032102e21021020154008000c0342c0200102020782920040400d0440e1039100328080d00d040c1a40d82d50000310009400c000c80503c0e55000b910002075561908040d0010780b94500074400841c0c540d4a18048204480c42150040c60b080944540390003d9245030001000f401030041c2c0c0c0030008050082880301d0450301c0a41181d450354000d19543d00c4141c4040b003510700c0c550b10641030040221760a88041d030400068a1456454070b444003800840f440290f500307004012000d07020400725400030812040943c00a400101e04440102c0310550204c2c0032110070040c04801011a00b1146040207242404d4108050032841180124108681100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 508138525 1250 508137275 508137281
    0x40605090a0812041707061a01050313080c010b0405071d010810151e02010e190c0b030408161202150108031c1d2103040201020615060d05070e122a060c01 68
    0x100340c2c0c0d010344d2023010980900b01c94865040041c02828114150300d48901c144c3c1d03144400090284c4000000030b4200308040007944a21300b100c1005104003c40d0408040003407603118000341605400318090500f81096000c0c0d0803c0d80b007215400c65810801d4200680c01030300c0d095508070701007800b45064a88410141c1c00c281782190780301d20b074000600c0380e50418081b46846e03030b100c02081e000c01c0014608804240009082415203a44000f010750b81c1d02c0d00d2401e41e185120300c88121074080001c0710f0b44003c01900b1500304c0603050b0a44c0c201c6d42c51440240e03443c42e40d00000e12505030154020050714005100304140d070312800700d603018000703958050119100d110141c001a14061500807218417000070103c106074034150b801d2141c0240c250f02d8503a00103076641501071301281d0134100000c1449000e40c1c8000459510602c0c4440070b0205061410003d80b01c003003c5580f4031310400c812049180d80b000700084080590300030400a4485e1002080c1034005040d1800100b900714108000b80004480c00b40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 508139775 1250 508138525 508138537
    0x70e04090b0c180f0a03030f140d0f0605040e07030618080408010213150203030403051602040906270c03020609010507050607020c0f060403020102030a1206050414040605090a08120417 81
    0x8440c0e250380305803060442c1c845030102180f01e80708101d04004111243c5a200c0c580040d6989030501c00da40038030780301d0b098402c10f046802000584800060700184014a0340000c440c90b4580c001c148000e503240d0b02004240c2c0c01c1c00310002465480b200c010408240c071034000e06001c0044211044080d095925100701642c0607401c036041a03074000828141c241c8034500e0b00d600426170203001c41c00048072010b00a440740301c058805800c000001c11064001e5090032404c442842d8003c10400c0401d0003450400050485101a8140041d00681d5485804500c0d41c41c500b205500080d8400041e003150308002c01500500d903c1410444184040781c0029420030149004800980040000c0c0e00980704200039042c02e290130500520080c0001c00050344c0000a8415256140c01c00280281d000c0742c95000600c0749510070b962182c03c16100d419111001c4e0402070050303004242c203002664401e8112982c0e56444100102404420007080310596140c10f00c00c2d406c41d22800e0f040c1c08101e20400807649542000b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 508141025 1250 508139775 508139791
    0x60306041d0a06090b060f01050d0209040f0c0e09010608011809110303130f120312020c0f1b01080901020f030610020705040501140108070206010602070b1606020f0403120207030b070e04090b 84
    0x4104150170300c500050515488038003203455480507503071031000030414094150850101500411a194079994941115003829281401000010740342903008042100c0c5025443c0110007200001c03609510441d489416034500030384008100d82c014180d04001c100305281070b42c43e40507206001e4043d0781c0500091007898440894120024140b134444081c0401540c441d001d0b40c0075038441080000e4004003207203654101c103000141c4928504035400d05050305000740c00c400d401007248a9104080811120030918000ea03503400d050303a1490102402c034805c20000764007180080c000184076144c0a1140084007401e44191000d10741c0e1040407a041d02c200303811400b0600d805110020155030300c23910310b03640a4460701c000d0a1651520502030f454000601403913144e400001000c0185104820001042e5984414115075520800b0301d054056041400115460208205040f0b4014800564001a82e400460f24401074071030100c180c0300c88102500c07042e0004c0d1140080c0010442103007001c1d120b42c40c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 508142275 1250 508141025 508141031
    0x60c070b030c03040c140904030309020f12010213090b1f05040306020307020607030e010b091801020417010204050a060801030b0c07020d0807030f0206100f0e0903040503191709060306041d0a06 85
    0x7240c40c0c0001c0281d45c58010403036250700301d0320703101259490020721a0170641601f80061020315a0022441079805418250b07000406099100510300055008220340b81400184402250b11150150305881c0d0f511011540012000885044444209400c2c003481445040503450701d40e0303a545040aa0300201c6055000d030300b0280070007000a805000704000034414100030007040e100c0d6800100000300140060351450302d21307910600c0101e402d60481c8c0c040c103001c0c036083e00300303101c004580c40c040e50143c00740c0303405050b52900c001289805100b040741a80e5002c1850708050761510601000342d00320700826a8411070225024000c50880002087d0090090307580005111195001a280450240010f042050016010401040c03c510048151522900d00c80342d15195284001d1850069401240d03043c00303403203562071203450b40245c1d00d41038a124002190000c640d40c000281030b401800c0c1c02c25041141040020140d280a60200f0700020100f461f026244560f03000c010700c0d050a0301c400300d03031040d1703 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 508143525 1250 508142275 508142281
    0x601020706050702061b0124080d034805210108030414060d0e1f0c0c11010903080d1e020c03091c0f030306090b01020c0a05060c070b030c03 62
    0x64103104400c064140c6050142c03800c4080e5010400510400c018401034420071510758034821001c0d0846501d180c240c00b4240b01c0852004501404103c3c2c62154030303024031620118100440c00b900440c0e40c0f038103101015800140c0340410750a4042d0345071180d065114140a54802d000f1101800c010141c13078540c1c2c810381c50b000410b1840300342c1c003050040b0b03030b6000699000400c1542c40010480e0143c500307801c0d8440c1007800b440e0100f20326004040100912504101b8281544200010940a0741a051f60340b408884883c00d0b80d0b50840b00f0fa0440100010310340c40c02240800e201c1000318803250010301d000702006580b621400c544d908440040640642c54003400c403440106111101c25185401c4821490b244031001820764911a00c2500d5000c0c02081506030a00c03908100680350064208000c2c030800405450002d0051841e40600e90900c0d28001001100e54400605064544d102800c0c4950a60401c003c20615400403152888940b141d4a000f00e12155030310044c1d17000714006860035071641 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 508144775 1250 508143525 508143527
    0x3071e020a181802031207260c0d051e033301020c0604050a060305130f0506101d06061804060315110f04091a0306040b07110703080403060e1e03030601 67
    0x1100306142543c0003400040001c0540e601003007200c0850745290303c0c02e03507803070b15460300101d05031031a00c210794814181200682e400d803c4000900640241c002a038403000381030341081c0c81e1030069064804881360004207010781111454001e5030810011141921103989421944030b6070f610b084d2810714883da10034140300c519601008041c0d40c2e03001c11900d1508050030400407494807140752040710201030b1030300c0c08145421489441e1403a02030b08044054124412030411603070381c0d6409d941c0c5803190b502203030000524810401d82c002c5c4045152081b0046a1100d8041110715080106e100e102c142079096102107941d2540310f0380d001103118002114200c45041d8491044032600700080150b00020803e549548890070111343c2070360010072002419800a00f18421407a82c035801154151003504280002e00c0142e0551030f10941459a40e400c0c0381c001c002c019921040c0c07500c0000d001c004203020510004d03060340c11030300600400d0030840d901c42400914400f00541170b40403581540c1c00c00801d000f015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 508146025 1250 508144775 508144781
    0x924031d0718110d02131a180a06080f0406230117030a020622150e1006050d060b0f061908060a140d020406090e030a0e040c0203071e020a18 62
    0x4042d9003104200e203404141a40985125100111500715400100c4071010110030200802400120084140003616000c80b414507a110602c04a2940d500c2c010034135081c542007007d2801e5440940c0d410445807a522007000d4400000f0f082140c07a1a03c500701a817406940f03842029a449002406004552424a8035101347e115480c01030b8582d0001c00169030f040c0d40001c1c1e80c82d00104003442d8540c08079202001c45490940d0309000404104a08240404030b4255800c51401040c2043c15215001141e02000040303482521900b0b4000307100c641c04030086a8554080e858440700a03100311249412000000e185034030000c0125441c41d04c0014203522180c0c80f0740c6641d844003050f660411303460f0030f1076140082c80c0120700303000d44a40140140d407021900c99402503401490920802d20228401e03d403126181d030460201c88000801005844031503140078003031368507540101e80203103150a0703140d1518042c800949840d0416644800346140042c5ca81300d03900402000c4001c0d42d0070f040f048240300300f800c1e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 508147275 1250 508146025 508146059
    0x2100b030106060206071224090e150705090402160501050405060a050105060403061d060103140d0e06040504020a02030f0d0510080a050d0509030708030403050f0d0924031d07 77
    0x340e02d400000d0180d6900040c0301e0f50003036464103004483c951000400c4002c1c02c80100c4001d41c08400e440c0300310310142e050030340400381c4414081c10f01228498000240e0b40b103a1000c05442040084800325402c140144000d0078200d0000d040540740005011170760051003c200e20480c0d4070382d949c80c10401840014440e95410007144401800a035241600240c0341d4095404042e242c2a1345000200c0070940300700540101c0708510090303e503030390f0b540d00302111100e01e0b50110304010700031920318881d401d119041c0b40e030618000500c0ca600745400d20781840001e4004c00f01c04030940c44100080b00c24004514090000424003030030120b514a003210911070740c421150312452907a80514200000a403011814040080107440c0007501c409407070002030315241040d40804564000001c0120520002092403060040003030220742c07042150b801c0840c2d42c02c1440c403580240c82000f42030075081400c40746040654110724907012401c01462482c0c04004d400c10303071090100c1e41c00401d0800c076607948880c032401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 508148525 1250 508147275 508147279
    0x601030c03210f1206030f030c0303050108120304060e0a0503030a06050a051005120a1b170619060e040212010e040b0c030709030308180f060f06061e070f060c02100b 73
    0x2108642c0e180e015140d4004008007100340850852000240c2038694819002103401c00c0028000190b5418080c03d000e2440b14181c00003400c1c42c0000c1654100000d4034207000c44044401c52640e541d42e210040100304040030710602d4000c294007030001c6002000558040d10007500001205443d080422040c120140d20484c00348440002c240c240a4002c020383c0c046604c0c4805c2c03000c15542d20703c4480300424840400682c10010070000144207a40044d0b900481798254202d200c1c10f44079042081000800f4070b00014841c0000c0c0c00c1030100c00e1080c0500300220801420241c1803c009003003c092058003600008410320500301040148800c00c82003c1d080210301c1149031644c14042001441074241d40800381c00d10403d203020403205040f2982d815104849101030f1a03218042c03040a0361650400c0c1c2d0860049648400490324a1407d84110f40b40700031400000c404a00b01c0f0221034013140c01c0300c02c060f5070307030b201401d01e42001c07845c00d0050f01a82c0005038060005005501042000c07076520b224068 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 508149775 1250 508148525 508148573
    0xc0c12032a031812090402090f04061e050f0a050d05010b06160b130b0a09050703020607060b18060d141e010f0f050f04020103090f060e0a1403031009020c030c0601030c03 75
    0x4c03443d000d030404a13188038600703480143c1da5070190400300e5030003004100a550003e14003100005c0441082d40071940d07103141d424603043c406a90f0301c1040b03151200080f0059104403840810806841c1174064080e54901c60000030900301c107081c0c0000d190344c010218408009441044040411110001c0d0b20390041c9002c2d100304000d5629250422011001030240303030003503a200d1251040c48000c000f42d13030081d507004041e542da42c062458220040c244020103240200101144030010b105c2c04501320388501d0000e0944d44a4800548610b003410314000790100300742c000c80c000704400c8001c6200d81d50a0401507000800c0740f1030103101003002c03503100d08441c01e9440d28001c00c0c03151100825104542081c2c0900c0d0100d00d4108a09004070f2643e18420020045031914102007030003903012400b0317a4081d001c0e4041042c0c8205450741603841e40b0040301c060348030a5000d0400d0042000c258081d0849911710350841c0d0400100c2d040c03080c035101080c0c200351420322046c0010010401c0d000d1559000e01c120308004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 508151025 1250 508149775 508149793
    0xc0903141501082b0504050405010f05040506060408030d02090a180e192001091707060e0108040f031d060703090833040312020304080d050c0c12032a0318 68
    0x40203c0d0100303580c000c0c2040300c1903484485540c4c405c40a4502408004008200f2355a5070f01854042002e184590b501990038400000d9292030490265030840c0c00000c06580b0384070705d4482c0100254002140741c1d600c62002c5001142c1849070448040c0e0340b50a295000504003800c503d054644048a150a18004004461440003417101c54544000d250f0070307007022031040c1407070f00103880c1d0711142d41000106500b03c1c100d1103252000010303088111011a200d1440b00b02a040044981d4071080714054500d40f14005e4100c0040d01c114002514032043c9094442c2080c00e200c00185554010042500014003440081c04100c0080c802606040d4800203202c946001c12050305116140540d801c0541c451503c0010781403501403040542c1c42c0c0407030340d4119940c1c905860a480a034100a01044010380703408009466410504110b031041401d82000745550940510f0b41c2c150b5500c001d180c151744144c01190038010072049524180c180c00202c3d80681c40c0e1601a06402240c08000041d41180e44140c00d8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 508152275 1250 508151025 508151053
    0x9060606040513180302070e010f0b040b070c080f0c0306090c0d12110109080403150509190501020f121f0f0b0702120607090504062301030c090314150108 68
    0x4071411070740d00f40c82088580e038002c03c880d0300828540c008000c900f4074405083d01010760101e107480a80341e03181400d080503600da82c0100c2a4803850b0140d00407540d000c000900c80c5542d03c00281848078850102103414540701d98885040001f071103141407a0350b102102480280c98107100855210326050010001180301c203000904400403070b000030380440300c6400b000c0384440c801c140e00726200b140400203000c00c07007240c40c0c41c84480d4404d02c0190341e0807040140c100000042d40c00360600544044004000c107404084021060515405c03040302c06650130041c044107519598041c00d248803101440d440249400b04101c6612000340c0c094100301c50f0350003410300500c10f4520b0020300382c3c0c188a61807611151a8400315040541c0407442c450075106080400c098681c3c807000300400c0d6201500c0600c400750b40c60880d00100a88424101d42c402d00040900d40154030a520114012585140000c08035036682c1300c010f18214140b420700c0840c3c00481c44031000d4220b005400b4010402600141440c0002c000c1e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 508153525 1250 508152275 508152277
    0xa0b0d11071a0405070f06050315060717030c1c0b030715050a2a2001030b0609040924090227191d01051b120a27050303070809060606 59
    0x1142410b41d01e000c80c041018000304020001c09066010300e1641c8058440d0005415a00200c1d9101f10007420003c066a2508041c425103040541c4000c581121007a42d185d00398141d04014441d501e4241c05000d0000030125140c400134444803100c000281041c1408141403d0141d076030000311002c0302c80b801d4181c005910408440c1080321380d03d007004130042c80b000c061070220b10581c0c030484055406400f1030203021a400280c40000c4050b0300028001076074100650545500307400c441c0d4404010300074401a41040d4120b500221700c5000d0b1250036403030100741415025809104100b4540d0780704102e4045042103440605000412081504001400e10700040700800041070010030005010842041c0d5906402904100c142c0b00c0741e100309000c40700c4000d0b0003800101ca1002d10540b0048000715603001180442e41c1101c0c12034180143c42d40c83c020180b01030242c81d00540c0540384076081980b803441d0480710000301c40d80f0400c0510f0340d03401d0150340140021800703854003207243c000c00f040c0300607561060 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 508154775 1250 508153525 508153553
    0xd020403060e33062e0e0108010b0a051b0d02030711010e060702060c012a020c1203250b2d09030d0e030408011416090501090306020d09020a0b0d1107 66
    0x18020032090354800004c9140400405419098030317940c400d4003100071850303540e160012031480d560300200c0b0449000444001d0710070311031803005040804c03c030380841748100010400c0d0b1913610003051011960b60f0031207142094044a1a0060b000845d0003170800443e540c040781541400d113089407202e40a9000608188958000241708070000540070407541000c8d00a0103280001040030f020050f15501000b042c41c258000540041c0561010b0424a1030729100e4540c1481c0d40c40015420041090545c500040b841d070702604c07a00c4c00100054000503900010f0707502c41c045005c03c940a1501d000000440541112a00990048074000b085184440002680e080c40024240425820071652015003035115036002030b5440d500307081c84100740e103004085050013903011608600312520300b000e044030100e01900a44d40003c401080c02c0022801c550094014030740f42d44c100040349082d950009072000900d6001d466010408603458005050b944074aa00c10311240380c01c1403034055503955a1144030104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 508156025 1250 508154775 508154863
    0x102304080d1115041104060801090c0306180c06050a0f301401030b060906090405060c0f0c030d0b0102010e01090807020424090e1c020a020d03050d020403060e 70
    0x301400d4100520422160010f40c03050220800f0f6410b140c1041c0c912000005a954000e9040100019a901c014404d00c881240c00801260b8a40c0c02c642e41c0300007170111a02c100301e05a90340640d840208208c101258002c05064a810365aa6407048016100480020284050100c407900300020225400300004014070800050050170b2068040a00240008036040900741d204100110400828011040c002e400859940b0650303903940041102c106402c5400505603000100481d41e88544007000e031120000d61414107080840c540070103440c60308a5100040004d031074503441407440d602842007507000d002820091194540540764010300e071061080007070107140c7d50000303901e90a1040d100954540b580a0308400e41903541e4a0210190a4211001c0028090641e1007000c001001050b01840802c0f6000303050781107015000c021901c0401002074092150401c0300039031a00a51000340040c610030340c80001e04400402e0533a1a000e10540203510700c01c0c44a0303c40d001205480c406900140907 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 508157275 1250 508156025 508156037
    0xe2b0905010c140f0a03031e0513030507151803090504050c12060d0507180f06030201090504090f061506020708010c081b07060501031518200102010902102304080d 72
    0x2480d508130b107800d07006040040075000e00b80201d0205079240e008603550138a61200d00c0d2140d500b0800c000102d5205641e0403c0740c081408a4000003400780340034261700740c000ca04401900c912880c041c0d09440c0034084e00703100900151100d00405070850b08800191405650412140c6001c40b41580c1c2c501c200c40c01e40500b6190900040c51a40ea510843c10005501c030080e560210b030340742c20003945a480007a0f0303002407504140460401070f40c14410201242d070140d54425842d4a44000e220052400910136138141301c1c40e0543d00b011547c0350094080c910840b100d400c0c01d03e0b103005002400c14405400c01480c07039050801c0c3d9280b0940c841c1c032582c0c111402c1c0c0c0c00c60310047e00080c00c0c401c40c0e214643c0024043d509100000051100341165100180103810b011311041d0529004245111206400100712184200c038100c40c01020a41c00c4e10350804c107000000d581812034002a008049410102c80011680c2d02201d261320001c2001c002070500f01c0042d82d003000c0c02c05040c580c0310f6039400a41010040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 508158525 1250 508157275 508157303
    0x8010e060709052b03020106061b030c02010c06021b030d0b01030203010f03080c070e1003031707021509150108030309010e0d020c10050d0f0c08130b06090702010e2b0905010c 77
    0x3820300100c1d44441034034000103034139114900c1d02902030005440b5010114414070402100340c07405101d13482581d541345d03a0340030314090030750300550307412418040940e4415401c0c88443d4a03005001c04000700204104015034441080045d000181c07504190b54504050042c00104a12454804808240d03070b8001001034440100b281514900f07042544030b0071000d44e00500f13000125072007000381002c2e6402641c41034030402012070a484443c50541d480310040c2e0046c4103404085501c203800310341012038141660320503c0c283c00c600c12000800e03000620650800414401c440609100b51200c0290300400740200b680d2010b00a92140680380351b05008443d41c40c8882120352062044030002901e0450400a6405004482004142080c0e0a0001c56031150105203d0310101321600380c1c841c0e000c58101120740c0d41c401485140d0034050901000e664961000030070f0010280150f60403250035483d12030601b0344802500552100000701002800089072003841181d80c03094000341100e07009200c401c000c030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 508159775 1250 508158525 508158559
    0xb0906040e0a02030327040c020c12010b061c060906030f060f0f05070237060f06030b01030b0a05060d0809103e06100302190504050a050108010e06070905 68
    0x600240e200a42c5400000346c3c0440c0201c040f6006442560050125402c05400344280001c0b01c515001c2e031400342c0d001c0456022a0b141000212600c50404030002c51101d07046000b198843e00404041d034803c40c4035140d40060510035100300401000301103000d100d01480c685030524204116040a8502512040614140c0520340c0155100c5002000c04100d1841c00010081d221400c00d103424140003100814292083c81c05c4103021854240011003c9014a1943c0c48200401510380b6010304a5124200000452130702100035000358011002c1240524026407030404650000709118800c40703107144c00502281141096038640f1900791001411030352001800d54060302d02540c2190010503210140c18050b0b002c02c42c00c0380c0c1d02071040300252460729100342d49031030700004c54003000350900799030040000d460300705205c084180822000a80c0d00c0e4541e8082410765034201d0300010520b4507080100310481c424810304e0083c1903550040d05040c01c0800c40100410250700c10b1501c0343c0802540b0418030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 508161025 1250 508159775 508159783
    0x1906080106050a05090303030c0d140615071b090b270117010b0a080c12070308030f04081207020c010e010314061002012403030f0c0b0a020d090203031602090105040b0906040e 77
    0x5104c0081c07c4a4a80c5130025900f1010340c848580702400700d0138286170b01010175103c0c0c0b00c2400b44400034071010440c10b03d2001c007006504080415030b61a170000d0340040342d8070403800821028010701034010450b10001014403c960f0b4500300b00600c0101c40117101c030134041c20040600d06490304260300b00090307c00e1548280c098174202006a910039514080040e9030140000c01d03150301e540039544034031080c40e0b2500180d203620a40c407000c1c241c01010400070b0b20351044044080e511038840e0000906000580c508100c20030012100e10b00980d01c000750004840d86c0008050200c2e0809107014800d100c412a12000b0310a406030403075005081c448528040c07035000303420614091465404190030f031300001d90a01ca05507071620080d00482c002c0410468481c1c850f00030b800b10250090f0100b5843d0700e440200700300a40c0500c86000c030003641c40140900596052000300f01134204904040d40c0501c2500400850311410780c4a81e102d280b1f00710044049031a241c0d02250b01c40d50440340000c2651a00000c2c60078 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 508162275 1250 508161025 508161037
    0x605070206190903030e03151602190c05090a0b060d0e0102040929012606031903021005070302040501170603030f040f0311010c0201050d180605090304051906080106050a05 76
    0x140c290703100d802030032a0381c00f01a8034200da00031780c1c8081501c642d000030700d501e9001d051010603903440d28000244690315141041d050428640c4100d911500340001d82030044040b245003114410722101d0308102a207003180b0699002860b210742004408901d40000382c2500c2486001540d0360345071404000800000e60680c0d00401c1d41407018440c0a05003c40c90224401d0b2900385851070303400d406410340a520582e80305c0c00c44118840f55403d9a00c00801100b190040203001d00c0d03052080c2c84030740b0607a041e010b8448203114441e8004040e5101801d8941c03050b50001007540d4209481800204850380e800b0407402c6480c035100c04134000b0340e2105c0707001c681144240b12a2007207000d40000e00051001c0c2e400607802c02c40b8003584100e00d600e118000111801a1031640290015405200b490075010703081d44154406401c1148084030f0150907a1480c00ba682c080720f54204c107810200c1c00300500c0c00c2c100602c0031000385000301e145200c0d0501c0c102070990b40060040d43c003004000300d03821a00300e00400403950 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 508163525 1250 508162275 508162297
    0x120915120e120a120501080a0312090204110315040504050309010c061803020c010207080111120601020a02100e04060602030313060e0a0f0c0311010305040506010306050a020d05180c030609070605070206 89
    0x1c0c0d02c410010705441c990301100030500040c44004403881580410b21805d41a664040098680501d25482c22207029280c0121102203a070307120343c1d0070010383d075900c81e54080034081c0482c5a00ca02c1c100390b03200128003488400c94002c5040004220002c0c0700801103c05030442401c102d101d0004c58240302c0b00401c49080d0300303c40310240b8110203090640002d102c001c001000d030b086680280d16148032f10f09071400d1f40071503400d80606100c0380c2c004d0140d5400e032030b90114041c81100c6080465800290951985000360001b0a0030002c5591031803e2501401000d454140021440d50070031022030517220b803451401600c803a030343d82100a86481d080c4650003603250003050302e141c880503d081c1301444a84911040310114131010340d210a41d40a405028461034000d4043c0c24607030b103140c440354050000100310401c1705a080010207001e0700345200701c5000e42d0055182c000c0391810303071024a01d000c1c10b1440482c800d90286040000b0700e0700005254050b100c41d442e0194881c042840810410301038181544 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 508164775 1250 508163525 508163533
    0xc0c081b010501030b06030d020d082d040b060301290603042108070306060921172206113a051305060406021011130e0103120915120e 59
    0x18400c42c01ca94034043c0b2804c07411b40c0e2420301428400c1c1c1cae40d18101c1010901007908400026900401409040b540d900246102c0e00c07080c10405c141041e618046030b04440c019030480520000d8102403194801c1c4c0708140045524544501180d200300c0510f030320340203100d110000f00007001c004003110900f0800d20010a17841140b029a600580741c23140840350580064580100051100e2243c15800b0482d59040055036a240181c640701628042004080e6403400d901205282c48641110040510303040440f0400000c0741c1080180020103034947c0301004001101444c2000d4010214040610383c4d503004000c5058280481d4607840d00c8080b20082d009413a4000c00c0380840d580200040c5008d800d04001c880881d030b107074801c000b02c0c2c0c003d9008642c0143d0283c02c040c10070131001e80c0070102d0314901001050502e180c1210080302c0c0141a040048000100c0707004104021042c4031400300761400b414a5070071ba60800d03142c1d07034240454a012000300207800f9011854182e095108003200ca285805803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 508166025 1250 508164775 508164779
    0xf01120e1c080405010b0901060c0308042102070503010b180105120c060a03020408061f0b0d0f060306090b0f0c030c162310020421020604180b090a0c0c081b010501 72
    0x2034101c0034103d805480035420408440000d16141c45018180c501036115131100307480715241243d0452000f04121211800f2610080769146054403000041806a005240b41c03410038080c1400c0d2000da215081c09a186604580d45210503400ca1354196032003610480c010400c29039005142140c01d20240743c000400050201840c0d90680080042c0c3d2048812140a80c4a103400014803030540c12402e0681450f0003c1400592601001040b890960b020701040643c14804882d044a2841e03004454150340c500234001088841c010301a48103070070040404207494154800d15142c03000034104040c40b080000c0045888050502d8008402c3d0050300801105c00f80303045020202000b8042040e082c442c840c80e800c103000c6d047c002c440644410000503502b10451001134a51103918038001c0381d01c07036010300c400302c1c510800720079024040c0c2c51848041a041c00240c1441048440500700407005401c1c5441c1c000069005510580074640c0051015542c0d14034803020003502e8100745910005500f0070b000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 508167275 1250 508166025 508166027
    0x31202040b12060306090c19210b06090403020c0d0204061d180c01120c0507020316061b05030304200604090609050f10150c150e0c0f01120e1c 63
    0x500074a40050b03032000c1058840c0c804040e6507601c122031407009a4410740015086d41007410304404ea600c030300300e201d10a96031100c22480b10f40503000c00c40c2d030070b0b581b401c0d07603110604c506044895004134003514800d0407030900f618004d4589005c1c007202401108484002c00840d00c2c2c0354400700040406881032000040c0104040c4000d0b0415619566607031089648031100920100b41c142500d1300584819001d0301280080c20083d044024074082805020b00c04a40541c4083c030010485039902c10031105161704025029000d0f190802c04c1490401491136032400140000085a81058122045020843c0c03070861418075046408052a0405000f04002449100036040031045d240070315001c5c0700c9030782d868002d41c82030401181c0490012159a5080020000d8030b0160b444071811841c00b03840039002034489070715041c010001d6030703101940c0701d039a6a003500050004401204085840c40d8050030b0070b400003020500d02410780c4010650b0781e103240701c0320401044040d0301c010181400b025602c0d40988 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 508168525 1250 508167275 508167277
    0x309030f031603050105010302040b041703040e04080a091a0703080a0e0304080309030c0409020a05010c05010b030106060e0108160e011d09010806071e09090c0e091609081513031202040b 82
    0x680b000c2070410001040ca980240280c41c1507403100d80240d4186890160b2117601c0c00d003081e000300014041000081000030002c0e8401d88101c1c0240503440d81d40e0304001000b0030000107035015441d03440e440c54000035160504da0490341815011300c0c03e07200c1611181081030003041427400508051100107000070b070000010019054280d002c90079500040c0c09841030100380c5040b907100a5210002c0c1500380110760144070b8440c10907004100014035189520003007801c5034070075008403000c40c0b032540301c4001c2507030700c200d000790b0046c1e0f2180039008050140501800820805004505003c0d40500c2096013031010703100040a504018540085569900c0d5141c0d1204e00a45220f0300254030940044850001c00b10341c01220f403203a6540e0b070309003840e000c400401002008507240800100340d1142509640e580d400b680186480e0306018048409100b024005554980c00f00889801103c0d00788041c14054500b203502440300102d0100807125480c0c1110040a21032103804190300c00304000c507840311800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 508169775 1250 508168525 508168561
    0x272102280906050105030903040302060c03131404050903090f040c1106040614100e0406051e0727051c0624080111162d060f0f110f0309030f03 63
    0x600402c001034a5500440b250b12046807a50130b5039104000400050401c10020a100000b510580f400c280840c20418801c030340e25032105105509186486003949490310803140c200319070710300441c13800c949a00451450051040074520860392100d4400f00607015100c0c0390601c0c0e14010540c2c60380e00e414600480201102d1a0071001a001c0d040040d10202c80d0030184000d6503407a0a041d0703405c0d030301d540d500009050020041040c10040045a00121051314405030241805440d9843c00e0641030034112400556601200d9100f041d900040019450719018032146002c0444509a04422418650040d05542c0314981004450004141b0207121000100080d0b401a82c001c2c846501400350000b00c80c02011640c410415070903181500040301c2c541a130184c0102c40343c91401203a4040c444888001c15880107460660325010b0b003410505080c440d0384c0c0c001ca01101c3c1003040b82c04008800701280503a803064850320340b0000100b6905c483c00c000707032920412641c0309240d8920b040b4a0f20100380c4244 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 508171025 1250 508169775 508169789
    0xa15090c021c181e0302040603050a0203012f0d1103010f030b0c0703050306010c050a0501020408030a08180c100306030b0709080f060603060606070c09090327210228 73
    0xd0440b280810340314407010100d07018040800d0003001e040410000c4401d080700c90042c000e804030b400010042e1158040c000056005002038082503865005150a580c0c50b800c500e62a144044962614516a0420030b030f8000e081d0825161104465171580d0010f201c01a06203d13150008000094001d41c8071990005480c441c2d0242d00781a00c406202c114a4082d0741c8008000c581d007030001940325446600880041070080089815842e1540c4545003240e1003a04860020f400028038584046e400c40d005139004400d02000c880c1a403840d10b00f00342c880c1007001c08644a191103d0b01e001d00380380b294004401558001d80c145c515805d1802028290140c10f201c0c0354814000c081e404882c0c01c0307010510318402d181c0035019080c10760b914010007000b54010003045888000143e0080390a4545205004150b4031913140d4001165140c0c5442c0e441c3d000d500380642c9409803a19007440080c40102802295810000450b48015814400200000788059a0b2611645d013600c0818075450300b17074a032400300e43d21 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 508172275 1250 508171025 508171063
    0x13090b090d050f0301030f1506030b07020c1909020306060d0608070e070e01021b120f0a1707050307170910080604050702013315020a03020105060a030b0a15090c02 72
    0x1020034142e07101d000e051000d0390411410f1004101198140d071201e240d8905c155043c82008642110100807240d142e0230a480c0101e10404005030190100031030001d16000310340883d0082e0f00d400c1c020f4951050380c00781d0950260007002250103500d411054851086802c60305111068a0f0651140e40d041d1034861018180080e1002c103889602400c00079152040680c05000c3c00a80d621540400102e5144503c2d04108107070400e5012540600c48004060b5070031028003155800c0d800c10514689080c0021201a0410000b800020760008200c6400586c010850102d20040c407c1008150048401854002001c603000da9130366680106050300c0303a2000c031010042c0351980442242240c8181c2e40041c80d80a003458220365440c84928016010f00d00300b6030742031425469440800b25034a00d0b4120001590020301c0c281304040c0c080c065250b0004041e50041d01d850302c2d40d20781c2003d80d03101501d1040c06984c0d40900040c14011501341c5030203080710f1841404003001c8040e0080d0b88450542e078808411907 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 508173525 1250 508172275 508172293
    0x4120203090a091a0f090f041b031b0e07020303070809030d050c07140c0310020711040e0304060908210702191d0f06010c0825080309011803050a0e13090b09 69
    0x262818017042400d0028061900541e24280c042d40d458802074401c3c2c0e00c0d0507595440171069015000c410020b98443c450b41d802015660360b4080881c00c0307170341000602058850802220b0390340041641d0384110b0138507004403181c0391640799905520503071010080a6003408100300c40404403000038503007184a00608840c0715008035040791103608129000c0e5040e0408940780410321015005000c1441c058203241e44041c000500240444411401c03085540d000800c04101d41a00218620010280d0350080c3c0004503550003581200040310300360800001c004150304055403241d007070300000c00e01c2c1808040406600c407415180909140c040480c06d0f0011140010410036680d980b0600404042c1c40d40c44003c0c0b2a5031790030400d82c00008410000c00785201c0900740090380529a03105642c000e8031900e5a0707040c0550501c2c03d407010410789001c00c1c42d00701ca0400010b6409002c0b6075a0a629107001529420b070078000132071102c40705816091541c14203102c0740c103021800e043c00c4d005114080480d01081 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 508174775 1250 508173525 508173529
    0x1d0a1b03051209030c030f03040b0d0608060403020606100203070210050313060606020609070506090d02090c07170306040f1406040e010e251a1c060b0307090e0108070b0304120203090a091a 83
    0x841f400d0076001c240e0001d1104200541c04100a44204d400180c0042402500c400351103281c1801140c003600107a1000d01440141d0403d00541907003a007451000e14a00b00c041c0d00031903440d03084048514100000040040e4142c2e400b17210200115074414814002c50350740b01002035840c00c040c1c4038503846010b0582c00103040d10300324044500340b9001a00c801c9071001203400308a00118028100008500c0401c580c0d000500001c0d811100001d185542540b01d041c03800a002c12950080c04000d9070511f000c1c179140400c4071210005a0100e0115008621400c3c14101c41c0c0c09004143c0c100b80580c0b090f40ca641070309000c09080c140141c0821708a481e0202d9441c030521a410450a64198903a00100f0a500f201c1441d642031a080b0781c1c3c00c6d000895502d40d101718140503075004039425400100880320038000002c031030300b40300c3c0140310b16401001c04070300b412440c001c0c520001c0c100800ca030544c40071609280703000344190b60b5210b000500c3c513240583d490488a002d003a0701030701c003203112001d2901c010142c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 508176025 1250 508174775 508174783
    0x105010e0a020c0735030a080c0304110f04020904060305070302130b0604090e240609010807050f06131a0d0b100507060f0609110903011d0a1b03051209030c03 70
    0x114808000038407106241c410710f07036510110407017083c403034121a1218055002400c00e01c52501e194038030085650b030340b04000013003024801411080c0302040803c18000803c20002842c4c604e0071f0101c8540400d6218500040c000f44905d4000c19005418a00c0c00018030078089406402c5074000d480039107581e580398144108413071418000e1580824288001d0040d90b909602049044040100f107840001c412070f14410324403c102c0340c640326005040c0070041e503800c207820030a0060020400500d0418249000150904514100c15002d0f04002c1200100c14480c14086001401d890503060f0304000003c1c0c0001030b075800707840d4542109040034000840ca00342001000c003136008603540d460400c0130030360b100e002a02000703105805413600d419000c14209103d1142c0240c2c401c10036403a60795103108030107240c29204090320750382d1200ca08001c00c1a80c9040420b03c140c60a5002d200042c0c07080035000717803c4807800550005413162154019a88800450000900707112008504039448401d64200f0142d403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 508177275 1250 508176025 508176037
    0x6070c03020115030c0e3402150708181f1b17010501030903170a06180501140d03110f03070c050d031205190f09020411070c05010e150c0105010e0a02 66
    0x208264400204110080c41b1301454209416452601c201c030342d9450b00303c071402480031652204420000211007041d4040008480d0341c041c0856115052510000150401900400e101c881c40d01c1c0584e00f0000c03030814404600c00c280c4030b0542c3d030001303d0700c5903c1c48000c1100110b95004030b8007219801511500034040d0080c1b0519102c450cd20340d03070030100110050207040004805103d004030305814481000085148550400d04000441030324028021182541248a03604003524040040c081c6c44244e500541c1440d0341501c0f07401c0c056949190032101003c004204007414000c204040980440100007003040901601d0601d210300e03156010030030380c820894401400720303800c242014a414950340000b80e201d101d5864072020580d1006808040d9500742a510586a55510a440451a091041031801c0c800040000c0c10b11010387d9403803a0f20700b00740c010b09040c07281030105001030356903800c0c84980d4030900c010901d0701e0300b8030703d0510b070701030b210078002c21011a0015001400001c030510a0f150 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 508178525 1250 508177275 508177283
    0x7030b06010e0a0509330d0206160507090203010f0b0a020607030c030b0d1401060e0601120f2021072705031204150534020306070c0302011503 63
    0x5540e200d00005444600441c20100d4000e180c40ba4000303016900c500c0010720801181d11301d01e0b04401c000d5a03000c4159002c0c4444240281c1c8411440a9a180c81090000b819070550395a41d4400c0d4040400d45507004803500241a03126946002c9031102d03041d006141202c0441c40110001c03902d400e84a00180184401e560040e0f11200000d00524031a8002d00c024118900f000030701c0b070071550040b5148851190050324180103402d5255000c160034401c100c01801c02828140140c1419000242580d0303412114508a0780c031030300340306100405544403a40c0d28040c00d030701041620302da1041510381e4001e40384003411004041c40b1900c00d00c01019000d842041f80e40e452100b145406e40500c000d03505081466507569103142c0b004100c540301005007075a80c0980602c2c0c0c1d40c07074070f29109281c2d00c180400d5000108012040c00071070044bc4850300d07030388030644031101c125a19500c2c24001032400110100c01035030508c101c80c140090039801c002e403401207030f02941c000c2c0001c100b43d05020000b689907100c020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 508179775 1250 508178525 508178543
    0x40b0306011d03030a0315080111040317042301020d14030112080403060c020601081603080a030f091506050f0904080a0503041a01080c09060108070f0813052d0703 72
    0xa21541c459003980d2141001000040161199500802d286400c1000c05c0400b081c2e40d800039500d1724200840d80c13401049204000c0c03100c0051501c5001090045110080080342c0030301040c40220084000c3e86d001d408100100740890080c07404418500038000c15450160184c00d001b00803091154002c41c0307002c441c0707145591450340f80842c1c03c14980041da0302a13a0385078040c0404070010f403c80c00381c1031010010340c0c01800c10794101480f05040001102c107800c0106803400c000c00008000800f55045501d42d41000070b41d4010030f90300c043c040e09050130000c0c24400c24041c0c46284098550051098480c1612141c08a801030414002d00c0c0c40180d401030321190b0280922001b2602c07a100540e80a8450507410105955010104080140030f07049092107070001900141c55082900986a125109181800e610f00b0505406400c41c111000c02c4010000942c000611410440d80e03440120b541c4101190741d80100783d001101c04502c0154802c00074400c100880b0428000003400c1c10549400c00d2001c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 508181025 1250 508179775 508179781
    0x1103090a03180b0310050f01110604060c0e0d030903200a17070b070b0f0a0b09240307060305092e051e09010902010f090609031e06020f0a0311040b03 66
    0xe6800c180070700140b0b41120424031001c0352455008001d58000d840c880d1085417a18189400c000f03000f09601184c44c1004403d0302e0310150718400080b542d4000b130300600000317032131802030404450f000c8040303698540006030140540c0070541c0c030420303070800c0f0ba0088100044203d07881040d0340c030000321804060303807000705180c042c40650704004890700f80c00c10181c102c030190f076950058000c907030704000025203904c0040402c01c121030b0001e01ca21607000710341400412151a60a0025150a10140104131800000c1103c11080c0041c10740840c0b0419004048910080d0ba849009021741000c5907408410f0040a015034210300340f0160340151111110038109460074002800c030000c1500910312034111004801d80c44e4900440788045001d50300360301c00455001150b00002d4030000d10341c1640004c10008203010045564003652000940303500c40600d40c105560304112a04806e40050068070b101d100152000c20310b866070340104000300d802c0e02c0610005101e0845031404e4040c6201c1c401145d02d0400c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 508182275 1250 508181025 508181027
    0x121701170a0b0c09091f0807060c08070c05040216050c060a050715110f070302011d06010504020c0307020a06090f0f060e01031107050a0c05010e0609060703030b1206070f031103090a03 81
    0x2c40e8002050103065003009107075000100c01450554010369580000142c2c040c0c06056803145c900904030010003070040c580f41c000300130440703001c40c00090104d0401003500c404100040e181c00e0000c0500400c09e540b1440300ca0b03840040d00d00301d040120396910800054007103a040542c03d9941405080d1501414440c0545410b00c4000c01d540408c621aa6241e80c413600c4202500701426030045a00c040d10340b20030a07841c1c007908544010055480e41071410260900f01240099041d040d5a8280d0300540c48801601a462540c0203080c0000e40c40402c405010582d1036004410030121091070840e980c1842d546c0f041003010840b02e00440c0c000030459140d140055010b5084003e5040350541d02502d4003800c3d40b0f0703060402d03000510860340320b4840c030810006981d10020881e0b483c1c0e42100c0d1a45001d5042002580600c00c940008081c5929241c6845481c0d580704c0e0100400c011210a43c0c084d41340099008007054490304110b00480d2619203015150061074003079070700c10490741e002022281e0442e10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 508183525 1250 508182275 508182293
    0x5040b2e020f0304060c060b0303070c060e0301020f0c0105060307050d1203050c0d091a0703060803091905090f190c0f080a111225080c09030109121701170a 69
    0x9200c10340c030410b0403140c5000c80400c0200028110780d600c0310320f064500d103800d01c2a01d030070036503281c4a603006002400103e491400d041c002ca6086092403840f600f5481c0210340640a21108504d2913800829056032480301908800c0c032480c81101070714885a244c00c100041524140c8020b8600e010423a180c0d00d5150003030740f10580101c0854603690400e160701c000c203c240c0d0318180302114040e440c0b5100e80a81041400c140d508444181000e01555040c084c51660364015041b00ea0700c903102d642c1c10070317844505802e9800040c0c007014140ba051803508601542884000f50340585012000680c020440079080c850035410b000150349092607041c400204540c00d9a001e0094030103250350b41c1d024003503203040e0b00040140781c3d01690341010a1400c24103051803041c42c140700010071407240102c08041d0b40e2018440e5400395a0000607504c510306200801d0040c05400001822418281541c58240d504508440040c00c04114a001c0580e2070700580200041e407041c100000780d200703100c40070000303103442 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 508184775 1250 508183525 508183609
    0xc04030809040f180b010602030415141605060415020f041401020c0301050702010c1205070f1107030507030f15090519060902030105180d080c0901031119030605040b 73
    0x9001080098168654030202c41c0d050241c420385513070314100d80d0100619035a1041c0100518005181411b2800704685008929201071004215210010000c542841e40588003920071519101024003031502c0d00903a0b45500b510161a00d20384020701e03181c262020f0080315040750515000b00d0500780b401013864000c491004d0014158010a0041032644c0c50902c2582d01c00d0714140c0c00410308030309001000c0d1070302d8030b90084552202d08201c1080516078118081092410384c3c1d240520304421240728042c20400c498100501034060f090000051000e0020b5031024a8020316241c0c160714603280b0f00324200c2c3e004003c014030319007003600c0881d000c01c40b42680c0075007180200300224940000381d0001e405c686040311030040a0b40b01d40c500c000f10750001c014141045e2000d0a14403040c2c02c080f03043e5500c6000d031160340d0b410151902441d0100352150800e80da825114107400c000300040707080c4060043c002900449008501d0004840c1c064902907468142e160806c141d81945051941c1c0300b842d03070340f07950 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 508186025 1250 508184775 508184779
    0x1c352707090b03150c18091e070903050604120801060c0203070b0a09030f12020c011106040f06021207080103020f10050412140703050c0406050405041e06110409060e06010203030c04030809 83
    0x440611503d88104c1d8512540c20055200d550b010418054420741000103200f5000e40400010032060800c050505605900d94541035081540d61801c100c1d1002150b80008185018640c280820000d01e60b070081c0b4132004036154807660340c0e29000304840701c003800e0303002039810751141508009030b482d00300c000c1072000e10030302c1c00c1c00801d40c5a45034600f1702001424222512202202c0070f500c019414480300c1212039007442c0c404014001203c01031b0f0b81c6c0c90040c10203001d540c0108165030800c00c1c03542c1240e03440340801c000e040091401c1403019008040234031003680208141d00d035a050a150a07411040e105469854960501e800c0c940c12241040040b0703001c40c0c0340300100d121444245000c01c0003600130341c813900007032408070070340024001500c1c2c507a0311850250b41084e00784400280c22015004182d0030040440c4c0601440c0e0424101410480341c403134018600001d00032991340c403a50800d01c141c80061000d83c40f1500ca1600482c0c0c0da200c119108018000300f40401c0c000242441d004003c15000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 508187275 1250 508186025 508186033
    0x7031427030f070b03100f0317030a1404050f070e1e06030111040e0406060806010311060c0a0c080a05012304080d06050406091d1c352707090b03 64
    0x2c2c6540303003007100e420142d043c1c44040100404803203002d59080181100401d40d009440c515955860302c22900315807204114808800500850342507406004050800c0403401d03094100b41c00d00381d80700d01000003411000e0186520219417650b250ba900c0c1d00882610284031092807152100c540e06103c05080341e03030b0554032035601c48044841003026001400c44101074103010f040915005040760310980c000d07202504018010000329030820081440301105440351a992a60081030b28280480e21200070020001c030318002c20b001700e00244801006110740000c119150302648000d1403411906202120700b04403c00203400114070781e01620220202010110300f190310343c070001d03054820b160060303a105ca036680f04101c0340e558500c0c02080d515a4040240001045107401001d140300e01c49180003e0214100e42c20341c0c02e1540b4002c0d0400d0341c0c07001e03a000b50b18529035109142d070702a054a20802048440712007490720b4400c911b000640c81d2401004042451600120401400b0003600705641402 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 508188525 1250 508187275 508187293
    0x6060306220203100f14030705042d05090d051315050c01020a02031317060622062408010e0112080909090114090307020901090f09080a03020703142703 67
    0x1d4000386005200ea101d51407002c03814588044080c210503401004015031500c80811580c4010840f00d0a541d0103403808115403640792420004800100b4900341001d01c0203481d041e841065900060282c02c032403041d00d00c015100441203415008802820000d4801400d0030880e55000c180e0b14403506940c0e00306941000d01c030741d41c202e003203820030201000960000502c101c11008043d050f10040c04a039140040d003400c802022a5803018010404c5000d00219064a0345001014540354240d80d0034a400784481921241518129280702d0640c1105107010848140050702540000e4142d4509000508040c1e103070558200001114010a03140c07108104000d0b1151f40303880070007522401e032901c004078000e0709403c810f4503c104014524042138106000c10801a950684000e045410710307003010410080340d11650004000001e8020100c07200010418000b603015000352405a00a448204d00b650141d400400c503071041142c42d00c8118080c58100340d04050f003034000c406111000d011111002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 508189775 1250 508188525 508188589
    0xe150307140a0207050310060305030910030b06040311040b1c0b06010e1011060c030c0708091504031a0907050f1009080601080a061a0105190e180f0a0506060306 71
    0x26000c0300b000c0c401038200403024825410300b001400ea00740c1c5c0c84042000000e02e0360711601e48074020104480c0c49040e40d1021040c040e803083d00f200c460850000c20b05035580d030740d13454081009007c0c0306009004d00c1c02c02c04011050700c0d02482e2012010040c100043c2c2c603d0481d40e40110300c00c0001c200b1418460200d41d0180e241d1904021002c07030a685444842c900e448240100d40303410310040040d4001c03802001080034091174482500d400300d60040c10b01c1d46030034074440090f40701601241e0042d24000302140000c107000140c0031082003010320040b07040f191b460b8449299110405401a40c0d00505010003500d000e0424409507048a4040e103098030805481d600319908054003a488290154000304400301405a14440c09443d288030040703c03070340101c5290000e00f680c01840c1200c214008407042c00c0701414000d0300902030240000385080f0401082500c445805441500d81d0720001c1072040014913103042d140b2807a401094024102401e60f541e0f01c0411940454101c80124050f44600702c1c51101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 508191025 1250 508189775 508189777
    0xc050f0a05070b07030204030605060d03021f140f1605040312111005040506090c0f1011030f04030c380307020703060504120f081303030b0f130911010e15030714 71
    0x1481866801587e100d1031414924150b4030080c003041c3c0300780010705082d00020f400042034658024030290b0900007122061031000104204401442d041da0460b0400c0302c10040a032079181303d000c0a10b5000301c4800d8001c02100c450203180030080a585c2c0d542d003a4503619014195600b132045003802110140640c5080309400e0b03480540e0100ca85034410010701c40d010109011000001000351010081c94808100180c008540c8800107014040300071031541e401c603014022101d04081226285560700d03a2403504038160380080c0f28034001d18881400303c1034408a40100204c0120715000c15003403100d1001444800f40d40041c085005600c980940000020b1650040074840e074024201c00c00e408580f007401400e1842c1c09800c900c2080008000c1001d5600018504a40700d0781510340085d403400c203030020a040380b9800180f035a00400011105242d05050341040c022103110f0000e02e44440f07900c0005484004001805561111403040000c03030300328002020715404111880c14640c01e11180c0c001e0030b11 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 508192275 1250 508191025 508191031
    0x16020d020d0f051b0f1608010c0519110f061b041401031a03010c05070c061407260f031b040803160501091b03050c09060d03080403021c120f0c050f0a05070b 69
    0x10760815a146a441b4030192a11001004100c00074082c40c00b0b02035009042d445a10b1325620210040842c5180712803080340311700c90226003034080342e45080e106080e4580d1880101e450307100c03901541c000100600550760075241120501804400c00c040c030200103601401c9117010b420b4011000e42c0c1076034019902402140402c0034642c840559070a4103060520030700f40541c22650520a050445901042c1c0a40c221011343c1e4000c844100c0010750084402040343c034412013100703150070115911004d0f00d1211300841c000c50364040c0e0080d4445402c0c0300094940950701c10b08186800a0002d403148041e00c01c44020114400e000003d000b980035511b028110740c24102c000350800e07030142c043c010000304008440000720125885061031528400080804407030303100c01410418201c0106081500070089040c05503c03400100c54808140d0100411032221403480a82d0036040c40344107526000b00d0f208018903060b0319030301c80345030822071414409a0343c1301d034986800700701c400c0180e940412017401030240 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 508193525 1250 508192275 508192303
    0x50f030405152206050c1902031f020c070905070e0306010b0d020a020718020405031002030402090103150b0306090c100e0303030103081606060b121e01030b15060316020d020d0f051b 80
    0x21b190030001031158540000220036103105402224514003680c1c0004e01d9a04100200002003480c503040fa40c01d001070b01400b501480140b045510100c0d00c08103642055114072130695641d001c801a0104042e41c0d1b82e02807150110142082008013000b071901d80042c01141d942e401110304a9546014001940100000d003d071101e030302141c2441903141c00d100d0381e0440c000000d402e5080d4200381c1c002481d8464103120003401b2813102401c0390f8525200f90407843d02c00c8002020394882c2d00d480e601e01c030b40b40c3d0211012648101e140880440005010b02d000b42d100100c040c0003141940e08503a41e040b0282e22005a244002c61000c13a400c00184ca1401050042d00740e41160984501c02c0342104004136001600000481e010030001030010292807200301d044a411040e80c0341d00c0d07112080b0500f1004109000281c00010000400181184100c199401c0140c264202c50980508810883e201c0492052180c001071650100304030651041018009244032801c0c007840318041082c1051901d010203101d20 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 508194775 1250 508193525 508193527
    0x40e030a080f130f14010516090519030203030319051014120f0703080408120403030e01030506060f2a010c0906030b011e032f070b0c07050601060c050f03040515220605 74
    0x180b280300c003c7c0281c07900000e0501c841861204148009040a8054020315000d10140e03003018402d405520b4084004540150540ea983c1c01c14800f1b1708d0310711001c040320452507030610010030391440c4805a14001c440c11010b000035921140310420240c2100c5124928243c8100e01d5141d81c0d82c9424090440198841c0d842c9a6440d460909828105a003804a030303c52600d06100030800300b0f411034100070390540d003444c00050580c0c0d45000183c490189001103400c40d03130049110400c8254550100300076103007030841e00d21700c1d000c2c4140b0a4240d46118000d100042d13010070b404c1000c04d0094018119400d814180f415079400c0c0300c0c28001d490707840145031500090712440c040c0e0601069100c0070003c04440c0c241c410f03004440b0f2981d0155803048103002000c6041c0100014407a0b0304180070381303440340d500205490a1b9651084020915540d00c042035400b40903408148a450100208450884c1c0c0e028012902e0010b8445a4a409801251546010321103a818110418041004043c090314446c0c41d0300d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 508196025 1250 508194775 508194803
    0x14070b100f120311061603150f0609170604030e1509090408070b0601020c330a05040e070302090d02040902010c0605250c150510090c0c02040e030a080f130f 69
    0x1041d02c00e13950860780440d0032890902c454070300100d00180b00c0c4a040e042c04213141041c5400c04441108550140100c0303552020049032403540041c62000712164820715a05c0329810b070000d03640384d903c2600c1c000c0214121003000001c40c1401c07884400a4070024620505110f400404180c00700001c40d8104ca50034030001d0b800d020030140010b407a420103028401130125400c5100800c100e106100d00d404035944030104200d60900d6900352004903200130844164441e22420409001078002e40551b8100c180300030002804984a40f0903169a1007005083c2900e09605409010080030f102406a040000c4240c0c1e100c00b241190151a00800c44908035007040104000390360031014a000f0040c0030410800100c0000c1960440040c1c510001c80d980040c2d40c0d114009181007041199004030189420305040310701d61f5130000648240e4078029142880300201c0000010f88a00c034400365a808500d039440890074514050006a5100c010b00440558444003511010900c2010b860308449110041441d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 508197275 1250 508196025 508196027
    0x20032125111906050a050403020a060203091603050106030b0606070503090112180c0e1b0909060604081b030d03110a1404090e011e061d060406030c060806030c0114070b100f1203 78
    0x2e440d4000845e030020401402c0a41e0020348035103a251001c0c12039a004801701d42403180030300c058060b201d200e4022550640d924070702140608440d20080d16a010042d000400e0350410808035007005901c50301652a20b404040151120300604100202c400e50700d0160602200005007032074001c0b0b00480341785602c246001c9180c1400d040040030704114203245210742d841c0c0149070007a07810b618000c840112065484001040682c081c50b4411402441903800d200b007490801d1100400004c13003079054600000030b940d4143c0a17103890ba42d988403143c104001c201c0bd030798840d40007a0b16090241710160325050366038030b002c4290f07101440f0140d403c0c0d54566102a10180c2c140b902c0c07228280040050100764074052074186c8650181d100c1c820f5800b040c200044c0d05584951100c0040c41c0e001710680651500c1e01001410042d0485286000c1c2c0b0450000e40e01641c0101407102072075425074016403604540340c0d101494010301503e94030503800b00c00004100320020350010000b814110300707007036101486820 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 508198525 1250 508197275 508197281
    0x3010b01020304054515010e150a090305010f0b04060e06030312070e041a010206101a07031106130b0a020f0d090320032125111906 58
    0x9441819075000300010801511900c1d05640640100040b24841c102c0c51a40d803108462905001c414810701d10b0342c20380e80000c11201450140030101603000316030a4144c019140c0c5029081031540c08001069070788400710b1214002d01038681c0c00d01c0c242001e1640e99551500f52200c1d49036440199445051500590806100d800000e18010502401e20f09040011a840f407158800c0c002c0000c0418000441c85030040894010608002e0001c1000402c0740b501501c964070030318411401030140c0d4010410750a4611361030000d40b0b2500021710181c800251184103144c1c0803480031000e1042d007000204003490700b8090300d84140007100c0055811440ca1800d0052a0002403606501c184184501440030642009a03000b0911440001801482030304040d1020011105040000310b40f400c180c00b4185000300243c951501c040a20460043c0340c04020400324204543c007255000c0e104e45102c0c0300114003039040c0784140325424500b004e040340388026424200700d410703030100040d8030038940c3c010801c0501c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 508199775 1250 508198525 508198541
    0x1d0c070f020a090c0e09060a140607171c0b0a06110a05060c030a0e031804110c03130303110c01080c210906072c010e031c03090b070801030f1502120405010b0301 71
    0x41d221b0304580380200c0020400403017402920400c021650301c00c042921442c0403225070a420003c5012000e08900394480d8950001c03035061000000059128214100d070301510842c00801012820442c0c20001d0481c2d801d0120380d02a40d031440340c0064180818000d20144d800b83c80040c0c10240d0728039254007490300b52184c1c04980203155001308040e40708130090403030000002104680204880d4420048084c140c003500c1070355103842c000000c1d252645410b052000040341c4c802d84482c10320b0b004a40d192615400010046800710f40d14a0000c0d244015140041c03034103083c0c850700c06c8182d0444403c0402000d00c11120b905440d40300b00e0034450115003000000190002550b29440c83c0e2501c0a492284d04940f03600e40c60512a0808200540d66424030012440b140300b901d00680c1d10503940401400340c0404181981d515a181000c21006846010924181c0c2d07003009c2051a60030580d6216524021014525001035500380300a684c5100002d5001c0e01030780c0030348004102000428105400c448c415 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 508201025 1250 508199775 508199779
    0x9030f06010305030307270b031e060d15090b100608010f0f05040b04060e0a1d0703080f0703020106080601060507021008150103091b031a011d0c070f020a090c0e 71
    0x200100001100001105d1b4418024038020034001000200d000358007400200b5102c904400000c041041c502d2480954030444e07590000411401c0b6030207841034180c01c2500c400381c00c240300754584400701d8803c900c450203d9140c928002103540071500c801150034400d941084240d1624201082250f612014460141023800800c406640c98800070749007071f03600e620a284c0039544908a484007581c45900584c01010709500310585454042180402081041e101034004000c0150310a02c2082c001b07100010380b58001e002c0382c6891186503104000d6003002e4012401c56403114804910020103200c054004c05441d103078141c4070f400e40e104105100d100d030100d0310b04118000042000c00b440384480c1e9840750b0030a081c00641c880b401d0800c00648643e050045a4014035290000108180400b42440a245a03941c402641c4d0b00ca0790100c10b0b80c040101c2c1d22120310804008646c91414800080000d0340c460541644020141c0e80030400110042d440a050203545a0f000c584168125140e00f01e12001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 508202275 1250 508201025 508201033
    0xa060e0d022a041802030706110d0311040618080f1c08040b1f03080f03060f010216142706120703020108010b0304030513030f1506030b130305090d0809030f 69
    0x80c10b6800c015810180024502c40ea840d05001e064503080c50b070340e25250980140a441c1036a85804002d440c2c444035002e90741c118884d004c05507007050b21900c00c00a50f4005c20140925240c40c0c000210b480040488940c03108002c4480d0025200d4401c200c902c141c02c0000001d403820001100b080c6021040d03150680090040c40410040080c1e41102c42d82c2d407040d144e14031106103070300294955500d0111030700010944080007070700035035000f410f0f0f011318402c500032a141e000441b0403100480e181d04081034564844c000c0c0c1c00003070156030320001c0100700700200502000c40c2d808204205094034070004c01c04409000c10901841503504068500300c2c0e1164100008140035031459000034069641407003261341c60700c8040081004c02d88190200c03449086405e03c440901e54503800c01c00c841c848440b40c01c4a07403280d525000d200442040c0104000c42ea000050f03e50f80755110305030701021310a1400120100001042120125510703100f40c003207194000d0080603125003080c4141460140c0f4144070159541c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 508203525 1250 508202275 508202323
    0x318034003020609010809190308150102011103010b0702060708040b09180624130605041805012103110105010909060b06030402030a1e21020607090303020c01110a060e0d02 76
    0x20f84004903451000c00b0f02e440c41e020b60380e000b051410141607007003040c01e03a810a500c52040c07551001e82c940c0500c510380500c80032044424010781c00c0740c000b0031036a0601c0f08180010440e04d40b5500207002c00e10300161115141031080c1d6101041640f16801c090140503000c680c104144c100249217481c1034543d4038440351581401c0c00058540000c0901c0203100da291041f078008090003200940d9a00451111f907582c07490303107607803005d422a000b40c0a01d41820444405c2d5000103100341c0a514120303000869550441041c02d014401c1c41c145c03000c0d0030340a10040040f80035104e03c0c00d108560003022541c4001600350304c0c500d8004280c07880d005441c0c0c81203405205000160340d0100d8142c40580d07108401d100301c0d841c1010884803a4402d55000390443c11481000300311075003441603a05c0d002c9000c0c3e094868980d80c038401508c043e4420300000c1c0040e400300416581e554040d114603050344034100125406c0d41000e9039403500303403562040014255002000030655040e010844c40868404000551500380 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 508204775 1250 508203525 508203529
    0x6130813030c321c050304090b0306101a07051e010506100518010302091c0b0402010801050103140601050c19060b01021507080408070c080321010614031803400302 72
    0x3c5095000c0744900d14802d091200c119401540f1030811340c0c040c040c1d0362125a55205540180400d691103030203801041c0c0001c180105070740c6010155900d04050001039200c51900340d20139040a88200e4280c800c800301c406914801d10500c2610a5203070300003151614050081c0700e09801c4211b603540a0040030f0107040010300070348800c60200c40c800c0c6030050b150f480344800078507000d5850386603281c804010310f110f8040c020031052181c801c3d0b00030f80315440d8990b42e80b80110100c90380861503948464180002c0366840d81314400038040c01540034204d54160504080040040320009022200a951000b4100495805004100b0b49843c4a01405540c0c13802c2c103005444840700410040c0402000100d0400708003240c140f403c05441d00104480e214144101c0c00290040c0c1d090400418840c1a0000030380c00707118420100f4034800500c403d50541d1100032780403103180c1001240c210303d03000511559280c6503459050401c000060f400c8010300c054000020348260604041840c0c44030b02c1001c09001507 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 508206025 1250 508204775 508204859
    0x6090f0608160207030209040305030406060b040503060f0a0e0f030423031009020103090f0b101418040c0302090420010201150e0910020c010c030605100206130813030c 74
    0x200000000b800242c50180403810036106420081d4014461000e01050681c000040c41c13040d0b102c1c1400300706440c0c42d01100c01050045100c1c0030751503400350300050f540240103001150004400075003c9506503406070101e041ca602d5210149407548042410042c0600c424030b47d181384903842200040c03607039000b0003003074940800840c0c0803060354480346c054085912135071081008541095030481c41341d00c140b0344054003c00c1a208001c00c3c00381c6000200702c007140300c4003400b40c82500401c0e4a41c13000c020031400c28a03800042c0280c42000c0c40316400009604e80d408100c3c800e510441101d10200386c2c510800754500402611103046a241c075032a03220b850754880d0101c041d10012071012605540303025585240c4003001000c1c85180b4008203800952003015042010302503050b440601ca01c030f031110180862801c1502da40c00044e413088004c03c1030007901c1110006c84070300070100e030b614050890541085200980d03100701c4003503040c200d0401021611402015502080c000b2039003000300d01000084070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 508207275 1250 508206025 508206031
    0x5060f09040f0b091f0b0a080717070806220204060203070c0618030f15110d060b030415110412030804230a030806010507290c030412030b04020705011506090f0608 72
    0x140d0440100d0180303160882c0c17a860740041c48241c002c103543d814000c2c001032120900b0b90305080454469014117440e90546800c0343e11450882d0f5514015a64180411504804001104081031507030300304480307c110140001c0004d04800c1e00110303600c00080c80d2966441080d940b0071804c00104942020044540c110300e5000c07680c0212240a056405041151151903262160b20369140751402c0c400c00c0720b65070406400030000e4001e007081010742e101011051071000300d03401071140e115110307011030075a51940b094103c4100d0780300050905442e4110101d140c0442d10040d404075120108000c200302180440000e4451440200090030300505080d5030fa0b68000007004003402450703030008404c0c0c0d2050059400191308400b80034018044400c4900d0ba181000e00380c1d2241041c00c0000428150394002228081c17a4403401822040380000c40c102e0041c5011000c06034132a40810141c004a41c0900440342d024485804800700c503441c0a42c0540050011ba02070114a40303c213104120042d00b0080e81c03a4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 508208525 1250 508207275 508207291
    0x809030c070603230415060f0e0117010b10030f0c09060e010806121603050f01021908060d0206040b18030c0a0302090c0d0227011409130605060f09040f0b09 69
    0x14513915849601400c1001109583d03881642c041c10030062041101074482e074105035000800010761507000e07100f0a05824011109032090510041224621035040c0011000000000040e00c0700e02c00e0010703030a4902d410160000a403a21a1017001980381c1c801d1201500c01c50801c500c156190100260880c80070284c15414840001c1c0001c1650b00e441c568400450404000e66400c500783e018004041c0100f070000351264451020b501c0f28210b41442101c03050350450f101416003070300c440c40c216541e08000b400b0359084580100c0c9480140c40300c0020b04082c020555070542c46800039140059800040d0350348502c60340c04440440100d45900e150482525010f94001c040740d03030740900c1c120b0513104031203014180c2403002070f078a150400420074a62103080c07214004500c004020004603124003000a811102d00005c00c4040d50038600550f140d06001344588011883e9aa0340000075041c1e0018484030f40101c200080240b02440c0900c0385512202d02070100b00100080640030518981000304681 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 508209775 1250 508208525 508208531
    0x7121803030b0a2714070207050d150207030905031009170705010603171216120b0d021e010318230f100c080105010c050d030b01030e010906050103030809030c070603 73
    0x540ca640703505035030601400e0140c21410007814113900c81c04404806580100115117005000c01c549646000040e001c0e4031507a00820705d090038502080904918a001210540e0403200d14400c500844d0000d003421a0003503d0710002180b4000900d800c040506501f4030300540740c030040d07000041240b641c1c01c016204410740741e038540c111480c00900501841d000500030440b400d00031104410000010403802c0280b44007070400703888800448221446419420340481c1c1c89594590803200c0b40e0b4810b0b917000704020850f4071111055004076440104c00281203102403403074200c01200f940c16002e5484081b00704980501002d09540f9013410707080303490b00200807058072840503241040041055610403118082500c0e00005d1800804009000c040e209001081c280c2d000000d0f07641c000c400101180d90000040c06606490503400c0b00140000b001403410705648045000d05000c0c00d02c242e1150602c44d201c0040c46504508025251880c01403003509650700c1000088a101e0010440303000711180c1e41004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 508211025 1250 508209775 508209791
    0xa020915012a0602070b060312120402010c030c0209040303060807060c02010203040b0c0c1c020913050604230114010f121e17030705031501030c0212070512120712180303 75
    0x30b014421220400a00703018008030b50030050044244c9014000c900440484002e204140500521805141c404a02c0c4035040300010300554011405000c80502c203250403115240d03598001a60000b040d1010b40000e036841e40d05110511041000b030000c0c114508111a0910440e80001d54a01c5140101d6220220201c0c00d821111002c01102d80b803200c0060040d108500300402e0a11420081402a84281d8681000c5a0b0703c0d6810341740d0302a9150030402500b00342d540c0c0c1d02c0341c00041005100003109800d914000018aa10a220300036140e481c51131420741c65494460500b105e000c098005001300d50000e01740400245550008000b0b11401804e56117440c1d51724141030298408402107411f00800001c208019103078080c0065108403900d034032140007480204011412a2030180d01030003d80c1c031a41461046e507403940e02034602180f1840c00c40d070911422140005c03542c0c000100086020440300103009070303140c12100e2003400e04401d260410488803022041081040044000340505683c2c10603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 508212275 1250 508211025 508211087
    0xb09060d020d2f0301060c140a050118020f03030a0507031815120f060e150d06090302010506010f0c03080601140919090e01110415020f07080a02091501 67
    0x50764000742c4006800c205092520318110503e07004100101d503d421141d0b900080c0000040c1034a0503121555150031000c002c0c0d680344544001a90800c0c4014480c170b000910014000f4000c1625102550700d2400e807940191052107140c01c6514030180c840c0d0001c0c0150074a80da40007040d100219010b19004a0230411b1004410405c0c0f403d411080801c00700014140115401040b202d0801400520411082000807801801c40c1c105024070390072464824081a01c41c078082d01e41d14003000d401403151a1980d0140d48100448424180071000350b51503c04000b0301d50781040c2d4205400013541059403841c00030f13940042c00d500c00200460b062041d07108030f1100d0a100c007020754240e92805400101601307401050301c0240c0040e407041e520400c0c00c004080d1980b90341070064411038851441c1803400e240c203104030120754001034a0404110f200e0004049407000c0c0410600004258601c040c003408a07031030051104800c0000c00311803044580f41035100321070340d11103082581c401c0380b04403102c605550201 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 508213525 1250 508212275 508212277
    0x7020f0603130812070809010905070501050c120d09031106090715050405040905070911040b0702240a1d0f09070c1407080609070602010c02061302030106030c090b01030b0a0b09060d02 81
    0x503015000403c04035004103e82007031070782e0350302a0b805600d81030100c6e59060390041c2070301d1503075800030040e41285c0300030001c95006601900c0000202d0303040d2001e110f10211101520303000030701d10f100c80344d4590b14068103050704082c0041070b9a45207005800303a8945440310740e560300c2051161218000c281d40b0b400c207c2078403590030340d000713400b0044c4207200c0c072101070174a140e07102250701540d0340d07161400c00300280180340d20088804136001441d220741803100a400700a2010320800c07110309500d0648a40ca00c2000f1600d00520000c0c4032034542c0541c2100d165a4550101d0100c403489004c1c008041e02d4454595034009030341d0740041e0501e050300400e0050702c0e201d0011b03907141400380040d01c00da10000c1082000031407224031400080044560261b03803640e08a00f03a980f180b0040003d80c101e00085000c0b0120fa2940500b002e001600205810b0707030b41e030740c4c041484640d903119020710355545510940961741030090390716200d0100e0b500090a410084070505511544016a10680000410240a04040d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 508214775 1250 508213525 508213561
    0xf15090b0403020a0c06022410080a2405010f03060c021e070e0f0c0405060d0e100b010e0f01080c072904020a0b0307020606210a1b0b07020f0603 64
    0x12000c0300941018035000c0e5664110407421102c10120b6034000c140c05100003028000d0034070545483c504100c45514103503e8407000390829162509559020550407010044620b409105510b10024140448000000c1c00080d1030160300003400c0c5801041283d044082c0c02007543c0e04000c0018400000001c2270340342c07401c0d624100401541905040b10700340c3c00401c0e8002210a154a883c840b40c2e143c118058104104032090120300806110a001e40d040007000360140319010303980021001c80c0300030454501940c0001000b58151101155174407560322800290211600b80c40441001b441e4000103010070074010712008040401041903000d2011030003040c7c5e91581d80c44001c1d884003000600707400405808440590240869800002e510000e02044900c108215030181541d81c60b000100100070b90045003035030b41030b0035100e0087e04152043c0851464507209911000d089501d00585c2400061980d10941982d03009104820158880f80740e03009000608071411a581e45c0e52174a40c6844080304 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 508216025 1250 508214775 508214783
    0x2190602161505090f030306031b060d05010906090c02031c0f022104140604111302070503190f0302070f02060c0f0708030702090a0c02030a110c0d03021005070c0f1509 74
    0x80c052502c0d000c0c42eaa0085020304441c40958401c0a0340301c0015550b884252240d5805912982d80040d03001030350000881ca05500400b5580303004492100003069503030a810a19925950b02d0082080300c8182c411295409514006035003030012101710100350203200030204201c103031100e0b8890401d4231141d04945584d60050403203d041d485800c2503807036808003181c003210002584900350032450300000340035104542c0484c02c00310500802c0b09024002d00d50a0100101c41e40a201c69400070354140080d10b008400606413468a80d00400001d018800844000c820b1503c10040f0402003114008803c085540544455a9500d0038280d028604400d9045d408076038003600c0d070b0100e4103040100051803ea4002c81d8140040d46038441d004003210b18991600016a00030440000402d000307041c50601ea02c2038074182c031045480711000c0b0b84c0d4122000360840058020116010440d6100c0c4101078000310705152501060056580e00c10940030694000303001c024142c1034099600d1848e8000e4041d46030700c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 508217275 1250 508216025 508216043
    0x213051506040611120702030d0c050307061419020c07050402070c0807080a03111501030b1305120d11090a05190513090209090c13090f0227070219060216 68
    0x140da8001800710106441302c0503107002d01001c811540f2110401c0d01c2d40e19800502070403044800301820f0366403d99807103080f109404180710540101d00302c1e20403a4098000001e4101551400c00d54640d0090080c3d01e04507480303817052050540e060400038492041c0d0380266001a95511030307040115801d126948034201510405601103400c01300491040c0b0b00c14030944400c80b06401049025442d0860703040c0140490301e03404010000b044c4150101500441945400441120162251810080304040c2d140c0520fa00242c9880c40465610a203001e440c15506840c1c00d042400001501010161103410301c03482c0299081040038070080050030040c40010f20030010164010603840150441a4003684107003020701c00502c4100340481c141c90b6420000b4403280700c0700c42090080c2c000f07000d0f011043d074030303e071102d100440141c8848901443c0c15101c00051100080b0007980031940d40001407844d0704540001e00724440700c403850b075961a00190701c52409622006a0200c01070140e881ca103003c1c0c401d0003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 508218525 1250 508217275 508217279
    0xc0d1b05250c0f05150f1e0c06070f0e010c1e03050d060608060f09060315130506090124120803040614070e03060c0a210204120803060f010903021305150604 69
    0x12165a20000c0ba0001d665010340e055003c44510246e010321408035207900000c00500b00810000c00009426442a50300300741020307080960986005821a0a0030200e410303007140317071407442e000020b401401e4001d01e89480e5410040c0d481d01c0441900b070240340700c01c1a20032290020540190103036107a420500004103d02956075400500c241800d40c0c8090158030108080c4142d401c2010700e403403160303c0180080c001c2036a0344040d2142c0650091002007820f075040340030800a001806400c0c0960f806200108601100c80d000f071101c9008400402e10780d011200080040e400c02c2440d040c1c4190300680c01c10740341d6581c0d080050203410400d001d0114080c401c4100420250040000222060b0a40031201030b81d584c26081525440f684d0040000300e0402c140c2044051001c2003101c4a040c8075000150805070764050450840c100c2400450300c007580031080009900340000030786c5201c2424a0310926651a41d0003281c3c447ca502c1c0e40011482e07841c0c1c0d002510072014540d1100710001c000d02030541d01c075 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 508219775 1250 508218525 508218539
    0x90803040317060108071d061c021b010b03150408040e16030e070807050f031c0801080609010603080315030703081903140702070b07030909050c0d1b05250c 69
    0x74401002c4800d003902074080303880f55205080080c0700d03c0c0710340c5400d0341144e81400b01c80d010405084a20342e005004004181d80c0f000c40904c900c03414640300c8000740e190045070b00584451201c01074961002d0f80b411007031003800e60b03000488200c0702030000061401a1214201448184519004030403c1801542444108074080e4046034a06140e0359080000078140310003603851f500b40d0f00c5080f0300c039444284140018a08a00c500000c800c00400301c1e2400d1603091041c00f000910121440080742d64200101310744502032000359800181d01c0000c00095085540d001c0072800042c00c1503040d03500140d004407054408101810240d500031000e2515070b07000c5210035a50450000041c000a4100451402d5000c4480c01c400c1c0200c8841d009043c010f800c110040d403983e0031200080c0e00700000c81400080900051003028025540c0b40a40d940c2d40c222007600c007083d00c80621460150700054485880204e03801426600b03000f6044400104261b203c1c24084240207503c54060090521960000350007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 508221025 1250 508219775 508219787
    0x28060204060905130b01091509090c0801030213090b040312150b030a0f1407030c051b03041406130e0a290906060301180c051603110601050f03030414040908030403 72
    0x201d404071903034602c00e81c4048504085c1c0e03035000245070208141c00b005014041104040340358500305807421072a8540d9606003182a544884441d001007418400140294101261002d24a1720445000d200e0217a89668082c04000028000703010040a0310b103200d007900d425000b00c9500e00781d94007404481c1d070711074034460041c1e80255200e0140500d428021200c600903409440040c0f013843d01c94289a948034001940903041881840040010410100d40c1903a00380c5981c0d42403410203402162542d00340794040800311040e0079003c1c810402404031810040d042040e00c03040c3e80d41c840c0d604407241c4514a5078000703411b034950302d0f654403a1048001e102c0c001a20203a07110007002114011625100e04041c4003180c402030180405c0c2e034400105141404002d500140d440e00114640715240500d03540310700c48465a0f4a9046001a00c100d00040324a8400c101c0701d809000111882191003100000081e43c91082c1d100d01302e036041c14445001a40e070340d80d62102640c1c54006003071036600d00d800c0c80e0060070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 508222275 1250 508221025 508221029
    0xc060a14090a08041a1902030406031109130e010f0f0e06060a0303050a1b1703040b0105010f090504050a09020621010618050d1103100c081503280602040609 69
    0x1000100c00041040700001200514941c03c00241c07860319003403040e103008044440b10f030340d40c040c07100b08000000480c8262184c40c405d0107079030103542c40b41d0600380024155840600000c0e4809170520400f6a00c3c0d581c00100768510f0110400022121070b07070341c0f40f02d0140206201032001c049c0780c075103610b000284642020750080304100c16102d1a0303807802c0400c00d45d520207000190000784244452100c681c022a0000c5d0065107400c0c1281c24402140d507040e562800211201052030408800c4c0400c020744015641d002d413900b400c00e418071081c40304000340411103d101d07013441281c0b54030205503070341c465510a840160300513044070355407080300c0b03035424408100f56042e4454101c03400c000100c161058410702103c83e04018850308441c079000030000078940d0301009480c0b4030000300d61030540b543d0410151501c000f030024003040e4880d541d000540104002000304006140b403683e80142c5503400b05805945501c840813070368114103071040110802021100081809100003408a5030b25040107181c41 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 508223525 1250 508222275 508222301
    0x25030309330e0706050310081b01110633041109090a061212050d0c02070906060c0f03081906030312050604091a06010203160c030203060702060115050306060c060a 72
    0x1c0807514a120761022200160031030b6185401540082c803249101c1c000031504404036480040d441a121052103040c00000302c6013511568607440c0d4280e455811840070b401102110010f00b25902c4d00c03001c803900d05d000c0180c03c04041003582c01340c0b80070101d4035014407074400000b0304100b00d05400c86001d4202c507405508480c0c41039804500140c00310300c82d4000c400c00c3e00c544400442104149a4034250481c0035040381106018080c04500c450a20510800801010940c028071007940343c1440c01c02140c0d615002042040b003010382b604085229424503c10407a8546000f10751603444c2250b5252503680308a05903440790030f2917000000d02d5849140c40c0702c0c0c1e50003100f0821072622400e00300002c4505030f4000415101211030050826214060450ba0008044c01541d19003110310130320a0560b081c03103400300d4201c090f00f14240203600302040300d194449600d0006144a5051111b8147d204894443d01810480c00200150082c2c80784002d0b2058914080c0c21207505040014031400984040b4102d2a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 508224775 1250 508223525 508223603
    0x82101081533060918061201090201080609090f06100801050709150f0302040f180e0d080103170f0c011a0f0607030c020d080705030a0e0625030309 65
    0xa401d942c406a25079041c180714081012102546007030b10708203000c1d10111103a000800348500700060711410f100c20000300c80315040c0007136803409a08005e10364201000014003a85020b40b6000180d0308000e50b2a0045000c0b0b5642c1c0c00e0740c1d9000591031a00c2d1070810540520b0045030309010000c0300800804040c1c5032400002c1c8015516060111600b040310712907048404400e0601e102c0080c0100d1010300341d00101d10780503160940356105000a5405540502c1066007040b00084000703089100358820f45c100d503400340c819410112001010b942040c0409004004120200c2c5040d400c0c0030111202d6440b030140c5552034906511409008082102d5001d40489907485458014a480c81000138803410003000c0b81d040c600720352030440d22804a0901241c01c0b000c0c58080708049504007001d40601c502c01d40c0110fa40380300e4080014003503c140b07010a80214401e0040c600e14001030180203202c03258040c0b40038284545400c0071400b40100704800b83c501c8111241380780d96803403a519640c0448200400381 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 508226025 1250 508224775 508224781
    0x110f0f0c012a080411030d0f021203060906130207170301080607020d0203180307090e030c0706030b030d0302091f0e0a1712070f06020a05090901080610030821010815 73
    0x40c011074a0503181c50400b41d604501070445070780c090300d0515042400b516101841c3c003690004686015040c080c0840410390b003c212510003030b410015a5503107003602104600b1400d003900400c2c3e20800152181748140540a10f83c03100d0005a41500c0c166500800205201c40d1589581103c1d50b0003800344200902035900011011400080d00050200302c95000754030700200d0041d10b49480402d1403496525000f034020002c0c00742c05501402c1010364082f005507680b03060034540c541c41d107a540d51098017031504160b0340030690f80c0c01040055081500d030801503507401599000401055100f2083c1c9608a1640214012203500030301c21601e81c131003a508040641e03114540e81a40383d4596a1420080d4054040c900520340b01c80c000d0407030140300c2c0e00d4007104588995150016a04000c4c00b036000a080454481d509203444000e940c01819090054403060800c4a0402e142008502001d00985400202050100c100801c000c2038400d50740da0324a51561500c1c0d28603103a080d4005007031052072104001c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 508227275 1250 508226025 508226051
    0x91002010504150203100509090102190212070816080c010903121404021212180406050a1202011d0307060908010e071203231210140112110f0f0c01 65
    0x807140034030f0300f01051000250805400c08060b510090194810002244001910351603075204d1038094102c0c0c60001d40c40302c0360004440c07070440211a5100855100580c100207201003441140c8800390440e075070640e20302d1402843c80301a610702c14010b00c1c180300002c03034000d075040c10752000390131a101e5500c4141c40318a0201c2c03001580c09020b11203118039221004100140340004464039142c0c010b00c2625030085956180044030303008640a041c002c0c40300030a04800c1d07d09446500040c1c042150500c81d21418032689001c1c40a00840080c103004451b00e032070b5883c1807a0030a2001d80c0340c00a0449900303c2e00c0790300040900b0818460b50440b90300786840c14043c084082443c006560b9150810100d0484c161412030f5108a80d011070300034030b81c0c041c805541030303400c03030004000b0883c02e003005080c541486a403080500030694002082040b0a03403403150560391001d48040d806030001c4000c2507811402c0085001c91240f03071201c0201000006076441d20003000d074050619074a0ba01c000700155044c0f43c0b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 508228525 1250 508227275 508227281
    0xb100c170721020c1c140307080a08010f030819030f0614010e1806220501030b01030210020609031605010209040207060902090a0e070504090501020903060f0a4a0307030509100201 79
    0x6004d079210381c00040101c0c021800d40094051280605044010000f01c02d903854150b80c0400020b69400800140341080d640e00144040c0c010702030514100d180a01d10385a1003014041c2c0c24840c507014026440c1354003502c0c07094026500080000f00c04016803599401c9000700b01c03001880641c08034001c9103210304180760000c07a10300352807200c0d0404034041c4e480700c0130000001d90300d054022007002d44040d01d1000d11081c3c410540070318866010020b065046004100c000c40e41ca02c3c01ca001c56100346d0401031210b4012041c0d600c070350303070010850861811030b00d0a140607001c1d0b00c22658102d07101282c04401c4c405030b50070000303085000340c40c1820a91180c81d669400d80310344410b1241c0c035074040d4404100c46d082540c40358041c103004400060901030307400300090400300b095882c40b41031400e4200340b262a030b840388a00340c1c401070400603035007408031710089030300c0c40c142c6214014248220400c242c50400c0ca110400550345001201170340e030b55241a1a0241c441e40141d60828012180304052900b0f140c0144 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 508229775 1250 508228525 508228543
    0xb21070f0f0b0405040e07030f050a03032712110f010b0f0118050112110d0606030e0c2b12082205030904110c0109060506030d030b100c17072102 64
    0x21111441c0034108002e00010b0300c59004c050710346c0c0c0b05080001001c584c00315041852980b045000e0050045141002815269140103c0740140803052420000d44c10b074400c8a200a0341c0060740009054061b0b0054889a03d02c210300c00035801440400c040b01a01944840410318003140c1301c020301150140119001d240e044c4100a40e0314181006101c0707980180c03440c20b440400c005020548201584403072516401130100300340c0080c1c0b200f1040c130600d41c06005100111951600800d040031014000030354080b18250720090b00d81c41102400059004c0e2070025070860740114003c089009071410013000d00760120b48020003000c0716004081500280b282500820303400500941c24050300008001c02402805900c5c410a1420409080080d50a000d00240fa502420001a82d86480c4081c1070400e41c03c2070340a4201850038200c90704d140d85010404040043c1494078041e00ba0301854080740b01740c00c04900c1640170002045036800c001010700001c810449192080c4141c0540b50f80aa035030b03450403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 508231025 1250 508229775 508229789
    0x301150804050312090309101805010810050f0301020d0c09170d0f08130b09010603020f040e030301061b0203070308070327050d0602190903140613060b21070f0f 71
    0x400c042d000c020044c441c0203070411001d80c00e503481e1200000000300b20790003140b04600421007005403014401501d0019800600003800d001c4288e00d04010040c4d9200e02600605101e0700188d0410059514258181c1d003a0340c01c45a01000146201080601940c480e0b110300071182642109400d0280300105144069003034a444110803005108000c0c5c80c0c034200203118940f42090000503101090356480441c0c0501c052500000d070160841c014012034035900c4a82e14000d50800d449a1050f072400000c8a04640301c6240c444401e03c000450010115000790002e07504d0b1040e00808024130900d48000d210f0103102c3c0d1120034604040703004203910210b09980319030300950343e184104120b0070005032041c1503901c20680180780a80c400d10242c1120100c480d502c0009161503c28030821084503152408600d245004046502c0c16844440f1f1606104400030700043d150828241c0c136031500e101d48618509104418100c1104454807103940300010b1003a000041501000041d40841c4035582c8419a200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 508232275 1250 508231025 508231027
    0x30521030a0b010507050d050c010c09050901030f031701060509010f0c110f13050a0b1c0b07200109050d030501140607080c0316050a060605041109040c0306081203011508040503 78
    0x81e0700006006006000314541441001c0190400081050104c8841c20341c560700c0d4161035010301800e160868944103642c1c0140084808184801e9695503440350450350f00000d110903400080ca0100d409042c0041c0d5003124450f444008900960014050a02c03001d080c0e03606c181d000f14140c000c131508486000081c00901c8441d40d08070240c101010072040710740c0060b00c02c1d00d002005011400071030704c080722601040c503611494424a4540186c100b000901c0c2003d25405850b0f81d502c1b154101c3c68090025030a0011802c560359824075940b120382d4402c548040204409001c0c0e08106440b2214030300e607403001a00e000c0c0046003545020401c078848000c094035150400740c159442d2600c40d070042200000ba440140109000c0c03042c40410741c0d1a05120300007500d28800c1e0b5141031016200c1c940c001e24419810301c440c01c1464043c80040e901800400c480c042200300b04004160004d00b0f00341c0240041e8090b43c4090341050b4021001503048644042e4490741c80c130b0501104862200c03003518000c0080d04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 508233525 1250 508232275 508232281
    0x1608010e1306110d0b03100203040b24060f09010806030f0a0305160f030c05160510050d331202010e090711161d040510020c150c0403052103 62
    0x484595151002440344100042120111480d01800e4112040401d50991103051a0506082c2400b040302d1740b1f1070621080d411418296206c1b40110380c01811000309061005800e140c0e11480d4044480c40390011701030660300c080881810100d94800c115181c0469400c10200c0c120703080002e0760502903c1d580014100103031850b07404680030f61001c1c031903249101c141c5400d070000ca003546581c0c030405482034603075007000d03031480c80c2041c00c0c42c4c80e5103003005009050f1101044103440b03400700368015240a2034030f20307641d01c5031884000003407160b003000040402481014004407aa07410140302602c14044588043c1307907a078018610b6450b06410000d00040d80b90b43c1004880c208a51050f8000300582003200c400e9040003642460320f1681c22041c031148030307444010400488a6250200c5420406040410314a490f0b182c056941c096102102406940001d5000fa00d030018807891800030618604104d040c1411040c0140c550098041030b10305000318028820090340c000c201c205c0041d403079110f090a603a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 508234775 1250 508233525 508233541
    0xf020d090b0a030207050601080f0f01050105030a1e05012d020702030307060203060312030c0703030b0f4605100f0c02040c03090f0b0108010c0903020a0e06010203041703031608010e 80
    0x50042c103895824143c003803244c100004c0040c400d82d4060030f215030080400b0700000d006030b464101302c412821b5813030b40740c40c0041c0007a4902007540b900313071034000c0e240602d10a150092000508402e2034098501d51030034603441420781c0313241419001c034150510708040d40304040d8a040f00301c3c850300d00020b500d03034030400c550000542c01b50090765000000030161003100600f00b00041081d441160b1000c504440040e04104140e01032042d0410303640c00f5111501c0b803c20000214001c94403d03101110420204000c45e61881c3e1072070b61074182c2207940c00a00d01303610100056041014040d006581c801d6004100b00c070b1410f4422058906403a0030b0350b541c480c00c0c0c90543c0901009000385a80d4604154984661302c021031241c0f40107240d0746200b4510301140f5803408414a0031181c01c4880c070801c100d0034038820000342c1d80b54000e100607200d03c0d000c1c3c1c42e503a40381e0300010b0f8170f1445a9032141d0440e0501e240404030650002c006180700d60b0a1340c40c1114410300e500c2c42121980d500340184030744c0c0701100f00490b1510f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 508236025 1250 508234775 508234777
    0x60f060d052e0c0512060103110f090a0e06010c030c080408010e07091a031b13181401050c0f13031403130b03010302060d02030a20040f08010b0918030405090a020a0f020d090b 77
    0x144041c1400554006c1101d45840305500ac00710350410010300280c83c4544d4100a000364008080c041d400382441d081030b000003440904140c0001e403c2207015010a4244055502114001d040d100b0007004459110f0002c10384400c168030540c00b041e4603081591114207110028100c800e00c000b00038019010300030030007412030584262050341192503084101d65034001441a0424071000b50010288010703245800c4098603622130090380039074140001d21040c0c501100a40d5150380803099007a8545901503001031001e0400d500242c600203421034483c251400c0403006200020281c1c0c003542e4220748403003050b941e502c428400290032031020046458031030090b070302840e0407003640300c408907400a030040c404407440d91003041034002e102c001601708105030f4519400310080045100a00103482d28400081c0710500040003080c1c00c1c043c1410102802c4010300817503001d8a8000d03c13070711050800c410307050025008190468003103041004104852400020300003c1060141d0b00c011500c1d04000084000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 508237275 1250 508236025 508236031
    0x515031506071a0a02030a150608130f020915280302010c151e06050d20060c0f0102070209072f19080304020405060111060f060d052e0c0512 62
    0x10303c3d400d802d0b1043c002d41481070490040c001c149001da12401d000c0f05202c100c84400d00101c080c0729010404105052b003001c1e0413580100c45a4441e6444a80c0d4180545156a0b404000f9442a40441003100380b111031b1210001841d42500e04240c1000d24200e401000e40328a024521410300b241c40800041d0310a101c1d80f4410381c0b1680c1e510650413904030311074041c0e800018400160045551500c89002c406118880082008594003004640c480c0c4810850380041040c6040a40140e60400c260f51100381c01c442c055403601c1d0444080070f001001751030003900610f4049104042902c00708283c0c41c403440c2e000050083d01c50141c3e02034911240d030800f0380b044000241e9840c1c019107800d031082c1030440180c511420302171380702c3d00e560780740600c100422540018040b605009650031000043e00c00060142d50050162403450144d8481c0c41c0054804050b84a004003907201e54805900c010101483c2c1a00588041200d2481071a00d841c8000558440604090004d403003800450903000042c240e041d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 508238525 1250 508237275 508237283
    0x3090d290705180111153909030f0d0309050601060c03120f0b060a030603151b110c0603040f03090e0c0706051b0307020708070b090d0f031e09051503150607 69
    0x608031604540f05c5041c10050030b82002e0210340e101c01c0101c002e47c0003450036203030304280703481500c0c446801e12621003120889400c1d860011010030b074000581c0f000c00494802513076910841d1600705003c0002030103803483c3e045c01c07a00c80c041c2800020720180102102c0700700326071507190b01800e0070182a44900501840360340e086825250b18220840e603c0302c60041c140300403290f40c081261800c6050030140004500b001c9801d451030900f00940401081c080c07031002e004d05149ca102000c045415a030f20300200010307500c0d400701c07000051000300603403030480f45402072103500c4021400d66071f4260303003689003011134060a481200b08800f10009103075500c00c90380051400b2540c1e113040e040f00000c11442c3c104648560141e80942c4062241040030001180280740c2c03840c03c40c0c900070001c0d0109089100108006003482094100b040130180100c501109013801c488925a504088040041c80444d081c0303c3d45d4028225155000600ca500300c04907482000c00c9098111203034411070a00505601050040d2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 508239775 1250 508238525 508238537
    0x10e040603081908061e091b03010605070b071d0d030507050321090f0d0509040b0312180103050f150607080403030f0e061201051203090d2907051801 66
    0x2000044020010300f000c8040c0384041210000b410f8405072020101a1031075208050709030403070b081c81d42400002c01140c501980e450520742c40342000040e40c43d2107042601101d000200010941c26400300240c8241030040d00c03240c106840702c03007050300c5011400d11654811030ba4002d017540c8900300408a00c003064030900d00340f13103003c80e1034640500719001204408141d1310310701c0d000c8500484030348015402c000c1c2c140141c0106030558030030301d23580e4107403001e03460902c00082980440740e40c90f948035440b890006400d9603843c48030800c4401c42d50784824100d003680072000509090b41c0d4460f1054038854081c4150841d40e580b20302101c0d5140940d01d220b0264040e404001440c0010790b100c0141c00194825140c200da40b0701005800350640c0340c012001c90041070300b8030003004e0b219020001030341184d03015540d03003200e49035070740700b0381e05511030700446980107094140c800c01084a070120200c100340e012802c1081c1c40300c00300300b180d030785170303010341e5141c0003e0300500070b4180904d036036002540040414107000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 508241025 1250 508239775 508239779
    0xc0607050a120513051c05190908030d05040b0106020d09050405041704031a150117040213060e060301110a0212030c0412060b03010b011e0c050709020f031006020a0809010e0406 78
    0x6141910f008585000fa8a81d0b0300e2480c10400000f00505401c08001800b843d2580d0480e010040aa005403807201c08190380c1110100042402500401c0c0036180381400d59a5031154240ca801c0a0030090320226000340803038000044591010820b4803000c00c1e1030351030282007407a050810000c2e0030054401d0311000c060341c4112200300d006200030802103114610402e08038001019181d805000184501030182001d0f1074000f0316a0700a548221804129041880a0302e0741e00118500308014507103803000901c1c1c4400420720036105840b280c40345a00320001d05c042c43c09240080402d000305d15100001d640504104044141c11b01d001d564803122030400d150800784d43d2003600342d58140c1c1d20826544203a54001718200d5003000c0c020850400400e08141c058403106038011100c581c120701c1309004010070745111808200c0c0503c0390400409441d00155161990481903521552080d04ea9007005e00a5010000d03036140081080c41016801c05401418081090015243d00b000c8800e140d51050340c500340 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 508242275 1250 508241025 508241057
    0xb0307181401120302190305030406051302040509070504150509342c0604050d080706091103060106030504080412150c030b180118091419020103050703020c0607050a 73
    0xe0500810146045002c44855401c001e81001e10024000106645840303040c0d0109400c23a00701c4c0c0e00551b000c407000031240c0d504141e0500841e480d14000354040d08090074440481c20000b520030030f444003102c0c200104802c042c11048148080c0c400d894109550307100080c0c242c5282d09400c48410000e00300c1c403040092540700d05803901c14050703404001c140d80d842d60002d4003808251080000703042d4081e03540c81140b00c034000303000d9000300c2c8a034510603100700081004001407602035803580d541c040818450783c642843d140482d032603203002c90303402031040d00700015620307100f802128000c07500030861a1409062031b03201c1100c50030b0b0303400a96496991580d00c241c001c041c0d214288185d151503900040380d46072542008402900341d101607012250280046c4000c03a41c00784084c860340e03402036000424090728900505107843c1c0c2255030300903000d07000c1020700100340b42034900f026907c01d9804001d82c3c0d840003010740407401041900d0a4950014000440c00c5000340f0040c5541d20441c1410441c0a041c011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 508243525 1250 508242275 508242311
    0xd031a06030f0f040221070f29031f030f110312070611040e190606110309091e010803030108011107050a230106060c02040f02070305070b36100b030718 67
    0x880f084c005d911010b0100020000d5188c07550103048040c210820340c801d150800b0f0143d10038111094908080000856503054414007054114010030039442006941c0e818494550314614005440200003000706101620f400714090304044a294003d82c02c00603285c035080010301c115203144841541c2000b01043c021070480000344903901c504120000310201800110580303503c3d620010502404248100000034040199896a84c064941040a40d554190384001407082100c100d54101e080c0004a85400c003c0020360503285410700074407042d824501e14005038411041c02030b080340c105100d0400021848110401000c40e8a00307604004020880078508640da00d030310100118150404140c1181854010069001500c203821820087c5a4401519911501d036004000303102c0100003956100025420040101d0f50700801c150403001000b5074000e6a900800300640c41c41020f01d182599003060045c0341d90f02c04041c0c0a000b0051402600c10400c0c41000c038480301c00340d200c10440f0092403802c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 508244775 1250 508243525 508243579
    0xb070c05060d0c0f020606010f080a060902040608010608010e0105181803130608060a03030207050d080706050408071b03021c030201060305250e0106141b0d031a06030f0f0402 77
    0x16000a0400070f050003d018084448408030030364001c0400c01010307a82222024040b8829030520700415580c81424070010b01c01038004208980c400714002c11040d500c011350606841c00d0740c640180da80d80f10307106805900b5003407003900d6128244801002030700c1400382c511a0016420b5000d0916070240301845070858100010020001401c1d8000304070180c0d002c404d040d040308044c0c60040b80d0a0850b18000d40b10140d50256034080c040c800380c91000c12080305c0c00c81d26043c0d0401020422414280b03013100d05980854010b03500208403400811200420000c09021640e0003070010007440000464001001c0c2509820307000e65503100800000f16900340a40c42c86503011881d21800080c40d14580c00038007910360401400f00304050014015150400c079910b00552440d0185621044140381c07901d441004e1210002032800b0b807500d0b4840355a0181c01c5a03e400580440c22680c903440b0000740002404103c031100030900c03420021400c50503826201c00e820030b0000e00a02000340048404500c174100300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 508246025 1250 508244775 508244797
    0x80705060f070b3603030a050709120503030a11090f0906240304120c0b060f150d0516020c09150307081c0305060913120e03191712010b070c0506 64
    0xc107480070b04060301080784c6520300444100c00b5003030440350700605a07203000c014480d01d01180e5500106580314082e0b520b80000f820207251038000100640342c019140d800030b44940e0042414003d21a114104c2007049c2d41301e00c08090a9040506810010810610300150215800100c2e00341401c1101d129a1161281200d0400d00079541e4100741c9011000d504819503090200b100d00c02100700007030b00f828040b64110344111404585840010300181000042c1d202c4502da9480002e1845d02d5405140c006922404040081c00c6002849403003c5c4c3c1c80c1c14a00c80403a81c01700e000c1000924501c449401149030302c40207000c80e12010b4845089514020b20b20b0f101802010341e401b080781005515000303055001c80242c81100d591300b40620864600504000001d04a000401003092928440c21814000ca603009044590683c90004a00c05015440c14256100038500001d1a0380301c1101c411215030294902041c40d40ea842c5c50000501364000402c02c0741d102051142c0000c0981e15440500040b0a41d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 508247275 1250 508246025 508246051
    0x30c082a130f30030302031e0106030518010c230403060e150603011401060503090a02270a060f030221030d0608150f1f0e0925080705060f070b 63
    0x340794150f2a054600c101c030803035240010080030b500000014040d00203d90508015841e91583c03150740f9902c0c410607404000c26000da0000080300b82d4076410260061070026496401d400c0c00c1c0b9441e609840c0b100304400041900701852040000c4104c04040f00386041100480c1005e86079075034842503554003142d0325200d5118030700940800c0e051041840d00140700718020000203100d54561004484140f1942040c000048009000550306100f50211540e00520144100400100d0f0f07415207240c1c542400d055401c036200160740c2e074400f485403109548ca4171340700e20452491035082042495280740e8560801d035402192903103e0504101503c204008080081031240c14030f51064603100da603803003c082480d511000d0049103040032500d00c0e000312000801010f90010b5038070900c8c200140741c2c480c031607401c2e4140400c02441c0000c580d11046040088812402039500c941c281510703280c81c040c58040781c101000402c4039161010040009888180466040448175212450030f0001200c0c442c0412607 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 508248525 1250 508247275 508247279
    0x100903020310020909070e0108011202060c07080f1e06010e10030501050c0306010f030915111209060411120d0c1406181614100516060c030c082a130f 66
    0x5e000703a8080e07440012031401c4080c94042000080c50302d141841040711881541c1400030940d1204001c0b0b03240d0100d0401241c10386d65a07030400c01d40c8e5151424601d10580140c401e0300c1d00050400c0c08121080300002d0062110380d08021901c81030400182c01c80d0580e106081300000020403e019462166560b1a18240c0300d280400015250040e880d500d40109450300014a001407070700e0f03080d0001038005500026040d0700454104205102c2c503c60340d66881d01c00400c01000000016007548164491103650301207245580030f00000041c020340286564200700011000184142c0c45d0307240450048101c0b100e000c001c914501c1c10820b05644803503804540005200000710304200c0034440ca020380300c00c0418039203054403070720a600f05803103250f204280006103540110711170740a88440e0b117607200c8001e0020000e07280070401418020034039000b01c3d040204010190b4090b03d0407502ca0041c10704644031b242d0f003000017484a810074400d00703910240d06114030380c10075100d0590140030b047c50406180d4128 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 508249775 1250 508248525 508248529
    0x40e310b0411040c1e1209050304170304061e0917030306040e0304060c110d02030613060c0903030c03180810020a020606040207050c010f030b0603040c090c030b09061009030203100209 81
    0xb00c0700d40780e0030b000303a04000054002540c001300c6095031080c03c1030b208000b0310b108001200c1c05019071400f00c1519041099202c1803090120007081101d03200725081d403480c02014010354990140d03100e040041074051000c0d00f0151802e50041d14914000e04d00544495110083c00250b41d11082d486102030b8030100811005040034490040d141c0c02c918015400c2c1441d00c000100741001c43e05000740914050038408000c1d490f005403250850b94010300361012880d100751000c044101d41802500c04a003040c1036051182d0140e01c0311011b41e609503035010340c403509903201a00c0e15090105074800f02450b1031030002d1481814808460101801c0b280580c0c2e402407207034000c0c03410304042c040c079106610401c08040000d0b00091035480d051760a0038521003c0300303815800c2d0010410b4248207900f01200000b0001003101001300302c81900c950050400142400c041d0490841d86641040d030f030000c081002081d21071070b2140300600f44010398603182c284682c883d40404d040a0780714030041101600480e00d49014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 508251025 1250 508249775 508249793
    0xf130221010c090e060f0303040e010803072102031b0c100302090f0f03100c14031312030b0108041407052701270b040204050402070b01050a0605040e310b04 69
    0x3207051403405201c0f40b401d0240c0c0100c510005412144a90780b0308a541c026500c050040c2d5008124040c215450356a42e0307541c40391a548094011101018540940c0616000d500d0006071001c140d82d005505007000b00204c50f113440070703104485900c0e03c030785020740e5025030b03500c10054036600e0b065a01503107641c00700e001e0280c0e403c0101d041611903002c048030000c0310740f00082c91801c1007641d1070000c104c00070440400d07554104d591a0310061401c00004000d51582076002c1c005d1454490f0707040040b00c00340b1328022407c071164a9842400244004040f0b00810500f142244400501ca41034034004c80c4d607400058a540a074044024901c2448600101c090030401d002500408820b080840483ca6500c0348190041b01d41011005a9170780b200024143c1d1207030381c1924064075015004551b59030450400c0103003120309100c0c2070710030002e0b02e00101c0c155104409031030444521241c01123550300d820501c1e1a4250262650038041004d040c0000000c6024014441d41107014840440e29030400b803c5c40946 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 508252275 1250 508251025 508251041
    0x30d0c0809010921050c190b010f0e040609031830030c2d140c0a0b04090e011104260303060d03030e0a0b0907050108060301060e0f13022101 62
    0xd0391400c400f0002040c02007600c001807800c030b440300c1200850442070594040c080c0c41c6601d240c901c240d0800d00c01d44020a11800302450196480075440da1341c410680c480e40030b590180500c1c0703c600a001c1800124076800c1403403114800d003085c48450a00c036000c1e008103802e95001e501c011030900c3d1060050621144240540d2a074007106100c4001141c402500300400180e009108880c086905000803c250050b9135020707501c10301c0c80c0100d2246050240b0000c13480c00d032404681c0034050112016180500510301202d111075022410302e8074010b60b070b4000b814410b1842445540302c040c560044800310006001400c100400150b231205101400e182071602d07115201540e41c03040090040b903607030721584130020b66414900407483c0042c0c1e0f07160303c1c24030102e40c01c0241a01d4071103050140d442c101107109000d8a00a1765142e132a5500e00d02003500383e41301c0e88030f2604844461404541150709580580d40e000605a010300e60003e110f5012401042544d101d120070700c0b48103135030000c4810082c061624 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 508253525 1250 508252275 508252291
    0xa08130515090a0e2a0903010e0c0319060b0a090e070b04060909020f0c0a0b01140619030e0304120606140108040c05060a260912180d030908030d0c08 66
    0x200b448101c1001c12500401409002400c0031588005040d030301000c00b510b110f68500881c00c850002e81215162155001600920320030350170519180d0702518002040342e110071004005044851101e04400136500c20300d682551240c0e01c560311924203403559000c0c0401013104410000d400712280b52041c0c2005140d40100c42e85503010042005030960201070f030b00070380314501c00042c2c2e10104040c007002d15110706081d100050040d15140030a0207890254103040300c1d0007925600d004000c1400f08003503446801407101c00300d00c0524100c84035501c80c3c6d01681070400c0160441c0d01d0145c958600101d0b80018020488580d83c444400b4851080090003920a421080c20034881506183d9a411420481030161034002c080202d500400148640442c0e03642c180e04211b0121003480c0307007002822039003088640012501ca60260f00d109014ac40c13040b10015501501d071141044d01150404c1a5150042c0055003080820040850600c800707200816189680c500001043c44c01001c01070301502000745140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 508254775 1250 508253525 508253527
    0x3070b10060903080913090b06030d110327030f01050103030210060326130b0409053405190807020d030608070b03100305010e340303050901020a08130515 68
    0xa040c0d000700b040000e80c0d50080c40151543c16200114028820580c3c0311aa02030410003142c01340100d1424103401064254140d40220300f0488098407161440c0043c2c81e01c0c3c0c0e00821412204c00000b918814031a14280d040003588504440020310304010352104904c1650b48400420403d9010012040254074010701804118503523119008075200f80035030011307603107140203d0003c280c0100e4200c46a0441d40300b03444050749d850f9030000705250401e00400e42d401e03141038003050560030111940c0c24260301c140402c9102c151031b944001400301106a9010601405002400e03010301001d055050503a0140d460a400e450300010092030401c40703e41e400d0600d0b1512406000415002c542e038002e03103003c0700c401070b540e845049020501d8031040e40042e0640d46084a580409280400c0380c100c1201004640d100c0b1400c00800708400d40d110000500101d51718a00c02c20002e4040d5001e020044014015030314511010f894042103076101c2405070200e0f0005030360501c418545000c80d801041d0090a20b9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 508256025 1250 508254775 508254779
    0xf0618011407120e01050705091309230703051209041406010801170f0703030305101a0304020d110306010321050708090111030c01060b0a0306080f0c01080705160503070b10 76
    0x820741e0140c80b4004105a00c40c4040202d090b50b04101d0300340d075101001300000c0c580b008004003117800080c0322034410030b000304045d60500018000d0031201d64020502c00b460580c1c050002684151100c180e48040c01841c0c400000b1403c10b01c42c8406d56039040000c0d80d0b60392130b0301c001c11080310170750406042d004101506105280c0d031300c03818650560b95000c2034681c074200c0d01d0101a01d44000d100040c000340c0700d000d41c0802010b90580140d40940c40c105030799414140c459591501408408800003040001071000501525140d03008444c6907005a007101091000300c00400e0401781e09070000e480d034410503807480c1003418031580351410441d030501d0007600740210350765045018401d095038241003113200b200b9a40420030074000c0722a1803901030001c10417a0360b24180b0086640100241c3c0e00440c0c0343c01c0c3d00080011021910080d2844c00e000907000014071400107441e070703072009000c4c801008020700940d5100c0e0b000d121000140d034040c0000319110104c03031501801e544001003100b102025400701c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 508257275 1250 508256025 508256051
    0x5041b020d0318050a080a021204060c0b060f210f0d121d03030106020c1e100807180e01030210050c0a11010c0c09050402011107060f0c0f050f061801 66
    0x250051668042c54007003030642509800b051078811151018250b03015141c0481c081000d4040284491845c1d6005eaa00340c3c401100b440101d4025482140d0100d4100e900600016404c412050303400707900140310400310128100455158100702050740c90100c0c088140b9070f0b01c81c0d000c01c1072400c0000d811008008000d41000000d05019a07400ca234040507031240401005950389010001504082ea800c50342ca960359072000940d5560103061040c028608070380b04001d0004401c5e44503810321005004201d0841612404680e911402840c0d8010841861150422044100380c1c0300300a18480c03044e10407a50448c01000401990403e6210511070204002180c00c5c2010504500c1c4e190000d050801e075140c0707040140d912030325824000b0300040241d00c0116003c2010303030000d4010360003039035001c6051030b0907010242c2d99444c0d8041c18022481a00c5850301681c4592014601188030765480001081c4607503800f4070300b2041046515550708854200103251001e138080e155540c1ca004002e02c080010305103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 508258525 1250 508257275 508257283
    0x50f0d0b09010b06070f0317040305040b03100305070801270c1214060103030309032709021e1206090c040302090705090102031210060908010b400605041b02 69
    0x10042003a0a29000a07110000079880200a01c0340a4810340e0b48060611705141588400d50341200441e80c14440004a0080d801e861840390350306440382403a10381400705548a0340c1005003107040b034050070400400024414000e52000380700d0b50001140c0c40c0b803a81c440c062a0b5510400c000c0d40c1c81d108049074800320740204101001c82d0755000c5000301c1c02d81c82c0d0622498000204440c0c4005200d601d000008240e8140c1c485081680281c1e03c42420848946203120040c5650305907400d241d04240040c40400d40300d034010005c0c9507002c070046024404602e090301e06600850901c08103114071400300401c03410000341d0164488001c0d0142490b160450740000c400b0403014001000308540443c4074005031340200220703080a0b0080b0340e0811513213483c0405204041d918007038540000c070381a40000c3c2c101014042c5808160009025400300c1d448444030400d500420121140c1005002134a038104500781007012110f03030004200800c003981000207000a80e1038080d090b070041071046441208990703001c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 508259775 1250 508258525 508258549
    0xd0f030218010c02181914060a05010f1b0c050108061f03050a0e0a0f02130b030601120807080a030c0207060e060a180b0a030b090601020111041701140916050f 70
    0x428000c442001a001194008009141740242440300303000b07102020120311117044503003240e04000e01654204880c20400380c2826210319170800704070034062015601800d41d4050274110307441d14a00c130300000348280040003901d00b0141d13014200c0c10006d1005580c40404c0e0755010700217540f019040071424402e41020704040344c0c203000b0540d070f52020420380b40d199080305450140e10701c11140518060b046c141000344000e10103e10402201d43d000000740c400d80216044164005c002e441c91f0384c42c16a450b00d07246505402262540000c001c0040010900400350406000503036000078082102c0501a250140744c0c0c02500902401c2e40000485070341d058204c61f4541e040b40303070030241420034a50801840110b40c0114100700e1001c03601c0c155481c2d042d481501240c0f0116210002d07925450300690807161042c0b1400e441000401050001311418440e80f64440c545000015600e070b624018045201001e403413520301c542180b008403200300c1e608002c0078081c150403a401c002c0c40a40390300155451401d8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 508261025 1250 508259775 508259777
    0x509040203100c020c0d110a09050c070f05010e0d02060702070605033d08031c0903020303240405010f060f020106062c040c21090201120504020d02120d0f03021801 72
    0xba40b501c900c0038401d2041103034400d006031407a1a404210715155600ca100d40f00c07d81c0c00343c0c0400400040c404080e010301c42c01403809600d00d51405e01d0a840343d0341e1030f2815040c155060b641743d4032040180c480810100040f0003040c0d016140c03034200884000c0c2050025404401006030900030310420410186c0e80c250f1503010b00c0d0115203c0e1030024440c040c0c8007942c0821414541d118000041d40003070100061501c09c43c202c5421018a002c0400842264a42c42000e40168000d0001800c600810881d40340ca01b000310b0000d000407500344000a0507101c0036002210801e03040d00c81000300581104d04850790b420303580000e1000c0707410084024107083c1d0f500e0340c2d60644003280070700000c06941c0240030b0800820143c4184070110f0301c850060207a4066001201c600252040048072041d9244940c8400320750583d80c0942d591010403140001e040042c0060740d211010840d548010703511803600711102c10502000c0d01403800d01810240141da07004191400741401004038408050702540b06012500003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 508262275 1250 508261025 508261031
    0x6061d0712091509080a090b040305060103170c0307050a032c19090e030405032103040b19140610020d05030a0f02040b18090a09030e1011030a0810050904020310 71
    0x1a030030840851002ca44102610f10714050040d02880010030080090001d03c2e19500c00a59a41150401e42d201e60b1202400c1c0c0d40145005000081c4141c818142032001071400a042405490505045611244d41110350b9402030803080d0426070031a07401c0c4480c107190410003801042d40300421100f0398001034076038400c004006140c0c1a2080c2c0c0d10345d82c0041c1c20340b010b08201000c0d00c1c500c0b0070f60300d40c400d0040601c43d2060b0b01c8000d81601c0301040c01c040603507090401c06e095803079580e00c00118042c054021090074134440e1010120605612030320703a0010403450220290b05014050104200003101d44030219004041140049a00034040703e800c610314450008282c00030000b800c0080c0216003251401070000140024600250507414000c0c19080781d5500d079075118201040111040900002c0c041541454440380c1440e00030781d209612a00360419881402401c6031107420360748040301c05008a5900414000c9141c00501303d82c02500301035071840c40e01c2c281500000c0e51500da09155080c0c1c552 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 508263525 1250 508262275 508262291
    0x1107031101020c0a0501090c09200a0e06120f0c030123060712050310140924101701050406080a0807030224090f0604021e0102120706061d0712 63
    0xc254100c400c003141c0102900c0e030b502201c0c0b0300240a00a0000305903400c561030080420b01c14010b1181e05032051840c084504400c2030313502c10108507000440f00200b4010601015102ca07294000104030600c407580300380c0002d180540101b090b019005c0c1406448200c00d00040c07148082c1200300c15851880c1c180220403200318080014100d00c07401c00f0003040140b000445110807500080a10b02595103131899074410740c1c44441c2c0300b1010702541d01c0786621403502c101241101400c10100c4442101240e00815403101e00700200e80040c512031040310002c0d03a01c046c0c0782040c140c1040b16030301401048a0501c4864a4070550f01da40301180340000e8500d03c40003440004050003042040c418052202280900d907002020403000110210f42c10403681c041e0901015136182c0c00301d9602c0c425540101241d201c00c0381d1845800900c8140ca4007141980716440e0b88090078117214000d0000c0303a1140c103010500c58200800e0030721080e100000714115800c068148294650007403048907428220040000303804d0303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 508264775 1250 508263525 508263557
    0x40606092607091e060803070201110c0a050d141b180903070303020306240901030615080106050d0b120109030306050901030b010504202a1212130c06020c040b04110703 74
    0x180000030601292460945d00180480011000c0d0041c5030007600c60480160f040c040043c2c448204901140e031002520000b804240350030310640d85824028503414241e0fa61400f06603151003507800700001c048070030310010040d81c600300c80641d141c1c110905010410381411880c6660360300418400a052640210002c1c4003922000f088101009801c0d03005140f888408811616139405134040c40e0000c0d00304880030a200100c0d0180c01e061506954039401e40e40c0ca444c0003280c00b83c1140c00c842281d15100e0280f0141552081040354400c043c00e0000508404103244c00b608841941d8055801900709500404c04164214443c41c11542c2c180c80101c0ca0240001c801c2c0001202d00b21554081000485c403801c2491050b840407034000c1560241c110a2044c03511285c2d130b5407092200c5185011310802140b2400300360b01d150603410403062a00100ca618159a4048558500f908400c005034000c1048000c1c42c60f140c061030000d494282c034100a052075912040056100309107003d000d0000d81e55490440b0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 508266025 1250 508264775 508264811
    0x60705280f060f0f050601051204061d0606191203030c03020f030118060803180d05070b040e070206070f0905060a0c02040f1a030c03280204060609260709 68
    0x900ea10002981c1007102034640100184581c080c000c1000780381c600d0000c0701c0905885030b207002e00c00c16180d06040c514090a100081d020040084036140c1d10340c122040341116a01d8455244210b400203401c081ca003a8003402102d28100c9018111006400d2041084600c51401541400d0f09450080382c26440884190064400d541c00c64032a60030000001502614000c181824040c0580e414041240e440341203554a0040c0452581140c04030705e0305c01120710f40380142d4003e0320311030420ba415183d0307036016294441e045075000d0708114581e00c2c01c01c00902c0c0d0501035030390311901509040c4c0680c800c3c00802040c0219601803103001d000d00040b040840c40c080c1d5100c3e000c141d8002c0040c07101304010414031f00600b0b055a5080c0d800080348880c190f02e4030b004243d01ca550400074006025416251003440c8040b00108100d910340c20002c0d513034130051b0725107005072005010152112a583da1401500c0ca005070b09688071161484c80220b0511001c0401240c0f9404850200801058100c602e98800f084 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 508267275 1250 508266025 508266103
    0x60501292107020f16030515010e0601112b1101060605030a09110901090618060b16020117070903020a05061c0c180f05090708090a030c030302090907020f0c060705 72
    0xd14171401013200040d114070020304069074030403000c0d101e041600f00440c03102c0c00828040e50542120340d10001d06d45500c294009003039051100106c40243c024400840d88842108003030620001d00b907088040d070250032090b03810030181281c008210040c9000002052404083c3c0b650b04070644031184030b014400203c071080c200c0400100780020b1560f542078040c0082071240b00d03a41c807810000f49500c1c40741d502c84c8112800c0300c6e8494602031400207c44682c8002e015600c800324140b0800e03910b240d072003400c891364081c804c40c036507228000064194010049112010390119105d0b810030040b0001c854800f400c03d0300c1070a550301002c44c0d11074401c10142d0341400380a0440d114681e0700c120001e4656181c010310001ca0324240d0b40c45005071111282164011801c681c44e004a9008514000c0000c0c400c000314844a4041d14005007041540310019403814000c1e103240700142e01044c4900c803559010310013444845800c072a034600e0080c40d56600da48031070a070300448000e40c8076540d1040d1940c00000c0400c035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 508268525 1250 508267275 508267303
    0x1020304032c27070e03070902040b0405060f070b13020a17100507030b030d03051b0a050a0804030315030501050612010c09051c12020d09060212071e06050129210702 73
    0xf103203140000c00140500d034080b190a2003481603c03000291407505108460030b8404c091080ba180c541442e041c00fa003a03008081e030801c403140c20040d44012607400034200303004884a4040c0c0034003000a00402604000c281c1100032108140c0885214505d0300050101c406420214042866562610b0583c01000201a484c0d01030203014601007105505034012481440c806205030144903d146d007040582c0500712010000c58420450000f240d030003000400c0e0b106101e4600410341486621040790880b0503036004079001da440b07506200040c80c02000c0c441c000d01d001c0c00200118081c17540003d250100134406c10303028101c0404002c07c400c0107205a00c60807a0043c4c0407407985020110000c0d519400c403102c18002411b90480800c41314801f1a090b0f2040c699814481d0400c1c055440d207841140460b4a0300c015003a6a003d280b00150150040074000c1c888500e00c5103200030480c61b206440c030010500000b20aa003080f80703a04000800c2c10703200c3c0080b40c5804802c0a681c03860801da1600b04203942c082 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 508269775 1250 508268525 508268599
    0xf05091504060b1804050a0b06041206110f180f0f0f0301181101080705030912090102100c110c09010e010311060c100504151a040b180901020304032c 66
    0x7203900d0b0704e0802c1d60000300c43c207075410082d07544c51440420407225203e4001e58841401c000802004a036000b01c0340c0900c6c01007174006505903040d80d050b900360303100c1d0001c18948540402c5c00c0ea01a4091b00d025a2040000d40398000200004000142c4000046404c1886a800c0d08019519620309510030201f42440040c0702c4c4003d4801d050505401c810300307440070b0000d0003120000380b0152054003940e01914000c401003a041d2101d0700c19031129000305140c1c0c0d0441c49800031680111400c1e00910340031030216103c000410080082c1d041c20051343c00211801200880010011075490400d05411641c04c440500310308003042d00003d2039032107500a07084181c481e010702c00b00402019072209015034440e80510416000c40c156400607203102c0c0920341001500f001d201e001c84c0c10540c00001100a000b0880760f40148100b001000c2000c2c00d0302d2070007480c0e41c080108003c044c0c102c20000c5501c4004070104011461008041000300f4241300314038002d1010100da2880d10000c250042015aa0a00c0c1e20b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 508271025 1250 508269775 508269787
    0x60a0504021605031605010c300908120702060106140712030b13060e0a05040809010e030c0324090a0521040509070201020703030c260603120a0c06060f05091504060b 73
    0x800451081c90000b41c81651034100101034185c0556454402d25400880e80052014074610349214103040c100301100d69910781402b1030008104200401040b410342c1c80c025201c0c02c1c1781c80300074640320050300044c05000f6080700d180401034100054524407035221101d21501c1c070300383e03504070017500b40520010340000025005901c03103c00e83e001402a1400c1a40c980b1142ea200c0f003040c415160162070203056100c0030400c00e002940715003410440d001e000740807120000c0ca0500400d240200d2641e0310520310030054070780c07640325903c01019a00b040b81e800080001c0e0000d5100c6540702c0b019001c2d202030618585401c0d10220002e9020382c0c00900008040307034100d10303001c000030740030390310050003240080d1030700b000100298001c41c200744540c010201070b245850000b01580380d00b002e002d000355505104080e458000191410014840700c4540c4e070f100035480c0b10b1407030100700340c0740260000e0f40c02c00ca401c1020b12840d11038460a551003a00e4440000002000c0401304000344500d8218040812340007a003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 508272275 1250 508271025 508271047
    0x302091509090a14010b0a0b13032001020c060403020603160903060207030503061c080d0911100c0c0f03050c0d14010504060b15040f0b03040309080d080a050a05060a050402160503 79
    0x2803043d036014041d03214503030326408034075422500c2030402541c3c82100d80304c1c140500a0702e100940f4102c0030f01c014400c11140c0302e498660301c181c81c003031a028401076490b031022a1941d0501681507182420390720320b428070b4296800644903010091994109564000c400d5500e2403140046000940c0c12041c11569480d00c0e00f13004150b60310445403907000300e4408460b4640d03141480c4802081d580c00c032040500300894155110082c2a88030404d45030184003c0242000c2c0c1d0300c0b0511314030215450340312000007092502c0c4c4900740000036440001c00b8a900b00c01000441c41c04aa0b020034488112007466031032800f860300e0310708491001c1202d20705628010400c01040b2036540041c29085084550291140d110b003440d440520850140c0307002c29200f09802c11001f00da4102440c1c01500c03038244043c44940b1110b8107442c00a00290303403000a51310405010104d100d40c4034040d0041318460081c0058074085004c50842e12a81c8246802960b000a4000c0a041d0100c0134151465005090340c2d070b40c00401d05 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 508273381 1106 508272275 508272283
    0xa18060206091f110408011409060709032613140a1206050621010f050c090d0f0201140a080108070803090d06110904061701050a06060207030209150909 67
    0x21350a5220044e040a80080d080c06000010b699001d0202881c5003100a032218285820000c24001000e503c00007620507603800a00c868000300c0250700302c21041701c21440401110708040340a4404408688880c0c084403400d011440280000303600b0401508601c0c41417004a40f00c20680b4800512660401e035845100100851035211302103181c07a42c403501c0a202c1d0340d920703556241c4010066115120703c9422280c0100503e050502035000702e02d00551001014100c0022030084608580c490006d00002c08526481036032103e00c0b50354040e002c0b540030f000701000c1d400342040201d4441000400e5861000000b016444501c0c5140c072110020b26202800b00812003042010484c0c607201c0340100c8009100041d2407161070390120680034215100500a0208a410a88100300c03141e400500781e01540d40445e05c5800c1512060301c1c801421000100d02c3e600200000d00b00714006070041 = true := by decide +kernel

theorem cover : BRFrame.Cov 508093525 508273381 := by
  have h0 := BRFrame.cov_init 508093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 508093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 508093525 ≤ n) (h2 : n < 508273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
