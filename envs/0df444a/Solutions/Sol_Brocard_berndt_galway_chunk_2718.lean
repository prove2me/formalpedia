-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2718
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:32:14.60769+00:00
-- url     : https://prove2.me/submissions/c4c108cb-fbd8-474b-b517-7ce00a14d8b8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 488669064 ≤ n < 488848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 488670314 1250 488669064 488669099
    0x5060102030c0715201009030909060623030f0a021c0c0e030601320d050d170c030c03040b06030a02330a0e12010b1e01030e0115 57
    0x1544010090b01190b110300300a040014046241d00c080f40e80d0380396900400c1d14942181c020100e10442c01d000e010b040d0040351441442845810000b03c1400900d000c2c0c90f4201244d02016006242100000d03e0b550807403c1d440991034200304200385400c4d2198410483c0c00180c4802904407807036800100c3c450070a5006000c0104522420040140300c8100c0790305440000c062200025911114203a031030504208450141c030144108140e103100c10070321000c0f03042c0d07031036a07204d555001005000f1490315446841d40f18644c02000780d072070451041c0005800700001e88440902070f0300141c0043d8010a103101900d0080303902908891464580e611400102c041c050840c036403501601c5e00250050b6110a0007454030a0088100c1c1c484a01078029140381c3d403122824165068010011303800c449600001c1c0c01e0110104550028441201500380d50051107904e544c2c58200d02040900c09010750018006c200c1c0c1c0100346c1c2c051158480b20079901e400e0391035545841100801c02039050100002151903080c6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 488671564 1250 488670314 488670317
    0x1e0a090e07050f03011205010f050108060c090d1a041e02030303060607050c130507170f04030c03090803073801050603071403041104060b0406020604121e031b1b06050601 75
    0xc20f4408645081e0607030003a400020803c00440b007103410488280184020211404000c0102d90b1502075802c1c0c45100003015442c51920005a10030b599480003d20b0508603040342c15401c0c68100718040046000054a042d2591100082034188400e010004924066800307806981542c8801050200e1500301600484060044001200042c0c650f451207c03003c14000e000450035040403d8050300c129040341a00c1d0780b4460b00f004110032a0402552960010b50600e0f00040d10304683c1421140c0c110b5517044499507000020701082403107080000c3c014025400d204035040381d180100304c02005a940062294101201001080503280001c0510381c014a2400d041c80110038114541d0b00540c411030b03048844000c1c2c036120701821308184c030a56010f414074282a6203805e09000c0081c2d03803000010001441405603070f0166013003511450310180c4038048a45451940c800700034018001d40f004980008128020f03c0000c0c0781d8910070500140d8400f2604201d0300011480d072104005040d004240a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 488672814 1250 488671564 488671567
    0x303120b1f20070501080f060103090512040608160c170c07030b100501032309011d062401050912070b0c062203320a051e0a090e0705 59
    0xc180c04540074074540640705598601214410304080d4030b502c182035010700d40640e4000d80040c0810790f00254503540140340e0008241041e6984c1e03004801511401400802a00a0341401e0200d0100100075106a524607102d02c0c0c03455541c1d0491000740340c01c410308040050305000e0408040340410a04580300307100e6052183c80c1810907c607a51811031327075030300441d100034202080248501c9034101d0381010b4a0300f4641031001803024100c4010b9080100b00d0b4182e03008003040400c0081c0003d51024401d0720780c0a43d014540d028110301d10b503c49004841000ba841108412074001c04414890f01020b080c05071203541c10481824244a0242203103502098a841021004504454520b01070054885204000c1c03c19140031b64190700e83c078144c4181c1c0f400c0810300c0080140003d40000c0400b110600c440c4112400c00354501034403d010f600d4041c0e031000c00c003002072141c00b1194428001c0500a80702031002980107a1821b0000041c443c10120700001942c4200c01c1c0700d1004004040382c0c2200305441c201f03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 488674064 1250 488672814 488672839
    0x131502151006030f02180613091109010e040e0d14040503100902010f0e0f0915150414030307080d0b060d111c05100603050c1605060108160303120b 65
    0x5102005003500d1286610041c000c1c10032000f030b40350241c0413003251000c4003542003d0050009081c50350720040034522425001c1940444a42c54116060040c14490030600500d0824a01401554042481d0600213244400700703420504250203500100d20414000700700b800c0000380100e0b0703e81391080d440312a1000c10040043d40e9502045881d584200740c00f00081ca501d03061002400104032029031206000400c483ca8880e81d40b180500c100c3c0c004191038012481c1c4e6100c004050a000d0f0504d00c1c0d42c05403c0b20118244903840b003014005564005c40d8000180e115941003664900545c100202008004c202e81c83e40654a90400419000c001d4422824840b0100c0601c0503100030554038001240081020042a08600c5072543c3c00b1030709100402c401d041c039003504079030b05070240200f405064540c0c022411441c400381c202c900c0c1248044a901c0a004603251081d101d010a00c600c102510441e14030304c80318842010a01c0860340c1c19254403201720307001ea420102400c407801041d1380c020000042c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 488675314 1250 488674064 488674093
    0x20a080a150e09060109060e070909110403050303040b0a0b0a120807020d021f0f0809190309091d01060503060c07060b030a1a090f0118020d0204110a1211131502 71
    0x245000b154420003130030aa40c10701004200302c541942c840d50091440318184111250007811481c03d44a40481c003040300741402c1594031140c0314a40c0002e00600c8000204010f1161210300c0d103004100c0102c0510003030300414104030003403495005001c2c017890200505000558140014410f451002d00b250408104940008281c4140c5903084604400d02d1203841100c50351007911019088040d090860241c02c10801065603601c01c071861010284881c481364050501402800c001003a000340244402d440e207502d0b080e81103040c19820300d030302d42c20050301046e94030307000c544948144120510781d03050155a07119003010300042c0c0d55840d09801a40524000b0a0b00e003940707450109504014a00070b81810001c842c1707410001c1e490031210f44d01d009039100c01d007500f01410703001c881c0c2c0464100c1049551400014001c2030819881e158420000812260094209503c8010008120400c102881c01081d00c0c10300b134400e038ad2045801c0520004180030604070011020700300c22480c8116480c0e215044503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 488676564 1250 488675314 488675339
    0x608090f0a030c06050a06120f050c06130515070807080d0e010c0e01110d020d031a0a03110306070305090604020d03020a0209070306080d050f04260a03030b090a020a080a15 76
    0x1c05800040030100000180202401a9900a82ea035802000214039080c4031903e003603561040200500041c0f6619800d11030204003581504500801c0c0c165500c0401c0d1590119030301e00d1246a00400d41d00008040480e111000e03100c6e40e641000b00186089285ea64011055100d065910200c0b5900e03032262000e80024426080e0b2500107803541c1c20201d2400c03001500c003c514210003c0d0365841161074200207a408115207544140900340031a44006941d02d1031900503019160036080100140e0010034800940014030070747c2000d0781a030b5010341721200d00701c0640d1000c80399111160b020b9804a001410542000020305020748107540c00c005030380c0e00180064106452410000b501c1c0d100a20003107030b05000c2c0170703802045030800313903d40382c81c0350402000d0f80640e00c211000a041c64409910f084122541c01c000801d801043c1e0790000320510340a0f00070102940d08501980740080081d40200aa01c21602900200c0e120828a9961038000402501401407494124030700b41100045200020700c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 488677814 1250 488676564 488676583
    0x2070813060905040f020a1202090f1206100608090d1b02060d060807080a110d02030717030c06010f18050703020c03040807050306060f010c0b040c24030c0302040b040608090f 77
    0x580b540c403581e1904080005039001540c1524000c0e10403c0f900c0f10712034100d866480001c117203000c050380318180b820008104020080c8520741044c299500d52035114008960140709900254007010b40c986c8601c400c0316090400c0307440031603075802040300725800d40c000c1e40007106048000c5c0f8003400c828810741c0450300a410496110302c4064407410306011040c400d0207410040c01c9810010b018454050b140c208804c0c005003140b03805a140e01d9040010b64070140415000341141003070a80350011030f03400135030741c0354403081d007404450003a180085100c04403000607804484594407985c0c00d80701400c19600003440094101c50506030300b08503c4480001c1480a030000700100c0c000b40c80441c2c07030001410f003040c00003094076124140c9103c0c21001681c0084802c801345d904031404e155030b5511443e10000d8010340b81c000602020020001e2410302002ca0324940240d03140359424048a49000c2d0250b007a4007440c02407058600050005014451003000d40c0c60313005000c0411200c40600102c4030500b030203c0f00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 488679064 1250 488677814 488677817
    0x60f020a0203090f06030606041e0302030a0807030306060e06121807080c132315031b011b23030d02030705040f1202130b1f0206070215060904060207081306 69
    0x11510b91103074a81100390322944134050340c2c12840c41c540180091400d04c182c1c0140340e0540d8002010007202500b6142513800303103501504640402c41c403810111100e401401d000c40c0003904100001c2111845412124541103014140d242401400c81c208182e9400081072440c950810610300700214100b002060018400c1c00042e004030005d0105016051450800c1040c0b000c1c20110700c51001c44140e40300480303000008031005490b0310350f41c3d00c18110b2110544005c0d810300c038050004041090300020b4000e4924241c0b10804120300151414103681c00c0c158000c0d082010f11175048050f032000307034000c0002005410540345890740d17204100049030015201c0c5400103e010400340240c404245c40c0f90050000003110414011295001a140b40814808280403d403640c40044003034540c1070204114403943c41c9004e140350100c640003559002d0454110740140304140a480000c1d41006586026041c0604540c20507541d0b40c480c0c030041d500a4008a58401c02002007904440d0b0b0303200a1005003825 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 488680314 1250 488679064 488679067
    0xf06050414010b0f060307030b180a150b071e060e070504050a0b18130b1602010606230a0c0b07020c030d0c0c0e06030f030a03050619051c1e15140106080c07060f020a0203 75
    0x10407201c0c011690880040f560020074cd1106000d15400802550062980000da507448000c407000139400340225154000c1c56541490701103442c805020030b803034045d01c809803802c02c03255541042140648070010380e1070390060480d04070001c2d01e240c000c038203330743c00030ba00742c10030f03240c3c140c01d0b6a442c508002c115520380366100d4040d005a6100e9080c06880010300c00b510b045000c02c21310745030303078800f903080459106404d00d40040d040141d107008018801250748c015101c0c0311303545810340010b500c80c1c0d07041a54911074051960222000380c0a0005055213a4100003411034960400110003040900540038941c940b08010b01014083c0d010001050321641035a000324407810441d0030b204003203441c141030060500c0344240501c01604c0d07042080404000041210844044174141440b10003604203100800900c50a050414402030f0f043c401c43d040510350003000400d4a5040c8a0304c891000c0c0a081e00042c034080c082514a4098409070000a0181c00c2c0003a2030030f8810400ca040b03a0000d1982805030300f0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 488681564 1250 488680314 488680321
    0x2010509060f0d14061f02070906090f1d1002030606090a12140d0807031a0402030106030c0806060301030203190c051906111f0903020a0f06050414010b0f060307030b18 74
    0x20113000b184488002e036a40f0003501e0402000244200c59640304098030040713100000000d052082200c0c01c0144201841003103819100d90418001d05011030070304103060b08012411001c0319580c00c0c0303500004480341c00b4000b4582000234000196201030600c550055050000382c40075626945040001c040120003040d41004524088001c8640c1043c0241540c000406406500d40c120f0350560340800545000074040c42c0e6801407202e1558082c400b59041032002c000400e506030140d0180c59682038940720b1100c0d940da841e081054510007400029003680050128418050481c0c01500c0110311a81d0366013400382c1c40384040755840e100c408040e4180c0000020030001030341c012a220000801c0500a0664a825030b02043d1081415a07016a20955203601890030b044c03007807100138890743d40300d804c004118106007802c3c0f018020aa9040e02e140301800c02410b0003810512601d00010700141800040051000030000d25810050020081c151602c40803111981d9000780d40041908803038904a6908 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 488682814 1250 488681564 488681587
    0x60206070f02060609071704110103060b09030703060209010c05010c02011a01020105040b010512010905060f04050c27060a0302060c100e010603080405040207050f0706020d0215130f02010509060f 86
    0x108090060800d2281d00c07400d824a1075400f05006a0081c002d854010b03490311144011599100e030b410f88190440e41200c144400c00200c00041c02c20030009030707410f000084d00c80c3c003c00700394070500c1c895030b50561222008200080040c2c0140526400c1410a00d00785030b02c80e180ca5081d81c00301c241801c0180d549105540c8028112f00329150301600030720007001039250960707030780340080410b000b45889030108048180026600f500301c150700d07076403000586401e41021484e000407101c0589003140c041c02118060315103820040c0b02c11480780800d1000842030054200e4030a0003490203064160400040000800942c403050010045480f10500030407401c02031488004c1110300004411405074140f45041011504103020b8909580c1c1c1140c0060f5188041c1c9005490041044410f8625005020001500c40c4e004107034415001e90729004c0d29507400f2a040c10f02e1200c0c0085031950100d407480050840401c540c0c0c2c85102d0428418182946020b03107680000710160001454808071040001d2400d0b00207 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 488684064 1250 488682814 488682823
    0x120f010f1401050d061e06120b070c0506010e040c0e0108100f06050a09020c1e0a0501050a0209150a030f0609061d090c010c060b090c07050d080c0f1c05100602 70
    0x41e10300400030340300c1d50400b000502040003901c00581000d807940c1c0010308081d900c2c3c0c080d10010700b9010040142566560b000b6042d58101041031303941c02e080d0000a04401d000b49855484542d101c0c02800680e0300b04180111180c0025000791079400c20342c0310101340d0391990003900703020f07104410040154442c0c030b140b10300a48844a0008041d942050b10411180c0c643c142403006942c014400941c65089851a203450001583c5603851101c809605002c0151000b04103481214040d00090086a031480c1640d0240d00c5146102504100c2121107442c42e2071010340905000780fa0f134a80850150140310600e003d0b203580d034001ca2912540c03a902000300c014411207070700c58001001e0000c45c1d20f00c1c141c80015140e10454230460306010034518130b1030401900d40c0c4044100c5400500d1203026051041e068075590b08181d200301c03054131030f0f003484840f02c60140a506100300c00014000b8a000422030305085c07541c00c024685084945104049121030748030340546c030311a0012504040607145851002480d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 488685314 1250 488684064 488684081
    0x15080124061d030a0609020907020109020a060f02031b0d091d0f0408070b0403030b010e041505040e03090d060b0a0501180b0f0c100c141c0b120f010f 66
    0x151480080210009008030390030408551a508001c960000c019050442040140e124507506010b001049020800c03607510440806000b40c80314801956000300990894442d84401703980482030742c800300b003124450400340c00e0300e040b80d10640f0b0600d60700b1400711400701b0035844042145d0308021022222682e1002c000c40c010040a002840440c511031f8440e1840c03040a800b004040466400190078404c00600301d0342985d50004d5111000d02c0c040c10000c0042c107408040c00c0c001407007241c0c11070841c580350040c50083c0700e002c21030307203442417030324042200502d5001c142980c903000c1400f6008641d680c0f40e40380709505019402c0401c101c40b99004000420003190400d07414000f4208404000ca189000700c0001d5541803440030b40d4485508520316090300550400302c1c86841202c600300002552034000c0340c4004115103502d10010281840c1003110701450034042c2107103940b12102c85512440744c0110b8000c00004d4407541401103002200c508200f41c124404505039104c4003400000a03035441132044 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 488686564 1250 488685314 488685341
    0x42403050d090b090603090304031a0a541406181b0613091a1e010302220608010f06050a1403040309050402130905010902030c030103020d0c09150801 66
    0xb502e900b0400c99414a02407072141341d01031728011000800901080040341c02035600450030045031000006141c6085004540c1da00e809400c0c101c5907150351300d01c1d03001c121f0003400f41c242d0895504007120142c00003140502c41d986080100e444c070480110850144000054060f003014242c281d07811031400d15101024101981a280b0650f00c03c80404000c40c130880a0104000310000d5441050300003607007070040c501c54070151a80708100003004443d41e40a041c0502c0c90b0034441c2598080042044030740b01003001d2000c646400e0148144096200c0ea00500903000891081c00200207480800541101c0350b8104001082c60000184202030001404200800c0c540c0782c071a01e46800400001c101220380148202c414402202007403c00d8005d91044000c1c00c0081c000315194580007003001c0360bc4207c1d10810704640d2404001042c803012030700031207205604c01d002d0680380d81d18641c280100c01c0780e40441903c4003012540e01240d50985409074040342a080700e1803400751400c1103040c500710382030b5015080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 488687814 1250 488686564 488686577
    0x405040e030a08010b030702011104090b1305010b042d0e0601110703150c1704051b06090915241801051606020901090b0f0c190b010e06042403050d 65
    0x200341650060102d8151742e11000a00e4580d21180c506901514900ea10a0000e82000c1030100c1c592485034030454000381e0032514100c074862080c100c0c0d000c54400380501c240c0090700b0407007404010409011100380e010384040d000c40c1c440280381e61a44081340c03500051740040300300d01408003a6a01c44140c010400c0041d000d80340303640c80c0d5070350310400c0300c4911080e10b416516241c032200c5442c0a140702050144080202d030b01545010719055031259815204200703a80b54090b07016840f420400103503003a001d0040c2021405803a010124240e642d00c22990b9503000fa248500071081c0c0a4400f0045014840c1c0c0300071540b500441c000001d021b41540d010141000010320902500801046a9004040c0c08c603030011b0340c65091200403281030381c65801200c0781d0400000c0071201500c0711170080a895214800b51030020001091025100f15a850050003441c640b07030061050319000c81045400c58801000010100d0712803c41c90518a040003603101003040503002001802004d024041c03490303c1614110 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 488689064 1250 488687814 488687827
    0xf06190b030604091419050f0f0705150903031602030105010918140c0a030804090e060606072009131a0c0d090c050415080708070308070201050a12110405040e03 71
    0x1444503001c01801d4a00ca80e03210101c400070f00001d900302071091403041c1d094074520408204488008450201d0442c1c081c880c2000c006054400495110318004008010f40000d91604040080c4208400a2504034080410004080b03980400c014203d070400c0141d040141c000d940105421204164021140c090400d50506200f04405070102c403a65804075130b5540c40111110380c2032400c0381e2541602e07044240f80d90b021007031000410242085954028040c0081071440250340e0300da04096891a40001e0184480b400091004c00259402400102a2241280300e0000684000000c0d51041d1000340400a4001440110907544078800e503035001c3c50580d4200120030440c00d20030f2040440c1038580c2c558608e401c1201660a0f43d0040000500500c10844003c01c0c3c26500c1c07030f03184558409882444c00c0014014000720b201c80440390410409814607041c0e80042d0740c1d6500400043c0b0803c03086102d1944070032018800e41001c58030003010a034135141040107000841d256403190760305550091004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 488690314 1250 488689064 488689079
    0x3251a0d1b1106150103150e01060c0c120b070c080d09080c061506160302012a110c060f09010c0f06050a0c090509070c030210050f10150e01080907030b0f0619 70
    0x444c1c603c0d50b000e180010341c0304080b0350250307851242500014a42d03219a000040d0896002c8042c0c4680c501822040c409296922486113500020250050a03250900005035001d4080e0007c9007040d070054006614020a68a8800480321099030442e04400b02007000c5042c1c4004000711035000c206925030100c41601080050102d006509003800b20107141d806031005c0503c00e41094180704070098040448200c078545040f02004040c3d944800510188110148038800281c01e9015000207080c4510345440000180304079841103d400e410f2100b80b221f03d40006030754203800c034441e5010300c50000b854188002d0a40075203196101e420104071009409009513035694010a8003c031650070a2031112a407890103a05103403d40c0400d4801c01d00d400d041059601d080c115161089400754000b585003138444d94000b02c0b002d0002c405034000f820042e60348a03194000da41e400e40001e0060200c81801d51741c0e0b640d6000e00130045940b41d460f00360074400d0000604054202500b0200e04180d040d2009080c00309 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 488691564 1250 488690314 488690341
    0xc060806030a120315030f1703010e04080d23011e0b1801180807030606170a0f140d1716080a0f0603060903050903251a0d1b1106 57
    0xc081c1802141c101c00544844c0607501c02e000c0c816243c00708001c0f082d502c1c00e00350b0000c11402030030f403100304015001c480c200754080c0032203040e0ba58407548101c05451715285c0b1903864200340032035018640e80314000031900b0201c5d500b05013031814403003103070f503103507040920030034419161919a09802084c01000e01598880e03400303407481d803d07509140c0d804045417400106e526215404044111042425000c100f034100414100c0543e0f0150005000c0d02d41d44034060038815a90034500c10043e041111000b0000300d0302c01c20101c034075008010300311640340400412403d00343c0d41c6040001203401603a500007143c0d13507034448035440641c440845040804605015000050003070204180942d1041c4010a803030b10713a44594055a08450b040280842c00d01c1e001d0141c3c1d000d090994468070450040d40d141c682e9854100d40032111a04800d40300034540680d01620080d2184040985201031040e10300c6010640700e40c0d102c054440074012954903800e500505035104148105980382c010b181000703080c0703000a4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 488692814 1250 488691564 488691583
    0x30f070f030b0f2403090706030e0604020607020d031e0210052511030f0a0309020301050604110f0702040b040c0c03081608130501020909010609140603100b07050a05190c06080603 79
    0x250000c00b091502c5a640c0b0070504148500c0d41001383c00700610a0043c40040c04006071640b5803001c12101d0044240107aa800c021a4001c1d07002e00100480350040c05c14038440c508803486820003030341c80300000c4412b10320745041a24020043c1e101c4107091807000e03641d00500350440910240c010004040c41e0150303414181d111000702c140141c040d001e0000c00c808000b101c850031070398420340c0e854801002c40100a840d00090684c031039800d210104119282a205401801c401002003525003403103c4100c1c081c0760050301099038402e60700d24081171292564001c02100703850310380d00c18a0101c001c1c6070281403140081d00742845000d600800040140c1c0250140350011244490810961502c0c54190f02a21614400b25000010f01000040043e00b00a0050903240f03031942034914081c1307120a0040f90b02044a03032508101b0614810456411250000e060881c0140c0c10348403442111380380e092400d00701410090003c0c1d051008035041c084141d21f000c01400307a40c9000022810711000099542d107144 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 488694064 1250 488692814 488692819
    0x41d010b120a06051e090304030b010509191a0a09020d05011d270d030b100e09040b040606050d05030a260f060402041503020c1b0919020f030f070f030b0f 68
    0x44c00482c00b6503200419600e14842c00307426801540c40d060344460385a8105101c1180e2202d540d500114440c9044400980b00d82030002c040400a681074580201821220507903000300b03007810000c00e240d525240d0555001e44103002e00569908080c00740e1404964051344408a0320050710146110401e00050300740c2c0000f00d0f0700640e4006416500202c0048040e01408a042e200f0400d8090425030940c00400c0350f840708032000803804005180644101c1110075004d0b81c8024a00c0c001000a5000f200e82904140038010014100752508041007031518004016505503202042510350160b100352000d50142020340e40c3c0070b1550078818120310400014200e18aa06440301c0011040d0710380398142c400410090f03014079800c0c940608081d009612016101030f1138000da1104c00d0b550010070940001e130160141480c1002c6e41d801e10114150318044424407401a020800b1030400301100c8041e50050001030070420140c144010301501120390105103d041c1410189501066514480140d4003004203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 488695314 1250 488694064 488694071
    0x50a0506090a200f040f0510050604121704081905070b04140d0201171005030606100906080403050c0723090c030c09010c0f052104080601090e010209041d010b120a06 73
    0x14a0004090b0020084c03500c0d0014070b85898403960308055040030380039903000c0c00051091a00c2d041445864800c5001c0d1307800000c2d042140c180003c001500c282c0e11960942100342c1065110f285060402e540c0c0c56a500c03070103485100c100706000092120b2402810101f01b81850b20b0324001c489240940c0704085644180b034507424860969010300c5000d0382c0300100505190281c6000054403031a50141e0080c01c1c02449440005840703070074833085c04408185280c54844cc8103151001c02c41d491000100205c0801009200b0001e10303460070000f1034060600300d90a200301e20503404401140300c00c00c20440d40b080e00440240120120340d0011280c0021042401969441902c0d0058445103520040140b65003201c0ca814801d01c04085088428522442d10701c003131410040005a030140214000c2c1007180e04040010081c4010300d60104130907002c00c45c00903050245582c001011103407610030003800b0704000c4508180c098002c1c85819044182112648824545c207580303280e1303841700c08000404040c0ea = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 488696564 1250 488695314 488695373
    0xb0a050705070e01062a0c080601090e01090b1b0f0705031e28030204030503030c04090b01360306020307030911030307080f0906040e04050309030c150a08071b050a0506090a 76
    0x110b00d0b002c2e46d105600103104000e807580d00d0300308aa603080c091144842c40741c0703014070480c40c0380d006020321b02c0c88a07040313840340c8170540740c6d002e81c0c0385490700c40086000d03203000c10844401904404800342c03000a001e40003551f210344041810f691866035032041140c0c2081c017003006201644c000e141103400722070100524061503100d071405400034030807504007031710510000c4200203d00030003100030810741e0410402404803401140054a004d1400000c20058580301360700700c082c1c4c0e41c251880c83e0f511008002040c2d03215550f9200c5000300d9009681c11800aa02d480100c0700340896446100100c0350107400035446e00c030041c5c440c0c0d10382d401140d40102d44c0c0c00340003402208035525001903e02600910a04001030b092a24200380e4035407003880418001d000d81400c19500c1e141220f151070280304012602850030103051021140424010041401d110101524286100218210040ca0751040c0c00408600000d82000d1749010001810904254880401600000c210700100034003240d50301400240c120 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 488697814 1250 488696564 488696627
    0xb100602120c030d2d060f06210b010512040f0c17070905090703020303040f030b10151206090507050d141501121e09021e0f060706060b0a050705070e0106 68
    0x1c0c02440800b00405030800011a17259440381d4101c89210080c0d203001035440c0d009407241c4418044405443c5000e00700c0c000055100d4102036049032052426610300182039400c3e0f24112000e40307085d80c244154205220410640150a80140544410402003003007200304891351070351540070f8910b0389501c070000700d529404204202c00140d03600509403a141d984440c80d09011405910003600c4584001c1c1c046040008030340d44c800300b501c01c41c0b2949194107405e5842954900c155804d09a04190340703000011300005e240c0b0915000d1000d07035480942d141c03010f12140c01914207420402180ea040d89080c0134000c45250820301040000f03007484000007100540d0320006080303101000c2081203481c00002104442503025541c803d1007207031005a107000c6042800c42d241059400d8607004041c000382180985801005029210711070180480c0c4a919512010140d803c07101c46140400c80205101c020002c5c14003040d07000e0544008805419890030400502c0044c1c82d031020440119003a84078008903 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 488699064 1250 488697814 488697851
    0x60b1b0c130e070506070302160b0f04121a040b01050415050d020d0c09060b04050a06050702090f0a0e030d0203060103060806071704061119020607050f040311010504030b100602120c030d 82
    0x90130003d00960f207810041c203000c2d44590020700c40190341c032001c0101295001224041d0b5112107a11000103040c42c2c00d04140d42c80034103400b1b4041c0c40d9084884c00000102d5411854944268030030b0007491810752501d000e11041d200003003030791600204100401d000b142c0b9608564014035404032100c52501c20035080002c8000781c5600002d1869042030f401240c42e0300360b000100103c84c010380360740a4569542c10111050300520100952007148400841c100f26400118550090741c204070004009070f0541c0c6007031859000301c09081c500fa8012040000365a014410380300180710300e0b00902254030b01000c00030101d80c1002c803844800080c140c08a002c5c401544c0c400042085071001559545101d170b030040107240c2580702180d00602c03e0303200180c481885001500c03c8400491a011300b050308542d10541c698a000e458141009828040003000c5003800c40070324000c40104248400b0789080800c02070408188401784006080f0404c007802640c80000f08403500001c0c203050000c0c9004900ca440b6441d07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 488700314 1250 488699064 488699069
    0x1409042403030305100902040b09010c050705180118050105030a0803070e120c040c0504060c1403090a0608010905060a0b07151d1b0307050d08030703020d060b1b0c130e07 75
    0xe0540420022003050307015807025000d944825510304c0b08903500c03c6c0202c242d1280e801201c10380034050111040c1c0354040d8254a601038411400d40360541c3d180c0c404251542c3c0c000b070040c083d10240800401c180e015240a2282d0602c40308020b004a44c10803021950b10844a04010311034000000014440b6100310407081103104001d190400780c1c92445102c60380c2c2c2c01007500c00784c03255103412521000103000c0e00494086034841c0e01c6d00c0c0d0790441940c07182407402403200001c03600d50200b00842d01160b0743e640041c00c050601e580b20300c0c842e941008502d608075a0000c0c2542d005401ca07a20074005045808151040158010101400c800e1414864400390030121076003000e80c14400040503080e00003080b60385400c84001e08420601240f0420903a40c0c100e00c1c0b04403074101160b05003010100e50042c004507440451030030003510385401c5124160444500380e001d007441010205603980030300d400b20303903500720a9042c40040400f070325148001110024100c2c2c0e80d495450740d40004524014040c03080000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 488701564 1250 488700314 488700371
    0x518160c05010f09020111010902012a0c080a1202010c2015090303091501050603060405090715020a020f1008060405060409080c03090102010501080604120e210c010906140904 77
    0x1040c0f0310090705101038050039500701d000c1070655080c02c0d8014014070405070100e4050759905606220110b0a5940240748046110380300d12a18442e00800c426000c258010145c0740c00901000342142420766000709002c050808690409114502d401e40c0503440a0440b8980b201d04944564164091880c000d21282d00401c83d00c90641006001030021020310f100340c0304401076414000310340d8002035011000340100da501000500105002c4c0c101944096841080402142d44441c0c59503d0011403040c0c085110300184c4c05411100704600704040044a040010390b0400302040c10300d040507080c02c10083c200c0e8082d035940c0c00020450341d41c81e003040d01700c0c81d004085aa40c1782c4412122980300d0b440103a4182c00340d07003001b000040d00c000c00280e0512880d0403100c804015200781e40c0c1214000b0654032415405042c0048203441c0700b4211180074000008003004008042085001510b40744480d4050800c0c06802c1c001200903103a50400c8603101c1d00c2c05c40d40041c03024501c0a449440245c04400d118 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 488702814 1250 488701564 488701571
    0x80a090f0501060501090f0b0d150f080609150c090f0a15080604060e07120906060f0e07030c08061003180f051b0306100303030e0708010e030409060518160c0501 71
    0xe040c840c06501540650300c0070703a1071211311501c0c0c0c404128014264403449420480030000e614026075a40c0c0416a807092605015416a940b051003a50307030302d500d80041220740c00003800d0081e95070b07003040700c804203403c0d031714825190307291810800c01d05004958100b4010100c1924840c15075441c5433075000609440c4215032000c01050b180140030f0369003160700d140200c0c5060030104002c04c1d0984402c2c0306841540d84c605c51203041c00182d10150119090450300c2c2511313040d02144100340e450320310014050440071603580307103889a40181518000c2058905128281342030100a03102e5807a052034800041c00c01088000c0740b03000c1585629080e0002410090312904001c0800070003040102d8164001048035141d4060a0304054482e08180d4a11001070100381040001038000d40107034084012030402c0c1c85880c3e03524040942503c018110a030201e4100280a0100030342620918014102c00c2e90001c60340c240d070002c80c46500c4000303005a0503444005035074480c40740c4504980ca54103a8010000d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 488704064 1250 488702814 488702843
    0x1c0e01090b0301180e0f061b040302100807021507020705120f160e0705040b09041d0604051e07080a03030e031c0501210b010302090a0905030c0705010906051801080a09 74
    0x4201d15814544103074101405c04c140c10103078401c005100c4024030700001c040c11103a100c6030281c909911801100400022061000201507510b9080c0343d0000701494652240500d4065002400e2031102100c186000d01e4200503c40e01c15400139811050750400c3c1e8090313990000e0000064940100340d910401503103e0401c05c1350000c4200c401507001c0741c1981c6003030451a02c0d462003da480c1d02441c0112040b100c41403010318054138043c0c006081d030281c2b0800e0046142c0345040100c0c100541243c4c20340c1c4641c440102980034a40c003d2950340860108009411b44c5824101030300c2d240c0745111005820181c0360440701e04d08038000c1c01200c0c5100c0ea1300c022405020050600c400103084240708170540713000140741c5a8403000803000143d8080d80d00c00070041480c0e085600700a01c05c000548402c0342d043d03031a05102c0000f081007004005804000004040440c501400140700100603045942040001d020034001400d02c08900403140300c090030142004e80c0c502144500030000101c5c050f25203802082c12 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 488705314 1250 488704064 488704079
    0x408010905102a050a0e0d21020118110a0b1902120c0a0312150306090b011403030307080c09040c08101703070f0c0302030f1e1c0e01090b0301 63
    0x2500c0c40944082091000450b003180310500220f01841844503d0f0b2008030404410b40300358002d01003060ba034144010035600880c049800300e03511a200f00d03101049840e86481c420f40c518070101030006c084c40207000e101d0440d1208414541862001000c1c500c0c0940085031076901e00c8501c0c80a064501c81060720703640f003000040c0780d040e400a00e5002500400b00124407050122045404c82c00041c4c0040c90300d5045903504468007424002011042540c0300c42c0019980070300c031030030030045001d0700b0302040d1701e8800e04000b1218001a4005103000145031031a804030f403408001e585c4d200b100350405e01020307690031004050900c90300500a5200d444c08020b04030032600314010a0103088820008603210f5196141c4c1d450300c100221800c241c1e64018442d81c00041c40d9240382c020704900c1580b00c2055160f5076400703e840d0503d03404a00c0c3e40ea230454607211484803001402d801e00410508010301e1080540c1b8441c1e00b01035031100114040200e04442d5440c00c0e40501001001040e949040c1581e85d0381d207448 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 488706564 1250 488705314 488705323
    0xe0f030316020a081204050c04150512070e1b0903150a0b090702070b1b01150e0a05060607080a03150312020d021b0d030c0606060807030509010207030c080a02030408010905 76
    0x208640395001c0104005800c03840010b005212680c01815149401c8918044070b079a624024400c031494855048544241d803168024101c10500c1e0b40043c4001d81d0602080010004142038281015444034104001d000b06811110b43c10540d407014000105408241e8603000d0f01c40da40c2e2458051040155003005096103004441c8245010903081080d84031034001c0049410055075000016807214806001c01007005006081e03500000810000ba031030301e410401e0039900214145403148520303d80420181005a0845620002f0318000b00704901e014400240c4078007a188001c0e00d01c0401040010030640260700c043e41c00080f99040030310540e138a1400d14007c503100000a80103000d110740848500d80000344580c840e0002c0080310302041414814800500d8401d64103404001c180300050780811250720400d4003400072a030b2407054500c1c04400c041d003075031400b0b0070030304080c3c0c4104405800309910803000480304d54010109603844901d07071000c910358060342e00714044a510708040101081070005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 488707814 1250 488706564 488706571
    0x30f07033c050c0f06180f030a05070605060d2f040b01080a0e0a0c0e1f0305100b01030f0f05060f0103023c0a0323060a06030b040e0f0303 61
    0x240c0c118808461640e010180d000394900712551000000c0d503440c1050081001e0000c0c03c66100480f40c0420020a00c24501141903a81d0101041207207501c000040c0203100034401030802c1d000840c60f01c8481d8200404a206040c00906026076642c049600ca9451543c4000400e40142405055411501c10507003c0b95218405401c80c40d03510302e4001060803d40038180351b004050b15481856079038032502c480540004c1c547e000941c040d41c1d4400c800541500f10100141507c6031b045000c5203404207941c002d0724510f9110740030420501c8000c1000410000d25214101d04900c000b041e10300c25580164064140b001d403008909040c4003448940d019141e0066110308411100c2440111840f00158220320a0400e54616610f41404450510006114090a1030388070500002c01d03900c0102c0f06c4c407944d00a401003200181d2110321380114a03406d0181c0410307491441405c40418200f01002a65000a92250b00c05258403008581c02c030b50741d07540c000c994414012080d1090200c19078040390b1a0760007103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 488709064 1250 488707814 488707847
    0xe0a0303050a030b0306101701020906072118090209120106060f03050a090503040501110a0c0e060f011805010f05041e030209100302090106050306040209030d0503010f140f12030f0703 81
    0x828440341c1c45d00044442c0907035014960304020509121442403501100032181100399000c1040301c810f510b4581c010314002e406200546080f100c00494580301c082c22882100410071188981c003000d0350011302580807900b4480d00181c0d2625600702107080d1a4034107943c103545520b401000544d07550003007598000400c05503400c01881d650311012500702c1d10325010152855105000511455000d05010b58251428400300d6104c1812175448020300d190540001c000c01c0b0381c11080c4049130509040405550310300f401c050581c41007049050a0750b100f54070400c2e04200d072071110100c5060144040700c0240402c40e12421803412900c40440c01d40d450b038882280501088000568035261561500b016a81c3c020b010701c50716441d00301c0890fa1500003402596005500300448a1144d804002e680403605d12074807910384944c50803034111450341c010f40c001c280c041d43c1c0900c540c82941d0341040b01781c1000030842d80703000380d0042d2802036460350041c0e6220207030107080000d80c032042c0741e0014000d40500456 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 488710314 1250 488709064 488709071
    0x6132a02010b1f0f050d0f060f090203090604060510081006050307080304080a080901110604060e01050601171911030a0506130b01021b0303091e1f020607050304030e0a0303050a03 79
    0x280790a10000500f11a42024045010005080c0c101d129101045908809243c0541811500001c0030100ca81400009141c6075641710304001c0c3c2401c01c9211402012840070071401c0d454001402600c420005000805069980000900414441d82d145018152170030444a684003c5441940100064047e05100780705000340010203845c00000c6800340c6440300c3c05081c489125a0b22520141c01017059141030040304451404210030030020144158001e03003000c5030108aa4a0407421240702a08081c108008008240d10581241e401c0c550080034075064820040e0303901c07040300d0003031807083d400c6d039a03020001044c0f090710305858005034044d05003102e075200c030041c051540108640c0b2140f0707800d001d6000100120702ca40d81141c541c2e003603040003605880c41c1a61100c00580000b1810720192102010241c0c00711103400c2c4010641810303045c015884d0304c03100201c0d401039550100241030804000e00040080d04141c03051151323000018000d08000b2905440e40340140050b003000c5008070020780f4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 488711564 1250 488710314 488710331
    0xc2612060411030601020709051306020703032009030c0d02040e0114040309151233030c0f080c10090504050c040501081018020f160f02090c0703050306132a0201 71
    0x42d8220707401104160000d058980c0381506043c0500401040d0803001100c1d44500404580c0300c0c001003c985100e507800040164001d0740d20540044017100005040106204903155601d00080320200b40710110381c0c4860b004038502c0058054442c82031810150b50900d01400d2070550030140c4540118407a44444080e0744c0c903500c4203030089280103c100c2c0080c45004051a64032003e902c07881d0140c844440c59040180500195441c071648861660ba060003850400c000340f03d035410003900034100b00920002003500d04901c10782e46850444145105000410a107806180140c2d240402440090000d01261900300d0000000790014410140890340c6480020520300500d40c10400b030301d0941001908088000070744800039001803c00180c0703428200103403582d642d1081c42c0c0451042c0720b41c0c0743e01031048a6105003d50440060700c030380d4405400348002c0000942103010359902c904156a25600501200e0072440900840411740440440001500c0071480c0480d00c61039210045400074081c560 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 488712814 1250 488711564 488711591
    0x9040603050d0212270f09010609061b080306280f260604080c07031b0302040b06070c030204091109090c0306010503150610021c02030c060708070c26120604 69
    0x8503d201850b003d40103071030a030102d002c03a281d603141c6400c40644030304146c0c094440441d070315580c2a0420404100b24000800440c3d0b070195110207000c000e4079240400607519510b44109002c050442c620940100c41c0109801d07100140c040117510841c3c064030180740d40c07004281d91910560140b2115003c4082030804056420803050003420b80d614000c1c2401e039159200c0100680003000c0b1140320340151080000414000c211410b90034000c526800345003441c41c4108001c6602d910090741c0034610a00c140c0000c43c81044015080301d40507503000c03030302d8005494024150b0711000c213003561081c1e03084280803001c000000c0c4d18071518006c1d0102d0300543d80703490415640390004810030f0000c599603400908641050300ba25060316007a0b00488035481501040040c2c410900341c0e03424011390000c181900d408500b0003401d5088071041c00c0c04001403c01840c001c0c120200d2440181045009050280d9143c9203940c16580d2402896001c1c2e440b40b6400c8400c5038001c5080cac5505104c2c5050080904081 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 488714064 1250 488712814 488712817
    0xc170c072c04021f02102408060106020303130203010f0908071a091f060f030f0302070608060d030c050c13060906080d081611060a0203180105060114090609040603050d0212 76
    0x381d4000b06198050303a4030310312055000700e5104d00071085000d01002d44e51b1019841c000c4481c0800070001c2e28040c0c3d004040da82c5502c02d41030740701400e031741d0204004204103a0040b046a41282c4100f184030503255a42c0042405018007240141c000c601d000c04000a211548001d00007007846061380d44011051240c1d44006101c00b52818086904030030710001d020702c0005160507000300401404102e0558801c154010103c25500589655004446031000c0642c10300c41e40c0050300c4927041403001402c040c1c3c041b43d5803803c0f1809c000c06110002d8003142c18800d08221030100801d0040510100400aa00c6040607116921400030f642d170404001051031940464100b00071009642c903c4510b80e80c0041c00e0492100c80b01c0c604061000d03840e691080c00d0000c0c0f02c140d00c103604051004d6034a08003114039030551080038800314001d91414041c4007840c1c2c1c0c01364580700c00607003030307440b441d00c1e0741075180080d000b8400c43c074066174490f01e084c0b400410400003003002007065669800b5502c40211070521503005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 488715314 1250 488714064 488714071
    0x605031b01080112032102120705120105090603030c0106060e03100b06030606090a090e01050f01050d0f080d1401031103070b04210c091a0301060f03030c170c072c 72
    0x4100b0440040c001010440081e0340454001d02c2c1c070038000b12a0420b0126880300010580007095000101d0040c45a0422215a0414400d00d00180313402003400003c5a500e030180035581c07160b1280d4020030b002c2e5804009582d4001d600070020400380d6502ca401030a03a00b0b00b410080c2c080d008400d40c49a21101a100d1154020320145c442c41c80d60b0350340d10400155500480040b40d0000403404042007210b580d101e1140d400c0215000010705040801c030728449035205a115521403100000c0d40b07800541d042070004041580881020f40340d60120340900060000d50404000c90003100c400003003884604001000c020314280d041c0c03400252640c01561140c0b166005007112000d420383c504041b1029600380045a50043e0b02d11003040362980701c01c0c1c040e5224001c03599070303103140302110141610f02807090800500c0149200300c101071640c0d038054110421540060301c07075100300c4c0e001c80c1c0d800c4440d001c943c600400352040e1040e00340c4031a0070a5201400300a0b26610f520380c03040d04a5501a1058420301 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 488716564 1250 488715314 488715317
    0x90603030e101803121b0f0b070509030a03050301090e0c090c0703052b1512020603041e080304050d050a05040b030a0908030109020403050c03010b06250b0106030605031b01 76
    0x1c1ca031441052040002640b2030000810680e81d0020b1001c02001003500007840c41035405503002c011a0000400d00740e0745c074007404811041d9075107550000d011b000c2041c40c0316a0242c468030050380c3c3e40209840034043d42880e1500342c0038100c0b607a820554850011416207004110802c000d0052a076080d554490803031903190498503d038007061111480b00003910b0007a2083c60217515010084000011425210040440301c61800450710314851040c01003100660110217001d4100b860148002680c172200b0002902580300040418203100d0020701802c1d00a45000c4080c145065601c1c02e04002d6008071402c3d14036000703210041c09090320a00849070009401d5032000d06007401c000101d8402e130310103031074400c445a0b100f1702c0c040080c0e8079001550003064100030050301d99146062071420300b1900142136103e40d15003c4807000c1c4d50ba400741901d681411440140402c0c41805208404042085101803d00e2010000005081e03034180c01030b030103840054003a2a02d000b00e03c4040380c8000b0280c1c0c007050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 488717814 1250 488716564 488716577
    0x90305070b0c0f0c010e012010020a030e0c010212130512150901050603060a0c050d0504380f0907030b1603060501050a1d010306030828050c03031b0f0a0e090109060303 74
    0x11642c07165101c901b00282600d807102c4090001d5003082d2500105550340c0d0415500440c032f1080407034052003100800c01d03103440a080340849483c0000d444003100c54103180e0041002c29101414038244072000050a005407545011050040c10781d030340c0c0c011a11041000c81009000141c500a060007075070300490b805002804180c4444500c0e4024140c071440d1101085410300c5842018051401400e0186025191a51405000390340000e12040400d030b00707020101d47ca094001031421100c004590000c1042048441a100c4034030042c00c2c90325903400680040b40302000d00c00040c045503000610449503071410461555520010358a0b8050218400040ba81c1c2010b802000894030b1885051880c051600203640c9850750784400080d0000b026940006c10f84030643c48180110421301100c200181c2019401c021a40e000e032556072100801420040c1c007408400c04111a140301580d1183c05400c54054490046503401841015041c28a500c100d0341140001003040c007a00c07501e800d49415540b030a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 488719064 1250 488717814 488717837
    0x815191a0a0906142512170105040e0c0303030a02040f060f0e0f041b020f0f030705070b0903070902280513030f110d081c0605100807090305070b0c0f0c01 68
    0x5444100c4c0c02c1340a0405104100131040198a85054212042c110140710441c50f2489040103002140c2d440c640740c0502c40ca5034543d000d0ba600c1c03040040d0469800316404640400c0c4070140c5420140600d40e12030b054070022050110103c40b5801902c1a01c103650349840c403141e5205811980070804c00e80a40120701c00001d220309604044003108000d040150020610340d8030307400f007410041c0ca0300d0010300058000c0001001c16040506c04800b034503002c00d000394145201a110192111410702c0390740890100028603104a490a018a40c002d0005c0ca000710741303602d100406e2403040e02c2160090410601e420b030312012440d0280040d81c500f100221407140710b07542582d45d509450700c21100c0135030300b41d240cac1c0320b4030b451035990032548841c0540b02e62a403603151051002c2003e0405411115022184e0a21300280901d48904403c14203030b803442e2814078019140e041065401d081150800740c00d601440b4000300781c004904001b080c401d0741140440f8040e1070441d882603201e000c040c010781d0000c3c1008490 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 488720314 1250 488719064 488719067
    0xe0703111e0c070302130905010609060803450306161b06140c040807080604120f0302160605010812040f090c021501141201090c060815191a0a0906 65
    0xb50901d010800b04072405191681c0010344941407030311140010507110025001040b000b070251030020000c0c40b0040c4a00d5003032030122501d0f4040c015103a44942c003901c3c2c100c2039400300c05542075411f8510307415803050301d04243c40c0b81301441e40d00034007103000f4407509010a82200c15512072840803000c2e50b41e0b500c0c100c944035800c074a5400c81e0f20f00130f42e8400d44428014018845510101d40168541c4012668891409107050f040c0455644000c8168009504000c0410980c40342640c0d611002d18102c0701464800b6400e4000340614400461010040c00c9403100b00130090740014142c0308860101c500c075892001000c0800d2107103000c1c50204400300352040080300c1003500074a0743c020b2140151500442c844403e411203400992103082c0021000d104981207017061780c2801c840d220f003a0024002000c4644a84020483c54469102086500400560050240b40ca620030b0180024600a214680313940304030940003043c00b502e0001604020a2640164400d00311862210551a00b18107580340c06030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 488721564 1250 488720314 488720317
    0x903230a0f081b1c23011d06010305270a15060812070f0b0a020a0305010e07051209030c01090302032a070b0f07020a03060207120807020a150212010e0703111e 70
    0x182c4c2c1803809901c01e00c18015803000d00860204100c3c91040d0301913500342c52016608148107a0250249508441c040c4c2014021034401e0380d80440207080101c0e031500c4031108854000d40100300c2200880c0d582c403081200e2100800d080000c94010b10894014050100b400003c46e405071240c030745213074850b8202c0381c100c0c401d400141220724001c4051000d0109242c0340c141080e64115210000c3c0340d0300042500320160588101c41c007505000044002c549044800540144101e280c5000d20000400002c0c8504004004072040d00e1900c03070090220308000c0c81c01030b540c0c0c0c0011051501c1710418507040015007041400c110b00c0e11f420100184151031a044000318242d101a01c400ca114104000d10005030b2216000f103030086204440043c1e6880003030820014555000c078000003003100d40410b01014640c0012066038107a00003a030f03280488010b445203402441180103590409840500000c2c5803103c072055180300c0c41c10f50f142800081c00c0800350041c64802d001c1c4415019902d9000e01002218200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 488722814 1250 488721564 488721577
    0x5160b160501060b03090a0605010f051e12033f1f05270601030501030203060a0209030a0b010e0f070908060c0702030f0106030813050906090105040903230a0f081b 72
    0x74000646640c5408480d1001d51044551401a900c40c146190400c54180f04450041c84c9680420021a0a140005035013160340181418000082034110344e10f5950100444681804036003101e41e103c0c3c0102c12000c9000b5000c3c00c0c6100101080648642c5204142d142c400b9920049201d000a41e0b580304c42ca802080700c0c04504204602409000c1031700c3e1185410411807440010309950300c054440e5038501000801040c40341014140301c01040140c0300002c841e82c0211a1000243e03ea241c0900813a04d45010b0340300280400060100006204000c3d03010a0300400800003065459547e410b000d4941903824811980300f507202c3c10020740480c144801410420340b0040c03d680c40d0070144602e40782510300a410542d0580d4002030b100042c40b80321b9200000400040d40c45000520700381002907003841052150300e00a41d203030040e00d0f08062207069915134502c90442c102d44464140d002a0410360072003c2d0240200750660780007c1d0103800b4040382032060b20351060f0b0303d40340190b2441700b800a17002761 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 488724064 1250 488722814 488722823
    0x1050c07030503180601060903060c020a050a1e08040902090108160c030f050904020703020f010c021911010e030d0903031704020d030c03030213290c0303072609060405160b16 77
    0x4001c150407000d03007801900c6c020110f41c0c2d682d07512a03003981000d500301c4840b49014000d5500500c4038800141d008900c0e81c40c4030750002041d100c10000c040c40c0303c09081c0d0030100203000c88000200480d44071407a0740a000540310aa88011450740c1d081008001e9081c0c410b41380c80820154440f050010384200003281411700749150681c140345102010405a0308410811805a0802c00c03864440d400244902d4901542c40d10003440328160484201c0810550702c0c00c00341c02d8411000341d80c50107074080d50072441c1d201405402c9898401c45a6801002e00b88240170031000149240c24454020444603101c60045030010866400082e103550195031031502e4003403c03802d054081c0441d000400b0080341d09001407122840d01030301c0c905c0e9603c0c0005110759241d040e1212250500c148051040000281c96203c40e0a01308924012a0760018184000145208030300880b04030040003861500400c03a24000c5110310100d4480c05200c0841640076840e50003904418401849225903080f0903080600126018 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 488725314 1250 488724064 488724091
    0x1b0e041b09020d0911011e050d061203111b0609220f061a0307050306190302191403010603110409060f0e03030103020120071505120106120c0201050c07030503 70
    0x850700358030280c0e04814400c0c0030395581c49a888052040150001210320024039210324000c0a01c00b1a24105440880e1501000004283c1c401d65140990000c0c001c1c0810365442a80b548882c85e00421707a1000c0e24400302d6038090765980c004600300c00c5640a08100300100540d0078803030328009100d40511030b0035228008144101400c01c6588e030324030841030031940d001030200e521400d048000462903840703142d000480d0030400070000c860342d002080d2604070000310f40080300081c040d604082c41c64110307003004c2d5110052580e40b50011001d004400308446000c00003100b0006a50101801c98001d4407002c7c021005802509071603140a5010a0030a8800d01e00002e0340c2d0780210b42a4102c1e4622840d9030015400000103105543e0000000c44c4018211450013480d011961459034075801d151048180c90080d030000401e6040c000c0c0709903000d8941c49291b080e00c560351250010311182c60080301e00c941600d440c200c0800d0703600c10b0181c240b1800e0310301c02540c40c283c21a50221100c0d4001000c201c0c14181 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 488726564 1250 488725314 488725319
    0x703020a170309120c060402040b0316090c030506010216090c030e01090609140604260d020c013617130306051e060f010f030f0e03071b0e041b 63
    0xa0000440303441d0041a14075101c2c50300101c1c091070b0940d00b0840003580709041c0a1042515000a8000d45c060760544010a000311075030701003803030103c4148074000002c1241002295642c81c40c2d1202c0741a11407036409100c1038075884016030b111100400c0740e189040640c00c040c4403c0b403a03070f04100c03004003582c42d0003d290b50407040694211038161a08a508903200c1c01c6d00030502c464100d080d000707070f100c0c20301030000c03030801da1346407489045401c900f500c0c101c41803458114141a0841a180c80c1c840d11001555103001e5602100d009000e4102e041130490070440c1d94020b003081c0c103170b442c000141c189201c01c0a4140c02d62102004403141c0c0594a0740c03801d0812070341045415600388d10005502c1410042a14101400c0003d614121808480c4010701d08004000d85603854440c2803070490403e007445000103103e000210064008c1c91122042142001c0d800040703808004000c08103507000d03034041c0400300e042161284440c0c0252044c205d60308100d0020070041a1401d8001840880d000f0350805140c3d03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 488727814 1250 488726564 488726573
    0xe07111c0207080d0305090a030c020f06030405011d06071211090d120e03010b0a030b040204060503190611040e061c02030a060203090c0301051b0a030905151e090705060703020a 78
    0x4040c81402030058100034000c1245510030404001481c9050a09100b00c1c60b141400310b580700c03d001000750070803943c10300c00e005644510240c0591058090070195480c64141803241c06803044003444055061172100d87c100003900421781a00409a035501d032840011629444005041c4510181e10084410040b001640c0e032002c0301c0141551207044903001c80c0e80103d401504200080c554140a6410443c0318655a03947d12041030540764003500700c0c402c1f52951b0001c900104042d401c115014130032510300a1024070305014034062a4803034032061244405503003071400d26001e43d101d026070690030300012404130301c4c25488084825400315614a012030181d00040d00c0c0100010040d0707125940001808468441482520034015081e0002e01403810011098401592a81140100d102c00820411281031094000d82c4000f0340210803506d01c076002c484107284060096a171400d03e0804000c14400705a80d08840500c541400b00c040c041d100d00c0c0000780300381d650200000f1030450050030307120750014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 488729064 1250 488727814 488727853
    0x507120201180303111002070b0402090403030902030105090318030a1a0c0f1611010507020306150d0f15060510050a181e06030609090213231302010f090e0711 70
    0x10f5000c0c1c5e451010442244210030306162403c2c003100b0306180104003a030081030050345d066400c50750503541407170301d40d5586c20210018004107400030352550821341400700300329000020300950803d40c0c3c0d80c84013074000c0f403007010b503546008203004250f41210300e6012a4401090320301d03607101020030341a0f45014941d4402000ca45e01a500c08070092880342c2c0351105000790a26001d0009901717003840c0349400d5507500040d5440c50001c1010081d51b030030701e02445940c0c8035407840b5500c00d60702000803102000f5038078050100700c140b00240d1003d140341a900242c2403070410282e4030b103e007458403102c1c07500c40c581c2130407950b099170110006c80012410700001038551550308181c000301c00d42031310300c030701d272410311000a0584a42c4e0b070000c007082d82001d802c5005a40c40392821050380c05076480000305071190300760502044200d040c03088501500f2104011a00303020503640512a03200b6070750201d0701d40d440441a02c11003074500a040d62013a1300e80005900a000b488a81d03d0106103034119104150f1081a1001a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 488730314 1250 488729064 488729069
    0xf0907031b0f080a0e0c0f062104020f030303010e1b16030512090d020d200109080c07080d0503040b040323040915120f06060302060d050f070309050712020118 70
    0x103070822101d16010750b4440d20160300402484002d10003505e4607801956611540340500e481400201c0c011001603840c402140c40d50480c2001e10501041c81c0020801c02500072a02680510b81040810b00a80340120440c1e050b1801e200140340d1a8407440032000540007201c0204841c80404c10210000031105565071806500c00d90701d455039019030070102008544054984003040e40300000343ca4443d600441c0e1140030b407103103180200e289414200c1c400d68020503403011400075442e0001260920803c0c0700240b214601000c110340d42c135a5200c154540d103401c1703141d10000154040c400700d8002034100c0f850f140c02c903019207041b106055000d2100d00f01c21500701c2505442410024003003100c2ea0303660095115a07800c042c0600b01c036034034000c2030316409234440d04000d2410b250301c1044803c01005a0046000e141c01070308498076420070001440c0248010754404082010b2540000e0065200e400f600340c0555200c0c014004680c80c11400d1101603401407812814408040306449450300ca82c0101c800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 488731564 1250 488730314 488730317
    0xe0c0a0c0f03142803051005010509062514030301081b041d0f010c0206060a15110709060f0806060f1212030a02030f06090112080a0c050d09050418020f0907031b 71
    0x2513240039072426030300d060720460040082c507092101300103044450f12441c1c1c2c1158800e08280b81e48203150340014220384100c10f000b454115144010b0007544040d858070040071482903113005a1418010201d070360303901003407041c948568000d44484180c070b241140347c2004020090700210b8517414000d4003640030524982c0c0c0c900740340d00448139202000400d008414a01400b400640001e04005021520300c8000380208414080254004a062449282007403070001030030041d00c0b00d00c0d48400f00c88001c0c1440d0722405079185d07101040481c1c00031002c00d4860203080c008009000c0e902c0140c050184c03204000b0540040c0d40200c155842c042c000e400001c61042449200050b960301d00800c0c18100c862010304024050541a0014486113519045170889241c011442035101c64000f8800c40c0c820202c58002460b07409208062003145401c0140003041c0d6804450621a80c0c0068000300310301e192480c00a9881245640c0c0e990050600c8140300c3d811103410301c1d01090314903101d030075400202c40d1a0209030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 488732814 1250 488731564 488731597
    0x30b04022b09030c020d050f0a05151608040609150c031d07030510181410050f2703040f1818020d02010f0c060608070e0c0a0c0f0314 59
    0x10141902221014101d140014082141a40c0c0342c40040c800305840074001e000324002c90a40c014424100001201040004211840e5030301030f2034465201c50b01902d4075640310b1405004920140014600e40610005954901280750340c0d5880d0000541203810098600180300d190180040810703014000075848142c5010500d841c00c0c0d00c4242585c8841d0440ea0469008000d0034800580007050140300800d1400c0c001c900c841c903542480e140382c440101d00418141c1034807070503941840049170f034132110301c1c0d00c103020000f950311200d810104c0003049800d05088141d0a12030701ca4035041c084150318815514045900f080c1e1590842e4510240d5500002296601c031101106c005489010b20001e12250507207840040c00190301042c490354410724001c1c144110307200080c2d105407140030780c4010190010703024001030b035480010f10344034035071030103103800c42010240000c100000a2086802d040c1c010b60301d0840141c515280c10182c000c900321301700d003004007580130400f01502080c0030f800c00c0c15644c221303003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 488734064 1250 488732814 488732857
    0x309060c09050a05040501050109030b0405070b07030c02090f010b0a030e030909090c03100926090d060f11090603040809190b090a050d0b07050903010f0501140a05090f010501050901030b0402 84
    0x1108140980c1c1c1301c0b910842c1014018007540c5d901507800422a54010302440c1552558500036040109941040d0302880d00460110185688030300c02d200000e000352450b42140c3c94242007560143c0c0d003400b442090080c108052046a482503004d420702c44030240a4070b04000c0a140000c54204085d21120310503402021008c00f00d180500c00c0540b4507200c20400c224030100d95070f43e002d081c40d0389d24148040008030302600c41503200e05000c40b1600c9500902d0108811241d20708a401454501c8120142c0d034903003e1710140313981070b81d01103401c1a00014100350071070b0f4940e82c40258680c0046002380d0004d07548810b0500200398004040094003142c2010307603d0301d250f4820b00c002000103612803440758849803948c1c004250754050315034000350140340c030594900c008400f00e070140080d07400c070300ca86900d84000040c0d06009440003186185040304c54050b1a941e942c208100d4020070b80b4083d009a0804004200b03641c0514010180d45006050116050406030001012a04080e02c02140098101c440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 488735314 1250 488734064 488734069
    0x160305120414010c021f0309050c0105040503100507090b070c060e0f010f3b100c02090a0c0903210807230721050406020111030403080c0a0309060c0905 67
    0x10804462500a8460a10b45041002542840402889418007045241c03800940d00c40d10340b1643c40300d494100c3d00c81e200c100c881000300207200481003580c15000d51640c020196104004540071242c00030010041c04105841c410002c000241c803040c1400a115000200c0755400c0010f411854000d00039816294035000014001480f424545e602c90051656000b0340383e0780101030340c5444410361030304910103071110310340c49200c595100340d210710310801525208200d441c420a020250805950340310b00c2c2400c0303500a40d0100c6d50448002c2d03201e8920000140082aa076204905015451a1401e0080e03a203843e030341c01610201401c0040040c07072018015216030403c9030640c206140d860003148034a46801412aa44200d03c250750f81006d00042c800107100c0f4095000c0e50816121118000c20074114030050425806482151b01550074940710003440455801941d10aa4140d198041036664003030100e4155413100940c8003c1c15921402140402c80501c1948802d40941d1543c003c41c9042608 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 488736564 1250 488735314 488735323
    0x6020a05070510080f071101020d021c020a09120501090209040b090c01171b0f0c0a1b03080d050a021b071406040812091309080310090e0c120f160305 66
    0x401400341c1080502c1103242c13903010078160352000600c052604a900c07080c5080341e4041e0101070301c131a590300100c3c5801c03044c581580204400c100f445003058214203403841910a81c01410156000b1803005982004084a80b42030141c0041c0b0610000860503444d50014554030019541a00c40310498030030840b0500c400c00c90408e004209007071a80d00ca100803006800716060080604401c3d1041000004508111034140e070701b041180d22500e42c0300c08850b00415030705c0c401500d0136a042d2000450382c40b4401540019042034036040a203503403814520800d004080c1102428640a0540c2003008038640010482a8011407000b00040e08000c2c1c54070002e42c9010180c6c940e00c601c0b600c0d0411080011341000140131002c80e603110b0070710b07031200d0180f0000b40601070302959030507045013000f9a40041000c00d10043d4425098440c940758041d03111501c1d50100c4240c1ca822a001c0e60041401d94030501d400150790a4110070079044603903001d5500305da58103145e2a0a4040c038114450030382401006410f01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 488737814 1250 488736564 488736569
    0x14160b061c0f02010e04200c1c0905041a040e0d0f110c040e1e01020a0305070504080303072a030309060c05130b090301060e07020a020a080f030403290106020a0507 72
    0x41c0700c8031200395030b519009040b1298410003030600c5159082501d00c3c0e2100c0d00210442c0001021040190450201070040c40c0c0c0400101c451034020901d6088102c0d12044a10f128480c9981e01c005090b420401444000d00303010f030303005a5035424520414010b603141c0c06000f503202d40210140c9004248103030f002e009001070f40c0d502021720640000031b80340458000341d1101d90140c01c60300414010030340046103081c05501e050311020701800c040504000d4005400504449609035000c100700d0b9510182200c03d4000c60144c0302c0e864008001103010715215140442940481a00032030700c6000c04110050031541d021802c4000c00c1c0c03500b58100500c11107100b004500c400707a05001e0b2900200200740c0382c40d8103043c058a40303d17120120302c5003104c1d01c0c01d511400c00340c8403140c102c001d10300f407415001e580c0d0100e00c10100e101b0b211011020442c01c40200c1c0790b01e41c1404200085050900310750b00d200d0214180d440081c4000300004940c8070321304d446c6180c0c500810464000e81a04101414101e00b001c403184c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 488739064 1250 488737814 488737849
    0x1c02071a071202070c0815011508010e043f021209030a0308090114010609440309030d0e091501020a1104150b0a030e01180314160b06 59
    0x80d0410040980203840c04900c41c65035000180c0e5600b0b1840c220031507183d00c0c0c000580e6440b50380c11070302c0303c00f0110400506841e2004500240407000d8502218903c00901602c0f500c0e1240c0b40218000440301011040301501b2035018050403418034500702201140340110f081002126444803d0160701482052810302000a1042c82d000d020340109640b641d81c2d6200400300801d40b40040c44110080d448901c01d60300252860781d07a96954807008000b00490700842c2c40d02d5a03c032184000c2d0000c91b200000d01d18141a80310361040200c000e10100d00142c10140d00c0050004000c041443e41e03007800040c80380052529900822240076040c02005140240556140c2124241c80c0340240c1e00002c2c0d904007280d2103644420007031400000b1901500d10080c10321115100008042800129000a400c0d1052255420480c070080d2202e50741c240c400581110101540001c02000468810aa000043c1c542c060142d450003c80070b61131064200f2030300f401e403010760b0b005050064914000240d803540e00c614 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 488740314 1250 488739064 488739113
    0x1501020609030f0c3a17180a081201290708070312020307030902030c04090f08090d0c0b070c05040506062d0c15070201060e070c05031c0207 62
    0x644280742d600c0c03207105480080c0000108400da000e400801805107080c5100751940d0003c60140c20048444481042c2044c039003190420012a00707100d10001d411b80c091400c83c2d038071a512600043d07040700341c2c60b125207842405030358208000304500c43c0091500c1d07960880940d61641c5011f248081d28003070710080c1100603082c0031503008018184400d9a001715040014030780d8646442c50180d401c03451425941d446d132800807041061a0707800d54004a00d42d4000c1c0c007603034600014002000200c0b2116080100850304500700c0c3c001040d071681c041d00c5403040c0541111403080041d11002f4440801d50700540140c01e0029802c001c00414002140003440143d60900c81d60400c4400203880d40031713900e13400c8641c0e1115010001132080800d0b0070115003880e88011035940000c00020358035542c4082d030708a00401c070640850a5244144109800c540059001020700e4031103a4085400c881c160034141e41500c818441b018421200803039100b240c0740e111750010781d90000c3d854080400244404505916800d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 488741564 1250 488740314 488740321
    0xd080405120f07030305061f170f01051c02210a030e03010212010504091506060309060501080a080f030403090306060608041202011e0902190605040509012133020315010206 76
    0x1802c01a10301c4964142400700b030560701c1b0300201d60802603494000e5a11030010585d6080c8507008403c0c0c0100c891118500c07401c59540115032006c0540030301c48d55400004030103841c0400041d07c48000c009038401403528044000d10107200a03080c0405405940319080352140108043d00040035400c4560305400a600f010a00d000c000084201445541e004507240c40100080202031004010380417050b0504100c039940310a4014020700354140121011071a100020812030400260301c01c5041c1d00115141c90600c00300710194040e04050320450070b004041038040006480344c000c00d0007402550b03482c00300740e1070035003080c5406099500801c0b080d64909064101da2582c03640d98107020358609035010950222910204014400070b000c20941c82c0d0724183e0205d90303c4d034054024022a00210340307044569032104440724818082812041c50190b540f00d410b00004c0c5404450010340082c05d0003001c4000c034221401060401c1e242c642c03001d4660020401206030802884000c8959080c80202074528 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 488742814 1250 488741564 488741587
    0x7050702091e090d03060504021801031805031c1d0714010917010510050603090709051e07030903110f030f0705070f080c0307091a10050c0d08040512 66
    0x8665480a40104440000520800e40045a0b0010303584900b9500c041031801c42c40c655240d00b18120440002414040300050510340b90080e0b403840d084131a4484044110384c0d00641c018024210308041c250b01d0409040301042d018030143c030083c0503013140020641c06011001c0203d41d120405144800c0c0074680b0343c1d00b003250004030b55040c0c5200100440d40c0d036541034016121100268003400301284980b41d0b200d814401900414028955580701e0ba030a66155400c03c04107000461300c584460744808820040e03d02c66401c62508000440008660f100c03046145408201d0101c41c9000426203840000003090b40c0800d0309101a00c950024200e041c00f00080b2685078400e410880252010114451040c0481804000e004103044d1001d24a4a5a2080132031349900304400454401e008081c0c00150100c2d5501030f04402000445a001030041540c04101091142803078500c00c002090201c504006810008003071100207903154420545400d14002e4500b81c4856441c92507104148415281103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 488744064 1250 488742814 488742817
    0x7080c0408100c110d11070f03120c031403010801090c0e070c020111100501081e0304060e13091e23060c030a0b061201061806020c0631080d080705 65
    0x4074002c004140c40480741021a0702d038610a108490f00d005420707655030601d4111001c1041c204020083e50115070b52500d4140c0100700c1c501c00a0070000e00d03541d40306401ca21883c541311000344603061141d60f03178054155811030f58009800c94601c6a548042c84021300c07101c080d081000303000194000000d841e1003400282404d4045100030706100d2280c6c00c0d80c0c0e8004090201540c0c460112000304465030f034601000e0f0f911b00c2e18905603005000392140000c4030081c0030044405131b8002d521018007050276001800440c0f12000400054680c1e41c510301c1001400103401440100051007106019100a0800800c00407403c40000c26010000c2039110260700045000c590003410142416140d656001000018003100711072036510403000508070f42c0301c0c0c000d40c100034180e80156940403001520340c500305452034494040d00c0c025a11246442c141ca00d0160020100d1a00c58801f03400f4450500c4d00d18074682940070102003a0080c41e020510200c0340400582d820321440d45040c40c2d180c1421880603003207 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 488745314 1250 488744064 488744083
    0x10816020d0e0a080a0602190c020109050d0204020d0c0f030c0e0f040504080d050103030f1e0c0b090c0d12080601020604080409051305060a0f050606040503060f130f03020607080c0408 81
    0x103214400035081c80b81d9607042d4421000308031210503035000e01040e1924000940c0a1a4aa6001e04114580400d13a0784140050078a40d90f068484a0030035040800700001d8002502040340d006030200200c2140c040076008460b001c1d42c030b03511140c00c048841c2801409450a03a2200030812507c0314401c1c22903901c813091590b0208090740c1c0042c0329181c0b810007900d244100c009210709903060000000c01c059200502d820000302079503610420301c482d0f00004109414490002002484501c80000494000c006180e000791051085404100800000c1303100c0003140402070307031034140581d0341a110582290303910303034814004d00c050700e460300e415900d541c0c0c24025802800b442940c1e841c00115440340690740600b03801d801c0812030700c0c2c914040898002030078040105160305801c04003c0395413802c1c90301c00d0f24190b0304004c024080a544950014140c0a0b00402124001540c200c0440101e0b00d010b41d0b100074507000e54080d00d507a14180d0006444a140070385a4449404200000c05c0800d502080380b0741c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 488746564 1250 488745314 488745317
    0x18041b0e01141e0703020f03040b04090b04020c03120901060f08100f0c1b0203010603022d0108070f030510211a04080702060c070e0907050f04020306090f0c0c03030114010816020d 79
    0x4540031a402c5c124981084120790107014840001c3c04a0281000400390048424001c0d043c400003255000f0b01c030990042d003c8400b0385a00500803c40401c21401c5159407006c400800051420b640f80d4484001480503030003240303e50481c50b0309462010300c41c0219240405034002c103029101031000300a0003580c0320140f91109001c140816021941c00317400880c02503400902911002049111103214820424010844080250540d9146502611445104044586407946080284007003907003d000c00030914a86101c12401c003140b43c1040507507800c0c2100c1e100307120f00e016600d50300c0d040443e0240d6000e4000141210000c00c0002a005800c56503c6a816071740c00303483c2c1020815407840c1c007185e904035015141c407880420940080010f072946c12140c084403490108000542800202c0c402518000d811400040c0022044447c402455401c040c00031440c0346040b40d049562415500203803c03d14110b120020000c829603031095499801048080403000c2041c0324480182d42d03502011410310 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 488747814 1250 488746564 488746567
    0x406021c06170c090f18032101051f090b0f04030b0a150819150f0501080c030c0906060d021c02031f080d080711160305030a02010c09080318041b0e01141e 68
    0x30641b40620550300010040c1314600b0030385904800301031a4040c24043c050081a1501d8440c01940a204100c48141307101d840740c031400703070500202d000250f0140805001e100c508200c0040040e940c1e81c0c1eaa403044103204000240c0300c140d42c998003080d46d0198070000f0158420f540000d08000e003900c00b400c0f9203922403000c103141640c0002000c041c200b08180e5403405444c1000000349000003040d00f044200d01101661250031407030041041605081c0c0e9810340001d028454601480780f01e038000e0240ca00002516091403441c103c1c0c4000343e0303000319131900e2552106860f1990760341202190901a0980d100508050f0710502c0d00105101c10081500d41046a05509a051a003052040f00640c1451448550f40251a401c01d95603a6115080e1040150b00e002048030b40c1521a0002c441271743d0f03a00c00603501d020507a02a098140c6058800d0a6129544282c1743d40d0306d402e11f01c0007800101060726110301303000c4000005007112001c1448241c0c050b20411562903000000303442505021121149507 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 488749064 1250 488747814 488747851
    0x1612050403030e0f0604150c09050d0201030605091305070b090d0209060f030304062d0c060b0310090b04060e061501031503020d08040e01050402040e0406021c06170c090f 75
    0x21400351188683d02daa250082d40c0b0300e512241c02c0850018400da01510100d8901518416800129001d2040c0140018104481401145004c1240c03841c1c0500515021444a450b40d00081c9188000d488500c00041012a64020401d003440507400520401c14018100b0407120701041ca10030010600034030881c101800152566944928244602400750449442d0f03500d450340648812200b10340c50001d500c0403e6029a8a283d150030341c3c00346c0c6c00c0d0f9611a4201d0103070742d5480020b0300c4082081681030043c0b20703010f079040d41a84035081245000e00040c4a09042034242a4203d422010003200a038110b5410007075000d0182c000300000c07000c03c2c40c00180004070912040301a48258100035401180c1c400c3e2601400b6550000e8001d417045010030340038690fa60420001244614030a50090a42c00d0000502042450303001c0d043c5400c56500d028500d0301d1030848942294816003104003161107004900c100710104001a0450000a54502d00e5606107800b44504100004102074007034180044903 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 488750314 1250 488749064 488749067
    0x2030121020d05030d15090501030201020d1404094d0f0f0f0310080f120901030b040e07060306060c0b0604050601050f130510020a0c090c0201110301090f051612050403 74
    0x40841e02c50f00403007600d889181003181000a401c00c0e00808200725030444000c104da0949100c0d46d41241d50580040803052040642510340032f00c1e444c4da490b001281400b001a817a012806007554902c030a00b811548511208403500603650220404030803030301400114403614500d0000f94400c284511400740d1105010080e0500b584100131080210030300c0071480703c90074020000914000c030321070b040c0000d4440d00e89814a85c5d40d400225801020703030050351180e07014545000200040b030701c10324000c80c0b010683e00100d03066900058086589a0087c1c40c2082229498460000608040d02d40140e040035661140010480003401c842c0c80340307546030701040443c0c0c040c40454541c1480510201d4440282031030500c00304005221b15030040c5903000403040f040c0e2000c1000300b0322540c807101092519041006400040062841000541d0b6070303407807205155904200558000d00e4a00d40100b21881112010002d490020300000010b004044051078030030b82140342d1854074892103500140710342c0d032400c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 488751564 1250 488750314 488750329
    0xe06040f09020304062009040f092907020109080d020d0212040602070c0e070c060905030c070320040e0a0f030e0607081e0a020705091803040b1c0203012102 69
    0x46812040366050004207002190042c40c441e501a0008100541201284840700c01c8400c1d40d44040b004100f104445516040d880400340782c0c3d200c8000114100c49903621580c806551640700110102d601061000d40001152503500803204d01c000c1c0188000c81c0d60303001c201c2c010300d051410b0154010a81c0d90985405a0588030526826002408075003041d0800d88000d41c007144095840201080e00401d1014405500e240590a603a541d031128001c1070b02e13101c0080003410000c4070a8001048104a84170040050714040c601580b100001c0301c3c109962103010921029800c1d02403810040000184080410781c4010183c01203180805000307541b1b0111000d040c10594690b01200201c3e1507010300840078060034060700d241700c2e01d1408107000d00f9a00c0c0c9a0141400c070400580c010710090005080c00d0213a542c200c01084806207241c40b000ca20141580c01540004c0c1d411140465280c0021103100c00d50b0601d40d980200841c55075041a44440c05e00c0024020002402c80c0f00d40b8080443d250b404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 488752814 1250 488751564 488751569
    0x402031803160302061005060304080c07051e03070e070512250c0b150a06050c0309030a1217041104020f1e0307032306040b0d14030702010906030c0c030e0604 70
    0x50550b9a41c84038600c0041000e018000154010f1040c1000204a0100d615460041c0c0d40c004010f181513558541d10312490740d202c100d040355980114840003980c2c0e101c01c01290041e005120b02500f400c2d504005041c944000350740f00c200301d05c0d61082031055a03070f0403004442031403039261084180c5540390070290305002c12001e03d09145180001040f4030250784440c0181e511740c810b02036a0510303240c0f414900c46030010301089a60144000e4800c11405004074005e0040c6d0103040181da091190150010341001041c107c02c0c0c4414000411303c40d84542c4c402c0080c480d4091052000e9102e0802d038644154101b940d01c0034034086c581c00698201d2105036a41a03c4010818005049012a544102030020340040e1008c4001c2400d082c91014020040414a001c0500c2000c49000546e610020032028088041041c0d801200003002c00e8081f4041384003500a840c0c114009560303c03100f5100040c14584a9400b200c10185480c40306039403954040c501407511034141c07900c8068110600f00103000b80c440e0340d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 488754064 1250 488752814 488752861
    0x1a1e0d080a0f08010e040213020a0905040213050103110708160c08030703020c01030c03110910051201080303011508010e04030c0501240f08070302090a05220305031501140405040203 80
    0x4070318541d01e03650140141c80c5015036a55060850b90b07035242600641d10703042d20001e601030b801e91003106602c000b40d80034201003c068540300c401c06560b4070200703049910000c9814a07071580c1c400f040c080795806010b105040072403458070b0f92800071942c4400000d806200901c20142405004580074000411300e40d0001e04102816203540d408245000383d5142c0100c0c001c2e40c003003030600380380c4e1045078083d02c20003c140e00188251403400d040c0704204206a8600400e000920805010060030031107c0d9040c1c0e4083c0080030700540c2d80b941800c0d60000c030102240923040420003010010b001c4002160501904550302d401c09400000403490894050201001807401004034400c0041c08040c1c02001c5108072040807000c07004150312002c4051321031600c0d000282d00550580c0c00704844407070650010742e00c8810f00000500840860329803110f810405501500040c42c0442809070110100c100d0800441090801e120700001c422528920750240d84941d501c240d50100000b00e081551042c00c201007000c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 488755314 1250 488754064 488754067
    0x18040b060a0c03030b0a0602070303031d0a050303010305060c1804091703070903020a290a140a1d0415050f030a0f0b01031b0602060c0d0219050c011a1e0d08 69
    0x1007072030003042240d16000a0380080d0602d590311005041210150040d01d4a95000d06401e50030764030f0075005002000d2003981d08003030081d42400c14020a000e91100745100e00040c0d65a540340d800c02c9454444041e0400e031001000b040400a00b1980c1c095054000c001a0340100d202000e0381007407038002c140840200c40b8007a0010800500700d07032013070b5084252842150b0750a00c264480025199891000c80555100b80d0640035044645c04503802901b10545980f4010100201a0301500c03000e8201c660003d0124070609902c0242500c0d10710b94241c81201618100107122510310400c102d0301d83c5104031801080a003280d040151410f0041c1c8a810380c00c070b01e206480b65490f1404102c0f0107401d10090710b5a01c41070070750141042c80c0c02c901c002101da0950040c900d6031030f100348801840d1302c0750141000c541e81c2001390a89210b1700b12402c007009116070f143d0580740d8602510315400e40e4800318000203000b140340c075150350b19903c0c55060707070300a0513411084044078500360100340180e014001c007800320b040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 488756564 1250 488755314 488755327
    0x81f150320090c1e09060706090f0501060815070e0102150a09020604080a03080705071a101e0611070305030d151205010f15030f12143c18040b06 64
    0x18041c2c010114199071111007040081d6005552030b0178082d10000c1c55010741c08000070701c00324006800c8842d40600400000134000f81503904d040c21100c580d4001e00550b00320005e80c60615400c0451aa400085414980b1700001070000003500d400c00320422001c0304e92068042205903183d031b0701440d8842e40c0034001d00e0b600c036220b103401d95548000100480005219400042090748140261002ca55010301250300455400c01d1b100e01150000301020249580303100c0006a10f140c00b041040f1074000c4400007490503080c280c009041c0045809080c2280d88400f00410004400004455900c0d400750f42c000b030607a0074a0f0200170000c4c00e0f588158080b006469030681070200662100d0000418001704200ea442c103a00d611005c041680310113132458019860640c04a00c4800004034241000c1c035101d03000e4003d44109a5450304402c12602c1c00201113150300800d10074021896000d115660070751000d01c0300008880381d20b445090b40e40c0b81000c01003252001c0319259030304280180c1c0030081c038a40c1c0307440c1c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 488757814 1250 488756564 488756581
    0x1f0b04090f051803030721090605180303070203041e0b030906011d070801051c05070f17032503180311100305010b0d0902011404081f15032009 63
    0x4410007040340c10500d0310002c14240c10b5070070249400d40032038074042c50841d904c4030400e4030000c0b1103164050308070040003101c90080c4101d102c1d807045144562000141c50804204011083c41d404490420a61003001072001c601d400005130303400c543d0525a070903d44002d003501c40310500720540c403e0904050110511150880104045050b03c186114080202c140c4004c03115421a055820f0f0b00466102070060000d400c00c00032508140c2d022602c0352317404480d640d43e40fa04c0c100040c0d2041c140c68030411011b0040100c000c481404282400000350b0030016144d840c40c40b0088090f00402400c0400e6506000b090f029603241940d98071120040c4401c0d955900b000c4030040b5441206034032030510300070340b814410702038410700d4141d81c1100c50303060a0001114000d001459030510980c1400b808150b2401304041c20310042001c1d01c403040140c03211040301107a941c400220007030307000001c41c205152000544000000c52048030b0700005400980c286402035200c01207815640350350081510f00400140c0e4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 488759064 1250 488757814 488757821
    0xf010c060c08220b220f0b0603010b0603090c060901020a05011401090b0409052e050108160602150c030c0c031314010c030c08310504050105090402091f0b0409 70
    0x1807804104100305544040070301c04a0710f40160009000301e60250128240f03458840b5404d4081d030980282030362407507482d01d80b1050400c06117812114074111008000c01c0f42420b009451b1841c0066032a0750850030300a5415880d011450b40c62070203880c1c0864020103980c820881d03000080d03004002040302070f400c408800705060023401100c0b055403c0039602c0070103080c00d00c201400190003002411448984d000c1280c004103211145904e4400c001d0b5946840e84000d216060085c5404002818200c401c0c90042d02840103a034041c90540d006920302d0300a031103504040540c021406818541c0e260b595505880b0140140d883c0304401d4030012810f00c0703520b034004503030109503584000b0401421880d0320045500b0b0004040040004100440c140300081c06071010f85901449844400b0590120003512182070720f0302080c00501515110041129027058421280904401e4038104540d241ca0307000315401c1040540841034808990040d916003031000f80d0070701c001c2e0040305817007030761280d8034200e04016 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 488760314 1250 488759064 488759071
    0x807080307170c28091503020d05060303030610050c0a0b07120e010b010507081608030f184309020d0506060c0a030f020102040e0406060914040b060f010c060c08 71
    0x5000341c0403c0650381000259a4000344140e00d04110000d907060382c0b48010312400e20f00341842a40c800200c0c4101d04034800190120b495580143c80d0700c10345030000251000909200d00a8208009000b11600c4135842e07240c2c503061344e04110350f480e45050b01c02407074250404030103480c0141003000d00100c5a40040181c40c407404001c0d09201d94200400c06074221210041c10b1400300710100103482c0000c07034401c098000a840b81c0d080c89020f44c1c0c03c1e1160f07090340d030080750010400b106903c100803000100030301e000550340400c002031004000c1140ea01401250904280c102e4503004080508130b442d000220070745042d48152107103c3d541e0790b01c01610194200b007519000302410320300043c8690403c803060742c00844050005028614144d2419542e0713540c61181c22085540030480495481d501101c0d480c001d40c4140800600d1074503242811007150f65038013590300c180c0d10300030501c0007244481c0021900f0042c00c41e00701000c3c4e40072200580d01da000481004286500f0101a00c9001e5000b0340001d11 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 488761564 1250 488760314 488760347
    0x9050d03090812280206062106070807230301050105220314211e0d1806060b0a080c0c0a0b0c09030606031908090a051c0c0f0b160807080307 62
    0x9100a4031841c0d400340e401e04108440050740441700203002442c120200c1c1e017811a02c14841c602100e060320b1049d0400108451110200b40448280b04545500074803041c41e00116807860102d00400d0b10a0041d0341c8010300c285c40c100b00001c546094107819441000001504144640c91aa41d8a180c05004150803000054049c01106220000c48003400d40c3c1c18030151009000741d14040400744078646080d00f01c60059141081800089120030440c0f041c49944020740705508103050044c070b80f400544006421210b12034009119224210360000300e40d0f60020030303007412581c0340c2144010032482d0845405c005081c0c3e111001c2400a100441d030002c10800d2816410385445640c1c000078107075502c200c1003001006c00c0c0444405070102d05204003500c4c00c7c1200a041000c40f541d200e00080c91201032481c81d106952199066004001e219850640204500c0d0080170a05203400b01c0320b0070b1070080840200c031900300103c107841000107080440745126880030040b5201d04006600411080100001c3c62 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 488762814 1250 488761564 488761597
    0x10030303110903070302060a17090f060109020406050a031d16051503010303051204050a0c090221060112150302040204031202060108011407031d240a0b0109050d03090812 75
    0x400344901080b50074181014004000907469582440550b9200c03590b030340104144080d03401c00f442c1c1c3d20310b490383c0590160700c000d0210a603246000c0c0c3c20b003401a44043c40c004d10400c02004a2600710702a100081024280007813a200307035800445190360300d1003a001c02402500c40c50201c5485d4186c40e0000c1daa816a0b101034540000786c0c808a980c0720030f010260110f182809101c1c80d43c041240b481d64098401c0c015120b4200c2203503100c01e850003079a00404100346d004103510f0304407000074412000c0440040003c60050400318006000701000d06c0703d01c400540c84c1c0011100000540020300029a4098400c641d030720340d1783c1813200604010703c141c1d82c014098400005000141401214130501c501c1060104603102d1040071750040c400c0b0341e00c070b080074205004016010407043c007007090100300d0120280d01c40e070700d031601c440c1404400034602520945086244c50007643d0022001064403c2513456500c071007e642801c3e9500540341d44180e21364841c5001311241031828030040c000c9134030655102e030f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 488764064 1250 488762814 488762831
    0x1061806090b09010b0f1e12150306010b030604092d12020111120a0e0d0e0307082122060320030f0705030a0209040207210801031a10090510030303 65
    0x10422001c5c4a0703000214003d109900407494030800421140d0005112005804002d00d004401030704002c1381e5149442c9004e0420520b03540c40c0e01030b10705003901140980840d40c10088a200c05000c06404103004a9907810300d202000038500c15066411040d10200e9503050381e00e460005510540402102d8000c507554600403128014000c41d0b0f082006001150f00300812005500c1e020340300207000006803a2106090010601c050000750000c03c044e42c0d840c2028007000041c5880c280381c641c401d1119070300000048181800c40c0d668084041c1c410032a00e6500d10360851129506003560001c0b004140c81a80d0019185815900064000c6840065080c0605103035480380413a00044030040316000c40741d400501c40178811001145c0c40b402103040141814003131800b040481e00041c508440c4d014124a400000d0700f605680030702ca0a105140c50300b565815a40c41704495004030300740318043d200c840003086d02c1c550401485005440320545c00c01c92482c1100c1a11400c103150300c400d4001c245410000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 488765314 1250 488764064 488764069
    0x10b15131707150f05030406020a17240f0112050907051017010b0a0c26040b070215161b270f06050a1a0c191208060d020105070501061806090b 63
    0xb04242c84141d845c1c00d42150741d941c071a103001c0e5010070002c8017004004c215402171514a1440b05000e002c100c0c0006120840c1c10316020108140880b005101e0480c042401c80140c0e440000015100d00d04500450191250a0224500105500113551100130908000d4613642e00098500c014060b421204410342daa03200d01180e0f600c9042200c3c000104001c0490001c641041d000d14244003503d17003603115084424000c00081d400a8000ba0f0860000040d01c0007545003296452000022040d402e0745041c2540048129a0507a090010310509000514101e200c42d02051440202900c0f5485105803820039103e0100c0310080c40a5281103240c4544815504160f124040c2038504c0600301c40140c50510036461302130111039002c0c1c1c1e060340040000e02c1c503108081c0100c203040910103407030014400b11441c0469882081d8580202000120010003049a803460340c1c51540503020700f059540c0fa200e0303081960240180e6003106200000740f032040b10401e10b07039500c84011100c000e90f0400c000c40e0900304 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 488766564 1250 488765314 488765327
    0xf090c041802040507090b0307181e17010e030f0306180103150e191202101e09030203070f05060105030c040e030405191e1403010b1513170715 63
    0x440c0c1c04548400c4041001070420703600036a00001c0d44e0801c0040715035a1015030405a004403026800a0001d0000414038441682c012000d007211012407480b4a09a1290000c8891603110f0011810f41d03c46040d01001d07820742c8102001d91039041031b070369940c141c0480c40943ea4002d5542d60f009042c56121904240a8074401e00d040e80e0303100159002c405400007114003d440700081d1042640034404500d220041e018110120b014804c00500507840082200641008082000b150f800c5003800395806d03219084440c1e030039047c50380e0840090103100d1405d0880c0366001d500320051415000042035028030000081ca181282c1e42101161184560403082c80b06039140a1040c21040c0c2c010300040c88036141c01c0700c0c2c004a40ca48503809014495441010480d03495000316890300038000040c0512181840407a00081d18109030000d00503022824007040c10440c00751452000b0080c08030340e0740341e00c0156a4542005002c0e0039100c41d25040b10796041c0e0740703c0300503102d4062022103001001110078003510 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 488767814 1250 488766564 488766581
    0x30720010b030606040c0e060c01090c2306070c09140907060c03230705060708090d050c0c090417040602030d051806150d0804090b03010b03031603030915050f090c04 73
    0xd001c0c050f5a201c400502c4040c0c41480002c6080c00420044080c543e11087d018210300140c1c000049003405003414608200c02e607076000f40c5000d401e142801c01d407456414111260b000d00a496055444d0400d0400074085c04050b08000003c4d810f1920303503111107423558051801030380700f403043e01c1035955101c0301510103000142c0000c012803402c0b0750114200c0d0300c01c20310300c1c50086090341c01e61800c44207030f1741e4505041c0225294000b1071760000901003002001c100d8150a07007801d0411501d072004084025684070500381d0781912644d6035600203401c0105002481162160089005850340c2d21040040e4a0f074200d920a400c0f010b141c40006503101c00e842880d00c00988800c0c0140165490b54a0300280517040c0c0c0c1c0045400c0114642e1344000254010f00801c0103161880c000a40140504101400d448940d545507119074814030800301100f40040000c1c103241d901d814005908220740c6440100100c0c44070341d07040c030f1501c0d01c4100034810384c0044120b031281080c5001d558000010004200440d001c44 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 488769064 1250 488767814 488767819
    0x7120306140a14060d090b0f090601050604181104080309090f0c03130809030703060618090506011503090206070302010902180114060a05130b36150d02030720010b 72
    0x302d00030045650801c0e0741d409100c0028082a18080d1050003110588501510465440c00e0100c2007003030202000724031540040300c042c0a45210352400c4000782d400c1c0102e000e103022000710340c0040902c4038016800500102011041d840d21240e8440707507d40c41c0d41241c0150350007101c154000416103501100708a107d0040c81705101c2c11a258007400741c030f150840d12400c99514074204000307990b50703404014810085111300300c08140f603424500c811200358002180c503840c0394105002c0f04001600400d401d415101008400c4541341c0360349900f00c0c094100c103603020b904030900281100505a06411050140b80203840480e1611201c0058400c9054248111900e600305808800e0052a2010041401110500c0c020b410098805402203452005034005006e0980005e0700e50380c144281e0b9200b4980c05440c000c01005148417909911900e4002e8526030301c1441862403002804c00c001060303600c18482c440c1e00319120702d004071018059011440d0b80b2510000100c202c4085901c050080354080c1030007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 488770314 1250 488769064 488769079
    0x5060103291b0708130e0a24090e070b07080a03180c0b031302030607021b0607020a17160909021327230604020405090c150f0f0712030614 61
    0xc1060b042240c0d044900b0880c0c58840400440e4220b20b00c503030b010000340c0702011195540c1e00340034441b28100c5e1800200b80451809860081c03040d0480a41e01000300c480480002c2a8401000003c1d4203244164200f090800c102195810511130103d025194030f68503500c00300804a9900060b80410303011010041080300300c41010f201151103400519080854a07082000c00701455001904048049803181c0c0182d0210411494020341040781d41900681902c07010300d000c1c00f64000c00c0c203101480c002d20281005000300030b5006c001c1081401003240c239072200040d40783d0720789100401030003500406920680702503803541619895031064400e041400c402014040c3d0160040b20820b452190080d980c2c407007995407012500302074040e809850005031001d04480c0c50305104202c120b0f407001d0420092035110031910302468070784041d405200303040e00c160035846400c141d1803c00a4450095110001c7d440840c00104001c1444080b082190098a060000c25180c214484086007500e4010742d02c00d44 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 488771564 1250 488770314 488770351
    0xb0c250e0106050d0b0406060c0b0c16080919150f2a05010605030609010603030813021008040503090d030519030b3604080909070f0c110d0506010329 66
    0x10310003c0004d0310001c003020038491710313504c001000c550b80f0b41d0258002c1084a22130341c1c10881200701c0b403603200c48050211030900b5803040720503a510105084c001d00341500040c0742c2041740d80d002040301d00005410080b246942c0c4640c08800c40d002001106c0002c00d0154015000107030283c040c6625098410ba00c2e032200102e085188000207c1580307043e80c265684c0c2002084c1e40c4c4090041d988690340c00070011070820300c0d40c5002000c42200903d06c900001444815070b0050b9980030f071114440240786025407642c2c546042840c254071070f903804594421101642c040030150004003400000c03c10144006603003c0684040c0c0c2580c80c1c50032040d80c005505030943d6540204480c00092168007001445940c01c041e44081d02249130035241507884d0000411861464500040d089510131400d2905900c00c15a10b0800b03002d0594203000144a0304103280784c0b55450f2281c0131503011042d0400d003110400d507540c2c1030040c0743e1083e90120003441252011011048071050f1100c03802a800395a0f918000c3d070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 488772814 1250 488771564 488771567
    0x90809042f090306130308061c020904110a090b061e040f0602070e18060712110409050a1b080703020304060b0628180312140301080c0406060f05030615040b0c250e0106 74
    0x44c1c04c0d102000c04400c410b56a09c015031152000e4a200d940300f01007000540c40741d1010400151495403080340f2043c18000b90480a4032000141c6481409450421110f05542d58412a036805290021180340c0d4400d4400140c0a500194000c00c4528003070300c620840d100c1b100060700c032850740100c00c50703079500020129001500ca410140c4042c407441c1d01c0003a18491100c21034150f58010f80c40015010f07292014400b001e00c8510620305035070003d805039003921010500140005000403c0e0009050380400007a003849110b0300444004a0700400083d5655824490403100190075001010824000d400d111036050040100809048000c4410082c041c515074600341c0c1c1c0c8000ca00306c681080b1821045002d80c00e240c0000d14040c00340600908107501482040c0700c01c0302c1d0107500900c208031520000c40340b8036401c007048a03000701d0141e031452000060b00c010300502d440b1f603910003400380600140034424890301060036484081c1c2030800c43c443c905000309810550036140240c44250300b0000c010006035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 488774064 1250 488772814 488772829
    0x150c2606040e03120f01060203032505160b070905030102091302090a05030f030a02060c03070905040c030b0a0b040503060f01061b0c1802030702010b010201090809042f09030613030806 81
    0x3000200041000a1500c01203801c641050300d071001000803900500031500000e200640c0503028510045086103080385400840c007a03142c0280000d40d5032aa002c4038642d00c140300319403421340c3d000d405002c03103d89071a041100d102d00300c8924000035035000d0081028a4180210f81c0040401000d0742e222140c4000010002d6020006195024001100005446e20284602805140001c0246894451402c0084d00704400140032b251111070801c02c12249541248024007691415100081e08101c410016402043e2400d03020ba800200c8000001e200a140c200500c03d545003a01910110b4840200803610180c00780184c00100b04a105101ca41078540b0080203a000e0180c074841d0340c016591025010421071118001d40c000750000100070140307409000f2442144001e00c020083c452054490031480c5c014030000d81e20440d01d444050302c0c00a60a10012038445030342c480d40700e2080508010000c554081c0c499a40a8090400040c1c801d41220008500a80c1c05071201000d17613540400304a001c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 488775314 1250 488774064 488774071
    0x6061d01090806070806100801210303091b140d0803040209090a170d0b010e0904021003111c110f070f0609120206010623120702010b0d150c26 63
    0x4010100074005807484041001c03d020f020f15403520042c0d42081010301030640340c071032850f070107008035100104510183d500d031005e80c000401e248040c0d070540f5441c04802a04083c0c038007500d02c00000455102000030411940221000f07103030001940031100040c44070030701c2107900140500a0900c0020050306003c400070794003c800505079504071086980b4040e8505010701c80d039a4500012607031031120100e500c5035009600003400c110b40b50070315a000048450b14000e100900030010500e05031b0800d4020340107044441103d40744d0585601000c0d214205c20058070800038200d40c20002110540221030b0b040b207588803150882c2a1524015454044030900060400c4401c0f030345d110181070210315501161004200b040d1301800980d450301e0b0000b08200511200001c5041c0400f809065004910048a160240c0c2e00400740007176881400aa00422140b0751041c0c0000d103071071000041100d10441281000c912410400102e023840800f2070714440b520301041808030415000014260940364039560 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 488776564 1250 488775314 488775317
    0x122d07080604030203040303030f09020303160501020904060b0316030c090314070b0d090b0106020705030c1311030705041503051b0306030a15061701050f070c0c050411180406061d01 80
    0x55256909042031a20400301c03410f40c0140c201003010310406605000d1035000c0049241d05116015060b00004c0c1c40f40b04050600d0802d0558011f20b0f42013000a405507043c1101c011710400c1107a41d43d50a14449520445117440d800c0c00481d280541c0078000e1080f055454070076956006514199994101840e52424640110313104860f00013034812100b500070f1210004142c8081140082407419421040041e0010301c10741d04000814440c40c0c4001990366841c1108451158021606603d0b03a002040304188099400d03c00002704101650404001d0080300d00010741e00070041c464450031001c44901303981e07000345419182c1800140d9041d034405550000c3c030050a8524250b2207039201d401180c23280c200d144e04030303131a41070030410043c0481114190b084000000c0c0054503020351402c1048000801c400f0501c025a14000e0500456a104074040d00001e001001240e040e045401401d402c914051b00c210f40304000e0700c80e40d50415004071001c0341d407540c950100310f046041aa8001c1d200e20340e416030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 488777814 1250 488776564 488776573
    0x304050712052803020114010b0a0c0c051f260103032007090b10020a081902030d0e060609011d0f06010c060f0b0405061507060b04090609050c122d 65
    0x5051012014891841c203004a0a6480b41e003e203140c06401c2d5900c01100c02c1c6c2e044400340040000c401d14404846c1e20140038a444407440450385454807006006800241d080314800c148203c1c0d00008180140b8001e50680f00c8100030480c0b00070b488902500c215034001031b58005401000040d0044407891100d1800d010020703400e0f640c41008910f0312003168408000c1ea42c4510309040507040680300000800424030203080043c066445043c514422071210b00341d944803501c080c080c0684203005565008020b402c00340516645041d10695480307080e9001032080b80504000155400284141c09070039100f8100025907580d8211101d0312004000c1c1114140040840d00d100021800c1c0301c1c601c1010078110000814040300000e000c21264014841d502850300490388001e104104819200300c642e000e100440c03003910380d0303003c14080d00310028020902410314a420f0204400030401010b155020745114880400301449566140301003400c0107202003460095855039a0201600c19107158aa002c84 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 488779064 1250 488777814 488777833
    0x1120206161e03030c140403021003090b0c09180712201b060a0603030c0b1f180c050a1209170c0303090c0d020117060f031009020906030102030405071205 68
    0x1e42c2091204810a001d0758411041d00042542502c100b900c0c60f182e074030700944030902103100040350b88194000a031044180b90701d1800c03880d10035005402050b03440b1512030014244414101c006801c40c0004600c610903a403d80460212a070450781c0c403643c0d0316030b541e0100284050140008201140f0072840202d07681400807100303294100100400001011045000fa2010f0040343c01d20b2000307084412001c1c01d00104001203540401c2d0740460b1600103c40410b161501c07205000050f09011309103a100d140c480d00001c1115400119100c102e400309000d0001216444040318644600c014401c003140090007a20150301895201d059514455564071440784840b103110102908040c429140340d600010401c140d00c3c1c014888400701c6001920340b16655251640040c10030b82002c50303582e45000e03203130000030215554400c2c1018000c10190070b4612040b0115403c4c0064550010168000c1c00300e18041100c41c02c0510031244101d03001405070a401e0300b00000b1820b00641007005840034070981d2101c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 488780314 1250 488779064 488779073
    0x3010f1550150d0e060f06090c130b0d1a060423060f0403020109080c1003020d15080f0c01090b0307050a110106270905070501030507140c060604140112020616 70
    0x202980002411402074440040988401c04e446446030440d50b40d412400c240041856400303030160300b0a004846400d1039580c0d203400c100e0b090245403900da030404807404001640c0c84404009003030203c4a00d400740100c0c007060604482e09070070f400c680d50300301c1e00030841084140c902a8401c42169003150030305e40c030a618840026026046002c03900c1c8000800582001150f030416446001000601e028003008041c9038001087c9000e0f00d01c8000034141c00040c0720010b94159070000341603c0f102c0080150301c0f07840c0c840690340e503c20f1981141705c81c85054001c0c140c940c0070301c3c5214111614031040d00d2550b41c40d0302084030f094000105c3c01080c001d20043d00e2062440a010319806005003503e03170540902140145965841d445420842c002e2412107801d0210700041140e80070342d00300f82000726080c0c40c1d15504807004440840c48454200e0049844210100e011030200d0040101b01e5060040b03240c51448605001401c3c0728003422540700842c41d80040c01c1210260035003c1411075401004442c5499 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 488781564 1250 488780314 488780329
    0x2041d030d06080706080f0a020d0905190512250201030b0d050f010b041109091f0306050f060a210c09020301030303020a0807020303090c01080603010f1550 69
    0x1a20501c1c20740355141882030031402c00c400c000400300d03868036105900741540110780d001c0019000038032840e00000c0d0f001f10008203402c00390b20783e540f000c00c440e038080c0442800d00640c0e68180080760039004001d00d409027841c21a003540c244885145161100940c540c841c1c10b0842000c00e8203d05164a4030345540040c0d44110900142d1801140548084510010510700715034102c2e40e464030a81c6400720f400f480c42659800c2d0340301c0c800141c1d43c502ca2601c82c04901d034000c41c10a407510007c1c0030200404802c00c9100d4001034010180e0000403005500d4040c10054a002c40e030084aa401100c00704e010f990a05528410800c00c1c01410520482500c5824004c241c6e882600260b01007500010510181980510510b600c19030320f2000c0e50031420105040360b115140ca001c0103040155040104600e55001c3d800000c104613402c0d070400c5007655a1302e809084010720b108006851441a0b10084a100100b01041e500030031801100d01c1e01014100101c00c00c4a11082c0308010100c140d40282e003a00c5060 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 488782814 1250 488781564 488781577
    0xf0504030906020708071a030a0603020301020c03070201140c1203070306030501020a0905100320071415060114190302071410050a2a030c1211040f080303070c02041d03 74
    0x2541c01e00c0041c00c04102a02e80030465115400d95445030000b08040d0391400c4c0f2000c18404c2d00c440c07840c3d59856004190740a000a90800395243d44005101400928008000d028851007a2140401c00719208240d0440c1d0045401410054009030300c0c10404802240046074840c41609000078a00d46075101c40d03013243c0210702c6a0003c40c0c2c00712010b00191070800500c3c2d243c0c0c03580d840d0038045070040001c203030341c4031200341e60451200304045000327070420807502000440d0710054030413103441a003035030710041201030141d420701d001c5000604e0f420101c1004030111f95402c03842401d410400c00c03103e0400c4000b54040072061b40c0d0040303030303031900c4011000602840820804080c8080f80b681860011402203404a0502d5002564502c4240c034400c0311544412000c5603442c2000194088404000d44402140703451400759286010300c4400c1e41d038001400351081c3c500d810740c4202c1150711141105e940b48001e640c00d4010442c602c034241c0051038035401034903425002900840c044c03040c1c03284a529682202 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 488784064 1250 488782814 488782817
    0x51503180607082e03020108070c02150403020414090a02100e1008070e060a020606090c04170f010b04020423060d0c1e0206100311060702180906070f1202030405010f050403 76
    0x1000e01844c00100e02e5030311074001040c2030b00420311400781100c5030101c619200085c18000d40800080000c2c5c0212020080141c01038040140c02d140c1005040c1e00741d11a000403889203240406030001403200c5490f2a1007494074800a080500c05602000f1104417129051002c11284a0800c4402e03219202503424501480d00e8610380350400300800381090462190f400e0003880180034203112141d0004259070032242c2611403a00307039102c00c401241c10344101e40042401074100d1450b82154040000c0d02c440c02d0070b81c078000f002080d111404001c00d921403482410024154949c12042c00c240610f02c20303011400003414a0324014551f410038003560b00c10380281e00401d4100104501d000c103403030814040c0d013415202a201e03600e48541d8040d0807910034000a03004a692401c040302e40e494a0040302c018031b800522030f00c1c00c81120a000c1403868170403915504d060245a011840003400388500740c0506965454581c81410b0180381c050007500002d00a40351503480b128041449600d1344106402a4003e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 488785314 1250 488784064 488784077
    0x207060c030c110606010f0305060301020906130806010f1805060f10410d020f0d0920010f030b1801030822060233070306051801051503180607 63
    0x3400a003201103600c3c860380b055040384041004581c0d020600000750a203a00300080c40f9103540002c03a009010361658141c01130400116800c14040c47d0ba01c000c11a19004215a030700e82e02e5486004c036007040c520034070402070076103801e1540184135900015400f05000d0080300c0d0714030300c000029000c5018031003200c0120354400080c40d0768032200c02c1a07000d1b501e04c0e110a58190f8640291401c0090140e1444603d842c4022429240040990301109c5004c12005881607e03810000110b000500560f64203c079011205804020800c1c036044143c0100d20050311790b000415250903041d00944440d007982c1d507002816101e442a03004090400314080c1d4000c5101c0b42c0c940401c03030600543c80480002c1c0448140c2040c01c10011181d001881218030409015030402c0d011285010403080e0700304a0118044030740c4c5e02e0402c06045c0d41940400304980048607000901400320341c03100e98241d400e001d419008030740003107907102d40360300c1b007000b103800110340c1c21a903a4036440c100d00c15041080607a5004000f43c0c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 488786564 1250 488785314 488785331
    0x31e0203100b03040b010312020304030803010803030726010e1b0403120e03061308070c08010c030e0705040605132309030711102c0d05030d0e01110403060f0207060c03 74
    0x28151580094010801401c3c503508140e1602da5100320144002070400e5030040200d91400e10a03c05da074001c0d540902220744950f1035881458a03500201c4000000409040e41074154a00101e41500c40005c4981c0d040c0d8541d003001c1c03a60070718180050441900006440360240900c2060000304019030054201d07840050b102c0310014100d003d001c0506120741d01a50910482c0858010f03040c40082d401100990782e18503034500720200032002d50012245501e0100c00c482141d8140e0000c0c804100c107a003d98003060740718030400c4201e4049000301c0da00050f404c03000c140c8955895102074060402407040f500341d0081400200e4101904485440203034001160700010001c14980101c3c80078000c582c040350019011000510201940d0b200504505100b00c6c04446012191292150580c02070107504404800b82007041d0f0700e900c200704056013145400b42c800211070061103060304403008600091300e014a50748608010b001c51400740f01071281c1c200480b4001031450720402c2c07843c0380c16417404030b4540e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 488787814 1250 488786564 488786581
    0x1050906010e0610030c02010f0c0c0b16090b070c05030a03090e01090c0e010806190f030b150303030c0d14040f120905100f030e06041b090e0a060b01031e0203 70
    0x104182d1055040c0c07014041030051650340c072001012403080b01c1c54001503c4c106610100c0c050858060175602092030011000500d55110707007281042d5004180a86903030f101c01141d101804000c130180700000d045803205005c10803009000b40700c03490240c0c0030b16841a41b50000641041d10039030048000c00c45c0322400300a40410790000b01d00400a01c8010070460a1908000d4075409440e846941000301e070900041807652200e002c0104002000c0c40481c000d0f45800803040d420200780800c1c0c620f14805000952006401c1c02c241402c6600540070310700310340f101e84000b01c10350042d811541a0903181c4448541e84080c00280c0740c0314034003c0326940d14045940c100040c0413035040da00002003001841c0c00703008544648000408555003490241c1161110f4041200100641690750180b8010082444140803e001240280c414481440201240e99170500300c22115201d98243c400d0b0000b0721441c0208a4903407003078440842c18100840c42400c51245044054141c04140318996400f100380302848 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 488789064 1250 488787814 488787823
    0x306010315030215090a171c030e0111180a0f0501300501170a02031506031906020c0105070f0f031a0d06060e0619090f090b040b090d05042411070602010509 69
    0xc4c418407c02142a800b401810340d190b0100300410642c5052404400c0084c2e8400d03400f003da0384501800030800140c60a0f020342481e4440c170003043c6000c0141c22040c0c030514010b04413404569082d40c0c0d01c890b05280c100103680b4002c1d0030380c00000c0c1c526440102e5800303d182002e40c01c4403c0c4460000a041c1d81018124525200703c5200007c0c80d6002e4040e010041c4c1340040ca88001c00b0610f500c00c50150348450001c3d1038800300d016100700f070300b1005514208011160b0080c00a4002c404024005956800700c00ca401100c1a04100c0018007800603118010b40240d0061034900c60030540e1840301103500000c40c059858018003214030603a19030040022500024199030480c40072103100703c5546481200050540e41405051002a919054021042c1b05640104240e545c040c0c0d401c40c140c039090500450412003242c607000b0030b01400f6800c0041501c15012182500c9200c0940703192102d414044282d01c0c0c000304880b0701441070b02502040b1000007000140001c1410394004112480d210350f04c0b03800c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 488790314 1250 488789064 488789069
    0xb090a02031c1205060312070507090f0b01080f0405030403200301050a060f0320180f0906071e170108030c120c1c0c0209130519080306010315030215090a 68
    0x2540b80106910701c40e036078008400b16566540020106498071903100007414114500030303801204030000741440c100540032a520046580f0150304002c0414481402d01c2503414420805000818080003d44403501e480f513034030b07003103070182e801c917800c1580303aa55100040b11812a044405914100030010614003409890742c00080c1440c10f0007020314080c1d54842c00d01c2c0500008103020468480b1a070207607001c5131011085400104a00081904000301c100500000d81d031650420040c0000184000c8c800900320703004414603030315201c00103882c001080520022141d80700800810010070203403400c0400c80c460281604001841e500c640748101c4504c4e219100c070b00c4207040d10051100070844400416492416241145944903810350719600b01d9403170b2070f038a01c000d40c0070101c2020301092484e42c4032515415841241200c010300c401c000590a0300e06150402000b07820308000050865100c1c0d04002d101c034040102d5074a4841c1c90b5800902c00da0300c184181d80a411010512400619001104200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 488791564 1250 488790314 488790343
    0x50717060a080714030f060703050103050d0507020d0201050903030d0e0d030b1c1704080d03090308060108131b03060504080711060a0206010b1806070b07082d060103090b090a0203 79
    0x10814a0140e070a5242d221920500c44c07500000c200c4441d480c1c405002c40c1c1009805482030303441034a0a0600640144400c0c00195018032880380d641c0d1003c0e005400321518660000c004181c541160390045481e81d02c008900c079050b02060019141028481c001c4c0b00980601c0e0000e01395194038150020211901440514440d0f20000412165030b50321504200d0500d4000803121400100d0020150a80c80345034066207041c0300b00d0f035400300529855070042403481d21954039441c150b101c0078011038980009480304065003055082090025000f003802c10001d02c201d50f14410301c3c9a40ba01c824080781c800310760503126100002904d000304a403482008880307050441d682818144203601c000d40e00c1c00c050003031201c01c0310006a20b80c604400f0006c0b41101040041400d6941c11461401d0f5001c82d105542e02c00c0420b10304008181d100c0403142070390203500fa00001b680f03000519030300d0340c1502e00c9014200605040d0340d0142c1c2408541c4100c1c0740b522400008004186c100c209206162a0ac2c0d083c0e00101c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 488792814 1250 488791564 488791579
    0x6040618150305190b1e240307120b070f020a260304030c060e07080a170f160b06010302190e190602070e1303081603060905071706 58
    0x412412a0a40c0000c1040c00410000d1003912030410700311039548030b80000e00300c0e200d40681180241d1540b5061190a0710031403a12442d51185101c80301203140c400340e50425600c0b43c80c0020342c55a1984003a40781c0d4642001405560b02c010000300c4d0410301142c0100421a000038a40c2c0f0900401080c107980080851500400116006400035210151840d008011240c0f41740c04611043c4030310307a902d03030001d51050384030383d00d0500d4540607180381d078041006c40c3d14a06004261460520221384030003220184405001100c8090361030030701c00d034154003500341e0521050041e5501514200041c113442600510030544041c0f5a0400f8100301000900aa0400d40100a15051413500e400300c500911201d013400c5041451000018a048046101c01000300c804114001592a030006480f0300b12001300c4941c1c03202e6210902d010f00c4840402c1005404a055131010503c0c2c11203221004c42c80400307500e4001615600d035005c4a0643d00e080c3e80e400d0000b888044c0647c001d1300300142c115040007041701d142 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 488794064 1250 488792814 488792819
    0x6050a0302010918090c170f0f030a0f050d0e030c122502120a1101171605130f08010507080f0f04080d020d09060c0f09181a03190308060406 62
    0x20845a920300584d212021001c40c003134440c2072542c0200003080d501110380100c03241c95110740d48a12020480301003061003001c0f41d1502d100d01c04070306c0140084400f4080c51a0190007041070300e15204c02a06581045020071920040307a23501e114541508100002460f51002900200c40c03801e540d403c08a540e0410400c0b00410410a2802c0c201c082e01c282c40c0b0a401e42901c0e4000107149260003100031500d40a103800d02c4003007003024140304240040c00d89500f250b0701c03045900059454401c54005c1c0c52010703031846003500a40140c0c080e084800103080c0400720903444001001c0d26100c0b661280d1a00d031f441c1c4080c081c900b42c020000640c4100310a003000c41b0b40c9071161014220300005072010300741e458005214074104000350122250049070300c01c240300802c2189889802440ba4401c01800074084161b41049603201d807803c40111022075940601401c81221914010300b4046105203034198511198130241c0c40c1031003030342c624980f000311010b00c0901c0d4ac21b000c2c1c54103100078461840766144c160117 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 488795314 1250 488794064 488794067
    0x6040c170a021009030f0f0204150b070f02150408030706110309100b010509041a1806061b19060f0c090f0306020f1213060e07030b040813091b020106050a030201 71
    0x150079001e501210804070780c01855009540044130b82e0000b8100d541141801400c3c13081401301010040e2082da01005105c04030070703458424440038010001d02d03403400c02881002c03859507440e2983c41800140300c0300241125480714001a441680001020382000c034516040c4259071081d00c0121078180321003841c52038903070751742920342d04008840915aa52014480087c0c0d115005860018601600030409605e0200402d0036420024080b6880361103480d1f01e01e0411391060384454081c410191409003806100300780074100100d2030620b0a8140700d807040303070700c54001c3e80f0140407041402480b0000d00c1544811614003961002400d00c1c0500c052220200110040b02c0350003000c60b60403100041c0c8907111842024054810507016a04503080e02d810301c00300c80c00111422040314880d103400c010310b0a40700c042c213031036288910001e80110b01200c00200810100001003083c0c3d054420409010b0b0380702c0f10341ea403c40d5030440d1002c0c084402c1c0b50120303180b250244122809880701f00c542180d02d030300d590b00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 488796564 1250 488795314 488795323
    0xf0d0c03080a05181f11040605070b07030f052d040b1b0403140115060903050a0f0320060108100614040b0102070b0f090a150212250506040c17 63
    0x1580040b035594000a0101107251300c40b00d0311455490b0aa034402d10702103603c2429142d00012400e0018507240b06502c1d101c2c0081c3c1210101c414648481c0e0074580c032074031004800390780180f0078414580c5414038178515411f140300d03880c40f0360541350100b00c0c1648070303012810740c4c084502c019401160140c0180000304900380310743da81c841170200c01386580c1031050781385c4034142c01641c0c00100741c0c028036444483e0306001034111305030046012640c11106513070352000300c0d0348020a1001519075048200301801060008030b00045650290900340c40c3c942e0001000482071081a601c040582c116100600020310240850462090110000d11481d824402c50300c58506080c0d030f20b14440d990300c0307440040c941d00922099000340b811209991301c13102280b84805036540048109445214002e1003c140c1c8031884c0d40340784940045034002d160313103107006080c4580c40e403108041c4600c20b150300f4095001c04000c4100080690300c80d10241c5400d00f85890210640080c0750010094803510303070003e031302c0c00c1d1000a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 488797814 1250 488796564 488796571
    0x905070f14090a21051207030e010302090103020f13030203060a0c17041103070f09050c0403050c011812060e0d03020403030215060a0e0a0b0f060a050d110408010e0f0d0c0308 77
    0x45003aa0b90345881d40021950381003980100e80035488110a00442d1400c0c00c0e14040107406a000e0311207164018079140c0c094450f052000b40402d115030001c0b00d1a5200758050400c1441c10b0400500d040d150704103a000c26005540101c0d242d000d50300c018011810144070254000850031310a00600c1e00e0120050100907580810302008042d0000003018132410782e01d0045000c1000e02070381c4d800c0d070b181c52040c40b04502034000c03016100e0034503003c6041424114221000c403500007010b08800d01c1d1780070044850b81d840c9100070329401c0341c190021030030b01d4a0441003580a4492480000c9a5644840803810304682144440038984180401c00c0802c2d008200c01d520000117142e507100c695200340014174040720940041c0280302c04a820000403044961001c0c0050000b103841c03840040b2481c0801109100e412200c0380021400d12034203007200b4042d008428034010f540360712420192500c181c0c60841700d0002801040e0351000f00001812071040c402c08454100c0c51a0140040c981520060090000903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 488799064 1250 488797814 488797847
    0xc0301020f070b0603070e04120f02120406180503030f1c06050d020625060e0616021f0f0212040c0e0c0306090408271504120609030c15060905070f 65
    0x3000040b1135503401c0c072840c0301a050320441200141464204014013200b20500800070800345030901d17113100d0001600022440c00b507034150789010304080c0116603078a0040e02ea80130080700498040b8071075909001034500c44040300c014544441154103590400400c80020303590141c80c040040c080b60f02c0e0681c200251a405581c0641e40703104030705104010004402501d071f0308610700900c20040121941080c600321400d201166400d8560410f21549802d0501300103026910000556100e00644440e54402400c00742001400c103080315070381c60590b13120110740c1203052400301c100000c2040e417a010001070410810350520600e080c80c51406588805000e03144034922050003c1e003001743d03660840380c2695031003286481c541014a6418220003420b00e416103d0401503800146449154042e60308440311081c6101ca0300c0810f4440314005c05c40b1b45001d4040006c20200440030400018880241d04444600051030b01c0c60042410300f110710181181d000c000540400035182507011b064640c910001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 488800314 1250 488799064 488799083
    0x90207150522120311180405150303030f0603011d06070e04091a06010e01020a031d0105071218050612150a170102030907050904020d0605071218050c0301020f07 71
    0x2d210000c00c0b0311002c0281c0701c40e05000441a803080100302e040c99192401c4540302032100c0e110800c00c450300d5000f43c1c800d00b180c040050000300280c0c90590050b5411400f004013806480c150100801c0c116030048412001174a00c500c00d0003840d08003440342668a2507a00348804006031502e00c02178640328060074000421010348444182541e0b20f500c42c1e0640d5501002c284000d11180900704c000310000c43e44107022425100a5401e254004075501e04841e500d03985801101110910802c41c40043c0b40d0038504100040c0600d100245003480d1402e44100b0541b0f03034070315504108a1000c807040150304021f000764030a100780900e20003200c1e0103d41040c140c104248140b44e0b03e101144100e0b5199105010660420300242c1010b2810b40c001c50040416105a8595035200c000340219240c065030700940282a805004000c07440680c005600650700389000320f40c0815442c00241544e002c0301814101a68041980d01040400c0000c101004c0040d0029420a910b20a52100d14050100c0c0034040f0101c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 488801564 1250 488800314 488800321
    0x110d0308010b090619080a0b060313020105180a06081f03082d030c070b01141008041407172b0c06060513020c07080a02061606090209040302030d060902071505 70
    0x2128410384211240c0480385d20f0b074110306508000c280070010384056250500d8050f04246505201d0122440f034984030505225115a40d801103c2c503600182d07a03075010500c045d20880c0303141d85020030300c8010122907031000c090b81002103840112048500580100400c5020308000051a02055500412101c00648500480342050b400e9040400d03407691140400081082070102d411006445254001c01d075400302a80c981c90110308a5050b00409035100040740c80207240315129aa4155000c0d04c1820001d032240340700b04e603003494400b0039048030a4400185031120400d803020001c1d0340c2e070100b240101031484040340200901c00801d420f00001005106180501070113040e8101c480240f4000c4e0800e04480c80381101c1100a41000600e0319950162070f0001032800c0c0005019030034103400170616403502145024001100e000f40300d0482d25103850380d00280c05659900d00f5103100e14001e40103143d03a44c1d21150010102c035519041260220f1040c0105030215061142c0004c1940c0c48000010f01d644 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 488802814 1250 488801564 488801569
    0xc09090a05070e090702030a02070f08030403060c1707091d13110103090503031311030a05030f1e0c010f0c090e06060c01110414040605040501060c110f060a0c110d0308010b09 77
    0x1401c840d61508103c940c0203211500c0e46c00001095108100d50903520050307180c1010108021051190040340c0c0d200384001c5c404506107501001c0005141d041c400c120f1486489071805c400806c649c40c0c804102c041104000c501c040c84141d080c010040980b035811864811301d2101724900340640508103040c85000c00e0701503400f0364400000d4640110032291607217400030300001c01102c82d0808850f000035070b41343c0d92640c0c10002010300569a01402442c01d0424985d00a8501d400c9180d050b09440300140341f21010030020801400c16800820011846130300303403400c130303010788064807034034410800ca80340c0420481030000300700ad400100441d040f507691003c010310507024003040e40b444800bc4a0008001076442d03a0f40481000c1007400b0764007030000942c2c03031081204942d00ad100e000302040300c0241840004a0481224202c1ca03801030542500d0440789012601c0e0b0380013030304441c0c00f14803044404020b01c501c000e1144001c4100b00c40c80407030f21205a500400c5130390188508964000c0110f03445202d130303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 488804064 1250 488802814 488802827
    0x5060a0c14070323060f0f04020406090606030515120c060705031209060f0a0203010b0715110f040f0b160201050d0608060f0103060b01110c010c03050706051e0c09090a0507 76
    0x31655a03003219207040c3c807400e15401410f00341c442c40e0300000c0011300001c1407074000304c0c0c02c6200e00050026044680c1c0c51051440481c40001d0040fa031080e59042c002c41c0046581c130883d4090907041c1d80004080c94025100100d940703030b01d06660701c9500203800340c10b84914002400b6a200d40c01380c961944802d0217103021440c500806042c0300e8100301d407004002d0f54078400518140f14040f003c0500a094a92583d2117007244020301070103c3c813180030000c1030049800042201d1b2101913119000500304035046145030fa0703800c135007014940e44030001410001e245001079240068031519103c0c524018945a10402004440e90000c1c184003000c5400817001c1e81036070044000b015001c0903941f031341c900140728208a400c240401c03a010351030192415a1948900d5009050f8140000100143e0a411005450b0350002c0e0340300302e04014041162100080e850700850340a0a09603a9145541260200d682401301c002024500c581500380b101c585a561001c0038039030807100c1e542d00028907071102030b402c6400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 488805314 1250 488804064 488804093
    0xc030115091107050f0a02031009051507050c06010b0901020f0f031605031207050721080c0c2104170a030e061c050915070e0901031e140303010501030609020405060a0c 74
    0x140c0500381c80c0e000c805d8130120f40c1d00002032089054a6096007500b006404940012078054029803000755101c0b40350140401281d0000f604e41002800d105c5202d00c62490110300341c00000005074003280201c2d00c0d580411111160683d00703805070002c0110494219900d0180265441011a40783c6455040c0f201c00d0040710204502c441002c04146030401e40601190f100c0d60b01101c144801b018a0030342070fa91601c4075480304e0250759036401162500c0c00c07410a182c001351104003c0e402040901c020f14001c030510010f0b88030780104c40030713192447c0c2202e0704107012179840d1110103904444410000250f1040340001c41101c01c0300c1c256101c401079180122041100d074031a4103414039110a00641c2440010b01261004e001e210303026090347da5810885403031140120380d41e00010b0400040c000a61407100c0c3c1003207128003034000641d504e40c94807160100500c01007001119003000005009559150003024060400e0190a41c40c00d0324010201d402449602d11510400c07500320416820441080c0300c8002 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 488806564 1250 488805314 488805323
    0x106080c09180a06021206060c060411031c09030204060b0c1002251103070b1602060904090b070801031203090c060e030c120f06240d080d050709080c030115091107 72
    0x800d0f0100e10308800250310405510421503403070800138120349403031001c07603078450100c0000c0c1c03440361242d58450f8050f0012002c0c640c2d040c00b035048026151102d10310680800c0d1540d03076440f0407031451801031004590444e084440c200b08200310b07090b41e0000c00282261807500d800c000694a1a41381c0d012101044e0b01850344503d004400819400d00100d20030405881c6006c40960b15040da81303040c002c000b4415031045400c0d001d494400c01d00075141203409450800000f81022684000541d18000c0c5c0c13220888450300460f102303d00600c00c0c0591010054200c0b116405c2c00c1060094503241c000c60b15100384654401c01503415400d081c41d4501744411503604d08050810281c242d911001d4903241c4600301a244e040f84500c00000302e414041031030720038446203404500d80d80708800d032041c01440840030200342c681d09010400c14a0b02000c1d403180c00d11038541a46c0c1d07211100d040c00e80041c01c001102140c2840b0781c1c10704c3c0d0801441e003544160300084441c0c2d01f00c0000c1c0d50440c00300072641e500521a000d403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 488807814 1250 488806564 488806573
    0x5010e0103031b17030a0c03060303020c0d05100e0105040b070903050a02061809010611100614101b03020706080903091806040b04060e0708070c0519020607080c0d020f0106080c0918 80
    0x400e11410130b001d98061801008244901007804e8011421510b142c0f001030016400294162818109500300751030490140e0103560000c8440521441030707614003d440069603641e2800c110034409010780080d001901781c030702a20000d1940d1034207035072050a403002a106010001e4441d003a20b021301e402407039003030018040010540c0d5030800035060b5401c8503290352190040801e00704040c40d45100b441c0507980010700c0010810300100070b0202281c1e215040d841030104903207048020171101d050010003a0700c01da0042140e142013a000501c404000380200c003071070b88140500203045d600c400d0850304010b071760482144070760b60f02800680a0000240c40c41d03049890b00d000803d1801902070351070b124400766107414a494880880486402c4050803018005030170805610030004141644040340b6400142254105481030710350b170300158019003060302c13941c2c0f10480d08418147c052001e0030b00142d44e80002c010061401802a0702c4200d1a01c0040c03040c010707440000c802070500c2f52210030b28130043d42100c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 488809064 1250 488807814 488807843
    0x70f140f0915030f01020f190e28060f1205060109051c050f0d1b0807020402180a05040e030403321614130c11121c05010e0103031b 58
    0x18030000e040c42d40301d034000d016550003054113640500031507001f80714031038040d403a068400c45003002c80c58038100c48104004552110a0065581040704c00700c400c1920958962440c507403c015072002c3d803550001044c01404108c0004954000300c08001030102280c0124541d039883c00121040701483d000720341c0c01550415040760b02204800550001441102101e850305030100e20980d5400784210020001501c01001e8044a211410a20546d80c416000f5509040c0c040c2d0001e0260f820681d951201c00d0007183c0c0703004080c6410344045000300002d413001c020f05007102c5000740e140c1c81a40000780030141191900301c9442503041c20803000940b60f940600c039800040140d15201e0119460030300300c2084001c404107000f2043d0032581d210780c1c030003413050030380400d0f18840300d014004032070642c001e010003810030f680104810301032900c1c00120100b0b401e585031180c5110342044241211000b10700c41c5030070018040b94408224485c1501d8060804502200b502080702d000c09086150040c075002007055038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 488810314 1250 488809064 488809081
    0x412060e010c0f03060e01030206070f0311120c0c0d170c0708030a0c0b01080f0d0305280b1804050604021203192331080601081e070f140f09 62
    0x4003080f221159420f0140d00c2c2d540382000130051003804082e5214908125100016242050200e40d4a1090a00d0301c0010117003011181407030f020a0601d00c080c1400107803071000303031420302c800b800302c0d08216030096041006444075115800c4e5021901c41c00c6800081401c03100108000c480014400401143c0c2d50302c191640060201040e410210751264040303002080302900801c501034152803800003485200003045007200640400342c150340d0121a00440040d80e40c2c07155021062042e1180c0c804591225402c003409200b40b0820041e610340782c2c1c91003c1c00300041d0041003498010f50100c42c06203200c2400300d001821441104882803962002c1002051130307a8012000c81c5580031201030201044800c59a00141c1b48034596107440140d0344d580c030884000071001d18600c058440403848400068407840350929004082e00302d001d4540c440143d440d442d50000c10816031041680020745421464000350b00c0d003540d00760003140c0d84030889040780c5103d0388840440340e4460034000d08100311424641c16 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 488811564 1250 488810314 488810327
    0x91d150a0905130c0b03072a0b0a0e061005010509060c010b06120708150607062703090f05030c0108130303090618020117090a0b06030f16090b0409080412060e010c 72
    0x8440480740c100d00024611400006da074414200f9803a4400c0c0310b000f050b61280d04210000f0054913900071500b042021407650351103d03210b81c2d104980051508050216245480402880700c885003103054401e0183e640c0c000240c032524401900c900d0789030003d6480003405002e0110450340c00c5000030a1240e1101e0517a0040b0f8091012a254521151194100c4030615111000c2c9150041410040500040e60643c00300410f080c0001c402c690003180d1803038003d108500d0131010380000f07019150500410014640d2100100310440003081c0324605400044d040080c000d0000482032403508a5005143c0250081c01103654001070130000030f01200b500d20558852031000340d000856041c40072030010300005030315005003060002413010201d159114284403034010002c5070940140005e050014004001602b00b510708039020240e0705041900b420100c0b0f044916251040d07080c44001c0000c550040212006c1e1003681c2940d02d540c6007241041006005c49607101c151541c688160480c0ca00e80c41017 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 488812814 1250 488811564 488811601
    0x3020a060c0906080c16080c210a083907260412140106030501060501080f041502211005010e0f030606061b061501091d150a0905 57
    0x600c00c20104952000850340c0c2c010798020900856825008107000c82e5540028000b030045ca8101d81c400303810643e81e01d003040d030091126112181c2c440c840b0890500c400340510303100f1040c0500070a0800c540034100621400e4044c1c4480c106104080c0c0720021180350030306684500360082c0c03400180f400103c440d012141e01c1500190f8101340129541480610200c00c001e001151202580381401d0070007000c2882c120042c4c500700c0380340c0045003050109003800e024043c0114025800005c65520b0013002605092004000c1703030b2600008420000000c000c07654900c64045956001a1101c43c2742000030f1040445695400040c04000100304c1c0b04500d0180c50381c04d580b4283d0f03c10410805010512254107031890119506800107000101c1c00d040032070240c160f0b0704000d500c0741c100107a100d4505090060a50714481d480b6044907418050f5604030340c1010003003143c0910010100c1d0740380941110148060032800ca6020402040304441e616007000b078004e05481d603010001750400280c0c404000e600c10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 488814064 1250 488812814 488812823
    0x121635100e0717070e060915010f020309090c0304110303070506160e0409060b041a060409151208040e15090f040c0b130306230c03060612180f0f0d03050405070503060403020a 77
    0x240c00181003404c3c40f031176050060008c1c0405a0591418400644441d5a10200c0b0340031840305008031440c9540301c6903542c0c01141d9014483c0d6881c181401c1c81e101018523000301d68041d900800607400022030004031140d025011800c10119191040d00488210442c5502c6603845410710502e5410b001c0160300c0b4a010100807a002c000380c408034015107030380034101c1200715840030040c00104980c24054004050100000d001609120b4071500680c041203400c100c00d4a2681000c01c0600030f04c21194507481c3c00591f081074195034440000e00143c00840014200200c43c5960b2002c542000000030101014004962240d0b0320b0302443c50040040341903510044e503180d070410411a405102d0044075000100304402e00d0009503407200300e14a12a0f1002e072802e5000401000041d00003a50902e58034040c2c0c2424000450400380f02070703880d2804145544040140d004082045103002000441d1800c0307200c20306010510303983c1c60900d2070800c40240c0c85a50140281d1003000704150b80030070340300402c0e40719 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 488815314 1250 488814064 488814089
    0x1202010515010807020304090510030f03080109050a0b060f0c0a14250f06051305040f091103011104120f120c12030203010b09121635100e071707 64
    0x81000441d00f00c04240e4040016804c20402485886801c0c1c000541c44054400c1c09000c141d0b40e5500c1d07030041c040001d420b41c0040e16000050010148030b0003070320b07003066400805000c020240d0000400d284160101410300040020b01480c9020007889000c0307200303130810341c140140c8445981c1991150110205000003140481803108400000041c0c042564501c200e031044c540d003424025030b00c59200ea2000b0801900c56840010f050b900c901407103108284055000c640d2024034500030545410480b41d945c8264102140060240c40708070a541c00c1310b0354118865207884090500a58501d00103401608001d02c1020304043c60f40c000880c0e880d02da114104030940b00240d540114100d000a00a144e540901046007000c14074003004400318030a851400c2e690342c82c4803582c0d0a40412140c2d03001c4240040c040300e01440c020b1056032190000c191804030800700130b140f0901140c0b100303502c040d4400601d542d11a281c2c90b01100f002680d010f451031040150041c10705403d0155503850310300c03407500210302 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 488816564 1250 488815314 488815351
    0xc141021060b040611030304120309020a2d05060702031519050a0902091303090302010f050f18030705010507170f040302030f0a1101110309010c110d080702130903140f0712020105 79
    0x800001c407407081750012080c039081027000d50200c001d0700c0781402c2668040c000400219411501441041855041c000e114800810700e030490001d030300300c95200900c038520500026000d600c0200c1c4001807201d076400d09400c240c4d00d43d24046c3d5000ba0f14440428002e03c2c180800400c0b100c25401148024000c0718410f01303d40d546080410300c4104075000500044001c4030800055000f0a0655420000c6040040c1403914419482d8565040360300c20104800340c07226041500e042c180001c0000d0442880c0145ca4405c0b107444540021802d00d00e2000d0100002400c8400b0f105840300b650040c3d90700406a50300b190b251346003da500c00704040305075807181f8040701c0302005600a4140c00f41c00b5515001039420801c4070001900e8540b401802a03a40d860004010996030796541c0819243d00e2003030000341c1e1581c0c168018008203801c460f10308043d41c0d01c2d158001d40440e4128002c1c902c440040da060940e10590306c00c08407400d004410005001b0609401999010358040d0005442049110305900b40c610 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 488817814 1250 488816564 488816597
    0x60b040f0e06060d02070203030f031612020a0f0e04060e0f011706070f120b1207062c150d02070c0e06010f0f03020903190f0c141021060b0406 63
    0x7030059666a034400001c110406180900360094140140000d0682e0308101031050b08014903802241c0c0b890220180b1300c040c9082039040034151040e0780071211b04504100b58004050192140d09040000340030881d044051940d440d80c04c00d0019041c0000b0039051828031003020300da4140203009113440c403c1c40b00480b100c4150001105071003501c065654174100c0e81e0f50502a140f0901008013070898039100c480345411512076000c14603028501c1c0f0010491245003280080158001054409614540d4101c1c510401650000e43c440700e4800c8580c4141c400d40120307040d00310301c114010100d107140081009402e01c051800b01c2c4085680076212120300e503481900440b0565034400b00031022410084040354420320035805000c804001400715842811034220710b0b4003001ea0444200c1c0c000c100c1855580c00c2000c02c41149000b0300801d8004012802090700080a03016441c291604001a965100b00008050590425541c0340790710100026034443d1b01d0f8403155840b901400012440001c118001d80303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 488819064 1250 488817814 488817839
    0x421061a01021b150d0e16331407150609060519140f030f0105250801060507060f0507020c040b030a0312020a03110a0e04060b120708071101060b040f 66
    0x3250000d240200300d050813240012580c2042c42e2207400daa9442c15410b0610360304005d48882402c040f4038803884586010520040d00d080010a003190082c40054034900c00040f8800490007132090416a4a0001c444400c40c00e900641a014155420445071101ca01a8982c03100e0151220070f00c00b4000749840781c0510000c3c00e0380001601c2c20740b00104081080d014a02800c030000d44000b82000d200e0020b040c0000d240240d0340caa00ca080d0b0f5910700601014200308000d41072040300080c030700d03640c9031000100a414804148a03c2c028404001410010070403a540881c0f602d91221004210a040451000b9960104625854000d41c0350421035001c074600002c0c091041d0b9496504d102d21a04807000c0d1002039007050310198145902c6281c0400f62448010207803180c950705549450200300d0b50f0042200747c41c441e6109000349802007081d0000b4101400f20107504c6002c9042040141c1c0364207070201e826404404848209501e04080860014120b400130720856aaa00e080c041b81c80e160340704102c59 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 488820314 1250 488819064 488819113
    0xc09050111060601030504111005040f05040605010504090903020102041211280501030e01110406080a0605220c090b0a03150807211518050d0809030421061a0102 71
    0x6521034400510558400c0e08910740c031510408c000d60360703441c0481c00705074104101c06242d404076002203800d011215001002e04001d0404803000c0c00803e140500292840c0700d58080c80c14195100d07425101498002d4048800400c2c1c480714000d8100001d0030115900b520141d88180300c0c998101c180c1d03072044811300590140e0303114804601500c0d0300d4000103400628103841c00822a5403205000401710724030300081c000400003500c0b8040d42e8502a010001260340035003040f8030456614513010b0749001400612074841c0403c450008071032545070010303207074001958022008034400081c1d2622456141e001102240e80a641e20b28480d80c1f030b00842c54540950303024a0340c070360008040521044d5201e4003140b5115010f4a1410150070440042106403182c0924000c000b40c0d1407a5004208a010407405800401614040759a803c0004056803030744624800d48012448503011006000c3c0740d0701754800c1090744018104002c0e255200e0340c0a00206090b20341e4054090900c0c450342800300d14030754004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 488821564 1250 488820314 488820347
    0x3c08011506090b2107081006050717090d060603110111010608060403140c1c08090102131e091e060605030f040303050a0204050409060e06010b130e0411060304060c090501 75
    0x40d160810300071031210b400142c000138012401c0445013400b082d00b4001030740542c1841d9505045450004c042110202c0a90b00c00c0d81080000c22801c40456281e9460303081200340001c01c150741c0c42c03000c000903442400740c0b040074003907030b150000000801c040c030304440b900510281c0340c2070b001020801e901400c03074034103214040b826001540040c0002e4414145c070100e800b02d880c0c1c07c82c146203013202100e03e0501c0352075011802001d8141000004d540100600c0d034031910100003589864403607140440107202921032481c082c2c0300a0148444841c0301e180c8030000d801c0c8030384104101c06050107800e542c0700490350900c40705d0b45040400304030703503201d0002c036480398940e080000c6482d01ea81d0741c01c500030310005080032951542404042801d503658021004a00c0c0240f40c080348611026409a041010690144199800800c000d01c504185202402d0840d42d0026607628169620306000e03041240401081c1e5102e48000104800c004c45a401141d5901c11507680c0150651120019615000001b09840 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 488822814 1250 488821564 488821577
    0xf011d030a0210111614010614010c12031b032c0a030e01032c0c0f0a0e0405010605060f0301090501121a07020a0c140108060f0a3c08011506 62
    0x800d0760009801ca4030b5543da91341e0150340f40448055200c4520300042d08100d400881c0c40d05c0c0c040c2117160901030750b00580140f0446184500c90000003902d80b03520030380000c1014580103480c00f5618041c1d800701031801d0740b2540614040505101c001c00800140a40c1940302090000c200c041c0e0003944090411140d280c0024030041d031007510140c4415000350320750703810580c88070f40300d10408106c0c910080c0c1d003078558604000740429000ea07181c102995804013a015113440802c0d40115a03d612500d022140c15400095503a291070600502401a40d004160041c0e00003410462440301440214100c90813003100f004166240c0c072800079400c000d1540503011080104021010400d020070b2550000441d00441e042ca01c0389648100c5602ca40c0c1e849698803042c044042401941c115074456802001152f1500025650a00081e8000c21768019844035002c8d000b80701c0c040f8154004520310b0610745d00c078503404281e02e0b002c110425180500542d140b40d400d001188080c031020844031000c0e10b25688415 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 488824064 1250 488822814 488822833
    0x8010303081803040e0624040b0d0e1c080702010c0507080306010e0405180d09030506150d140102030a11070c05010e0d061503050c18010519080f011d030a02 69
    0x215040d5001070400c02c80c1c01900410300300c01e0841000100f008004921152405182200030803000c3c0c44003070521700468144070b941034410340d0100e007140c01352640d1000740c90300c80142021100c014030ba5146198030710b2241c0c9141b10744052680480e4000c040742030351070220540c4c841200b2400e842c01d0310004008910705104101c006080c24000d1580150306260035503458103040002010351300300340c0d402004040710f4183c1c1c80c0c90a40920071703092626154200080c50a10b903554040c1d03220310081c10480c1e80c40400412060710b036110184c20304069080440700320640d101080090003940b09a817020902483d0070a0400c1200c0388100750340560750080190381c041031912006440c6511071003410703541b02c1c00000d5074100151a9201d002090300d84030305440744513429131514625180450021910078008040e004051102000c001815103d083e101c2c10355080681142c1c0c0c0383c0007030b80d8000c28458000c000054400318815402210541355000c2c420800409036601545c8901c5944110030040e000004c82 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 488825314 1250 488824064 488824067
    0x712020f120703051246150308040b03100f03080a11161229150609090106031e060612091a042004050f0106110114100f0b0a08010303 59
    0x740007140d0280c01c0c5545170642a021169040e601142c9860415202e105240d0880310f4907640b60400000d440d41002610019004040c1034029501c414115286ca07000000e0080030b103003118400030769004107455105c544440c111086504200d035800040d20240c40009210101c06074008110f0750043c44d0300b480d03c400088200ca1464815030904e820b8818a01110000200452020010180c524100307080c07140f00d00d0102c0c54212420303502c95a0200841901c0300041040d000f580d002501d40b00c1500d0344000d8240850003501481c1080e552004000d000041d65640ad03800080080d00c00d80d178480d041c000101a42e80440e412400707007600054481d410112480b0890b8031801c1072602803c5540d079510070421030f0218142c3c046034210b41c0b12041d0031035040700c2280301300380624143d0111400d1280d481c2034102e806515005104640412020b82140f1241103000c2d4840300450900410941d402c2c0342c0300000032242203881c49400d045500c0c0500000e9000c000000340c0e103611580742e44040385a4a035860 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 488826564 1250 488825314 488825317
    0x60806060703170c0a02160e01120c0b07140c220c03020c0102040303030e1615050f0c011a0f0405040510020901050d1a150703020a080a1101110712020f12 68
    0x70101c00b4010004208414180a50301035442136515010243e56002891002410714220103425407030110b00003000d101c1202e442481a0569004416132280031080741400861008558804402d0010010b000000e000004a4000c0310940071012900c4405542042c405c100c0f9690b503909140021641074419440310941000587c1c52440c42c0250804a00c81c298a00f2a882a4002c8011981e00ca06a842c499024401000643c07940c42c120031026140c00d9814407007542c0e40020700108400025603a280380c00c050256581e030b9882c45c008011003201c45052241d1944442580c0380708651002c440c07105c0d49000c4c02494461540580906603841004107407001175084906100d050000601070048000d2880c4101d11b1080f2070001900580d81a400a004844414800b060981d00d401c00010300801d8000840b02d040c40e91015030141d81c1d0b50102000c664140070180074540c81e50818941c0074502d60300f400582185406884104050340d0803c00a80c1d40b0010341a01c08507a0b00401d5041242110050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 488827814 1250 488826564 488826577
    0x1090b18040602160c0f150f021f18060b03060606070c0e060f09150f0402043203030d05090607090303090303082508091b01090b03090c060c0f011506080606 69
    0x7601d282542d80c5d680300108926040100e00c00c4418008003c03540c00703080110301c03081003403c01451791241840c0080d101e4410b080119014030107812000059581c95000304061402c0c0079983c0000e52580c60f2550180005400f01ca01c2071140f8004514549484030480c0d05550344403145140c000d02e84410240c1c1a03100419803030380100c40300e0510340d0641f9042c0d100ca119034082c03000380c64050f02c4181041200c41c41750304c005000740d10611090010781c149c9100305d4180a410000442140c40b9510f26900e0481e500350200c0e050301012a5590b040903080d008075005081400580e5442da4500d03908460b09141440040c0006044031070070004a802105a03a40080c000707403001103140c0000f0128240481c58100d95000a50917104000c440841401040c03040d1100c0f41001e00c240308103100003040700388940903260300ca640000c041004044100403034000d45901404498442021030404c03a02c03900a00352900c0a0350038440e80300c00c10f0007101101b500380c82407621007031b00c03c6d1280e40c00d100c1d1b59003010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 488829064 1250 488827814 488827837
    0x904060f020708070b070903080f0d06090e030a140f031803160b0105011205090c042f0a090e01060203041401180b03010f1d01090c02121201090b18040602 68
    0x404066100e804240001c00c1060301a0410980d90300540c80c0c007a550b800300070300060400012001c1400040e00349021030721036204d036000b1940c9506441c070010f801407030103500c481074a6240001f140d030150004409400c1e080300c7c80d110070940d03c1802850300c801748102030669401c6141040080c648442c1c1030000365020a00c40100c904182644810220300c80011200b41c4090a42500402c00d42d030740400441d41d10045a20203200d00e040020300e6035540ca52401107540701c6c0e074682c0c401000c00001c04034140848102041d0542106544861100043d0711422590303000890070400464036a048441c400e0484900e68002c5240501e040250035a0b000307900821030411815441d900302c1da200c1c03001c14101030452038600d15929450540c60581d4107072241d010841502018803480b1101002c8041107044034075809000c10904070341d14080f0300302038000302501c4104001080840d1070380c0081c1040b9059075200d2004100801c0e00104004421003d4081c00018090140c0010700058258004d0402400c89 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 488830314 1250 488829064 488829071
    0xf02010c0804031e0b070201090c050405180a200105041a030c070812092503110102031903060302031608190602040b04060203090319020d0b07180312120515090406 72
    0x383c1e030713500300c050380210540c14038240102a6035042c01030301d001680e0820b0b0280001c100d9000196661281040c50b0310800b80f21b145c0d21000981031a040c5060002004450300541c0d100b070880f0704d072002200082c8242065031407175200440315654000d10440c1d080d9071a8190030701200011741a06c00301540010808404d8160901c84c2038006813041c005419035003403194841e076652030301c4e03051245051200e092020402c80340d02410300c02c0206801649003503a401a4100c10900c000f000141d00d14841c8420302035500c00760a0200c1005030b8035501200940b8400c034181d0355009207079030a050205000d40036804103a006092101074035480400e280c020b180c400c202c0503082c5981e80641c01e002d9082640540b0158000284400c2e452070b090181804048a401004c10004880c3c1c000c41c844000007600102600e40350b5010a00060184103c0608003d0240c4001103035a103074500301c80500c8502c81d0341d10202c2c0c055802014104454000c051003445455119a684000441040b10203a005882602c600e943c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 488831564 1250 488830314 488830319
    0x2070501050304110d331505010804020f09010602210f0d02030703060305101a040c021c1803080417061603022206080103201e01200601061b0f02010c0804 68
    0x94240b6050410080765846c080240c0002280b4144040808101c2c6c0b4030034a05010000001e51680190702a650280b0700100c007603449101046c800e64420001c0c55026001e6000042c41560000358800c0806004810322241c085030034000e0554000c003150f1054100c014000c511441c0d01d550301661380300b9003510300407030f201d03035252203143c10141ca0061110010b40c58001249020f10032400746400d42d84190340821036000ca1100003034840a203407194006110b110a041c1da0703098410840d0841c9101100507482a0310750b2440e2044096119210310341140174009121041204003040030f601c80e408c2d03118010f5540183c684200d000b580074400d000e164030b081e000740c0f0310a440c0000303000c8041c00b0a92a258419411403c1101c3c0381904007444540c0542d622540d40f4513900d42c0c5480c121600c070b960720b1801604850300d005036000754107521110034490030400900740c0004001800c074101c030201e40722000d403444050520903d4009082010305208031301007212005500c40e2a81c2c00f640c1c1e0088030071504158 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 488832814 1250 488831564 488831573
    0x1502030901140d050106112a060702132a08040c03081605120408010e030705151503030304030804020405070c020102060c03041b182d090213021b0c0102070501050304110d 75
    0x10360030b0300102c000508040c104480401d04101d1045039002c6081c208c4500c6204400304011101144101030003400c0c04240c09003191500210060204074048082c0309024101010780d520104480b040c881803500300251302c0420380501205400b968005810706012402d503102ea034560390010141014204c1c441802001241d000d102c005840d48096410300c4d5107034641089070707007956a8480c5c0d03400990000c105c40b80015900103144030152012841050403907a41400f81c2440410180b100c1d41c01d80000030801c4201540302110300c2c4214402c4034208815254043e08854002440b1402800351b48890080b4000c4c03141000559070140c400c0c000d0300780c4d08280748444540e2a041d60b11a2200821108064012002500520200b40c003810012019403200c903003607803201424030221240c0d040e56605080c05540b100e00d025031880074200c1c025540c6403a0303203541503405d00400009007034a004020701c00c0640e41c0702180c49421160142d50b018255183c54445841030f041440c2d8069000e414030510344c0004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 488834064 1250 488832814 488832821
    0x18051c020c03011a030f0102210c090402071b090c05040905150a0b040905160e0d1a1014040b0d1b0305120a021902060406050a09030f0804030c1502030901140d 70
    0x2148111031302110070118040c540f400912440c4840103034018012648941c400c20941640d2158880c02548a03407100041c800c0548181103041e03421038000034059081c4948039622405080384003051040f0039603603010341c1c0c040b03034589180c040c0000c400b04030803c180c0c01c0760b812864224185d1102451300400c9080050318580301c1e1f074425403007804041420002d54405206d40d940c0000a280782c001c80d0083c07000d0051400d000d00c100c843c4100784151012061082c0c054034200252240c1188460601300000480700403000384c0b0405444012030b50000240e82013030302035140031980103006103110300354954446a54025103103407410689221900007010880400c0243da840d00d41117241075540350407100083c02d201503418030014403480c03c1640030060315640304442c210b501900e0503e840355803c0e0310485184105d1f520160100c400c01110109010030f08e0000d00c00c403842100801035865540c0703c414071008080368004d0240c0c0091000349500e501442070030700d14003d600c10052034a80b51702000c4044 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 488835314 1250 488834064 488834081
    0xf0a08061b041e033f02010905152a040303081e130b0711070b030c16050706020127020f041b0f03061a0f0a140403110418051c020c0301 60
    0x50581e048108240541c0d1402504200d8015001e0204441d44101000e10003401000d019030415081a00c0d0401c5ea10070340c03040ca10f40c0d0340a8180d82e08411300c0f000400a8042c1514180702041c50128407a0708c0f03d82520b03079804000b4a80f0078242c2014915202581c040790010306082c01d0f8188200c460010340015001e00b4801d2082401e1125441e00030b0030601c14980b4020070034000e2004c50700c010500c442c000900c090440c2c0b800400300d80d490b0346003640c40700349008060344d81120703001d400400703010440046100c40580312664004c2181840e841d6a0f000d00e450040318001280c00d466080c0c90242c244003000c0708443da03000c1c101241380018807020b00d010140c1c010321a400503501d0300419020395854050200104007070341c0310420383c20282410202d90b2150504180804000180280d685802074130128400e2187c1c02409494556a0a020a034017500b0411248035034948184c030030195090210306544940c001c0c0041080000c41c840c4007007900120416802540701c0c0405003051a9000d0140d10078 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 488836564 1250 488835314 488835359
    0xc0909071a0702040e06101d0f060d0204150303020c100302040608070f020c090705030402090105040b0105091309050607020708070509100b0a0e0616050105180a020d030521060f0a08061b04 83
    0x8000d8549083c0c0c03021400f42c00315001c0b064460308284882900c5082070309d038100b1400ca40400904500d48001002000d8001d258900c07030303c9402001060580119105170140d40590704070985043e1040300710204d100340e01510001c20041404601d0fa83e12403054003480c20b9031801100c04628403500040c00c00c0038211403820006000104000850510700d5002c0c0c01401c09447c1401040d10110000e0568020050028003d075440503444000039981e8100d1114039030080c00780c6021342801c0000a448950702c0c06600c00c0c07441442d800145034145007000e0745c4500c0306105010051402c040075140e56a00c42c1041b10700301703d00c01e6000c1040b951000001c2c41c0b040c04030ba1b40217111001924182c2e003540c05c000d018083c00c3d001040c1d8502c480700042551038880340d0444903003210703515500d0243c8003806a51a50100e8001640f1191501d0b6002554180502c000b01e80c0904908010340c1003280d2040039005807425a00700101199255948544158020304d00040701c1c0d09060f150803d8800303103162902503c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 488837814 1250 488836564 488836591
    0xb3001050a0b040b0d0203060c07150f0212010e060105030103060e010b0a0f140d081e040e07020303010e13020a0308250c050910030503091c050d020c0909071a0702040e06 75
    0x1c0285082d1282144a113020340304000e10b00c101d0f80004e83c0350280208200e03240c000c0003840b402005048025001000905002006941480c0e18410000d40200c110068080500b000100e240c400d80ca1031a8410348050751220b185a0079a80c4e14000361400210f02c503010764031441a0280b594a01e540600900300c62041169403514045800c2806280c0c541e066001d40781e03c274405070100380d02604445100300581440380c4c07150300206044480388905d6200d0f011141e1302e2424800502c2d40400290304031a12520040419150032050110381c400703c105c0258030800c00c3c14108005407010b800f810305000e02a211502c184000c0e08000403010319608100c90742d0580040c1480b20780f0b03019034681c0d08017505120140e060b80c11035072035a0352131180e0080e8a10641954071440488a0a035020703040d0b1652100030f45946500e5200042e66521408030102e1041159a0014200ca50300040001c1181c060524841d80700d141040a106154040c000590b0410388401002124410400c01540514066006031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 488839064 1250 488837814 488837831
    0x10111215040c0509090402040e0309030706030e01060b0f070b07090b0d200301050a090906091502130905060a1e0b04030302060702190f0204150f0f05030c03010b3001050a 75
    0x4444502070b005092103400d01c0361311569207646020381d5115a05480000d2505001c0010900d14091049201da052052950120f40540e040d0480001c0c4103c01d07009000094903404002070600070703005964503a900a02425000c2942615130b603411070500c0c10700d40742d004c1c3c4440e507182c65607202588694a46407122410456001c0806003000340e910a83c40980c2503504000000e440d00569120307000c0080d848440000c18040c460f8050200660302044d602c105400c165508400380d00308540e8002d0505620000240f600c40e5030280d2480740b00c009100380d0030f050030100a03260315803490704641c1010100c00800b08c1d80350000c0000b000918001e400078a603601d040d4a0007483c2c49030412403c280e54198804190001e507005040200c1e0340e42c1100d000c42c1d51050b0700500e2040e80d00f5580000c50503a8180c03000203602da0200f154401307850081c2c0c241d5050940550506081e40e122503011904040c92203164814031100a09101462a040d407101140b603442201d1103003907030015640c80e500c1c15660b0700e48 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 488840314 1250 488839064 488839069
    0x513080a021e061501080705090307090b100f0e04020d1806061e0312110c0a0b0309010b0406030503070605040215040e07110f06190905070b03010e01120510111215 72
    0x31008001000c000074061458903040d000e02d4071350b4000c112814070052401180615020f40140c41c0021009422521102d50b6400d00d03801400801108034040c3c008000414074103417050400480f6583c01d900c514006031480402d000081d0700c4070035090681596903a00301a00002d080c140e1545c24010400890024101180071241d5161100c420031101580d61042001441c0005000c445140c0383c1071030f0003090600c0350309034281295509015031103e0000004a411010400030718056408031000308405080f00c02400700325074041c007000d0942d034800c0c8a00000035081d9000b4540c0b0601c090041c3e41100c0da0408a400260010740006802c401048108160036038403400000c100c900510081400c203400011031921510044d004401d0f80144018000c06c1801603004003c08541c80011180b0184e074440078002503030130030300405120b500040c1c00003c00e03502180300d440d02c440c0c000011745030540310f81028100074022914035004c41401070054036030085065113550311800001e03900000740d00c169800c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 488841564 1250 488840314 488840353
    0x90602090a051219021503040506040c051c02041802060d020306130902091506041701060509010b070b010b0a090513140601030c090501211104080d050910030513080a02 74
    0x2070182200b5100b151203030740d00113810410b07034840e4290711a081520f0700104000f192051101c001c0350a00206000030858001003280c8182d01980303100701d020340c69204004860440102805c21669903003400c00141c946507000d039541200340c0c0b4070200041901e46c0820202d0f00b1103000d03148900d5012040000c90301b0302c101002d402c2050030300d041000c1d1041c3e0340015a80080500903902d800c100020094403903c9a00850f4003400d440c0d14a055403010040980e03010304100c0c0a014004c20901c000000c2e1401110182c807040c0d90701041070710f800e80c241003da002a400650f14201000b0144000158030b40390400380302d1052203030f6000800c20381e02050705081500800b40900d410140b41101412116510140d8241a14070919082102200a0752441900b4807082c04604186240a4014109000b4030000700103c520001c10380d0003400c08080191054060010500d40280d600d24000503014840e80c40113500401607000345540700c015850b01c1d440fa0700a094240b02507030221600348a001074005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 488842814 1250 488841564 488841569
    0xb0d14010b1809011a090406030209090307030e03151f05060d0e010506091501030b01120c0906260f060102030c0706020313080601080d0315120f0308010801050f1513090602090a 78
    0x3c3e1220225403414000c5819400c0210a80d40c640700f001c140818140e071284c101200075a0010011049400c1c207050035a207a900100c412404200205151543c90030b0105840c0306494104480000c156280d01083c1143c41801c844003c61090010b80402c40c0d80c1c60602a0281c0c424292000440d50807201a46084a4000c0c204601c50144002000000c601511900503620028038005c10401c81c0302d00140c1e4004000c5207041c00003070400503c2203549034496581c6003140c156686a40d2000b85c004485030705d083d40c000884130f5844242001881c0c003c14080700b0f0f50060410301c1124500340d40110050300307002440d040840180c10000342c414040c0c402c96000805070500c05d01134401540b5104006030b031048a6240390043c151548901c24043c404d10804100904880704004800142458101091001c2c41d4080340401c04460010640c400305109080c42018800496000ca40701c030070010100200c48000c1d20b901880b03002c0003880e4120a8040c3d030384014800c060141c2c5035040e200802180700b00d1074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 488844064 1250 488842814 488842819
    0x30605010b09150f0f0d05060306061203030a0c09181406010f0e0d030306030f05010c03110a021915020c06040c050d0827060c0c010e090903040b0d14010b18 69
    0x81c030180d807075030b55034242c400c070f800c084002125034903561030000c140b09008506100d90440c070003050140c50402160401c5104403001c130151070180c3c2d180b40030800b04404c140400c1101d82c0c030600014641c081c0c0c0b58030102c944100e034249041120355a5494200321000031020911880c0c981e600040e80c4090001d407160020000d003002c4402c83c0d80c01400902c15032100300a80d226401c07200c1e1107018140a070740840701941d0007107046940d5501d44c3c04d00c42d01a01040e045000043c0c6403682546c0d020310104140c408000199025285040c1c640c0701d0811000c1d9004800e684454411884024030302d038a03c000c203180b90103000600f40c1854541048a04000c20303900c05400341c0650350506001482c10b008803140c03042000c0346103107440c1c41c003955460118180c40c0600e170001d400142100a56900140600c01280240e80d6186040404000d03c145400c0680d1a00b0030b80d4406d0209011600341078000d0150021007050009100c160141e140c502035100b81d00c20440620001100100e09490340e95619a0000c01d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 488845314 1250 488844064 488844067
    0x418030f0e06270607020d0308041502030606120403180807080705310207020a030b04021e1c08070c030b090d1403070309020f1e030d1b060504050a0b040b01030605010b 74
    0x403495001004050811003101040300b000704000f96550034094440791a0094100060300e1070030b03c1d0140a038802074a003910040c4500643c00300e17403040740c001c0f07030300c40c020250100303080680c0192014030b1240301810440602c90301550486440c000d426494009100031801010400d1400c107450b810480a0307000742e4050107250b018007952101e0300061510b00e00c0034010302442401e1008080009000752000294000c0c0c84c0c141c000244101d010045000d81d008442880e101c460300c0355200b6229509526568000d441e001041000644240c40c2650b240d000d00300c030614011495503146c2e507080441d04226441d800001c10322400c0c080410600e141d816581c140f4694000b2510312401030350200506a504040d1600d64003001c540b19051018100c0b038015020041300c11500c90320055926031034118234081e02c40c01e1062281c00344903521209108100d0814200c890000d42c0b151006404010b001303441500c036480100c000a610011200d100d580140d01d80c0d0f06a50451501d10166081a40080303d808030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 488846564 1250 488845314 488845327
    0x3090f0503030a06050102030c032d070510060b0a02151009050c04030b090a240e0102370806040b1804080a09090e061f1a040e011a04030f020418030f0e06 68
    0x400200702d03020502103c0020b498440300810004bc40d04010368084901e80001c01d414041060015071054403007901ca0003401120b456003800d61150060504480040c1d104158001010028124071901306215200c2400002c1d100c0100e60700b505c10680d00503900c0400000e0401c24000304400e042c2c2c0040c40c5c2c1c8007a103440b01c43c588411800c00100940d1078030035942c903840701d001e61565500031241125140000e54a074030300284d5415000282c51520f0785500150740006005844800711640042c0258035481016151101840010214040d0882c1c210000d0302045924000c0100494459442000d00580d6444165002000800e042c1c0c00440d0b55820702c0e0340e404e02c0c0440882d103641e1218540c03484407252989074407101011501030740402c1c03000c04401140c40e41c481c4001c0040007500c1141d0f0100c81680d9941040225a20000c07000c00301050040c0300038400030302c46001107811240000d00100b1101e026610048294040e20000c030080b070f041c0d00c2040d000c160001c0203250701900440c1c04a040c6207 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 488847814 1250 488846564 488846587
    0x7090b010e18090a0605090d12060602100b0a12120905040c0525020901170105010b0c030405060a030b03010c08090d0201090506070c06091505070801150207120303090f0503030a0605010203 83
    0xb09219142036000010000150101c0400c00c07030080c4aa410201c140964200750006a031140784040c00300300010144021800c2c2e40300180135040407544241d0007020070b2111505004014a91055099480000c1203000070b50b0421900e4000140340c040c201c400c9030312150342406090301005a00490050b410064450402900311003034032003140c080080b10070301d480c1150038034081e8007001c5402507200f511000042405040f245031080810443d500804c41a40c07200c601000c980203011b01040c40303600400c002c0c055400d01002034022041c0c0360a011034401618000a030a45108094070070000b2098401c00041c1e0904001044806c21680004c100764800c54440503155040200490180000c140c0000104182e984c0f2103130700b0b6a048641002013200c083d0401020b0981900c4140c0000d8500001285100c0c05020b80019400c42c3c2d0010800c0b2441e1010f280d01c007146200080e800d01d80d2b203290315030104001c41c0b200008184a44055079891404029038001c83d80390350070080c1194024001d2100c1032 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 488848920 1106 488847814 488847829
    0x70f050a0c08010c17270d0302030709060c0c0623120906071b020405220c0303080a0204050a05090402030c0315040c0501140a030c020f07030507090b010e 68
    0x2a00c040008840b450a003080e11042003202e9804a00346000d94161400070f4910300030001341d80512038075a0303407c042d1243c3c10700c000310f9000001c01083c641e00c841b1a401078081800d040700010900e88170743c4001400c1d4090f40080c4122a0021024046440422144800c0005080d980c44641c0299400ca400042d510b9200c07910809001c5480725000302131000030108142590154500c0b50380800000d1302c0050000c026951101c0540b03102c042d20425801c0411b409110615441c526515008041040040018055910520052240e0795400000c241201c0e8110b6610135541c0300c0c3e00009041c40f0300300081030b90500c40d030358a950300e014021011a00c40c5026418180c106540d40c00150788034801c50010309807640f4104240000f0b1030003588081001d0010b03204445c07030402010703c400d103800d0f0207420544640d0710003041000180818007071400482d1080ca810101e001580c0c0c04a18031 = true := by decide +kernel

theorem cover : BRFrame.Cov 488669064 488848920 := by
  have h0 := BRFrame.cov_init 488669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 488669064 ≤ n) (h2 : n < 488848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
