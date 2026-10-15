-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5219
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:08:22.352238+00:00
-- url     : https://prove2.me/submissions/7c7d51b2-f468-44c2-8b26-65fa895a382f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 938489208 ≤ n < 938669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 938490458 1250 938489208 938489239
    0x117010806150f1e2805010302070c0902030a02070b070201051504050702010b1504081603031713051c02010b061201090902040e071e1a0a2d02031c060315051302 71
    0x342c1d1000c1118505c1100340c80d148904095000c00f003102c1d40000c518030410101d00c1d1100640c0254013560068440850a071030205504005000850080510502c01031b5205002c1c01c08402010b8003415901c01c5906003801d2000d0540d030f902802e000400211030010f80d54481c64401d03401031143c82d004d641c20500ca252a03a200170340080c09401241d69010070b5801d0018240b4660310009001d000c0200400e0447c5807040e0300c4a40c2403811540051101002000a4000d4031003034503164a0100c24841602d5000710301071070702d1342230013904070669040c1c1d01c0c2420701c055600106903001c0c0c140100c205459444030750300709642d10703074010880801c80303e02551030080d01c1d04400c50f00480c4900a40c041e800c0380d140001790315645d005041c5003c400740c410050038812142d0041360388090348200042c102140c1d1036544083d0070340c0780b50b0145481c3d05800840e82c1e04254200c061914820440800140385850700070000301354032500071203080b200d2000014103680d819075815100565000042c0d00300c85071000d400d8a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 938491708 1250 938490458 938490499
    0xc0e04092003010c05030a0e07030b1303020c010504050f0108040804030c030c0e0f06090a090525060306090b030a150e01020d0e06092a0307150504050117010806150f 73
    0xc070741c5000e1038880c610035400d410300d800d03600b100c01d010000030ba040001402c403043c181c0c014601100110280e440715540d9440d072145030442a1225188a118100c949040640400c12445101c60071b0a1150505140c040007e01640e44a03441d58144031200c2d00007410809a2000c48000e5644003042890032500c0303013040c11a16641d03010f6180e500e22001c020415040403003885600c07403600105002525070783c41401c800a41848001211035104002180c40c421401044810845411030300941d01c2925003036005007510f0241d40f0440742c035880d1440c60600c50314003241c21844140c101901c001d074004603141890050603200311900f60382d480450641d88032280d5030003030b05103101d0707000481d0a6030321345200064407100c0741c11301222020303207103090101ca050230b00382030142c210401401c0ea1742d019902e007801c6408000720a44038001401c0000c05000c40d607000746041d00241400e107501300c0a90704190205940e41005060140300c51400c0d1110303d1190307211002d242d500040074140c1115103100403142c16 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 938492958 1250 938491708 938491733
    0x100303020607020c06040b39161a0c0a060c1d120c100309020604083009010806040603020d060b1302070302120304140a050d031a03060a0c0e0409 64
    0x100140603901c04501c0703030740c80001d00308044000101024903041ca406943c0000e6489200c81074550003400201c00945025902990450ba5025548800f000400d03600f8509125035400800b20f8540c50030b00a1140410548450440300c0010301d0b90395842200c0148945481d8220000400071410042440f0195621841c90f0703070021411f4000c41c03260400241004000031020b00703d4151540310081740003043c542410481d000c5803040c100014652000d8010803041c1c0e2040c0c1208905a10000c45002c15000c1c4c00c1c000b140150040040c12030010001000440c180310f03540d501c50411044032b002c150303103030341d00d034444d0700156401808840c0c02c081c00e24040380507155031030314240b00b2490ba589012158919008031345403558181e0140c0300d88408001c601006810180060300d0280384060721601c0d8000411100e02e81600601c0100361b460b0b5038903001800c3d1802001040c012080340055a400d81e240002c01503003000c8120320200d002c0b0815481255400340329011280e000d400c1001820603c01d902c003850 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 938494208 1250 938492958 938492963
    0x314010e0d030204060507030c02010e06070b10080a2f130c09080c0d0204200403030c14030909040b091018060614061e0702040204030b0609100b0405041d061003 71
    0x4880030701c0d03046030030740c1280154841c070400304e442000b0550004c0d00c10b042003507a03244141008003407a00c085021405580000c3d4044880071140310610030020b8036200c40c031004001ca2001040b0501c00384c0c1d41c0c00700c030b200d00701c240207140400e2009010084880501c00706880c0030142804003000e003021a684090700c00b0303100100c08581074050101d2516000304800c0300038400030300b102059162560a0000134644c147c081031410f900c0503503200400100400a00040d4020350b075a00004029081600b44421041ca0048142e07108224a68094480c2070b107580c5d1054202d20f8410041ea0340b0602c40e420901c4052016000c0d80c645060701c0744084855030789030003160050204005654443d00a1880d40d0003003d20568419800c4c00b0440154803194200501c210300784411f0750030704142d0350115090b030b0070035003048070302c21040c00070000d05050130441d80d9403000b40200801041803601001c00d00c41c0c03007140030762130046460303040260042c9010400c1c0484120741100711580351030040c042d220411643c0c0801c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 938495458 1250 938494208 938494213
    0xf020a05090f190b1b0d110d03060311130219020708070902072013060f0501030f02070f0314070506100e0c0c1c030b04020a09050306060114070206130314010e 70
    0x403040c0d00c0c1802d1080388288100035010660003810131412141c15041400c90701c0fa141c0c4620200b07801050b0074441d5440d451810313211501c503041c1900c006810010307940c8000b800c25150030b000b0404103480c44800d0088070030a40d9500c1404c0c08200c5000c010303101c0d0500000c80d5101403840381c200a50b000844c0011500d207070b01a03880030342d2640c0f8410164400ca000c080c0c9104907031124039180040c0042401e0348240000c1c00250700070003041011007a02c1c5690711000103074003020ba04000387c0d60107001d6076202d000c50304000c500c1c154850b500e00300c42496038400503081048411650008010f150102c824454118040303030940d2508031041b503003114042c0503030b80e00040d408001c2141d611003101921924818840640206450780c8401c46981070014010310030140c480c4600721080c1c6130361005020007401681c58410725030904007810b05d4400007030459410040c8001c0050b44109584044e50742d01541103440d5942c400c0c140c0384000900405800c05441114182603800080005602c00000203040c0001d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 938496708 1250 938495458 938495479
    0x270d0207151d0102030702120f1903081b1317010e03090d03050309070e0108011d0f190804050402270904020d060504060e120a090b2a010f020a0509 65
    0x9000515500c540801001ca90b6040300d002da84001c1120480c09020103204481c00c052041d00011104a00d003050301c0c80941008140100d204814481003001c3c0b15a03c81c2038000003d02e56009024500050219020502610030320420003c43e00c11546040e46101303082d40c00d1500c8003803403005004102c03e071010f658130744441a41c540c1004029113070700d80c100600c83c01c200052614181c84591004100502c20300550760702007000b0750203205890203030081400001d11440d044849101d404601c8510314026804009044000701d00002e00202c4210360003011403050140e03280541441c00303079402181d445400030441e00d002000740c1c40410701030801d04035948203452100302400003248003920040e400c991104c1d003041c00b1442c1508060f81162152200240f4100301003015420a0100b003100740c1d41070303c0014541000c950200801c005041c1d824404c43c40c00d241d16032002c000598104000303083c18117945c503031007180d0f07001c2d8003034401c50060400c15992030401460050030356120031140c41c4510401c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 938497958 1250 938496708 938496719
    0xe0d030f06030b0601140c01180506090616050702030c030d020606010815030601090504050c10050a09060905060412210525030f080a0908120a052d270d0207 69
    0x1500742140d0704881c224605440e040f0046546850390348201b1890b83e002c00410030818001d102d80c0806141000c4406c41244451808a090413409001c0c5039a90748000306124910500301d07a854140052814180e0f23a0f01001d10100e401d2280c0142c966505024546203008169004112240f00c1d0400f6691b9296076035901c0107098100c0380f19010140c0680c0311368014404904940c0c0103d80142c000d03011603402603824400501c8920400e03603403600256000c540c1c001c0580d0042c10100203401d0a04001200608000105e001400355116004648903003c41d82020f018072810020044000c1030124500c072020f40348081d2565105400c41c604a0f61200400c2140c480041180c03209a58580c1c0c03004c421484100e4125001403018000d07800c0159608820380000c2c0701c00740182403035107041c1042c9680f45000c282c214201c840091604182440003618503096083d494401400d81003070144a0003540c0342c00b1a02c0c9841c02108500b58901c41010840c0300c00f070740d40040c0040002403194200c6100c1c0e134680 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 938499208 1250 938497958 938497961
    0x5060109051806010b03070e03010f0b0f060c0619020c060c07110103020a08130507080f0f1504030f1202090a08010b10030c1d04090813060318151e0e0d030f 69
    0x4450b21140d5040400140078000342c0400542d0400c02502d802038142c5007200c0001c0c2141c0400c4807400d80340343e541140c00c04d00e080080340360615400c05c64500c1d04003c081140c054a449006084d0014808150310300181c0f08078a07070581d042003d07504200c60091810f24a94a031365488201c00740d9020700714160501082d8030a000f02c910f40305080d80c03010031079102d08881c54481c40880e401220305006803e004203030860f042041e801e181c030201e002400f0360156103001c64101120a1480982c25180c001084042900300c02d851804e20400e1400321281d070000265940203000b040c1c07086a001ea4000e0001886101c150081c00e41d000049a08500e05034420340d007501111004a200307404038004811212001030041165140c1400c0600041b8400d90300e652880358a50007019049103d21350030005002880d414440c4070f4080c0300206486010b001175031aa9030344609500300030050b01d9103903d04688459007021034108441076113041400a00c0c00c01503600e4072500e10003142d00c0080d1030b211902c030701503059 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 938500458 1250 938499208 938499241
    0x2030702071a0315010809010f0e010618020a02070e070c020415170c030c060f040302040f15080a2103150609140901120809011403040f020906010e0306060f13090506010905 76
    0x41c0380b5403960860004c8019030381000c008200c0882e44d50f035020400c2c8a18164000c0c400c500d11400000203846043c81d04180682d208000340c08003403441801180b84080e0001194001d4910703844801c0c050b517031043c0003111000c049050007900a41083c40b040700c0030385880f0019082c0ca240c0800c405030207500b0b10a490355200c080d501160306600500c071004403410268001c0c8944021001c2c07151500e52680c01080c160782c83c0b040200380160303940c1d2810000c030b1034822502c0003604820001e440520040e403200348038803180c5160341114001109011074254020385c0b001d900d100c84030303c00104c03560703a80c04082c29504062090059940403104c1c00b1a281c940b08890724140e07001c010842c4540c4e00c04e51100d16030380e00f04900184c1400001d0546503405030122001d1481135100b03184182d5024003501c1031003070080000c1d02c0d05050040c074090040e425034010274401d80c003180c1178418040d03001d02d50b0700080140482c40c4114448601c1e03d01c02c03a00303204003c5400b5050f1082200e0510850b142c070071301500c86801c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 938501708 1250 938500458 938500471
    0x30f050a17060a08011503050c0a0b040b0d0618090b010501022d0c190f0b0f07022b08041412032d040905060301060e190b040f02030702071a03 63
    0x2074154140c030307641401c21415080310001d803000302555291100e140c2100c92048103160b50012040c002c004108007003016202119007500c0b81007200380740403072903805c90080d40110a00c2c0c1d040400c4900145031a035001000400340007008000e54880710820030000e100b02c800076510007043d1800482c0d83c1d400001c05404140d070540e52600307490160200c2040004c08150300080e50f0245c00d03d031000990703d00e480b0390800c1c41002100d4450a18220590541c15040d40c091094030900f4802414604100001d40303048540541d400c200030b0322408503540c0072541500c41c1c030101c94074500c00035080c01a4080500203075541401c941101400d818100000540580d1b03544034258400c003c0c04440c0400d5545094041c0380c82070340c031010039030710700c0044002d50400d400c01201240e449c1d08204851409006e83c00040c901000c10601340e04201e10b80310035112161200040660700d43e040007019440b55441480c4240326143d0440d20781c18400380094441c1c0c580d1049a4040030b45045a40040707090b4002c40b4041c11 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 938502958 1250 938501708 938501717
    0x3052401020d110a020409080a0207140109120201021203071d0f0f13061a210613150f080c310b12150703150b030a02280c030f050a 58
    0x20302c00c0382107542c01903d107000c0a82d070041651440060b15940603094038184540d0354241c0f40c451942c0d0003803502c80141e10054402100c61148255030741c0005903942030318034114054010b0f194030300040c2d01d44801d103a40d600c0001c0000017000403903640000e42d84540c45441035030111030b032051020403900d42a0100200d61001c00001d100141c0c2c6889403804500e403151041c003103a01599010400c0028418001500c07511000045203c40c088024280c21040070101e07107021058107040012a00c43c60400390700b03005080d603032081d030f0a28400b14141c0000130200d129404203544c0d121840a40c641d04034030113060190108400c0d80018909680205100c090309000281c8284405d07803581020740742c806441900460302d0030b05146144018005210304810f065180416414911002402c44841824038100c900c0d682000b801030300b000d40102ea40002c0100e0000d0303110010b01503080007281c0c2d403c007100c41c1034942c401540e01071a003100f144504103000b070320341201c10484a00152068800c0151070000103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 938504208 1250 938502958 938502973
    0x103050d030b130c0807080a1a1504090f14010605070b1b07050d030606020d1106011e380f1219020403051c09030804090e01110a0305240102 62
    0x2446980120075a0340c000744480401d0303c90028003800c0340c184c0301c640c80000c1d03001810049065088613907103030018003c800c100450041c0e0b00105180000b1001c410303100703000110802412100940544010f001040010841901c66111a40052220b5010383c1c92074072070000000740041c01482982c80094011226004554036000c003e9051310b50902d024041010074055070000c50810080403020740516100020030508011019103003916100b1400104000049412603102011900904444008009924030034007400489001c903200e0300040d809200b08003440d0100840d00315499090414040100340e9807011880c4408103101c1d14091141d068802c00c841c0341e41c241c00d2051030f58088a48099090306801d6104a40d00b40d902035441510300b540440940102d11042401c1c3c0f400c13490072828480c0b145455540e0b236070070a0141d80710b0010f85c07554036152000110001e4010140450082510320707699541c1d060050014001610440890a80e0010002e401000c03903410103a40c00058004050b40c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 938505458 1250 938504208 938504233
    0x605010c06091a0c12010f0b1204110904080a030c0201091a07091701060512010b0d030f110d0815010f05270d0326150603040311120d0c08010305 64
    0xb816024508403821440100f04a0f04200d6100743c03a402189104c8469a84500c0700d0703078002c8481c1040c1c0018001502d5000100400c8160f00103d41e4a01e00c80041c0c02a40d41c2e5a09003400c0c688038015081d608001c50400700410041060010810541182c8040181c2070000e035089007222020f41d0000c1c0b100000b0a8402080380b00900d1040e4094158946280079545802541041c050b80900c03010007a0744400040c0709919000c003800d402005514020011303c04084000354405c000043c018003032041d5000482c82e803038850064003400e40c2140c400c9468000c403000005003031440032500310184050b446540c800c0b540c42801c03c580000180e549640c2402086240181c0d4051070394403c00c0503600825840c140d50b04c5021903c027101d4000c1d00d1f400c03143c039488080f643c2e00081d887d031102c0c0407030031100402c07003101c05029500360b517405c2c1940d13031684a94951030b080e140ca01c80761950225500c00c03241d070700c0c0d60040c2d4035000703001e000d0321440700740130300202c850050b01d1000b0203001c010315940284600740745 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 938506708 1250 938505458 938505461
    0x1080109051608190c02010e010b0f09010b0c120c07170a0209040b0a06080f010b04050f0903030103080306010c0f0c06120608060f040305040f03081210030201050d0905011d03091002010605010c06 86
    0x100851104803007642280c2484444044840e11740c94100580d4480085809000c020303c00da0386905015512090441404400507448030014003e00d100d03082c011502c2d101d003642c20004004003140400d10307a039565500c0600e02e9980d840030f10551601440540e12102880c030702191001000d40c0c09080b0302d5154441d5600c548499500400000c803240da101e6000075038441c104a001040c1a00c03900018080d012842440182c0d8801004241c0000062041c0803040000004807070440390084100c540341d4884200480c1c00d5850340ca006003101d100405400103206a100c200021101152100400002c101c0007000994889100b80d40071504860300140e0785400050f50554414480d29007940380ca07480c0e81c002322a1007001d400948100b000843c84240c1e40c030a002030300ea006044000344030150352442e40000d0040c411070744806499900c42e92480100b1070250080800c00c9544108580d5001110348150380e01e411800d0710b948901c0100c0f200342c292600612a1505642040c0c0d240000340240d61101c07170 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 938507958 1250 938506708 938506711
    0x40207030e10021c090905070206041a070509060705160918020d14010213080106051c112b020411040e0408031f170c030d0e010e0d0b040f0201080109051608 69
    0x10250b01911110001e4143c01c1d00c80a083c1c4d902a0b1660408542070010700e03812502e004101009550000c414080400c000340e0b542c4014030741035000310504d603450701c10881d25400750004181d08900c01094900400001254001c2014400b49207481956075882c0804242c0f41b54107889040303c4c200300d000c0703005418000c88441035a4000d640103001d0300341c0218040c0c2260702081d00e407801003041c1c110a000e841420f002d06801440704503402007001c00c4601c4c64090b9500c0b907100080150303003418040f0300243c50f00813103011102c18080d21620440c2600d400c4001c3c03012198007c0340b18074502040c89171186021016030742681c4840ba8046044ea0b81c9a40f0b511030780d400902559923090344c1658131084600200c1004003d050401c551000c4c40041d941c48916001070315010600c20303086a0141e90301c680e4401c6c14003020b81e40903c2d150300755004d02c1c008100c510f0800c10014140084510400003440440e07120100303214400e076500c58503607a80764202e03000c441c4242d4000a6845100386940d0003140700b0000039 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 938509208 1250 938507958 938507989
    0x4120e010f08150d0b0406061e06020303181e0f0733020f0102031003020907020109120f030f02030a060e1f060c020406120507050406080f071e08030a0305090c040207030e 75
    0x60308504145d8860a000100c119021038030030b03464510a01114030200380800d246031004008072041d5017840c1019403a40002070640e264055565010700c2c034070f4800c014010013003958000c3c4280050f24000110380f900c6459401d00c41c14800e000c0300150482c4003a1612200c0300001c4110004d808101d03414807040c091103c4440110710a04c980104480170a100450045030841298002280b41d44148605608010440420769140507081030103d280320809107000c0320b881c0f40111650385100000d400030101070740e602040c58030110401884a22070b41c4a001590742c009552442d03a41c800c2d14004541109642c01c081c500100c40d4100310450240c2c52030240c1a02c02040030940d9501c543c04400c01524a22048d03540354060f800410507070506200d2803020700300c2c26005d841c0300048101225074402e43d0344243d030fa107010041c1c00156000d030154100c401506020090325502e05003598010b0207071205580c4031102d401144614003581c6454404c641c0c07150790585501d0380a020030b404002880e100310124 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 938510458 1250 938509208 938509219
    0x807030503093607080106080420120f01060513020406021207030917100f021312140708030703020106150c2004050108030a1e0e06070501110304120e010f0815 70
    0x25240c1225000031103d488200c000307012181881d11901c000d00711030041c2d0050301481001420321022801541c59034a08080480c42c1c2d14040007804045282d49206189008207030040c01c04d04000004107402410461310126501d10104a6010368031041f0300c07e43c80f4060160f13110744503110414010b440038140d41402418040520740c2d8503c907141c0b00d00c08030700c1d201c1c403544c001102000100100b807040000700b0399002000c40c1000514070803044800c80b01e01454003c4425450000104044078001150314500e150030b945041c2c4e0350b0781640e9540d0300000030031805075003050804a1640030355404408007102c240d031800c481034403a848042118a8005148203000c40c00c0c03007184400d03122806558001c2464400440e964404041c004001110b0036460520a1490400c0350980a6100708644004042194031561b901000c1c1352184c010801101c40180e4501c000c0f080100303004041c805a00b070000c403a03c410441c450b0300401160a80103800f11a80810061400700f1b110594030512421070f01d001802 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 938511708 1250 938510458 938510509
    0x71202040302030a03050a121a0d02040f020a0f140a020706030c020307050105010b0d0e0a0c0b0a201005011d010306020a2303041202060106170411100f09080703050309 74
    0x100c1d041a1013420f05030040303980090030f0400e441d4022451004103d02002c10040800c902c00c4288200100c60480d5200301080c4006d201036580340e500607884070142c107600315500d2801c0e0310080d01c005404511000070132000000c0400c0103000b001229980e0781c0c0303540508900c50030704600382c000300100950501144014000b080015400f4031035280a04a0000031344e866400e51407030741c801e80d1a03259880505400c110010400190840442c0007038940310780480d40c07034000001c01201c1100d00c0c4c2200844868080320046841b800100d801071a5114182c000e000d141e803581ca540042482c40038103006000180401040854244c2d4081c044c081c50520344040150140f205414003a184a05000400c05c000002d10040000b0445800016500d80c0050f202541c902440a00741150191a01156003401e40c000750810000c00c102401c924001085481c91840340d40f0014000218407013080c1c04a0080c0c0c00101d0040c0f00003c06208032a440300003549070800360000d0200c0ea0b10440510b10b00d0300380b6102d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 938512958 1250 938511708 938511713
    0x30510080f0c03060a06210311060a061401030504021e061b060a0b04060e1317070f020f03060108120c070510110d090f03060207170c01230f0712020403 67
    0x142001d50646000141020031094042504000c0040c1c00c6981c1d1511b00703030040100c1ca07030054480c2500300042d91030140c0c65240d401d003601e00c8031030810400c40f107004c2d4504024030b00c01c0e654440416140c0c1d034450f51018101110040d4101c410a9502940c0444010822510022031070490b904090024213014102a601d80560182208a0107510105e80050041026040d0f561244515141040b10144110b9150420075913941401030503010702411030448240a101ca4040da0007030400c0c450031090b56070040c0c0d00300b0070004589080c00320f01c900800224404c180c54000390050503a011140a01500c9112001c296030540c01624445403c0c015410b000900380d807440c0c00f03c0c050840c0c644440c00e0008030030740002e0401e0b607254080005c0c0400000203014400340309540d5001e49a00010040c0d0340c5540b030a0801b50115441d0116104801c00030b2031000442c03064001c580b001030803641c2420300d583e00854419500703000301c641c0154035840b4400504440c0c454582225020b115903001450a0307100d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 938514208 1250 938512958 938512963
    0x1504060f05030609010921030603080f040302190b0d0c02070e070c0c1d0123090c040f080307020603130f080a0201090c05010309020102100506060904060f0321080703051008 76
    0x15885860111920030003007100e4102031100d50b5104080f0402005401e20503640c0c41a03e40100c001c5c50705488041c0205d081903030003513102c8405990844925030711540e00c00303041100c0da4003600080340a401c0d00c85240004104006110082d508210191800d14080100000c002c1400d00382030401c500c00c2c5503000440d685c4440005001d001d660741c0e451015840d0f820980032100b0603500121824071262120403801c1015017110381940c03800c00c41c10751039000420f04200ba4041d020b00c8180d110b04460103218126144200800840340c3c0c50603210358050f511075000b0b4507802040d0000c0d4001d8801c1002903859804102421000d07440f44110704d600d003c1301d031910358003a0000a240c1000d42e569107150014400c1800045000303002c04d203402c0c044880b203503000035190070303c200300c007007410752110085803c40d07848606a5140c00c10280c0108035640d42c90480c2e402840300e038401a15115850201e441c1d8000b00c0c0549501d0f0490340d901c402d03100b038462160807001010024003240395003900e194082000e9006 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 938515458 1250 938514208 938514221
    0x1e0903021206150904030c0b07110303180706050901020316240e010b0a050f121c0306050a0510050423060c1005010b1905090f030a0c03050c0603060d08031504 70
    0x6032801807a180c0f5180e402c541440410495007840380c0d440d00100f000203580004042c0c0c103680d02001d00c00150300c4031402545c0a82c030340503c0c40020300000c410013003100c40946000f0b003159010000c903654603a489005440721f2041e9400311340181c10401440d1480c00c1c10003030111459108819800301d0303902180340c018587c002c0c1d022000e0300b00d450300c400b020980424005c02c01c0c4d140c4102d50010004d031070040020320b0351100c82306580c002c0d0042c106044100c0350074850b414101048a50485445132240c0300200140704601841e4404c00d400030000c28142000103c0c0c40c8a29025140c8034a440e05041c2c119030800c02950340640b0008954101c015542c50b404081e1540001080092144469010341c0e5800c0d01c0c030507040118080424401c9649407c0c01c00c4001e98410a24182259600d04d10b0021840782c04c25405841d0f0103110710b0611108014000c1c00140440b8024000e48500702003003007c01c0003900c0151689a40a081d114101d80868100e81c020742d08030310003038146030040b940c0f90045800d0b1645c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 938516708 1250 938515458 938515489
    0x409110312040f0801110319150b07020109080601060822020a1214010509030f0a02010e03040e1602030f1c0f110406090509160305060d060911010e0f011e090302 71
    0x1400b0808100341d04403120120040e0010000070310103400b0080d90481207010007859401c40100a89840507038165582c01002d0744898503880d1580c4c1516041214665400f98100f01c0c0015624000011420404140310741a03803029071b0f6000c80b03a203810340901c1c110748001a13012a02040c80c40210016542c010140c0d00034144501e4840b01c544450070001040c90200c00d51191b60b074100000c20401c84004001c8950303582803103403540d480d00c6111504074010103d241e000050ba00c030010700824002c51540fa0984282e40321081900c4191428070120380741c0c0a2001d010050b05014007411007440020641070b510f4200300b00c40003460122200c6010107a50840c40c04031508680010140100b50340048444007a000c00d07503002131a030030020340e08151446c0d0341160004042e500e07004590b40c0e6480c0100c01c513490390001070500c80c20240d41455220484082d403030728046090054100b841c0d0410100c400c0081c1816103a550039120441c2d50030454602c40d40801041080716000440183d858081c0303143c0885 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 938517958 1250 938516708 938516743
    0x161401081e01230d02030c040e030720030712030e0103020f2a0d020a0807060504050c030a080c060612150a021b15010e060904080a0c02090403030b18090c04091103 72
    0x3140ba0700500e070303106090f402e60048181c0002207025840000b820701840c1c00c160b0f00042c030274215403005030541c0210b800081004400301c0d0381002500303a158468ad0f070a00124140c6164654481c0d01503902c03140c2d540014003060b503130525901c840d030082e03010313041d9020007074007152820883ca1075202135805003000000710701c0c3c200d005040f81741100300403520001d0013500062004c42c409032240d05040c0603040c1d0007040c158071400050100403040c400312040f42c1e00501203031241310983c038061185401111002469110b410b00103801460304148003244c0070004806466070741d94403120041540c034000c0101124a40810141080c564468240501ca60010024210820090b0030614070040c1c1a8402c030180701d003000c1440100d64a18138056003166000c030003a41c1d91011001d0550340c0c0c0c203c4070001395020040074200300505805400189a298088421080c610004140c42080300000d5800a18070b600c403101400c900d04150740440d40442c050981300258240c0b42000074508220865070b0347c02030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 938519208 1250 938517958 938517989
    0x10f151e12020102030d0c0c0c1a0d0f0905031308010b040207020108040b040501090213020a180506040e1009050a022122140102070614090307020105190302090d0305030702161401081e01 82
    0x50b0700788501e008ad1602c543c8281e641000c20007041110701548070504070751a0b540180d0079881d1301907444445100e40c402c0549444a900707001c10b017024600d41c86810f24a50801c0303111845132a0074401c441145034142c603607800c0782d255030f00e48007001c1c0300c010b1003180c0c81d642c0c0e1503e00300942c0d525041f0f5001c07121070201c09a910700110000400c40301403540c6050b04140305c10300c01e004a554220a45007541c5c40b0300c0c2d01c0c2d50180d0f0380703c00b03015961007260711240d0010300d40b105210302c034105900244000018030751444042d410f05195043c043d04115403080d001115035596061205d0f11011056129001d030404561407228203041e1070880c8e1088c03108813106039450700452410700321107151550109074800518149091500040c140c1c0c4a0100e42205116003109800a05030081c3c3c19610b10101c054a150581d14442c5400303001c82d4030a80302c5502620034000c0d0f81e41e41e0206c00340b501040d110500a003458400b4190015038907090060301503200581640109001180082d19260003050400401440b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 938520458 1250 938519208 938519213
    0x11010b0102032b0f05061306030f17160818010206041a100b121807290408030d0504110d05070b1614010603120809032a010f151e12020102030d0c0c 65
    0x60031f08094001345194208041000422018040a1290b5401c8000c00f00c0ca032021051110796441600288025210341000400510911601601050100701c203e100042050001a82c3e01c9100310303801131102c006a5500e0041c0080101c0e0550011103003d05d41407801d884035802c560341c0d0000d032010380c2401a01010800229540b990f141054490580500f52407428481180045101022040c41054482c0703108183c18203da4119401400d0000a403511215500110303809000140d0b000c0d50380c600c0554000515160a402c0074800ca0741c4140144120744c903150306004a03410191003071042c022038444540200c0c0000003480d1450440600004100c3e0071450072841201e807020001081004400810007191000012583d19800400c0c2d440e07140f02d0001d0380562a00c103e001e406103503500b8040c000282499981041e82c45021801c0c000d0216078130b8805941070042e02c1803000d503a0703054289042100800c1c0c031601840e0140103205503841d2101042034081a6902d00158200140e12840c442d800d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 938521708 1250 938520458 938520469
    0x40603031106060a1802090a05090403020d0e01090f051e06160b07021b01200d020102092b02010f0c05030a0c0219030c17010905060a0c11010b0102032b0f0506 70
    0x83c00902101c0d8894801c0c1403480c006100481e00200b05801039000074034807a02d43d640300c0020003d00e4002d000b40114905840d0080d10380c400312100401060304188407003565800751501e00151600e894407080254078050402004100f5034091184a0882030b1020042ea01c0341c000500ca070741a0312061081150840c9050b440c1544020880d03000c640000d0105007801da8660780842c00d4003000d1800040b1b0a01c461524a5241001d140c11012485042480c1c40d0264064010700346d58001110f19118150000d94051000d42c407012403400e0849030881d1070340040d8081e1915840201c00b9180941441030103a0b2000d141d58840e000001c041841c01ca141d80840c9085911011017071300f41e00024000511b5503940c1420402c940c010141c4a40c6c0c131502410b042c0100354025800345820904440d0b4074100050800020020560b45c0c0c000207401407102c008014050040e1104e07521b06030f0085140c012040740c1005c6100b096100381024032503c044140c2c0941241c01200729005d0356220009807400c0c00d404100e03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 938522958 1250 938521708 938521711
    0x14010f0605100201020711122a180613051f0e100b090906212506080c0d0f020909090d031a010c293c0601030902040b040603031106 58
    0xb011a8010411180000c031580000c2400b45010307600070340050035000881c7d0814003510301c6d4072000011103002e41302c0c40000660803c0809001d5410070102402851120024a8201d5045400005401482910348820350100d40d00c081c00e0302c00601840d07007132078600060399600d5101c0085200d51006201e00e8800d400640b0307000b0642c0c044c0381854600100046840b2500052406110340b06c0b0b00740c01c40b0041442c2003100121901641621000310400e9594214074000c00755160745140c0090000c03e42c00d0003489120300400c120011b81d4103010b04000041d010b000c0310404000c00700d400b80182042070b01d400391140d000d0841c800103440c1c9001c2130724005040300c1c900c0709207480c41180000000d001c2d0341c021140c1480d039904101d6072801000801c05c500c42400f402c1c0001d4201120440803c0701c0107943c10254684144201c00e103000312050040b50a0410b5103003070211400441400200f00f4a60181d80001e0751141f01404c08286003401d80c000a0460f0401d500580200e0112034514841010502410703 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 938524208 1250 938522958 938522989
    0xd060609110403050d0f020718050f090111030103060b010c06020d020a020c03030f0426070b0a110d1b0c1a0a0e090405070314012012090601051c14010f0605 69
    0x15820b06107562901c0e503940030820410402c1c020107104005031544280b014130060403102100c0b440c80c4c2c422144400003018200d80c210301746186400032541030b00060096004007103864002c1400d5034215110407000300319000c80ca40c140320741d540c05400051114005810103850480005840b0b1015000c081c0c02d00354880420741c460f80041009402d50140720050303a0603a0844c41204000c2040c0030001c030804500c10221114a2041c0c100001d171030401e80e001414010107540c0c2d41c62004805080217561005114846808211480b480040a6680c3c8041034019800b0713980140206598001c5032121030f51211128003905c0001840c0301119400c071400d82007034902550050841c0c90642c03503041d01c1d491103010040c80700c07203d1100c60384624401d4000ca102410406102c54040d18180304000c4580d00500c042075811003604001059650040b07034050480e44003400d00500031640c03040b01e5500b5001108100d0b60b40320508500100f00700300748541500c461807003000160680c2440100402400d910414 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 938525458 1250 938524208 938524241
    0x3006090506090a030f0e06130f1805040803061512042904050d0503092a0f040e060a0b032107050f07060f030c030b090f060406050d050c100207050d060609 68
    0x500003584170b840a8415039291070700c1d45240d890031002036107a224550402d01000714080e07000c10885440000c10080311603020451103000c0c03c5654803419680100d40107030004605200051060800c10f03252900c0041b81600b0030b2600001301c41100401074165029141c03100e01500b03010b01c0200800591401c02d541400300b0109203025500c1c540e035a09025a24001c00c40d01002184d003000040000140e581410f4204580d904411070501811070038550300c1070310900b00b070102d282c040e0509128918244140001410150391031301c01c41c070041e0900852440c2c1600c240212011103c4800e42c0403503000950310300c1582c1d6001c2c5400c003185481d00c00d10517042c0342d81040b03404211054000203c1008a401420041980030080c0400ea00900500c000c05801c8210340041041403414801c0152107403004482c10040640c840c000e0080402030010024602e40c00b01c0040ca4851034154070215003240c04e48119460703070740c41e200402c0741e43c00980c004803045038030703920140514a014010265407001c401d04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 938526708 1250 938525458 938525473
    0xb0d091502091309030512070e0a05040b060a030908190c05010b04020a09060c0201140307021c020607020c09060301020c01090f050601090c05090603190e0a0308011e300609050609 79
    0x703012a500a00082e4400765640608400c0600a50587c0c01d00049081362044a00d80030001400080e03052a03040e2107400ea1900209152409118841c13805401410140c1011000c232816401454150400c0d14104802d00161040000d42d0840c0c0b0600801580c840c4031040f510301c0c00909488609080d40e10590042c021102c2d0154803080800403160300345441c000354100b50005944840551202e822603140c00010840003c4c0c0010f1051103c804240c110074080c41011401c0743c031210305507600300040c1c0000d4905030162600c03210b09500032000a00040ca861100400c607400c55400420072121404201080000e100302880190300400d10244144410b489600c4010218400c0903865407045001202081c6441d0100c0c028400d4010089400c100340107010403110313034400c100380046000440c24800480c0000002c0c1090799584000315483d541c15060100a0003a405580070550204141e41084008950140261085113004039000205030a0508000b41082c00003013103040940d10048 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 938527958 1250 938526708 938526727
    0x10f0905060f150a150f090b0307050903150403020a1a0f040206032d010503301612200a02090a0b030a05070e0121030e0103150b0d091502 61
    0x15001da48080c906802002c59500c041c010080400340c800c00039000640314a0100702c8001a443c0320158010303a846440161158034000c45903050a4002c540004005001140e40c04e80500081c1142160007400c2d43d2120144e00c000a900d42c00c100c0d015401640f04081500a01c4510b291400c0a00d0081d0800301c3c09140c0348a03914888000600024058100040000c0762140d0107944225498034504291505451280c110b2071490028000c0340d00c28002c1c802d8040990f000059408510520b00880c8540032041d9860481c281d00081e1000c45200c50740b04c40700000032030440780c4c8284400241c0f5000542da01c240300380d4115508140740c0078a5a8031484103107002da9100c0b405643d20030005a404161444018082810019010001481072040c640c01040c2da110f8810250705844140442c1100007441501d564805c0c0100700019000c620410340300c1c8125442071f0486103050204146010303c1c56070702c800341040d83c0c1c400d80071580b2459498000b0820401d0304020710b0310f02d1021031b00030360030700003902c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 938529208 1250 938527958 938527963
    0xc030b011b0308070509060d0c11032104171b070f08100e071a09041505010f0c05010b0604080f101a09061f08040c050d150b04061e030203010f0905 65
    0x407000030b01401a1640056039140c410701c122001c0300b030040c095035250406c1c0000301000d0250401e4a0700495a000440011000d000041d1440d0454940e00f9006a100c00e070000800040003402c1981c040041d041c43c05802d4204600400b01c160494050000601d4284480c42c2040020703080100450f21208080061500019914096030b82c24a0001070003440f44400701c0c41c09110754441d41002038814040da08000001014110240b0203680910500034502c2001c02002d40a0143c140490015215000e40c240b0070440b10b01c60340d11030400081e4840c41e4100081d1160050f5000705501da005081007407503014103004420f140360120704d090001e50540001c10151048010006004a5415000a059543e1120701b03070402d0509542c059410819400300514a40c01110305480c0104240700000396814642680a01c0a8100100300d01842424a034100944090070b4050f9000d0388420007c545001102d5020945a881d40040c2440c00d00c2c602c1414251740e07401e07001e44580d918080d909004518003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 938530458 1250 938529208 938529257
    0x12180b030c0d06050406120303061205070303080a06051c12021f0207060920150f160609050d020f010c081003080703232124130509010c030b01 63
    0x2166401d40e2034940221502c0300412581c0d209940c03044c10b1140c0042c0d64942d0102004030076009a130148002612031500340c05200d0780c500000c0059026483c10070200f4130608001d80c01100c50a408241030780e9a00c0002c03140d90b2a1800403441b030300c110380d42a0800031500800b140a2109001504550b1320310040e607001001400c1003200103e400207948400c204481d40400780b02036000c038061081141052008428000c004281e0380100b000054101a110000d420f85c6c1891110440d03a500e03245003039042c003401850b8803008417199604c4051507800103005000c1d0f402e0140c403035402011510740380a2843d081d00c0f01c0e401e6040c140804d04090040030902c913105941529005000aa070320141468103c44507030701000505407140a02c0f6094184d840b03603200030b00034804180f1880c4d440e400c4941c0b00c0650044243d0745004c1d0b10900c1e010b040035000c88441c00007400300c80280350b410041207020045042d0f4504070741500b05650b55480c07405031a6018400e00303074000802c0c030f4820451041c41300d04d070306c08050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 938531708 1250 938530458 938530471
    0x1002042c06060a020f0303010b04050f01090e010504020d0b040509010c12090305121b040315050a0501051806010306090f290102060c0c120a050d1a06120912030412180b03 75
    0x60b40402c004d000700240503000c0c01881c00c51395a5070b0f59100740e04054100c3e01a551003907118140c6c0303d1083d80b00e40c7d105000e807000c2c03000451a591900c41000f009610100c0798250342a02d4100148c415640e0b44a06071180d2500d400102c0c804042d000c0050081101c1030001318000d1030301d0700d0704000c01c1d0b0103000c2e9080000c070f9881d03c4045440340e2000100300d020480f044d0041d00300000740442041130031060080407403258030090001752140c1c1064000c0d038009000343c0d47c00c1518040d0400354081050710860b04028103040014000f85c541c446002a941d64110610245466000034121201010000c0580c128807000c600683c40045000030741302d810242080c00c82070400710f2003000d60398090111128020040d0002c540d10208a036014025401486001c041d151501030b51000101d21108440d40c0500010496850001c0f08900141c124402625603400e031b01c10302c1001020720000d1320086002c0c03402858081c54607515120010710005094031004030203844568100320901103601901d801c802d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 938532958 1250 938531708 938531719
    0x60c0b09030f070f05031201031a0f15040f0f0606092309040b0916030b040308070c050304170c040e01020910020f0c1c0c03060e0d030612170c1002042c06 68
    0x300b00341845d92550180c0b00c90041c100368403000000c00c10442800c0c45903510442d04040790035035101c5468142005e0704481c00c000c107001d02203995038030385404d41c0b090401549800000601c101c05948802c2221020f0b00220040703803109070240100c0741e01e925940c0711604412804540003602d10041032500001500c000e1100046801003046407105100100212200d207100300300c4160307242010341d0408003d89003034001c02c41c0b10000c50440f5128a5407187c0701030700718000310701c0c2925207a0070200ca403010940c80590b034052115000c00075520381c000e04040b610700c1c40c005615000310034100f0010000e01051030040d503000c0041414002d01c0801d4680e0130f400c044501030b0103540c00c1d160310403240481c8e58000f040108840d4001c4108015948201c2a01c40030404503900c4220000d410b4041301e9282c00b400d07030900d1550071301100051881d240c0340201503c109920f8180b0300550102c5250141c4412240810340e0042014403e9080342a089006d2208031000300c2c02c50011200015600d0001816490051 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 938534208 1250 938532958 938532983
    0x8120702071811070f0807060e03030a052413062105061e0604051503010c020109050601080307080316030b0a0602030408161511191a010603090312050a15060c0b09030f07 75
    0x1c900382d01031311482c7d50044410322125900c240569160380c81144c910080d60f1810000c142e03000c4645a10b4900d419010104c542d80c0c940400402c076190700305042d80d1294035100e00012074580c040c595050f090705095840008000c16070b160403424224010407030300004550400000c10314044215103034101000303131000121900d030102ea40180d84651400580c1542c00c0c041d250406560543c403600300b4900403015a507180c0d80780d214003a224070540300e010302081e4090010519407026500507099268a0382000961503803000c021401c070fa4050b610020140e00b0201c3c0821401303c081c0607000700b640b000c004100f64039003000c041000c4101a03151000c00c12416044c0d14100d007030104000850b2200c00d0001c3d140c441c41c14a042001c200c0000c5010030880348150000414078024003401108076855240c0305070401e0603001c46402410000c02c0c030a6034540b204410301041c1500d141400141c09540c2d260000d01c040e600b000d0005c1c2030050041081d507842000101d10303c0e10280d0a07101c0041d0300981c40d0500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 938535458 1250 938534208 938534213
    0xd051204080c0a2018070c060b0406030b0705180901030305070803060406030204151805131b050603040b0601030b030f030315060d0f060303111b0d08120702071811070f 74
    0x74503040034801010200d070402030684180c00811000c418420843d8500f5064480c00da1116180300305031501400321f19221292400124140c2220240c443d01400000f140340d81c82d105c04095a038252011000324400084001c1030800c180c0c0d18110141e41075031400c0c2c0ea5455a500204280f1842101030001040840490741da95a6500000011a001082840107003001d00c5031006000541c820111110701e00d6180e1aa041c1581c000d681c41400214400c0b0310a40b000d86400c50300002c0308240358404130145002041d40d80d40c8902440c0250300600441103c0c1c6800800581102d84190b80e580c4654801c0f0403484e154080082202d902242724018200041c0d003030004115980507146d001041c0300c1c00c1c42c000c004102040c1c3c0c003d500300d901a81d030b14880d1481030302c101d07521400c816905441c02c0c00e14002500310360801c5080808050b10848145141492a94540f03030000815559040107810100040201c82035a449000c43c0d481a61010001c401d40042600c415105161009002d0940a036080c030a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 938536708 1250 938535458 938535463
    0x402040507171005040f0b150c03040e1504050106020f120a0c15050604060b0720012c1009061b0c080d05072f0103090c0f03140d051204080c 62
    0x15080e095041c40b06141c101102e40120800e45405040e0240b03107071200b41000740c0030900441c0c610040103460642010040c050390394031540800070311055803004120000b002218080d4180c480d0b04000c400d013811049000801081e248103074018801c43d4413584151a0749080480c81c005680d0703043c584c982c0d4401d890f0a040d1101c0c16481c1c40680001c0b2400000b040056054000501c10380f0221020420300d40c40f1000303441180100d40c03000c0d2030b0030028110300c00c076040608100015004141003802480c501040c43c0c0466180c0720307400054210b0202005030450501485030030420181e400c10440607401e00000070901d41e064031a41101980c4441c14006001e5490030600160042e030042d41ca054425000103441944241e0301101c8a152a0821100c00040015504440c44030034002080c070607076240c0114082c0c039000c503082e00d0814a800c0006600c02d10101188011407080c6100501004101406418988070558403030900030100f1008403044001000e041c1e100742d01549190302c950030ad0700800d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 938537958 1250 938536708 938536727
    0xf02040608071107051c0b01090207030f0305090c090c0d0608062a0c0d09061803020f0d02041e0e0105090a022209050709061e0510030207050f03070f02010906080f0402040507 77
    0x11307045540f400342035506e58003c00c0750082c2603000d05003d01c8140d80e01c0d030f1880203e108204000c2e002030740c001c08540456200ea08a260082d46803811070310303c100ca00000551200080d15803070700014000a215540b00d41601943c002409144090402843e14518450500d41c80c01c0c01c041803812050000040b8014020503034266a03a130008640e140000d0a001809058241c0504c40100311300b001081146203010418005595002e0080c182882c502018040312140c8094102e030300030f840718818a90f1800141e0412030780101e4401c0441d030407000807046801c4881c0a4100304c400e81000c15000050b0f181c081780c2c48001c0c040c01100d8009242e031124858020916260f001b00b20b80122400020801c001d50000c0b01074800303000c1090882d000244c100200c4821a2050a03000881005410200c038002d40c00341034010300607802d0303030b001440c400c00403421944840c0c070031201c411880c1e2083e419940d200101c203026111f20f00b40843c040c1803100300113000c2000100002d1056440b2000104201d104200301e2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 938539208 1250 938537958 938537969
    0x9051c08030f041b06090b250501020301060f18122108040b0a0507090b0a050c010f0f1805030f1308241e0103020d0f020a0f090f02040608071107 64
    0x2a5120300b01000b002c558071809550655441074500144034010350300003241e00071150503450325007806103007a4504a81d43c2003c1c030000950403001c01c8a00001c4080035200790801d00c518001a41e96040c4038000d8001030060040b80104840b0078001c9031000540d0403880155160451f0384802040c01e440c0c0096040c189080f1702c0c00742c0c08005103010f00786420800d143e00551150500e80850b80d00c0c6003c0108445080b5245000910705010801040c000303007009240400c4580b07481440e046807003c070103080d20b000c0d14402a10b00d031f4840c080d00d0303e282103110f100303800854000381c0d110039071440d02c030241c5d0380c01043c034030315804080054604039551007030203000c0c028400d4005440c100d074034500c840c5402000040c16404103450050024102540b0340c04000e0401c0c0750903035902444d07403c61b024000708405030002162030f602c909a050025130358414014004203410b24001840c6414840d0b0a4141c6440810035005d0034010310080c082c40fa0882d00b860f1303026070a4980b00040e044002d0000d0f24028882d40b05 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 938540458 1250 938539208 938539223
    0x60909061a070524070201050a11090f011418040609091a270604020301050609091e0a170714070509041b0306020c0a0c0e1e2a0406030f0b0109051c 65
    0x5003001040113a840c98030800e441e400070007155941c10001400d4603400b000711040c030001041400c400d803a001c2440c60603200117140209442d401c02e80b8121503507000a5030503818446910703c1d90401d280c1070041308064218400244840b0010365988032440c1604e08541701009003440000b00b103e00070600150420010500d018280c0060411098441e107041c0d405030701079400c00e40003500d10701700800c61a0040102400800440040341d903001c074040201c12424002e4010404080d0129855400c9261600c0580c0101d564600c0c0914180c10075401c8240042c1840e00418804c014954802140796441904214010f00c04d142e400c0000c41d03a91416080240f00c1480443c019001e0603000464200e40d52041c911880e0403500c2e210002510710301281c00c00760000440030400300d803001c12201d558120055510081401c10000e003a800a014007541c10068000f0100d01003204650502418400b0301d51681c0070050222501c0c0001c2c14040766000c0c0a024408000c0d13004a89280700c210750100ca44c21180 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 938541708 1250 938540458 938540503
    0x71110090b03132a0b2203080304020117010f05040e01091b18050c030705031305010501080d0e0f030714011e050304061a01082a0f03060909150a33060909061a0705 72
    0x800c048e40c0d40068406900003404941b00e80c000c90420701c0e071a41658240300381d244e07489141c00100800707050002e00b299400d540310500301e0009407111180395000c0415402504c046400c21048400d5800400c0b400901142820240185580e800d03080b2600300aa51914035500c0c0c0d04e052040030f82d052441c100170034647c40c00c800010040404100400900c00541c2e40d400030a00b11320070072044280c10881c407907254000e8003040041d1031980e6085c110415041c18400c4209804e0340070104031841340d2101c1008078100104200c2000218400c843d112004003d4050b02c0d10ba0100000309038080c01800c6101c000090300200044800e40d05104841000c0464860f40e034102502000c1e003140c00940708580509121008a0f0300142c0110748520201d6038903103040341d00da0700e40b80058003614403480c440c100c2e11280500b8006030603000780d58442d2101c2071800740f030310b1a241c0400280390481613030000f000c5038a098414084000364605400940c5201d01080342c079001642086800c0c07503142008040303160504034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 938542958 1250 938541708 938541713
    0x31506040b0a15080601260a021809010905070e0103021207080712020f091819020f0405041109030d0e03030403260301032105071110090b03132a0b2203 67
    0x4166120703030b00a1f0780e841030b0082410720010312848034007034501c842a035410010f49011103c0d800f40150018101d00c4a1045000c50007241301c501003130f04031804650301c43e01045040d68115501c103842000a107000c61a0822042c0720441100c80a0600000c10806001051442d44280c03110719004030201011992441d80d1400300840c1e520421a0500400c0317030000600700c100d0b2030583c4d02c0c41069402541c2d00a110305614040c025070184050401150b0705010118946e121445010014203400704050b945000c00700405242c02c007414209400c10003c10622400b5407004001d0720304481d402440101c503488032020908082c00840a1540841e0380400000244241008848100003081c1c15113104621441c00454042c4a0034801816048880194003043d06014503054104c640ca0300e0030340c0b00580c5402103140e156000756694000e00c42600207807000e10900b038018442408150f4810250100c125100300c01111040c4964031000001050b0803000c5031850505505125030f42c03080d0b041d86500c2e403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 938544208 1250 938542958 938542967
    0x10807031d0106051801081e030c060a050f090d02071206141618060f05180a030b1b18010804022205042d080a0203071a0114031506040b0a15 62
    0x144071311845500640020314400074542e0b002d81c16548004042d044866000345803000c4000031102c4003060b0700c070411a68100d000280802e5005001c1d008012036942807682004440c408058152440c1e5044980107008494001542c2c0742240c20640740c89502c0c110301c3c1460001070403042d101e51801c03036070078040190400450030a0320741403c0d01d485210424800401c0603140f890307503000340404220340701d04440320725000b00e0141040d00c01000d4084030012000740803d95581032944125441c46620040c40806072200d19141c040a0000c4521402d00c1c10450b070789004440c1c2002c48a06002840d004a0107640300c0e1500d40e105003154000d5142c0340141c20180c080142800c035020b40f2062841d5805140e0015015100505d441481c801c00041e26040c0c4ca541040350b2180360900d040d4841000f8500c00603070501d4515520041006a00c4450340c5000030741e5035064050304a040c42034001c54034011100c3c2910aa01d60042401c0d180013070940503078400305000f407419410803000980030910713000040c0d610 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 938545458 1250 938544208 938544221
    0x1e0f0806180124020708150c0d0f0615020a031709010b0603010e0a0f06142808031804020403080409090c09110310140d060f09021c11061602010807031d01 68
    0x40c180000011400b00f401c0740c41c0e40180c005d210703081d0080401c980000c0c1500c0c80d0607400c0360325101c096180001c1c0030b8844044418000105444a4480104200c21402c240020100e4101c50014055415003035400030100d52140c5080c44540201d03001296101a0940c040c02c0c09100251a0310381d00d50311640454042042200d4440000d4245150b0003042c2400b40210002c84d0052007506060064420070010800c00400e00350000126007600750089043d106009002003608201440c1e503107040001001003610001891809103004100c20800185048229400c03130311507a90002d1481c2c400e1a204c031308080c440d40f00f448441e040c000b940200540400085024401440010010302d6558803506c01111250010580c03114914038520081545504520780060042200203a072030351070750009041481c92611818110b404100d04010405114042043c200b803c03260182001d4946030030741180082c20100030f04024503e07001c205124001d403c16100c810808401041209000e03000d14024000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 938546708 1250 938545458 938545499
    0x606030c0905131e11040c050a020615010f0c0c0902070804090506040b03060a0f06080a0f12080c070f03180b0c07060e030c040b0105070c0602010c1e0f08061801 71
    0x80c1201042519203000410340240b948100f800c01c0b0413074440e0140e0202c0c01107070815514804280e422000e540d449125020039140b0781e454041c0c81c0c035400d0314003e240041c0100300300d00070104508a81c2c00c50fa0010b44410040c010780c6024051030b0443c0c0360054003204558010f442c0385001142110800c20150064015a00e40003001c00981e82e0380006c00c8180c03100c0d12144c9400d40c0105021540c1e8403c541c1010b0b002455102020070035a647d03a10303061800c15410303419982911000c4900040041021a8000a007034501e0240d01508180c1c4030b905151103403200c010310307280451060320201030141c040078004000b220085419142c1d0740342d10740590340c01190b001455003e144408a201c07802454840341491000c2c0c018000691444c0620000f0011784c2070850512005202c0c10000900c115032590241001e54004580700d100c1240152101c145c1c14a80741140036051440c00341c0c0c5a0010b10905007200e5450720440c95112a03000c201910500c0d88040500d245140000c5440e1050981c3c0100f00803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 938547958 1250 938546708 938546711
    0x2e02010903110303060d0615080a120e010801080709200304050a1101050a05071b3b0403121d010c0521060913021f030b0109050a0f050405090a0606030c09 68
    0x55003410300b603449210844440358444007007028080072610b2644060765a0141c0464607080b2a2609025868101c0403c0201d07070b20301c401140803541c2a401000e04941c68000c0c24690740a5041500240d10b8103500d01030104840d5407200090f42c00641c00f070440c080501c503810601e5403814a03007061525116801c42c00d0700e000d8610140000c007548104100c440700c0f4915a25907080c80116500c00050070484001443c4100c031004001c141d40302004a000204d00444500c0d0040d000c04099007100c41f00741d44001014100300d1410070000c01d810110b40c0503c034600101c0043c0c42c10044011105030000da1511106079071800000300c030880e42040040150101112108144021641901040100844015070480c516230080b94000c81b100c100100080c0c8028841c0324030b0100707009103071011070021040382c0004c0e0b16100f0b00301b06540c1061441015040a0b190400300c0c0c0c0c18000f40048682c41c910a1600581e620400244412400d0008417170383c03a40034800340003465a0381003240070480c0314000c0300e081c02d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 938549208 1250 938547958 938547977
    0xe040920010807020c0d0f02032e0c0311030c0a0c2f030a02060405011101060308030c0403060b0904050316080d0204090c081602070501120b12031803010b0a052e02010903 75
    0x7280001242217040d1401000302426007100c1d035454419050880c0d04036010300c81e480c440d107406440842040e1004548010300b0035000b0040d5058030030b0381d92255440c0285840c1c030300b030814075150300c07421203034011851a045565118440d00031603911201e100060581d0000c2c0a109030750340d0390307400883d07000034a03951b80c850301d910f4903010141c446842480c02903201500b0001000254000c28460024614a0000140d691b40da600c480748544e100305c1c3d400e606410001801d004001d8503200700d001c00902038a420b035061505948640e0b99102d0392000808001039058440b0400280008880c0501502c0005540722035480402070040e01c040800100403c40ca200050b21070000707074800d45882e864960080115a1a01d0015240c0c1c5200c9a80c040c0280d131100071000064032a9252450848001c20045a0b1061481805015803403101030a0b031180e4100700c82e00100c0d6440600403c00e070f81c41250f8a0b405c00d8030720001c20b101115804100e01c1c4120b54140c082e00030940660001c9400d038000d85408000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 938550458 1250 938549208 938549221
    0x3050306120c0f040c05040b0f0d231b0705011404050609160e130609150506060708040e1e13051908030a0f020904060e04020a240e0409200108 63
    0x4660300700b0086500310b810303081001c00700c0ca040d400c030011500b45401d0071860b0580f9641c50941c6940f11900d80e0b207100d5000562400c04504901c07a10b980503901d0268800d100560350603000d140040900030401c1024891030940031400711108441a0f160b11a000300140e42500d40d041128500885060b04c00e4000c540003c0d40f480d40201d66519002082c520588019040501c404140d0501600c020000d141078404000050494824040c015014941c0c0490503207158401c1343c1030b00d070000c281a020b8070040c082c0ea00040e09074810354056031241c0303008461170b41c0c681d08201c40715038803041c040828045490910485442007010440d01c00e01810590788141040c0304200d00701803140308000c0504008200042c000d051a80c40700307210141c1040054642103072400090142ca02a0300081e0101505100b0300045290a00d0101e0051214000d080e060fa150b1506440050180381d01c1d44007840b00d0464000540e6590303510140215070710840019500406481690301060005400d03404034a00c500030070344 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 938551708 1250 938550458 938550463
    0xa05010e0705120403091502061503010e0d110c06130608150d030305040c0b18091302060715060503160e070e1e0301020408300901020703110f0d0305030612 69
    0x410041500c802d498400c42c100020400ea00091041c0c0400021280221301c1c1c4160303070a651719181c066401022a410400784201d42913100d160264801d0385044008100005c01003404c0e0050001c0f07041c42e84100c04000031050414200030103095000707000041b5841c01c2005500e4200035212141c6e225901b41e920066080404000e0303d00e8594007150003422880000d02c613401c00782d48144a640384010141d44d8071552800c52b00300b001c103107a600c2b04095008045081a03540301d0741c00599408044805103050300840e0a6100740c14000d02041005803ca182c1019290440c6c00242005012201664081520300c03003c1000d40c01506000402100811000c912036407038503c412800600112060118000120340c05403414101c98055400f400005021807091001300103d040090f0b50760900b9025404895046c0882c802885a0340340c02d111600350350340d0000b4418250381d0f10441c1c17140400780d00e0000030880a0203d2100e907110300020150f104055001c80035501030356050b03a410001c030700001c00e105e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 938552958 1250 938551708 938551711
    0x109090c09051e04030201020306120c060a1b1712340c0f1103070b2b090501180c0b0c2d0f0703031d011e090506120a05010e 55
    0x24a04242000244036498965002a82000344100e84050780c0b0307031403c00300010000c110380660150350302004000141c00c2120000c114280c41c8000740c030450410a00050706405a00c0400c000c0100c2036440e100e5074404268102680c40c1c10840b4008002140e00e009001c41d03114404850411480c24081180b1000c02c0300004035501e4000091074500000f0102224048845003010080000740c4480e28041f81c01080c00c000d170355015000c0c2101c42d5034003000303040c0b030b0040303a900c041c0020303200300701c00c114884500c035481c0030184007040c1c0070340040c4190a524002d42004c120190a552070011030011056003c000f500016200d05120007550380c1c1e8481c02c14050040744070320041030b081040c56503002140c1004c0c0309540e0080c69100d07009601c1064100740742600c003000c101480e9001e40c3d014005c0c1500894401031000c030094031070011460203000207200584594101c10010841035079100c0c1d5074000d0b114403018080151410341c940440b084c5001c1c800005603985400c02e4a40350002c00c08207121240107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 938554208 1250 938552958 938552963
    0x131202030c010e1c0507080114271f0506030c04060605120c0d0c08150603060109050906130c0507020f040207170c10020d0c0f0e0108270321010909 65
    0x106007109040005440d41d0f041010030551100820b580d16050691202d54004041e025100800f07a140c1130205240c00c4944510703d0801c5291b070301c1c0812500d0f0000c46060100c0b100c2980405040303905803a0704901d41400405943e242c0410100800c44a00143c0c0c000c9204000881c101c440606a100502c0126004c6006002c00204104492a80f11512024694000118420303a80c6003d080e100b40100f164400c0700c1d03120000c1d01039000d1101e80442624100015030080320680d1641c1803140028041002c240b140038050030010300050341640e20b0a846840c210312214003400100c1810100802a80c0843e00407480b90031400800320007400d2501c01e42e201d40e81e020f0760070030844803000030503a41d6801000d2044d021b442280e240f000e03104054000b800100c40d1a0401003036640c40080b014101040e0703085003208101081c0002c000503a805038045070005402c0840c1d18203d03da4512003440351a290500140d144800203040301055007040c26214150720350048400181d0300e40e030398201a240c0400c0013 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 938555458 1250 938554208 938554213
    0x71b120602031f230a090f14010609050a0611150f010612020711090402030a0510060f0503030310030803090106030209040b270307240c170a0b0d120201060807080313120203 76
    0xc104c0e110030080c44010344040000c1c200850a03644900c0340c800e0b9180401d07200305154075484117030040a2130401c0d06025104a06080008501b0040810354481552007190100100e03e4082c408060082c005025030340b1307031228400558600303047c180090400c280b050394001508540111800f41e524425184015480f1190394045002c00d001c0041d1110302400c180c1e494012114940c0000e0801c000c1c80c44003085164001c143c45141082ca0840c1000d42d034001030003900308000304046a51039a000405503540195425265180c0e4049107005252a030030094000c2e0b00d0390b080c40280180d0314040ca2189131350303058650031203c0074606601040c4081c09640c1c0b0b190700900107500005d030b44a0181d52300144030881001c2074221030650a082d00c20703140164011491400c81001d0502a4400303e070340c040d204807418800c004405010a2180480250240030007500200d00c0c00528401e4110b0b000800011003240c00345030f29118103d4481d8025051a0080b2500c188000380ed4035018164102c0580c00401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 938556708 1250 938555458 938555489
    0x11115091507120c0e061e090d0b010905070207031e020310061215150302041d060403022407080601030507021e100e03070206071b120602031f 63
    0xa8018065801520503030351801551803080075500c208003002e00c102819900d4a55004503031800c20100c42080042c0e0f0200a190101c00903280c40758001c8460090442014030100180900004800d001d04060f00e64488a015141d009011401e0038845c10f87e41c03544020003207500d03041800d0380c1c6c9140c0c91200600c8999089810500000d82d14210010680098207860006129003c0e800490301d0a8001b040a548204803040c20300c40140070346510300b40d44072420815681c000a14107500102403000911864450140520304090648441c840c6064801111080d0601c0d00d4042d413142e500b481c00d06100703408000040003c44101c002c450080c0c203282c40d03074410b0f901c1f0040110064280200301c0c40a601c1110602d001c1c038194404c41c482444a850701a01e001c1072840210402d440f0103031440401079009001c201d0150340d0b00011a4015a4020590030041d0401da402d600c3e180000d85c1b00541c44a01301c2441d0f002e019254004601c164103070504001c02d08041440d01920000a014084001c00c4204 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 938557958 1250 938556708 938556733
    0x6050f1e090f01060f240806060c0c030706030b090c072f031615020303100b1632011a01030e1603060c0806030d051213080d060806060111 61
    0x4416040211202074860080305154038a01307481c040d6120030b807013429095042140283c0c860043c4180d0032240c00000c440746c5140d03802044050044c100301d20a4400240c1c80c05250810400504096800381c16541590307030318140680203001c1d46480310f018241180002d00d203400d916040f20700d06588100d4140c180784688030040c404545005200848240c0c0520043e40c82c0d500304544000703445901c090400081c00c00c9162061502280700220555100f1f00602089000016212044e548180801798480041c1c00c2c43c2c1c202e8103424100981001142564110051440c801f803c4030074110384012507514080c0008079080f40d010280e407801185601030b50780c880d07604c60b800c0356026251a2341120203148507001000140721099208854980e601d00035000a0350300198502d6100e0350440142045402a02002c1c00360f21440c050310300b0a040100c00a545041180170381c0041d590400c0d8030079200d00750303030300b4100080c8182d01483d0207511800780094541e6104402c40080c3d800300b0006481c8441020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 938559208 1250 938557958 938558011
    0x11e03050c07080c07061206050102340b0d06060518090c3711031b100c030b011403070903060b0a12050d090e0606040e0a2706050f 58
    0x60201060310400300168004242003030301034045100781c140a000700c1803038000c0250011f0980c058002055080c50010048c80c0c3c0c01060044c901c0c0030704054041c0c03843d60280d00360101c03100d2040c0e03180c1303400c40c02030702156040010026103a940440305040190035103c143c141c072f41d806810040455105a51101a00d500b060303180c003074014148106150500c050540c203500b21843c0c4a0207410341c662410f10038200d10141d00250080b000c100d040c000521041c16590702e03120701c951100d0640d4001c0700540560039090401212921040240c020040045500b800402815100c03d05a000401c000c10403030b2000c2525040700d00580f03080d1140c280f01441c40e40d41e00042d154164840e41c2c40001c24200040305001c00181c1150548900040e05d10108100c5002e0310200d82600900d20142e181300c10014540c80301320864059174290300c1c55240b507554010007040502340d42c11248210b82d1401418115040d100102c0041e114820207040c4041d84e01e82d2150b0042d075004071030f5032000c10a10105c126030701069 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 938560458 1250 938559208 938559211
    0x1090e15031222090c020303060d050705090f011815060f1806030506030d0e0105120a091515060e0d0611040e0c03070e0f130c121a030606011e0305 65
    0x9026580010904006000b05070410801e51a622000d8107001c0c040740044100d0308050622000100504140004025a00d01000313014501964601c040300e01480010030041c0000c1c400101950700d43e141c55880d600c40d1050030721481080344481811082c003581180038034622192061002c2103407a180c00b8048070484d51200000c3c044c80007405800d00c890192101c1d00c0302900440c1c5001c210f9040400c00d0500d40142c0441107010002c1400d5550100d0380d00c90b0468075100c0c800d103036142690302e54102c0300c0010200c0074402801d0000d03071071f00900302c81c0468121801c05413041c6000212107503501815141c03001212280740d40030052203200c0f00000e004d0f42c407a0381c054a00301c00b2142810780303c0019618500041c2d40d0b1490802c0040204000d0641c00000c0480d0b48100f9541d080e4120134100214031007040500b44500324544400c4220540c610a4414407030120a1074014001003c44048001042ea0321851050190181d200041d80550062410000300400748244810021030f4034001c5005000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 938561708 1250 938560458 938560501
    0x80d0f030b09071206090629191d0603070806010206090c01081306021204081810050306040515040c03051005030f070e130c15121803050705010b042901090e 69
    0x5440344089000050361150002402c2349820503812088094400d0405819090038404441c60800074018900c0710030891401020650411045124a0f9040f1a164400160980750442e101104018038644e0001150340120000c3e026030f10281c480002d15500c0b400134200c1e981c0031823015070120304841c00101490140c035000d847c1c01418504001b60000d0002c006070ba09407a03412001c10160340305080d182c0380d51103402040f19541004a14030f40080c0c50b90000500081c031950b914000100d000d003080103460001d5030010000c001d908000500a0020042900e5100880c4c012400c0402c89040000e046c00700300031503600030004649848140c1002d02c4008011100c0c4040e0000c41c0c0340044d203000d520b28094840a200482ca80c13400c02d500801000d12417401c4035074141402c03854402080210342400405425181c16540c400071800c10714050306840780c0300350b0494600385064103203074611085404003401c071245100b80040c1008c0115014280c1c0e005280c1d4400315000406c0201c0c84141c2010900131 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 938562958 1250 938561708 938561711
    0x9060714011103010e0108030313030333090509070b070f031403010b030906060d15090611030f04021314010e041103010903030c1103040f0306090305040f080d0f030b090712 76
    0x2803100c0660075a50040303082110030001000601c07011413502425805404520000c0d03081d0300d441e041200f4480758100001c0c0915580b0001e101500c41d0392034142c005542d5481400c09030808030140b21054900030710a60210390b1409010134000100454004103c60300c0e1060f083c2080b4650303c451701216a10ba070103c007844401001500b00b603004030040c50081101071441c2d6100c0c80d110012a0414800418481c45820000c00d071400090f48900c0c00c5480b11f06202000070518154506440207050614903a10703121004030130000b05001e44204244150310940e180f8084180c000509810340d522001c54800b030b41c40110041c44007aa80c16501c5502c6402103550a840d0a84030700032900f11450490140d001a4a480300300d0070b843d4100c00d90054244c1d114005600d041c0c40c03c0042c1c0c802c556140001400e00307450f00c4003c41803520400984002d0320f000c0c07550782d14560b52998041d03610082411200080341c400046045000c0c00391142914102024022002660b6020070403210558880c81001d00705 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 938564208 1250 938562958 938562983
    0x6060e0324042a030312180c0306020a03020f0723060103110904030e0d03020a0605060a0302030a12050403150b0a090212060906010201180506040c0f061d040f090b1008070803090607 80
    0x4120701c0d08241c00545c00707030703e850124800070040381054800c0011407002d103226080110300010300c040116000c030390700440300503200d030210351040b8081d104184001e800b0790030115a9100b0b10aa40058605291110340c41d42c20000040c00c245440b05400d01c03019005e14003121aa1185003800040b0b254400d100349000f0441009950004504075000807040d4010b07400103034060308011841c801d82c4d8209208850f144106450355001960700c10240e100108441c40c10070f4409680d501820981e409154040e6012120101041000c00148a1009200d100b481011400141101c451088a541d9501c0c1040b0000070794403441480626000900300d00e045650759032001f400750b10800220901d607489000641002e003080c1c100503003607a4254000c80d507003500001e410041c160704801c2c01d80032a0f085034551040964080c002600810960200304039072800d140007a802c1144030840b0300d10401195900303000c40b940b0399070326958810582c050900345174020004a145498400007404040303100e08801ea020 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 938565458 1250 938564208 938564273
    0x30c0203090d110310270f120c030f08060a23090c0a030e030a020606100c0c030b0106230a0c020a170d02190b0c0c0a0606060e032404 59
    0x80d0b031006415140c522442c031450145180c2840380e0b00f1128000907040c040103d115445071400325031a08600c4410040d000404100200c1d1150034003644e8000c4e061040d0300c41d500380080c10390443c00714200c3c000350505c101c004c4118010210240212400f0305800300041c280040ba9401200c40340030803010301604041e055603a910111034501c10404030804c1c680707803081440058141c852000f103100d490b404c1408100305955002840c00e512403411180788901c05811102540d14940411024041800064012081c0301e99004003034108c0b90581d6030201e0343d00003403808203c8800310351620b2424510402060158511400b440e101640c00141003040090341c0704000514280c00e500c045a0b2900309148110031503406005880344200d10310ba0000801419a079504500c103002081a41c13020004500009440d03020000300840c603511039070421106440d4400035042666605800d4402d00c280c1015107081007039403a0ba0703042405900c0c0f5030401074945644891b420b20444988001c140d110084ac00742 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 938566708 1250 938565458 938565469
    0x618040606030b01021b06121003080a17010803070b15010201023f16030c0c05010f0504120906080115030905120301050924010309080903070303050d2a030c020309 72
    0xa040d142c800181849010001a052401a40350142900c940c492102015207442c0125040ea400302e0451940c01d40e5201c5160300e07005200e80010300480004604100e22a800460f40c031100e009044090685a0b81e40404136030764824500020441c1800f10007040702c0c0780300d8003000c004207001400050304150b0801c52058800d96030700010f20148015410f8941e0820030485001c42d900031040e054580340c900480d00e11803840c001a01036042542ea09103444a00c2d2107010300540e4207a02c5402402052040c0c0689005090180d5082c4c0742422a003820101c044d005280c01d004840c169103c02c3c0300e6a00c0c0c961600f1408103690100002e054481c0c80f4400000e009000c0c0c44440303601030880300d4480d4181000d00107114002400c1aa560700600d0f8406c01c00c090803203051041c0c25003403901103001450751034a55520f01841c07500d65058851090080101038004006c0c115110303110108100d00711926100812600421501c7c1281c003012941c81c1c4101c92194118040c00b20071070040f01d1030801d02c50040f07003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 938567958 1250 938566708 938566721
    0xc0207080a06090614060a12020607080301290a02070303080c1201060513081204150c02030d020703050c0405060d15061509090f05070801050d0213110912061005061804 74
    0x1c40c0c25545003c1d1008000d0640324401124081070b0f0302c1001807400704041a0031030030902402c1d41440c801e204600456031004221400d0560103015aa100c0d44c0d5140b841042c92b03080781440401807400c0b9007140a82070358074195096415a42d00500043e803940d1400e030365001d005860151503520030041000700c00f1403481031500070b000750b82d1207a40d5580103ca00159445450f0000707130098120040c0c0aa00181c110203980c16254030301c0e540340030038607060025a010708444078001e404ac0500c0360701422442e00440d20b2001c4074041c01c255001c03905400200400c441003141c510394001d0312404a0404a822704245840c003c584080c0004e10030b80306c281c580c1c000c5d084241c42c0d400203020307940e050104600900a1083c0501440e205100d1400e103607174080d040280c1400b88a0080b0128401e485c02d55685590011708850040010003145202520145450380f042c80b00d0760161a05140c0008074000000d06036206110107010078030040e085c0f0041182a27845138400b0b8180004115420049540d0751040a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 938569208 1250 938567958 938567963
    0x504020d1404080405031506031005073605010305040203100203090f031909050d150c0201150f03060501211e12090603051b0306060d090f03050d0b0904150c0207080a 73
    0x68441707180004241c40d00a0303100d0412400340c030070030034000076840000310071440e00c10482002c542d0b03a44801045801080380c0c9030b02001c207035201c4228140ea95000581210442452520b00104c0d0f031100019420b59005580003505075100c074051070058009540550b800000300410380b84e422954040c40c602d1078112041d003071140c00d00c5000251445030400720040003490180d03400080703420582c03944400c4a0310103241001c2d040d11080942c0d84036200f0b5004008402003001560562903c0300b24460b100003079400215507072850500080b5420072540140c1350b010341030135803d1040720f016136112650018900b0403861000b00c5421400005030300d0307842500140040740d94400c0b40302e2600ca0002c082d9180904510709001d0490040c04002e00078008a0780e00c40c1e41620115558005c8440004c014901c51101520a0304000710400805a100000b030014200000c02404004460800c009810409841c000c001c0e507243c13003401100140380e410a00000f6801d0040e10a8142d17212200380c10b00172510b408 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 938570458 1250 938569208 938569223
    0xc1203171e1302030a0210090b0708130506070203101505090112030f0f0c2a0e040c0504021218150a02130815011a0c330f010504020d1404 61
    0x314000c80303412500c541c0004040c00a0b00c4081c19a0080303510790300c008402901031040014891501401145400020301c454816140e03141302509040350a904070f80000180380c901c0d2207000034146080b1041e5614680c00030090040c140c00303032401d407000701031340304040c2110b002d40b10f40024941c0c2c40514044c024000343d04406018585450003c0054591070003000c240080012220411544000200304c0c25074040307014403240c0d80480030b001d080040c0c00c54a2600b0a0740840110f20030802118040c091441079500c2032001e51900100000d9028945244948007281c80c00906442c0b105a41c02d415002482d050711124034a55808940349a412580c40310041d4000600904070a042c1541000a02a560180003400509400e50040306c07010311414540c5891050058000d04000003243c03880c101d510101c8120301600e045600002000d82600d200c041031030200b41c46410b000c00702c3d00740f09001c070041c5100b0b103a085c88204002900718241000300b5907030f04c0d82e000c1411700e40d42c10901d0286004000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 938571708 1250 938570458 938570491
    0xc0f0a0c1212052422090302010c021005090309131407030b010e041103010308030907080609060609070f090504020c030c0703080903010b10020a02130b030607030e0f07030c120317 79
    0x107402c410f0398009800000c0100344141c2e00140140e0b96070100040c0c4030100d9400d10f03039a11444101c40651080c0c2c054107a098a000803044c01c060f0150302690046d180d81e0251035007240000d4402003222400c94880f030030b94108208182c02c078a00444005c60514801c200003803507640d451316503c030010381180c0c1d00c4040303a0754800800103580c211040d4465003000b01c50500900d200b21b0031320041c1340010f00c4000e092110110105000c070409008203405003c02d181210424a4110700c01c5079642e0056400500400c07602c00030840092041c500346240d00d8480d1110f11a003407030841408000e50102841e01d00d1800280020711082c1020301c10100118080c0544c40c2d21248010101800c5885d040c08861143c185e64240d02c80e00c03030300800c220701d810703804940e800c00801040e009400a880c1e07144070355615005040821200340d426601040200340c1d40030881d80e2055825100f40e540758542d010191110b4440780c401c1080c04810040002140c0c440c1c030300605070044501c5611100d5206a80c03c1c100c0c0d03183d010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 938572958 1250 938571708 938571737
    0xc02150c070603050a09020d02040216080a0519170f0711030a08090c010c0302060c090409080a080906010f06020c190504110d050c040536180c090c0f0a0c12 69
    0xa0345800c117000007403c0181816503400941d40a81c0444000d01a03500441c0400c0f00a111300400540c0a0308603c07583d41d0b0343c07841d01c4014080da00041c84020b82c0f5424400e085031503407003210601074141640d4100b0301c0ca0381f900b075801c040003800108114100489801c9145a948080c0003805101c0d407151a5158141407a039905418500c0c20075600c0e04006c0740012060100303a0018540350407030300c1c0703141081d40c654245010801802007000c0c082d050007000207c11096903400a50329101c1c10310780090f00c5050340c84641010800b5030910943c401031f032152040b88642e150805100440048080c49040b4041d612004541a07480070780e40001a2b2031b000c544504450190b00501c0e13401858040342624060501c0002501c00180107400715400c00014040701e0f1502880366606500060b094242803645002595241c0210011421410354001c0076455102c5062800489000780746100109080c050364810f04002900045903140412183c04110000b01d01043c42c10802c9020750b0303070340c0e040c01060320 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 938574208 1250 938572958 938572961
    0xe0c030304080c150a0806060a030f060e0711010501030b0105284707080d111b0303060916091d01030c170c01050906040f150905060c07060c02150c070603 68
    0x1d02c4d070041019820000c0e65006076101c2c5205510200c1110036603140c040b012310450081919a00003040e0a103841804220800b0300b000c44ca204003e00d030380b82c1c2c540380000e02c0707003600365078081c80010007140481c8c0050003103160515a030483c3c807041c1100c0701036900340e0b0302d8000c065050703552050000100018058100c440d6021401207000342207250b482e911030080304c804802644040003d5210f803004581c0d2010881c0040c11600c003900000c43c02e1265002e00380c450003040d4007890341d00100820031240b030100400701100740c1c2e1040038005c0c10751250b0382e252130034091101c580401c40c00030052140d20104903000e83e03169102c1058030b0340300d9903c039a606500d0001002c27030190304000c801c010243c02c012620100043c00c05500c840a00c1d040b622441064046030b001d006640083c1c2402409d82c4020800300420103222512000b655110705074a80d88900340441361284460310543c0381c22050044c0100c60003100c858080500c0500303160720402030100d01e03c80e13a403c440c0c402c1390260400001007052a038503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 938575458 1250 938574208 938574229
    0x3230f071103030121060609020c0105060f040e03071103211c140406200406030f060f0e0a0203220305030907080601060f0e0f03070e09060a020f0d0e0c030304080c 72
    0x681c00294550750410742c06a2a5000070042030050144034402c0b81d0412240340c004000400c207180e001d544400f400040c0c1030107441b08841c0c06005146544c07003a00c0a280c40e00071b0104030b8000c900034601e001e1403520780044900030002065014450030b040031060103000b40d47d5105405620f0f42d51034880c0c520702d071074140001064110f81000740c14103841c00103080701022a00d0300280c2c042c10004480c1480c80f54000d201c80d02d40c120541451011800040b2136030036800500c0e0701850141d0400000391218105140ba0200d8043c41240a10000015002205031f81c01590002c058102030307404410380450110312501900c0c001c4002a4010041c014900300030003c880280a00c81c0282ca05981020030040070b074420700541400700203140032403ca5644405000344034103080a82520030064450031041201d40741540e00400c14410900000d903500e900c0d20941e0480110b810105280104002c0040d000c1c0160010703e141074040c0301851541940e0030401000100414009081e48045441c10441100300b0b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 938576708 1250 938575458 938575487
    0x9070608090109230a06050727260a0807080409152411060403020604140f0307020105180a23010509030a0f03120509011a0d0308040303230f07 63
    0x43c1444140080c095803100c4642910562250448040b14245a072405480080c06001c441c5400103105a182d408101c4503040c1c1803030070742090703803112481440d440020700e4450a00d1011b14401801031007000c50884020010805085410452590f1501510399000010442d0348002c0014200031402d00d60186034050901c1c6039100504514008800b003140e14003284941300001c60098003400640135103035001c4c41da2405003c136095031030f103440c01a590740019101a225040800b10304011850000f503414800c1d505500918140811940155510b402c20b1040801d040c1508000320004e03106c13440400001c214a40007400261003008e841c2011080802c40c80e030401c8010420410640c800103010345209502c40c0181080910a081c100d80141c01d4651004a460605040c403045050541240a8004242e0380d000b90503400182080883c501420004001c258130b000050302090080d84101048800740007207400b0f1000d51108224145822260181e5140c0d0380014402000c7e8000f009130f55418 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 938577958 1250 938576708 938576711
    0x703150902090915030709020403151b09050915031b010905031902100e0d0305090f010c0302151008012d052505070602070f140105150613030209090706080901 70
    0x10b240804070b0704940c0c0040100100caa40c2d60021916a10100007403001800e180c0d0086464546030b10b40351010258074031114401e5820900412001c44258144501c030301580e440d10f02e405850700080c08020a40209680913903001c038070300160652011b0000a4000b40c2401100c1c4020303003c00b001500c001441d030841400781d4804024040d82c46018150403c105404845000603200c80c410200c540c85141c106d21500b21070807a19100c1010380140240400c41422202d281191004100440c0e02458400c03020300103a0150343d10042c50318401c1d1103d81c1021206000d00c89481e200c0b4921405c3d59401d0004c01c569606c0755500341e80d0b10b44905200c1d80f011010000c00e0000d070a1460b4040040b42c0f00c0c50303c140c4100d05103640ea10f1014018400c0710140b40c4d10030402d544494080c2000e090010f0000000d842c4032414180c6d16102800c18811144191881240000e481074018244506500291090510286402d10110141e5100c00714075100f2481c2e100240701d000d0410303d000b40480350103401d4031083d0f07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 938579208 1250 938577958 938577967
    0x22a0102011a0d02060706110a080f1302060304320708010b1903080a05092106061f0309081303050f070f030f030e0112050103060204060f08060906060a09030501050703150902 77
    0x35074881e0340c05800f46070101c81031a1504014201a0010009495841500b200c001101c4140310b4028030914487c50014115512a582d061050200b9102101000b54429801c000040007e64100208000960070302d04c100c1014100c0c920000740e154a903844841e690340201410080f0200074040c58031707d004140c5c4c0c28a102040091960501416400001c00032000440c080312100d202d2415507458040081030000c2c0c140c542e120360351420340740d417003290120b002e4040000da142c182011584400e00280d20207840c0c40000000460042905420031280080c01b0042982000000401c0101545c090f401803e20004c401c040d03249030510603400004099818a020008145111400c2030440d4041c1031480381c3c110043c004a07640c1c5d44030840c101e6400c4c6400004424000264081d001f40d80ca0394403070326018a4046015550280211002139000003080c00084460900d84040c0c014800c2506205e000c0c171303032280d4960307080d11000c85061780041d68401509411a00c3c040c80000103281c840e03800c42c41e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 938580458 1250 938579208 938579261
    0x120f15010e0603280f060e06030a0c0510090e09010506030106050a0f15090b0a0905090a29150304031107052704050304090c0e15030105030a030e01022a010201 70
    0xf800000c00e030958814584185201c400068039241c403004011840820400d0002d41c208401070a4a000d44100c2150f0100060400d060005021907d580c0040080d101c00d440c0a04001c0840c00319104803003008524000002c00245664009008070301c0c0703500203c0c85113860700505003103442c142d010750b100d0b02d03400b001081008802c0c150382d8180e8100b400901424526400180d948100742d510010000c240012040d036420f0303101051405540040700c00f1292911843d41d80741c10751300c0c2200803142001c0e40c10840e00d0315030856008502c0c0ca280142c44802d50a011100c1407816400484040d004600c0600c150310040405208260160070100ea013900e0034014401b00c04084170a226036001035180340404902444410415a03008007408030303042c08641400c0d24010540d803100e1071a903010b1044003083d01c0c080c40b00d410989041e150098018550400315482c01c541103221202d00c07505600410401b40e4008450003281010704149600101e80515403400090842e036214403c40344042c040e0302c1c602c68 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 938581708 1250 938580458 938580469
    0x41d09071503020c0118062f2d0705070e01062609071a0903010608012711150a0e0906030c01200d0c14060c03041502120f15010e 57
    0x3039001c03036140050719541a40001e03401454000590351108061100e06402c0003504c1e000500c0301401561201c01107149a1a10580f0046248010b42141c405005190703c801005099a000b40d0b0700146500e043d410842c82039a4961000700c080e0b0f03050700301c940b06016032100c40340002d0041c005413400d659443c140020868003008078075044ea1302d081c482404181d81a104201c0e10001d0402540020501060f80e5564821a400fa1800794044d508000c1d000603848010b1243c10707400d0310030f03035200140c1c1240244800219160700c181241c8103130000a0480407038545e240e690b0030f03e80a41c09110741c2c803066240d000d032030301d80120b07526403290b09440700300500e03034802003101120590282804041180c10308694a4551040d0a85040500c01d1031444000103501c19001004e00e4040c009040b400d007080d4090315190801110b50000f04130081002c01c0c001021003280c4840647c403601d0050410650150042c6103a0040d1185020141036200b4403900602c3c504521245070000d0030542a500030f076901203503 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 938582958 1250 938581708 938581739
    0x19020d091205031b0106150825110706080f0a151502030c0102210123060f191d0414040b040606170a05120406020a060c090902041d0907 60
    0x60301440384602078410000108143c0344221884804d44c0702200060004a0081c241c51203800100204400001000703030040c5040c90081443c00040700c03426610341d040700c6050441c500c00c0030401032242c3c1d40c400d46a006100c1080904480d55840702c940c00c203ea44002c0e541000303850a0401c900e40080d1804502c106004502254503200c29030001d010105816421b501401c031300e03028254000510790309902c034044a01400e034a160008425142d0300c032000d007011407001207110103030941501072043c0c280c40d00308060312805400e03c80703082c03505501c1e1b4a40700140d40030140f42804941c6501504001c051601c008180851050b1820040d8183c41c40110ba145030300500b019200713070000408101031050503081700e0040c01c69443d4103d55824248041c03503880c0340c400f505070b1381801904a03a20240b80c182d01240c0c1100d5440d03000300000d241c07a840300d80044c10450303034140a11180a000086480403070002d0401050550f03041440200c10207002c100e82003001b041c40c0c0b01600306040501038280c4406180 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 938584208 1250 938582958 938582969
    0x304050a0803190b0402210603012403020a0b0307201c0f0807030e0a020906040e030f0a1107050d021c0c0b07020a09051006080a091e151509020a02011503030519020d09 74
    0x142140e443e1980482d00414111001c0105000c0100c4100061407102c00382f030048900c02d44048640540c0c0d884481c0813804151070840c00a0300d1462104401c4030b20250341441385240d070080d660000001d541405104031507011b40c0011a5410020140c542d4029070715551080490074188403401f07803142c1d400c0d01e605107010020700c00d00e0f0540200b40583c07565404451005990700483e0307910b041002d84e03440160003001c00040042c808940500a921005c0b40c1c0c00210780f00a0040125070f03000c2e1303007082001d00810485c0b02c043c2010000013404212144002d80c001c00225500642e41d841c0c90040c400501c3c81504148021420101070019251a045100c0115401441c04c803d03e62a03503690440500b003410005071028801d501c5584034680c0102600f50058810f640914180501d500c015050310182400721040c40d061000030855001243c0050031391070b07103520000895048030368140d02107840300e4100350009000400d070ba0303186204207404440810250300081013040c00110740200390310818000c6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 938585458 1250 938584208 938584267
    0x10b0a05011e20060f13050a17070605041110090803031317030405010c0306140f091e010e04050d140715090b0a09021009030213020304050a0803190b0402 68
    0x2e1214040c42030302440a01c0c02d00c008454042c445100c5010368808043d50401603030f8200c0404101010410b440c4c0401d51640320015120402c01038030754104181c06042000107100c810050360001427800d114091042e03208810ba000b80c44041c0d001c3c07000b081801c0000d007040c0080e40406100894002091b01d82c072140800341c0c0c40c6c1c641c0c0e851a04c1d019554081108000d410f0b07000c01803104004042d000240e04000580c1c0800074940d40b410394800b00d000202c510758001131850361100050800c0103050b170740821068100e10825181c01359540038080d0903442580c00301707020014002040818461a01c01404c103242c182c24450202c8001c031141d21807150004e04c11811052854050040c5401a51000d90042003581c06850681803c5001e0011568124402e1a0703c00c45200c8030383c011020b40c01901e8000c1c2c030354032203296110881030007540040c0041d01d00d4807130481808000b8480301e0003907102e00b001080e001c0c0005003245080381541c89a0904c07a100b54014044070b601c04034074001c800036a0032400c00307 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 938586708 1250 938585458 938585507
    0xc03031201030212070b0d0507080a18231218030a030212071b0b070611030c0406051308030a0f1e140711040609060e0a0b090f190c08040203010b0a0501 67
    0x240391402561b43d00000955030049520522080a80c6c002c91185019884a100503a0380c1300c140d500322000c160710040e034084480c0b041804250000d07003101024604900e90046c1e0465000c82d245020036210b4000c1240000280c0e103c8100c4414000000448003a030080c1140501c40c0c0d40652a85650603584408650100d0402d007800f113040304d908013800c1040d0b4480c0c0002e40395a03100c0c181d40e2040e0000d941d0181400344005068120b901220301c20a029441d150510341000c01c100e400c0d6200181d0328040b1000c038900815840414401044040c08035200d40d00201c0c108500a04960b42640c42402c8400300044001451a04200034101e1309001c50180740e83e0310814505541c10070508404c80c1d40044c5850800300f51100c4551284054801c1c000100f10302d076880070241002d03204002c0e04140c00003005404079082a940720007042d008071450540b12005114903141004a030035071a800f00c00161100c00740700540c1400e2040c90000d540c1914040c0c0d401e414200040c2c5048440b850903903031628402c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 938587958 1250 938586708 938586739
    0x30c330e0915011b080a140f0415091203050711130507020601090609061815080109110f0f03062d04050a0b010611070306020a2f0c030312010302 64
    0x8403002810500074009045401d0400c1120b4285200e885418081003522102e03140c680514403200700002d501118040c1380c5816681c044410b604500e115410005050000c1110407009034050809026102c200f0712540c410a403000b084aa01c583c440340180c50b44581000110b6402803ca9042c5a0040c8202c000300100c0804212011100e4555040a500d404244842c41c0e81c081030441c100d0304c2881042c82442d0b112544501107400a108400d820b4a411070040008403403508440a807800a001035504030340e071150454207403400710303408840c0d00d0711580c0c9500207441c20040180c0c40c0030b0107031900f010560f8100003080d510315000e0a6281d20314030003005020304140b51510408260280c0e400c0b0062410b081c0341c11030b80d075016008221855000720002003003481c0705d416030550861f40701c001058202d2441d100c501c02917114180e80c41c20007894035860b20320710142070941c2f0350040030010700540d5132070103007240c41c1010580002d003032003900704119100c54006896121819030b40c049038030040000340c04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 938589208 1250 938587958 938587967
    0x90c060e55210209040f11030f0703020f0103110406050301240c14030c070612050a05040519110907020322141207030b090a0c0b03011a030a0b0402040f030c33 70
    0x5580250300a44510070002003203403c40340c4601c010301c40d4441c0310001c10020708049d2641d00c10145180d083e40042000c101629104c035001815035818180045d000c8080400040d1541c065003111003c100c000004024004074030341040c0082e83c000745030505220b140d41f802400010182b5010b4100b032000c072600100448144115503080066604a544090b03582d034028243d003920500d00d5641920b400002245803985006a5200c2c07035108001c0c3c403000c072014555054951003403405440f0343d10300c03070846a21500c0d0072405070b02600c0719030011a25003480000380d803031018012503039034080c0e4450036040088002070320350440c1921040b42d100c0c1200d903a04039032620341015a80040c00d00c40c20700301841400c08020a031045401d004a9214000380d0311810688400c2c4001e1040d0405040b010864441c82000c0d04055600444101004514400202c0008069800035040b210300c01030072150410411046a0b071031030013010385420841440c8010121056181e0450300500072070032100c0c1006c0c1c00340d0321a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 938590458 1250 938589208 938589269
    0x50d03060e0a0914030a03090201032f0a032003271f0209030102070803090d0203030402030a030f0c0b0108010608010b0301060302100e030304031401050a0609090c060e55 75
    0x581080361b031201c8512800a015244046050b1b01191a140311860000f0f040f0364440300c0c1946005420b84000300080c400e0b20b540e4014100241007507628800c0709182c0710740b41200c8115000d032005054890a00096001d00c00c0480014400c450044520180000c80d02103901c0c0f04d0518400d41c000505ca0f400c0c4c8490b4003900c0381c944401e038154400141401044a0b000196016141c500304032a484e00c0c10604c01d0366244010303600a581340c2d00c03001e24100001c6c801c0802404c400464540010f000a00b9075aa8404c1e10081c0c01112841c0d440f12820300043e0400d10501c013445504070024442c031451500805d50425505640c0d104100c00051580e0b201c0c0c5040007120029540124a0041070442c0341c9038034020a02a200c4a040c00d04110300010007583c54052500c0c8a5045002a15101d1030f03e941134400000800160b41c00c06061113191203209001c015441c401d058881407003200c0716400030003180c1041b1a407550501d8204050504a442d940c339078a500130f89041e00703c00f501220702c62610802e034100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 938591708 1250 938590458 938590493
    0x1030f020c0a030e3102070b070c02030d020c06091e1903030e09040b18010e150f0702071d090a080d020a03052220040204060903050d03060e0a09 64
    0x5040d02160400a07410703406a010360f581c007142c0100c060411060303941019401c401c0b02d100025089401c0403100e802078000400341703c0180340440a0341d50f08070344202101c00c400400c1045065500b5404c0a0209100603500d41c80601582c44450000922038024520100e0241c2c0c40343d6040340f14194015085d00d9600ca000b45860149003100100b00701c5410035001c100c1c00200300304030329246400d00c0704c000c03070149030b02402e0340d4190390303038100b400e80300001e00410302c83c0395900e80300c1c01054043d01f0700421401e0b52809070700c04000e240502e000c55500740c1c040c3c07915003158007912041080a6885e0b52507440204040e404040325207a00e05820b14086108101903c029400102c10140038800c1d030080c1380326103071342e10709019580d24186840000c0c6886141c0a1075541e480c3c03291700000300080f040d50b026000c14100d006c060284840840c049800541181010800044062007406020002907190002916090240c3d034200101046e4407034001c0e2091804940f19950b031030800c00c4d1211400c41c20213 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 938592958 1250 938591708 938591711
    0x30a0c03110f150118020a080105040218091009060b040506090634260d090503120405010209150307020a02090705070b0403031d0a08180a0905070806041b080f0601030f 74
    0x10000030000c2d4203c00070301c50b84480102103400d05030030000c503000b03864a000d155200c041c0c490f03203401c0c04d2202a41c01244041410420ba102c0a412a6a0b1712080c502845000d00401001170a100ca0481150040d800205159005110410444c0d41d520115000260240c90850b03c4084226070140180c040c181b0880035503088400480c007400c010098014614001c1c24044e8001c075201c1a9050f00d102c0d001142d2100d000201701c9143d111a1541044800b68820300c210ba1604c0d2078545400c9002c441501e007120965000a160b1001d407421550354007c61030035840d101d10394140341e040030703644020380f000080c0219404800a032105004070182c504041d08002c180419142c545001401015451803075070245542c14110000b650300003907000c058076030110f502c1c0e10b8135641e588007101e00e040d148500341d80240e0724007012603454214000d042c00f0b5405615240070505080c070070002540c81c280d0309001c0070002c0c00c90709801c5650201c86580c01c031290b0f101801c402d0300c07a0401200030f0810324240c3c00c0c829 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 938594208 1250 938592958 938592973
    0x918020603060f0604092a0314040b150d0606030b0106140d0b010306080115060206010f03020102100509190803100b1903090302010b060a080f100605030106050c0c151b030a0c03110f 80
    0xa6018100d40e61441f412510b48204042225064046910401110a40280c044001000100e00c0d1035070341d4000303500e001c4407005134500400040d180121038408507640d90716a0010410081004103060140040342803800407100f030180350030654002e00030090030040d12032140c9003241e4000c4d80000f01520506c40240300d10110046000030207480d900c544001441307030f000001207800511141c070083e41d0f8140e01502e4030100d040a0703400a080042e209100341e0082280079840c141c504c280580e0f80b80d104820031178503803805030204201003c003a803000001c00d6042101316002c19403140b040414001d9030400141040c1142001c80c01424001c4640b50008030001d0303c011001d80010140d07100f00c11450000440e80e444401c1e040c070010040c400d0b90007245040c0014400540a480a0714684404000322140c04000ea00001c10038a46864503080b5400c0024040c03806419003584403402c0e0a0101c000c5140003c5081700a183d030180f03050260420649001c44522001c043c001d031802d68141404a5900 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 938595458 1250 938594208 938594231
    0x3260610180f090b0f060405060d02090a21050705011d061c05010b071502160f11030319081f0b070204020f04240807082205060702070918020603060f060409 69
    0x4003841c0c0c44003480351705098501c120300d00d4060205e8059442c003030300907810000f0110146010390004080240c0c040070b4000e0114052044106010402c00d075070045407010402d0b414141d0034003000d900018100201910b085181090320841054800415610150b4420821a162812205414103d40458100000002c2e40d1030664013404e00359018100d0382c804480c1050340a002c900c81c0c984420150703208130001c2c9000c60f45c012401102c0720302400c1003d0303680a5460009040d80c0c03042414240030f4034000c41841c400390380014001e51180015240c1c000540729a0003411440d003c6115088110400046101c11901d56406032142c0c49040003003540c98136107c0c00c1c0e14903509400381d01584030050414440d0845441846041d0084d0402e03110a5030a4442da207803a00040200040541d628422455110010700c00f0800c05100c0c044640c0a041c409040030780550070781c1c00c0746200500b0580d070841088003603030341c94046070341180341116054481c405075401304000b4095584905081ca00d458000d121 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 938596708 1250 938595458 938595461
    0x220510050a05130b0c1002031e07051c1406010c05060c030a09080d020c0d05190806040e0d0207140a06170702150103050105060405060d050d270303260610180f09 71
    0x403010100c4051b25180807280045208a0104851241c003040d4080c0d202d0100f4102c4180058104401c2d2038420f2070401561441050030107000084010240c0e01d42e5070008031110a18100d80000d4240703000e410004a42c0c50b015551400038140c0c0c0740700c100000c0807800c80f4155920000400e54005031441c2c031980b4000703c2c01d00a40000c00004a640109102001c40368410f1003207402244602c0074071039801c50f0100c07003212400802800190003558403400c24480c0790041085100214442c2c0c0103207881d0f0300381411280507141460415002d15110a002e11040b5088980003000703a112804100081e07844800032894882d20b040220407504654001105000b4190400e9200d10015113090240d5210320050045142800c80050f0440e080345902c01202440350014903615501001c0c00944001c1048a20402c650668402c0700800c0c00244d41903504060701c5c0c4100018070103030842d100103160000100345000c1950710520304000040f502110000e0114480c2805420846865208103854100050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 938597958 1250 938596708 938596717
    0x110f03030109050108010e070315110d0905013b0c090916140d120903060204060c1b03050c060f043b0123030f01090602220510050a05130b 61
    0x603041d00f04070020444800501804007000320002c0107040c4589103844040301c2400e4101840c0303441d0746400610000c01402406001e0a40484400003603021603440c02ca4219242040304c510342c25020001550300c0c5014400c4074001c004c3d00741410350347c1088442c4007070a10321441000d6900c104070006011440600282c140e01e20450020b107c412107071603040715803100d113640c0d8000b41c0c006101941d000005001d03241502201d00700d82050714180d505d0783e840d9401d030b03002a042603000070668000c607002d10003080204083c800703115516181c1107095484440d143c03810355900600441d400208002c8034505902120700900f11119a141102078103400074a401c0101c07012816403c100c6600448200c4c41002c01b10f040301d0302c0c00c03450540c3c4808000b020b00d079030b0601010103901d40155001d00c8080182030145506c0c80384144401a5a03d0f140c2c50b1000360250400202d80317008111100030700c80b94650300f014250780ba0040c28004d40b55000c01408541e03900ca18038030140280910103001518044500250 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 938599208 1250 938597958 938597969
    0xa1a040c090e0c030c0f0c101113051801090518030a090510030e0c1302070b04080403060e0307081e070515010302121203150a050603360d030b01110f030301 69
    0x9200c545405504861038002650b100d003450500708140c1d03010b8400c080090400c2c0c0400000c1c0c41003860712450860407500380d0010460100b0b0300151000d55400290304ac4c2e4050803044032081000450800f5a400051050050b1000c1ca9685e10100f00031500c2c0340d2422100c0c03c82002200c0e500e1030a0000109000aa0700c5000c0c0601c0c1c1042110410500030b014140e22000e48070020506a4003c40c1001a0444241d10301185182c3c2040500b01141c1c046910b90f00c40c5000f60b2996070341d1461440c01d981140c0c500c0070a01d0082d00280510b10019811104654208400281001c000c1c2c20402c0858024824200000d00c10f10941040c004000c807182d180f03d040701d0085698034440f80c110304c040d0ba01c0340150481700320036140c200001000413907113400c44031010340081c00040c5180e84803404112194015101e403184a000d012148452111000681c4035000340040d0f04440c50200e42c8045a88001c10074100c010b0644640202c881d5034807610420f09030516079001c688082d00c02c0441a5201c2c3d2013070103034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 938600458 1250 938599208 938599229
    0x6041203121406190504020403060b03251203120f3905130905091015030b06040f0e0d03090b0f01050109050108040327091407080a1a040c09 62
    0x7084109034074803030b089146a00c10010002c0355242400c001d28068003000c0b420324034002d80c02c040f495807a1071000e00041d41c40341400058030a2940101340c0b404128203009204880000d08000e615061a400c807411549036220060111307860303141c141c50032014000100c038100d191107034411105460b50444104541020f001c101c18040c044120780035010200c05200b00c50201c0c0c428111060711980052a603000940c0e001c07080540c0b103d103800142d03681034a0f6103200d40e01c06401e1000c1c100d091b1042c180e0403d58031380c15000c86861130340c1e01d01d034041d00100344900c01e41e0340d44918804020290002004880c48030203551760680c1003100600201406141990b2400044001440080111480c903050b1341051f1074008610345054011115580001d100301c00308a001e4100350942c0c2e100f0300050290904240c05030080b9400c000b0803c1c22202d012400c9200451010306100030550001081500590504c01c04a18003025102c02e500400c19503800f6038105103480b0700c000d00658003001362815110140c0740c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 938601708 1250 938600458 938600477
    0xa02031006090f06140f2d01020d02010227011206081e0303061c081306170c130302010e0d1a150a03080a030f0e0a060f1815180206041203 61
    0x40340710444443c0e0040100081c1d017404400b0051403c000c0b0004806002000107400d6052400c40081a1400d105500c0003105218481400b40d0380500441c5071880341071000f1810030410b00c042013014194001000c401e0391454030904426445100c2c440052098140f05214041c6d4030609107640d032241d4520380b003007020f4007501e0030304003940441228001d2400a01811400000d84400e00000162100845240301c1c1000b190a16a0740c611030103000b0179950b01c40111280a44400c0440301d07000626000315603c04012240560404030610015a90203185c02c145d940f207841c020400400b8440c50103010352081c0b180785103180000c82c0005104600f003003ea2008220890107100742c180d00c6010080204405100c1020364a110340d2040004550384a0081451080c1007200360501901c04820b503103080d26801d8103c1100e015009503110001c81c0c020040d41116503440b030840c10256082418501078071841c590004a800101900b80150010300207070f07850350b0b40c100c0b03904002040907040340072504120 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 938602958 1250 938601708 938601731
    0x6030204061202030601090302031c02010f050403080f040c0f0e04020307080a02030303010e100b190e100504170c040c0c0308070201021e1b0313060314010b040312020a0203100609 79
    0x94400315050368a070b0b504030018580821000e03410080c800b5040005102001000d42e81c20440e562100c0e000d040c0008100d803107a2802401d56681c04440c0780918103260904c0002680130000c00c2e8419400d2108075540d85442c42c0c1010152000c1d8081d08461040e07041c045450a001c2940c140114401c030103c64000350345904203511100b404601943c1500280010000c4400c29285507500c203600003141000300362922503208a0b038100e074001284c1944150000c40884d600700100030700e40d0310102c51283c407a6006d454000e11521590081150381c0c0c041c04103c02941c0b40070000e048035000000c006101d1001c00380300c01400c0003000c0200385d000070010000b107800d007030040c4202c50356000d5088489001c8601c0c20b03190032403075120260381124041c007141106c00c0c40c40140040e040d10841c01070100751803450310000500751a9060f1000700101200001004400100000c84084030707400300c4d401401d100b8a00050741490b0f18644040d400d0b0040e0700542d040700444d607000c8070039501c00401c10060844603e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 938604208 1250 938602958 938602961
    0x20705030a0b010b031b030c1b0601181a0409030c2307171006030b0a1103060f0d0f1403030a0f0209030a0b1b0c060f130f03140d02031e010603 63
    0x3598090442100003005001072150a801035074060b904030201040306d148101c1541055008861000b10030f20082580c2c950b130000340b000c0c1111400c03101e00401241d41000080030030210b00200b030b804807685d25400340da001c13104013001030060f54000308104015042800c010317185818444086941d651400440303420030200060440782c460b5240000d1620710b040c60708083c00981042040c1c0c2440c03143c17564440000d003d5005601c061441441d040c9001d040001b010400d89a402d903400d101004180108841c54545000404902038101c1d9503003841e480c039080075105450f0010303015062803c1b40001e403c180c82c000005601661005408104040754481303040104d015002d10b20398150800011480840c1819046503080743d00710011030300e080c2c0c214102e030304139500050014100e90045000c110b040c0300c40d480c081c0c0e0301c14100780141011402640d5650100c031184100107052000b05400e14180d150100e099030030000c01c25130219543d00b0b00713540268403c4c140c2000380700385844000c008508070740300303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 938605458 1250 938604208 938604223
    0x60102060114011803050105130c12050a021c080c03071b030b0406050a020d1e05010501021f0218120a020406080309061b0a170301060f1b060c140a02070602070503 72
    0x40241c2c0c00c0790708240d0044030305401d1034400c000110300445001c000300b0742c207116050180301204141d503a10081403920180039040c1740c2c41600a4010304144101084c1d011844d9400c003a8115444d0100c2140003040c01c0c42c8003211440981201004200000140303070000c01406220701528508100d04000c1c40f0f041290080ca0100401880101010800044998100c0e64120104c0388026060520340101501240c10840d03a00f112107100d206002c020540920426000d0202803010703007107899041e040d00c414508054a020800b507400a010760409452808011a0001c01031108000811002d15036540340003450051340320350300c1c1010000300000c002085821020380584041d040c40b4a041403018088040b44001845001c1d120701e0b03400003180603804800c03094550250782d85030750400000405101100c1103070818070004409804103505944c0350f1044c055030000f00403514010050040b9040e054444551000c1c581c04a401c48034280c0100d000c0c42910031300e50848100990790802c00d540c031000b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 938606708 1250 938605458 938605469
    0x61503010c120b03103306021c1704060e15160e0102070b0a030c110a083c0405040f140f040c0e09060109050a0209150d0e0a05010203040b0601020601 66
    0x22480b14081c0503486412802da2214000c042e1800084107450590980c4e4120324441c603441c1000600102012400c1c1c0340c0d007004928010000304c201e081440180d03031a040700d03d03d001180c000984c8421103d216036101c1040402c49911122503092a1034603001612010700e40f02e086000300307040780d82c1c60b01c00e605d03c3c0c912460340d101c41d0510f074034655030040d103902951040050447c0140c101c04600f0303048010082c90480e1031507070b00150b0300005030401041c800a013016080d558100004600200d03a40c5400c6d908002003684004c070b80202c84082140240d5000303184180344600c10b129203800d105040c80a80704441c0142c406000b9881c101419004030351f000d0300c0c90146054810b01281c1601c0458400c280d10602c24031401c1899a203c0c11000811102200c1c020b03402d034001001488031020602801d9000781001c2c00650800444d40d00207011041c800c4008181a4004196207001c08401d070000350000064000344d40c009101070030594041c1d80111010b6514924040206842e540300060303980c126038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 938607958 1250 938606708 938606717
    0x20c0f060904110301080a060c08011a0f0909090f0c0315010e0402010c02130501060201061a0304110a090c0c1a13080906210906010504020a0e0613080f061503010c 72
    0x29208040100507044049a541c1003503541a2026480d04034a00441c086d059003c0145550350f000e184c03004c15601c4030414001004505401001107240751a01071410001c880c0a20f6280c0c2d0003100b5001490052000803640078081c0400d02508450208003500090b080000351500700080380180b43d45c4401c0a44c0c64815068508010070850620318070441c0c0151051402c4406000306070001042c1c512107401d01044c1d5079076003004002e04ea4091042000900310b2080c0002c1160043c00070004034040280007501c40585044009c04503903440d68610041c120b111000c210842626200500000c01c40508840a400038401c41c844001c000001c24401c80c1031741445a00309486540e041e1240c0c2020300000d403c0b500910070444014180410300c1c0019818080381041ca1405040c0c683c600b04041c0c0c0710a014610421000c0c11050f840702128000d1706050740d015035610b400d80b040400340c0c03030560b2242507507004040503000e01400c04140c150050984030034208080140c1c1c0209030803101c51600315408107 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 938609208 1250 938607958 938607979
    0x70f020c0f040902030304080642040c0e090a02070303140c3f0406050a0b0913030203040e10050a1403060a0c03090222140907030320012a020c 63
    0x91034683c0001c12081d00c0541680d0800c0c0c0e031650741a180941c1950300f070355103200c8501803407540d1140d032002c410b030121100c1c104c0c1502c23002b010303113020519070301c10402d4015600c5002c1c002020380203500c0404c07030b1903024203940c0c0035292209501000f50086041100003a040c9152240a1140c9000e124054400c07410007615100d48500d404200002c290341c2d00004104591120440d00c44251040c02820701c44041c04841d45010b14090040303450003060340511b9460000007426075183c1d06c4002c0e034040e035180c95407801001182030680ca0f50169a220861751080d0350100503a104040b9104001c0319000c1c4d583c09841615401044d81d45022142119010351103a03000503071088290700300c1d011000302410300085a02c0a034000c250007400c0503041c43c4948603212071000c41e111007072041082c8544904080170441c1020701010b0382343d011610014040004244016180000c102c10301130b21000307860000c0029034961804007401030300008002050454128951008900100301c0003c0c4035001081c0c40c8a9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 938610458 1250 938609208 938609239
    0x1b0109151e0603030215060405240301020906030a1b08040807031209150516052a010b21100e15040c09060e04020f0a0b04060c030309020901030308070f020c 69
    0x1000c0e58075070700118000000c10910076030582c0c4101000345020fa0b018140883c0800162400c054001d8590b0340118500010445645040103091440240d0743c80e00d00b640003002000207019009090b500d2380d0024000043c40319000395640400400c501349060386006044c0a24290b90350082101c01400601c0108801000a449101400c644030442c11002610900d1900e5a88800510740d050a500694031424021980d42d850110107004075203291591410141c4405108071400b01110118040d00c0400050b003d80c0081d00680039899001e05044130080b15042908100c0701550320b1300969001e514039a9080350054020710601918201c02003449102e10f074405001c500c0020700c10760300308881e004c0200d00d1002900130300c030003080107501402c180d0805004015801141c40001c512920880804004585510040d1030841d03104c1d0070216182500c0f0b0034182c005e0203c02d032000b90f0007051000040300301134100c000b40e07000704290341c4c1e00403541155003000c0e030707aa220f078160040c1e005604002c1d2284 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 938611708 1250 938610458 938610461
    0x60d0b040305090a2408060f15071e05030310060503060108070f1e05040503120403120807090f0605041401020f210712020c100207061d0f0904081b010915 68
    0x45030101800d0399842c1175654510494098105c440d40382441e459404100f6202d9000c503005411a00403642d440c11416440d0020708030900120000c480914049408414880d80c003c00a01c0d4042c811000003103402c6619144d5180d5104581c050071245102c107003c940c8621900a9034031072a0181c40701091601c600c10266031084a1a000d4020441c2040700b2300e0b02c41c0820f80c0011003141c010b841310790b143d80c1003100300b40c04c03d112000802c108140620040012805a0b941c0c9040e0001d1802d013144582c0710302070304458105154002c3c1a80720250a00016250351000007402107405814507038007003048040c01242c960030400030b0360000758801c0800d0740a2840e10600f04020010b40701c6414640304480c0d40340703000e036120b82c98000c02582001d01c10000a050820300026183d81030b00c041d1240f281044400303001981903032800c803a0b00711711784141074550702e40700e10802c1c508200400207802490140780c600742a610042c00d0803c4515130640d200f500c4041401503d1143c0c5e8440c03c2022260090f0a4480 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 938612958 1250 938611708 938611717
    0x604090e0f0115140603060306040303410114030c22050108151015180b03040b100902160f0501021e040e07080105030d0f0302090307120b060d0b040305 67
    0xc03240c0100400040c0c007000920032118603050151980504614002c10542c0c82000700c03a00ca4003400081003000820fa4012402c0b0307500c154141800134040900000c05003442c05070403040007480818035000c0418159090f0031240100d005550070880380c2e22620b0400702c20104408894050380020700d80c260520740220025241c0d0000c045980040403c01c010030140c0c0da01381d02000281c1c204002c0484914040001c1ca54400b075181a1a1207903490011260f5100c2403220b44001003010a031070301e1174403003141c2411600800d21480e00070340b42c1c00c06051040d5102410740d441c2e0902510a1400150722100307000b40c507001d1405521060010b541a12040880440194101c845540c00c216405000c110020b804100c1c1b038202e24115101e030300340700711101502806002d00042c0500c0800400c9aa5400100c040854400e80717045e10348044200c10650103030165102032545406200c00100306000c6150499550b02d0090340784500c00e4a9000500020088091004e03240e5072101c03000030042400b074002032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 938614208 1250 938612958 938612981
    0x41704030f110316030c090b0103110d05061503010b0a1e020d080402041409030c013c291314070c1e0609140c0102071208041707030215040302060409 66
    0x2c651400c3c0ca04c1401d82d034409260811030b040a070254041c0580c100521401d02041020b00302080900007105000320940210316604c0b0395280c4440c000750f002e44540d621100f1201139030704010745030750310361036072115940040b0720900c0000d20718488242d201c074603008816158a03150700a0284541084800c60b0b00000042069030440e80f2909403100400c40e48040f5071040381300304003468981c20482c0c0e9140c2900c1003c404407029036940311401c4041d25120f01c0c02000452044c900400550246e005034010342100d10070541e001005c012418070015413144140c00076202245d9131030050304d030021454112414803181c04800c07058080010341e40c03405103481c1c0c5002400b504510342001400003409003100d140110803510103443d14588410490210741180000c0320000103000070a4003c00001d6807100540301c2c0f400205c0c03032612901e041c007881d801194003130320340c50500f114030350900240c4655680440c40201d000b5100486807a02004107031050340c0940b94002d10709480c2c2803500c64641d000e8000003091 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 938615458 1250 938614208 938614213
    0x40e092b02030f0706050714030f0c0306011110051006180501030209032107140a03080a050601052a0f160504090c1d0402030106052416120305041704030f1103 70
    0x42e483d04040c0600034240c030522031540861645000c2100a00345070110358a80c0c4140824400c0c0050101005403e030b03440350354000420b443e540d45600403940d41c8080701034014580a650315482c0551500e4000910074402005507294055652500301e407140e07056071240c192404d107607805011a6100f0340082025100c0102120759550352001d04040306402d520032000e5541001a5100401400321004400c040c2240080c00d44500c081d24040c200c1c030740051104811a690b640042d40681c015400d5030419400501c060400d2640c008169402e041c10446010003031042c0440070601c05000110414004549000d4200051030101880050030030324804848030b45100e08080380f540c80e034150034524841e18201c540b42c00d080c035006042c2107507a0b0f5080310703008a60002c0341e440c2110720070460301206684580c000b559144102e1820416000707a8a0040c285507070b13420849201c2ea07054120a010303d001d207200c14220052594640560f108600c00101607800c62544400032400c5003980e0011007101805 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 938616708 1250 938615458 938615467
    0x9010203040510091805010602011d060a1509060e0a050a0c0c14070306020309010203070f050c0c13110c0f01060905100302040f0b120a03030b06090a0e070221040e092b0203 76
    0x40c1c081d281d6541090300345c41c10795070f100100309082d424040d40d90500320b808606201a80701c2d200407911035400a05050507075840e40042844200801c0d00345000340b003d14420000291507281c421860002070701d1603c2400d00742000721b0400515885025025203082d16103052610441c2c0c0d441040480c89841031105000c1d02c08000080b450740c0c0007e61280fc50301000581d83d180c03c1e100500510300c4900c0d60030401c1002e018040b104640003a696840d540100c40306c100c0c115001a040c0040e10b41f40454000a5002080c0c03018101400110380c90ba6008c090300920945445003802001c403032080b680410800c80424042002d42011341c01413032480c44214001c224400c40c000880c08481d610b0404005580c071800f11001459410710400c08440e83c00c440044c40d2511880c006104440140154070901000310041b07031010303000f0440d5000c60344003048502c07901010b8464001c4c4a80161007101509685800026511500070810744900000e845a84001140107074080011042c03019010055100810 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 938617958 1250 938616708 938616719
    0x3090c010c1a01030b0402120a0c05010309020f1c0201081609090b0418120f080c040611160308040f091806020c0a0203061602190807021e0d05010b090105060901020304051009 77
    0x90b54503010f540680c84003041406d00c0d10611014816440284a40e038018084200010703514043c0035080f10300920b80450714500e1800000d0503404c0105910b9807207550444251082c540030542000d05c607000b40c859055550b112403090300c03121103104a8000007070039400e0600036540075910206650202138400918440890b5001d605030b8902502039a11104400350040d803658415600083d0420520b03205c12941081204280070b80140e0061344144020800060380c2c0e40d0701001000b544031100c95205000c140d030790a02200541c0130307028801200030f00c00740104103440c1e030380210030b440030282290000090080c5c44000094000120303401d1f090183d140c990015035000c0004501401c54055550490904400064500b01208000d0220300f044540500007058100060321007150301511a43d100403070001400c040d00b203141e401244d01201d12031818040c0001503100403465502039800300d45036600c1d1420003a07240a000022070060b40200010f111a08051100c042403940c6414420340c15501c80 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 938619208 1250 938617958 938618003
    0x3041a16060507020c03010f0e0a080c01141008120f18030c04020d1a0d240609050109090209360c030d0216050d0309031b1701020a02100203090c010c 66
    0xd665403001a40058220349140c50288102354511801e02c0e410020070304111060394486204040c040c0510002242c420510781007904658015070714548514201d01d841c1d413801c2c2d003080c11030040085900c101001031780c90360464421189000a21466a4208509500d804903c0c000c0e0b0074209405004841800010343c58a0002c0d1800d03441302d10740031035220f1040d404d501c88000e642c00c0d000e01c00e0303942d89024008a0b208001c081205100c09070ba480c80e0003506103090002d0090740e4130040d12709207424000200400316a01400b41a40308490740034240d22003241004044030f4030340030303c1407000440101498800c10740d0905a0402e0f000320a41c1c50104001c000682082c290b40816005600111802c0c012181714001c4180900401c0311285841c010300c3d1401002c8c108980401410b00c3c0601111103c0e01740030900600c0100110600300700c0050000c1c0c8942d002c4c2d040661203802601c60003044a81910440c000d5a1003800640c0c0100f035002020300045944090810058271a075074000c1c244c203190f5215 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 938620458 1250 938619208 938619211
    0x80f06101e170f0421260412140313060b090c0301050a2c06030a0507030c06120e0c040c05073206060a150207090504050c0301060803041a160605 64
    0x107035190480200910814102c9220009102c00e1202002004000020b201c1580c603080d0314000000380403214900398029120b0b00e07501c1d041c0b104144220401030641c02c414500991047e03108201c805000f5501d032030700f40c4550024060741c0302410345c24000124200c40f403444910303019005050100380d4410900114103040e106483c00001110b0000c014041410300000d04401850303100380c131207603840c16003500c011131248041c0503002042002d804120242c0d0304001d42c81c1065004001e40c0c0703019650b403906200c60300813031158401140c0c248120321405038403031080d0b60120a00d000500485c22200080100a1810507002c0040c480c05014a4010400c3d52002d40301280c01290f170f04e01d0051364451820302079031120b0389010059100c0c2c1c1c00c0014940b9640303294011034040380300c0b88881211882c2c099080044581009128070f2400013000240800002c008000c2201940208002c503104c01550b0f40340e11680c0520401e00c04404401c2880310912001000032618400c0403501d000c00c42e0380d841054850 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 938621708 1250 938620458 938620517
    0x10f050c0a06060f060f05040e0703180210120b010f05160602190c0302060109061217040b0a0309120f0503010e061f05030415021e0d020f0424080f0610 67
    0x2104d240600245410400e201d1458489060044c100703071a002404100103c0200400100b68690124504070f10042000c00c0a056004003410213003580303110001c0c2543c0e150003861464900300003000b20030354040c10760014506195a075007490302d0510900641c03650715402c4211070a83d400c1140c0300b018a0811035000d4a40c000307546104a80b00d46080080ca00b46042e0007d1030701074a031000400101004041c0b603581c10382d004011511695070b804d0300001902032503110700d4109a001860280702039040d0f10814425109000b042e0a4800c6180100d0b2124403030380b00382000c100104010310010184905096000500400100c00ca081000c0940031100158201d40e001c90750103c00c0c00104680441d58014201204200b1410700d40000032184450041c01d0301c0c0201d0b080006060109025141c0403260305019003030000303503100d0b503541140124001e40c9120901c40d04441d020315402e10310440b100c0d805003d111804200d181c80e6403042200d0101008104810b0221101c8000211452034101150902 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 938622958 1250 938621708 938621729
    0x519090c03051531050d031e0506090c0d0605060d0e011410120302030f040b09090f04030f03110c0607020102041401110a060518101d010b010f050c0a0606 68
    0x41c40e6160440c07400020703400f1090403260003010403103c0d08071484103060b03035100e0440c0028905007100901210f01040d0320050094000d40300f4084050b5090780080b45200074804094200f68141c0492038102c40042d101c0c1584000c0240c0424040003d4001501d8070500e01440058020341d28000900036174040c2c0c07a01900030381c0b02d0807018040803080c8103400d282005220010b00516104408031001d03c0f05000700c040f0040c02508460a26108000741c828a83d11001400e07681c5440341035150a580103e0380080c07069038036500240003e05219400e900440d495100e00e088401e010405401804401440300e0b01d90f40c041c40314800d4124100704031401041150001030f9180d0030315401d60401803c40ca00e5505004403605500a000000541c01d5101c50b00490001042d0b01c03483c0741007036005a40c03c0c0c141c01d0b134172800200346801d00d005c0d13000c81c0d06000007281e07860714042000440c030f007a9181b00c0704942c04182810305940a00e4000c400034040180c1440c183e4005503115030342c6900f142c010317030041401039 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 938624208 1250 938622958 938622983
    0x6050f04091709271e1e090f010e1b01020a030909050601030f0c08150105090303040b0309190b070306060c050c0915040f0510050402040b0a050c12030702010f0b0906030c04051909 79
    0x401040705c0101d40c6000301c0440c961502c0400c031101d401124001407401100d400001d40f11600c00d12001003084100300080c05868080030f01e8550f00c8144800c4080f00205003503041e4965800001c49808260b499110f2850451800300c10000070070300103003102d05041d21092003402d0043d95104400c01158152110b028074201001210040780d2403041e4103060003000c003c413900b2941c001066030304540f18081d40903030383c1d030703a004030345051104c0e00f042080003450042000040058100b41c2e40c0c030408499a082107055079800f8202c650500c00c050280540e04000168a41800c1c5290010703072201c1441c007690031981e05c081c0442c08850700a092190315540d0b64082c4406064054005401044110340940c101800c046901f2000d1090484484c20b02900140451018000344018040012500d031007a403a4900709001038061300380e20886c034030380074580340310700c580f52400145243c09a040580241070030503024090100400c00a0004a00c4c8070840080011015950240c0c1640900c2411540c014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 938625458 1250 938624208 938624221
    0xc03101e051305060a0204301e12090b040302060c390402090604270501090f0f09050607030f022a0f01090f0314070c060306050f0409170927 62
    0x10581c0c090b0100d00b035a8010070042114000105003107587c2490804141c1c4d03ea6904098074239500040300c0c00a003190701031400851801e11100d5003481e881d002d0141c0d41071503403000000b2503000c6050b00900c00304110501c401c0c809802d1081c05809010303405801c442c030031202c5d02c0b07110104540e031120340b01e211107015442c0942088182003140900c0e4041d6030070b40c04c11f282c02000410034020b50040394080c2c845005202e800703580f110809490364034917020403c40395845950b50000f4218071551038001604201e018482400c85101d400549038210015022588038440300710050480e4086003604a602445801030304100300072003500340344815141940005849001600345025420410500d92400043c4008a240c1e16451b80e81c090b0325207400008030342d4480c0c070f00d003190040500c0a46030381d0322800e01140c0c02e6096801401514400c407000130141d84284200300540342000c000602c40441b51011104400e080f070040c180b401d000614a001040005079480d02480100007204410724007035060000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 938626708 1250 938625458 938625463
    0x9060f090b0d110105040b03070c060c021603110609150c07050919021e07030206010e09030a09050918060c120a050115111e06010e0106020c03101e051305 68
    0x38460380c18107010310400d80c400a84100c0c45540007400243c5040540d00640e8072842c03c58000d40413482c7d1858603420001c1c4003c06000092008a42d020714003540403003214000a0040c414006040c480c4195505596a210b5240100c0c10341c150456801d001448450b81c0360158020407400200b07506807504140f426040c5007500542c030290280e0201001e222040e07100c8010010030051a020160303480d01482c0c0d50484121103202004801c0101003040001c00d40e01003500c504850f00036030302c5c80c0e0316120400c00703135140e100312200d200201d90342c030030304021908004080300c2e03206210010420032510241b0155041c52821200c40d4001d480c000391402c024800003034165049003054000300855810301d200c10aa8802c00e05181e400d105190b201c0382548042002030040d00702d0611000029244a0800310b5510002800750420a0302c020b0000303d030b042d100180038035660078018000c018a0350003a030000b000341204900e04a501c060784594007442e0b401070103900d00850b445c080c07035082040da42c1042070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 938627958 1250 938626708 938626739
    0x4060e070e0f031005091204261501030b0a111306210203090f07060203130902031003020418060e03090907081911030402010f140a03110c01090f02120706090308070510060906 77
    0x90318a50f00b80b0003400340d141d2034001e02428400540314280f80c81d27001d0781a2031501d440040c6204d207402c1c040c400031041003d43d030020f5009456104061192110241018006015100b070380381280010160401020340300b1b04980395241d13641e4400340c484441441490003aa8401c0f10240600e601440009800c100200410002045103201a6003000404030482201e070303000388600440540c011004c80c0d981025a540c11004550040082000f8070003600400010766001105540381e62900107140c1400c0004403c581c44054002c29540e0786950b55042900d001d20040e00c003100500d822085083c3d85442ea01c10400c000c021076a84540b039140c180300041403451b52104010400c00794030001c00b0543c10a0058505180300c909010844c4240105c9403103290080110002c115824900781c030041c060510741c600b150500923140342600f064010010b60743c0c0c04040c41a000000e4503035900f000031030313041e03809002c2d0144580192071650f02d60840041c140c03242c1b9086010016540d540400078230241d4107103030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 938629208 1250 938627958 938627983
    0x4200c010b032803050c10060312021002030606030103120507150b0a090207172d18060f0d02090607060e0705040f0605060d1104030b0a0905070504060e070e0f03100509 74
    0xf011807103d0890301101c1c552443c0c0c0241401000301d0149241d040502c0014800c0042c0d00b42003086a55a0428980c0944942c14120140c0980c8000d4680440d440c02160320070035000d0000d03450b43c0d185550707496034955065151030030400b0070300100000444001104200840040012401e90003040400026480c0c9600000c0450310401103280050007a4011403003400d050f81985440c0d2003060202001380e40b102c1c0828012043e1000501c0d200680300c005002001c024203020082401c01500340030303503445148102505c5842c18400320b81c40d0020b0b60000c000304680980381c20305100466403000180c540176003001041d41c20060050081d42402d124178012840181418401c40745071030085003040c4640c00818540c10341354484003000021701d10840e001035030711045c2c0040340d10706001d8450081c4680d090844080c0103241780081c16240500662060351400c8000b0031040c1c9030240107580e5070340306500301c9800002920518079507039002c2c012807500b0fa0708017202180a1a000064504101c0e954020 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 938630458 1250 938629208 938629243
    0x2120a08070807023c1908010e1207030527060703020d030c0e0f150f040b0a030615170402040e0303130b01120804061107050d0f05010b030703030e04200c010b03 71
    0xf04026030a400140301841c103222207550401030043c5c0c01044c2010004041440f13480100003002840160550050008512000039503180c645a5a4100c929100782140a40002d8043c00b03180b0700c0c84001f0741110050040c05032a0b000c0700d00c1400206035550020761041e0007580010790410440c40c1c040c00b490110340c0707070791408080145880c000103410340d040d020740d07a000750f0301107e140e400070600d242216040018464010f132a80e982d046450181e03070000c0d550341c0c00a0b06002001803c0e1418424004c420802503c944490292030013100f40c2e4007100604c1603034415202c1034111103c140600046000d031400c907250700929401400c024082c554103a001440c4500700184c0c600200d0821025071302902e48603e05281c4600701000c40c030b807a0402c40c0c1c00161344082d4920442d01044420b0000d50040381c89030000340807030349400d0101500c900d118440074020076410f890002d6189026486003201030980c40170641041105e100131946500403203014400c580d940d90403c6114541081849448141185d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 938631708 1250 938630458 938630509
    0x101116271b08090c040e030307052506051b031b0306130c090f0e09060105010c020a080d0c0303060603051306020d0e06011e08030315040203040303110c0d0f0e0d02120a0807080702 79
    0x30543ea8031005260a0800002242004400b80304403a4049040500d03121200c110145003070cc48000c00301036485100158007140ca64404407900e9060700d21880913a0b000da07405124980803900d0a520040843da4081d80c0c149401a4002581c424550108140d68416650383c2c2001ca51900c40400c035004070703c24403807a40c10019441c60000b04181550800e10300702c0d00e40151172020891b28000b41d000020355004407521000c0c9281c0c00056440507034007035030b0141711842e942e03201070b41100d006907042400d1518106070180814140e40060195640c41c5c8030028002080500b4503060040030381250f01c00c5080d042d00c0009002e200c0200b4000381142c2c002840c510705003130000551401c407440d0403901079500440082d09050007644100420389040c0d28141d070f2809082c4d0603903202d1403107601c1040461200f580002c0003030b1107220758660308103001e0034640000c80250200507440200200d680c800384660071210001a0224020780b0346180302da00b8480d152005403042041401442600b24001324200d070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 938632958 1250 938631708 938631731
    0x705040e100c050c07230603010e070f182c060a030b0a15090c090609080a060e1905030a080a0908121005101116271b08090c04 56
    0x41000e0308815020000409800b8040259aa4000d15200b049079000300c0d41c00060a1030070180140e0300700760980c164400d28104e00c0410500740020301a56100714242d400003901c06000781801c000c03100740c43c2000410000c0c00f41c080d460125440d000b807468a800c0408030540004002401c210307030b1b410b50003902c0c0a858218045400140c49100162450350244040780c580e0b08542c0c8403004203618852100c812649401d10312026003403098102d40020001000000c130706214035840420344160b180500710b965401d4540380050701ca0b1517a40d941c64000d45a00c020194007500e0500405445071000c0c584465068a000d000104002c0c071303219a05040c0120348001a801c0b00446042c501c00240d41c2002d40c4070b480000004000a80185400004010300c460700b458101d41c1c0d54407031805240440741c980c01d01e800f000601c4174551260071103d4444001400e0482c0c201c0034503080130b110078000080c005002c0602e01030466814907802d40410294400c0c8000d4100a004500804200340c0e0f044c0309159030607 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 938634208 1250 938632958 938632963
    0x121b1103040b220f09091a070503160504090e070303020d17240d081e0403120e030f060c0703030c0e10120914010c110d050a0e0f19080705040e 63
    0x407111251168614011200180142d903800e40540a42050384c1112919104540c0c01402c185200342e8141e40000c80b2040d494254036051441541907542d901d003152141d01107803c2c50a41c4c0c0c80346c002448824400400e08400c20310602409402b00802007008030f145d07080190512665080398000c1213191100a8142d0240203222074108403825600e0001c4140d40144c910855001e02d00f890740040c4800004040c8074884004c7c0015003003582c440300110a804150441e5071146100007800004141c903d0f00c2e003503015504041c041000501581ca007845081c0d0303001d0a00204072908040d03218003040c00018598940b044600c0060f090900ca1110394203040010400c04084440744200107403d207003a00507202a07080940382d9548001020003d02505d07841902034800c002201002403440410b142d600100082c00c030740307180c040351942440c064034080c1c01ca401c5511002039030b070000420000c540f40c907111401c007030b035840101c1e00701413a01a00f82115281804050f40c003082c899810000c2542c141c4001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 938635458 1250 938634208 938634217
    0xb0c071a060402040e1014040b031b030f06070c0c17060a050403051b030c010510030201082202060703020f010b0609180a090501091203150b0a050703121b1103040b 72
    0x119501003000396034450000b0301038455034000000960301c440038444520807126071002601ca2074000c0000d000070140501c41180d5411841d20b178164019100241962008915886544000342c2a2586040310706075041c90300c041610751900007815031656405110301c0008500242480100c10700d15803100d00500b940d100c4003c0e21740212199988046070030075000744121380560b500106209030281403007040e6901c0381c10804503d9819402c01d00010758013950020040d0560342c3c140c403070780500d464816100705050451048020300645141600340969034540180040c0751180d4020700e0b071401c943d40c42c00c0c2540c20b500095401003006001c142c1d2103643d80e04100100b0041c0300c410a401e5900c0e2555a0f001c1c05651002900551170500f00500b0301c003e80e001540701e044103031800e00c048042e800c40c040e8141c40c44d2280740581c5c0020720441444912802c020000d1501070301d01480380d460300c0c06111044480c16068409038000c44c102241c40702da00025071110040500c0702840c1068034000c0d00c444070303100c1e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 938636708 1250 938635458 938635493
    0x406030f090507060c030206010803161202010212010b0d181523090601060206010e01030c06050306010c17041505031509090a050a030906320f07080d06030b0c07 71
    0x2100d031203080301038155034400400d070364000003201c8000d90391340e030301070000404040e00f640140642c10000c00d1800c000022242d90104008255140b682d664507003804900c0341234032942c01c6540030003440405041001210380600484400988d03112904940102202e419908031380940303011520304400716400c0520100c0214076103c012400c4125031421502020100703542c02c21001e114000d1004402c00050740506803500782e0200c88640e41c03901c0c10192091000d110082c901c2861001c1401498440c8025681003030042c10b004059040c44e0b42c611540d15400c8406900450001c41c0030481c90072403a00c1d10100e07581d9401d015140d400c168400884d06c00159240d503018192440c082081b01804110000001e0340190031303180c459aa41c64028001312051003000001303150219594001c403140c0400207076500080141e075440748992401d0000c10742001800380c00c85071042c4290000f0032100402450381110f603400004110342140341c1404105005024051103000901c562800241c258450360101c24 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 938637958 1250 938636708 938636711
    0x30e0c0a09150306051801062301030f27020114040501140703110d0c0507060806010c03080c0c0a1a010e0105030a1707020a15300506060c190606120305040603 70
    0x1048607840c0b03544410355100030041c078586410040607000d0410ba030300800c10f184000348001e5a5074040c0034404e03c48401d450540102c8101e241c1d500758000d9200000f00300c0c8281022500c11030154181c031459002d000c03522503c541d103200d59021980e22501600c41300403040e03007843c02e003414000000d007403826041c2841c1c44d41c2000240e800074103019404226404c1c62010444100215036800102035501a00084516100781880800c41c0e5004e0301e0202d01c2108180d42c0c84080b80e4954504640c0024040c1101100c0340c42040050f54280080c440703014411b00070003040c0181e8220206102e070000c0b059002a01071240c4000501c840c0c0d402050710641290422440b1207002c1c0c518110803c113102c1d80000079402100c940c00055038003c8000e1103600c448440e195001214000604074040e01d507103076510702002d00090000c11500c8219404075420a4000d0401814054100e80b41ca03e4540b2001540c19084810700b0480100082030007108090130030304405c840441c0181d42d0160942c0914000d16040c107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 938639208 1250 938637958 938637971
    0xe0f030904021c02131e060c020f040e0f1b090108030f0f040504360c050d0c121406010f08070b03060f0d0605070e0f0f22020c010c030e0c0a09 63
    0x2c90500d098076071100240f00c411551000c862011840360812485032941545113203207000b8108001c004100102c0f40507888448184401d50b080203100410726200990160340c81c8404192004100301c001e00b042c801a0042c4900000c111500d824806003004680c0314a213090f0050121100100a41f5040b41c00c40c107080d5156424200100c1e858080d81d0071960308946460440b0480700d0f001000505410047c0001c0c82c09440700900d0007640804041c409042447c90003070800c06d506260a2a82c4014082c41e0a850f10a480b04102c180d00d05490030281d6617500100c10006151000381b02d16030041c00c00300002ca1105181c19031480e220007951040700701380840400040c0007134070713501040412882c2c01445c8001c181900c4c5016001480160344401c005142644083e003242041402602c82d40c00042481010030076007010403c8520140000314138030005420305600c0148180054504c0028200010411280b4610000d0480d14415040841c80d13016088040440d11800c440c4c6096416500300403c1c070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 938640458 1250 938639208 938639227
    0x31407050901080316170a0201150801051e060a0b030f01050906060412080a1202070308041112100c02030708120411040903050d1a0604030503070b01080f03120405150f0a0e0f03090402 81
    0x5040840103d199998400150310741f070079a041d80300d909582245080c0c001c019031544042d9003210780448580340664401045841c2c40030700340d50f020754044001884158440e85818101105801c180c138094203445080b00180514945200f00948c0620250340c410300342031a01203081e0401c44c012001800580c00060300d80590b0784984680542401610800d540d2880980303001030440104541c184d0b240c2e040c0c11065002e500c8c05c440040000c078049402840c54401c2c0705c045c0f10003021044210011740c8010000c00740003c00200103444c0020035140c02015910381801c1c40040e0843e201c080c6485103140144080011790081d0a07038902402ca001d000501e421208240c400361320721102c00684c4004040f40003c00c01c0000801041624411428201942d0ba10352001e90b032000700c5451f1202c16001030109040c90b41504903001d07405802841100c0040700c600003060a8414160b851804802c0d071141000030422981c0100b84480d0803900003800d07040743e5800982c1d164059080000d12454000581004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 938641708 1250 938640458 938640473
    0x5192109031704081b01020c121309050c0a0f080f0f040f0206030c180406050303040b0d240311030d021f021b0105010f08011b080c13031407050901080316 68
    0x2500d02d88440080d03200d040a05001c1042d404c0804a05409222a9811401988180261100c0d0003104c80100004400c1c6000f80d0300f00e421207189100c103140f120074009007148080c080c0501440800ca0a640d0b152074044005140301c01c040180c0c0240001e2500b80001d9000c1006001d0380981031201c0b41106407583d00d861a070042d11044041e43c800070102c248201116038100600e403848446c240c0790240c548501c18031050b00c0d654403c0640c1030700300340810020151510010b00b025100c5a0000032070055042244d042070100b4a2602d019900c0c0040a008004c0004400100603000320004d0a9800c070343c903c029550004111640042038186580c9140001c031030f0142c0d281c030f0780028031000f40400a074101500800003403040800990007800c00240e80c540600c150050070000e5510780038445441907042d5075000020342000c82d501410030000001048103c9560702852003005064101200070bd122844c140250300100d100d101040c00400c40841e0000c11120000c42c003101c198100240c40c240b914 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 938642958 1250 938641708 938641727
    0x90e1902070221060703140402090a1808070c0e060d020a1511010f24031e0311030706050a15050102100914120a080a020901020a03120e07060519210903 67
    0x4031241d801114203440400045105803017854250703003c100300c11b500250070914171070a550181d000b18641002c10800607640e00104001950380041d000c403500e1550750085203601c0350005841500b01c079402030000c1204241c54a801c510111040c440a1605800091101499120b05903015400c2d8030b1a20400740990b0a01c4c801c079407024001c00c9140d1100629402524180c500c0040001e040b25441000b00181c10600c41600d80014500b90016005040c203400311000c03400940034003003190f00f17a01e0b4a5800b00010040584a44000304250030f05000d0401610401aa50380400303000c0c40b024411079a00083c0403404080d001c4020030003030100d051043c9032050005998a50f401004003160440c25a10002d0024401c6587ca804d01561118109412400b0703804242c2d0040c1c0040c214180130a209074007110741100d1415000444146040308240740400d550320007804035902180b0101b089000e905980d501000d1400c00212810b81c0c4080c41000d4081d08110f00301c45070386c0d40c0441050621514011 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 938644208 1250 938642958 938642989
    0x806100e03071206020405030609030c0304120c030b01080f010c0f0e060904060e01060c140606010e0108040203070b04170115030f0b091009030c060b04110318010b03190201090e19020702 82
    0x1c008900c003a0904c070000c3d5100340940f038001e220380004201c01803400012a810300e04040051401c1c60b0800fa0260005800543c00380c5201190b070401101050050344400c1c000c2c440ba04c014400e491503400c03941d0940c1c400340144018804068915003082c0e400010010040c00200c6032150344541c418001802000181c0090f207203201d00c440041411030704810418070090140003921013010703070405c0341561008210780c2c560005202c104a40340550180c00f190740c1091006068031942e607255042c6110b1900580e200501751f40020030b102c041c80d174082c403034003060130040c020340c03555141542c54520484407a80c5d801410001e0340400282150414050b45100c010040d00c240480c0c200360900918a000213035080d10114501001c0c401140380c28070074020095001c80381181103564502d010100720002800c803803403179522440c02591030b540510034180d0303014012403001044174440c000107003041040c1d040f80f102200c1c1402403201d03622030f036003002e03103180c8048038056a140414404200d02540101c040c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 938645458 1250 938644208 938644229
    0x30f01090615120c030609030507052e15170732060c0c0f0d0c0f03060c0f1e0504260105070e0904022403070c060501060806100e0307 59
    0x800700000c5401c1100348089100d8400e501d662a015003462603c02c0003c014054001d01c20100001003142d08081561400303410020b00b0034055440326410940c101c2c5919580c180800e074141001d0404100081000648000402410a400707017903820031040c6004903440c80c0407002c1251618101000100040c04010b42c502849144221a001501020301100c001700a4581100041c0e4107100055034240e5454400800e2145103d0080c0030001d0b14404072315802c8854040d0500200d84140300d4400100b00801070810302d940b42d801c2c4902100c2c54041500200140000560f000903481518042220500189000e8520420000b42c46504c038941c0600c080f000f20010b0381c1410400e40d5000071454112074000e025580e02c0080c1282c00c2185000c846d50b1020040000c00e0150800e80803018001084006c50700c1c00e019200003501d501d8008455083c00514501c04603c1003191501070540103003954100000f80b420000d000409510748031150350704020702081e0405196401700560401481c4254a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 938646708 1250 938645458 938645471
    0xf0503090a0605030109060603140a1104050409080306030c04090201020a080c070e070c0c090615110102040e0103051e06100608190509010609061a0f030c07201e0109060e030f01 78
    0x20b0140c41c40d0800d100c2c2c610450300d089130014109010f406680c1025000034526001d96640c151408002c00c404440c0c501129004d00c008500d60311180f01f241c3e00c0a014084050b01c03403500004051810703c101c030741030b40107509021403800140d8001a54100c0d0640c000c507029114070a070820146061000c3d8450200551000140503e158100e107444100501645904850940b102c80284c1522000c0c03084204422280c140d80903200d202d9510305070481c4143c0300152406981d120b0400411030280c10564098100b040b58403000c511409400c11081c0000c0080e10aa10700158070031170341481d5208070350910559400003211440795410918651038459003c01ca40d05001c211306001345110b01600049500d021000706403403115600002070f000d2000e064030b1407c801080741c1c00b0329410203017110b42030050074401400000c803c1035210788111901c2007840f0f072000e01081000003078010080460340500c026400740b030702030b6800030f114800d440142c2001180028810042071519040c40c440041e69447d048 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 938647958 1250 938646708 938646719
    0x80712170310140a0f09020904060f0906260a080304020621010801060e0603031b100c0c1203051501030c090522050c0a0f03050601030f020c0604060e0c09040f0503090a 74
    0x10090064642614454030303a81c080c9004d0041d1003006000300d8040a107041e0080150368010380045c071100350b01070b10100300c0d2542c910b040d07100c07031480c0d400458150351118070902c03510703814200d400c20f83c0c50307100c1804910440b00e620450b201c5404201c0a031200d8400070001e810340d05c40c042203980301d00c02c0b0850300f52203070f0002612581c165020b0050301c401d5420300d2000203182c800c01583c5805818010013940c0303480400783d11064000162800e0941e240144c165006088083d4030070310311502010344a600c403036402da203012003824025851190a05207413005026aa640741c5141144450080c01d00082e00f60381060180d50300209903221503440a000ca000030741c2010400c001210000501e102805103860314800d500082c0510029800043e07440309280039610b1191300600d070007036010b05001450b40151554001a82c1c4501100c0c0510b40c414410322007000407034031820142501c81001fa0018050110009650300005400500001c05444205081c007000b1300844050110040808407544c1e03440b03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 938649208 1250 938647958 938647981
    0x250b0a020904021b06190c140c010603050d0201090312020304030203030609040602270f04050610180e090309010210062108120f0a05090712030302160210180506040807121703 77
    0x842d45580c114541b0240310061940074091000c18072070380e84800751080c2002003445401d800c40329541c5095900c80000002060342440311948030102e41d400815250801d04000d000c2003810103a101c1030741d1040040001007603011080d00e80022040703d074004d2a40711803c181000e8007610f1001c600d0051042c10240081c44c00c03104850b110441502d1b010082c5103410300708011220201c0f000c0e504000c2c2c038a600c611941c810b807401c5603051001091942d55988514983c4000381c0304a58840031a131001905400c0384d0f0f010001c0700c1503080700d034105100480c2051401c1e84440d810f003003000b03101c2c0d8488006100304000320f010741d00c3d000c0707401040344894079107a80000c40c040746c1550428051031510001c603841210200e4542d041d90440202c10b8448043e5540480080d440414240c0074122050300709001a5a5a082407c21442942e02d590206104039010a103400682d071010744191000c210800040c5404901e0070100d46c9280d9401c50200c1190410441c0351a03c011107142d210400001c021111000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 938650458 1250 938649208 938649211
    0x1917030a0e07180e0102120c07080c160602010509010501081b0a0503060708011805040f022e02011e0933020f03010f1e090b0a090e03250b0a020904021b06 68
    0x80b0802841101d000a18140c00c0340302d0308558200140c1940e0014007078554000060130b09c2407091941a00e0010009040da040c04c012403400c1c004100521800c102880e424002c03176800501100017006507501d040c464541d204848000f20303169012850038000f0b15550101d080f0001e240180c20342c0d000345002038009005460900172814800c56400c0c0c180032090062084c0e41c4601e40c046241d142c0380303001d0380821941c070406d0392018a85000b0042602b1a514032000d00000c802c07030540002c100c950401030b80c0d0500f229114a0081c076103107060580b002240365044070741103100045001103900a50700d031022241201368112008a94000900503118003404001903040355030b403043e1800402d843e903109000241449906651902c103080d8240042046640322a0040d0001000080c07a01d60718403044054071000c1031500e1003078001040a05c12095811041c90f40c911140705070000b49403081d510225419400b401403800725a001c1004c1240c0d860f554100c9000c0d1080d010318040b0421800321082e0348100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 938651708 1250 938650458 938650499
    0x10051b010c1e0206011202061605060a061a160507080a0f03031a180601091e0e010515030403050901050f0414100302090307170313171917030a0e07 65
    0x18054104203070b02540c005280b41150031940074000691800302084044003044005903440a0100002e0f01c554a0070b02441c007055200304040c2c00b05182252040b400c5a01c01c0d80600300780100e200c450442030b050503040394404981541440680c0c4000d003091842c00880f508200103600c2440c50075004d00403030f01ca002000321303c00c0e901840340c4e501e80e10610401d0340c41c0c0b040c042d40100354040701d2005c1d0102040095881181850710048180c0c0c0c0d8488208076800900c4004141040d03043c0a100c41000a05104c0c05000c0039544624002c003588000641071000034000703030800c80007007071118a03603202d48101c41e0440c1c019142d05440340d8440050449a850b0341283c00e100e059210810074985000380261034200b18000c014020003407401c0f0002c520310642d41d400380f006000030400e00c40b0004079500c4090141800000601200c2a10240e6510305040849101b0b07000342d0a4900a000580004041222103185078100d91203407038410002c005080814540f0807140038bd0b0102162080e000c80700f0581849 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 938652958 1250 938651708 938651717
    0x31e010b0c240a09030309060f2a2705030d05190305100b0d0b120604031b11151608180117060d0c0801050903030406110307020c10051b010c 62
    0xb148034024076101c24030481164959a15001034140d1210390300089007030b4081e0030040303101152a902c01c011250014402d6500d6543c5000d2a480780307100d45081c0c0c0f0b1140090225404101003030b007003d032902116490030b402d0020603500481c281034a9401c5103004100180c1102c045040c007000191058010b1041035148031036015640603c43e10078002e00340101c241046425038203052078143e040c242d1162085a05207500d9030050785043d203c01e0302e013025050961000c0c040f00d060910f0002c0c0540d50282580d00a140c5100681c00440c950008030f414144003152550140c44001100410740e001d205011041403850041c0c1d44180128071005010300b00440a144074640c07000d40054071100c2c40b43e0042205042d240c0005001d5040510910b41d1081c024280004005d64403080542520030850351035040360800b100307100c10040c0c40e0048075554442da02c001d909502c3e115200039a108616641544680341400d14050300034041c5080b54040c0220080080e2035100100d2001d0190540305003810004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 938654208 1250 938652958 938652973
    0xb1b160909030e0f092703160501140408090402070f02040c0206010503070f121704030507120512040b030f0606090a062a150b01120905010c11010b0a03030302031e010b0c 75
    0xf460700042c0c1160800000b80760264544510040f0380c40585443c4508950b011b00d104030700c01d0700e0800c1000e0501040201c21091f0302d40035038a00b16080d6401c220f40004009005401e00c40001e849000b83d62000303a00340c0d40141c4940700c80c144070595030504107010350003502d00b801f1001c0c0c07940d000c5861416508150304481205988808090088500340b04900150704030982d91000a541c201c01480345601c001402e07800d01d0744a450342c40c00c01e03099912005545461200b150b0420a052000d080d89440354500c09081a1900e2840c03050340c4070041c171100c0f54101d0040022560381e614019190404805040e203500941c417100c01030504100c466203445909907441c0406040a0650400400030340d2004445500064003080390003c0c0102811302414030001003060a180442c510034040664011000410b01c3c46102c00080d194149026071805680d0506000c1651234848072a001e040326814500141c0c1c1e0f40c2c885540c801c008020301000b03418500c81400000f02655207070058007002c041c403003d86800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 938655458 1250 938654208 938654237
    0x6070204060e0f15102003270604050d03030c090e13050c060310031b240810050a0b09010c080d05011a070b010b0f0c07060302030106030c090b1b16090903 68
    0x111034215030568030816021421303d0341c030701c21490300fa010100c01170061114403001c08020306680280842329a042481880c01c0c440c001c41007014071158038191000d6150504210100d002c0250307211018003415141c0281003039051007880c60304000c040c00d880001c03180c10002c2c2000d4550b41000d00542e8540f013212130720140e0b4070f4441c2c126802000003c2921990620315946c4004890100e420395240e000305083c005455417100349041c0b5607a21020780040c0822200d0000b034080b500141010480d0b0b0b035139950910058039200d00c014169a031342038085403101c50b05401205d803503d008030b00800204010a5890b183c0b480c2c0c0d040355043c0e4440c0f580418001c81141c2411f09107004400c0c0113462561802c004203d0201c00d04002c0c0040c2010030381301c0385440e00d159140e078503028480c0e200d00e000a90020040200c23540c03601c100a400e2220b440e00c40750141c60801040424010003e42c000c0c02000c100c861301c400c0f4000c001d4503016078000420000701c4c542d1048003c00609a2440c00d4022660a211104c40e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 938656708 1250 938655458 938655481
    0xa0c0b1b31150f030605060405090c0c0312060907050c070323030c0303062103030705031509131202030c0718061205061f081c020309121f02032406070204060e0f 71
    0x31b03504040c11823424070345031500304442c0210283c203100070210200031035414002c0900040c051600c525000700e0107030030004d0500100c90301c0188808200b0030240540d015030100400e10300b04a0f9040b031074070079588290300303c0c5204034035030100011400d20000820003c9408080065842100c00b101c2c45403050070034102c0080807584c2a030039104550802c00000c0ca4040c00b9a01658003c80c00d02c0c03031040322203100700109001d40400d5450a02101c0800300c0c0d4001c000194014007010f0320580702841c1414409050959500003c0c00717070007504c440881446d12000d01a0b8400d000070200354440d00303081002403c289454041c1070381d001d100c5580140355204003407000f03080b680c1240c4600340100540d080c0c8802c100c0c03002c1204440441140400c02a50803503a442d81e072160b1030081080301412148440c4081117228241420000d41014010f1003004031160390aa4461880030b03560f40c0c1d01d104184014005a42407254003c0254800d1812030007040052040020500c81e140c0e602c0c0c065515120f8280028 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 938657958 1250 938656708 938656721
    0xc0305090a241e0606050901020712052103070201050c0f03150a03060f0c021c0e0d030908070603020c0c0f0a050d05070b0a0c0b1b31150f03 62
    0x149141c0c0801d41610020b000904a451200c298030301c4402006040d81640003600d20020340c07407914103e00d0783c14421059851081200525132400c14600e881c60749000030351505078500c15100d600000718081818004140401c0756401030500c00203480d81d08180110b85550003d43d0748100642c6440002451401900c00700c48030001c013000703500d00b90790380c41c0074402d1000d841950305600000c2003540000060900e000d202c048880108020508800ca2000240b9101c4c69000b0440d41580da49400e95980341c00417055030f010901924074004000b0300b030509507400e00303055201d43c5040c400c420000444030780c10b501420325000702c0c0f0103903091755100100b0040381070442c44ac41544418004000c1000d458103041580b400b41c032800603512103a0b51540030008540007011031a01141582d01e800c0104001c5403906a4000d818040e038518002070141c40104600a011a210f1400b003042c60000301c8080310311141142591b51217181d84001d440d03161520059981d9142800410000c0341c2c2d20001d14041d01901 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 938659208 1250 938657958 938657971
    0x30a030507200d060f290411041520060115090504020c0c190b07110f0a03050c010503040309050316060216210f0b0a0b182224050a0c0305 61
    0x700c0c9003180e0f54803954001d140c030045658070299504070003640c11041d18420030340548200302044030703d0545000d010549540000406c03404a040000b4030080480c900c504450350094a00520a9031400c400d104d403c0c6001030b102052880784100001e00e2004c030a00c00319400495942d21600c3d5030762142803206a0090300307a010300c17642013402e680c01c16003029944104050841a001000e40780e840302d030700304d03c2d91005606540010548444208900381510465075000040d071354500d082d86140c4505442c0d40303000c13090a0400c44008007040500d4403038800100504401415500510014542c030310311088248640790140c0102d08001d29441d1500580c83d0403074030f0034211707038150580100c0304005002000360121403145220b484440440d041e00750803032103a000003000050020043c410014140280800030680303100d850100041c0300466141d11540c5655811120306c441c00600c1c24a0340c1003190808080c01885404403400a0081900600c0c05058400d5041100760208071088066401c115101e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 938660458 1250 938659208 938659219
    0x903010b1206280c0302091e011403041a0702100506090709030b06150a050d0e070b0a0503060d290603070f05210105010312020d090e0c0c0a02030a03050720 69
    0x740c00c65860f00040e0340310000281d10000794000c401c0707001d012200715550304400241d0100b5508614201519031200e0301144c103240c02841c48581000034020783c0e005c0130240360305102002003410032440c0c60400e003400308030010103c2c2ea8500707800c00965603000484400045403c1102007040342c200a64090b02400791641d0301c92039182180c403144180c00e0064031054200c0181c1c00b54600d800f0509000d0700c6a01c2050b40e40380d64401c00414440152151901c0c501c050f508078140401406240d80c0840d0104e8449080c4103407655107510014001c040c0c140720280903849407055541c044806107484d0800e862402c0c07200000e5482d1802810b03542c040c5809a144000540721061015140924465410880400c0148540c00a001c516800e41d0350030f80c0100c58240d042d652440d545501030105040644e150702e000c0c10110318040a50740d2400e80685980700812001840006101c42803106500143d000f0301142c541c6000c501d0001c041c0c0e48031440c1501c291225a203c5030030708040244540600da001002c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 938661708 1250 938660458 938660461
    0x70311012d090f0803040c030507170c0907030b0a0b1b071202060702031911012d030e01020f04120b0c18010815120a20130207080412080903010b1206 66
    0x4403004000ca04000c0d01e603c2c40035001000041d002100841c840d6100d6845044c1040c5540b818910b018584d4025000b5191030700361003624504001182c00b849001260081855200c4150680c0207080a401d2181c001c1051100811201400e400502c440034221900c1d10000b51802a0503031a00780a00a881c0ea000080c1c050b00d0241c600880039091141c0020199201e0800009401041d503502c0c000481e0b0803001074880441c0c542c2c1148543c10b9604600c49145041c40545c2c409003800d810341c4100400340f641e01e1280d10040842503059800c3d14410382141755a86845403101d40125543c0401100c3e0444082c000400c03a03d2614103603417120021495070360300c07007c0d14401920360490050100000e0050080c0d41003050b27445500c3c02001c9039103200600922000b608003501162204210307046a10301068044078680c540c007003503120501004030010303101c402e1441e11180e54461540800103112101d01d2060600184000815201004a00800440c420582072044100c004401c900181e0071900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 938662958 1250 938661708 938661791
    0x8013306171e070801050102010c030e1507021e0705120d020714030a0b0a1a0406290d0c2001110306060a09081603021e09011a0f07031101 61
    0x1801d00b608000c1c46518002c0c070398030407420580100d40440b5204001845400100a04d580a214503100c082c694a814410000c0315100c6c5079560340c03030842d85490351140c000040ca84038424020104210350000243c9140e660b0304842030740d10b0750305019940c8030750003d09055008400000f110b00305841c1c0c5030054208146055418074580c000c244040743c26008145100000481e1802482e10640c0c002c440001c2d4220071140c1800b62414143c90745010f1442c1c40300c184444005200d1040070742015808110016041040010483c060468015500c5081440c521082078012141c0c00403044906800301c03071244006001c609941c45030103080c4002c0380c10404074034030303040010080203200140c0c24168000c6548a165529064507440d241001b011036503410f10851420b8103c928000f2451411402c81815402c000f510410041c400c68400c88420044410301c4004070040d21200c0c0f08650020b9110340b803d0038080c2c004003a080788000654640050403111405051210f50680d001c0e9000100c200c0303c68 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 938664208 1250 938662958 938662997
    0x80f04050c010c06062103031506081b04080105330a0b090d021e040f0902031e1203010e1608100b0a12020c0c01030c0f0206040b06010908013306 64
    0x820042c0c4195440d01c0005c06c0700d01012040741504400b42c040b030796142d078150500604031444450140c05031a0400f5041117003e0b481101150840b007520304102d0040164803400c0803920955115204039401c050030040c0303e00782d01442c10140d030701108002e102c1400c1e50025140080c1020000f0342c0c404110001448040101006815100005040110744080d01c0c0c000611411480d030301010707240103c00c0718100e03500303050090b000b1284090f40244243d4080d03600103905c891024642c04656201a140c90a85030700c20410703c58500310125402d82e03296120214940820012107184811003014524501040c0c8104a0301d031148284019500032a81400c00305000c0f030340114410030402c8841d10a074140e030341c05440100002e03405e9030024000c4004800014080c0c072030f000d01c40402c2c410b5110072a40d00329004600742d07030302960081200d2410342d10100107840350705483d00304500c558031f0106aa50b100100b105204100c1520401d46039400c1121840900081a20301031580002e55480c915101035660 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 938665458 1250 938664208 938664227
    0x1020606060c282f0d150506040603080315010806120a06150f081b090709090e10020c0a02010e060f120c19020601090507090e070503091f0903080f04050c01 69
    0x94410100c00e120842c2c0700c0422909042007804090f4061018402a8401c0040304041140c0d0903103170511905e4460722100c40701c281040b1010346841d103440c00280c0903034a40e0300c081c02455010007540c0e101e081005400d80e03040703480d80e440303400700d410100401c050340b0702511101c80c074407648402400442c0c6242e4405020700133a1501d03e000c0c00c1180804111000b4442d0110f024210607001884440c15440e07031101e102800810580c09400040c050202081d071003c5400e040c0c0b2859000495084004c0c80c40605d400c0104000e84005071020821780100c3c0717804221000014000d80c4c0d2080340e0495607040040511403c0c0c0915050034040000c1c00c220a94800c8081c0e0020b00403010b6401c1010108640072440000c04c0da00d001078100100501c030480307180c03042c5500407105140100c025828202d014100748400f402100c140100403000825012080002c000c00c441b00d04035600c240368846800780d02030003c40e17004402207801003002458411345125254450380c0c200c001080110306150042d00c4030102d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 938666708 1250 938665458 938665513
    0xb03040809212e0c0e150408030a110609060105060a110a020303030103121d0a0501051804141005040911090c04081f060602031612120906060501020606060c 69
    0x242c120b60140358001e02514aa00e61032020800d9511040ca40301848800d6011a183c65a031800082c520150f500004141d112241030312480c4904101aa10704418040c42c0e0282105120000b003c00b2500d41c418445045501008100d50942d00d5007080030340c41d4102402181d41050b02884080c0752a03218a0606480c1c03207012040c1c0790403800a0300070a0950380242c1054a06221000c01c14240075442590580000c80c1c00e0820a40c0d2003120001503d00c81c441d11039541000400311303010102ca1a51071051801101c01841046281c4000210480c071140840701d40b2500c03030b0013900015060410340171711003d80d030b8004c5c2c007102c1942c151020420031050180c0b0304452210207000c040f5040c07c04106030514003600b2081c2075180e10b040c0380d00760283d03070084c2c04c6042150014001c3c13854401d0410359071505142e1140217200a0b9180d140c1c110b420441c101140c581c61401d0050420503c4010344c0581c00380c41c420703403c0c0c03003255440d1000d01803203101381d1800c548a40c0c07014942042960018488888601 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 938667958 1250 938666708 938666749
    0xb04051807020d1d09091506120a03032007050f12070b04021002070b0f04080712150f020d32010503030403120e04091415011a0d090c0b070c0b03040809 67
    0x2254100440c0d0301c5e1100302c40c10482548920360005140b01148101035101904a41001028090005031500c842d9080c1e401414583c9401c0e6803c1e1400c00d18071100150680b20036819100d003201d080c096641d14507019824494061111151035041e03500c021100c0300b40d086096403600b512103500748047c9002040030b10301107004030f02c0c001c603051100f040104404184400c035641c5690402c21031500b401d0a95108410400e5506080c80c00030b020030b403104090800c03600000410a91b206603070ba01030711809106100e40340c905401070000c43c40001c1c080c3d40c0c80c0035031012000007100102d81d10740c1000081c00380701c0d45903109120410004102001ca030451007070710b140c60300c0001078480104007560f902c83c0d012039508010400d00ea03d03015007007002c45051601c07504292074551500c10344200e02681803902c41c040c140c0001d1841e20400341c94005211144c0e1004900c201d00c0d0f0388152030b12494124080464002d411407200060340a0403000b0f803400340d5040310a0620300310000082003404000c0c00384015905 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 938669064 1106 938667958 938668007
    0x402041220130905070305030c0109200612280b040c030911120f0304061e0c05101802040c02031c05130201270b04051807020d 56
    0x62060b860020b030410325400d10504010560b00080c00e07500c0000760350020054150f10403400140900499542d15140709000280c091440400561102c0b040c0070703900e0001c8400c0320140d0030546e1001424180100d00c07a124100c540c144061031620756072540c0510700c41c10103020b00e203401242443d04203c0905c07255142176540c1450300050b03018407140d61981c031801104000b4891001c00740c80c2103c0e1510396410004100402418a4405114070414952003540c0507599001507990710a01500310f198510000781e005000907203e00807034800080c03440b030160703d43d0721a440d69154981e000d90b554060202984814940030380003000c913145030804206000446c4004a0035050303091800401120030441c000c02c1c10000501c3c41040c0498036180026600100380c0208100c03101030307940341e8903141c83d4580070070000384c101c4a200140c0c210300c82c10a00d880c40b0742c070320b40a030055505454086 = true := by decide +kernel

theorem cover : BRFrame.Cov 938489208 938669064 := by
  have h0 := BRFrame.cov_init 938489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 938489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 938489208 ≤ n) (h2 : n < 938669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
