-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3068
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:34:02.590997+00:00
-- url     : https://prove2.me/submissions/bc491a97-2b99-4435-b582-742898f33843

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 551618705 ≤ n < 551798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 551619955 1250 551618705 551618713
    0x50903030a032c100e0a021806130204261605062208240c0910112406040605061e0405090a0b010305090703030909110f04030f020a09050603 62
    0x2011800701c0107007220025180d841c4440780880700c000303d054007000750f6010040001d01314040d2041c007100210391650a201741240d0100d003040c07000d80c40c0d040f48410280150811800207903689004100801c10180706007041c01d20004000622941c5403a5400d48200c072041e410b103808a050314490382c0c41e03004030060486018140310070849850000010502040850b9282002000030921040081c2c096400111140c11108100b01000d000307110541a18682c0c0b030700c104290414001e02483c601440105900a07562202c210320118001c41054401c05004002c40b806a10b48a000c0443c0340741c01034002c403108074814080380d02482c1a0040405542014200c0f0742011041c01c156030020501b040d10745031130401004080342caa00c42c4491684114060b503008190b00300d00c40d0005003155001003070038074180c00c411010b20001c0c0d0300241e00c20445400c4140401c82d0300450301141106e101c0e0b54000e8038a210002800010401000340300300c09280212046100c0c50b9840070840140c400c102c1c0c0095040d04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 551621205 1250 551619955 551619967
    0xb090c041418070b030c030601170c0403030c050f01050702070623031303050d140f01050d020904020105031b071b05090108070b0307091d0411030d0507060c0203160305030f010605090303 82
    0x28616005905030b80e82c2104032100250744481d9081e042d40305030380b500407050f070000800500d075070008004c00f15143d103071603107404500c1c0c1a9804c1e0311600803400003c0801c01c40301030308020701000f0011618045543d0300200f0a500348442d0203035440c000c0c0c3c401d81010962171503000042200c04000c01c0007042100b1000c505d513a5514008100501d039440c022000d0081c14003c060320101ca6119102c105110855001514200758143c0008000140d0109108090a4801000686550815980255080c2002512034503502981c4e100c10349281504a808480450074505000e40000c0c3c298000304049500701200341c90700140005000d0074003840410340e2100004115107a01c040045a0200c251710b031a4450523120502c10385807003603d00202c40c50140301d00900c81801440d0741b206207110001c8000b410800d420756405000e074004c40c1e00140903031f503a814462074064028400c44201c0054054003105240c130903d0080e005410941310020025480000400d080f8023440403100400002801941010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 551622455 1250 551621205 551621221
    0xb0909010209031b0a172404020f01111c02060609010603140714040e0a1506090f170a02100f020118023709092010050d180b090c0414 59
    0x9080c501135941010039a00d00081d501c1d40c2c01c0d42c3c0b41814517540041c1000c4060032008046021000400104000d40700e024880181d46218211503088021b00f80280c42e8520307d086281071410003401c01954285040c030300d40c28150301080c0c882c440c01c000c655450b507990303d0b598124111607001940004408061002c181040d0103416010000050f40040e140740c251100340c0181c0f5204d0550f040444161204170005165040702d0070f4002800d03140c508138901600d88900b85d1315003c0709110b41141860380f220b0120101400340800c1c40c41c1034010381601c0b0005c07003c1743c0c028400030080c0b560034010752a00116480c2070b4501e0303a0441000d0f400528000007001c030a11a0107a0076401807013203610316480c03a0b54155440300710402c0b1006280f00302001078890040e06040030002d07851540c23140e006026081c0841c0c0ca5071082d4a1081da103005151281e142c0700c000383c511700204040902c1949005440c100802081049800544a40c49040c00c0e0b4440b440d1000501c400e80d03075a4401d240e80101844c0c0090640 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 551623705 1250 551622455 551622493
    0x10c02190f0e0a0509010e190201050409050f040c060807080423062706011802030c0d06081f0504031205090c0a0b0a030b0604080c040f021b010b090901020903 70
    0x556104000c4060a55441c00020258042d5204105142030381e0100b10082d0b5070f078400c3d150b0060014009001800107111011741b100c2054104540b42003494004034256445032094401401c8115410040c40c10440041a00440100c4040b00e0600c80c04002040103480794468900070b51180c1c81d41d103896245e07591010400748000403200b801c0e110495140b400544c08012407405084407041416184492030500d680700c0707c00b00e10041c0c40d82c1c03041c0010015801c00048210300d1098103240103850f6162440d20344282d00c580c8518550a43c10710502265046000c0f07140e4039a4070b074115040301d100c52030b291400281d41c02202c018003c60385510b014903100c1141d801460f8403504203002d50301c85060a600103944200305400c00a8117882c04240744880c0381e010b00c560100310f86c08858a501b807a2400f12440d698552034070b8910300ac1c40e15011001444c0019405a40d5440d462441b0240c03245400d08840380284420381011340f00700540c0001c0303a451030040c4203d40300b454000d006460390000040b5004c2d02 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 551624955 1250 551623705 551623729
    0xd0203330d14031603030614060306040207260a030b041a0f151201150e0618060906070b04020117160c050c0913030e04020a09060f031113180b010c02 66
    0x190082c2e01240c05007400b44002c1409142400484010001da03040c010100c802c01d03003042100c145446002c0440c0d95404003076a621040403200540d42c2e880c18035100d281383d4102c900020711009a0000b00450814540250464603060b50341041000f0701c0b01d04000c190303141d6441d03a0300031031056040c1c1c41071401c040c40d000300c2007031000c2c00114101d0506a040394556020131501c88254080400500c10485800c680303064004a030718098075014071200000f01644038220140466221580394028181c9520065400702e01c4010015501c40800341044140180e00700c07802c0b80041e03003880841030002c0b003810030b50b800740105801141132150150015242844249000d0303c0c913102d113004a500310740d2086401c0e0303c100303119944c1481d11030252501038505103044020314400c40c01800b81048290b84020300c1c1c400c5072070904e0000c00c00f0444000540061090140c003a070080400a401c0030000b584c8800e8804039100b40c02c5856454842443c982c08840d1744800d05400220341190510243c500b071805440 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 551626205 1250 551624955 551624963
    0x50904020c0106051e0a080a05121608040f030b0a0c02030405060906090607060b03060a050f0a050403170907060f0212030112140706030f1103130b1801020d0203330d 73
    0x24191340310380000d18192509440035030150310807000c020441c00c0003048540145414402420701030400da50b0781d5201c415507011500d9000010444030500d10b00302d060480788681000c0d0080e904c503201c020000754017060340802d45080340f6150110704101e54911410880da06c0c5d41d07001d5401c150030403081101c10341c042034260b68810014050818680c0d2080c00502020344030704c0c0e00103058a09801407504094004140100c01480c050401001301c1c107904d40190b0000c903000b03000656030b48519060702c040102ca800301180c0111041003020140000441d2000c1c0d902c1030300c1c3c03903030400e054000c201e90b50810445420b054403000d000402c4110a04842810711602c2400300107600441c900d4a0b1b498540290711000019071504041020b1100e60b2041194076405005000c1c5145012454020903a800d200020425000c0c0c0d0005142451a01110041180c4c0c56000307550f0b61403002c440300d01a410030b80343c0a800e800e110f20b2803072500b90800c4152040c18121281e40c0002c0d503078002082200c2d083c418081d2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 551627455 1250 551626205 551626211
    0xd1202031e0a091a0c0f070204020f031807050d020607081813060906050117040f060b04060801060f0e011508070201091403030711010501120b1509090609150106050904020c01 77
    0x201500e08000340a6104100c2e600001030b4a22042c1072200b00001007540c880c0c02c0b444240c00340400c4540c100c04444210b941e221850f40c2e10801c80c40403400901c00c54420103042031000c8240000103c0a142500c0ba00000c141164a09a0ac60041207030f1115079540003940400b0800c90400003d500c80c024000c551809450700c08400d000501141d0040302c0305541044296848900f40254541841402e000d40030a00e03201041030a02c0324516103070500608041c10024803c18840d003040310076000507141410142060084a9442507100e01030300070360280d0f103e104600c4030003060200c00c10410714101d40d41c8030b00703c4a80e1023041000b554464000b80600045540700d080c1900443d01c410050300301c000d1070100650b40d0b4070f0203400c0240b12202c694904051641003800401c440c0b901c0d0380a40c480c691700611940303a1910342010003910481e480c03040c16008240c8104210180c0070218001e44582610b00946881010b00d50201040c16005d0007481c1c04141c042c800e4427068100307a4080c00b8014000300c000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 551628705 1250 551627455 551627491
    0x1d040b0409020307031209240c06061a0d050105060a08160207050301090c0e0a140109020a050c010f06060f050c15130506090d09080703050307030e0d0b0a0f05090d120203 75
    0x72a01300740403a0026580154004181290309500c806110300070f00300c601d580d140e20001200d0881002d861010700700304021041c0c8900061001c1617205c10010018108814400c500e0031010500c290403916030b5403400c5251000001d805d06080701210664880c980e0b072a469a5107103a140860200c80100362070451044000100e0103440034444c0c20411405000240540f03403910302d00200c0004011300c440c44c070780e0511083d5004400720b8600e81d0705403882c1d0744015031203109040c0b080380c0c940101c3e102c6080f030751b00302803c0c0907083d0229409041540c1181c0d48012800000350810384082c8112100b80c0a29440b114440349071000070284190041d21101194002c3c4a0075212203241490aa801c500d01e40c0040c01855220381c4c1100f40b04004151220181c0310783c030300c0c40d22615100c2c0906503000c0c081c03040e1051601d1169031707641440c82604d03920070501c0255050030754200000f40700c04650780d42060b2404000c141c2c2001e0000e0503990050313041d40d590640824080f10f02011750009003403100300036111004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 551629955 1250 551628705 551628709
    0x2206090513050f0f1e07030207060b010f0c031d0406030c090b011d010f1b03030c02061605180307050907030204051905060a0309050106090e0f16061d01180605090f011d040b040902 79
    0x217658000e40b440d9402580b40c3c441801e00c81c044a040310411414054464000d0300816040030100501c0c90b094200104081c010b2105070180c09052104641e1052030010044104450540c0c03090580c1c41c242e034100010004d42c030040d16041054441008030a01000703c51030321350f2080c411202c0159403450800d02c400c0d00e4403860354006100f5001280440e88620300c00068035810050190f002e00051050b0040d880d1040c800380542c465004004012603001c880701d0001d407002c002d82402403e01605005a5180c4a44000c000750001c3c001c0601c1100c2140d0802c0c90402c0b40c1400400360350f0700404080c605810a4010303001000c4d032140440c4c80b55203c0b00001018040c0e0300c641040e042d440e030040c2105e041500c00342800c1c109144003101401171000c40a1102d01d5010100104111010105241d104480b02c0144c0d51400e0011020302c500301e41003808501e03550320001805503a9801d4038900b8241068034010b4802d000f140e10720040310a61006c08010700d190542100c41041009000000c10504c1500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 551631205 1250 551629955 551630011
    0x6040f050103050a1208220525090501090c2f1911031b13060e070504140d02030c0d02060c0607030c020f060f04082206090513050f0f 59
    0x44192042e80000f146601031210150380d4550000d0f10303203011511842c01205400c0540b0303603400300401c1d005810460904000b03080103046140b8119083c0c0c9095100c21071400c541c0b407403090040050003810000005540c1085000300c0c1d043c043b0175255405466000b9271886040803002c0041100506c00a5032051000702c00e000600003103445490074202c2100701d0a002580c0d00f00e42500a0203a4000000103421504455415440e45002c60300d5540d01c88824a43d080030345600e405c2680c08403c3c210a100859401200400848185441c60020704080c201080711123000b2080c0a50190003142002c0c00c1c1c2d2402c0c40000325150720041c001400c12540c100800c0c60208119000c10210390b882c0c101d00c440c250100b0480790050511070060032245049208a90fa030b490240c00140980d901040c0c1c94200d62908034404001d5959480144540365900c0c0d00604108080c41814001c10100d100700a40d4103e40c00380921401c0c80c0c0c086220f460312000c0780d41c00c00703110092078007c0043c3c20000208030006194 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 551632455 1250 551631205 551631209
    0x618060f18090218060f0403060b0d320114060111030c0106080a0c150c1b030f0b04120906090b07030c05030f120a021206010e030c0d05102f0306040f0501 68
    0x1010040e01c0d0061240050306031004c00043d184254030a1180340140c040c0c000454065070361214010600440309004155501d401c114003d102600a110541e44600c240c0301458401c030f248a00c9420020f04c0e11741e00c5003200d041c95206c401143c03104e03001030141d5000b8200c803d141a14602145e1810800014081c2180c856402c0f040d0705030408908481448940c3e1100c80140c8074100307810415440a100c080e240d90240c601c000c0c03000c466903104d0f00480e507100a181004540140900040c040c00b85011440c1d070320100c80480f00c0f4440d040d0000c0b212031207480d00c03005450460300d60100140c01e280507c100c9030051002201088003c0c1c2c08000014814001b030901200007000d80c5894224940c001d0355080c00c000c0009452504c10301c401030522903e1707814aa0050001c0c2010700c0362580300c00c0842d01b422207181006070006116044002044000120020742c80d102d6502000680203220310b04198025204a203045519800002080d021030f642c001c3d600071100a00024020200c07a07041c4098a00907 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 551633705 1250 551632455 551632469
    0x180f0303030f2403030305130609030503180c0a0e0606040b2a030901080a0203060a03050d111b09061219290f130c0b0d020c070618060f18 61
    0x5040741c0e5103a02c414000e1803081e01108010030380000029a110b425081c407480040c0405440d40040b64103034460307001540107590410300c1440300188a0601401c2e560080c1c1d03e03001812901e0070340c40710407140401c0040e0354110003861b14881624160942c00c0c0080c020303000707aa20001c01c210005100300c00740000c2c04095410703190445030501e014408020300300400740d080000d400c2080300203a00d0b1303401400305c0c0c0d0040c14500010713149d4543c540440e503d00301e1a000109036102e40141c8100841d004465680a40a0304044a880c0c02c0c1c02d5400d08010700032807100b5504444c2031008910245444145450300d00184801c4071490344214401c0071031800070a105403908480c0b0304119024240ca8840410100040b40340305c00103003481827002603801c00060500320b00002014008003040344014490009004000d070340da0b101c0c40402203540c000d50060030b4044492091010004040740540421214003202d030f112143c91a01d405e20a56079001ca01e4440c0c002c0000d4a004002c803c0d081c102c000b8050410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 551634955 1250 551633705 551633711
    0xb0913031404080c01030c1e020102042903180f0d090e0f060306061e03100e06131e03090e07020f06011e12030e060c0115050d0f03180f030303 63
    0x2103418090001d28aa60850280c07100800080c01900000901c04490003c03c3c6400640840c810f0003c41d2059284142094a01d00780e0340c400c0001941500a030050300c1020348207420a8038010340444120715440401e9500500600019120f06c448003229a2500528000d5501d0040c1c0c0d94407290401e65007450003408201e19a50910070b0001d640e8856500030100f40d030b4000d8600304500041e0f520840240814807580000d01c41805070600d10b0030107440c9080c003400302c036551042640804050811442610280d10981e00091564010105554400c076000544400c59415680208001da01c01c08002d85c2803000c6260000b50081d0000d01840c498601d982c09440300340070900b0043c2c1085e0069001d01d14040c02c51980d101c00e900608007000485603154200c0441403800d141c10359052084260195010201203506001042c1c19005121004445015100780315181c9040210014a4060203803012030074611050010340180b9480010600003610540406d0340c8403960303c0b143d549030704100c001a032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 551636205 1250 551634955 551634991
    0x504030b09060901050a021204020d05120a032003040305040308130e040503030619050117040c080703080714011a10230909060604060f05160501060b0c1e1b040b09 72
    0xd0f084c4100340e0010b01d0a401507240c0f15010b0340048110b0000341002c1d2050701214204010800100803601481600703180c202e80301c1200700303009001004a0f290200403402c020700424012640201181d00c00d56054852909241c2542c5400034250002c072080080c500b140400440c1c144550407006e4407442c8201c0055641789010014400c1440c600070904c1344680d1603c4041c010707aa004074040c1403820b8401e078009801e59450038904401c0620b070b0702c4009680076086d0003000b84083c400041a416008504206070b0801c4030410908840705208110000b25008202c40c030300c4e1801030052003807510745203400e0814603030030201c0e1a2880d1008002d405a541c0004400300381d410840700c03450340240115101d030300700fa02e1b241c0301401085e81d15084070100724000420044a4103c4848500440c1d00f001c000c05c145501d03043c600c11140d1110403c0e607064412613004101016000d55001181501480548020780c10518403d4404c140c00011341d40c800d4403a00c04001a40703880103070b075204010510401718100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 551637455 1250 551636205 551636221
    0xc0f1201090b19090f150e040210090f0510020a120306050f010903120c0f0f030504170102090a150201091a01050907020d0c0f1103150a05060a06020712030504030b0906 74
    0x42c400d401c009005585610140e040101c0c2603001804030b0700030b90400720300b42e450034000034020908040121082000100d003c01c03509444064507104920960358002005ca5212081d81ea1024078466442040440b080034480ca04043d10303041412011801262041001aa10b0420400014504c1c0b80002c0da41d10f0304103d0391510311a07000055000303003030040005055803148050304000c1010300303003400250113640d02000303110349035070b00c403c4c1c0c02104064240a8030f25008100d60722900c10511003031082003182584480620803a4030000000301070740c0d1124034090314045110300115516055550310b001c02404100c3c020f003182c014030094805e03201658144810417440c044054100d07011588142c0e41c011002e034100f0185c20145030000c03040b9a20704d00c1c81c6010841c100f14040206d401d8024900f0540f031380000c407801c140c094405400c0620140d916074050040440080c460035005a00413001004500f04e0043c0d00442a406860194941504d9848280b10f00c50299a8407015034040b404100c808 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 551638705 1250 551637455 551637461
    0xe01200a03030c030e060f1503030313021003230c19050d061505071e08120a0615090b0c0304030602070c0312030b061206192c01060212030c0f120109 66
    0xd00d160382410003254445c403070129643c10b001024812124a0540401c50858491022040c140b0b4010222592441d0100f840055449800740072402440038078014518907001e80030304101e10880e9840400400003e16100c1020800a0300800000004000050801d000a40420000b820540300c2c160b40d1410032451400f259202e41c0008144087d000c0c4d04094250311000312404660000c40000110321044982c00d0b4280d2000c1c0002d01c1004005501102c80c41028030441c0314808402c1d0404c081c45c0e0311001240100c101c0392019002901404003445030035044400f03401a060544216802c203500d95803541d08a80c07103d60261241e81d0f40e103000f0010040142890b40070b0040d00d00c5c060180c00040004101140244814034010584c042c00141c80d903180e40c1002080500c81038502d448580d82e0303110b034504d0100140401e50300b078580180b822a0800228140314101d03038055000301030a4100860149150308041e01e09090000c1c1001500030728110200901489100b02042c4040d6500d04500c607011 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 551639955 1250 551638705 551638721
    0x30209120d05040f090c020705061c09140d0c02030c011803021804170c1207030e0d0b0702240a0c050d0504081c0e0604110a0b0301080a1205040e070e01200a0303 71
    0x204a0a001103070040c198081a030230100c4005480303894898054100452794510801091800503191a004205001e03500d540c85540300c2100c005d90b2404042c0010849030203415000103074056000c4120140d042d48105c00c0003410207001c1c81c00006040d16071740047d01d1002c940ca181040c840c1440c040c00180908401d440c0c10b403008401900785003002c10f080180c0c4074801c814a068a02c4004592641814001d407541c0004000017807000c2070b400800e145c418104101a92048018071030302d09001a05079000d80300c90ba0850b142040060729030303079000c0001c01400c0c64508100401505000d85034103076010740503581c05544107802490300d40c0d003121200e212869a52008802c001d00303112a0700340f030382d0740410015003068002111140f0442c00f600820101d91183c0d00807c80c014002000084d500c0001c00e0085c130445c880c04403c514440190000c1320140070703600400d004150b040001c580514011b1800c2409040107042402c2c04042c0d200c580e0803442d10503114200786401c91105001010381c11b2240b000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 551641205 1250 551639955 551639969
    0x30405010f0e061306020a140a12110405010c062a0504060806010f0507060b01020f0a05030c1203010509240901090e060a060f060302031b040b04030308010e04030f030209120d05040f 80
    0x9203914084c14001c9840c0049100500b26039030000c0c0282180f845580070708d1549a1251480c1d6076100820002400c0900d420117502ca0907181500f030f502c55480d58000ca5048440503510401c1c47e0075070ba242c0c04010030340120742c00c1030101040064038100c0c114070036003031544c50203031a9035031502d1030048094200035005103481c0c10041c400e0030085d6516042002e40d0f2800d60807000c00604480380c20010303803801180050188030b82c46020f442d5410050000700601b00c0251000c01c0d6420800c125021000328002030142e1035001c01300d94005030303160f001c4018000c035880b40e0b4140c0d142e418080c88082648800c081e004240003c1c4c65801c0850383c0c00c070402040740c0020607003c003003010314076141d07070110858014040c060030580c001002c200b42d0300c082c5092201404039115503d40d00d40d55242c000d411903100b444120007045d0351400015156000c40c0d03007184110340680350600e140042c107008030000e50102d160f86d940301c0541c0000000c1c098040102243c00d111540300e26039264200105009a04c1c19940400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 551642455 1250 551641205 551641213
    0x1603060b011e0c0c030b010803040602070509091504050111030406060608090a05030a1404050604080304050a0902041a03060402070507090c0e030118030818030a0503010303090b130b090a050402030405010f0e 91
    0x2c440e003198902060754901c02890041061442c1d07142a403244d41c0150b00242072003c81c0c07400420a14000300081c402c4450f036400310780f040c42d0781d003081c08000c1c1e004035508013403030704214643c1c3c0d40e011014407101d900500c01c00000070524508011042d03181c2060b14140c401980e40c05041c440c0a402c65160703a04400b600006281c101a2945c5d15a540c0c4100100c41c410015122100c2e0300380c2c45507805070307406064014800c6032940c3c2c886040d00e40c4c0f50000c2c854544100000000029581018403c036019910024004900281c540c01408240c0e400030309500e0f007140c2d0804c200b40201e4400c0c0914405040e00320380215480300d407108000c00007041c40e207035244643d01d42003507208080340496500741d5480e4182049050f41e6601100b11036001801003440100340800524840416440b200960581784a80c48441c2860b80760b03509109140036171803c1d881605c2c1044400d10440c041803000d0071040800416481003141c0707540116044e43c1094030210b990760344030100c031000700c0018000c00d000350a07054010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 551643705 1250 551642455 551642477
    0x4030c031202012d0e0a0b040605070c05030d0b01050702040c020f28150e070602010b0109060f0509220f060302130507020316050309090124110c060c030c1603060b01 73
    0x3441c00290103298013004010040c8441090300256000003417048000d500392400d40126040c401c1c40a28100c80407942580f4003400260804c0c0500701303640e21950030100031400d14000d03401c0300e0014055050394038140300040c0302000c016030740c50040e504100c04641c0942402030203001d200745005c202c884070084884041200d2540b1241c0b0344000e203c1c140c1c0049101d03080440e0401840010502c40e080840d190141c844045402da40540218510103020f0740c400e03a90356505c0030122030030020140c1c0480003642c20042441030b481c064180340c41c403409450409103001c01c445545030485024252803481a5250401041940b900d054200c02030342c0c1900c400d100c0c0346002d4038020f44a01c92550217039658413061202d001448010000c3d143c030a840903000110340d584520503100e000c40001d1442d00303090169107050b100d043c403400488420302c58a10040c0f1110340004100700c03003600031601c2c207185888240b01c01400030300c040000001c1c4444421021003080e04508000f01500c01140c0c00c07905010341d071400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 551644955 1250 551643705 551643731
    0x90307021512010803070308060d0c12141c110703030c1b08030a2f060c091305010e01051504030b040f081201062f03040911040b04030c03120201 64
    0x4451846904031051200040c0d03101080606000b030500b00410190350b040081a503110003c001d044090007900e5a8580380d49960800075940c0310010005c003098003000c0d00b0000d8401844440c0401440b412615a15090764400300b803a10794032800d803a0040d40401d002c0060039401600044003d00040c0241960b5170464501800301450420700516203880450080806491015054060180389060300ea95504809000740a0f00c0580e4098840c6003401e450300c5490000c000500c920603071110701400540c0d0311451100c03242e8026840154110040c0d00820107008c500e4030445020740070484c5420300550524041c0000b512004c07034081001c180030402840031400e98107150707601607489062941042e070306191254003409522050034400441d50000319811b608a40000300c0350800c00103409000d0014042402124003455035108140c20410040c05080c24903000342d100304150310199841c0c02c0c0d56040d041c060790b102d40c2c410759a8070a100818410000f029010140c0d49a5910003032040283d9412 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 551646205 1250 551644955 551644957
    0x11103150a03050607050c03220f0b03090606060f071a040b0f040305090f0604031202010b12070506040b090a0f060513060905030d180503031c0b01050307050f030403141605070b030903 81
    0x1040086c040701180d80516000100200e0780c00c007900004007a08030790884a00f003141c0c8501d001c0c4020100118101040140550007079a100e01041c80081109881c5c09081c000c04d40d11410418001e04410000e840109881c0c00404d00c002e407042c01a280b542c0745c103050600310303800007512841406000406101c04254003000b60747d5080c00407a107008030078204400291710f505c101e500c000d2900d04429481c90705141c06500c5200c80720820340e0b248a0b424420514140c9400d21400f41940c0200207100900c1100180c40242c07850a2001d8900d680c0c00d80c403181c1c000f08248140e8460b40c0007072000140341d4080400307542407030010702041c2003c2900c01d04110011351245114440c660070030214400ba44801c007800700c003801c01484007a0940365220250000004020001511007003c135040268403001e55100d102164400c4482c0e0352410309100b44c040c0d1000c8541d0000d04144c042004407968000801050b0008203219003085241110740e100328504a805c0c264250711200c00e8140034010484044000300c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 551647455 1250 551646205 551646211
    0x120b0718060e0102030403140d0f0f121a03011d0c0d0215071b29040830190305161b1406010308040f0801060b090607030c05011103150a030506 63
    0x30602aa4482c500c400407491400340341c2c400f038003c501968640000300e10100340f8141903151035071000e100c2280e9900690f4100020f02080c000150410300150468481c0e501c8403442d400148240e411188440002900b99501d00003402e0241c2034181c698204640200310705240d4640569107040c44030000d0300000e614800030074040c1e512400000d503040c01c001c488040f07491014008030912800a468282c00e50009080d01504014032143d0b00c1541201c1c40400240d40403070306507c1c0103014601c850b101c84c280c42d00c00310210710380c041e03401220459250106006440c0081c1000210100c1c8000246c00034207031b03080070301100c101c041a0310072071404950260303618444008659804500d8400d516100d003a408041c0904945401100004010494150014812140f00c0c4503181800c0340c071909030700d0807035240d44140c0d00c6607a030410080c181410f03d000504040d9029080405400c03036070b0f88440d409c4d41d0700031030300b904c2c400000400c00018485410191410307100507035500e140d41d401e40d5141f5540311006 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 551648705 1250 551647455 551647457
    0xf11030f071407090b01090b031603090302070e0708040c050909060103120c0c0b0304030908030a0c030f050f0703030902090a1a0609310c0c0503160813120b071806 72
    0x1039040a0040141c81c0780b12560640088641284d901c406a900030300b0046034090000d207059400281c2101d001c02070f2030180c600c40c282070302c0e04603141005400520302d12004409600501030300203000400d41010030311581054071107000510f040d2400203071480c03030750704403510800180c003e01c103a07070b06c1c0018801c0c1941c2d4425414023603494185029100081c890400a02c00c101b58200459000448000b860185109441d05060541c95480c1c203a124010940c40500083c083e01214000ca4032410100700316005c94203142c1e00c1c00c131158466140641c00400140c010070740305c805407411400e0010080d43e001100b038800300000c0c00401e0901500988540e0703014420403021030701540c90341c2c0713185010041c48886030b44144100011010a03104228442c18502800c0c64910320403800781c0581d440000c8290700501a610302800c0c54504061296100e0050312206010300001222081c4c2002d0b9001400c800500c4d00740a9a5900d0081c00055005115038108800503e404605484210f010700a0f00c4003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 551649955 1250 551648705 551648707
    0x6080319050c0106030302030702031b151c06240302091309022b060605010f0e01080901060b18240702060c0a080f04052806030b1c03020601060f11030f 67
    0x98003004886900580710422115440c005000042540000c0102002ca109a0941d8802074490200d0301052103802c0740d89801c1898000301c100c00e000f01c2d000500010404c45071100e034007044224154229032164005a03450702c10b0325a00400035100954010381c845081c54150315145c1a04080b03030180d182030b00d10422207078940c44c50104550303607845c0172840000005c000381d84c26080f080052034240300ba100d007580e10616004000c0340c9075102d04500401d404089c1c4488500042030001103a14000060450754695a00c000205180d0030010013015035601c40b080c00c0a10603031200c104401010b00d901050307034048620500713914411090041c0c03090350740c041b5145030701c0b42c83c0390f00828104200d199008008400010700121601c5100c1d0160050328001d4a41e070f1031a641000200840c15007032468103140c0c2541d08000c00c6800d220b0340106845000c007603c0200c1d02c1190031251f1b51040c2d007001c1c1c2100560052801403010343d60103030a80400e1402482e01d0400e245c00142d9440d103e1244501c1d444081074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 551651205 1250 551649955 551649997
    0xb04050c1f050702041409060f01090b03060c031f15111504030c0510060303051c05250201061715070c0f0b0a090b0f04030e010c02010503061c2013060803 68
    0x1469501580e130040100c5c09068847c6040a4559101c40c0c08660703101d0108000000420034640e24468400c0c00c0340058001e00c0c582d00e481c454207035103400c000c0000b40f04903181034681108455204d80c08004150f10f2000c4040b00000741c1c0c000d0980e40e200ca14418507680002040c2c4440c0c000f0039007082c0c01c03c0d01800c01d400710740c2440c2021820000301002010202c0c1c00c4c03100010406034080010500050100e02c4201ca0400e85100b40b02511010b49160070700740500d44d840031400341e04c130000840301c0f406030000060290f6110180450100c9517070b42c50010741c00c440910100201d64145081d486181480c0034000455036560b8920400c13200315025108050407400a0090b8400d0fa020007080354000100741610b240c40502101071810441c1c003100010310812102d0059409000034141060b416100e6505564500d03041c84144c045004241c4054400d2040c16130105940c540f10b80880e900d00c40300110100307045400e120000340301d808090b000d149401000c0240b2400030080c0d480b000b00e043c4950a1180d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 551652455 1250 551651205 551651209
    0x2150a0e060f180303130501110306100e191202090604060501020a030c0c090e0f01060602030a09050609150307110114011508070e12010b04110c031e070f0b04050c1f050702 76
    0x90080d0403c00385512000042c40850382803806590a8a0710401c000e100c521101200700c0726602043c0c500c4c1e500400c2c61441800d026002d02c8009030300d258040e091000c1c10014100100200256901075854511424028030960421180a43c1d001009850a0011602d800d00003590380c150960007074200300b050b110700d10401c294890b840c002002d00c0780081c400302d00030030b0380d03035449024814440f80c8640c80d01c10b000407501d002005449008085849002c40107140400f0300540e9407201c1c83c000d40c80000402d13402c000e000950040e40c050046540c500d000e5204182c4c515084600800091600e1801800104203129141a02d045000ca10b842c2c85241511006000c0c0d5100718003207200d80d44071001c181c1d0380c00700010551100070303004400c4800b8444400560006286481032103035001050b04204224081000c00307490300342c0700841c00d541c62842c09010340c440b19a0960700306030440b0311403005030a00c4180041008083d5000c413080343c103007140520002d00d400025a80d480080c080c42408907855040d5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 551653705 1250 551652455 551652481
    0x2190302012c1e18010f0501030c0333060e090429190c05130902070203070b120109140708040201033216140d02030a020903010c02150a0e060f 63
    0x245000342c0b40c500100c004180c540c007003c10060155000e2a81c0c0044402003000c0d01d01c501d03049400c403a03d0040c035603040000460282c80150469010305880b02100300400d401402106d0521401d900c1d60101c040d245d0001011001d0a5400003042281e0310031104842c0d82c840510641142e400744108104080d81580c0c8648880c45200750b90904001404000b61b03850384035460046011100c4080003007440038a4140e0b514011610060200380051030140030002083e801085514001403c0300c00300380c0eaa03030209819501c810000040e9402c81c2004210070030007401900b0381d941d2200511081458074400c010444c40008002904040c0c0f600b20181d0a240c80d580f04110141040d008281c16074424000210004d4040d210441d45c030f02070710fa0001d0750314400ca40548698016100c03040c0752a100746c2005010350001f508000d2160382c00c0052105c7d55a007440707802d101d01c6983c2c0141c81d034441e0103011024100002024929040c0c10070110725540140820800c0c0d00003200103020450361a58508120f0b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 551654955 1250 551653705 551653787
    0x803040b1b0d110105130c090e030f0301030303020409050114130c03111305030601050f060307030f0609020d0516110a0b0a020d020433050a05071406070302070219030201 75
    0x42c042c66400c010850ba10000781481c10449038001e10543d2105250303980001d4030000c000e09520240c90060000c400c40f604214001d40780141202d080940c5030200d01d54070350003a441140400d81c0000d0810030402c441c020b940c0140304404204403000c0900001c036411095000700e50800b00d03601c0c0c0c0f091b656540030380c1c030888001c43d603030b00500d403a0706030401040e51400144c001e2502c64480c0000024031072070300100020561038007620306800c60301c8251080c0c010300740105405c11050348480d03010031194181d00c0580303680b0301c42800100f81ca0600300b04003800c0c054141c0c030103800c000b180048400c0da4540003800d803422a1340000c03021055510080301c4002802803680c040c810900000740019003800d40c60f00e6130b001c54a100a0b0030303004a0550707034030307412078840848440101d60184030f40d0200034040c2010b00101d5000300c02c0c0644000180f800281494002c072800c001190740030801d4010b504060152160800c0b5080d00201102e05540001c2c0050340c501046807149840c140101b000742d0719080100c11 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 551656205 1250 551654955 551655007
    0x11a13030b0703090512090312070303060b190f030e03191b111008090d08040201020c0a0f091503110607021f021e0105070806190b0d090212070803040b 67
    0x5030398100004014054451310500340c4444c841d0002c010301c8040900111800070380c0c0200140242d8411150182850304440020b406041d0344000000d50550b0300001820040801101a42444206803020b401d080c4c4032440681003501d410080c0300c241c0360000c100d50986452142070102400f645004490300c0c1100310780394100c0c181600c0d01b002001410500b50766070420448030001d5100701554120341032981100c00d04099480035080f004060f0143c01c0c4250000d0044c03043d6440d102e90303400401d55038445030b884519004450030b01048456654402c010f00d003c40440e40c85030017440e503100c003400700c8060014540b01d000009056011507885415040c00400902d02d6103034070300034100020f5220403c0403d1485450721510420005c03001c107120341d034070848190312001e40702e031603a6003030001030705204c2c5c0c8501c103c0040c4c00012038107480030300140001c1490388a0204216140384140028810025a900320550000c042840000404000d407000c0c5d814083d540c6440d11001804c030301c11030705090410a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 551657455 1250 551656205 551656223
    0x8090c0310020a020c090705030105041107020301090c091b27150c0209060109031a0403050d1a0a05062505010b10050a030501240c0f05191406011a1303 67
    0x194008074141c014000750982074080c1c0c0d05104a50046c8206d22408944034800180c00f0070041c4560b14142e84800200b1b680c0403c03513030420103207502007401c413850520280c4600a403110f0401188859004d0030140d0803040008140405418001034003c140101a0744903842518480c0342a24a8110700c1d44001d03c900e54078041da0341c004560140451022180c164090511000000c68950245d141001103960091046801d001590661100207001800440410904101800c00c034000c0703002e0309141180d40b1901e010301d000d800042041c1c02949500050243c40c0501a02b010340c580304088040c0303e154840c0002c801d4985190280c01056040741e0207500845840031650601d03400300140182140300e031010006643c80340c1504201400840d1214202038803007458022840c806d14035409003611586480d56000180d9507090b0078682c41076000d15030341760308204030014007030f0020300e50480f03a000102603c100c3d414054003001c1c1079042050302d0030319480004c450711400010308587c00215000340e01c503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 551658705 1250 551657455 551657473
    0x10c11030a0f0f0b100b09091e1005030c1801030f1a0c0a020c120d0e1f03020c1e070302010c020d060e03180405010b042601020304230a0506060108090c03 68
    0x161500141c1c10a83d80c2d2a21500000d1205c00a2801d010a440b1281852824014a04104066220001d02201e100340d0403051840c0006000c1184034010301c00703040c0d010386203420030040c98078000c550041544641038039031004d03102c8680c080c100c41c19250403a08803c4c69030400d0601d03960f0100703201101c00e40c945070b00c401c00c02c00054a40c003501c020000c07130b429038a465140d6010005002c29841c100110350b00304000b51803105010b450b1540b403800c030180c400c4030101e4000c00c81d00c820420400c2c0390004290001169039a016040c4600302030340441c901c20b90390b416061043d0665414031401300a06002e403505c1d480041d541c0360312058040c2c9500c1002408800c14960200c0e441e9005000c00440440201d4000221441d107030113034505942c08084081c0c20103150085881008000440840c0c0d0744c503030204420540701d4280000c41c4a903009000500c1d00c005045164400800694071400d01038000c41c40c540000b4401242c1d49420060034a0103403020389440e2521400c02e008055019414480d003c08 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 551659955 1250 551658705 551658713
    0xc2a0f051509070501030606050c060a0f0b06040b0405030d1b06052211010f1115041b09021e030c0901030b01031d0606030d090609090e15041a1005010c11030a0f 71
    0x1e00139a2004c5ea4148180c0c2d40d920815540d0303004864051149800240001d8600200c030341c07050800e03110401c0041162000d4601013501544a60450050300c1000a030500942c2001c0046503100d0030a0302e03101030550f484036130210507240d80540042c900354075100450142400304039585008190700305100c503000410b10300100d411014005031404240c2c084c03c0880254010255801c01081c2c01018024540122011208522000307204581c855074003011502201d0b040c1565a029200c16075006a460444000711001d203205501400ca001f45c08000300328440400c0030580780c2c85802070a000c074803025400016406003144401f50760310068003400e040f00440000504d030b03006040c198240d8580c00031000080780c401035135004c0d010100b403c4000400641005610552911005000750303040500800641940c04c2401c0e42c2c01d803168240300d5600314003c00168034050308240b03610b68450300c161500001074074007400d0707d50281960246401c0640503480900c01240301c15032046a0810140013450 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 551661205 1250 551659955 551659963
    0xa020706050a0507120e0304061803060c0206100504090809040b01090b1318050615031312050c0c090615090a030b0109020a09080105042f1002010c2a0f051509 70
    0x6a40384c0040e4420100f000d00d500f0350300c204003070307500400059880d290602d42c040e644001d0b001c080e074a03210011200000407400a116400100c0341d01e0780904000c0c2003c1e80220280c0b592500b0091060346403503404030009100d80200d50f40e8110644000c11003441210060790010025409140c600d0000903a4034a4403001136100003d0341d030200d10700c00c0d100601c0e045140c1110404c0700e03520380080746200541d4080e140040615801440030310005a00da01c81c0d960445c0c01a07001405802107800402d103918559414040c41d03002d41003e46d080f02d614580b180c00200442c18903a2501161600015400d881c3e448031985840a9900a550043d965039a421810000e6000d80d442c0000940950804a920041802002e000c2c0e504582e580062000c0c1d0010050f01804c0c0d039081c04e000001c1400c1070140c03921403000b2004202055000040c4851180ca00601000b40e056501920600344044032503504070071002d165001600880d41101089032072405038a8190f05881d1548511142c9040080c1400002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 551662455 1250 551661205 551661211
    0xf0c090307060206010f0b030f0103021c061a0108012312071a03010302010809030c03040303080a090b2701020913020a090f03110f01030603020102060a0c1b05010f060e010503070306050a020706050a05 88
    0x1405544215941c00e00343d10180010f540707007078049c1150710041001d884c11110b20200258011803c0c040784559503110008c403801800d01c01d541c13800413409003a0b2980c11888040c01000300382003107512120790380d480364000080d90081e5481000007460003110b6410403c18200942207049072030380c444d46c0e40860038601d84c10910080340040d088500181c0d2000001c81503070741d0328107164015800c080c215541504e48030802864039500e0b030f03a6004407802041012485138007610b50448003400d5184075641c2052007444403d4140440e07070040002614a8641141404c2d000d10b031041c0c0180c40340ca10f80000c40b0b080d00c55510050364075001f40d80100070300c1144240c010800c04100c03601750035812210010b5003036881c0c5120182c050380010001940b810039a401504605d105031a080c2d060820103100401c85452400095070b0580d0355000d55110141d052064a003d0284031b0f860300304c41e600d0007000954680d00d600006013003948403408960025060780644840c9548040140030078604110f05c4c10003400300b2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 551663705 1250 551662455 551662469
    0xc0f070320070e091b0a1505070f06051609050a05010e0a03061d0c0108060904290114090906040c060507060b0418020306070e0a171009030201150803040e0f0c09030706020601 77
    0x2ea2405e00e03001200c089004114038050408208a460051000302c6208032001d00018040200b200a0014450781003140c0e100340310351000038043c00c01500d1010400d00e9490207a091100811090000343e540c1e44042040f07540901e13150004403050300228020004607800103111f1420091040309045200c610002c0c04002c1d0812130720030210310401141d105c0d900303440583d00b040740b010115003c1425851403054101407543c0c2e816560419000d0907910300400d0340160150154601001c0d1a0310f0700455403604024028001d00f418149030705c503624500001c0c403d007414040001003070810400190441001400c000740104143c51070301c03c0481c022540c9810892007400f84100240c8054041c2e101d09541c4900078050040c00c82c01c008041c01e40e80700d83c00c2464024482c1c0240081505858060300c8061807013640040345000000300c8144504d100b0360000702e8660400e0206010399034007215801d070b1142d84144e01c50240c4e140c0c024081d1441c4030b29491035805004000011502c16000281f03a8126041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 551664955 1250 551663705 551663713
    0x501020309071a1e0c011409030310120515040318080d0f17010302041e090c05031509060f130b09070609051e0409030905120709050c0f070320070e09 66
    0x1c0e4520000780d0b1191100003a00104c107465010b010b40409400350111702c031134400026107011000300c0daa122a034119a0b00e0341d10780c40001000102001000510000c100d018040304180106981c1c50f42c440c080b413007940c4c408040c500300013802e2501c01c0d40d007141c140b43c4142000d01920340f03940c9441d448441c508103a2001c918070301c071008003162140042070301d078a510186100300c6900719800c00018101154600390500441c4402c107080a800d48602000303680300701000c00009240174203060801c0c0340d418600f44000038040402018034008a8210351107003982e01c48020310740d00d29001440d000325072100039168070511000c01c1030340000000d405054035850389403074926903980c0040040410300350040d4100302044404032052400d00750800542540720b07080141c032031034851000c5002c000c1031008014296011003420480310803103209403a040511485603a140180b9070340380342240d1150b100d00400f0001404a000116060400c00004c82d0f038420003603581c0c40d0307a291112910041c003a213a039001400b07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 551666205 1250 551664955 551664989
    0x140f06040b0117070807120f0e0f150106080a02160506090c04050c071407170a120f08011202031c030204030606140a29040909050c09010b09060703020a050102030907 73
    0x2c083d0144504100720b001420b1070542d00c66104603044000603142409102400a082030800028044e060504842c6000007420101441c1220300c0c0c1400955003d084d600b000d4480001c0824190441c0d05503486810030f405a0344403081c2c514000c0c803070b1039000c0201c1d1488145d4101003000101c0c00341d01801c50001120868a2000c080200301c0788140d901c080c0c19801000842d002410640c80013000f5107046041d1130645560300c0c00d11210124005456440f50421903195040094002c11030005540e14034181001030070030316018000d40302c180144150046038015030011550200800c10300f011480180001080030f4030701c0540690020f0008440090400001082d40400704001c05060080204400581850b003104841c000b010880e020041000c0403240c44150b61a000c02800144803004001070700c040300341415800d046400c0200ca2042d00a0001001410302c060142c40c209501201c190383d44281c2840c050b440e004221390002d240d94008810484298004941d2400b1034541e0758a4404480f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 551667455 1250 551666205 551666207
    0x2f04030b0c1b010606020718320a1b1101020c0109060515090408031f08060405150c0324043e0a05070b18030d060603061a040e0a140f06040b01 63
    0x2e1031500035900181d01c403840402144542c400311a84009000800003140900d0015160b010900c4090108000715034800039101c140c03d10f540345512070402d03101008503445003218000c00004070400c103001c02c240005c0504553312f00703504031904078181d0402004a00d000345001800781000319940d0641b50010b1940d04002d08240038407503c10b56000f40824695603501440960301202c28655403021900c4480116501804100b02401580140020240d02004030191034100704010f241030300d0f40e1014824040b1002070605001c41410703581100c01008002c142c00319000b001e00241c000c1d400c015151140c10594090301e0090346403044612401940e08424000c109a40308645802000401c100030003400300f5071094520750000d0990160031050b4000010032407440e0850496418295500c0c0350800405400d07215620041c02030f402c013100741c1c4444025000c401d0003244140258030092100046040c2180e030b02141e03400d01c88110340b000c80d08000b140300244110440e40c5500036841e00c00c10311059 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 551668705 1250 551667455 551667461
    0xf0d09060e0906041d0a0317220f03020c150d0c02070506040b07051002030405060702061501021f0e150403020c0904020f010c060912020d02102f04030b0c1b01 70
    0x31400252801c40151640004d0000501030880c820b4110405070580e0b0180740028808200b0950195850415202c035194005038000005800307948100750000122660702405400700c000250024100c103256885401e060781003040003c8080c5d03100313141658941500b00e140c4050712559104000c100491040004180d0360b80113107000b02c1d40d01c040144410032074032090200900e9900d200c1e505403010a0385903c1484103a81040c1e0f0221010342200c0308000036160304102d10740d88a0b502003842410168041b0011752a44a210011594855900318004628a4503000600401e400200b01c03507143c4a00321011040100c2070f50101d0040c0140c028150151500c002c0e018040c940040095421807040801541c860307104031822610582c5a2032a1401b0459035204150851980c1c0c002d404466500180281881581f0014801d0f6070f00e00440e0440c43c13100c0e204103d01c0ca040304103e4202e10511b9642c04500d038012680000d14a0034150204280201058064846e14030345842d4040400070940005084e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 551669955 1250 551668705 551668727
    0x90e0112140316080706020c030a08090c1f12090209070207031b050f040b04090c080601090b060304051e0a0f1112190b100e0a060618060c030807030e0f0d0906 70
    0x841c2c00702c10020f004202443d0040410602c2404014580b80c3e007280e025007990403006c221004680503070100003400c501400854800f0b01c0840c0e050030710700c0300b00d481800e10b4010080a0300800c108008070b102241070560000c500d05800400715040d602c2e0007800255999101c1c001120258201172400c0e480e5880092482c0640340010080485801c1200511009051400050780e006403503980c0c500106989001c448050058500030b00350035070414461400352510141650f000b803204100b04004588c0110f980850151200c000e4001d5400c100986480c0203210440684001d0303004000070104400c00d6004070910b032059034034001444803060103680301c004801c9400b80c0341c07401150640008070f200d603126a12400c540b0b402d29203151500100600c3c01c004407100701140380e5a000a005080d00140141303590294008654007003400c00744003e181c410400b0005050000c00340c0841c0d440740c017071f8100305410803140c8122801c20303c240700709658420040c12404041601c0040c0881e07020f2060540c016 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 551671205 1250 551669955 551669977
    0x50108010e0f0403030f0509010b0928020f040b21180d0e04021902010603020f0d0203070b0304080702060a0f080609101406041d01140d021503040201090e01121403 72
    0x4440d64944030007400b502c0000303008804050350b55103820700320320052040c14003400642000003450150a0240010004c024180f0300708207110303842030000010b5a03164043c06d2944101d000d80c0354001d20b1409010b074080d030740004155520114541050050100518010800c0465171b030f021520340715440c070b40d42d800760200154030340c2010030415801d40c056070340d81e0700e0031384003810051504520000203011804500c4000006035140c09040007580790422070100c85c048101c4420f1414860350740042d44d43e140610401e406084048000360070701c10030200b681c03003140d00580002c1d5501c9150000500c1080300411490115214102160003418000f03911440303807032903443d0300c103015003411800b5059400c40c08440d64426810000030a441040d04032400d03805401c00c12000760365040c1428405492040c02e0300c3c80c0658024450000960f0b81c2d6041483d800d076000c1640750341d98485000484610701280c01c041c103002d56900001a1000c0f001150500046c02a900742c051031f00c0142a40c2d4603440350030312000f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 551672455 1250 551671205 551671229
    0x30c020105031003120504170d32031005042405150c160501110d0509010503041e08030714070b01140a0806100302040b0609220e0111030603010605010801 68
    0x400154000c40c01190890b46000000d00f649940342c1e034100c00d4850303a8880800241c400708081082c6409030418035459204c1d2000741040520300c810081c0820010300e204824001c00c003c03005003a000e100079000101840d1196aa642d1400542e0303141c88003442c0c85010b000340d1500c050740c400d0724000300d60041b0301100340304403c5800d49403104112181d10540c0444840785802c21550100c00d50800007200300401150010050f1840d01c2c0004d0441a10010702c038400750810070b04420b103a50f121045424291007403c19035180c0e100d609121608004000c0030804018156503000e09001040340a140710f4400b9680b11034511300481c0c0442841d01940c40d008201000c03240c01800f410105501080810001030a01c1c98510b9507040607601d048401d864000c07190081c51b0303081c815400c0c039014000c4802c200340c0710305140c9504900416400b13800d04a0582402c01c0c00c0c43c1007200440d01f03401220020443e1002803000c0c446842c890708140d88140c400a01c03d61804000186e5135000c0e400d5a4101e0f4600d100e40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 551673705 1250 551672455 551672477
    0x3150513080a020f06040c1401020307050a080f190206270c060a1806081506030c090f03010e0f060f0a180602030619030305030708070315090209030a060222090903 72
    0xd55507500000b101d042076000f0754880c042d50b090104141442240207441010b18103183ca0440c0700311080322407803141150070130042c0001080b80015203113421030f8002c0d0880e507904001800c00e00039002d00d019143d10300b0740c640e89032a12281d0020f45c41e07029060030050f03110304100c15184134590111307110380401c003508006106482031400c80060300942180381007e114420009a40190381030b0507402a001042d246801d015908850410908040c1c0d4280c600c24a135040001c03c4815902032803441e14480d1094946d8036036140c6080d0003001c04446124120356406003404081c41d01c0b10703000c5417007001c6c0c44000700c00070304080d80e540550700c5803194042c01c40c500b0494545071031f030103548001d00c9141c0108002c0c10f1641c510407002103900045000c0e9540b65240c0c20804801060540064080010107003003513010800e079256001a241181c0360728400503039405580000c2400c00405403c0a0041d45c80270030150550301803201c034841c902d04a008071010881d203841440085035441180030f80050948010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 551674955 1250 551673705 551673713
    0x5180607120f09020603180105010603140f04050a050102030a0c030b060a050306060f1306050301030317040209060f0102070806070503070f090e0f040204090606030305090102010c020127140304030c03150513 91
    0x4014800381c8510b0200d280082038002c00e0b12035000b950f2141c40c0309860548520b0741182840383e1809001d440c6402d0255094a0726203040c08400038243c0d04508940340c0c003040c100002081200c49040e03020f0001d6441c2e19010100c0d400801c0c42a2400020a00b080614555464810b088a405240035100e00d421038540806014481d002822581400b800030481c20858140401c040e1005207040d0b41c13010768960551400900c204000300c8640b400c40d14503c180300060b5500341a6a9000d90300350350075482d00950342c004034941045a03000c00c0340c41c010310050041ca135074494000e601c10009502e5140c24141c00b10000c66400d190783c41480c80c10b004c128003242c0f010041c881c1158120340010008102c400e0941c44034411140e26601c205c01280b03000540701d0441d41c085c0503658080899000800042982d01070b80b0004410a4004051602c040c4040104101d152000c03130b0ba03102c01d0b02e0212a102e5807640f4043e01e51880ca40426200740c01e81d158441d100102c40c0c0650740c41003c0e003107a0720b92403031269a1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 551676205 1250 551674955 551674961
    0x6010c12050c0c010509310204030c03021309020a0b0d140f06010917062404020a020105010f090c050306120307051b011409220f1806200f031015030518060712 70
    0x1507001c0b284402c11f0140d552488040c00075101950007440360440442c61803042102402d00851801d0361503041c03290340c170b000d45c1e100c00c0c3c030350200c44c4207550382a580c0b0160140c0500414019400300a1200820144000600514003d074855003017a03d0744e18001d500c81c1e22650402c9545102c401490f40400c0001e580c11866900801002e00e89085207034420500500080681c4c1000925100503076460300100315005400b00d104006041594042245c032814440c018914400207141a00138001c00350081c0c40d99104008840007140c10200343d40c400700083d11001c0582c141d40d00c14500141d020300c4060030340380b800d008542200701d00034940f007072030920000e40c05003d030000180b5401941c4d480031160110480350080c0c0312280e544818220149540d450903e040b6403608095901a990507040030046044203400c50b4258142150103a446e81d5a030502411005101d030800051198880c06122100350903800c110f0040200038501c07a8a0300780038060550b2090304944038400a48050042d1811030a668 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 551677455 1250 551676205 551676259
    0xc070924090c0e010e01051213021f030e061e040302070b0a2a050706110f07120201030e060c0405060d0e12091503010e0f06010c12050c0c010509 64
    0xa556840c0204080c200e056410340680c0440c2600d0780301c1ca400d44920741d000900f4403040009090640b90320440b007000901601480c2c4035141c000801c05d011030040900c80c0c8100389150b50060420391515415907426290300480f0003d03402280c14002804402a80455010b100742040c80c810100c3c1d04110100d04503028000d0700a505501504401103030145254004100c0c044460312009441e034075042003113415040840b80d0154400103032131010001900807440d0401c5607081d160048034048100b01c1c00341050b13004040560b01f8403490310001a100b114401944074036000b602c00f08060844204040d460301800c0300e061120130b038100000d002c0b524020b405050046008500090040801804140340034070300444031488079400303e50806a49480c4040519803480a02a24290b503d00700080b0145480581000f4090441c08001107290f40700b40c401c4002d00b9003003544000241d024480107040f41d40f0003d4602000d00603500c085801354041c0c02254000c0c4c4014108130350308e02c2284031840c072803810fa07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 551678705 1250 551677455 551677481
    0x40201031401030b011409100e09120324090402031f0213120c1d19090b0f220f0f0309050d14010507030506030c011101020d020d1b02030c0709 63
    0x141c1a0380580703010303a212003806540b10302020615541000400240280303000840c0b40700d48110301c20440002908021801258802e408012103502c4560485050004419104240a20200411841c01454420306415080003005500f48001d140c083c041030203000c580207901a442840f1018040303092405000111308141c1d07006003401003d250622210803103601c407101c03030500015100240030703240844400600b071190383c191080c1501000c807a050000109041604140f002c6200581c94540e003060107205c3c5e100303128030701d1031078156400700360030009440b094882014003d00c100c0002050a000c40441c1d00f00304012041103180d80d42808083e0001c200f1002c0050f8441c002031141c0f07400c0321080c10380b0b121700304180300801c01403081740c01c40e04001d040360101410641804440e4801003007072511480c0a2806100c15055650b5160180c0f0841800c065410f02c0002c094529924962160300b0240c1603140b060085140c602d400c83c2d49024051610030f141d0040f020400c60f000b11907020710403443e00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 551679955 1250 551678705 551678711
    0x50a020f01121d060a0e0604080304020613060824030a020402160b2e030c0603020d0b0a1202040b0d03091502070b07030f1806080c0c01060b1b07060c080304060504020103 75
    0x21035030b40c1c01e0a50b0120007440c1080008507100c1e8079a010b050003403d9001110010030010351102075610365071804040d101230300382d000010100c3c055403a80350844d412041d03105901560943d031460000d0940000703c9001e41d40c1d0f10107801c00180d00404c0281045003000060007000003130016020480258012050028090404410b0307400044580f000580714441d120401c0c5040c100d284040da28020b0b104440c043d21080c282010b00c00101d40070300701b805650041c074005843d010075440c014001c04800490507406118083c00207045d8003040e02e00d00c98030303100752000d0141c6403a0300d05002c02c02e00001c84c003c003c40d00b00341041c4100990442c1101d030f072428520444003140e983c1d0000840c940e02c409429000151005241ea02c9242c10406049030f500e600c42c490301046180c800e000b041741101070714803034601c00b0009440c00c11040940041000d0a2043c0304d981d980d00845502c00120750003080e040002d03010b0000002010740c025520007110a411610442c80c6a4813944d54100901005104906040c0d03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 551681205 1250 551679955 551679977
    0x11251a07021302130902030705040e040f0209040b06041a100c02010c080a0806090705070312020903070b1209010c090f05060708070f0b09071a070b040305071a070318050a020f01 78
    0x2070303078040c2c2e10b440b0240924010303600c507064500244204080d41003000e04074010024032000603440000c03038040f01c0035079139000190b4035030b407810380500d03099808065070006008003400103010907550780380d0003a141101d0400488614074542d00841d160002016803120407207100c0c0d0103880c0030b44400700849105141a060001a41c0d40b20000d40d0495842da40c0020400010043c0b607003041407802d0b41120480c2045810216640d80c001c140b00045006022802d4012a44d899191000c03c00c1c031020303040b442c0d51345440b019079080c40b01d40c48804035a40503082d803d141341420058040d940b08419511041d1044104c203040400380544c945c41040110b401d41720802c103510200d102c052081400501c20300c001141814182409490000b541e0070160300680721a107100c14464030700046076111079100e0406800e90b07855080544207030040500191109003000c194455104100580d1031080941c0d40701041000070300c2111400800705141c00420740c1d0f214090000141c5003164101d0003101052410b9803a1780 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 551682455 1250 551681205 551681209
    0x180212282d0b0702030c0c04020306030a062406210c051e040f08030915031314010f141605031b0d2406031d0304060c0f020d0311251a0702 61
    0x1c04031043c1c0016040802c1260321858107100019140f10211025030450400000203034450440810080020381e688162421107842172aa207401c2c1000c500c04c03103090a0741c0f0f40c1e010f008142882c3d00b002c003461500b00c00d40c546020070311403010031400c0356842c18240b4a0114240401c16103403101010703070b4003040c04000ce0380c1c00b403444010040c00b03485000e9503c6030404010b00120801800030b214407100d0034802c00020300c1d060b4080c41c282c160002001d4181e05000440785005142e020591118981040090440022440030090091000c1600116000164842221940003d84c0d03401c0c180f803414010b1074081c41880003c0c01045200140003d00000346a55241800b55050101300100c010400e0405c155038040c81424010081d14003c85488440c441803d0340720b11890044009016280c81d441040c041030550703000149030702500d51500c4c5051030501508243c4454006405c620030310074020049907001e18191841d400c01a076060081303040100080583c5407400c1200d074200c9090100ca8056 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 551683705 1250 551682455 551682473
    0x62418060f0b070210090b031b0d0f060e090d080703050618090f0106050f1318060908040e01052706130203010b090a0f0315180212282d 60
    0x60050b050750542ea00900d206214010b9404215082440f050020410000744003001300c5e0b0303021100030796462038603840c0110380d0b905014680104094510348254903000d80d42c5540000259020712106140d1a034030f103a4111717512400000d08074000b0b0360400c00319a101d4001d41240350050b10080503540724245207000340542c154200c84400c0140c4c001d0b45d0780c0340107030828031599003d450141c0c6c0c1d0100501c0f4890202c5d0980700041e44c00b4107615602d204500040550015030f030700c081e900c4171052040f00741a00700039030683c04c14014100c21610560002885140c003007041c401d4024110031a070510910030220700030b650001000541c00ca01c940c03031194124032545c8011406070201c00b4050b5281d88010f0180b04036141941c10569552340080380a10115242c00e1000c00c0312441c80b100441c101030425021107060300386090080d0014440311070140c2065020451107a244036855030984485000c41d4200c0d4207411000b40a429902c1f24029403041c0780a01103d250340707150045030200d840d81681e84040724 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 551684955 1250 551683705 551683709
    0x1180b0a0c020f18010b0309191a010f0612050601020f0d080108060106080906040618061b0e010824031903020f0609031903200c0703062418060f 64
    0x1d141c0a090008500c0d2081c80e00441800a0307401c07084445014040c4881858113004801d0038070030100c005542c860040115195070b211000454114105600d000031207101030070701442c5400006c0c0008500d03420010130f202c089440542d80e103000381002c804401c00030100074041c0e50450144449001403030404120440020965940351200c0350f240c01e8006050007010307081703141001030100c1840f042003070000784a038001da003003000002d4001041034650022140028014a806d0501034a00016250090030717044a144c5500c4003c2c680300010011a4412401c68046410101421004030219101034440d034030660003030103c070402c403800b40c21603100402c03989007100141d105034042481c84c681441080d401c0801200150b08248440c4181c01820708441e450800705940c940082c8a10910309400c071081d040845000c5583d00c580024050301c7d034605007c1661610b0511089080902da1514072699404d204e10403005924146803c540a11a014105000164403040041109603040d018100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 551686205 1250 551684955 551684957
    0x524040b0a06050c0105090c1008073e01060b16081e03010f0b070c05150d1a0f01020715030504020a03060f0207030e0d0b040323040902030a060f1401180b0a 69
    0x40c80780504e8107003e00b5243d0050a0b04140d4110b40149050354541d0b8107024130416160401c131086a41d4110f0494000c40c503e1108810841c00355507240004003004212001003e000821030b90140c400e2034620b00340e60a52103416040c02082241d1245d189161b807900c0555445850b09500c0c00c0c000000c8070680103405000040101c1c0700000401c130005243c400300c001010ac0c4904d807802d090707445c1c035400d00740701503072082c1b501580071886005c2c1c0006180c0c086584403214000d00700007100403401150318450303203d090380e070082000258083d00d035800090780c0302c101c88801c2c058000c0e200302654210301821004e402280c018209910120000c0c00c640a00b203603580c01c071880180c440026080080c16840e508140d03074000c118800c2040301150004e1035130750b07000790103003444403000e08101d003c040d0140c07146080b00603200c00401c001c128890280c00860103031442501c1030201c00c1e1100340b0050b0001c501e1003084580c002c60aa5001a075000340b049907960034100a003600c00da5628240b20000764405c0005030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 551687455 1250 551686205 551686207
    0x130b0a140a080a0c050d0f0f1104050903041a0c0c130c020607030e0d0311130603140a0e030d052805060a0e15060d060f0b0c0d030524040b0a0605 64
    0x181c140707000d81500504400740206142e0909464400004540c3d0203424068a04003901c40e051050195580c070b00c0e00e90100140a00141300c0c14107a0804891404980c8194140340c045000e4a03800001e40e000d917000316040140461001554071826807010600d00200d0207044c13142e120039590342c440c202055840c414040340700401c42030700a0038990010070b440181407070281c0003600010700140b270703501180c61070900148051100d02007504c14001e003015509140342d15080462883d80c1500300410145040c40200d15680702c1514003800d450440c01e801905a0040c000c1d01e44140e0301d60000341d0000310940300b6210b05410441c40c01e1a079a064046101c0f03050310f40003072044904001c02808010080360504207828203001c040355003540c08200119100e42c50104002203880780c03030f44c0440000c01101102d4245142e951925140682200a9941490240c1c118050794240a8000c0320311079013051f01c0c003856201010141d0001002040e21550700a507440c2030030112030b214101030001a108a8a9071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 551688705 1250 551687455 551687489
    0x51e03010b0d0501060f09050f0a23090a0b090f18070609141225170106050909030a0c03110312070e100c120c080c07030b0601091211130b0a 62
    0x1010079524182e11180c1001400351b002c01880da4030040030020b1381c03c219000c0080c0d880c041c00080380032030f141d040f111004807c10b6500001207203211b05001d04030810f031200401c0390b658101c001c045032407052071140c200c4c6024000807810030004003503582c451041c005a2501040780324500345400720302c2d08194042003401c0001d1251111034400750414110850300110f98603804140152900c856602c04110b04581c039030f503040c1809002c05c1a030f025003c134854007200102d09003060b5000c2d204a1241900a100407170104c1d070091404070441f28500401d803158100410566001ca404541c000000002030100744690300b0901c0c003529545000d06c0c2c1c960340d190686440c1c0f404003c41704c11100001c1d0b09100c4003c800000244182a400b100201c00b4200650405260700b0103074071a110342d0740c04c0e85040c020440003000700301601c002a4050003083e41e4040d032b510f48610507031401496085000d0081019400591054900744101c0c0c012401e25040101d40d018a04000c10a4114180c10218140441d02c070a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 551689955 1250 551688705 551688727
    0xd05130609110a0b0c0a0305031504090b0a1503051b1203071a0702010903020c0409060603050d1d0d02091602010612030908010f0203070f05070620130b09010f051e03010b 75
    0x5003c01801d02c950040349044801d03240369030341c1e0703807004070060521401200007114541002d0400d084494041c03c240800481807402141d01d050441e01402d409140a0501340740c3c0031b00e07455400c00c1d60303805002051414a03569903204c1d0f0f0000b60054030b5201011a07034032405540d080c0080d001051090b42c10144c4051100c0003500104002085002160705d401d03a0000400d03400a8070055541c0141c600058080300780c02c260025145503000904144500716840b001c8035030003002054140380c0780c440900e1501a80c0f00b00711003201108000380d440900d05021902e810034480d250400480c442c000080d82d940d482c0424910a043d0300e006801041d24200708102036002170003a0140640139003811451807030900d0000e400b03640007007442800c1080c082001003c10aa50303020501028030798140308946015501a1010760303208001d403010051840380c00103800e43c0d883e4140c42071114161a081483c10f44280106c51540182260036081700e401800c41824400c403200541c081d180320000903a0b55001f01803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 551691205 1250 551689955 551689969
    0x4090615090e060d0f051005010e071209020d031d031f0b03060103050d0f170f15030109150f020f030c0304021c02060415110607031a0301110d0513060911 68
    0x100088018458004201141d642c132966810043d6001800c09145640c078105079140140d4501018001860440049001401018203510500c60396440840203150100000e080d6070300840c0003500700700041d19240006e80604015880e41303c103110090381620b00701001a140c034000e070115810a03098078031681071002060083c4011201c06a000f8240c5516507560035540d2158624000c4c00c00c50b0112046030024407a010304201c81c112070b482c2c0c3d800b501301102e1240c0300c400180c070080503804141d0740c40000b0b800c0600036030451941000340384840d4820040c0540150200584031071800350700b00450101441500003070f5005031031040c030341901c900d40780c418080c441082c1040c1c10079500014400c00016640d100450f42601c0030303144103401280480006480b0a81c1d80340d201c0b4401d025120400c000c141d815488443d400c0f08403442441500c56680c141800c07503c0c0340c40b030a80c04c0403080000a41911264202e81c3d000051286641b010310343d80e072941720445601d01002c86048a02c50302001192030a50 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 551692455 1250 551691205 551691209
    0x150510060e0a060f0210060603050f070f2c0402030a02070c08161e080f0a201507080903060f01030501060b0c0c090402041104030609050f030c1b060409061509 70
    0x3040036a100c6400320700080c80190580304450404c07800001c0094158420300901d0110b6002410a02642d0b44800025020786401c6403004040041c140000c4d005620500c66080001c0241e1541450351078568200c1800d010705141860303400484000d06129030305c542c4011072040e540f101c0c0050b128150b03403071300039049000361b8804266a030025480042c4005151140c034225612070032241000405180207001002d40342d400504035000e005800003021001080102520344110104c6101462150361920281d25210740c141d045081c3c04040140307d83c164000b09070b407901800e01503050010300800280f8002c000c50744507185028031401001040700c2405082d0141040303550320340c2402e41e000c0c04c0036130303480070010000e00c1030b1003150100b0706546640d480215030040d13810000d86c0e55030b01c81c24a00051300e40140126a01d10030b07042108592940403040c3c40c114942600075180140700c4940411503043c28030015a07108004210018019040307100300c5000f800c6010281c04141c210100240c8031030816 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 551693705 1250 551692455 551692457
    0x10e071202031c0c06020408060402031203011a0304051006080d0212120402091b04090207050f0706090312090905040303240315090c0305030f0304051e151315051006 73
    0x10140c0010380c1d010030002e0030a00c458003480780b6a83c080c40120352034040e81c6000303081948000340100724040d01143d0b50380320300e009800f00d81260788000340c0c0c1c4405210920841c00c0c10480e80d000340c0705000078040155013040c002c40c110341c103402e018500d18046510701d5011080700c2d8010500410025010b100c100090a01500020b091407400c03146440c54820040c4006d104918800000381074116110032680c40d801c07000d107030075210741d00c881c88400252b220680c1615030744071340c51480e00e5941000074100f060301c059a54900204c3c1c0746075981a00c0800c02c00c917130828080d5800000c07424040b1485900d220398042c1d6004a245440c090924202c6504152040920f40111a051010912040390045200c0d84038000245030589810411050031b09034000a007207020010f10000c40800120107103000350b0050701690459500540c0c590a07a201c80540003120350024000361400d000700d0304040741d0001404441900c015442d56030581e021000c164059040c079500c20078804405100b0080c01d016040d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 551694955 1250 551693705 551693729
    0x3080115020d031e0905100e07080705010809031902070303080a021905130503071e0b070b040b10260c1002030904150b0d0b0301230414120408010e07 66
    0x14500001d45400700c1e05003a0b424191505029041000c013001511042c1018100400c400d042d6864100c2e02c40000307082c80c2220500b001c41260585030040f520b58100c500300001010407034542070041d110040006c1c0565854081030140c000c00c061000f00d000440c95485c6e002e803141600f1841e000d4020302c00a48810320591050100c004180880b1008020f56403035402c01c551134032074803040c0344056515a00444d400d40200c030000200b80c0855901c026803000c410b906c424600f40c80c0c202030f00290003240009403a03050b40390b02040108110003e400d4204e07915014841c2030b180c840052400e001c111780c82643e141c43d412094198148414000001c20000403110048074650094000f9a6401419402c81c844d90341c400383d0114448180c400c01c40180794568105450f00500c11407000244100d070801d600a50a110241020b46480c80140400c216500903240c441c1c4c036191100a41256043e44120300b0f4403e283d40d0300c592203500c4010f0002030001d4000460803151102d001402d0121039409001b000c18 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 551696205 1250 551694955 551694989
    0x30209010c03081b040801020301180b01020a080706020d1407030c02060c09150d0c09210c0b0a1101020d090507080313060f0c301403060f0315070903030801 69
    0x39116100145468152900f6815a100d034403100b80000d80c044e108002c1550b0000e00002c0807941034000d103040f10031081c41c0524002c5031401c050141c582c4080e503a07005802032800440014039040c050310b0f459008540040c01e01d40f011681070100c860020100621a04103020000072035858020480354000034400740005d41406580c0c00c042d4043c80c000c141c400c1181c0890340001c42e44440945945144000060219001104000e4103a007006c5c0101409400043c007400f2020070f0102c3c001100e07070352001480018600c2e04400d0344050700504180ca041003000e08982c0c00d010f1090010b07000320f20341242c0000ba03203040752502d41d2505205500690003a0014481012400c02c9120030400b110071900700081035011114040320400c3d02480d0003070102c90f1181084545046001250b4030140d0b07400d884040b598106034080d501c06a554229607244d8004000040c81410004050f56012201508507405201140031250807136001b251884001030703401008000341984030a42500402c80f00b0180d07484c0310 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 551697455 1250 551696205 551696207
    0x1300501140f0a18020d14180d12021b010504030504051008010806060405091c030f06140d030f020a0b0103050f011118091012060b0f030d090513020c06040c060f03020901 75
    0x1400c00d00c50460107000c2644c80c404404101c0e0120b80300002030ba5010401c1c01c0040c0803a420140040e00c207083c0303c0c0c801c042c0300c0310b2601000400005900751511503041280b00c0801300e0010358455660100701d500c200d0f8103040628024010140507900c2501d5544c0c94030b0a00d4244540c0488004905080081082c0100101c0c4000300d003803a00640d055a02150301c3e80d9409040346401104900c00501450f403810300d815442c1d045c2d201151050000d0028402265100e03912100341d43e408030245e9221b406810340200103801800860301c40d18190060381c00c01d00031911a114489001d0744180c510703400039080740c20a51820705ca01202c0e41c03130f01120b80d0304155240031070f2051525090300d014080e80e4444081280f00880050030002002c2c18100004401100d10345400074110340c1d9250b0303021300848814500c05140100b8042034903945655840441450300c0b0400c085501da807080707180c501341d081103680b1030401c0511019104d6406410f1200001d40f0300306c001480041000140c50802d881401901426 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 551698705 1250 551697455 551697469
    0xb011209080d09022e08070f021009110a03080c0c0319171c14060307180b0a0b04030f030806090f060d05100513110a0305070501300501140f 62
    0xc1e1042c000000380150441c0b022030300184562401c1c0d084813020102d10080f558151071580c4d001041e642d9007496a4565031800c2c3c0d11104001200760141c0c104041009a041e0250321114429014000e03403903006003214040345110030325410039140c5810005105040c1c000c2008104d80f108025801840b003241d0001e110f80c160596583d00510014008900444d000c40704801e5075146440744444140c04140190981c00420f50940b20140f0780007034a0000b60149004281c03031003255031217140d4131250207400c0b01c44c800034140044200d034407400c0510049400302c1580091300c003031803080d00b1612205000e800c024003840d500500403489121918108148000d801400700c1e001700040d1445060703118581360140c10142411a103110691606003007220b00e14203045008580e5014204940221001005000f00c0002c6800f01030031a0b444000300300015481134240700c0101c4000c44041400c4062102c0c10703881040030502140000391070700014040e10f814041c040303048000840c4c1030942007080c2c070042a15 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 551699955 1250 551698705 551698717
    0xe010b0a050c2a0d02031b0a030b040614090a0f08070f0b0907140402090a14010507050105090102030f070e0904110406090f020406200703110a0305100b01120908 71
    0x1014000c18542032050040003034821040140d000d41e02d0300740c0352400c00c41620050705088118032680309810031181c140001e150000e56009006010000c2900f4413201d1414401e000b0540c000d80001400008102c1c0c02c03000500a0b0b108420200f10360505040d00300c401b078806004030040303801200c1e040d000038200300a0f15451a034404c818a454100c2070800403000d195400d00906210301c410100031a441c00401d540b419202c1c038200000e51004004103000490141d20020f64110110450034002d116400066801a41c81490550300d48511991134030b00b526001e6907a0400d0b0ba4000c810302c4031b001019150303107a10813020700c0c0030076454104600080e001c19000c0d2000d0451000040c403c0700b1a103440d00f01c24050020511b061000d003840c480d03141d000350701c244a08000640b29410023641c800e034001c4201400c4070740000814120b415034440c500740458445003d0342c08608a040000018400d000e02944200254400184420003100160aa08401c00c480160f54a404160030000711402d0690f08 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 551701205 1250 551699955 551699969
    0x7020d020309300a02011e140309120c0c031b1f09170c0a050103050112060b0619030c11030a02190f08120a18020a030816021e0117010e01 61
    0x102504890306245410515120405000181581c03040c00e151800584c40950340c0c400ea0310641c045054562443c41c4000e0302402e180050159103207071200d0000100910b4102d03050409441e40c84185031080c080903409002c15002075088a100d84041e85420300032050000043c3d8020703011903103c20300144c0c00c0511041c1101120016840d1a8417013882082408081c001e00101204451000d401c4240d54801c15210940300e140103400200b2154440d000d01c81c121501d0418030400807c1c01d070744000162a120a000ea0440d43c203214800e003410418011010000301e90310000307900320031030000030700d00400100705054681c410040c01c2c42d001d500040500c3c0785010014940d05452492400c01451f802040018181040226100d0b0710b006850141f6030182401c1c0c3c00800c03641c164a910408002160a000395100703100400402c08030708440000c004400c0024051a07001c0301341c3d40040d240345030b1032504007010201800506010b5030481208000064044080c84056140500001e40480c05020300c2c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 551702455 1250 551701205 551701219
    0xb0a05070f080a0902030601081b0303280309080d02030612010b0609010309050c100306050907090f06050901030b0d0302060912041a1b070e06041b080109020f040e04050a050607020d020309 83
    0xf4030804a641c0c4074103000c5900070142c50565a41d40c0007940c1d201d00e03e0f181c20900000303d002c944090300d00041100d0a050403a002e1504558913880c21034046214186040289510340160b040082c034120010034400440d041c0051b16405c11200748641d200c1d00105a08140e032510082440c903982e49420744001150900c0c0228540840c4d142907030800105980c030a420017500b084054405801d41c029a041c0c40e8256800300b9980d590321001c460010003403017041c104c04100b11050008602c10f070001c0100e0031060401081c031114070004540c6540a40c0f009500603000362060202e9601d0921000008050303440300030303080ca0301b091107442003022902145030019038001820041c003080c41c0440c0382112010020b841040355a5801c06880c45402c6a04c14425483c1403d481c003e8080450381c003c10410b01c0e07640200b143e007071483d000d00a5100c0c5c5079a01a00009100003d0481080c00340710b0b200700c1c0b1800c054043d0100c14500146004000350183c01950000c2301042c0140e0b41c004155a40c040c1c08850319 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 551703705 1250 551702455 551702461
    0x2030a0b030f030901170c0301180603020d0516052704020319050606010905040603030e0d0302010b030f0307110d20130e0f06180307020d060f06120b0a05070f08 71
    0x45402004600d400c550540a0595520410030010000d031200540c2a01d03180325048101c80300d0300714038a007102c030000c02c22070500042c48060014604a111841c5120000138144d86a800140d4802c030308640494050384102d9050400700b1081d41710a0090600b9900380c4001482d030702c081850302c12101200b41803031110100080946d0f81c04c10082c062100d41c04415080c100090604a403141021600940030440f071150014850800340f19040807243c25950750601400c1d242c04208640c1100c04c0c0c16411036490714001e01c0280d405024003044420303610700440d503072078442c0b82c00c03030403002c0e107852441c403581d02c0c480780e2030103d4081c0c0156003000080c1c220320300c0c010300f10800041c0080044480b88003520301d805005020500300003030b403942c3c1c01100c9044403401d030b942440d550403940c2c103548200b00369081130144000504200003c205424882c1c01d0101b9100c03060712581c400c80c6d100d60311284030a0038401201040c44440346a15410100e0704900344540c0c582040c0180600448603510b03000c000950b000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 551704955 1250 551703705 551703721
    0x10c0509010e0307050d0c091808070f170a12060f05030c280b041404060501020d050f0f0d020301050a0e0106090e15102705030606300a12051c0203 65
    0x104c01c002e014000e010600021190031310030b0341840d10b0b001307040c0110316288078401d00a0141c08015031150b4803062040c40e00c40c00c0e0380d03002c2004242c000200d9094030b94400002c0e0341084480070742003440301c956805c1c0c80b940c22105010142c50311540066002e24806105100b01c3e02c0c041003581851005858004c00ca410b800848220207203141606042c2c1c1452081c04209850540c0003081100e81d0501e0107500d5241c5401080100d6555201d040d0140c0c0c4440740703944000e03000347c0c040c2101055144056007040f0300644640e4056000403964800268008014821894520700c80790203002c02c0d4030070703044640c1000c00107002803515001d4040407201007800200c07008540f5112403540e00c4041c122000c2c02090400281200603007a50074003215507030105c00380c2e00181a20b0b1000c111035000f0020411501c4d00b1301481268901007003010440c5108561102c4140320005100901c4524400100a0b034911800e003c80c0ca5609848400104141001410103600300143c8501c00c50b110082c0c0160f480d00c403521 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 551706205 1250 551704955 551704963
    0x10b0f03180111130e130b09010b0a0e060306011d06011407150902090108030f0d0e01021213021504060c200d14010e0312041209050607140708010c0509010e03 70
    0x1801105660038000c8205030244031a02500381d0090800c2c1c00306100352108210038074004111101b02d0081c1d6450b200740c0218808041442d00405403200002e0600540c801042d001c64858212901500c4448240940360804200c1e990040c24500700c01c8050240d071440144001d0342c0a411281001082c4070300e10001d40c0c149040310406079100322070b030a401c464080e01d9800784c0051602a0b101380300b00310001408031408021135414800d154483c518010b03d0607114802802d025038164441d43d820310050a00311000b0881034040c201c001019290150140b0401640b038160601040e9a032001707000800a41d84c200700308800d1b01d40c0c44501401b0540c1e40c4165000c181e521440c4080d4003a1484d410642402818400a01468460340007404445480c0c040310f51761384140c011808031075406000080101e8170009004060848500d800d1402942d0b800000e0083c2d0809ca005581c00058590a0b51007444104600402005524000d1040302103969001e002c81c015a240b103414802040d0711120b0580d4140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 551707455 1250 551706205 551706241
    0xf060603070c020f060c01050603061f120f02120609011b09050d030c080313020109090e0d08280209010e040902060a03110c010c020d1106061f0302120c031e010b0f03 73
    0x5c1c01040d1150841020140039080030795919009028903004111030100100017251607a2030541c1e0b002180e4a031002d0032103030760300c210b5080d200c82d000c41c00741c000169129618504445203880050100c1e05104031070340d085540d0000007030981042c51541030300348d035040b0720500115503040b500e00c41114440c1c01d050f6131554803084010a120700000402010394000341900090f28005c0e07840c456925142e0517040200c640d07101c808601544400000d44440f482451910750020703d02d40c0102018022510024201c081c0790202d0030829004541c0100c19640a900443d50401c111400e001d901e0030703a00030680503c0303510046810140c0354580c0e0f28220b80070392700711906140c20070020030884107130000080d141d80c5030b11040d40000d0714203144940400d8002072924001ea1000300705c01c48200440700c6030204001910a10800e054003400740f02c0e0144444c4441500c2000b104000e103a40c0c0c0381c4106c5040b182c1e4110303148450040c68010050001c41ca0310010345801c0a18000750350398a4031148100b0a40d42015 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 551708705 1250 551707455 551707459
    0xa0207060608061005010305090c0f01181d0c07020d03050d06030209010b0a0f11100c090b030703240b0f2203030c0b070f05070308060f180105090f060603070c020f 72
    0x10040005514800040f8544125400d0407410b241c1500c40b00110700751882030311810388503030000400b00716510700220503a0715140141810027800d11035001e0030105440175070150700c100007d060175088c40880420200d52000c0c0106203a4030340030301030b40000d400049004001d400c0240c04542c44941d00415032250000d0b68000300001c195681d2080030f100755601a45815000031081c0300074222242c020503401c40700c00d001c3c130060082d111002c1203c40083c05501207400800035040317000903503035840300020b40c00349481d6640440c0e0600c640f810090384220140e4482c0c1414005c18040040071887c40c00d80c0c1110821014455131050700100c0400503100342c203109a80300f40d164000004154101020b102c03014030420840060380d4400500740c40c0380308004115030104078200040d000091255812541c02040201008171024002d40829908044c29000460f10160440180118600010459444070000803c032400380b80c1100440ca1602000c1c001c0e00511002240c1841195202e4180c04410040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 551709955 1250 551708705 551708711
    0x312091106070620070b071103041a1803030f07060b04060e16020606011d04020c010e031908010b07021804080f0d0501031406010f060f030e1c02150610080a020706 72
    0x51820302c00002d00201c000041850031340450340c0103101610040e20940c641002a4a0055a641d041a2881e0112900c425600e000811012404c008000c411481e046820181c06880312040da400d2420328003135015141c4258014805001100c209004582541e03a1000020a0207000c8101080262200b50070001d01041060100030803007108100d135070140c85003035085030318648513440103440e10f280c1160500318000c07611103250101d05054004150696074600000b412110009005085801c40c3c1c03c01440c0d0510480744a902d6544142c0326409803200c50344151601b2243c0d4000f43c400d0f02940c1e1810f1100303e14000081c00d110207003098807003403946c030301034103640e250203915003401020240821207081c410308040c2141d41d000098150306885849100e980114104482940e1421000c0b1190b400c06895035080e100005c0c0030320604034155003030321200d11038005008001e810700c00c1c003001c100f5414171000104031181e6620386846000f20a10f04080c261a02c2c0d844507000139100b220406400306007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 551711205 1250 551709955 551709967
    0x606050307090b090904080a0e090103030806120c030c0d080f0a0315081b09090109021207060e0619050a050f0705070f06020109020303030105041109101d0d0312091106 74
    0x50088000c40c86040c4507907a03030703070700903195600da441d68010580300c1c40d00010008001340000b104c11006000714002c0307050050244802c00000350f1110380c00d82045000408a00c1400084d080040755280312460740d4000e814103444500100740d45c0d1052842c40c42c42491204003800071701561000f1200004404841c0541d02c1e030b4041c402502402141e00402e584400368030001550f00c40100e0b10141c05508001c00503041c81d490003c000c2e0040c000350001d5030342d550718142080140e560156406941c0c0c6900c0141c00050710300b41c00680403000511002c0e0040c40100000e000d007140c05040e040804d02d40d4100142c070751031032030340403189030089030030344481440300180c9001408400512002102d00c03c00e080d044198482108a00b65010b01c00000c3d01640240014000e41c60540c00203280c442d00040d07054100b40c607020000304152098051040441c281c01d042400c0c414040404071042c0b9001d0300e0000d803804c041e81e0000c01e009009510006000e6403a000e08041043e4040200c41000e030003020152940 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 551712455 1250 551711205 551711207
    0x203061603091a010f0504140f040606090f0b0f0925050d0507020a0506092107021507030f080c070f240606111608030702010c0609020a030b16300207060606 69
    0x80c03c203000310201c002c801c5200140d9460940111400c0d40d000c0b560281c01034a480201d07a24000d005481111204d45a003004510a0a144500d4000040798400030404801207821b20004161840c0a0f0380207807203450400c00c09110440c1002024540c4001e800864410100c04071030324003d012190740e69504000c1401550380c0c0c0018007101d0203000d20292071030307a107918907101e0b92a200c6038013a40100031107001801d0b0612004024181081c00904501c11001c2900310b420000d50107000c040780451041074515544a41c000070199005107800070103480e107581e036220655420501a401032032500d0510142c690300300c0044d1503040019404e0130901100d070b120400609030303100481d604040c9204a00e0301140e104034079800c2c401113400400203940740031465001103800c0b10b040407040d1240354486000000580320101d2120085010760826072090a0a01500e82c20001501c018000c200706d640a07038455901450f000092055500002c0011000c55020207010b409500c1001e0099450400005241 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 551713705 1250 551712455 551712503
    0xc0d111005100e0906060f13020403150e1204230301140a02180303210405280611030601020d0e01020703051c0801051f0305060a0b0703090e13020306160309 69
    0x14403d01031851840740e5401c14020350f60441196855440800d12503080540e00304100e5001c0e41d0a10784c0360162425480351501180760329004811030301555a2044906550414002461112303100b1032014900380c0b4000d50082c485002c516010440241141c496a003a038096010000304c100700c0070780200d01e1a0170030304c120003900181e01c4200b00070081700d0b40c0840e900e03001c01110b4402d51070002c01d4040012010b40002d041e00010000c842d0391042e00b01c45403800074940c0300105034600050000403030b4030187ca00003041d608445030410101d40c0620600865a8003c940016841d40c1071502036006403d03000102e1030403c10340d0001d0b04038001c00500c41401c140310600e500c440a0151694802a41d07105c0c00d009004400c0f80b00342014024a80130405003901c250800c8dd0000b50003090481c845031a118402030369400664200d01081c0042c1040000380c59260b0010ba2184000703010030340741203c076000b01c3d0f00d03848000c111288541442c00c1814105001c0d60201400580181880454044070403e0700300c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 551714955 1250 551713705 551713709
    0x30d0305091902030a080c0c1203040801060e010509040f020f180f01060203040e1609051201090606061103040603050a0e07060206150307060f0503040609060218040b03030c0d11100510 81
    0x860301442803002250b900c10040c2c11002503018004206902d5541c1b142d03202c5401007a5042081d00455500d030340310b43c1c1d072403c442d40e50310342c400051a40d9518080303c540c2100c01c00da2201100c030344614010403c650b50b003d101c41d401034001790080207030041440040c0b04030700c4c1c10340303200d82c01a41c1d07407110710b4017031001e4622030720606094410b880c0e02d0340c03900c03016a074038081c0c0e2144c03543c425140c1c00050001c0711100360140429a06060000540d903e55000401d00650000c90500320780d514980035060200d0f40c0110001030845081810910507501c504503224412400f8090a0640321808140700000c140e02c030100321003246041d0341003e502c4140094032180300342e0743d601c031401070350030106080d1501040031800c403001a1200d030030100070003e06a59641005205890040e522100307200429000c0c00181045400340d9540d8080c0c0036104100421590242821402940248152840044005800030084c5540d040c54002c8105d1810f010303290a10b154070f00390fa440e00b00b00600514608070250102 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 551716205 1250 551714955 551714971
    0x90129010507170d060e01171e1c030c0e0405070e040b012606030706020d020726010e0105060310150614070c0f030303181a0702030d06150e03060c07150b030d0305 72
    0x3461f90742c5030250754003080c10900806584c0c00c150b501c045600d0880211306203424458090b9400382c01a0311012401444c0c1d2054100401e0311100450b031800e5000710f01140100044030100690b040410004240d040c402d11054003655690b03140c240316a00402c00312000d03003001140221320f0f6a451015546003142079071100d00034814903201182a03800414412000105e0741d00904405d480c120585800c011030f481d01010251000e440121480000e01602c0500c0b19117500110306400c0c28420306141c401c0410f00900f03524038180c45038844450182c83c0d40308558080c1748c6100c010100d545050b64905c546100140480520743d00001c3e1155414a010112400f03a201082000200500f1901c81a41c50000510380340c403508403440f1010345503c0c1c0e15040b4209104030ba0810466101103012600c003a0403900700011000740c4c03072104580c49a069203041c4000d4020704190704204400f10154055100700509140d5010320f40904c076115544441d04900004080740c0507400c2d4948080c0c000e04055503201 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 551717455 1250 551716205 551716229
    0x90c090d0f020916080c1c020a1706010c02011e090803120709050603010b03061002100207030201060e18060c0a0228030305090d02030f07020f0a0e090129010507170d06 74
    0x2540380b10a580c0d4290300140b003901c54191551b144109451240d21038007100c2a100b10034031880e10003550f05c0c8042c0010b0140740d01d80070058000440e41c40100c00c0d0042c8502c0c10000542003440050b42e0103402245415881c0c050605010481c81003582e025030715401a000510012800c00c540c0d43c42c6031283c6001d188140c60b01d6507a207032120b003480603501c0f0900580201017070800115209080084e01580ca5140c9841611503908445c52044240c0c1e015280a800603911401d081c000e4a03d0040030340d4005000344548680c001d0003460841c5c170f40d49d000b041401d49a038045444810345000380941340307600c040c101402030000c140080100c06249201c905800180c0380100013550281c0000d1407100c1ea101e2500150704000008a1082c1d450303000701d8040383c2089001401243e20740310480c9000207441d09503800d54052410604980c212200c90b01c4071882c420300c0d0380078005606034130452150f141d0700a1070401d555141a003403407542601014494402c1c22400a507030b00c0d0101040e0f0003002074401242c0c42d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 551718705 1250 551717455 551717461
    0x15061c081b0d0f0e0409080c01140c03070f2006180f070b040506070212030d090201020d0305070e101e0e03010b09150111070305030406051305030d0e090c090d0f0209 73
    0x960300c4002c0b61604001c1000d81d91440b003d1805002e4828600d00024030108144402d0fa9034410f00d90805c10304424903a440352002803250201c41c3d4036550110a40099604526080c5401401c441a103001d840500c158003855103031020703035001c0b50401c02d50440e00701e620301d0508100141c000140b0040030b504602075908266030200021881c1c40840d05050300300d0b42050300b010108092544003000403070b4005041506070011050900103000114001c07000083c00e4211070001900741000c0c02040d008051a25080125980d00320341402404d1400340e82c880843c102c0e1480988441d072202c00c542c602c0340b200003414101c00c0e80c0040310300c00500b016030091146030405420300038242000d07181402006024944492a075104485080d40c5003c5032045030039040d0350391290750a50f4015004103000510000703610034400080d03203080f030082c40b003640180072084034030f0170003407001e0240e503515840b494011000c5200e031022001641c0c0034020050110400380c0e0b0620b0701d11440014440c1c1240608045c03000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 551719955 1250 551718705 551718757
    0x20103060e0402030d180807080f0705180f150414011e0612090606050a0e040303230f040213061404050702030a08040314041a030f0903040815061c08 66
    0x4182c000c640c06801492030181e1703207030255182c1002040d69052540324070000140d40e0b00420075480102105000f0704614400d5000301c80c1440a15005907014030050624421080b10b0501c501d03500c010901d5581c64952520740141002c0e42514444039031141c10410707250102601c4401c0305040b10305012100c01c0140b039880b031002190495100c0c0354045000406070220002090301b0199421340328410010302c0607100c100161381e54419400080300450108100010550140f040007a19100714940440c46442c0082018205200900109030b05c03484002117411910707404285a400b1305280000e10405458021596200140014040c4203608000201d4011800881156006215a80d851906541c3d90b1010b0741c41c92818803402d01d0001d03080100040804101d005841000000104296241842026407650307020280c4a00070700c2d001040304010090300001c0850000c2580d186444103580c0e52400030701c1c0c154828504000c0c1c40744010040041103c000000c00e2080d0f245012180601442d120f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 551721205 1250 551719955 551719979
    0x403051515030a0b0c040306050c130b0405100e0d0213091109070e010f050c0d051803011103181603050c031501051c0503160c060e0d0c091508030a0c02010306 70
    0x8807003501504203140c0b050108804646031503014041c4071084c0e161907925510001210801c407418008141c0c0452001c4008540c00c40b03131070080454400442c105400d010015501013122043c0300184150000c2416460f100d1080b80e80303001d80c00a000041540031150000042c0c0250401140d4114290207482010301d40441c00900400c001c0d500c91a000071808010343d101c948048192052110078040c09001e00700030000c1c0f03858102036070345040e10b4610300301c04038501c80040c400c13951081c3d040c545c844445120080a03690706c1885004900e2000404c050814284030201441d88200c071b080742c1d808070038004006012100d410080e01180d400310380764000c45c1250b840a00270b00d0740c1718001403035000e0b10041d0308044030b441c03501400940f403801182070754401c0010a1801c08031210203603d030342088000d800c20000f020440c03050300c060901241c141e60720755038800303240079002c40c80e0755076200f945445442000b00405071a0711403c695480e4205100130b041680300d000201d0000c0d00704900402c054041003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 551722455 1250 551721205 551721241
    0x2812051c2d062904030b130c030c0303080603010504050d1202040b12010e16020c090601031425030e0c0d062706050a06080a02040506012a050c04060b040612060b04030515 75
    0x3c00344605050655945c0d941041e405000316041210a8409001194000d05480006c42c03082d15070015a91940c030303001d0105840101014481e034588820000403440200304400c00c0c000d6860122901c900610600c0300074011030f0082960054045000a03008032856030b168103031820304034071902c10341e2080c0140005002034070f10790005030014582d0350101c1c2099003102d0740010741410040b40080c14440c2c01d9036a51012901c05c40c5e040300c9000302c60072009a88a403102d5440307a924092000004070322420340e50f400b490343c031700c1c2c01980e5814030b035010b120b0a81d01141c44400750704803c0c9410500d61422409428842c2002d840062601010542c2941c03240303d080d00700c50030280508502640384e02004014003000f03100ca414801e0a40b440b00780381c4d0a8094442128000701c2c0c41c2040c9400b141020303450101000c1d94140104d20f8284140950300d5010140d40845d4141d240c2041703142c07112010403001d0205588444c61180300403502004210020940741c0203881c5030b41151810fa0f503100800c114170b100c60 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 551723705 1250 551722455 551722529
    0x7080705060a021213030602070b06090702030a0e010e041d0703110d030926070b0c0106051009030b09070801090c030b070f0503182812051c2d06 64
    0x220380d5140c0713803501c01005048150840c03440c10032810741c0c82d250103050340c0c01810700f00c0d9069030303100030012207181070305019400030814401141441d060f014098024000058000e040c49403114125040d07a4541d001009501004c103072000c107408502c4810b6945a0150008582d249240f440c15015814134941940c0003642680d81c600d6030a01d801014020300c0740d800c589000e4400384141d1440034503401c010400c01854081c40c40350b924051840400c5c02c503006070300645d102e0401035410850346d5070701001400c1681d40041014030075403a4000e00c14506102503010a015500302010101400480110b060849020b841208407a039581e540c111454a40c045404010507410700c00b040b0715003040310507001e81c0ca030348170211299200400034010100381c00ca4645030455007043c2c002c44c20040d01407100080480b0030f0138060300305207650060004160030090b54050080d507811418241c80c0d541f000507288104520310203c0301200c000071030805807849016048201110042202d8136200002c143c883d42154 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 551724955 1250 551723705 551723713
    0x41203050f0a020d0b04090b0712050c0d150314030418050702100c05040503011e060501020304081c090e040c09060f08070b0c0304030819080c12071103190207080705060a02 76
    0x42c00c1a800002d422a9003480503065403210606881e44952049011160094415102c1403512500003450400c02c1c80303441c10a04d0901082c044920b030f0710b42c02e07144101c403c6280410340c1c14500f07d00c40d01e580030f40c1c0d2024021080c007601821b18004040002c1c42904d000b03152130360701c00c461042c810041d503005032049401a0b0000307080d4460a810b0b61321107070401e1003502d0203918107661480024251560411603a22250860000702c4280c0d126100b5034000b04000c1c0069410a450030002c544c982c9640e00c0c00000344044881c2c039a5642d44180c440c07801a03d040c1580806500f400c1c10004904019401010f00d202d1030004d020400309070000940c412100740c0b5000b031401c5802e2030f0a44c0070750703000741e242e4030690300c800d0002000080b0904045e0281c00d444000410b58022000801807000c00090441c01e8050010494803100c08115000e99030300c0042c508205c015860b240180e02d282d03114204000718401b00b410b02040c0c8540d03010500000300d9020300103c6018035218410060b42d441900b18140242e40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 551726205 1250 551724955 551724961
    0x9030a020118090f050a0c0c0302031b011404061a09100611100203040807060b0a0b0d0209010c0203011b0215160f031509020a0813021e060d060905041203050f 70
    0x200c21444102c100e0151250440710555581808040e100c40b0050000c24036260b00401c614410f00b84201d03400581c0c1454042c03113a08254401035200c0c03044150071050b412400c466440c1441094120002c0c461102000510303078038081c1420002040d10707460a10302e10003402c002003082c1ca81510101d0240d405840044002864440c06039200102d0702c000d440c25004826028100241030300c003842c403541c003481c2820340d00c068500c1e11400f100d1080c000544100381d402c4081c01171842c000150b58070300f5004000181c0e141c19410040c4c070141140c2000940c1076080c0340d40940084d03000b400c0e9030203090301e94084030000c110358408142e98030f00880b8040c0d00b411154040007211071007036024544066040c01e00081d14901741102c0c40394251a5000b40031040e40010350b44024541c01445964044549112001c10780c030130b60300062060340407015160b000b41c4c44041200d2a90340b11000c40d9032040050a0401403256504040c03c00740c0011201a04d4403068542800400c2e4028064284070340f0490350400c0f01030ba = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 551727455 1250 551726205 551726207
    0xa05060616050a0209040b0412180b090102010213060509130b1327060203070e060c0706032c0f0601051e0d140f0601090507020109050705150c0706050307030b010509030a0201 77
    0x251030402501c0798407500c2000d03c00741e02c4078040140501d000e00d841069a25060402210b01c580d804501000c00c841aa0481c1c0d984118142a02c1524080003004c2d0b078458035000101e029010780c5a40101c12808110002203e6811500400000300c09403031282d16800115a60000c651019106541041d9480703500c4020041a910103213001e41040c0040c40c0c4e0f8110881c60100c03041d600001168800c0d80042030040880d00314071402400c290495045250407000412541c903100b180c441c250034140c4a20205d2224601030f802d8840144062100006440d0306150043e41c4403d03d160400181c01510000b18007030800e1752400881034500480a00712107a01030030b1148048103034009643c3d14490400301101e440c0103003c880c078407041c008000d01155061290b1030040790405008038095a240c250410000341000c1524000c8600031100c580c0784040b684102d00240c810246046802c0c0903c0c2c10118902d5001406980542160b507000c004031581c00d00191190710955140e070b80d0550040420070015 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 551728705 1250 551727455 551727487
    0x4031104020c0a0302030304060605090403120908090312041409280f020304060207120203090a1421030301030506150a03060f110d0903020f03070b06090a0b03060408040504050a050606 81
    0x61400508010714080c601c55501d4240300826000720016007001050000380300003070050030f014002c2210308011600b041c1d5405400401000c4d00e1700f5655032928054014044418141c60380c2c41009020745a0040f0611440307021588a07001301814501c0c0081407100c03909009403410701c51b4412034226443d22400241141e01c2d10292441c1303114490301c418220802001e10b0002e9406144502e8025807034200601e40580b0304201c6607041c208540c004e02030510f032592039580f00381c01c035098081e10031000b0400c0f1004c40d400341c290681442c911548004000300310700e40000254101c0303024400380c52242d164600d902e01c25080b0403203481e0748400d0848013400820b002e940103060300e0800da40c000801c40b00604080315141c114200141c03070544e517015031005141d014001b111b4602c00f05400703945010f06036501c0304a101c3c00030307000c81d001c4c1040c080090303074180aa5000d42100306008044032a5858545455480c680c031900030301e4043c908120200d00311056038010540502c500134241c50401e14840303060084 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 551729955 1250 551728705 551728733
    0x1031b260903031f18020403120309050d05090f06031f0602030f0711062107230301060f05040e010308040f060c030806041806060306061d1302091e07020a02030c0a0b0403 75
    0x6404000303400103441e6001d03000a80d058010200158487e45141491200c0c03600c85035045091608001041e00005e5000c50b25206034045400d105858112030400b04014001052000b900844d001061141240905e4807046100b2000c0c5000c5003620740b108812600c0b40240c0341c0d4100f80e210305001d070030001910485a6203003064050300840c02c06145001160f005480b408904110820341014081c07000d6000e41004128074804c4030352000400d001d5030b5000c0360310052254000f08054041101c0140340700d80c0c2241d0080268a9414800b543c4900300300c1ca4550062003884100b1005100c0050030300c2c05800c22240c2d007601038030b95510a58541c010320000d031001c0000241082c0712551480b002804c5c900c0740d01c01550040500061081c00c040c09401c6081342803a05142c0141400c08000100410103402821a03506962960980d1a1480014034031000b4a4481034107100700410040103030f034001507601e803040c001c42c115541d0303958a0782401248100d0740210340c05c28004020510206200942d940c407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 551731205 1250 551729955 551730001
    0x1909141006270c05250b01051008010b09041103090601050102280b10080307060e1b0604060e01030209090f100506131208090d12080c0306100e01031b26090303 70
    0x85040c1c95044e14005c02c1c003c4101e151200b81c110540304041c0226201428090441a11a40843e103291f941c003400a13181407049140d1104c0000c5c6480080d201c40d00020504009121010307168201030036001d07265a401d00449005100c0c080015200022031801b0241403185960401c60000c0203498000d20000c0061654030100042100010040c00030401801f00070b004001c0042d203800c903031400ca8109180c00b01901030f41c15603003040c005655109800c0b5001c80d465424080491809400181d020740101040280e20140b00d0040081401e40c010320113116007160718442102c140c5420400400e80600d400c1244410354110041c0b00f00701d076030601841d10324092810641000043d40c000703010615100c804941740062000c402c04d2040d04141c4468000c0140444d250441c07501001248802d40080c1e00340c07007006506103841b0b4082c3d020360301040e2030940b0480d0b00070b05076101580103008d596022a00828012030070300303401c00d4000e444003940c0c019201d41c0050b602e55121307900b402d41801489000c40c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 551732455 1250 551731205 551731207
    0x804030c090e0705091f080321010902092b06090c060f020f0709180c030320120d0911040f1d0a110f0a080f100c0302121909141006270c05 61
    0x403400c142c04001501c50768120300c1c0d01d4440c14003c01044c8040600c1070744800b03482f60051049004036580d41400500d044080c0050b504052000e00c62482002d65002c03001d41075070303e088804d100f800109054101502c8071500d031600308200f801003c0341d8441403640e01e1000b603000a4818014540340d904841d03081c0760a900f00301417400d10358985881c000e1850340704a0120b10388d46010b6841c00440030480250300b0158001d0110324105600c000b18511441201020860391015407500300801c000e243c1000400141c0100309884096800d000205170414801c400881c0350002d0700c0007401e00040d8500c90607804180448030045000030720910840c81c6499030344c002d80e501c4010032403038020032100802c603002d0002007070000c00030488641141c4480d50a502050b00401045039880061319030315401800502c21400075440304800750005040030b140040a5466943c5280382502001443c04503602101400700815960351522040720540d02030748000400300740d40340c003e9180e03441d4410300310030803542041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 551733705 1250 551732455 551732459
    0x80c0a050102130306140702070620240c04030c0902160206130e010f06020616030e030f04050f0f0a060305040c05090903270604090b030a0804030c090e0705091f 71
    0x80c0782640c1200c0701d401100d5610701c00410500815000d004804200e04a00e2105800e004400a441d081c075801035800303001c105028512010500382c80c0c00d43c00791207081a520000b6494503200001c00304090b04101020750714001c204c0300d003000c1c01160100c1c0d601c0000140018a010401806074000304813032280c108086c95079502584501000f88000c00300308101c03806407400d101e40e68000d444180c10124445003140028040c0c150006162600070310b4141c13020b0710314040000c0450141901404415450001040101481502c0800351081d15070803601c1440141d08141030082401c0c02090403980140196420030a07907000b40e22607a00b00c3e0040781d6038007184e0344480125a40f1042650048034035400002c001c0384126000d11520300c148640d1101f2100c00d04d09000040250103103004a40300103650340c15a4945590400c0005507030ba0b4442c0c0001d0f210356413800c061031881600d00c905015903003000034152200e10045481d07016250000d2622030541c40d448c00c1a03100300c40e62481070314202004200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 551734955 1250 551733705 551733713
    0x604050402070b010e0705131e05040c09050f04112a061611010c02250f06080105011101020f041202060c0708011a0f030606101715010305090a0f080c0a 67
    0x104800c03070181050a05551420525010008000b0004020031000b84003420408c02105000e804956a90200241ea1f01101104581e0504954081540b0903d0002542e850640056061044038000c171444c0c12080e0b240c1c41071100b943e0040c255505103460402c46841c0320620a030142030030207803440c02203091194082400c5d241c04026079581050303804c403e80c07400302154441880d185400501c0001c9c0601c01100d080659140c000008503c1f144081404c40c840d003100c021501c81c001c1800c89a010022a0b40d5100540108004c2c000c0d00d0000300420015064240c05008032a00290a00e048074546858550481d40900c4001e01c100e9010342e04203e4a5420710081000002a00080d0000610341860b82c5805040001c0c100c002401240088030303501142d42d021a400780c1c411410398030354400c14801c5500301c03410220062106420780d418014041910811001c0404015080c3c07410000d03034450800c3d0710398980340360500600480840c4150710015102d40c001d81484224030044801c50402c13991 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 551736205 1250 551734955 551734957
    0xa03050a1209120c0536130203030d0c18141504081c030b0411040e040303020c190210030b030319050d02070f0209010506070b130302150108100b040506060403020904020604050402 79
    0x10507900204000b5045c00075140c4030f130f901d10600100480c0502015070312160300103280c8000e282c207a03c6003403610000741070012219401d204a03a0084c1a20382c1c6105203241280140314182c04940018003000c0e00034101302222031860242c4481080750206071041c141086001c0c40034403140740240506200004404c48200034180050402c1c5000121812601d41c00a0880b0310204c0d00611560601c40c8010903100150103c6050350f20030b040e50302d03c0342d65500b030a601a10850003487d00b64455103607518102c01c00e00300c001408600c2211504c030101c500e20821030070344481300310190345504100310540000c01401d40d03209051009003811420401e0154404040b41c104400a840341c0301d0740e506020852505005403400b40a040702c0007402c1500c0c0e40c941d1030390a00b0080507a0045561520b81038103150080101908e92005210300c19459078488401540703480c40342c4007031612181802c101310741c44e140c00e00506110f0800a040242494516001c00424000240059800450400010459440d540 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 551737455 1250 551736205 551736239
    0x60403050f01111806030c04032102010506061222240b0303120117011e020a0806010903020303092b050c01170f012616080106050a03050a1209 63
    0x4001d084000305000c002400d541d8600c900c0d404a80003044054862110400c013080981410340d1200d4907a907684000250a2285030405040340c450540c962914885a0326000c01d9113103542e00030700032030f11074a050140d40e0198540300d901918151000079420049064114440054880d5500300d252858840001414105d6100c1e0b1107000c0035050840c0c41320f070340e01442ca00140b0540c011442c002d0032810132094441d040c040c082d2071043c1e80c00130781d030060303825040307034499a00c0c920070403000c060031014250003548070b201c2c40c20104505030700180d459800b0b904180c088a4018001e90b25205198003040059211481564404030420b030301183d40ca1b502c04040c2c030b0410f10900c01400c030109004000b41c968900c14400d044032030504d0003004004008030001c941120079505003010b444000900d80c0d010203101101d251214410316189800000919002408031070840d0000c012030f076150024409000784501019100f60320942441d0300250340d81c101c910071800985000c001580e00c0d5600000c540c1c00030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 551738705 1250 551737455 551737463
    0x20706050a06170f03040e04030210180303060b07122a1401060b04210303060513060906060f05070b0a06030c031b050406060c030e01052104050613050a0b07020309060403 75
    0x2c5000f4485031a1240d024618082140003c1c00b040340407020480c1d5034851405040041048440032500300350081060b0103252803461401c1c84003450340465600d050070f07595410723000242000400291000352504032040ca5800c442401c071001451401034900c0c0f1045c0941d082441c3c24805082e008900d02801580c800e03200f030308030750480c0303030309a05a500b5251281c0200040144c200820084c1100c8900b42c800313030503041c0700305c09200400e0307007020b0b4028861580000d8112039440c0e00ea42c030801c400d0b44040140c8000302d40800c411501c0389811900708090f00c200e075020600800820002c541156440c641c8558001c5010514680b40e0792501ca8280480d0b004803803444101086035044080104d455014000948007041901c1c9410001400307080c010703c0140501c06108820200ca901c071b481210b0302000c0101030f0300c440d03009040f201021400201c0f0191441e001d09400702e010080340c102944680c41e0050000c1086005c2c42e183c100c0d00d0600a4403502c02d601c02084000c6803038880b600604025405 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 551739955 1250 551738705 551738711
    0xd0608070e10051f020111030c0a0909020a0504050105030a110a020d1b2a09180203010e0c1f022404140601051f020a0804090c091e09020904020706050a 67
    0x1030040009154032000c0c0415000e500312003070900450f19800321106032942134440c40310381c411072640181e006007d10b5944a25030311b800000c12640380d01c140e00411002c1c00c6640e4202c01595589800c0080340030f1014200700140d01007000304172541c4070301c0c041e64100b21074040000744283c408894440960100708020050b82001000136030150b0016001401c1910b00d65488110350708a51718645a56110080c071181c100003e02c01d10705c06240b00036000007811035283c0410801040f4455400c2e035211403181284250b0801c0c0413810030384d0700881e14005614015001503040121000f204000c1e02c107410f017141c00c500c01c0d4410480958030181074602484007116404001d414607003010050300f0409800da18003648040d00401440d200c607203010303201c00c600704150350100291b54400c0382842074081c40542040c101040120b1441c141d6480b03c0140322258403586402c0d81c0c0e80114441c81c0780f0703a841d01c1d007400800c2c280822071954a80c00400d41703920000c00043c0b4001c0d2650b504c40c12201c0945540b11010780d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 551741205 1250 551739955 551739959
    0x20a090e0906070c0605071206081e011a100c0501022b090b0429040804090e0607020c1c06020c060709080313090c180b2d030a110d060807 61
    0x140c0d2149031500003103440c001e401d107403030000c0d8050000518014002c110701c3c2c0c0c44002030800c0b8828030380500c5540305928140420f0340c0e0744d9241aa61070648010f10742d15224100071b810030302c1051040105407858901203c41800d403400400c1300818443c40402c091140a59925001031404e2005145801401c802c1c0e4040034840d6520003809081c0c0c0803414440751819031310001182c0010002c5070b006a01070000d100c004002c44d900b6103070107182c030000500794a1090600040154180150082ea00c0c03020013001294550221141d50700820786803900940c024180b280010f0510030440c0260311601d10303c148c065010b41e581e10040b0b9000d8050b541807034100400b40079600b5440031840e001485480c0c0194141010000342c0d10180352144506030340c0c00c0d621900050000e010700342c80c840c440504036950041301e0792001e0903038031540010303080c440b03020442d03540314210100c6010160190040e1041982960740e0003004100501031006090b20b1020240125100500107000c4d040203840d02501805c2294 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 551742455 1250 551741205 551741219
    0x615080714010f0c1403040b0c1f050f0a050a11030c0a09061d060306040612030c05012a0503060406170f010b040902030d1b0c030b07180f051012020a09 67
    0x102407071450400a000403404800c540c030084041200b50000303018012007072030001d864a5485180d00581c1003410210755103240280100e10b2400d02c00000c2c5014001c00341d0341502c40c0454804440602c11110f0b54000b0403030000f402e50100741d00900340070000803034030041902c40720550000c450070111124001101c090495000503240c1c01000d041c2006001e2500604c0b01c500941e02d0b07040c2d002e001d4080030002030115a16904603100915001c0321b40481c803005410010914280d901007a105503080c1030300d0000e486240d5048441c1e034220b003140803941c124000802c90380345c1d102606031a0b2180c0c6801020aa010300c2c051044115064070000f80244482e54a000d82581c10442038039105515000362000980c07030108440558031a01e1400c0ea014030000d082d03124040407001c030054900c03807445001100b0895410b550301d0003223210381c81e001c040c2150b458416002030000d0107400404560364104114070304081b40203294402c41400e010300d03105420201c0c1d40480e000304021000044d40c485080142c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 551743705 1250 551742455 551742479
    0x1e04030203210405010e011701060908060f040302060a0506030c0a08061f08030a180e040b060f04051317090303030901060f05010f3009030c03110a050a0f06150807 72
    0x42c0c0d00040d0804001c441010160519002d140716490500a0007014090035038460b80c401800d908180c1c58404032961904401400d83c1c005015000041c0300340404100050300c0c4210148c465581a801440555160480a40509805410150988100c58070003500380c0e83c1c01c85180180c500d96004114920740289004d202070005031601c0b44820b12075605000d01940803040741d0406410f030401002d40d038916000c01d45149800c1e408102c1c028501004d0104100c800c10766035005071021a6a00c0001032150100700485100382d681201c91410f01411b04006085200840b280c2009c03050314500b0486100003190455000310b403140c1c0243d5681c40180001041140410050b090a1030040ca03800356100014000501d03070700e20344681000070144140c40041d001000100d00111070000e00c5550310341d150207000392024481c2240802c414001204d002e000000d0303045140b540203c001c1c00c5010b200d894090003000701c003800303448031600d90503031844480d441a500380003005c80c040100035032032410080b1010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 551744955 1250 551743705 551743723
    0x3060c0315090b0f10020c1e03010606050a17040303110a0801080105010b04030c09110415030c02151003030e0d05060106080108150708010b0c0a1704030c0504020a021c02031e04030203 81
    0x107601e0800c80340f246464054151107542419101040c241d805014164549440c0312056544124504010b0741d124409030a100c10b60441a802801002c3e01c403c0180c400f4007500e64900000741103e5550203241c00d1008030140c200340603050000b0b8911030b0b481d03983c2e03143d4003a904c910086032110004100e081002d200d1540182070340c590643c14142550788941052a80303206010899450300c250303180611819003110b0082c00503010400c000c0300342206c082d000d00310907480c0d03401500035501d20000c41c1200c10742ca03902c00e034038419800f0003803400c43d03030182c40c1113203100c92054220390701c54124070004604100c120301a028030303151588039624243c005403504400b06c14a80c0b002103413100340520550440c4c80359055981d0b0f2a0711584609812030140c0c608060008007400c0103052150310360100041c500104250303030090030211386080d00c0c1c400780701c2a4452100204010b03801a07848401040450319003142c1400c061059034a0001112003141211310000010b45c002040081e081003146020464400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 551746205 1250 551744955 551744969
    0x1051605030f04030b0a0b0907050a0e0910031401091101050a0201020904020408070806010b0a020601030b0411030d05180409053003091509010e15060d1b0305010e0a050309041503060c0315 83
    0x218006150340412048c05000c0e10034014031501240c40b20000740105260060100e0150a803181454071a198604410302d500c8103886002e154190300e0540d2406002e143d0501d6003202c10200181204c0e8011281703544050844011554213200409550307886000a00080910100a000e29400c02280030308100c0113034003401100d2001c0044003842c54004c00c080303046039040a2034040c036a4490a040100380e200000d9103516010326510480515000f20203400348a007182d04030440f0b101e064003070008a41c015000903203030364014041011600c0480d00202a50354113419400301241d0040344282c82a00165018041500404030211070788045001a0381c0c0800740ba8028031a0070340150301e440d2589103c10740d4003106150040003ca1039182e00d0004030f202548040c070801c03481c200c84c0e0f410148481034082200e165007801e5806a0400c000190307200361302d4210340034500d04a02c20003004010030560600c00c0c2641000c20000001c95111711941c641c0380c103107450114a480510820002e41c4901d81c220314 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 551747455 1250 551746205 551746211
    0x140d0f060f0b070b0a020a0c05101b020d05030f0a150603020306130227011407060e071505181903050109110307080309040b0d0c03030504170601050105030601051605030f04030b0a 79
    0x4003013402c0c03400c81c07608000000e01c0142e5884121200300d406904049010308035124a80240303a92207800c1d071102c1c800450315543e2a0506404003000c0340ca6a081d41c9080000a4092000c14030000e0a4140c20780c016001c4a0300003070b0841134144504d03001101e94042004660701208105850a080c0b14042150030002c0c41149864004100c1e400c10340941c20368400105407107505407000380d02984001d0309400c3c2203600b660b200c0d0300c3d074941400039000c81c44c080c0c0c40c680150382c800034044008005545030605251586414802804006444070042c1c401d40d03a403060310140f0a402410a0307014034800b642c000c1e800441d21904e1810040308881031900c82d14040d80c01a201081054004010303104103510854002c11803040c203100042840c507181402806c4558603982c00001c0580040c010001ca48807142010140d6100011141e2a55000d101d4580818010400120705621450080005200c03100e1034845a90f15500c07035a02d0341d0032101c284605801c0c00241802840a544070301c0382c0c4400c0b918030034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 551748705 1250 551747455 551747467
    0x102016090c0c12030f06091d150603071707090f05010503250504020d0f0216020306090303070c080703111e0f073f0b0402100e010f140d0f060f0b 64
    0x2000804080f22140c400c05030780301480c010007405c9400010050a650409010681116200c40c4400c2c1491401c1d030181c0c8503040720306c0c4100d03c200c503200307201d032100030040c2956078544003041c60040645000d0b9a1030740180000414049000d22130707004242c109000018081d81441d003070502d480c3e1181000403400030380d41220420181140d03106020b0f10000e42c3c01680304c507242128070020301152010505024000303c2c4881c0340c07072055124148001c3c0202c04030f074a2521004079050b100d01c826104803002409082c0050040781014008000d054420f140c889400e1405440c6981800518880d84180c2c1c807204100700000e003800c0102866805481000d40f0304545820a00c00007000d41c10740f81c1a04002d4820410b60a000202c0c0034001c0300f22414120b15000803900e8908040941290220301c1441c1074010740742c550344584c1e0061000d60040c1c5030b50701d4480350150700b5203040d40040b40c0d00307260102c01c01c01c41802000a01079001c4031010704001041b103c4c20205100c545021540208180510178060 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 551749955 1250 551748705 551748713
    0x2040906080a0b0a150512031e070803060f150d061401020d0915031407080f0a020c030304060f0b150c070b0c03070303230106121a102016090c0c 64
    0x8a0f03504128198000100c0350040c101108819140390f02c095408946c03500340511781c10300440141b003030441101d81d081a161a0b000c140d1024001d101c0701400b8588140f0008410b400d01e04441a10403c0051010b861401c0410300d50000d90f00144910242a803104010401d4206528851040040034006480f1803a00f40100510f40703203080c4078000101121f00c0c04940c6940c040c0c0d01081155108403c5401a8601843e0141c0b00c500141c8000d00000c8000d4001580d0340700b40c0c820b844011a07044065840c6407550b44610020b008841689070303859680b80000c0240360b840794894141c0740c42200e078060300e40301070105190a0442c0c55004211000e01008480e4140ca0044204c03a40b1070b40c94100003451084080140c0030202c500342000c0b0b501140305001042c60354200401c080c8405082c1410310500b043d4140c0350b134001d6035402a142d00301042084951000d40104c0d0010200700315003c00b072240300c001c042a2850001c440101094640714000d0511211485024948000203103080100348000c01c0d0b51 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 551751205 1250 551749955 551749973
    0x160302090f0d060c080615090409080723060702121c0f05090a14060105100c1502040909060b010309030f0c11130209120f0307080c011d0c01030c1407020f0a03080a0302040906080a 79
    0x2c5144600c0d40e544181c0e0070420120b0134cd0710903641110b02e0b100c084080b0001e4484a540740c0c0001e852038442d91000400c2c81d0310004503160100340d00d4400c03070305001301c191042811b69061409a0091707a203a000c1102118810310900388181c504400911215840c0e04007010310708204054403845410600052115840340000c10103c121f0a01d001c012074001c5007070501e00e002c0c2040b00f104050703000040c0081c2115a94102e503c0890041c407040101d10b11040c015070441c5c06d104001000b0070902d0320301010720346c000e21004040c0b502540c600501040e6120004130024600200202c015034040b0300300280f8180140004541030640006204407680113a040d5501d00400744001e1180344c00080840007804203400c0041350340340346944d01040c85030140c1400c0e01e130000503901500081c9011070750119244907000900e554021800050318006d800e0302441003a01c069811150891402c0d1070010000d21031f84018081c41da0282d400503150ba0418110744241d5240e980117507560b034450000d07580803a008030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 551752455 1250 551751205 551751217
    0x10e0c0901020a0c0905070e060a020606060a1101091a060306091b060405030d080a151202060c0c06030a0e010b06031e0612100603150203160302090f0d060c080615 72
    0x12005548a04050004038a802c00c8060000c2001695140002e40b0480a4110398001d40c0c0c2510b907000010800f04c00d0103224010203c0000050744414007140c0756040c020010f228a804d24a080102450100500b03420364054031002c0307a0103400e001d47d240e060f510030042c190b08080110b01401140c1003082d28030340e55950b04080d4031000002c54070108000c0d56428111801000c01030140c1724068000072020f00802000c4401205082c2841541141e88450481c001c0a0314920b0b080c000b103140b00c43d028805203403c0103410b07820520072499101e18070341e2004041c6204640903100452801c0551580d00e084d6207950103210702500d070500901010401201d11005007a040c14080810b0755510030024400b85076218010b01e0300c3c003e00841404444640c2c001c0c5050741d01828841c5890002ca50700eaa00300e100c2150003091400c50059942c1c809032090f001007100031001088049020002c20014144001e0404110341d03144d07031100b40c00b0200750050b405543c0181c2c111426858541840005101d5100e03031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 551753705 1250 551752455 551752471
    0x9020a02030f1309050a091a010609260303090a0501110910030902040908040b071a060109030206070305090306070f020d2a031103030c0703170c0703030209030307051b0f0108010e 79
    0x70414452420480098030003c4c004280c080c00f850400302681c0005145010060300c0e02224410704211800440d50071138100c40792681e070301804900d8104204d01f0b4480480d0035810401d81e0003241200000100040c50050300e401d0041c0804000d00d01e041401c4079540c9580c480316150502248071640d440600484007841c050a0100740c00c240c906c00500100222500200f101c8004200403504101d01005001c910f032042c10380490f40500c0008840302032500715080350014a200400f0720040c01c06d1009880590300c40d0805508144600740085d052080c12120b410000d00355600100c81c07d1350401140801009074184040e4901a408400815014203040700c21554500d008020070184500c40da002108a50070640780c503410510b82507059a4070030310b001d0f030003e54000400c05815000f90803050046498070212440c10741141d9064000c6d4010b0a007a0342d03d40418080d04011031418818118801c54903411500b00c11400c0b8104903103451020541410814104010b12101c00e043d0061500a800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 551754955 1250 551753705 551753707
    0x1060f0e0d0f020301090b0615030c0f0903161206050a0c2a0803151801080d030f06150c051209030307060203130804091e1b110c040c1809020a02030f 66
    0x7103410011503100440344001c4d05076103090101030500000d1803155018074400c5403140c07002854500480c19074007050740d2440100300b080000c0c4080e81070340c000604080d0005016150a048450604c07882944940d100700da140e10a0003c4108202d100e1161651183c486071007000341403500303603008088040031114114050701c0c007502d5a84810201c1007807104140e101c440c040c1e03285080c501c1c940101c0b90920f00341d03008081400e0200d035809103140d0b601e03042e508200c00030001c1c0e540046c8100c002d0035071421200e0000b640c403500451022418150303910380749110703100d1410120040c0b8125140101715000449070b02414405001c003035601000721094540c10840150f00c988442c0e211036000c5e02c040400a200c03000000340051102c4107608146074802007450b0205031001c1c0300341000151035011046050084e60304a05011607405a40021480c1c0c01c1d65086916811005001c28202c0c0e480f00c0c3c20320302083e030070042c2c201c2110f07e8040d0746000d810410b805508180d80280065541d000c2c08031840a2200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 551756205 1250 551754955 551754979
    0x9180112020f3001151203051810031d010c0c030c1103060103031112030714280306080615030d080711070e010302031605060d0b061605010c0801060f0e 67
    0x299030194889500206030103400800c56600340d49203441c000c0f440c4030405500380380a2854528081c0c0f104401c440211600c10981480c956040300e261340400080e104106049004084a0303c40f08440d4482000c5510001141c00d4038024240504800600d04140e6a05003c0414002e991099030347c4038040d4035003045001c07040b80386043c1c21440c100c48240303034062040070000403d0542c491410001190701d84241c03461600c05061807000f0b403000b1180c0b100070642d41c41d1020300c031328000e5004100010242d4100e10780d1040b1140100130082c0c013101107000281e29007006001d171036000d003c2c4542200c021241e0400256854021a48940d800a00c60741404106c2e0002284540108980c0344550415001d40d007800d510b4082108801701d0a010681c083c2c490016010300b010001d2890009444000341756130f0406252601000281c20400140750b0000c0082c04052004070040c08403c2e081c030310030360010902424a8100416000d4140d000b2410085442403466038503800031007411a00e1000da8020314001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 551757455 1250 551756205 551756209
    0x25080a1206231002010204050105070f03050705120301150c0215070309031a010312230307170408032509030f140f0d020f0708070905061f020309180112020f 69
    0x5001d074400400310040e4a80b41015400b160400400040112141101c200000308103d01300c2c0128082d5502050f000c02c01040429202e445030103006200b86041d621380005a550941080c60040b5001d8501c0d00100c01400300c00e02030b40042d10141c0741c605e0f0042c840702e4150009190003004140c210910000068950203040c89501034001554201ea440d0885444500e400989508244025142403c11020342d6241502c110303803c4d282500984046402030114106e207041e140d02c003420b08000e22000f160104031894442c00304511440c010400152680307000c04024150408416440c41d0841d0382d045943d400e1a0410148d00a032600700e0f240104190845c50300704c104180070785040b111407148802d0b0601502c8009810f51040c0d07143e43c2550320760300000c44400d40d0350340240650622a00440c0c01803101c51005c1d48500d81c0490028540c0e2181044468006800c6800c1e01c0f4200061f040050f10302200c0c00c0071903071241d001c080c0c490142101d40c54581400000104900020b2068841c810720811036 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 551758705 1250 551757455 551757461
    0xc061209010225020301180506161b061a010302070b01030f050102250201030b060c1b0333060901030f0f0611030108011509090302120f0409020f25080a12 68
    0x8240701126280c0c1c40001c0d034000001c840643c4504a10960a00d0312007441495501d005c20081e42e40f2400801d510745821000e00c502d100c00e0b41c0b1600401088a040d01d442c0c20700e0404020f40039001d91000107500e06c3e520301e00c04050a0070b404d02c13414180100002e100150014220504603500041844111402803508078068824132507031031240e58445040d40c50034110500f030b81e2040e03031003600c0c04c00c4900303c031106100c981c0c01445140b01054101043c080100c403003d1044031441c900c000c040c2d803140496075400c80e00da210b00c0200c41902035a181003654802043d242c840b40c10441c01c580403c000d616560390840222450140101a00e0442c00300f5410040b141d00610180204024511740300c2da1a111200d0082a030008040c624510340030001504900b58882c0c820aa03030141d02405034046281c0180340c0d60391006030400200c000800c000600028a031016246214410004582d00d0581660028019640e0000000e5030100c010102d000680350b0011100ea8007040d0502190786000082c2007001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 551759955 1250 551758705 551758717
    0x50a03140f0d0306090e0708061f050a090903140310030f020402070c030b0603010f0203090a060c140d06061413090515030a050303040303050708160503060d05101505030c0612090102 80
    0x25100340c40394050443d030160400016940d40b03250800040140c45a025500c0c4104d100747c2d142504401c0104056000c91001c0f4007524221400d0609266035800125110f035025610818849a4400341c0200f015407203043c13103500644000d0100d0460406030748043c40d40213244801440001140c1c1d11004544039a0155000540c001c6020211240e90b420401500c02045401902c25460040c102410095900c03d03a130150010100604182e515170b5901c0303008000007807811050001c1c04401c84603402c81c61002301080c440c401004502c03149050b40107402c40c107291001005030307441031042c40c000580203030000381203070055400070030661244110929003019034503020360103002c0d003401c0e8028007400100450280c1c0c443c1c5d90412040c2e403019012240e58600b035650320a0040e07680c1307260410b10300c00c2c1c02441d08030340d0003000d100084115669191820900d64400c805d46234851040310045482c00410600802c020703400b8086020b01e51000a8852060f48200030000b21014046101c0d940e00f5030613261 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 551761205 1250 551759955 551759983
    0xf010608190c031410030818010908030a0f030b09131220070f090213060503071403070e0a0611120309030f0f0319181101020f07060512010f050a0314 66
    0x804015075100060184c2180c40450340610440000300c1e000f88020f20190003200c0e00101003508000d14622030f6070f40448121181c074100150100080b81810301071000702420780c1581c4441c180a1490180602614416014030b841b42c6040b00402000005c1410606000743d0b20217070401c0140354910040d17410128141c140c48400c1c200b0000c4150318040003500c001950a0000c1c030304151a5941616026446238041018102940d072200700500c6005402444e0092018141108450302100c0c0c440750613002142d040b00014481d90740300820b42031024854010300914680920800403c43c83c991f9286e1440010101e5140f00100268001000b4420f03540b22004009500303030b683d414132694076000d070800d0b2044500386410124000c04600107214500c2d544011032043c0350981080c0d1034505803d22030160182c19801500d0b42440849010700868000e0030440d121145c413154149820440c10301c0507081b4464850102c0c4041c44696910005c0804a9502000700c1d40c007445821002400c04802c400044 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 551762455 1250 551761205 551761211
    0x10e060f120f010903140a0c0b1005130b0405070c0c050f0604031202031c060305061b0904090c080d1b14100c030b1c11091003150e150f01060819 64
    0x104100b02c1904040b52080c002e50f1110700440d45419004510310031480141c0114680d4205500018940c080d031b281d000b0982d1030607903012940c4001050400006c0222402140d40d03800720000b81346000e101c2c1541048040c075007072030006640d40e600c03400c407102d0780a040c1c418807145070125010342d1020111009542e20a010b01030000c41c20401039600e81103019810f001c51416500c011600046128400459812400905c01501c81b4494060300d210b0b80101d406106204101351401511035010b14040c1c00d1140003a5903603245002e814174240700d04450b410081280c070f2b00124800591010b0420300d040e03046005840541e4260140c00c0c604508040199000c908010100071025056400b0380b922a41c1074801c40294401c002003900402d611a800411001c0e070030307490030300c41c0c10500c210a900c20301c0391610040898480d20341c040642001c1c500201c3d26500c8a5071501a0601409600d00741141c01c83c202540d0300380481e4000c100340e814002c035030420007030300300040043c104200da01d2000302d044c080c10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 551763705 1250 551762455 551762473
    0x1302120f010e0a06050f0412230c070602011d0c041a09010f031214030f1f080606040e031303030c02031005130b010e06010f03020912011104030c080303010e060f12 72
    0x403545443d0901c805071004c07460000085c03c070030f0809880b648140d521180c2001d0154001e80e080d0345215044500384001c40e0304a0312591107203c140014100312640d02c0042c000c00e4900f020003401d44080320160f084a0700c2c4c0c1c40380742c1a070700d100203401c00400500b11008518084642096000f0580c1c030b031031042c4c1c05401400006020215189040c081d039028400c0c4103200039080d1415115034164000061000b00c1c100001600003540e1a0090342100c50704122072400c65150b40b07aa40342007800d800c95040d07604000103010340341c5003d02c01d480c07501d5040c401442c140202d201614581c1e014510003d0b0034003d5a1f880c12003190f0301172148090307a020300700c41041785045c0b00c65082814008407104480c008490000030070100d0804e40d0062280c030050392102c5104009503422006504803a081d0b60700400a059000c000a07020b014404801d800ca20320540c6a9141d4248101e501c0c4ca258003030b05494000704010302601c52015403055200704151580c204005007070703010810a8001000469040c0121a10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 551764955 1250 551763705 551763731
    0xc1e13110720041401030201030e070315020901090f0e0c0d06080105040f050d02010e1209040603080d0b03070f05010e0402071a0106270e070804080d1e05090102031302120f01 77
    0x45030202c04524045220006802003800204c81010381c0305800c00e10003800400041d84a40c215400c4001d121054070901c682d00c4c1e41d080c040030340f00010045d10a401007000303081942d0180300000203008030030500440501d0001d022031007990281c4100c4c1007290024154505410a420020003000f6041c000c00c05c80c6818180113005944007541100c0d107000e41802000814414028195800359081c0a0b00d52008100805444d90b40000c05058110344c03240000800700e98400041c0641d09411000450211038100030141410140d07000780c00c00465140f0306000d980da10914144405900703440050381d805843c14000d115906001d051601d28050f0000460401d5100d020350401c0720700307060580585101d100701d441c4030b01346501400c3e00c11004000002c54491107242c1c003d401a000d520300a2500000500c04d034181d41a244601480035054800c19074a01c4440c4642076220700d16a00850071810010405803000181810191068100000e41c421180081c04000011042c45d0020402c004076001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 551766205 1250 551764955 551764973
    0xa050c120a0e060903070b0c0c031e19030806040207080904021c0509030406020307170412260a0c0611040b070b0f1612020c01150303110c1e131107 65
    0x500400092180907030038a0350f04207070007954480341d40100038084040c101000c00c080307500001420080c51103100d0102105440c14040e070381419600724139020000d030070709801c1840e081101002c5802c45172040d5480010941c400d05440d08004200da0260b03458900c0d04000105000b04001241e02034800110804018580d20a80100c400307982c100388050390740d0150440d1280280c0c4604000f5030001c10202d80000c0f805000c145051881151303e0342800c0d2296055000000300503011206103c2841107008480b08065400c00c5820160b01501d251541c6a1001068003d1000c001040180c43d01c5034281460b1541c025a00681004070320a611400f80d401d0202e1408010303101c0ae40300c1c542140101d40040080060030607104081d4581d4081c4030100c0b05283d0007580409240a51135603150012040d81c000c03a000c6500440c000da44140040102c0d00649081550410072140328100700314545c0b03445417084170410b524503011182003c1d074008294100d4007608090018254414000a9980030080200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 551767455 1250 551766205 551766217
    0x305120c220f03031803050303010b0309010b100f301509050f06060d14010306090b0708011a0d0b09071806030213051c02090f01090b150a050a050c12 66
    0x3001c0120710140da040201e080c240d00e026910b101180344605102007409102944c0c1e00c80180502d84001e60354a48410382945c000381c0188103240c600105020240500b40103106c2030403802c850400c40c8440452021340000b90310b00c031510510044550560381c006210100386041000b410a001140688864920041404140360758011900801c00300d6190420720595114a0224440c0344e41a242c2c20200907090300045600403040d501c2e80144810004a0104c40d802503200704070108040c44d0030724080b580354070000d0020041195060040000c1c00034000200724210a0f00c4d00b542d542c101460681001d00504010280c01c60000d10920041b240d211070442440117042c02c41c00c0ca074945518088040e481180440100c0f041960014010703450304680c2002142c0d840750011550104660215618001c1240c45009055210004100490441c050f0703000c1200d0071103200e01c90050460328071102d03004d044403100030400d01040940210f0300030012541054044001c842a00c0e2864414040315440301c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 551768705 1250 551767455 551767477
    0xf0f0510090905070504020912030a05070c120b1609050d080c120c0c01050d0f180b01080307030210020723011a0906011b0c0914060301140402010203160305120c 71
    0x300300050a80081d02c242407000e90700401800c0702d00d24041c100320103900409102a80640083c40d00461003000304004c00d00d001c0c2c20788a503620703102241090900c40685600060503000346d80d080c100091396840980e130344a0320804d580d00952034109002c0300c4084c5a600616044140c0b600d101c0103006200c0094001d5006403400c54100e40c1d903028405e41030780916050820180d0100010134025130095016002c41002e0950002c0c00c9041d01404805a59250701071380c0d41c2c6446502d81100340302c40c5918050144c18041e00462502c0000c2d030f0002d580b2442e040d43d81a9041c3d01003000030070003510411040c80940000c080728622158441c40394028000d160528151410104640300242030801400c1c2c45040d05845070880d100201c14069100200e42c03404841c016032000c40070445e100380e03201d4900b4541e0344103e2807032039282c000103050840c2c846000c003014120701c4008000060703034000100c628180010482490440080c90151003c2c094008201c610071001404c0005100d01c3c003020b01524981 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 551769955 1250 551768705 551768731
    0x3030a080c0f0d021b0106050102121e040e0a11030912070206070204020a05030f09070f0608090c19081002040b07081305040908030702010c110304090209130c02030c100204080a02040e010f0f05 85
    0x80394041717034202c03aa24400c3c1400741c0c0000504508070301100011b4010424881122070200c4800c20001c280b95206070403900c0080e4600d014007003102c0f0359108000d010560000c40c1031a504042d070030301c2e945001020105da11003070700092440842d210b00301660010b6601420a64a8009689010700302c3c0d0421281c96a180c0701d280001100e2400c00a10441180e50411561140c0340c140942100d40c4100241032100900c45da501240e41520303450030101030004941d030308105280c1072242c1141000c00d2025038465841c014001032240007904001c4031580da902c01059540c50412202e807402180596125640c8189484488401d0240d14001180300300c110b03900800a0505075641a00c070a87d910483c2c0500b548244000d10410060781d00611100070000c0c10000005815007540c03040d540684800710050b000816484441c0b4020015514201000c1500b9401c1c6810403004e641e07660064500030380714903150303444040010401c3d0f00101c0344810442c814484060314000620192006442c0103a40f000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 551771205 1250 551769955 551769997
    0xb0a081510110a02120d110111041403070833190b030c03100204030c060525060f0516120b010c0f030509030f1f090203030a080c0f0d02 60
    0x615003003500046401403140392944140c1c4030403508050718454101c40b0f84110300a40b0b001d40d403030b8480c820750302140308000e00182c0440a802401c4032a44400c001042e81041e030b17022841136480f0156815594101403d0554600c4480040c0c40c020241d405400e460240040710300480404440e1003800400740030322100c3c0c0500703000540c1304e81c880c12207000000b00c2550720a1550459a0b130000840e4007001802c848003020888000f0b42040032084041c500035500043c1001000004040540142032a0400c2c82c03d11042c2070542c140075055035010341c086118000c040c002c0141c00d90000c100e802e801801004a4904565100400b5100c00c0901020070f62482d100001c10365140240620319406949031001c40c04166101c40c1d445016540c101d00307200052200e50740c9a1410403480b107150b030030440288201c0302403640f000c0f048046c20418419040c01c7c03136140c0001d628000101c0d04a00e440c1d140176a110754450f07140704003501845000034826980003565a03003614aa4001d022a00300055401e010a8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 551772455 1250 551771205 551771221
    0xe1804140a0c2310050306120304090e1e010b090106050d060e04110310290a0e073908130b041403010f0e0606060a0e0d03210510090e010b0a0b0a08 65
    0x3001c080041000410410000c0c47c4d82c03d0168140c00781c14000e008607800d19443d6002035081e2501103c603002e041c2d0015200f1510821944084200761158800030003c504283d0080342c03607080d05000e50001c1c02000500340a842e91f081d40032400921651588600d1800c00b8070b000d403110a84d18034807e01c603101d1004c160f040d18500c0e104015103400240c50140c601d0001c991006100c1c034241c0c0c3c41c154460342c1e9082c001001d40003041000d209460741d40d104281e080c00010b09a507542c800900350b40b00e16101031346907041ca109940c01042466000840709841d210a1010710155280341d4010251142020034000307a24004d4118034060b85804030000c1c400c2c1074a030180c440c1103440e20b1003004080d034005008074006040000051100c5011458000c0b80c07a103543e008500d84041815040b0b00217143c2c115880c894103810030354010400c0e152032081c041030900c1d00c090340d00420786000b80c007040e44c0d450111030505c3c8025402003c2285001d00801426a074840e0244150b0301310101000110708414005000c40c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 551773705 1250 551772455 551772469
    0x8010303020d181a19091a0301080d120b12010507020f0a0507030b06180903180603070f030e0f07030b01080d020d141614010501060e1804140a0c23 65
    0x201490002001014134000071400d03d554040c0303e441404c50100102e00326040840a61000e40015884200404d40303031440c0504005007040205208640500041c0240381010400e9800c0c0c00c19031820100210b80d4a041e20000c001c5d254000c0da0181502c041d4405e401010b40140380310311a59000d5901881c5010070141d00c1d00340641f801001500521018400544820b54183d003001d4041d10300221a219015031030340d558801d0311141c103164804500715044010391116005043c6060f58a5411401c2138900a0b1110740c5202c12001416100d55250f4216a002c101c43d0075060f8049003114001030391303800c000724061420300030104a07008003800e1900050001860104d90111540d628004001600c0d40803100e820801041075078003203135030781c0700c01245034551000c126045c0b1a00000f007a500d4014060508900c103014a03001d8203103c40b1181900014034000c6610030b401030a1500c0d1200010280707410942c03041c6008241e10503030000070038049075402c81201e54244007015800d110030358200300030310 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 551774955 1250 551773705 551773727
    0x90b100617061203040506041d0601050f09090411041104030c050102060f150d02101706150d09081207020601030b010614090d02210a0615120b070c02090708010303020d 74
    0x2070080540105000741030021114100c41211002e03039003020384400005480d50300a903c000791078000b5102855904501240d0990484070900f843c5207490440030446803107001d00000a88521541000103050240d2041d4031800070310010702c10000510506484c0d2541e82003070200351411340c3d1a0b24040b0b131550001480500407500c1c3d41d85803610b03982c1c0400c2d0b0441404540c880e15080140300704480016100c2803041140c1030340c0c030b44510b800380d0304203d1140d505007401810036100f070800303a020012016519040315a503407032001d40400c1c0c5045600f081c1c120f0384500002050301c103980d03408000a1039404140141070301d20030450390400c1d0366243c0e8115132046191040518841d420030081c1881e16040711000200c0784003800007584c0d001c10304100ca49240d1210218180380d00054241020440035104050700b0704a80c4151524050810320600031260050000800303080c10100811451409030f070100c60000c0d030040050399540b620000052810100788800c40240c8200d166001d0128090040c1e121 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 551776205 1250 551774955 551774987
    0xd17060a080c0613030f06050702100603020604060f23041701050408090d051501060e032e090206040909030f1e0e0613080102310303021f0f090b1006 66
    0xc00c0c0c01d42d50030410039510800541e50424801c00700040004e140780311070b81d2a5401240b000802d40f5007000d029003480209203100c0045071404100740010b0350342c00e05032416031b000b0340790011118140d45005d81d0200c65001036966001c0780100c551a048116000078000d445075420344000080c80d41011500ba42c0064500914560b000d0158000c5418428035012a240c002da017150a41090040003280c1c5a00a8001c140010100282000741d420100241e01181c040042402228414100a50020740a4100110394503469803484001d41d55260250f8000e1f009001d0104060b106a2a001d040c1c520b04265a0340402c1180350300c0e01040c40c10b042c40241d021210740310740c54010310101c2005210392001040d0344000329021804909100c0910181c89050b11050300380d180607034105003002c022900c85600f15078080b0001818070001c0c0d400300d032030307150341c40faa130283e01c294040144180d01a045060305183e41900d000d404c84288103080300d416000d20040854084499240c031030403540b050158002c20 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 551777455 1250 551776205 551776213
    0x10e0f030c0f1f020310050d030f021c0c120c02060d05011401080103021c021507030323102907080306010824010e0d0c1e0602010c08060d050705030d17060a08 70
    0x310303443c03d4540045130300410b00c1102000b01900d41c0006400081c42d094103500246144000254441d010400140d2804151503219000c641810f001854082c1e0014020040f0007546843d0320241e02440a04c108103070700808113a15090322020010090109200301c0082c505002c2500c0b24650090103c68143e9030040d204400c00d5074200c1099143c0d005021003207800461080101e5482a02c05000c1c4ca144c0d03201e5540440c03618805040300014001c1e00040d25042860306e810b1113641c0c210f6911440c00c55580c0b058080d2000f0f21b40b043c2c02e005a00c504281c3e00d100c0c80c00110217003000b40b0310005620070b11098031980e0300c0380c946015500c0c00d004ea0112040d500101019414010360183c1c1280b80000c070024200407022002d03544200e6411015841900103100d601d41c0310086032907150640011700301a02c001c2118603c00d080090071034401901060007409200313001803d00c1011300c1014090302014048400054100c6401040700c0c0000400c0c0c030002801c1000307d849071070040101c0d0b00304c640c000010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 551778705 1250 551777455 551777503
    0xc170d050f041e0509010f061409030606010c031b03050306040507090605030604021b160302130905190807050706050c1911040e07031203020307030c08090618010e0f030c0f 76
    0x21001c564041100300f81c2c042e07070000c4001510740d66038603010301038005003510b43d062900e04000548182203080360204102410300015210780c03800104642d214109180c0038140703040303034202620240041a441c0501c40b11b0040900149038004004500400b0b055904002d90707500c0010440c0c22001c079010b007a000805c20404200e00e0305d415000344c014005000c101c5c4800280c42c1c2e11103440e0400101c070780300c3c80c0101c101f03007002545040828868403500707090303061010541d55034415486001010701140188440c4d04081c0c24816258161150142d12901301d62100340c40c2c18024210760040c03603020391903200d1245d480c484501e00005820301d4940c041c1c12074040d00314200400c80941315040c2d1810152090140001c081103105040038009891600c00584c2d07400e14030002401c0d640041044010700000d0000d003c40030400151155211000420306605040d1142c8668090309041382a8074042c885d9102010031070b04040003c00f59000050102d40e0307514003564445441e0040001019a0b1118000302 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 551779955 1250 551778705 551778719
    0xb0f0909120307090f031104110705030d09060209120a1707170d021201060f120905060708060103061e05040f0b093c06030106081c0c0507030c170d050f04 68
    0x255400c1800d40c10090700c21600c51170107203c94040c0ba8020b4440c2003013014091114140b038469103200c807142119a1b407800308a9110140d030f912480e80c5861500d55203417801030a10034540e042d9100e400d0000c2400b10100215146241d4900d120041610010b02c981680200d00301010203e0705c489502c21380c0140d0308040345409400c1a00401602c518442d020000c0003c03440321100e400c0d019226503101d0b4038000c143c2290040242c2200e400000400e480d101140f07001c6080000d960307900c400b191601c0b80b0a503951400483c00740c1103990084c4e454000144684207480444009002602c1056500b08601c00385000581e064401e003040942c6c11081d4070b00454440496100b4584117540c040d07980001c400d20703400501003085092080d8001e000c001d00240020303443c1c01e004403002001c0500043c05060280e18400c01d040b0246440c80080c800b1030120780c410800140888002075030031001d44401140e644810500720104520b401003030340a01245081514051001d80308072050389c0380042c0c20035040202d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 551781205 1250 551779955 551779957
    0x30f050c0a170409060609060f0e0d0615170c01030b030606090103020913080f0304050c0a0501020c0f040e0105041b06110a02040f0e010e010606030605091302100516060b0f090912 79
    0x401115040300f0400410050050300409004225a0344c481e4200c80ca42a8018914040403040030100f0203403c0703001000740d03a403601c0001e0716500204002650740116070903000050b85513000c0001084580d40801b4161000310704d540b80200d00381ca080c0b012450010816884080031984550300000400050000d4104410401e1380201c2d031101030704c100d07485912a02200e8002e0041d14803200e0000080004201041c0100705448001382c0f16200c88506103030010352529414400c0900030500541d56000540d00c07074110303c10f03a5200d03030020006400c15040000004d8440c0d10421454110400000b171001d02c52040140f0141c40369000c1c01d59900c1560801001c2c04808001038805511400310b4151820288148282d0140003030001402a1900901805079000c561010748140000000c2018540014030501c50450381200c0f182d4082100400070345480c020485013011030201c024400c41000184e60000e0303101e030401c942c0d03008803140100c1040100c035001c541400e416082a5291101803480700 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 551782455 1250 551781205 551781233
    0xc050d0f0212010e071701030b191a06030703060b0c01060306060803121609030506090c011d0303180301060b040b040311040501081921020a0c050d020a180207020d0609030f050c0a 79
    0x4070384208030b602c1b40c0c032145051910a03001a180c0000d10070070310a414541c000c0820f0500240042803100c00f0885000c00501202101024003820b000000605843d100f680000081d1003a06030300c50301e031500380f80b985000300243d00088400c00e01e000d40228a1141c0082501d48080c0f84c40c8003032486942d1103902c022042d07400580305080c0240740201100044050080501c14000704008014001d08180010b290010011541e0300314840407140030030503200441251441011500040ca40a01440120b801400507078044220142c0115011071341681d4000184110f030b008512004401000710200000ca450070f1084e0610f0b5404014000c8401c026440c000c008030b40245403000074521140c0c1c40781d00720b034500c4840c90010f0300300e1541c64007007207ca0002c0308040e10301a1840c1c02e403010f899022400111950080f8114171010401407136911030340c0d80407508003941c05403403480840031516200000d0301c446070040f004100600c020b00da103a8841c800b40d4051003042c0c4000c0504005903110001004111 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 551783705 1250 551782455 551782457
    0xa020d020d0e030c0c09130803130516030303230609060a03020a080a02091b030606030a021306110f0a021c0c0302090c04051f0801061209060c050d0f0212010e07 71
    0x80c0180c80344499584210b0b020b4a104801456940031034412803070a00040c07085c0309101d22012000d01035100c074103040505200780d00411036a40c03a210300d610b0b00b25641020030000c181d4440d01c0a11a5040314014003001181c1c0309840c240020003000141102b00c7e07805005d00c210311202c03000050342038601007455a1700a400540800b0100d40c0b00c0e000700f0400707071942e0030115550f0b1000c103000003142403500320305501500313a400c400882d451410301800075200203000148640404004101d0a2540780d04541800c140b8062078080131369113030400340a8a10030100d2841d680141c21501102280228450704107540c010003024a130100318003440c01e403440b1401d0545a01c5404000440181c4450841d140644510b0180c2030f1030714031f8101005500b03964449641500c500c5212035480c40364000c0403940c151442424003e0038402000032080080c1200e810203841e082c100843c3c903910036040340003001c0e115800441408602aa90020400c0e481040d0700340c002802a44010407103061107010365a00b01c201 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 551784955 1250 551783705 551783707
    0x6080601081e0c1305030106080307023007050a0b130b0c01151d1e0402090612031c0506010507030c0f1a0c130e070c0b0421030b0a0506120a020d02 65
    0x144100ba0740101e82e0807200c40600050015807001c219800c0180640200801c500910601d41040600ca85070700440a0003401510030160850020a0351240502124015040a400c8110f07050b14030f03035244200c0c4502400f8042c88280030440c541d030841102c6040c8022a110794009181c20b0762484a6404080c0c130740c03071a558412404140301513030004400180840c90340041100c61f055507200c040c500240211481010b42080004217941c401c40385503000b6011119580c182da101e5010803480d00c5e0380300180c166404001406400122080382c09a504c2c00c1c0000200080e40e543c50054499108a005c09004a103d641840c000141d6400720000c2c4548943c1340c004040e609640800d0064809583d1110b060002003500403040d0304043c00750000b020004000c42403401c01d40405485407815003001340200000c100040e0600031100302c001e2440105005034580072403c82e400a00501042d100e1621915404100083c58030b0001c00fa03d0070417503c2061040903484103e40c40009520400c200004250 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 551786205 1250 551784955 551784991
    0x130204050904123c090302100813020a06210b0d0807060605060415020f12030f0403170c090916200f01021c0f09150c02030705030a03061e0608060108 66
    0x140d0110840142002c0c1c4000014a030420306089550240c441c1307000308108411a080000da03a4a000003005400c180c10710040507201d080030320b1a4421a110082d401281c010400291664001e0018094948022130b141a410800c3c048105403811180c4256201482c3e0920401194014004080451180c03d0024040c0ea980c03003ca009900150710945d03520952110505502e6018000c0390030030080b800152861560214140781c40d408060420103011503030800040805003e81480f44690310051408206441d00d03410300c0400394001c03c0b07103e00440c038200200c1c10b404038110f0043c000e83c2283d11040443e591b100303410360040e100100f00f00c680b4807a0419000726071000b88000c01e00c441c41100032580300244159820152000c0c050044941413820030401c000c81e40244840e100004c45081c0440e02c0140e80400701d04e507002e9a100685180000216100407682561244040f03440c2442c00c243d201c1424401402c1d214003900c80d40001c500c2c1e400009800b58402e4604540c041710388814a00031070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 551787455 1250 551786205 551786237
    0x906622e0308030f100e04060b0310060e011401090b0a03090c15020a061406010c0b0a061805090f0a05070501080c0f0d060f090c050706050705070b070e13020405090412 74
    0x9000e5900581d0848000414084048010307040e5540c0300c11080e0381c4090b528034007030000380181d40080001c0c0c25240d403244000352a0341c0522801848010303605c01804880c0e12800c107881410070a125011035403110101a242550042d283c200440b40c07101c03007440c01e0480110064000c0d10000c1c80c121800014480c002c0788a550107000c000c09000207038003c000c000d000f4a80002100d00440d9981c0815802e60200300c0e4aa0744044d0108a66900400c14001c42d154042c4000240c902e9800518610030080c4c0070101c281d41542c4041d100e03074518001c0301c0c1106141449140c0303600c1c2415003d00302c2d03048640c1c144401c0d40629011034014540001707140c64484000340c0030303250307412081c0400b10b550340720f6604104280620328854003a00c0c00c41020401107004000240181c803d115000305a1625075001900b03550003032068607849070b005075090b0715600c0c003504001e10b0007440c01ca040d4851100780e1100980b83c2014400d90301604c4025024420030344954985001c0c601e04c540550040254200038401c07a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 551788705 1250 551787455 551787541
    0x110a050310020a030f0b034b01110403081602030309060f0c06093708120901060e04080f2809050909010903090662 51
    0x484080070300140c4403d0f00c41c1e03000b426680c0b00c082106080d82440aa610075903004522aa0035000c00108141d10b00c62801210000c65141e944107242d4015802d602a4500000c0c00a10084c2c00010000c000d401801c03802150303540a40e00002d4010341c1c06120929818000780c00404c50280003d040301d0510180100091459014080c01100720130007055942c0c1e01002081601d400555040281c00005842084450011492805403c04166100b40c00303469600c40c2117981000c075041096241d486040f41002c088078982684e548000d50719040c1c00142d403806840055024030703440030b08580383c00c103071000404054001240d90618800c3d0aa41c003200f4402d04030101e625529140c41d80207001c5e01e80000c02801c200001e0421200764105041d040c000b0f40d0044206c0141e85482c10300c60703c9452805800c11606040780300300f00440400c00850f0454404501105898800003854810305000080100d003420000d0000701c5840c0c402031012460704180c40c004548110b0700201040d40e20700d0b0307011340e140396 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 551789955 1250 551788705 551788723
    0x8100e122212021017061c0f0501021209010c0c0201050307021e1617100c05040f08061506090907080a0b0303031303031527060b0d0515040e0703110a0503 68
    0x2200300402201d0045042041351aa540e004900340344140840080c12240e9002004003110300c1f402d05c2c0c0e001c0405030038010200310030980e005400108201d4540c42e1240c000d602442d9a181c0e0703000c41c180010f01300001409a5207040c0e5083c3e2351107101030401e50054a507031b00054041810360140220174251051198401700c0c8101100009041e200c4030b2882c1c07480b0b50f00703054008070400212102c441e00d001000140305001405981340014a0f0090944110b800d4060342e00b00c201081c0c41000c0014603c40c0c00101c0c00d000c0c0c0781c14440a001c0c0c01046040001034032500300b41c59044034000740041c00303181c047c1700441d80c40802c84101140d900742d0100020f04550013114660552051044c00c6030034141c1c14130450091503100590310b20018180104200d800d00907224281c124801d003003284a070140c15810000040110a2003039440303424000a05020f40300449204440e0702030701c0d070740c01c1c12844c0c940030713042d5425052030180c0303600b5003951030310003404001d518010b03005a180780c2d0005854404010340c80c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 551791205 1250 551789955 551789969
    0x309090203191107030e0d0602120a05040b0f1608100510091a04180e03070c1403060601032306030c0d03170109140a0c11120408100e1222 61
    0x5868202c140d91000c0700c0401c00b03601c1c80030b00180003e4001980080d1001c417040b000f142c840e51101202e160250182c402c0110726511307452000c081c0600d004080d00314034050351180c58620403d541c0c256010340b04050403a0010300c0700c06c4080741407074054014224a0741100110075004040b940307a601241c00179070043d42d880005442880100401480005241652240062550720f1f00d807801c080c5201d0341e84807800ca000499510050b001c600c078420000c813500c10354060b000b100810b1b610070b8510541440150140d009001e80b00004881d903229108845a082c13103010901408511038090345030741c030402041d13141c0500c00d0310040b01341943c40c250503100441c426a141000b08114014030b001c010f030180d04c60013855007015140b80d00801d081e074006502a000310400035569104440881e4030190748402d4584a000e11840c011481d13240710020403e0380d0410040b100c1c1740e001c900408017125105940d5400517003107640710b0012692070f0f800030302200040d290028800c031a16403100501e8801a84410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 551792455 1250 551791205 551791231
    0x10315120c0506030601050f0f090a170c0427020a030204050c03061009030b040305030c070b15040e0f061f0e19060501020309090a020f040806040b060418050c0d0309090203 76
    0x1504005800e10038001030201a10f401e0b08504040001038058045d80c0e442c84811240440c00003c40b00009050326079060380100301e04580c80c0c0d1f9403501d0041c3d000000824080d805045104450740c1014012003003001c60100b000f03050800d0400c0686141a4465003c0341e21070300803a4008056038407801100c0c01a10809140f990700e040a4041114800b401090b01c028040110010030111303039a201d0440c0e0243e01410030554a64480c01c4a4100c2e00c513101c0000d2002c507428060086240700300120410381082034404002d00408541501d6803103140c03202e4860554001000a461b6440d46101d04402c0c16191103007404082c2c86141d407900e120012507401c17582e28921001a8000c0001c5d0291034014502030020318684458a0045a04900010407260b02d440d0002803844101d0104801c40c2e000300764403c00e076241410b00d0b10b4020716001042d1a100c2c0302d213041c040140013584000800c001881c2c0e00000820008200d401400301c0385e03035017a4094040c0300001c3c0000800343c55500040d841002e65100700c3d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 551793705 1250 551792455 551792489
    0x80a1a07170406150e13080d0605030a0c0807060e0d12030e0303070e01080f0103051b130e011406060309060a18060e0c120303010f05060715290915040b010315 70
    0x1c2c014000185c0c8001c043d00404000d000020603926142544550400403255a0700034510386100504038550240b41c05218003450441402080090602983c8034842940c0c0e005507030b01c104030b407540d292024896000303e412540794005030104c5000f9040318010304000c00e43c041070041042c1107400490340500410170901020f803041d0b070b11014269100c9000c8085810f15410342e01e0b06075407034402484d05050b40020500507181a03031b805940000d00001c2c9070301480010a5603145034003801201c510903c00c0740303264010403414500141a07074403a08120b0010a0607644001c810400340c205440190398520a195280c03002c2140c0f4081d100c12800007000502d12802ca2900f84400b00c189944058160741042c00103001c481160b2030780108482080f24807a451351402d0401d400003c05030700e869132605180c000d040a403850711588110044d440c414203105071102c440d041c00041c40c0100c0301082d0b0b40201900b61482894031390720052500300180340c00150585070300b401c0f05014020707420002c652040c1c40c0030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 551794955 1250 551793705 551793731
    0xc1b0204180b070f030c1209050f0d0e090907030f0b04061b091e030c060f0210020a081006140f220602100e010b0612040512030705090109080a1a07170406 68
    0x85492144e40c1454204411401658001d09903a916400c0d035280d10345800d00c0c1420b1200c01c11007800c240b280c00041c1c0790342d0440380c0e2014005d121440c001c2070003030020100150f00d0081c04250881204c6d0400c0c22003809031141c0d500c01401190042c0115030040d07030340111481c18441a0a10b01c83c0328095141d03d0320f86170420001958881000c1090102c8285040c8244001a030701a4010106c45040c202a25600300ca00400d900380650401e0400000c2d1000c1254020140d020240c20301440c200c840d04098140c03030307046c102d0b6401e401d0404400d82c0c1d041001414040389a9000904041c50300a590200d0344000e007400384900384455018000683c40900d50180c4541188503100b001e00000000304802946040070800724042e03507010307440c8441c0c42c4c0e000505020f0240281051049400d54855603480c042e1800703402500515501d40c001180b40c100401c802c100007814a4115400c5903010380d0f409804446050700d00d500400d44020444042c144a0142004100b070501503441008085003030034a0442c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 551796205 1250 551794955 551794967
    0x80a09050405060f0f0102030708030f060f030609061302060c060f190204060915091e060201061706060409061506091d01060f0305040203330a0c1b0204180b07 70
    0x4001d21a0707180109200d21a0307541002002490b03419a0544135807500940140d085001c0c0000250000c800082000481c43c400c00da4036104034800c03914004503c00c440e041c1030f91590121034441c01d0383d02007000300303081c540c948040e04405480241140e1074142c60704410382c146130043d1070a800c2007681c0b005000c100148003107040100f4460b000d0460030180f80c2480100703000380700c4c8500b40c0f00b2005044cd6a115030320484001028001c908d080c8074419184615818007901c0510512006519000000c0f400900122141d012808510f00901e00d54490600700310060200c038404441c9141d1380d80111101c0115000400014607903a01c62103c071929003201c0f141003c40a80110310012014801408055005a51100c4440c1c03a40340014040e80d0f0703031010a103852900c1d00c40c04c2910550340b01885c1410b0600d0407030003c104025007803a085894040c0d0880035030b401401a40c0108418800442c51842c1d220242c1c0d601074001000444c0122180c8030740814041500c000790788080401d4100b104d001d03000a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 551797455 1250 551796205 551796209
    0xa050d0b0f060f09040e060709080613020f010e010207030b011226040e0405030403020d23120f07170309010902280b0d1407020f12030f0a020c03070f080a09 69
    0xa6012000c031081c40001501c10b105580d03035191a9000480c0307840c03003501d455028007101c9602130308440090034240f101402d1040c1ca4882c1c190b5510555000403d94421a10708040311507026120b11a2101130100558946201458a90440c40344a03000404110595800c80c000c115014050b0180609070600300070181d004c0881e4004c0414000d00c68590341d0340039044408840034a42286610340b41c518201c1c1c118403030381d1704c003a51160101051f441800301580745940c0c05041c0404d00480c0c00c030012800d940750f400051a041c000f03841400b14641107001e8400502905204200155000313010000803a901e0b001607600d40d081e40c2d03441c4080340071400c14840006803407c00041c40000340500101e064011442401200c411210200301881c00c0d0445030004002c00b4a00f4004145920340404000d40e00c0101414001c158880d00300084001041e0104881c01081c203400b02d4000ca6840044440203580003040900140c4010007845d00445e40c050320380707034095102e868213561746c000d95400200550403075 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 551798561 1106 551797455 551797459
    0xb06030d0342060e010306050907020a0b19180b090f1c1704060b13090b0f100b0a030609060510050d15051203030118020a0504060e0f060a050d0b 64
    0x40034141e80c2d2003aa000c0040325520740c10070454109c00d43c1d0301c40c09608101c2c0202e006c10840100640c1c0101092100c1120b201010b2100301100c0c010141c40c4c0d544881e00702c0b02400c128600680d01d40141c8090700418040072a407071002d48030384000c440398101c00f40748480d20310404d0091108100e01003c1c00303000b00d014030302802c2c6040900140c4000612031340020005800c211180e126085946400c01049501c1d6502d486041c0629007000c1e04a91030b1240d55400050752480000041c20f13400459600030a402d40b07000501804c1e1030b5550403103403041c0390303800030b082c42951321000303555015410b07070301c0852004480f1412040c80c0e0704541181e6000281490002c6090200100460484511444617015504d10740c81040880c080c0281c6140043d00c100410058035200c3c184507025910001c14030030580000742c002035102e62201041001080d404100e40250001c1d610402c8498642 = true := by decide +kernel

theorem cover : BRFrame.Cov 551618705 551798561 := by
  have h0 := BRFrame.cov_init 551618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 551618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 551618705 ≤ n) (h2 : n < 551798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
