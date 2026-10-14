-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2042
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:30:56.84732+00:00
-- url     : https://prove2.me/submissions/806b7ec9-4d82-4e12-84fb-8b060375920d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 367086330 ≤ n < 367266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 367087580 1250 367086330 367086359
    0x1202070e24012c13051f080a080f03090a02060c0115090b030706050304051501060f02060711060705070f02030102070602040617060109050d1509120311031311060c07 73
    0x38041910a10080340c0d0300540f1011224030034800c40742c020100c0c040040c841c51038410440c8402501a111241c840110807088134800c1d0f5001c28031448145501c5d4404106040070000761004038040e10100c1c00702c0c0d682244074881c4c070650485040e4048009501c64800b402582e036a15006000c050380c0304130400105000b0b007401d064640c8103d20031800843d140001d807040c010581d101070000d20000f07042030030645064000410447ea00d10034425480030b8031007443d0245000b00a65103030f18540d2101d4482c06800c02500034003440800013040150f03411100c0000f401d41d0000f00c0c41c00d00f26650302c9141000f1404d07454203a006901580000f4110040040c0d03030b07004008a81c495681c000c2e201003480c00c00d070b00c9010107072059400503201c200140013a107031001c0c00480e100d1250281e00d100510b2000120240e0b201c0c8801030b204079201e291580081038040c011000c8140e04101c5641c0f8615080c241b0340e80302907081c0700142c00c1941003541c8400c16217078142241c0588550400302d6400b55540e9490804001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 367088830 1250 367087580 367087621
    0xf06090b0c130e0919020d0c090c0f050c0d110703140309040510030302121c050a09020103230c030c1209060901060501080402060306240d15050117041202070e 70
    0x810b0ba4100103240010030020a0095620201810303114100c20300d6085020741c601c4060ba4031800d01709101d000140d541c82004002e051003040400c00b8098a207000e005031200c94003190031b1140c05c111601d48014041000280240f00781064805002a030621515102d038a13003004000e4040096903140812001020308810801128140700c9944c0e81c80340001c04130064030005000d6405401122000807203880540001c00605000c08000f40c0940404825200c0c140c2d10348640c00d81e140d00c400c1c19940d143c01401c4011249a5081c1c5401d419007852158802c8002d00031540268044003091540011904941c1011902030f414040c2d414108141501d5203425561105550703e001e1000400703501902105100d01d80080485080d41d80f50010b100d0316032a107800d2140c1d07602349040a03000010341072000d41041e002c148000a000014664950a0310405030031841c18003800c031000210101400541c5a40558801d006c030b05d20302c20071a410780c541135594100a030700000320020403070824220401c0410b0388 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 367090080 1250 367088830 367088857
    0x708070b07050a0f080a0923060f061c06022a071d0c091f02010911041413062304060c1d2103130305070f080a0f06090b0c 54
    0x1c0e103400c0402c0d01e0603c00c040b0040701042103200706005039400307102104d6000607801400324006c00c441d510480718030310840e0040c0041e003400d6a15402041c3c2001019800b05080c41d6030406801c01c2d0001070071841901c040d000705203024018090401081d5019a007240024000842003101c41c030701c400c10500103100c4c000d441c501c6200300c00541c501c6000c0c5100b100b42000c2c074582c1c015031281c0c0c80c10840380d403009401301d4001400039404803a0742c1c182917522104071610f500000d40d030340b4149003807442503e0040181d440303a8140341407034908010068806421580d02001c42441014034a4580c020784647d44e030b400c1c0c201c42144400d0a520100c810064030881c400c10341000032158010b411b41e1080e00c40480c0c809546c006481307110782814540c00124003540034032065221070540c0000030380340d030b40603171282d101c20b81d109582002000070801498010b02000e0b0540f10841d401c00f02c0176aa1a90907510180c803448601500c4800d1180580c01074a190780c120b603042c0010310346600014020b031f019420490784ca = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 367091330 1250 367090080 367090103
    0xf0a0b01214d030601050d0e16060503071206030b0604050612010504030c06050708100e060105131206060f08060a020d020c0d020d1b03050d05070e1f031b0c0224070807 74
    0x1c40e204000c40c0d04c030300c034141c40c0c4c1d90400740800c04050050040e41c510303102d03610400b0b420035280690208500002c004030341e41c0e00e90f01d29010308001d20706c8111a03009a8000d00313002c001d20004441c06281c1d64040c4043d10009501d5641100180c0001c50b8030400b0440781d480d00040c88281544518611551402541c003401287c80701042101ca201d030499a80c2c1411420000034450b10548500c0b554001c60145042810f207246008130440301515940035032031001c0c210051408000d60b41c000c20000785200118a8111885c2a00c61a180c4c840204002c515507400610750079241d00c2039066401c6200e054084840402d082a0040c0d607031422000074030045030040c61613402e00e03800c1e0324084456980c140e59003410000703000c0a1101801cfd001d401d00007800a40480940241c945000c100c1c69045070880420151200500241c2100c20700d441c11740f494881c2080c40c5003482d07000440f007200c0b1075045e00e0395501110025a81c50050811041510a14400003038820500c42001c001d44030302800341c2d804682 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 367092580 1250 367091330 367091471
    0x30905010c080306090901110c01090b07260712050403030507030e03180f180705030f071d1c0803070c1b05031906140f0a0b0121 57
    0x150014281001030148204000213001820084401c0d60040005400892441c1d1800c0203822150412a19030f101d40e0355480c2a4802d100320307042d00e80d4211440741800c1841070460b59801c54400d2981c1e070520844078002010440041c4901080c071003002c92103008124605107450000c0141c07900741c82c41c60002e801c110488020503004030071107081c040700b1448030b0303000c0548405000710000780d40545944205140aa14649072845c4e00d801d01c42c0072103503260ba5407458a0800c14814a90140800080101000c00182035841c125042030340e0b10800c4800090810320110701e03100218021100405480c4003205001080e500305041140c40c0c0d103c1e1400c0240e40c18150341c845006090ba206203581603101c1503c243c000211400a8990300780a100b021a0350400d0140d00da001031010340d48880550700c3c10041104101d114429928500424a40201e9a452020482c270948400218031525640e54030b582d5500d140d034400903140e842400548650f041400b4a844003000f107182c07078100084000380ca40008 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 367093830 1250 367092580 367092587
    0x6050f06030c1005180a0e1303020607020c010801060c020d060e160509060603071103160f062d0c020c0307080c01030b27040804090212010504150b0708090307030c06090303090501 79
    0x4901c400f2a56909051505100851400031000e01040d0303000403440d540440ca84004201c0c491250007a107000c2d82c405039541c90f00034a00600184000c0c11900001810012a17a100030340e141111010701c2e204009400c03c5c00003c8081601140080003a454401000c01c5070802203451125609800e1080284941d01c000744080d461080f100298052400c20004090074054549250603040080807030341044500085003070b035500c0100040c1e03103d00d820183c0901f00a2280110b030584600303841d02d40303000181c259194140503805e4950041d00c0b42c5400d500c2c0c034003910802140c0504c51006044900032135a401c1400e840b03504503400380b07000904040141c00c0303608101c0b54500392510740c5001514609a19070b58007080000250085500d45c80c00c0100040910300e50025016494804a03844115458801023000301e901c1c108002155522645041150b0700443e41038440d03007a00300e100303a03540d0180c2d1030009003482040e4200401c00e400303e84000c13440b107902c1101e803400c0d41e1294485a03c43e940b24001035 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 367095080 1250 367093830 367093849
    0x80606040915020c1e070e0a05040f0b0c03010509060f01050703030e210408010f0b0d03030b01050d09140601050103380901060507050f010204051c0201090f080c010201050a0e0706180306050f06030c 87
    0x7c8281d101c41c4070104210114503440264000d01a612070240c581c01a078643c0c240301e10585103200c0f0380328084018070803407070505c86070307130704200e046603810341d1140c011380007904900502030042c06041d40c1c1c1070001091a000d01c0307607041000c030703c0d40da00d02010350703000b4400c40b60742017405a00d034150300e058843c0b600441ca900c1148060302f402051800a50342d50394046002d8544400550704208040c0007a01902055000b07005072a440b8008003000031400645103840c040f016440b070b504241c2070940c0361045008100520040910395016000b6590781c80c0b20030300c2100c20320007000d034001114400000f4020381c480050301d0b506200c1c0b000d07500d00030b040415040c20b030b01481c01500e910800050094483c04200c5003804400b61040c1030030042999103408040d03405900c1da001e616141c0140403011300569080c80364a0344946545010404051030840c11559682c140c040e0344244202c2801c0c1d104580352a0710740300f0080d9402802848540341ca1400c50710f40c0802965001e00070310489469507494541003035817 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 367096330 1250 367095080 367095089
    0x23030132010c02130f0f0c020c03010c080705160f1b060c030905120c100f0f0203030f01120f170706060e0403080f060a030611031609080606040915020c1e07 69
    0x407211141c0da15002c110041c90804111076107a65141c1700301d41c00b540705000d1081d00d81c035035500c00a2074170b2200e44043d003080314902183d8400e034503180e60035010903000400b1a811800b985001038480414080038040b2944080700508000010b40c018403c200c00d4030b000c03842c4440c1220016141640d00c0034161491495010010041181c0701014422814560bc405500d041020101d0b1400506680401d1311030600711048000200c410307007a420225000140b40350f146903548001c615601e00002e06a07240b4a0600a034640f100183c41c590060007006006044d410342c00c400c540181c1420040d042215a000340805c407410b5003040f200184110b228440103200e02d40544498409039183e80f1175840c04400280f0f0385e50700441048020000c40c005202d411805581c02d68034035a2400c00e400044180c540c03003946e090400109050038812003001180807904040160390204142d101454012110024581700784646403011604420020300003030004040081c0c91800c0c0510b402a800c2180c031502607004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 367097580 1250 367096330 367096337
    0x6090b070302060a0504020a030b130201030501170316170a0305100b040e04030c051c020604050105100b0412030302281205070f080c040504050c030106180e072303013201 75
    0x81c1350314500e50007455220b440200340b0402603881b5079500300300c00c40c181d03200c0107200d14000c604411543c0620078240074107a081e0746104138011002c0c0040d42c9200e076640c5865109814541502001081910411821811291203481c0d900c4003100400030841103507509894000100b00185441540c4e084609442070b07100c9120255407030f6241074407500341222003240d07140b141c0308240b81510640b10590203140d401340d015006038142414100d00f5241c0260900d5000c10a01e8410010885032200711811100ca030340c0c40d0090207078a4101030703000b0f0050f2800420399203e14940b50f0500920602030461030451615012407407070b1011000c01c01c54504640400c0800c02c017100d5404109c0c02841c40e03a40c403550700240189440d40301ea002c901030321020b403a855542e440220050041c1c1d90403050160309202d244001e695064908003400555000280105081c4a03500d00220440306150541c3c4100c000700903085507495a56040749000001081c001641d014111024041a0800310000001030078051350f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 367098830 1250 367097580 367097593
    0xf0c240112110603070507020901080601080606210105101d070801052e020303240607060b010c0204110910030b061209280c0b2a0c03060103060606090b070302 70
    0xd00c00944081d08401ea4070124602d108500340e550740802035114020603030703809448956510501c40003c006801813281034000c200144140c01c1d000403047e900c027200701c03800c2d480510305c56211044003080060f00c0c2040e500f80410492207442100a0004594100c0d4102c500890100307400305007280103403281c00c0014036140040002d0300c1c08410a07026602c00a9480c1440c2c4031080d4101e43e181e40b411031100140c1c0001c41001140c908140c41c642c5000c14a004011800c0340080000314540b03c0c80f040100025901c05001c448d81e48150902c02c00180d025204201c50a11004044403d802c114020362080350b0082c1803500e001d102c0e00030146040c85c09801642403031162000351007210720007000100c50717104160340d106604c54045840245810140f294289288003030409407180f0700305400000000e0010045e6441442403030803a6176400c0d11802c80c00d030148002403d9107050105802c0e0441c1c3c07520608002006000c1d40b0b611003000c4400b151548801d540e91250061041c0c095148003402582010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 367100080 1250 367098830 367098839
    0xc0f05091f270203100f15140d140f09070f0609030b072f011404050a0f05100204180507031514010c0c0608150f0307030f060f020f0c2401 61
    0x4590340030000b0901030b0341c0900651410003a000ca0b0011102e08400d81e004140c2000000501202c40c400f0300701c0910707040340c030300b01400e000380154007080401d01880b00005510b032603c0c6445d90012141e01840089480e103400c10700ca0000200c03006669001850044110014003452030340c80c4a421208652140000c0314079540b100d401a140082030001805410b030190002d08001403840310030032030400e9403581c4070784103011714508444460032100e103e9858003080c840400c41c000f843e01d4407254007501000d5804100d247c098241a52245180030160000c10b0100d010041c1004000307684880190400c000da948600440c10384400ea07201c104580140c103414040e48014041c800703003160040c18002c240070525554001241da40f41d1081e00050a104144802401c0102d04507090590031a990403003520120002a22600e00d0310006204083d6001031504110407504070316040312650306c0444d205c2140311118500d81d840542d4800150003140740190206220341082c2074000000804104039a080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 367101330 1250 367100080 367100099
    0x8010609030f0503130609090e030304080405040509070509070302070b1b0a1409030d2a0b0a020702040b0405010e010e0a02030c0a0c0f050f011a0306090d0e0d0c0f05091f 75
    0x18040207032241d0008100ba0900d800d40610390704018116a525035421070700c1d00c9241000c41c0d427901030030103040e0400c0050001040d034120990f004d60380c08841c00500c1d902c440b00124541318071603214039080303482da20800c410035400d1b03806000124020102000a44e940c040508110700038600e182031030ba6030600107107038182c0c46040308000c500302d59219603103881070b15000689025943d280f0340d4001800c0c02049480501d41c403608841c51071400c40341c0410381002c2d560f0b00c0d040c6000108a0b907001e42e40405c900055550340e802941c620f407006402045156100d640d2072080c01c800340510302200000801203a4406003e2084910400a9100c0c29043c8507810600701c540c2d10f103040301035401c0c560005184002c036405120010010808500000b042c48541e0181107102403140c803100c3c800d4110324100407415001094000000e0310a140c403003442442c0100042c02900e00840c0640100d0010700007040d4400005810b1007a1003045407044003503a81c07500100308491380841d0482102d0209602003102c03000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 367102580 1250 367101330 367101353
    0x31e030304060c090e0a06060905010806030705040f0605090c1e0f03040308130204020d2705120a03060f0b0c060a05060d02011101020d0c080415021e09150c0c090105010801060903 79
    0x12518012103156558401c1000e0b0405c2130703030020f140c1580c0e2075080200c0f40d041810440140000e083c4540f8070b00d800400291282c100d4403a01d40125243c0c048566a40c034154400c6025050017400c00d032050500348008411a00401c0380b0078032070102c5011003107402c00c42c1410b48244070030b4403035490f1459513a0742e001c60301044c0280c1051105104000320b040103940302e0014000602c0c01c2100000c00012107403881b4a07440e0302043e00034a0313028090b4448082000403810484900801c45042d6440c9202941100186070a030300004113014000004100042188010001402404102c40542d2070b1901c01008841b015104554020000c0030690010750255a180500383c2c9841c00060400014800400a0b03640410712240061909004c000401c0030351544031088220410017141810381410400f0040540310b43e904c1001070000ca4803206541d50420560010012600b81d5a03c548103c5c00302a0740e92102c100c03203407103080640d00105055105040c00c81c1295280d035951283c1030300e1503e56031540300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 367103830 1250 367102580 367102601
    0xb03151308090d03020f0114060114090a12030903060f0b21120a0207260c1903020d080306090a1517010b0a030804080607050a08221709031e03030406 66
    0x71090000c2e0707940c0ea0761141d410010034029000b400b21140f4010005084480503018901c00d403070510140071302c0f80d0b40100002c07403090302c40c084180c0c0c1e202800002846083c5c1a030121820880c00c50b1a0020142c2c00a1458200d91141100303200e900700031840301068030707665540150043e010b10240d41c80b42d000040c130000b04d000c1c820282c0d41030007101407014090303a1028054501582c03112404002c0c1031740603a4000d103085e08042c445082c18444080740c544890b100080603202d803041c10f0300360088100c80000c1c2d4004540c010986c10f081c096910704610315410482e2198070640c0c001000480c01000c501440394240082022584440d01304400c40c030340d6030605800c111070343d9030f503200010440d01e59140d190055402422241d4480c0d00e49004103142800003004a02045010300114840b680c0151039160081a120081100321025502c1516400300b0b000010f00301d000701c01400e4081d815102c0061862035400e9069a10a190300c8410030b03081c80690505002c658002c100140210707440d6030105c203080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 367105080 1250 367103830 367103843
    0x90807241b05010218040b09041b0803040e0a0b101205190216061d07031203110a0c02100504050f0906030a050a121b0b0a1d030c0307060b031513 64
    0x14411440d003104031500d00745003140c06a40c002003051031948100100411354004403420b010890503140811040b41300503100911581403001d100011504044205000d403101d10102e94855603501d01886540a003668015503c51600e664207031681445202401644116281d0b00e05400d00c80070b54000404000b000c2840142103001d580c040c041140c00141348069800b800e03054202c109040c001d08070740050906150320f22002c14603030400710b00881d4500440f500451400004c01d0282c200b580940311240c0c400f690303840000351000095402c039805e0300c0e00c64020350300d8a0034202000420f6440381714502034998043c0b9041d544540c3d81c9030549081d0b5100501905580e0b4003c06560f80d949040c0540600326260f0a141070099030480d030041945180403441041003009600070703154098146000b800c10700c282030302c8940300324011094048441ca00d290360421203130340311484818940c0703a422240c42200c0d454105481d441c441c1c54006214100c0d01c0c19103240228039103c1c1500c111860000c06401c9030792 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 367106330 1250 367105080 367105097
    0x22a0d030614091f0503010906240f0b07020402120a05090f0304081005040804080f2103010302061204050a0b1003031107080304060c060b0303040b07060c0f05090f0102010902030a050a0309080724 86
    0xa58600703000d62322010b40310b08404030301700700000b92004640c0600b0503152285903041004021140102c1c0d07540302101c00090109a9070002400890301901c1020a468402d20241050008620f6590301c183d10a9402c0c50039903000c1d000d101d914a80740c0c0300b2440740811550107689501d040c0b11036a48281d81040c460005103103055583c000c0d65082c01180000114281c1080c00c03401880071284a080e5188902c905250b4503640c1154001003c0b4000c0c1d0001c0317600b0b0022180000c0030003000b000f88182450300700280d1000703072410074100354007030320180000c80c009080e01d204c0e20b2603030300006405419690120055403c141c100003084a10300400356094034041d8031403403503071001d0f10240f0083c40600750142c2a1507803480c450a02006942061004408204505510b200e800354401c00317030348c00c0d800200d900c080b4088202d80103c1c050030038600069818090700300020b007000f80009101c0112807281d202d01c2044c9545880c5c864a460152081c100011891200c003910b903802a0130302e1246c0072a90030001031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 367107580 1250 367106330 367106339
    0x1c0b0f060315030a170c191a0402062b0c11060c0c031e030105040c0f02070501031e020d0e06090a0c030f150c02070503070f03080d022a0d030614091f 66
    0x8000c001c0000083d0002c4001001e50307118005000c07c14a0810724804078541005070341d01c41d50b000d0022000c01140c07440881c003140031965000d044902e5402d070030314491441c035034005000700080070301d402c0c104000e8a401e00603481c03940103070a144002d24410000d42040e13a101c26074854598800300400106010812001c1004140030051440369144a04c0d20398a03507040ca02401b0480c1d1032141084248040f1003c02c1e0f4105600080f541c0070f980b420b00c0d000c0346509003144000d0304c01c0081c40030901c40c6400494114100c0340c0e00c1d0301c1106501c14050031108107440d10900e064581049841c080c008408100c0280041204030740d010800340d224004aa8004400000b0f203012103001000c10001600810410403440c90200b10441c05001d07000c02c543c40683ca180d881181522956031241c1c101c54000c180390443c07201c2d424420402c07080080107512405251100c03a0303111502140510b011a2a01d1804a071707501303101c240754a81e46d102030940541d0f5250029244581011481511262400c4000c08075 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 367108830 1250 367107580 367107593
    0x50d1d07180b130f0e250608090309010e04060b0d0b040605060406091707051206040c06050307090302011b0c031a090705010c02011d1c03110a030c0b0c0d021c0b0f060315030a 77
    0x160b02281d0310807007030101d40106c0fa405910310965100c041040b001d40188080d180001c0100c40300c08109003408082c9054000c04500035050f15840301e03040d124045907100041450790000e82c90000111400c00030140c0740c0c0700304851400350f4001d1400040f4650424410820304010150b054a030003400c50345400d5840c0002200354482031001f50a41e04500144410040030440a50291480381071450a40c41c103038070010071a206520020341080f9009054076850311610381d100d8070850f08049550105526402c085883e403054030008030550038847c00088480c08003280010030782e0016550248042c190f50011214444200300c520108003042501401c26543d01d030351900f040c0100e003440d02a2140c141000760150100141409850300034501c0340780085c2d81f06050764105039210051107119118640f01450500990041c600080e10000d501c1f54408080031a101402d80030b86000d112580e44102800000104403071a59041031090020486850001103c03095158010b402c03550f0204071500c909 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 367110080 1250 367108830 367108843
    0x20405030715080901060515130e070f020d030b0a0506031f081608010e030a111203091605030102070308040605060d08070b01050f0a15050d1d07180b130f0e 69
    0x1028815000b8911490382c0c100080c2a40500000001c1100c4ca05e0440491003d481d035611100120800043c40a002000303d0507020180c4818600c801c00c614200002414581e0040040c0c00503128030031080d5061440380c0685a2112409407800e8100ca00e440e05000d107940028003050b06c10051207d100c401000d200090394010a00340b001031050309140c0b5020440103542d50807080c61039040c0829007100c031a0000840c3d00c0451a443c00da8a4201c1049031181882c111000140a03075000100307024100c2800106943c214481e10340401c491503440341014203d20400000901050030080010003003030f0300c3c0d0700c1260311a0000c1c012003100c401c2da944004140d40501c404484e82c00619005000c542400d00842d0700751441601e0380d80449082c0f14055500c088480c0c0410101300c80001e000c07440d51525000f0b140c003000144240b020702c0ca4601080c649032121401040059041c4107030103104d040c5103004903484510003400c0d44c542d41f44000684009440e81da01030f50441d0781c481c44054001002000351 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 367111330 1250 367110080 367110089
    0xf030f0905060601090b09011b060603020d0b071e201f09060b030a02150c4801050417030f040e220305090108060f040509010f051305060106080a0204050307 69
    0x90b00852070800005000d1842c42d80050030266001d100348070450740c01582502032140e07a100c03000302c0841e59140580250440c0d0708001c2d04084201a96070400168108403401650151201045000c40544600298821180981c0000c65001783c026080309510603084074000070009a8482c8080302c200401c07580e04408d5006039240c0c0d02e145030340501c006481840710604c1c0c110043d0088015540000d483c50000c50015108039a00007040148000c04115281169501031a03402490324001c044041110489a0381060310100a0303501800114103001107901c840c05845441c2000d0078144d105101203610034503e040c43c4820440d503401c416801010380300070f0183c2c4e51000d019141c02e540ca0481d40b2484d5142c0300b501c043e4002403000098001c01514050042803810110903940d49002441c0e294140c20f005410034500028071040f090190040a8030341010700d001c0c07115448501c1c001010906a0001412541102c030050000c0d034401e9405030f400c4640c1c3c68000d8101510ba8000a0418410307601 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 367112580 1250 367111330 367111333
    0x40f020a11070801022a030c120d0518030a12020903100e1204050105070f0602070b10090e03070f0b0c07080d090627063204020319030207060f030f0905 67
    0x100310070074104008031000790078400000d6017058202c051b24982d5189640c0c000b40305400700c5d05c3e5240485801c1087d18150b0041408890140318881081d088650118141552850428001034400300304107013005006102d5100031454400c42c0102140d91784e01c5442078850040c5c0030480c3c5000c5030b40c00c20228440705c07030b4090300085132a1800342c80380c07a20801c03800e113801000c4c05110130401780c0e80010648010301d0704050f141d14114180d260040091184500003010007040b00240640003c815a01809442c0300746000c1100d0580c2c01d4480d50389010b150801440c280c4803d044138005034280b03140f160030110346c06906013400c03103d5941c13030040d40000d9540800345a90384020070600c1103074018010b8082d217442184139035a02c1c40c03150060314240030030054001a2590380e4003040080b4000705290107416120f5214004942c145454074007502550241e00c01d105c0e003040225610703602840020701c1c075415002031400345d10702042552246514039040007070590303a03001031004034514064090554460390 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 367113830 1250 367112580 367112597
    0x309010e150a060608010e06010509041e06230d0f020307210b0c0406050922020f03010f0e070909180209010815070203040503030a0c02060d140103201c02040f020a 72
    0x90164003124551383c08101040121001000b0f0300d603410220980011080c42c0c400c2c2d1f0303091040e020401500c04009444003455003841c00141100c6a548080c094481e030410410041e04103c410803070505181154070340c03161143c825400010b20000400d0803442c409002c0e10803c0e59589400003094030000078907802c2801c40d0b03417000104000110090b61041601c40511308081c109003004201d4005d1030101c6004050180c15032103607803010228111000e9004001359510707141003001d071401ea0401e210703c0c040541220404544862070b10a003d00c1180c282c0e542221040ca03011070322001d0a03403a40040c0310713120015480805615004042c901a092120080044102000018114640090049007150003c3c03009000076a0007200311601e2109904e040548030209000007500303172103854100d00c500e51800c00d98401022507003c1250480740200c00742e0201c03800d0203100b50300084020402660104000320694441e90119000c6984640043c0c0b0020f4100074181e00c0703800b00da2054014901298110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 367115080 1250 367113830 367113841
    0x5100f030c081303080a1506091701060b1e1c02030f090604150c05250201020d030b0907030f020714010506030d031407080c0f2703011e020309010e15 66
    0x14000e0503442181d514104005180ca414400a1800030210040c200305020000c40d0384a200758200c80607200c03500b809080c0042d55550040d06440e0340707100384c00c004e811078601a00404c0c0188070b91421104003e4a152400d035400301c0314541d20340c1611201a02c924240200c421031921120242c6101243c42c000507520301f08900ca1820380c42000304070003906e6110000f00b200083c260118a41d102500c00f03404103c91569003419102405502020f4a009040403480000d900c0403194580c00e0324001e03001d8600c42001d4000407801e40e50900c0d456900601e0807000300f011188290f10564902501903001418554036a1320740c0034480000c01d0102d400c5c2e4441d41402101d1905010069000c08981002c000c96901c4410032145540000c1c806000c0c003540a0018600480010455221303945000089a941207540110013550840d940f460a030b0410a02d0b2035049801d0500c103082c00b417110b104030040508000d0301100080c0d44010300150455488440c40c1a256408100058188200c0764030441a0b1a11 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 367116330 1250 367115080 367115087
    0xa08070201170a1514010e060a20060703051006020307020108150d050714031506040518030c070f05060f07061d0f0601031a0f0f061503070f0e010806210705100f 71
    0xa541142e80f603170581c00380c54240d9a07001040d802c0c80c5c0d9010303a1550b48074051440107803860070031112051000919041110042e51012501b144541c0c01510100f284c0d440d04103005420650f00e02408016a20401500340558001c14449030f00c01e400216a00f048148600070541750380f42110115050703405084c051081c4601c0c4140c00e178003e2425030080a4003010a0003407110160060044c600580c1e0b118013081c903c1c21a003c01c2008520a03000303c030b603142c1c400e59800c0e03514400752140f60521040c548006c0340628007482100c8481c2c070442d00007400c001007501e40c600101840d41c4502c100d5030703803c22071842e00e070b0061200360305080707010000d0180c3c0d43c0346081c0728041d01003a40c26003003800e00d01020005c8240000c1007585d081401c0001d68402645d8150200b5101d0300c0090304001e40080220804c0b01107540038040103070b4282c0c265a000b80f080084001547c41c04002d82c4d000703a00001081c0c0743d0b00c0095410342a109541500c1003220315041c0d9550100740c0380460034009000182a5258040c0201d40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 367117580 1250 367116330 367116371
    0x5010c0e040c0c0809030307080a1713080a030506040e1014011202090103080307020f06011202010e01140d020703090b0a020c120606101215180c02010501080a08070201170a 76
    0xc1036909124401c24282c0080c450034120600071310001c0041544000c41e00d04105840449501c240d030315950f60300942c0c2c00340041020321002d1200c7d9a0b0840099942128011030104540d8410342503820309004c11001e4000d0100280316035041961010000f100d030104000950381340246103130001b140c100c910307002005168142c00c0035040c0c8107a01c1440c00180c4421000c241100d8000006d541c07682c403088001c0781405105114507009100b040c0010805404035191501001e00c01d0f00c50791100c0c85010015505114141003049000c01e052101008042041d00140145440b034a08240345075210449100190040040840181d10000701a070f480d081142a45a12900d440d00411042c98601d0004041c400c1a503140d00c100404a40307401052521307600300c072041c02150594140710719200d500350441d0400700c6190030601070034642510210390062042d54141c818003c05000101d5080c0c5070152a5400014100d04001d105000d1620000f08561401c0c004c10310703007402061880743c0300300c4840c20381e2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 367118830 1250 367117580 367117607
    0x90b0c0310051207030f031b050d08090a032c0409080405030106050315010501140403020607060902031002070b160917010501050f1e090406020405100203070b0a0b06030103062705010c 81
    0x2043d8818070036000c0c10001e68032084986c80568401d040c503280c51b0444800a07070001c0810407011180d03071007080040c0421945403a841a0755403840c1560760184940c2d469000500c0030300450f0b20710b001400c007000c0001084005c921110a10030b1f03802c0180e0081000c50f400c00b94150754210700440e083c4500c5c6028000c10005140850052520120800c580060b000f01842000d0500c03030342038100ca038860100c00685009580081c4981d031035640c43d0070104050003085108074802d009603a00f98028118601c01d4520064201310122a00e40c2c038441401c080d512500e4907035040c0101001c0008000071940100340510301c21900100d00c552401c0244440301002103a040d00c03408515a80e1021410710312841e0245090482e0003500e5078a0700c0c20101300a1145401c21034010440e5040c034200290000010004c40c2c0c80740c1081180e80d07452440100446000018040c2d00460800040011a45540165013242030004194034010540c0d1010441d02c41c54032021210799442d401d52508003a0440981250303070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 367120080 1250 367118830 367118839
    0x6030114010e2202060705060f1014010c020414071806090e060405060a030203010c0216050a03080301030f050f190b0907051c0611070311191205070501090b0c031005 73
    0x19410901000314203540103140c0d034809070f8032074001d24040a0000080301010380203400707240c0d03610072400d00355291036085400032540342c0c001c1c01045084a250355003034101c940040c03111084001e40001101c41c080050402c0c0c2c0c0c8140c44000415264503026001c40c00b442c8a5244c40306003c1d6040c14014403660f20340e0124060203410300d410001159440c0c11a039201b04210303400a11b594500000600c0e0500c40e400c06905503107844292950140c0000d003020b42003200c0d4a82c1c1521a5031041048115070050100074000350080c00101b00107507940c400c2041c21845982511030302182c069005d841e04c116404c7c040741280d400c04026090000f00021b10b500240d0000113003407483d05020108400005540d400100422401454002d01c580c0c7e500c590341c0c0104290b403055031117640f130500519190404019084a000b050302501c0714100d24074a8960050b0711003602d01d071018208406440326002244262115500c07160844006226000c603140701d01107075000d140d141d040850124440c2031071900324074001c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 367121330 1250 367120080 367120121
    0x302150a08070e0111070b0a181d18121c020705060f0c0c0f03040906061d0108040f0b310b01030b04030e120307060c0323101d060301 59
    0x681c48001140d001046041c190300c0002458012550013a035112100202e0180710008580e00380858002e000e51039a65880300d521a2401885402104a0b0b100d46401c11144070820b20f0a45004030520f540440d1606500c1c80c070680f200e50780350401e2401c401c46103401600040c11654100501a81d04003007000100450030012540e41380c07a6038290107010300041c048070100150010440c0003c0312182080c1400344c0c1d90b00f00110280558a40050007101e107101d040210105545108040c40c054200e81c1000f082c491140707440054230300c0d5401900540d10070402d201400081400b4120480c05031204841c0b0004c1400e04000320b48494034800b80c2c150000e80389400c25000300f8404d02e0514103581e00702c103c420a42d02c0b140703415603009084a00058003c0702c03240c100303069844003101070320845004590034031140c49001c20480403558100348442c0503044040403040b00012424045602c07a40601c2d1401089840d100d0400c804100c0c80c1c0c202d0035480c803400400090303007403c0c0100104030f2030351140b00b800d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 367122580 1250 367121330 367121347
    0x40305060717161223010302100c050709020f040e070c020406080c030c0f04020c06042301020a050301150c02041107060609090803060d0309121202060f010302010e01180504050907030215 82
    0x3500402c44020f0700b045065220000404500c0d402142c1144010510581030100f2280c08a02c4000034402a032080c144010901010b60240007200f014640c0207019000f17203410111040c1c000e420210b4200c51a482c10701001c02e041030000c03036640c0070b45101e490341c3c8012402c0c0d104020684000f904400b50075000a44111a40d40f8002006416044111030b841700c0344000300041002401003554200241c41403034140028001c28402d00503610160410060126400348a280d0030b1f03105005c140d40000d40d003080108110225104003c40c1040075103844c0360b4400b640d400040c15500032582d510b03652400007943c40100203951140c48014481d030501880748460300d4135400703050301000701064003a0305510700501c1014402d030744c3ca0018006000d003c1200c01200d09019550801c1d680206001d845842e011485041c2d60030704a9040b03940c16901c900b00800e0b040d00464000e042100300301c408103040040070455075698002d44d0300c10107044004204082c0f541c0104840400982080740c1240300421481d03c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 367123830 1250 367122580 367122601
    0xd111902070f061b1208070f091208030601020f062401140a050f0c070e040b0106020a0c261b1c0c03170d1a0102010506030c0d06050c040506040305060717 68
    0x2070880795a1304200d8124440d4103540f55000e030301842d00500503200100c0c40105a50094070b4240600741d241c0d02c42c0d000802008080c0c865030224002c0710b901030710304036500c000200c04100451303101d6018030544119000c4030341018a0181f0995070100c0c40303940c9880750810403d00e03001d40d800c0d03020240380c5010840000320918505101e60710700141040300c006100303904a0124000c550004203144110341754680c2d141c80001900d101078800f21828003c250002810074070010b08403a806801640c0d45150602c4c0191961910b992481c10309401c030b5030103c1c1968001018058040b9590034102c040c1100c00d06402004a0070495030b02031540740d642041c500d804190741000703007025694444400606442250b890100d5409180c100c0f94410781840e14a450629841c1d810861400017a0004d00150310340f002016200c0100800701508a503505d10700750040b4402d50480b40d003000004458918040d2203501141c81030740980c005032100c0c0d00200a000040c1d03400700782e000003402c81c0801e065513401d111072400c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 367125080 1250 367123830 367123859
    0x2010c06180215120a050a150803042603030a050601030e07060908060901140c0c01140411040b0a060c02190302090f1008121c0b04050901090201020f0a02031507050d11190207 77
    0x80170340702e5696000070b010819560040411008400446219554440304203a40754400c0c0200f6443c86e006000c1104040100c2410340c1e80021700f179001e14115a80c203000701009010003440c042c10180c880c0035406114000f4040c050180842eaa16488024180701784245006400341040da10740c1e1422a945404846e91004150425540d8100903a03d80d1100c41c491701405800c68040340c44209042072004101c1d4070302d034080e0034000c180c40c180711410340b02040020034010343c0306050200d5803842c0d07050300502e01910425a0203105030203c6040030f8583d004034035600c50813a00102500d20740b4007440400301e258101100104155801402c0b2800850384201160050580340380040341b42c41083d00700740071907400914078080b0207041040a498512901400b0700b2035084141c7c054082c071440459007400110340e0200c100d401a0042514050b061501507968034020a4601041014050034015440c80c1c02448100304400c00d00035156003044000c0b1401c41c0c008803c075815588031447c2000b0610500301132 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 367126330 1250 367125080 367125091
    0x50603090c01450b16140f0c06130305070b030603060108010e03090120060910230402220f1a060a0917120f0d11030405030304020d02010c0618021512 66
    0x200e4640480540b82d0618140482d00030318030321800401ea03545014129170610101e14010010340e198594284044d0391101844041411503402c023002040c3d03517046c8107008001840054042240c0103581c1e4549034104456a000422251000014060f1038030b070412885014001550007001451a0800e0280d0780b44170b0403048a040c046100808402e041190242c41d003036190307410a81d401450041180ea41300c1c030038085a420624580100b280c45401107000d0f1045d000c101c0415283c5070b855036004c0064110941c0e410113440e20b0501c0038281d040000c0d010702e81c04040b00c4003011403900110010b00901429050f040e6018000c140503508605134024100d60450360414080003034814281696414005580d0302000407060003c2c046e03010b020418001d000c4408020703c10810308501241240d041d1200351000741543e482840420301500e820030b1202d11712441414140045862581d403442907414024122082c122001c40560940c24155140d014100d90082514074103a81114040c40401c0050003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 367127580 1250 367126330 367126427
    0x10f14130f02010c1406060102010606050901090b0f130308030901050604050c030a0e0f16090605010905030a03030c0302120c0a0f03020307020a0308131403030907080304050a03030509010306050603090c01 90
    0x1001c40640e409488034070308035908412036051000389842c13480c4d50f4a8040d00e210b40150710340480064502c1c841c400381d41d4000d4050307641e0314016150510402954006558050b444601048006c2c118620b030003401004503c644100d07501e0b0318000340c07034030708441000740003500803820f00c0100015404440e00312503000222440025520039002201450800500f28104071807140c01c034442804082440e10034111a2490700c240031141c0c0741e13401103c00b14a184074094069014141c12400240241c00400b0085800d10700142007100303d0500164007901035a900122041c0061104d003929804264481180e00d58202035242d820074020003035681c03288880207010050384c000030840743c0904114040c0d040c2e800c121250030b00909030300850340725401650680c2241c41071000001b000c02c00402581c049a20082c890088186143c409032141ea0000b516030b03040542d10540850b6031b81d40c450180d13028841c0900104a45941c071000504110740c101c440c140d605a40c00444c0b0090001000e4070340602031410b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 367128830 1250 367127580 367127603
    0x21f02130305010c2f030a08091006060f030509012906070b090303160206010807090b1234080c010e0102031204030f1e090b0921010f1413 61
    0x800c40c1240850750001000e5509201c051081c9584c849002807210f50b220400c01c0540d0440d0241d00d00da144043c05100f10b540040c04295403003402003121681c404641d006a40c410b154281c40c1e041201e0321500480042031500003004501030b418407a49a00580500003000395000685041e860344d62448080c00741c440c240d12010f0a2511510241c80040c1d510822846450a1800e105a03e98100320340a02d004032194649030f03402440060039a0403196000c000d0010fa0307003030440d188080c0c401000c08a070071041d03141284000364410080001e900800a40c0010980411401c501c1d5010384502045090815038105114001c0081600c019482c42401d20465541c1303e4801030f8258095a0300c0508240d1081c400c101c01c0c1504610a000300c0809940c6184200c0306010041c04840148445000010700c1c5103c00c0c8500b200c2d610013441c00703880c000c01c0640318000c102e07400d030f803500780f60034007080a6515424200c40e40e031441e020302c000c0c06c0441ca4003241e1a10b4a070628000314800841c0c043d045001c80c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 367130080 1250 367128830 367128847
    0x70e0d1104180804030b060102120d09140f1b010201150b0304050c0a0321030c020a0212160b090f1002061b120103081c0605010c0f0602041706040c0501021f02 70
    0x7640800c8503010040711500e01e186583c20110f1041e00180300c10b883d00c034102e07400a0311961020490f041120a070240030f41c14000100c0020001340a4070001f120024004540079812a0b030030001c40c5020004100200a804c0c1400c4c004181c1c014a0800907055a05040c2c81d051189000c181190541d402c2421007a141d59035410210702d4003407040c1a99402c1031070400007005120b00c110300705140b00500c84607404002d1006400710102e0301c0c0704407024016042010f4920043c81c5c401d00d0407041482400c2211b1080300d849142c800405100d51088008543c0080c030856a81860400d000760b59004807000c018a9009541c041d44031000180710200b10f400c802101c00c0500041c106940c90002652451451984c49250000d441e81c008a0011102d103e8407076218030a0405003c1c0f9415124103071745032400d01105039034042c40712242d0042140c442c0d80901c0045420b40000340119020051000249841d0402c1c1c20070a20898040d00b06074119001400d880d00c0440031007030602c0c0c1d280c21200005030b0303940c0c41 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 367131330 1250 367130080 367130089
    0x8060a05090a0f05180c010e15070311010c020708010608151b07060207030905090a0921020a0b0f1008010908041502010e010e0318030610090b36070e0d11 68
    0xa03c10b007a524586024480d045c070200e004d03030f0000a1804111008044020010b641922019104950010a00000301c04503045100a4400d9902c241040728241c54843c0c0c803503096900d600c2e500c00042e4044d61003001000c00074003441d801018148082e200d202c01d10719a800c0398080081001d0308070389080305c0c030820302003158003240c8e0140d030411011500e4070307003528005040c45640e1080c50b100c2c0340c0201c00700c0c040d690030340314400701c05500c0311100c282030a00c1204c0c2809486a07050030010360052484520116202000380351058030510b8100700c0c103242c1900c142c1d01d00700751508070448580c5802c00c3c090000d55a00100c5003030b0780c0c0c1b0000c00c001001d41084100d015113804002c401c242d508100c001002241b00101525038055071b161007c04113644401855074900d0102c49580410460f030500700800211580300c8150040e01600c12036070340e0703050400c90361240300803600c90788003490921b140002c2030241c00366950010820701d0040200b17400840069080c03078060001030681890000c0244c0d003940d8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 367132580 1250 367131330 367131341
    0x10030504030c080403060f1116112107031208070f031505131a060a020c040f11070503190f0c0210050d0c0302191b080705010b040f021908060a05090a 66
    0x6019190b50756132512454080090171280e5055450642084800111840503805507a03030a00040030b0100d511901da101c0309407a80d4003181c07460b0002607044242d4a000d800c4440c00000800000081200501d036142600c206071900d103444c0100310100c410300490580c444111410944585004156044809600302c801000b0394091a4840c4011b034082840c3d10341c5800160200501c5010b507058027505605024880c490315903401c0061b0000d05c2c5980c982d180c994400010384c800b207140007540f4040201050a25882407006075840d500100d0003181048100683c402d13042c2480ca002580c03001c0ca220060301020507010024815880d241b95111528411002d548400445040c2880745c03829a450140c001d6100718000303a81251f0800c1605c5070a4080d01d20144c1c10440724124a15008454581e01c2094000d140304890340d548ada00d62681e20f903a540210307911021040d000503039816074000ca002603880411964800c0c4649007040100355641c110301349040f564160b41e8080969215102e8000800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 367133830 1250 367132580 367132583
    0x180207082b050a0515010203040513020c12130e01060912030c020f030304060903030e040c1e030209040501060306090f0b01050a030e03160c06140c070302011103090406170c0406030210030504030c 86
    0x518080402200070440e130040d03801152603030464202034941500480c0c0360711a60044540046410382802190501d40d401004d8050405041d11707113a40003c6c0c9030b00c49982c800d816803409c080c001d0105002100e24402c80d10300402a6007041001a4075000144132030031484203014003030240c80c80581c01551260702d03030308440010080541c0d40c0c490702d4140c0501003a00c01d01040c0c00040010307410520070704040c42886c00300b50701601e1b0110368000004024096041c001c3c01c003420107800384450038040c0c07581d004207400307003009403000314084c0d00781081101116540c204586400b07041c403000c5003450b60450120394020703400703280c042010b0301d02c891200c1c51442100103440100c000701408009100e280c0c001002640e0071681d81c21445541d20141c44c0e2980907984032202c1981022034108015070189071b207509002c0700c5005136421300b80e107600090200c1d00c1941c0066000d40d8030144500d184c60090010100c21101120100145400d40c3c000c5000720382d100d0a4082410ba0f80c2c40810141030145405c1254203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 367135080 1250 367133830 367133917
    0x40305190f0b093a020f06060906010c12050a0e030109020a03081806120106020c090115181707031103031606021602030f01020a090e04151518020418020708 69
    0x403240280d594502c51300d541c105008032000000c44500c0030b101090440e045d504040c001c006a80f110420084c3d41c860103443c003414070190800000020f450400703030340007420103501c50307d03102d00150034040c28814001d803c1c0c0744264545030090b801070303130348a211606403908440b00030344901152174922482104c3c07259807584040e01251104003120185482c9058603615800d55017100e890605011b080d080a01910074884d605240150b8030700d200e0100c445040f00000d44d405e08041d501e02c035206c0c2c3c0001418a000854011820510920100802c1c004003858180c00071468890078590306101e101840350020301e929000140d04141c0700c21460001829038005064032144440301151324000d52120072494003180b84c8090002e81050b48032030b1035200e590858500340b4042101400d180040810414200c0c92031271510002c40c40041d189555180b22070400c0d40180e9881c1480240c1001c100018600c000300760041104000003988102911100c3d6a01081d04c0050860244c01a00e09020101042050f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 367136330 1250 367135080 367135123
    0x1106180309060c0f100204120b0a110a0f0f051305150408070b030f091605041e050903090102010609020405060f0c1203070309021903120c02190b040305190f0b09 71
    0x103d1004500da80b285040c0e18104c0d040310704050070f6801a806984225044801c0801e20a80810071400740d0700d48c05803140000040a5a1b130f03900b0230882e50460b03240721001a040170f10500101e50040c00300e004c11080c0d41011820100d2a1b2a10b011210540c01020b0107030f4100b4090300741410b05607003910040d14008042d5030720030303840c0c00b070340c0b6482d400407224032480e10f449201150500c0720110f000e903030005414400e071a0700d41c20b003401d20000c0c1c24a09840b60300b07a98a1076052041140750b200f2103000b800c02401540c4c1e00d1003400b000901350313070450304122602481040100525650002160791440c40b480303407242c0343c038108201c0b44d0924100503011440c20380c00004000c1000e5040c0e110031110f6100b15961a58800380c40141081c1840b2808000c00e0810305e000d101034094010b4100070744961006108542102e0381440400101480364001c0c00da1100200c0c0c140308001080c407180b0344121f00c0300c000403170448494652454a403403809000d0110002c610100d02c86150503c0700780d41101e0070411316000d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 367137580 1250 367136330 367136347
    0x1801050c101407050405060301030f02060c060403020705030c09010f0509070c060c0302041703030603070614070510090c080f060a110408031308010501061b021e090a1a01110618030906 81
    0x30307005410141d08005a002c0001d0002c5020301c09503016240c0141080341140c1c2103555500341c11803010401c0e83c1c89401840180c84a0804106d0180318a100350f010700f0722140703400705040c91301e0301007641c00e0301c9004501c3c0180020146080007501b102c07021902c1c44415200c48000b69141d42008501400b0035090040485200e038160b0024070407964208804081234108201103516408141caa0f980d051f04801800c001552145e03000804400e4455106031405509aa40c58542303c502042e02030714030344420424007030002170804d06004000c000043e0012058111295450700c03401421507081503600c4862440c800c450300306490280c80640200ca54448091008462046c01842402500c1d0b01303000010445620690b1074030028400c07408808041d84081d401c2018034001014083d80e54242042100c0e842da0b0351400940c002c0150940009090000b0102d15402c16145803000d23040c0400d4610f0003201c100001009036002c2c1205454820b00002d40c03500504611602c1841c5a110302c0c007140480 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 367138830 1250 367137580 367137613
    0x3902091003020f0d0305030f090f0106030506010e0a05070207270c050304060f1512080706020f0714030301061b1407170105011a0a0c030201060f030807060509121801050c 75
    0x107890080711610450030700d14080040c40b003582e01e8014009003003807001c206070968142c0150b8100140c0f0381500d241484d109102421540079a000351800c0d400500104100c0d80310754209504800010424002440d01e0080607640340700310311801c0c5503a03000c0c140e00ca4801407070342d100310003080d04618107014014012100038400e80055a05403038151400d201000400740f90700c10003d4030070110301c2050100d807400060b0100158001015103280c8410000440080c1c0d50744020041100c901c60f0403a1a1655801c104600c10080c2c1440e07000d03a4020801484556000078404507a4031001840d841e0290703241c0f0b4100c10000d41a0313050380c503510410001141c0060704800400c00990803070004c1199a070ba407540c03803501400354482180029030800003947d4251040b01c81c014030900900000c00c0d4540c0e0b80520b880e61b8281c030781c000d9905c1c550200303100b003c0042d24003070b4582082405004040d8a440c05c004030005116941021400758000030031800f080c0d000b0002d61300b198107074505030345803c0641070910 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 367140080 1250 367138830 367138861
    0x5090303040303480f08030c03012102010c060203040f061a030c1e100917030403381b07050303010806010f080307151119020c01390209 60
    0x107a400c80859100c0301c111100042203104264114080e40072550400b40e1100ca404d502c2c00c0b01581e034035041940c010b01040d070450040d405021000502550b0750324001c4050fa0010b029075140074507080012115016030380c4410101480740e00900c006035a522113207003900c145115a80c006000b075080480c03a05400d950350101d581e8100c0d0a909607030500861404000400f51640700e100d0315801c00140030b00041c02c0062503807104c0c00c400e0404103021611200c19010718078a4030406100e035400000d050017000ae4200315104000364411019110008003081c914840001c9083d00030100501070000d00c201d00d0800240c5840c3c0e0b440c03d4095607035041410050b4880c0d100b4010341c4a00c0c424030700006410025581c0e184102c0760110061420a907042d076915a622010050759a051a22800ca40c140508060001c0c5188016191400000c1081620190901c111208018140f00708107040030541c500700c942001359804c240281001c105072403103500380e00d0400b000b406900708640714100042c1c080011280c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 367141330 1250 367140080 367140107
    0x18020d0c0f0b07020901030f0206130b041509060503160201020412060b0306100308070807020406050a06050c0106050307180203060d140d0305010e040c2304020307090509060301110f0a05090303040303 88
    0xa07a550242c441540c064a80b00703490000b5041560f00c80104040303484820b8002c0c0e594402061103142054800040c05c3d040c55a8016038460100060304000c540c1e0f003402894480500c0703040c0008e42625108000d05140001420701c0b03e444030303410030485002e2003175046a0181103c0d50103183c0c10a224105940140b080240d060b029105020200325009074041d130090403603a00c0209680781010030760300c40195401106040341c00c03640f20003020036a55a40314205010f0546691071a03150500d040100382903c1700342c0d0007140240c21600c42030210421a2940041128130f08202507903c2c2c0f6800003058561041040241000c01034a9014821610204908582100c00d075014040759803590304c10340c1c042c44182d07401000301d2007203002004518194812242e00c8410240000040000140401c040c2d0703004541100000d205290300344071a182c40045a600102b00f0381c002c101e0b0b018510249081440b0710290101d41610102e44e003507980b44243d0031201e00c01005011380ba111607480c40e02502c4041b01021 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 367142580 1250 367141330 367141349
    0x40308071e030e0c030615060c0f070311130b03031603051b010213060e060403020d0f05060a020c0106080a020312090a1d0406061202090118110301030b040219150318020d0c 76
    0x4c0089091400158246c020104e071000d0103401c4413520100001680f001815049500418000f403001c101b00744840700046000314110600c0d15002170800aa24904282d008240d500d04941008144c500105581208021031900e4500c11800e05060341c190082c0c25080e683c46100c0c25910545402c1034010303021416136040359104140c0c07124426107024a107d24219000301c4180420009440c04800010005028040341401e40c20030762140760504004030781290f00e8a0300007991696003082441091300410200300501050440f941c0040d4490013950300001c0303116804210245a0741e968002c1200070401c01483e4001001d1600c00406540006c80d030607103c43d03143c04000070f000c8200413840048260700401c051296800c05041c0d4640300c40f44c2500b49035079030f030f43d24441001420640046018500400c51507040b440e00e0703c100217107a01510316034582030108080401a407045545607015000040c14040344141042009064407140c40d5400303036010009100388014046011115000e4481089 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 367143830 1250 367142580 367142593
    0x4030e0a0e0c040e0702030c1c050c060f01261009050f06130501050f012706090603080301080601120f110105071205091203090a06080a090b041523040308071e030e 72
    0xfa01340d03100d0088d0120034550b5004042d40018942c00c441a8a03100c5160381000f81c2007803000382980d442c0c80000c4545c050040111001440802d1007259607800e2003480d2061180010745440000da142d824035215201c6c00b0791150440800c1103400d004545038004a54125112480c00180c07100d0041035241c0155515483c003008522181710890b40c05044c5c407504410512812941d0442c189154110751401983c1582cae2038001c615000c3c02d004d02c41c02180a020196140d5050064060500710182d000755100ca600104807400100c0d0354401c95007080c0c0200c0913040407088480141c1c0c080c40b40d214004e120351001c0d4502100207030000e026000c00d0000f500c3e050702000e000c4802075580e2040030280e950180000c2408c110080c4a00c08040d480b1078034880108652109507228456102c00392001c90300d4665100704400e90721224400c10440e001c0e59000d9042d44d282228500d00c6042002c1c0000c1c0c20840c0040000c1e034071a0040702041c0b818002a0340101010454040080081ca41469030381068040d41 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 367145080 1250 367143830 367143841
    0xc01020c060a0501230904050f0f0a0308010b030f0402120f01050f0901140402011e12020c030a021219120b2805041506030b0a03080304030e040b061204030e0a0e0c040e 74
    0x114400e503890741820840d038500143c174800700a41420000d2044a25100b032607541c40c8a245c0c01c0c4402d020182c00785004080c02d8556140c042e14110058204042c800800e004100c00540e450392a1608285c041e00e00c102c0314507460f80007a00380b90b00a500606075600f0242403003000c06103500a68481c4403010020041d42140c072403400c403149002d46000c4d00145110411300f5010310086541c00d181c402d181090002801401c03803c40036600b00c00501c80031500081800c901c2e10307030184026017441c1c501c06480c525021402288504a254844100c000c0140010b0500803ea1840c0e200f659011402000101009040504050800b40c108042c12040c44689030000e00c6081c503000f42800d4058012917018541d042c00300450080548c10303c200c1d07202c0301502c0000041502100218000c078001c1c0d40e0040084c00150a000c2681e940325130b07550044504102011022a100e071405400039494038004000b08410000a1300c001800e4101110104411050000d84804032009108039820b0100b03100310703a80c90 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 367146330 1250 367145080 367145099
    0x230705031b07053409090309080d0f030c050405092a0a0801090507091a09010212121504060f081c020304030c18020403140a020f0906100309080c01020c060a0501 71
    0x10004010407551104403014045100f2407960742580011040c10542c08060019021303600c40035602c4500791541e03a25811042c550302c2816440030300b040c50300910f0480310280006243c544810b114508142e500c500c040385480c42401114014480203014110314240603144548003150a083d03032030005900c1d6580b4044945c0c000071b035090729995465030840c0f82c2c0303484400780240c10010045420890503074004688080b01040e20300d61001c031a22307015243e1400c40000380c9040000202c2c0b00e0190002d02c92020784400324069194401c01a0221000035019400401c0c0034001c0780e003101f03081c001c402401080b5141c0008103200320001c3d058a055000300010b10603600c0340308601000c2c2140146500034001401811019030810340d0402c030042c5825540e443d42d810304040341c1c0c03416030540c000c3d81c2ca03141035241101981c49658811555205582040c90006008065042d0390806164840c070301c41062050300d03002d032140303c1d03030b040c1c000c0d0b695403143d129058540b00112801d00b10f1910307060011450014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 367147580 1250 367146330 367146337
    0x60403030e310203060307090c0c03030b010503060d080901031d0a0201091706010b03040f05010f050f090106230307030c03030305040309090c050a030207050a0c030803060103200409230705031b 85
    0x14448a600340240740c0d81e0b007030010390300007403102c0e81600c034000c00044c1e00d0120744102c800c4009580d60f000c900320041d1400030165500629164100442482408656520355a40c20000f540c45070300349a441c40c0000040e000f8000c818240b10354203c080e196100116408505125154402d80c2c1391a01c054450203018202e000c0c503000c01d1600d0780400010b22003031040b440190b80040c01480903100c101116a5642d007075a42a141e0181b50707a858105000e501d90416040941018080c0020300440d0b051800389031030b081d200c0340c80031880c0800c80d0130101c131501d040c011130014581011030002d145480342030140150a003075404400041c000b810004200c0130500c079100101e02159591454203070131200440194125501c20b0f0354130700482030341200245007040001e0080d846101c80c80d89900d4040009022620f0a4850400654040d10791245194a0f0f20481d003d0303c42c1038034000341020701d810400c490302110040260780c50b03c1100030b0014042e0404040d40c0b18116440640c105000f101011100f50300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 367148830 1250 367147580 367147639
    0x2601080f0303010305030d0203100911090f01080f040b07050f04080106051903030c02060702181003060b0a032d050303090c03100b0f010804020f030d05070501050106110304090c030b060403030e 85
    0x400500c0300d1f16100301e0351b0b0001c64120650000780243d035612043d9400032210704c028850f10361200012054801d05282440f0400140d090910002c1403800100907241440d00a2005040e005220b0010311140d00581c161008000050481c54840741c80d12880c1d402452603000d43d130b100c0c4201503104003156401c1c4907003409490780f560b035090340c42e181542405099004018201e038407c0500800011803c1da11141500c0f400d2074070020300302c0301e01e9402c08000300c4094040f010300542c1500c00c1400410490590032112603444400f101c40403220303011400e80f407d07401034004d0550100105102070b243c00090410555982202a1092008034850b014101d0340c92814040d00306810341c0800c2050343c015080c290740300d0b0003c0d051120b50210440042d0811411103c1d0303202184003c40c0c00d90501c030f024420303180509100d05020040700100300c00a903590180d4402c03220101d40f641d100014040c46500b015082903005000c260316942c5030301d005000780c9003c0325898090502c00c161040948014904001c894 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 367150080 1250 367148830 367148833
    0xf06010b0a0320120609010b0f04050f040f14100806190902010201150807030b0c181314011410021204120215040308031b030c192601080f0303010305 66
    0x200c1c440080d00507201c21419005581103481c0d80c00d0b82151403000514080c544010404040c0c944801000040d1a040e00304180c6e854090200120445a9608980550f00100c9844255030724107130000300500552824460450700304414812002031107144180160b8059610764155500e03a540d2554404d07044503030030204200380b0280b403d0008c844c0c0c44008120700600c000301c4c8028284905902c41081e5520225207680007003001c0040c414420940d5401201e0420760300c0c41c000100c5030141d040c0c480011a40c1c8034625180159403081d00715030080099a124400c0c081641d82d4400441c50310540d001301d4035000c3c6144459002282e440480c1070380498407014070300740c28281010303004a5002a18081213800c5085035a144000041c00005040198400d001d4681d50b80b82101b40c24003c40520012100349410074013f12548402d00710603242c1040c0c40c00310740082814101000c484c07085a13242804200580108411a4401510f01c500e0582e03001104545000c180b0580300d035500c0c0300920003d40b50303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 367151330 1250 367150080 367150087
    0xb09030d08091615030b01030221100906061d010e1014130e0a0c0203070f03030527100b190320120a020a0e070c060902011b080c0f06010b 61
    0x42501826000c0e40105200c0304650600106483d0510010140c2c0c200340c400000c208602c0751110b906005601001e40207180543c20721828200592120504031340d28195000e0040014469188a511400040842032000d21120390f440c0340290511040e400740346a070440c140103d5106500840c620604406c01400070310348050486402ca584503500881100c0808080204c48613100d00303090688041c0902103201d40c280e041111500d41100c056100d0a01590400c0c403c5c1004148610b1400100c1034241c103003c1801d65038110388100800c1c400442c20858425031070b104420540002c3c12542c0303100c00c4281000b244003401d0810008034400c3c41d0f0403041d070540c4031702400014012089840607910301d100892403100d4a500040c001703024003401007810351101940c04298980710503140000d1000c000340e85028100440014050b940741da8028055030b0302c172601c540459115041d00c0031007114000f0140c4080a103454003aa503507220145010b690300c61072844c982ca05002041280c100c0d405d0108040c50f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 367152580 1250 367151330 367151353
    0x60109080309151c0e1c020d0c050309040c051e0f09011107122405070906030e0709050c04090b06030610080702010605060a0818010516031a060c070e010b0903 70
    0x3000c0800350420752039110140204214102803c00510545200910100790717208448603092400788141c0d50110f401e07a03410328150005070041017684c134841142c501300a4410365400c24a20758410030140130340080c68008442c1243c2c2e801005420456002000e550001314084003034412400381d501c00342d0b1705140400480d141503000b0303c04101c030080030340c003500c00c607035031322405001d91400740d40742500e0702d0359113841d9030707205098464940703801040d561070070081030505000040c81b4003000d004003c2895540c01c030752441d244003007103000014203600ca0140014030303180d062007007150018421b16044605008190289140c20003d41c2c5c481c54010b08080032100c01c8120840d48290302030700b03110940d507813482d0111311510b0b150b0044c80f003103496440340c1c8054104600034018107180d0031044262031b40751500381f103040e05c444440044515181d1030b001c1503c2d16030414092203500e58078003d550025001590321000360780070078202d00b11000ca01014803542c3c0c0c0c4007510785140c805c12881c203074103810090450300c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 367153830 1250 367152580 367152589
    0x9040f0606120b1206090d140720030a0c060513090608030d02030606070605070e0a050108070806151c0f05130c120809030607020601090608210306030109080d05040b060109080309 79
    0x1829440c001c200c544c1c000050504142030100c1a104400140c1101641c940200e0f0019104201201c141036154640758041d2180000c5150b00401d422070744003032200303211103941c0c10804491078a4200e8080b5080940c1d424000d0061713404071001d02d4480300c250000103038003001c0784100b80450308248083d41c40c2c0b190465400c00250310007050554008000d1240c1004038440f0b11449204005c10340703035101c0c06400141003001e80d0041d81e206a0402041d0720800c4500b0340d102034242c5e002a1705483e00c02c0c6000568220403054054441d0b8800541d6a00c1c07145203000342180c01011003000c42c1d070410443c50700e03040302c00c01c00c00f040688094408410608200400d01014443c1c854a80c09000020705002c1b01900090401005540440c016400380c00140302c60200c501c1410700814000d8002d2007003034001096030312442e8400c0f403c1340d6041000700020b61951429007200c01d0242d03004000564031454246d0110090000f03032070980d049030f50140010803035401032601c08180d4080b03000840c28201142d0800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 367155080 1250 367153830 367153841
    0x11070e0114030102301021030207150e101704030e031501170f030933070803010305010b0f1305070c0b011203083103051e09040f060612 60
    0x25a0190744c200840d40c0d20303801200304a00f00c81d8542120b03031010343e001d08680e40e04030006031020b890611058000c000f5104000b148421500781d20710010140c0300349003416401d003003056100d001400000310201c9075107980710302c511211180485a07405451012041183c55940e18a03040c0030101204022501290040407880d90010004049407000886400e10104200302079209040c0789003480701d081c0102030280499203019007258011030400d15000f001404591424507030307101c00b0b01001040000d0f107165003031030040462060301c1035541ea10185408141e0b0340c0240700640b42c5504c1c00b01d41420130f1410f030324081031850006194001c546040080d00300140700c05028801800413804240c80041d042e0512107000745100c46030403081c40c0590034054000a00249100d410700038104080101e4444900b20700707900c8841200f009102000d82c64203403018843d5030040503800140c4401c1503442c04010005040c41c24090ba400d10510405008410980f1540d009540c081156080c1c98000c421003076008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 367156330 1250 367155080 367155119
    0x24020901020f010501140112090804060507050118030203091e0603010608061002120d050a0f0e10060b03060d0b04050a1502180603071d010e180f010f0806040201120207060e07030311070e01 83
    0x242e100e11a52b128034590740300c0d5201c1e401244005c00d41d102407010a01c00c8404011404140c4a8180400e640003500c0303100e00114144528030f0920840140350101000900e00c4101810035660307540c4401015201c20700441d442445414088501d0440c00d1021401c003c00d200d4540c641c50408008940031800fa04006060300b03025542c0e07922040001d03601e8000c0d81640a140005880c412070403da008082c0c617900c0d0000c0c007028008009110b5a81c541c4015132500a802614070703072882c0c4035490040e0400c18440d002510b610500703e418280c5695135402000e402410811407552001e0460500072103000486104000c200049182505020090451250014140741c090b010412060004042042240444007603040a078100006c1c842482806400742c41901480c1c10303403501e011145640d401300180002e040102c040410046144180c054441b540ea1101017402140b115468150740c2e0041444158001054043c810007020804100d400503501c0c0100307404502d03800e02c3c443c21008110102c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 367157580 1250 367156330 367156367
    0x50702130b031b010801081f020c0307020d080918040f02090429010f09062409030b040809010807030e030d05180f16060f050901030924020901020f0105011401 70
    0x101100300b50303000e0241a0410310038049080205252100041040105070001d4a403548039510300c62606004482c4006941c0c0c02d214056510030203200c0090850042420003900111150303d6a0704010307800c009010740690079101400300082c0c1c41c02143c614070b4240c070003030851100c0c1031480000d0b0500610896015000300c204c1c500031094000d51482d54402800c40010150005005004d9582038040100040001c00b509001690034041c1768400d21200701c5000514042554400403003901a101013001142c1121720411949804d051428041d880005414006111800002d0201e40607200d088040c9d0020f800031070400c01c5100348500141000b40a044c0c1c40000369a0981e51010b080100b00c4003004002c010b000e407111301c0c1003040065000e9410010500400c00700120740a0340c014151030819009203404944100d00b810b1580c3c04141e202c2c0c100003070700c00c4c446c44440d08840300e40041405007403c0e401c45210200e107619540c01c0318803c0c01a100008420070182e1200c2d072162145903410f078400c10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 367158830 1250 367157580 367157591
    0xc100806010e0a031e0b0f0606030c1c0c050a081b030a0e01021b0c030d05030702030d0c110a0b01060909020310091d1501050a05010c030801050108090109050a05010f0b060a05070213 80
    0x80300c501064402c91004200c0345d000841c0c1d10108010860442c0e003015240c24481c681c0e0900100107a500d001c002c010180402d80403c10f21880c400e0a074044a000c60030110406c107400796101c0050096100380c0d14200814466000b1580030b21480d603988902810354800c0d0350540c1c0380d191020b00941030a42c01144259000c0c00b0180006003005207031500c01c20714070010f24500015100b07160502d840d200020707090000900401c0780302c0b0f8000c07044420882a6190000700c005a2030b40c20313100300b4442d058501852081c2c0c0300041c00c0003c15180ea5069947d1600e80804441c2e0315104002a032004a50341e40d41c103084180200b2400312550000a6030341004031803c4074035032030350b515281f50580b801c0309020365401000041045041480280002c1c00c82031806862900d11034034007a1544106114642c1040060703000140151003c4d0301ca00d281c140e125040d174540b05500e081850103880002420010549054000d036501d1a21508a03925200180c9829041070300c07076020403000244124503154402e403241c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 367160080 1250 367158830 367158833
    0xc020a020402181203040e040f0609081204050c0303090604140a051f030b042309250906060f0c03050723100516020c0d050f030a0207080c100806010e0a03 68
    0xc0c005400644081e0b1992410900c80e5400c10048000b0030112104d00d030010031060042060b40030f07115034000d030080500700e07500f0b00500c1c06000801440d04090030800d004075034052103170f8080010500442c010421645412561020180c8070710804401070360005041008003d0700e20005903021b00040700400c200b01195550b000319141000c0c00c040d00c0c00c280a00304c4041021505031062a006e41000d40f800c0010764140400b070281c944102111000f4a49070200040e000301e4200000d0310420395540081c2d212001001080c03042e00c6403401000e0200b4103201000c03607498815180d90507880c034542e0311503040719440d84003501d0a610a04040e18811140c5500e4a6070396080403640d507280110100a00070014001d440310121100540500410320b5070040a2043c164002010075003410101c81d000c500c0c0e019498000e1030903c101e00c0100c1580004140129110f03000b00740082210036200980308070300048002c00010790841d450f118003190584011803020b5105440329134807c400030340034683c145d459 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 367161330 1250 367160080 367160089
    0x31f0b0301021605010509030405090424020a02070509061f080c04030f1514010e0c090f10030617070803180d14060601110601030c0b031306060e040c0b03060d060c020a02 75
    0x72440f0705003440300c0389560420048240718959000f6600d07000303507040c02e04181c001203c030b5030040e1020300062a04002c05002241d034446003445203c1c4d0050855590350a408040c0d126030031449020b214070b803d0700010f4214140480311195401900030a0202101034410a5648041c007404000b89144148000b200192081c075450304014000c1d44640d10082c0544000400d8901d60074001e5111503494004124604083ca805500001c040c0500c0b902e58900c5400300700301c488149010b81d44484c101114110446c2c16070b101206075034440e1140300718501c020003426030f034041c03501c120800da40c004c10802200ca01c8194a1910302c24000b031403111007680d1a150085c000c0c41c96100703000300d50802030a0009a40c0c014101e4200240c07207002410040d80365446064900000d8410300c003801400200040c840707510601805001580281c08010250325030400d1044c40c901100c0480301220586408910040c1c8175090ba445080d000b00126104001c40c0e8850001e4488907040b40c003944035440e04100160784 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 367162580 1250 367161330 367161337
    0xd020705070b12010e22060c0e040f090605091204031e060c02010e010c1403010e0402040213090506030c011d10052502040b041b050c0c150901020c010905031f0b030102 74
    0x19900143c0c901d9410312a96210510028200d92a880d11052103050780c46c00c4441c0008003503070424400620700d404503c050f00c6d8441040001d5034010724000c44c0080104080c2d1100079046d008030300810141d41c814241030307911880c10085000c08103050000f0800540d1894034502601d00c1410403050070341095403680195031282a001001d0303519000d00c5c81c40101c091241d01c800b00041c2c5000a0000c50001030701b034540c8410300541131240c0c44a8001001d40d00c40b501110311140ca00301c01141095a196584070040c0020b948043c483d000700902d00001d50701c01d0000c0c0381d02c10201070080d40183c1483c010002c01051208950061000c00d005c6031416030100d103070350760300c2100300083c401d00440303144104421980c0c0703455464400c51405e04024079103556400350312030007842030804540d640b0103001e186280201901c0480c2e032214114401140d07021512000e400f0454003a000c803000c0051150056030b0100c61409001d815501018486a5402100162000c0d01010300c4001808140440c00b09003641e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 367163830 1250 367162580 367162597
    0x1e0405090a0917030c0403030e0301020714060901062c190e34051309060912110c1f050928060806132d0b15030105060d020705070b 58
    0x140d03102c0b10102071109401c181c003c00b0450b503d21034034500c0c01c890b485d00c4901030303400701030100300c02c104c244201c6803800d45c1260201c030382202d200d40781040c03d90003050350381e50201c0e03403680b0300d5080807000601038101d01485503081d907214403020310142c020801d000061000400110304d07001510b200070451100362146600c1b04c1b518102800103419414403107417000b0030070300100607002e21041000c00d480c2d1204601c04161032045428580c41c2e40310244e0b44010705541200504010f00e8403d410f400c002ca4074018a07001c1c109078803480c504840109880b5118001c1c0503030f098124045040710020080b00c0804842281c0c1d0509000d030030300c4075170800b1485406200107101c0c544656981200120701451025400929881c40c0100141c60200c02191300e83c40e00103100d050782c58442d4217100b04041c40e40c03110070382c0d4219400d00c04001042c1c000c402c03002e022150700d014007404640c41a0403c00c500d0380c0c200c0341a0740d00035041c145010b140001c140025404000c065603d80110300c0c020950040b6000102000c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 367165080 1250 367163830 367163851
    0x40e0c04050c250c0306091a0903030130110a08010f0506040e0601140603062206060f0c111c1505150109051f022820061e040509 57
    0x10211020036100018403000f5280c81c822880391a0780c0010041440b040507203500c140003146542d03d500c2c110300c119950302207120400c1d007200c00b04041500c0000c045e504841c291040c0762010308075039200d5400c03075102c1e143d100c00741a03c01e004003021030461080154002000392921203413950303402080e82100c1940350084a940d440d8014401e41c3e00d0540113041045081002070b100652410100315804400d50442c275020300030200c000740c0702e90b903903190240c0d00c20141c80300c102903690724034a01001803c080c01508045039040c940c1c107802501ca601408080350b44450000ca45c240c4460030020f640c29035200484a03000c9800490000600b25501a1078448a0820120311414440f101500c182d032402d032403d0400c000e04800308503980e5544212000309501ca2100603092441101c01c174200004004000c0b081e0100e01e081d01c86290708030f603000c0c2415009900410f115031004000c808480401090360398400818031407440ca0003025800f01c0c952905052000740782998a1021504461084070b900101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 367166330 1250 367165080 367165087
    0x1501050f0f0604061407020406080a0b101d06060409020705070f080a12080712050c120c090d081b07120212150c090a0b030c040614030103050a02040e0c04050c 70
    0x60381821614108803440c1220422840c20740329010070400d0055106600402020711501040b54404030219915107801a0041c8102c030344800302d40c0d03500d081090003141c80c0c0700d100340024201c0a28400000070fa40421803030142c0c256050a4007a00c4a9000d84a580d02060410000502a03c54801494000c7c41200603045083c640700e000140c000840d4800303540ca4104600500015a403060035011003421410140c4140d110070750100c60140004001001d120315002c01e1000c031414100c0907140c7d500b410740d452030a81d5590f50b80b00300ca50189a980344c1e041051007010300e00048500001e0032002e4041c00442c0c1001c2c80b0300c4200b030302c0c000341a40302c412135a6403407900ca0154100b1044c1888070303000102c01801c2c01c0428021900d06450002d0007107144038804a00c001c1142c8d01c6c800581d0040c442c0c980c05584034144009140d10f158818807845010400743da21540b081c180c0c4030282c9040325004800b410364802c054084c000900012000c0003254000c103514041c1d103503110f00c500c034050b005078100381d501d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 367167580 1250 367166330 367166339
    0x11030c07061e0e090a0207060e0a0507380307050c070b03070f020c030606091003060e0c0a08070609090f0e010c0c150605090c0a02150c07020102010b12030304030f0207081501 77
    0x2000b00e50248038104803808520500715141d0b098801c0e08030741100d100581c2c17007403c1d050000040c03e605501c1001030242c00d15080c20b204000558138103848030514a0320f842c16554881441403040914616a1030024108400c908030050018651210050030028502511007044505142c95038100c0d001070f1001100b440540750340012421031101c29400142403261a40340040e940d03003001030101d44140362040002e5101e803590b1002000a40e440f120038448840340b04100303902c5004030a96a1301074030280c034000840020010309a01111425111a2a4542000b01c3c03407010700488495207020301e07241c2090007486e24091140500c00e030416a1090903100c0321385042038104000440448610b81000418003696450080498200e003820001c3ca6440348140b0042c0d081450f11401e00c0c0c454882c4c0010000600304070300090034200c0c400d9008101035014181040100010403040c142d04e50f20a20000f40007900070002922440498011100340c5643c1e42c41039031a004e000c00b44a500710716040300400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 367168830 1250 367167580 367167617
    0x2071109070e0604032009041104090201030608030a020114090a02100305040f0f230d0e010c0c0b0f0304050c090112020405072d031401080a02060f070213022706030711030c0706 78
    0x8946d600c04940d84d001d02d0500d900e6607011a035410724054802c659810803001107a000c2e074032a10040610310700341c984403200c40360064000d0001090108240744070300000782c40c0e0755001c58a40700d62070703004040001450000f10100c1c01408028012100c0c012811042408034110002000c4600c8c820b0b05c5040038079003507456503060a0b8a4079083c0210341d101312403088449812042821007c2001e2038100c0804415092102050416500144003000c0c00180d1090071105140103600c164000c0302101d0010712035000344540d40c0400d1050f840e03c0c01d00e100c4150010b1070560001c54110300286000800c81031006031140004040041e1003003404503003e00464102d03010301554071090560a81d07140c130740d031400c000e0715102c910324140207100d40320000d94070302d0303490707200b81503e007002e402400c01000400d0840001c4000e5000041107218207510200707511416000051103129601c000d050f80341980c95242080e04c4030030180c031a0890742d00050100211030b1344100f145400800c880e581d400b04e8611203c4015 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 367170080 1250 367168830 367168883
    0xf0b0a15031517160302030606150706050c0415020307240f06080609010e19061d0a060207020109140d1b03060e010b0a1505121503100b1302071109070e060403 70
    0x5841c007040e0413104001594010601c180e01c44020344e03043d4a1302c1003240d01c01403944a08040280b07214234003800e00800e04d0016015000703944091040d6400070004090581c5d44c0d01604000034802c5a080d0103000702107442100b00200721106400101d0045003031803010040d0341b681c3d040060603901200070407540200034060601c00c00390000c0901004c0454415036084000001d0b4040e188584a00190300913075000c0381d40c41402c0c07048e1001d68158000c3ca16068010754005d10050340050701641d4081501024a0400280c82a0003040e0504041d080e0b0b9aa03c4144080c04016002e00c40204c40007000c65441d00611040281510000031108090303010466410041d800a1841d001c1000b00001400c1d0080c1c111146100f2504010810780d842e95680006058880541905801110b10001507181c1941089500140c100c2c0e80b5081c1d5078001b10aa0200c0c0203456010b481c0c44290b0f1000c3c841420020401904451507140125500050070081550369106900c225500360119401090710f40718070418 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 367171330 1250 367170080 367170103
    0x402040503030409020c0304080a0503040303022103060f0a05061c0c08040209070503100f0902211b0306240a021009020d060b0a0906060e040f0b0a15031517 69
    0x4508050512000c41c2c0e0328040c078001c950119a002804e002d6050041041e28001c1141c0300455083c1170443ca0003a880340c02500c0200c016120b035190100119414060106a05000401c02070850b5904d00420044420000301c2c9600003018450204690300c800c0c0c0141050540342d6602540a00c0c0d00c00064100c48100103c07500300011a801d21006039204007240340c03c076a05180168990301d62240c80664101150300ca1410070100d60400030f401300d003580180124242c101c002441a2813007051402100b442203507107586940444d40d0b000e103600306107400b03590015006801d48081c0522040404e0f01969011262881d0300c0c4041409807010394100902c4a088403030110a1005c1d246603404a10390b1883d4180c010304182e00d511f05408640c550b01004001082c220b1010302c10320303a82e00005042100301c000814004e5080c04109003101034640900c00d00c2400103040290001d2400d0000401b0180f00c0040f80304054484004910320034082c1080700181c194a4481580d074031010400b01e242032510f414 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 367172580 1250 367171330 367171339
    0x90605130506060913140a050a0c0c12050a02070f03050a170a120b13090606090e06061e0114040603050f2223010e0a03140c0d050d09020409031d 64
    0x2000425250342090300c400b0001070310141032501d82003065074068642e00540031640100b9600b007202c14179458014a000e60211002000f0195190ad41110100b18900001e8051041090b4098407148200c0017000d03206030a10650700600d448510801803952140d009880310741c460540340061015181c1d1a0701c0c010402c41d04103207480c0301104050000301a041e03c50012a940d00d10203681611a094222103250f484141000888454036006008010a0144c0440f841c60044004005c2200041440c00740a0081030300c0e141d52141008040c0302e03580c40c04a6810014405498150740344414050005001c241d10041201e14000c507600c00b140e03200074a9180865480340d0680031900c82250786291003034010540c4022460902a40540d1018200600c4050343c41c0940068240345c000c5890000c1503c00d6071a03a1019100010111244c001c90000e11050b4201c4010b00c1c00a900920003820980c80092011a0b0310146400241c2104c60005086e80841c07100702008038030707250303000300c04c1082d207000c69 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 367173830 1250 367172580 367172591
    0x80f03040e130618031206050d1502180a032a03030f1202090604090f060506030709291813020c250b0304050d0201141e0403140409060513 61
    0x202840180d0788040c042c0c000c008044150302040c00001d030084515491020950403610701d040c9401024a48440c034401051071510002040c41d19002d01c8403400326410060b645c800f00c0c0c060b54000020752002c2c9004102104507000c80700f15450b07210030b842c0114024104001d910007480b4407030280522402c40b6888a140032042813000030f400608100c1c00558528005405c903000c000144000d205441000c2d60181c004100040e08400750b4103c0b1030a020011760601509a03900f0a11540d0b0005540c841c2c00704a10100a1003031405140384000c40c0d0407aa0b168656800b505100c0242c10781c044900e51900490114071070310b032818515241c01c0e074984114002c500c1d000b5001035a944a80c0c010300524000c160b10a210407150801d80d03804405044005c050517a2400e00d484c0c80795881415850810240d400c0451010110101c2803003141318480ca001100c0c4648040054146110740045c811030a105005410300c8103030000030041d00141613107040c0091282d050004208061543c1c204c07240701d0742d0600 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 367175080 1250 367173830 367173839
    0x13081e0123010e0a0f020c100b030102090904080c10020f0c061b030106050a0e06041e17070510170106092105190311060903070c320609030a0804080f0304 68
    0x109101ca0444000328054030a90710341520030300280c00d205500e08650b07030020a9101c007125001c1010211014076010400003000f080c1c060509070301855104503404640c400c001004540d80c0300080c010b0302d200c041a81e0f15400303c0c070052801ca800c503440180101101007140380101c1c0b81041610340003189501c02d4200f1581c660555000c07032205000741020008049110102d8501030090010003101c010700044d1190340314008283c0070010940718900360030aa1200241003044022022207400c480c10203002e41038280307014080c014103600300c0c0b0350810140d001c09118030205451461301800307040ea24610380b64505412401c407200341d1041c80100208400828000450004060300882d2600c0701524000140d0300b8241d50281d45102d03445c42a0141e001001440d80c0c0110040c40310038481d140c45140e15803180c240d00402d4000204140c11082c080e5084240c500b0a4020302d081c258000782000d252040c4000440d0a2100345c120481c0c03100004503060007a40c80070b0211000c201c0c03c0d0402142000c1c6803 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 367176330 1250 367175080 367175141
    0x5070605010b13083903030705100c0c0f2414010311060a0c0b0c0c0a06060608070504060206040b1b0703030b040b061216020109080a080421120213081e01 68
    0x117107281d101000700751003401c65082e60f00f00c102070100031005003900c0d20313407241d400c00c240c440810070600c0707450318506484c070094140244c42d140d12060300800009406800c941e50b5000001101c3d59425580700850b4520954071001c1c01a060340900d02d60004049501d5450044a16079407501c6e2284150410710a4621035a030000031303d45966088004800c241d11080b60701140d030711808034481040d01036010400306000d180d1300070000700d501540c0c80c60099a2031403000c990500031402649c4c0160031070000304012440034034260350801030f5144980c0c0c481000e6038140b0601d9111700f000710046500c2e00c061208074a8144a030f03035000442524240d1810003d0590212081001025868560051020000018801d62110911a44c8000310079900c030307080000035056540460302110015409403286600c019003580303844032141c2030380381c4603440c0e92160b983d000039401800c10b8400100b450540000c0c180380170000025600d0b0034004004c08810716403542401d55900c2140c00700c3c2032341c0c6c1440b8041b10700d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 367177580 1250 367176330 367176373
    0x10606051c020702030102070b150604030c0611010e030a0c0b011d070c0311060a060509130b0105010c0f1b1e030c090e0f1f0f0e0307060b0105070605010b1308 70
    0x84600c07884058100d41c42841000303000d18a4082d40561001caa400204030500e000c03030b801000c0325400400c44001042c104400c40c865804002c0c403581c02c0d002c007081814081e000e411101e4415000211f0f05680e5405140e1075508a11600d800041d03112082500f409100385000307014041004400011500c1142161107510300940301c1c00170840c20a6140c400d0521416070004a181028266800350400c4002c0038081e050a00400e0b124a220380042609083c08911000e40c099010081c690070380e18240064030301d00c0340d01c40103541c04424180c0850004940749a1040480da201030300d0b50450b4141040215603c0c040140c40070301c0c840c00074050020580079844602121002c07540441d40b00d181d8441a81000d06050b07005540748034a1000700d081c821641113120b038203229403108015090000010800762002d5141520481d082000020003003907045d000800031403c181046490300300c607640e0328012124243c1c80725001e07801c08290110a62a01c0262100821a90000b4000e80900c251101b40c01d05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 367178830 1250 367177580 367177597
    0x10b0d12030f1a01180e0a05060f220e0a06020705060702120c0319050f0a0309140a0201091203090e010f090f0501050f0111070503030d02120a091e05070e0a020a09060201060605 78
    0xc0c00400d241242030820340d04a001e4228110011b255081c24840d01c0042d110559a40384224440d40340c00005040c80c030f40003136044a00d509884a82811034110f00014034003040541c0450003a0381040f00404c2c0307039000074440c1d14070500c0104018a8200c80007401d0060264100302c04c0c140400000b109508000f048d00c0b8000c10031800361440c041e000c8400d6805204d03090900301200301c0402d20384192505940301d014480d00480a051450410554207074903030004070782c0207000c22101d240500000803160a448011031090038030a9030350b5240c515035000900268043e44008100100c24000781e200780c000c81e913000300c2d907180a20880d41448005038551a204800d981000300d02d9001e2000900f04102c600d008180180580380d89100461906010354058501c2250410f143c8021550040c4030b44200180540c010308102d0b40d52080791208070700c1e101d0001040d0b0b034900c50030350302080c00108080000c3c0910407140780142d071000c580501600c6110150f1090040d645041030070010660484119842c1c403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 367180080 1250 367178830 367178837
    0x92506050c0a0f030309030806061608071e050a1a040827040c030213050a050303070f110405070e091e070507170711030709180206090102010b0d12030f1a01 69
    0x641807031074100d20300000d141003c0c01a103100303080344050580541c80491158000d5480003042da80340424801c06104141c04c0c60120010010f89001103060b1a0180c00c60310700c0f0740301d6241140f01d4080c02034214071001c4015282030f08880202410420494402c6903841c03c0004806550701d0140c440c0c04a41c000d040029002d1100102d0002540002000b90100e849005108200000c00c00d00c004000350403169021090040000004c640303894050b40803804c440380140114513040565a8090f141001035204880070913040907980010307981d50241a22421196031808212207040e4200011104003400340b4040300c441c442504c500000c2411025070068032800d0042d82c4642503e808100032050f610340b0b10110801050100030044841d044405011040341183d6420307072900c04000c21a200b100042c2c00d00c00c1c44000071001030401c8005045403080500000486000a0001c15028042560708807844545450000c1c01103070588501c0141544c070813400c21103100581c05000c0000900810603061 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 367181330 1250 367180080 367180087
    0x109021c050c120f010e010b090a1d0d02010b210705061e0c070302030d1e12060503030c011d0a021c0c050a17010b0117130c05031509250605 62
    0x24003400300110b10256901400d000c034080d18080e0301c00e80395072101200091a50a101120704c1c4100140940a14000014601c1202d500d17443e40200060200703080c1500c081200c800d00c044950024440c0700300c40b9513580c002240c015005000c01104101d0011440d03030000000f075006102e420006841030a807801504d4032641c500b403e548801001401000c100c08080300000c040300c007070301e0204000d4104c9101350122440105101c10a49a09030340c0c0c2c50aa41c642d80c0c503000743c410300d88140d030001c001403400c2200094940e00c80e00440d066030f03c154000316207a9100c040107002401007008600e2520a108040d158000595001881c48001400c2c490120034904100a003070003050070311000103000050121000c0ca41d280c4840070010028100300d20755519003540d840306940614044201c0820199030207041d607860504948051b240390304107840070410481b0200b5982c60400c00400c40c01007828091905150034124949040900d08600c2030f04030b4111000c101042004080e0010f450703517030a19a89 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 367182580 1250 367181330 367181333
    0x6040b150c1002190e0f0d0c050a0509010303021b0a0f0e2707050906040617060106030c1e030f063c15050d090c170c04050709170703060f0e0f0109021c 67
    0x103107001000b0960701c0001018604100580f4800c1078048030b09c00d07034243c2403a540e9030082050500c8248070140140e0044c000c851182c0202d42d00d013104508000300081e240070f45807101b856805e0040c0d0040d00c8075404c1c3d4001c0c05404812005d0204c0c00001c6400c0545e10014003619403510350240d8440d031070042140c180814003659071500070748090440c100070341e800a00c81400b116500d0a085c45401d02091a1101030400580709070000206c00b40e00c048601c0c0c1c03110f411442240184212140c43d0100b80c1c1d1502c0103c1c80e1445512400c148036088104032004414020744400c03040c031107444000c0c2d03a68070342c0702c10840f84160440e003007520002400c003d82c880d02140c06100280c5042000103207010021136010030700d95214802c0c2403141c008401200d1810a0741c00500044030310139501ca50100303020440800c810000c90000038011400702081e603076440d40c0d030750b41c510940b44d1f40503940103401c4c1c903410a0703010b071030701088982d04803843c84009000950090300442c1400d49640111581d50032004021030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 367183830 1250 367182580 367182589
    0x171908190b030c10170a050714030f0103080706380405060a030b061f0804030e0904030903060e0f060c040e09190f020402040b0c100e03040305100506040b150c1002190e 74
    0x1045409455044101d10380321403240014141182c00f1000b1580c15000745850141c240140e91252f003c010050400e642507031602003194220200446500346c80b810706d03598200452030a56103071200c2c00c40003e08010910180d2000c5008841c00901440c40c11080204a84e150b050700c0003126004021043c40343c441703501262804d80840c004510718008524020300f03c1746d02006141c421802940ca940700400c40d081088098101954041d0010f46180d40500102d8110f034401c1035045413043c12696501c60061395681440d00031540c2404140f0041400c000220310615040c5c0c0c0001c03120003410782880341c091104a0340702c803941b000d05500020f000e194115120782d411107000c4c040500b8810b480d50480701c90141e42d43c0010007aa0645400d21181c01c182c25000001e45007541e9101000d080145584042c40004060003080c00d1792007500d82e0307503c1c2e0b03030b81d101c0ca04080d4600b21f0100c5131983d00c01d080f84000d40f40601c29142105917a00c100052418800145014040c0c19580d01d4100781d040303912400074 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 367185080 1250 367183830 367183847
    0x80c04022b02090a0806010501091502150a1b050910020105010807150c0803131103060903090d0507051002030304030f09031101050913020d020706050c0313171908190b030c10 77
    0x903604101da1500100d160700f170000720241212001d170381d11000350361640e000c04c0c40211403140c01400b41e40404103840710f0a43c03030700000d40d1001c00d50200242580500100c4052050b0214020740803a0001074500b00c82d00384a00d2118504200e0b000a120304c0d45010b10f0300d603803000148101ba05c0d04440408803100140b2409031500074a400055080d00c81c2007940b1f141000000d001800c5a001d4640401c0c0000c83c20045580b0340315803050000b4508059945080c0910b5891201080b00d090080c100041001e6507400b030301c0c4241140942c0155185c0c035082c40d01078004a6084210018400040810400075040405515400c1001c2c0780c5192603035050b00c04240c02840c0380e46500700150021502ca912603401e5405090501e00404061040d5282c5440d06001e0f407200f669041c2000a2100d00c0c807020491018590203a01d24280d2090318003081441c2c81c0c174883c61440700074000a401c8009204000b0745003040804806845c040801070300020400190341c503031110189502514040441400c3c5601402c000e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 367186330 1250 367185080 367185097
    0x1b0d08040213020c030f03241c0602090402040815090703080409020a0e12010209010f03061a0f0403060c020c01080108160e060d060f020307260f04060b0d0c080c04022b02 75
    0x840c1d486d0340282034540350a80048902404081988604c802d28000c2c44001e02075400700607000c91803503000440c9840841d01400303010784001c4e0f020400500b00f5200c80c1f00030401010141c02421841f030138400c40e51000b540281c400340280e030044609102040d144400c80d011142d10040050f96880e80c010161001ea0365120656071040342c074aaa20000c2c0019001000e0200c0700766a07100c654440c061090f02211664007a0401521141407225080210000102407170f00c0034135070450034260f80c2d0b40e9000079500b11102c4080181c101790081c180ea0f507040b0186601400601010b040964030000001e250744d1080c1c0304444045040d400481e201e9110100420440e1340c121109002000384007100348040c0d0300c2600c101001520a07044924460b55414810889044041e140740542e1110383e4020341d44107020344240c3d0400d0395012100d41651f5100c60203007020784103181c0d40c8012490080b0310790410600c04d400ca405540104140c03030380d03018039007084280d43c01254907014160381d10703d031500000d001d081c2a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 367187580 1250 367186330 367186333
    0x103050c0409033c090e01090e1f020c06011a030a0902210f0d020d140d0b0d060c02011a0d060e070302030d171003020604090b0112050c1b0d08040213020c 68
    0x40a046400080c8800e1002509407000b00c0701c03440c013628003155010354a2056104a48800c001400411b1003900003c01489101c0110350b04134450050328402042c1c125003034203c0650000d442e805a2505005480c010f080e40c051203002d0f507240b205920402d10000304400034040c1c1d81c1c00c40d8011540c901809108820344008000031504462800700d58810f8404501c03125440f800c40d290041c0b40c1b00080094044003a0707680c00c6c1103584004c0060086410401005801e1500c4400d01c000c1ca860b01c1c01001c1280f4002c110102d1040788201f000783c07c54114a640c00140c2003400300610207030f00d51000b000701d1941d01000c00500101700c0b000c001d06020254000a6250043c0b9071245000c0d54410780011010041e05000201a01c540b0701c008000b0041b13100094010000b0f2100304018080c0ba44041c100e01e070b041c1410340030720f9004502d0b03104440c0e00b291182d140b584040b0303400d842c24403c040a8484003808200401141c025500042d00300c0c0c4006000070300c00c11100301040584000b580640da60b0360802e00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 367188830 1250 367187580 367187627
    0x5070f20190506011707030212070503031305011b020121110304050c030d0807080c0f0d060303080a24170f010606210203040b0f0702070509040609030e090103050c040903 75
    0x808820320303a00c4101e0191401c1c4101c00020555440107a46031603180280002440403d28680c00e000305048410081c14090080000c0010b1b2900d0070700041151490001c00f499805040100162111400900000c98640e003200e0130001070b40c00c004459035028000380045048030110520f440070700180490650700c1000441030000304070f80021011640002101075880001c614481162031180031100c940005403440003091107400241c000b000d050907500061442c281c01280d400c03040e910541d004400103044c190810003501043d1148a00300002c140d10601c82c00052495420400414090b004c10709c2050f80f410f1040760780400242d5044034003c2c0c024480966100390141103010b455807184400031781d40707104480c45045071085910441e4040ca599103d80c41e0396842c00c5600c04d0092905080d403141d80804038141e41d400d14264400c5105403c040f5101a0744d2500401745a001c1d9595406a5044030050000810214015050300c0c4103803400190a011411704460107105460342c0541000141c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 367190080 1250 367188830 367188853
    0x100e0a1a0403050609030309120306270703050109022a19060905010b01030903051812070803190c03050a03090602040f090b010f02031303150f060b03010311010305070f20 75
    0x190007800031680142d080c0c8030980c0d51039008903220300c01151030355041d0300210103e0a40c030703040c00091a00b007072014041064003848218124440d10315042200c1d2200008400c01c0102c03a81802490301601c4414819810240100148440010090800c9501074008191803140840401c450a0480360007100d5014002e5a41409030052152f1079080e1125428140c4880c6c2a500900a010050740d040d1b039000d1915080c2c1241c400681c2808102070307880500100000014a81002144043c000c040b01569940329440c1fa81d84410100c0d0100000b0f00038680c0b034101c086900413050342e40300721a904012600c1030151500344001e2040390042c0401010810000c24090071715408405590001c2c0c070303525034024075035800b640e8074002c0e5405419622440601840000c124004504015400034008115078019969000070380c0c0250708031550901010004205000c2209188003210b0001e003070401c031904210000030141079501c1040c4050005240110200300504920000c0c4509403200b5280b40342c82c4d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 367191330 1250 367190080 367190129
    0x10031a0418030f0302090a090209040912020d03051308030115050403020d080a021905060c071506120b010e010b03010902030603030c0607080703110f04120201090e0103030e0103110306100e0a 84
    0x1014041c1c0c0020400f40c44409610701030710072134050800040001510700d103040303d01c01c06075000708081c1f41c0198445600400042d4048812004413890340c0191802c4805030070f004080300d80c000d01d071f101c200b030700d03208401c0118224800f101d040d6442c1c2c1c217042c0307021100d071002500d2522943d0300003500070540841c0c000522010301c0240c0b1152051754280d861550000070380e41c0140c0c0c00541c000e00240c11080100c0c40d414103070300c0201001c070b1040f61004c9240c0d81d807070114400c5807100c0c0d1025581c50b8081d20510200300444a90f107001d44000c1c2104040b41d418003941a609010501a240c0403e44c00400b040040da800c000390b418150241085807901e24200b1002841b5100c2a80c03810301180c1801200f50300b411b0203006480324a42181500360074585440c90300102c000000d10140d040c080c0880c0c1c003003910840700070340301d003c0d60080e1101102c01240344001401c40b000c07140c449a20203020701c01d0042030f82c4e80c101c80c0001100741b442c00d20310030414240007880d182d507590300115610150603003110a2208 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 367192580 1250 367191330 367191371
    0x80721022e2618070e0f06030609100c090b12010f1d28020c16090b010507020f010921020f040501050102150403050f1b07080d02150c04030f15150510031a04 69
    0x1203c6e800b01540c0c80303010605a03030b0142990070341a290005015420782110690000414045501e820b40101c0d50300c1c031300040301e40d0000d04a00030000c440b50050210a06081e004002010469054520b01109004140e1110340140c44402c42d01c001e210240d04c1c482070400500c2c00195541c2d0111368506040100316543c0010203030030b4403e130f01560750004030b002e10b0384508220b450040e151b40d86882411f03401c0100907441b044000c3d05014a0141c04030f0020150b00000c10500b11190400c002001540104410220084055445542002e0040c00180d0b800300e0f008011901030000d41800741c4452070300f52628041c4500b03a80384000082008200351160640d500a10440d83c000c6c1ca5040b51208010340d1901e191069840240e03200e0380401c1c1040e09421042d44e8044d4400390742c1d5041c60340784da0329070601c4192100c09648010a0503440048203807203200c0c3c1620041d2805440c0091440c1502190154103290ba142d0141661280601d21500d030300a0400c0d245c46004204200b210700f00c022510704101c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 367193830 1250 367192580 367192591
    0x906050a09140c03031209030c07080d0207050a03021003020a020f0f070e010b0301030b060904240603060b19170c04090506040308070207080721022e2618070e 70
    0x348055040c1038590300418030390303030180000e80510720f02910301031075401d50100640065024801001a062703107190502115001e0100a4050328505034401f10091501c0080c2d003000c0d100d00201c3c0070030001641c4261480103401c50600f800b40e15010101e1099090840e16121181c00e800380002420b072014010030b000d01500c07105050100c003640ca13018034861601003400028108103102000c248545031294640758843c0c440e0448031240e001a0b4141d00300c4840115610032600d40701d207014410032215000d456030f02030040e51410804581050030640f03903807052248aa0100030038210b6540c0e01001d000c0311103c40c3c405807044c40304000c1c80c5005561084110b4050b400103240700e0201c1c0c2514800f02c2d90300100c441c1c200c0140801d40c10204100701344c9015520401480540c0c052240040c3c44404500040301000381d40540031050305100071501841500440c01040035049820f01c03150410b6108541206001d5140d20780da60361114400a4042da05500c6140e500c00c2c403a00150030001d0325026441070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 367195080 1250 367193830 367193843
    0xd11030105120c031902120f01150801020711010e281d010617131b0501180b0301030807060e0604080a031a060304031d0d0f02031203071e02010906050a09 68
    0xd030030490045450f83d001800c41649900860300840040f0544d044d080e43c1c0c280000c03d9080508441241c0b5460000000890412a510f0300f1102d03443d008032002010007080c40e900207514081c0d00341e66603602600c48542c600d0500409031582e40303050720345179042c4007189010224012000c6d034007003550b800000c540c4104202c51440ea440085088c003441600e0b4125103131034999440c041c0380d07a284c1002940c0010300c03000a0f8098120120081114920b111101a40405800c00107a0501000600302103c03603801c3c180d01c054600003002a00002c1003205d0440c1e421416481e00d540329460080e01820300c3c0d00c0b1881c403510440b014001070103405002400e000032076807810000c0f8542101078074003070840754040f20381c0842c1c18030020b801319002e5081d65040100d2044400b640856080011b01d10600c003d200344e51030b9041e503ca140440c18104a41c040e64030600c0045821407030011402000e00300d81c110356109101042188550301030003500a201403581c05041880705250a0b1900c1000b480500000c1e40c84 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 367196330 1250 367195080 367195099
    0xc02090a0e06070f050f03181c02030418020c01050f01091401050603040303051003020a080706140906042105010203010e090d360302060307020105041203020a0905090c0d11030105 79
    0x411600c41c2150800112000e014141daa0010590303d0040e81c05400060080c100003107096010403900862040c20005994040b0060320100185850702074620403100550b15952660f0f0581c0000030b8604840c0780155609000404514260103402040da0301d82c2d0540c01e0a050200140c2c0801040f410380f241d02d9810403a501000c003101c8000442071213560b4008108001050120340300e9044140c0c001c410305034560351141d0780d90124221011581c400212078000c0c0009209195108a810045444e54190f16040208450008015200380e1213103060940c500314181c0394084103808a0344019403c5002191250ba43d2441c8040152044407000381703a00504181c501c130305014411244007076947d15204d448144c0c3c1110340100c0b61422501100040041900001c011f9590400541c070407802d030350000c40c40b17041c245032031040412040c1c0c410083c50300511844074042d40c0180c24104654080300d82901a48401c5150740c4140700e01018442d2850804080b429030400010045040f1001514100304 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 367197580 1250 367196330 367196341
    0xd06140a020708030105041116061a0f1806181306110a02061801180609032c060f0408101a0103061809020307080d0c0524180c100c0209 60
    0x102c1c490700c1002455a24148010301c80d90078240c1c012901031001484442c41d160a049804010244031101250708039180c50a031140c9541080c1d0b0301507490010344094000d00c8010f40080c1e4420043c03012110036415000002e0071998941d0780580d00c0541891805001e0700b0007910072801c1105c1c10206882090403c00e03a070301190320702800c0f03a100803516400f512903900d6290f0400d415075001e8090442541d04d91380124000300c0c20a402c42c140c01e100c7c4500081c036090518014100c0e812014903094054108260300b041c40c00c2d2084411840c46040310059a1040300700c41d001c01074029a04103d400c0e11485090700303d40401075100f09610224840c48000401d04a0011015980c131401450309c1040f040c1103849909106401408180344000d0998155640b0f940c0103515101d40240e41030005140780d10281e060260030701081c42242500601d05031005111081d626065102803e41800003031000d44080280000340038510003c4c1000300441003c2006400083c240e002d81d000980c4180300303a501052 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 367198830 1250 367197580 367197601
    0x3090b0c09010c0c0e061f1b0302101806060e040305030c030408132601020301080c040902040f051f0603020a05072010050408070806040c06050a0905131e110301230d0614 75
    0x8010801a645000064001c4011240030b82e031589070480035803041c0010003404403100c1c0250cd2042d49481282c503110766080c24104140c500c194000111100c04000744400309520104917548007060409095603601c481c40d0401492142c0551420b94003800315020455040840041e10181c50070030010300410020100d141c201d100a10400d02103a00084002c10030b130609410400368bc5000801c0040c11240340d4000c9c00a0f01c001310b402001340c2e58110442041d581c29114070b40040c00c482d240c11800c0942d41e54000e0301300e00c9007100292030b051883c15911a4440c007807007100c40c03e4401030301c1c0c0494281c0046000d4442d8020703000d03403c001d0151306008100b2080000c0e0341841243c0207012050b00d1441d041040d6042ea024005c10000c20030640000b00d216100c00d2000450401804030014151010f4201d14241c0c0680c0b80c132162410f41005240c22006c02d21100396415030303c109540034a4040e086c0b0707800a00d414810300361a000498a100d84040c0034040d0310084200c0c031544c0c0e19458594030a007074130 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 367200080 1250 367198830 367198879
    0x6060f1403070521030d0615140c1011070c0308130815070c1505040c0513021e0c150f061c081207030e0f0604030f03090b0c09010c0c0e06 61
    0x182e007040390b42d103240845085101369050040070307100079280392079101040a01961500d4004e070502c1500d00600354001c90b8425114250484500c61260034600201d81450301c4044c480e070b00940070f64840d03210803801e0290701d044600301070b0311120200e5115583e143c0704105400503c01d24000c408040f00003e40604080b51840303403a15500d14503c82d80c0d49009058403010009441920416110801d005940c01c2d5481143d000300d01419040c86a2031510782045604140341000c280b400f4014072010400c0e55007444281903006864140c00d4445800c400100d16060b400ca6200505038040c10904c8140203480d00d02a0040006640303540407074400d007511180780384030004001e056800410645882c04101c420094104981c1d180200d1000000d40d4018642000c42c0c000c8403088c2c000c101071200309604607418548030001410188103172052521000c216a200030005a0a030710700040b182d90507071248481d48a0701c2d6101120402440c1c40345075042420f4001c8408a00810400e58101100c05070a00d51 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 367201330 1250 367200080 367200089
    0xf1103070b0d0510050a1202030616050a031a0402040b13122117011814060d020105030402031e03130509041509050a020604230a08030a0f090306060f140307 69
    0x5901e80841020510b004150051241c207040030200030104031a42d0f003010540042c004820021450300540c0101410124060441c60101c4407104200c4209a040b0041c0c880424050500150001e5136101d0f1088650b02010590343c0180300007004141d01040b4001780403e400079001040020340c035221009180031601c42c0183c801104081650041c18405060008207103091400c650b19070040d041d54240d002d001e8000400360300b030340108111801c0c010710400b0794000a5841200d02c5040501c04214080d0340e030324010f4100540040010155201008000030400c803804040180040b030200060711780c2c000303030f0300340e151400d07242000162498031040042c01181c100404038082444840440700410300d45c0000c642500484841e00096a11603006e800184040714948038045911020400c003040c441d150703144107120b810070903c52030b0307400800e0310382c410f070542011102e041540c8419201d0910302d500040c0010b041100114120070091510307012a0400b21024020140341c40c01c01d510f8a0b914000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 367202580 1250 367201330 367201349
    0xf06051f0f121e050105070c030e090601050a030e0c030d0c050601080318040906090f05010b0411041203030c0908100c0f0c24020d09060504020909061b03040317040f110307 76
    0x40c50b0002c0381c0c041002d921201d070000d50754000d0b509a940c4203803d60302d0403501880826120142501410340101c0c0787d0283c0c0508403035100e40e0745466000a080c0d400355020b81d80070940c2d90800800c1c0c0c04002c020042c040703030000741140c844d0040c01000502d00c82244108640600861000181c103142c0002981c8103585403191301800d800d8031005000080000300015501561182903040120b62a4084030003144e0180001260b40180003050000b65040c4e0b511a41c1101000c100400c03040c2c011403424519540e02d0701d00070500441000003101d01d4141ca402034401c6000f00d00600540309042d0b400361420030115240e002400c901d148060750300d540400ca02501100c3c1010003055040c20741010803140b20b4050360014201030075212080120345206108a40c0d05a4447c28803003507140c8081c020760b0002c1210300400300c034500440480800e121403010a403420b00f0201c00304041500800510091200b1600328401030720713160800c0b0b034070b4000d1500305441c20500d50025030518203001c20b80100303580344540e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 367203830 1250 367202580 367202609
    0x121a150309030304032d0305010e090a0308040f11090a0234030819020706050103050606040b031507050d05191a030a1b1502030d050a0204050a060503040f06051f0f 72
    0x105c0c183d409607111010403030030001c80c4041d40c00743c207090044c9101040325035900203540d40c14035203001807040014240003a036601c5030210305c0000c3da10266050348940e2120090000c06401d1070810482c80000c08055480520306003085141e00e144d85c041c26050703803080301403201200056000380001801c0d0081c500c2003021626040080380c000d41c3d005400920b6004400140401000c00004903040044220303038042d2118010001d01a003001035540080c01203904010000c81e41d0002a652214140001c24401014000800047c05801540c20403007070b041c0180454031300f2601441030031201d4021640c2d400d2a09003448500304000e646054100340140040203507135442e8a44001c0c001080c00c0b01e80382441d1081001c0b0308048080c104054136035143e001980c0f51440340e2059400d41d10000d08052400d8410301c42080140d40d034125103403c4450504000d9035030f07111030614069101243d04007400c0d0381d0411040c8003420030448401c00c0e00811802c80c3c08001915107003003422007204c80c46054540c4c001078 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 367205080 1250 367203830 367203833
    0x61202060306010c050c030106061d0a0e040b0a0e03070f2a06050f0903010c0c0302071202030a020405090c0a0f05030708030711060a020f0607090e0f07090b0a121a150309030304 78
    0x1c8104d000800c1c06101110791441d01500068250351803030700030798006104c650b16280080c5054134100b000c084122202070909041c50f85004aa4074020005000345e0801c10100b07650001952200411122047c103895640c811410840b0983c0c81504040f0361196a122421101202644e4002e054002e00c0c4c00405005151107c1100d02d03810804d200a0300c81010004d090040c0c2d0240f00710440590303c1d880d50801156035040190070400e02c0c5d40b0a83d040c80d940c140300720060350081640c00d012a4112000120754032002d26452500181ca820a50402110280403c40c02060503da900b1114101c1c22210010384620101e030f200d001d1380b00000c05070301c0d00c12000c40e1585040307005814004202c0c4102c80d04000c840518601e414000d03a03124020800010090054017a40c2c0791003903000302441108120350801c004006c005400601c10300100032004140307900524802c001c01c01d10240f035201e081c00544880c402160080a030050b24611a10403103070604400d0703840c0d1050382c2c40340c2801000f950a60380c45 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 367206330 1250 367205080 367205087
    0x3050f220206090f061c110304114609020a050306040c020f120a121a0915040e060f0a050f040f023015060a09150b0a110106120206030601 61
    0x1d0301542d4480382d0320328a0041358442c1800303000103941c414410300403c071040d0943c0d03007110180d04140280403800c104005c003013000d10310690340007001541d03041e000680e00440d294001140c01e504840500002903c81c1e501840d100742c0c4107441d40080442030f1003c0e81c1c0c1400c0703000c900c1520350510204070180005226442d181c4e005408801d034a0054400e4000030380d00e154200021046c42011001000c21034811499000d0f2055500220281040105103103080d441452040040c1445104064a1000541d2940402c003800d030501310140c0103000881e06035a210352542011901100c055603ea400a11800a9401494001d4041c0b1401c02a240c80700e0315600e420524020301a40c00400d8a9a510a010210100c4070b2034800001744041c1a54010300030f032420900048854040c001c4504140982940c0d9180610b0817240c4d102c400113180010703015080c800c5c9041c0d502000410301c02080ca0030405800c40724444440036140c00801103243c070303411789100016182a02940100c02400018520b501 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 367207580 1250 367206330 367206337
    0x321190203040204180305030a0b0306070c0615030212070305011a06160f0c14030c03013605070e010e090106030c140609030a03050408120309030f0913060603050f220206 75
    0x240005c05c445101150791086200550b00440c000b410010804c000c60009200d0840591000c401500182c00d10342001020000a48e9000e01460b50350002a1070030741c5107080c40c200450340500303c100030380c13040290300e80c44241500c0261510350030076400c4082c0c5030a1020101044400511140c200a031b00700d064007805400c014212032003043c501d091404035610f0003490006101340e5020008042540c404d15003002030411416009a0416a540c058220480310580e85085103040005032110301440500c0c0051403500064840d0150f050046007a00310721840078180e80e5440000300c0d181e11034524081c2220458803015044120742c00c01480742111224581c114440c0c014801410544448002801d1010400701240402c2d000242007040707003020f200200d0b80c110403038040c03411481c00f0041a9100d100d542400e82142d100003030031440316901c0b400e403902f20104030300c0100902070f2511000341c0101025119035462a245000007500001c44042911400c480e82e1040e041c007813155030031b2188941 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 367208830 1250 367207580 367207583
    0x19090b16090e090304062f1f021801081e01090c180602030f030705120709030b0a0c0206191413020414010803070b1506180907020d170703021902032119020304 70
    0x480c09000c29240301407118007c40c0125400a0069003424060b85000349400440c0021500d005010b80c1504038450f600d50b0007580828207140c155965804100264407000102000c0201c0c0d2500020a20b44403e13445002e02e40f1040e152011000c07000d89142019400a200c0d56005a004000d01d844103208000903680190640c1041c509003441001c2906141c00c1c125000400502040340030801d000d45502d40503008189502c1c00c21801c200d0710030003900d808006211481e214900e88540c00c02d07500b43c0d440440314850820f400482414807401910082c032300503200341e1107079042c03c03d00a03d18204950250407a0304400045107402c2c21550b51001c0c50b000206401507104044800042649808008150b00400d800b07088018000c0a0100103c3d840050204030440d8400c41900c60041d42220701080e18070420000c402d8990380d4000c0c00c41c040d00c900d6420300010700c80e10b8009076406400001411008541a40c02483c440070410301603000c10086442002058034865540751703200c4194010b50300503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 367210080 1250 367208830 367208867
    0x518010321120f0b040c140708160210020105060301141b09030c04091b0605040b03060d03030b03010e010903031b0905060304050a020d0b0403110c0f0105070215030c07020a061719090b16090e09030406 88
    0x2c4001d40000c1c0d0740c1414010340d1000f53f5181d1080144a180a2040c05280c1800040311412400e010301200910450602c04c4d41000d580055003c0140c2d40c10080f121880c20010300c14000b003038080c0380c044a6440815205d00e4440881c1001180540c02981981c0c15aa48000041c0c00d43d03448004022072042e07008010b50500da035620511295440c04c1c004d81140f06208000840d0810461a000b0112130119100b9820245180e5580840c958080d182c101185c0d03003294565200c1e166170034018200406140000c0d0700001502d5244100a0342005481c8114003d4492410810341522983d860f60030400c1000e5100400401c140103540c040c2d00a40a040c2c006401c14507146083d01d010b101030742c402c0e00c540c491688042007034002c40c0342007080040a03060764607060140040b010600141600d000c4e28105070303440103c4841104462a40c40b001807260401340040142c1000170448900c0c4800e41c100700001802d0000100f0905640c4603100c5c000c1d0741440c002d5180c10303e0102c00325011000240d42440d00d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 367211330 1250 367210080 367210117
    0x8061201090308060a05041404080a111b12150c0a120e0c030c01020d080a090f1e02091005060d0c050f0a090518010321120f0b040c140708 61
    0x55002481181162440707515043c0c40342c2440020080d4850342035020f41e216500300150f20312a60100c8000903040f40d484080c2d03d40b140d00c00a03064840c0c07008030b403049034507200c0c5c6000c80c180031489005540754411f0036a101001c080c1500c0e02a5202c81c9003a0803003042401007004181e000b46500002c00007642d45240c030040156403640010b050b00e007007480e100582ea0001c4070541e8580b0b0705004c5402200d100340010103481441c0b960181960b030009002c5404540d40302003c03418042075062007410550710000c190703514503c4030006060392000c00b03030503802194410000350080001d10000001c5d110024455800c110a82d05804c010b012070f01009000c114050001281c1c000d10080500a000115121000c2c2641480c0030f12490b044002c552030000800d81c80108080341d235803946650440e001a1502014100021042c1c44250000007441440c5180000e02428441c1950080202000c201c50074040f0050992003250802c0200c103c00100740d004200c150001055040100440030380450361200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 367212580 1250 367211330 367211359
    0xb060d060f06080a150e1b060f0304060f06090513020d020402070506180105090316030e0a0b0a03091703040b13050a0f080406110a030e0d05030409020d020910050a0c030806 76
    0x5603006a0f0111245603c941402410801c08043d445400001e0107000c03c0b1201380c1100841d51040001400c0f1100d8280101e0140d40d51601811110805c200202880d60713800d00345810f03401004c000c244842c0c45032410710041070070340c15401401c0c021060800b2104410744c0c0c540800805007244002283c0c03140c1d08003c9807001071001c0c41158413a00c104034a000e402085680e005007543d000511031680c1d43c20400480600d00e401040c0b000559400d807500707010007520040030959001075500060400100843c000c5145603250308105200ca20908090701c03444000020600b01d404142c8000301800300d40000035181c0302c04d410803524558010f604885440300a600d4012103924070100c2590714000024040c407400c1c1d04030710260b182c07031000001003503904001e4074000c203080c01078445c0600c1014000c0d8080280041041030340c001c3d204420085681c0c02c1d03c1079600c0c1c020350101402c2c0e0301075103c620398003194074003c00580341400ca444c2c40d50800c110395950200d410f500020140d541c000c948952016 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 367213830 1250 367212580 367212611
    0x1807061b05060a0204030b1806010b0706021b03031902091e03070b030a0504020f01020a0b06060d020d0509030406020c180610050d090510050108030c120f25110d0b060d06 75
    0x1030103001903c4005940d40c0c110308004041d203d004003101200701080740d46002c03545000441d2811654072161450311010f0394508000644210f400305803440141000000d200380001c001940034034540300500c80b03081d40509211059009204403e50f02540030105048075440340031481164250080030b0301d84082c0c0700e440180c0141c10642e01480c486a49408210840c01c20040c000c034610b2090004111000a40c1d4032058220801061140140404503070001038000640650b251205100801c6c08035151620b44680d4980140c41100d00506c9003540382c0131302c1d003401001e103014600004800842c40c0d40350401c0c003000c440c101e40d00d0030400200300903030060f122052260075200c1d032182d009080030360301c4002c00d402602d4040c0c1200845400800080c002a0400191907247c19012000c0f070340c4400c4034010706603450003040302090719120400c41c00c0e440c1e004105a00441039120f0f05003403100c4020001400300700420280020400b890850105074a49059070000d84090710840c00411021074410058 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 367215080 1250 367213830 367213843
    0x9030c03030705210f04020f0102011d25050a030f020a181d0106060203070b0907050306011d0f1005060c12040b0a11030a02030304020913080712081807061b05 70
    0x10f080410700301e10042c0c802490040b440c190418607600703410003da80c4003040c240980001e02c40c00c2850700710815a4000c0d009a4000b14045001d00c940a515400c030302d8440c1141c06030086000ca400b4800001300c0d682402a00689030f0140c800c2d44118256659108041c1e40518142d0780311121345000240901c5601c080103003003040c0b04c80803c099007501c072031000140c58058507000c0c0341d0501030140580e5034004140c4200c07a400c003034614065250102c03058102075442d08204e030517014402c00840d0700c0c000461564103003103141c503696500e030765004030031040c002007580c88429107040c04908119901d0440041c0844202901c1a81c00700516500011200e0344558404501c181703002c10b02c07100864100c690381c0e00340c03090440550b103484e00c0000002d40302c2c44014002440740f080000030070300503035600240c10640c80c0d104044640c0c079411824146014020410200e00007460800040c102c2090102e1031401e020040000b08841c41c1440819260004241e05107844004a44903800c0482e17010442c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 367216330 1250 367215080 367215091
    0xf0302070c180f050c1c0b060d1413021f02010e100c02010f02040f1203110d120b06090d060f0b061612170103030807170a050702061014040509030c0303 67
    0x411000c0742d801c1000001d40701002e05051610b4544001c201c002801042100c450002078802c04e0741c50784c0d5200ca618000e00d44071a9143e0400d0001c035a455202c0ba00e5401052964200c03c803090950341c40c10303000613000c01c3c41c040007034008880d62507444580081c0e03510050b00602e14000401e405208001161174102154122401c4039181e404080c070040c1c080c8100c20340301d4602c0b002585058100b502000400501d03108250344083c3c01c1c030781c01c0140b61082c4c60a00048042506440e407130401000700078144240c03101128011480e104400095145c100200c51040038007400110090146848400040411030821380241e41c4841000c452035842c1e000516003600c1c8844c00111019031414110049601c0401d04428082282a80700c104482e03a11414112613040c0b0700303040b495a88903800c4811031b50351109a22200c4132a428050700c8100c541289100f40440c0c4e0850305240d44000403842031401d20f110309807206001440e00c40060400750080b5a020004604417494030300c0e61031341d4501d1a40119003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 367217580 1250 367216330 367216349
    0x90b0109080d08040b100501080411010306030c0e010f060503060d140c030709060905100b0417010f02030c0d0e01110702190509010f1401020703110105160203010e0c2706010f0302070c 81
    0x204030800441042c0546c100f03400d401803005181c04e040001c1e22000010300046c0000c0e6200006020360382c841d0300800c1c0038581c0600044012552090480042d0000303004071110452901404101584a00140ca11a10300107000f2002618941c580040c14452010501041d000b0590989020b0320304010520091080d00000101c203440d281100044810140050785c0d0821b0326003040181000b1482030320705942107202c0610140e041049601d004106c0c40e508107216034001b008100c0c031498090007a00d000e40080d10140304420780f03004c0260889540b5500c544002c00705000340d48c0503061040a0740031503400c106841d04419115000a00c40d40d8017684a24000c3c070384614140b00c602109841003211200038002840301500359a649990f1042c4642400c0c10030030b000c04d0a07555001c02903800c802c080d80143c02005070744105a8100c0e22808014080707401288685181c04c5400c014070b0840e0b0b842100d020420b40c080c0c44102c0112100310769070b000c1c2000c243d020301424000c1410b000b80c0c100100030154 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 367218830 1250 367217580 367217597
    0x807050705030106060e090a060609030201081f060f020c0a03171b030c01481b0b01060906170103060c0c0c080106170d0806090a020d1104061806020304090b0109080d 73
    0x101b080707e010061038654840d08000c010424643c2110410701a00d80c242801c0803260fa403505036040402d51400c600400d0443c1d0380300040c41c0c60b04019008090700321513003034a0403c060101032000f46e80052100038542c6c1e4800413003000400c01440605003400030f03110100390b0070418299241c0345411003110980036940d182c003800c81070318001240045009010719103680304201d15803c4620035043c91529030034070009040704c03010f003440b981c04c07208440310041d6425004801070600e198410070074012040800c1003240041451030003200d41c40e00c0b07000441654003540e801c40c1e0710034024006100c03880d81030203244001c020000d2904541d030005803800100015406e407400b1208200112400d030021140d411103e004100c0c158400b5849902c486d00755000000b64035100c03a0100244180114a1882445d00c1101d80024040c4001442200d880d49e4039400040080700d4035040c0550b0601c035600140c2c0c000c0100b00101903c5402694100e041410050b4451381d544458605200707400846a00140fa0034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 367220080 1250 367218830 367218857
    0x1a0306030f0703030e010f090b03040606261c03020715020310060503060f0d111203041503110307030c0e0d080705011a0109140a0f060801090606020a020d080705070503010606 77
    0x4126064041107603800421002d495070320043d0480c490000301504101030041c407030205c1170103613000b40002c09030300003915a40e15043c10000001c000c0b90054000e01407450a000c60006904d0500d1000c49208001501c20344113200025000c8402c1c109200003170640038011000030425100702c2054900c50700760056602e1400211001100d0016040242070007002d200f48601d90302c03102100c40d040c8109542c21401501b550610a5807421300d1148664420750002c2e44d0b442958000c0050011110100400220440d0b054419415116802005801c4090910000f6900c2d4480e412003405002d09082c0036000c140594086000304140c100d00740c800c1ca10000e66141048400d20a2410392035078140413002c500c941c0c000003813040d6407034400c4100b24102140a5007203980d458001000411403c0c075102d50b025586e200c0a01907007000d106008140c1e24100300000c00d20700200701410000e42c010007000c400181503403280312a80001e80d003901c0c41d200724000070501c5c0d20248600c2c0c0103001107488104130055070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 367221330 1250 367220080 367220083
    0x1009050a03091a1218030a020c0909060108061b0c01180b1b040603110f04031202060a06030507170a060c05090a0f0b0708030c071a07030e03031005010f05041a030603 73
    0x103a4003078000f54941224456480250710305a13044011180c02004454842c03503040c0190410320800750055001c0040c00342205900003a5440c0804000e49890034141d0340c1c811740a45444c02481800d2140d000440010258815903081c1104104401d5119042a050750710726421114108410000c00061942100a01512007101980034200341d1080c3e0b40c0c1d107011640e4080c51b0203207214403810316071108407003d46400c0d03000584240791525421030b52610794900313001c2c4191503010903050141c000c490108140203040d0107600c054a03002402041303260310380700826080141490011810340502c1071078000180711401140c0000251340e8a1989404004040044001281c0c0c07005091201540c0300304103041200702580d07900d6400c440b5041d00e0303503034007a0600b02d10f2107004c100800072181d0f2030102d5010100c50302c1d0309003e10000c2c2d41c100b168205400b2600d0382e0740f006032000714256248140c108020361044601050750380ba036181407030811740d40b13984180301c07a42204030058800c07101004000315420f0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 367222580 1250 367221330 367221347
    0x3010f0608011502120906040e0f04172d0d0504030806090105062106010c0203030a0801060311180f04061806090f110f071109090609010b010305010501090509091009050a03 76
    0x108004030407190412200082d50300c1002081d0a0364171640490207442650b20002550002c00d100d0140c4142d52030914403044140004860840d29005181c00c9151502001d10546c3e800c840320841c2d03918250b1450484000a100540c070a84031050100203200000f0018094240a244a034944012508020040204a4070140c0209011f5901407054415a8006900c1290814602205990140c0340d4500403034030b00703101c806c000e03402d88400680b10302915442000700c1d04a44865a04008e8044461040c2c01e0910900021010710902402e00305280d20f4010030103000100f008000191041e900d005d1004180443d1603035a01d400c0e61803034100700b9041140a40c00f400074000c042005407402500904245000c3c14103e15054000459a441000305180c4c00c09199a8010b00110705071900840c840d07980c8608907180001e5500b06420340c2e4144d40680a624180d900584803400308038240b00c1403084a08000340301142e10f2250234020b20b40011980710b50801140500c010f0000e0f940300d0308001d0308244 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 367223830 1250 367222580 367222589
    0x2161202150c0a11101503060506010528022b140301060206160201060b190e090f0615042102030d0512190b03010c030b180f15031203010f060801 64
    0x1503140c0100321070000d03041c00f10348910780ea81c10641050120f0780d40c1203180c03504881800211900d80500c424800000071100012248191030501c199030f1a480111101d0145281e0100300784800d10060741c00341501c0036a100840b2a80c8101c442c051103a4040070003444030140c2000880496009601240d035100c0122014440202c41041c6103500d0044000d565000040040a01a070020500500c1a100790060401000810040c680b10740c05144640350300b910401806000c640900031491090070103000f11442603182201c0d94940d56074038400d2000b0b1001c0c0d0500003504000401001c20301405000d007401250041c01002038020000b8814545480541840e006c1480400d1042103807080350f040385298481d03180d103040d010001c0c144814202030306060384400d505509003031480401903130542c0301403041c0c4800c882810f04220114140340f00780e070081c1e4595026a00441c0003a8100c07500c26a140079004001e4100c41402c410b2503c01482a0420b802070380c180c10040d101081029032001c5440e0151 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 367225080 1250 367223830 367223863
    0x180916030e151803121501030501061805011412040b0108150405060c1e0c060a0c09140411040b04080309040f1a010804110301020f0c0609030703140d02161202 70
    0x607035000c8100e03144100050070f00700804a02260212850028015210428020700e030b642014103101e040104440082556240000d15010001401c144141d00040d084100101c08401040c1010300454013081010344001011608001040e0400d00741c40c40c0703521660103142c41007c1541414001401d14074020001401ea001040520000c03440c04103a045d003101c242e81c0d000b030f07540d0b01e115900a240c4001c1c0c7c0c00104c0d00200804c1040c1c1108001c101f4904c18108a501005140201030090303507028110f010700601d205444580c5412828198000c9100082e01043c581c1032070382c1c2e00441c0130b950740150030444042d00046049001e50a15024002c000f90b00d8501c2031144401d9009014110401415002d0420995a010405000484c10001464030303001c1d0003075544801045120b01254030082400ba40ca00c650800140b9203100802a0b940c2140d1550350150700e20b10203007a2200715040150580e040d0340d0300b004a288500401541646968840d40101025508130040a41020000d60840742034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 367226330 1250 367225080 367225093
    0x31a040e0304090207030e0604121502030705120604020d02030112140604020f041d16060801140a18020c0a06140901090201050a0302070c0b16170c030f180916030e 72
    0x3800408401d407010b850a5000068442c001410211001c2501910f40c035041a80010049a0342c1480303074032118118000d040078a0508001c2003801c00300c0c4011a0300c840040e1061110200c041c8030b51100d250043c00c01800982030001d240d401108a900a80c40700d950ba8130300209041c2040b4011550005160810300981590f240a40205680b01d8182841e144107503a100700400301c080508051101c4200740340202c1d0051940c000d91040301c0daa00d401800c0101d0380b40000000e04034080b2102c00c2200310060300544810f40382000c0b03c14819048000c2c0c0144503000d0040484440040101c2020b190080c031006c03130141c1d02a0a80e504101c03000e4000e4100c3d9060041c4c40340583d03004011103d40c880c8074a00142d8642e05818001c8100c04180c21a026144001034055504611203034204582401010a50600484a200d00c406c520a5802002c21604244800c00e42100841d02900700074000b9010a4101c1086400150006404503214040030104811194080d607240c40f554200300841d0000340709 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 367227580 1250 367226330 367226351
    0xd080907060504050d03030216120e04051005012f0606041b0e150c07030b100501090e010902071403220b040509010e04020102070305030315030d08040221030415031a04 74
    0x503c0c030490041c280600c8154110a00700352180c0d0480c0c0c0340c481846242e404042e110b01e030410941140b0301c4640c0026110320007a1089103014402c20780105219404c0f520500d280c800103495203044c50826107080607240c01d10700d1000d10074594a20043ca00c80d03010701101d140c24800c000c00c581e121040040704100744c012107121a0703007208071483c15a5040380c1c840c07004034101109080c584181822041240a048400000c200003030311228055482c101d0480d0a03680c8844c0116101180c62040c030218440c0e040040004d1991540100301d46800f03440340d8804240a40c0700300340340d0342c410202c1c0a1120395140441c2c1d0040f1034007a0352406400faa402030751402d482d200003d0a509018000c801c0c0480b0381030701003000c6a00800c01c3c20015a840b10580b61a480c04a044c0b04010300911405402801348182c01c0000501c28a885c6104550062825885106294180c0d82c80301a440c6002c2c0d00340310420000c0740ca50200c00001d41a00210750780410a000d0380303070300001842080074806000d68100000042d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 367228830 1250 367227580 367227587
    0x609150507050d0804081603030204090f14040b04020f1f030c020d020a0303230103030903141207080313050708011a0402070302070509090c090415140402010206060d230d08090706 79
    0x840c20181382c80c04185d00d80c0c0c1407104541c0b00d004809070143d008100010b0404d509500a0402c0b107130a99401c0006a4102d40600c0540d0001060090207948440c00030340040d404114881c1c000d400074010b0108a0142c0703021450740510402404817034030300340f0102d82503c1c0c0c1c90700520509402e10300c050320030816503240107580c03400d15800040030b06896540151070704c0400c40d0307030907846d0108615505503942d480c1005020408540019281d1180300c0c0390000c080300d4002a0352071154405400f051408000b0740361821a504040d1558113a00f90001c203000104104205030000707000c0f5000001003003901c0300315840f003000c1010036480c0114010b012540110b5000301d0f02404a950a4a102400d40d130f40075980390405401d070307611076400000d110500040c0017484d41a07500c0840905020088490258066810080100c0e802401030b400100010480c0c10311020320700001e4840c020920946884600c055070715209801f1440083d404007080d0784c801c40c1d2140000303800c01511000307002c41600300079008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 367230080 1250 367228830 367228843
    0x402090901091121060a0b0a060905010203040b030405010b031b0406050102120a0305090f0d05190305040f150b0409050f1501030c09180501020c0106360b0301090507060915050705 79
    0x1107125181d800c1d00315102842c07000d160901c4c0c10165066402da803600d03204440c000e100034120700740903001103500403504074004c10115007601c10580045090615101c00031450b544000c0c001c0721195204d51a00b081510100401102c0c520044114004900e500c01031004546c0f10354060707030443d1300c100a0307501c0c51620102100c02c09101d03898041210b40d0f42039415403901e4500402018648103100c0c4008445500c6006030281041c040c4006000b058818411420745005480c050429405216081c000030400e40d01c11144005800011402c0000301d0f000804885c3c05035020751301038011803050041d41200780111540c116051018031003650445e1940f00260005008040c010341d916003444078017100720a244c81c85a9403040003555104400e804003406848144102c6000071101d28905541004140301005042d81d950340241c0c0000700194000c000e0300b0242041d5805569907035131207012650074400303040a88010703205c126803645442843c1ea0702991428a160800c0400c0c40700000158021402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 367231330 1250 367230080 367230113
    0x5030304050601230105041e051002030c0607030b1f030e0a0b01050f150f03070c081c050903041a0906070227060f06030a0b150a02010c0207050411091e04050f040209090109 76
    0x6074240395608c40032581e0380003100e400045e40b200d8503081c040310f956070010003010503442003c103803010b50701c681d2001d41c00e1f150101020740c1e2021105969481c0140b180c00d501c05914010710340810090050030b40b503030501140c4041504d6810250f801800b25052000010b041000160358100d0450820010203041b80142105a1040940000070400081c81aa401202141c102d24260741e100d07240f41454110501789003908007118102400074001c4040403081c3d404507490310700c480c210035042808854082d4041581a0b074448024040c5501681710320401c60500d03d1051200d2002010500d1415003004009003210308c00c110700c85d815001d5032610703000e49030400c510040104801d501c803000900304203801080045080c101081051f00560705410400038801240c095510b0a07071104140410ba0300010307050b1b00c0b50032041003461480d00b403201640c1c0c802941c110300c2441c0801385400160950b42c042d14170225900a0303505010039864501182c64000135080d008004010b50307070742c8200420b102c6000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 367232580 1250 367231330 367231349
    0x4060b04030b43111203070f0504090c0509190f051c170405040c0c120f0507120c110108060a030b1b03010801090c050109030b01120f0503030405060123010504 70
    0x8410f004604058081401625141c0340181025002d0b00a0321000210200b00000300c50441c4806040e00c00301d510340c650544c004500c2c2c80e41d9206103003560801020107035103041041c200070000c3c0d200f0440c40340d141d4144050341d03076507929001c6108001c0240c01c1c03400b61050910111000b0015200715600c031b4011503005a510940304480303040710103e2842051809042008002143d66030040342c01c0090065070411102084180322002c2c045a03c2c4070280b60040c07183c900140d9420440f0b000e130143c40008071a601d815481d22105503204401c80364030018000120315103408400421044a030340e001701c0b500c20319200d26503242100c0040c054810300c1c480604590030f4100031800e0341102000031200c043c100c425440d80d03541c1d03030f0001c3d0b4003c002d02c80c0d040d50a000942e401185940c40f0304403140850390003034050485a402d280840c032515801c103134100d550104004c0d000b4000b407018000346100340e001e01c1c0940300755850040e0b60388441c141544000c40d400c40c0d210703944030350f03030307004000d56003a11200765 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 367233830 1250 367232580 367232611
    0x7080d0801090c0302040b1206040e0307110609030a02120d0f140703030548030f01090b032b0305010b09130b06090307080303011502071a0c120301060e04060b04030b 73
    0x18198006e105941014000b094001801010194600c02482c002c00003900c08010b100079400166440f03018403100100903441c0e034080c44030203103000c202916081d100141a210480203941c0090b0f48e400ea45d0044100503009040b20a484c19008200d4a810300c600e4200f076581e01e0303010f880144181c031405070003c05047d6110080f9555140c48030340d00380326042c0b10074601c62208a0b50030580081404082d5142d0380301d04a6024440300c841c20301501d01400e0360348201d04840c4d003401e1000024101c15251241c041c0705210082000320703401c0d10703014083d02320128001c0014900440080039071341c0503040480709c08801c02c07410b00c041c1c4841d80b031070003070040704140014604001c000145c1a88564600b00f545481100703004984080c011000714100c0c2d1134800c2c1000c2503480403070184d0b1501c1c0319100d040360300b5209003c0d51141c84513540050100b03150b94030540d80c8513200d101e10540746420a802210010b10404460304882c01c151103050702074255041840d00b4186990740703c0c0c5201e40c1c0103000c50200080e86 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 367235080 1250 367233830 367233851
    0x7140405012f0f0f0102040308070f03020c040c1d0f032805071710060e24040501262a0a0b04080102120f06010905060f091206040507080d080109 64
    0x10040c0b26903030300510121103158002c0400056036040200c502d0039080c003604e02c0c5090300e940c0510858040340c0e8005c00d1107042029584628141c040400307010b41c198000c4600701000d50303039184513840240c64152a800d282a6421124182c00e55108403c9806042c40c48901d555541d00021030129805070300c9405601141d0f144658207088003400b2006100b4801c80c040420040140000100c00d0b003550421180d030309150001d484207071001442400074186040c0c010904400c5c0030405032441915400d080030180520380c0206048540903444881000a046821210804c0c42000c00c0c00100040004202c55840b0b00129901c03014070203a2061105103007003c0605a07291801024010043c1c0c485d0750f91a282d503812a01d010703601481103203425441c1140060180354074560341a00640060755850020341c10042400b41030740c40b5007003590903418280040e0600303036118130030307500200c1060000d07084905251030030600e459410380050400d40c120f45c00040045a125140c0c0d81113501556012030324070141c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 367236330 1250 367235080 367235117
    0x321110301080105071e0e06070602070213060510031a190e010f090507031a011206170106150203070b070807090b0a02010b0102210a03020d2c01050714040501 70
    0x11012090445480480002542101988010300c42c0305a80c50304e103000000310a6100038001810304031400b10b4032408044209003840400341c2811445070400615003485900014a4510081402c030891902c40005016a00300150031541065040c102401024138856024080c401a000740c41e0181d038180d40e16404080c8041c0710480100000d8543d11010758588501c50030a0855016002419083c24007290308188244a0000c07564078410b000c1c6480e400480045511003039000348240c0440c0c0b51003010070000580e1869124044845000203211407400c410505560241001315081d9003040c41080d0101d40300402e502da0014076450001308542e2143e10545100c0e01c00e030010400004046042c641d490380541c0483d400032001d030211000034a10100c000c12400720307410410320000c8103003e140007840c0a40c0207000c000c01c5c0350384081685820405105116804921100760324002a074001c1c1c42d00c2c0003031080350b400010903e02400458082d045c40440761041c0d208403130420500440b046070b054031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 367237580 1250 367236330 367236341
    0x1e0f03100507080702070e040f0303150305030a050405030601051c02010804141c121e0f02090d050a0b0a0b030c090702010b090f01170f0c0609010915031b0c0321 71
    0x105404020700c1c1040100108080c408440e284050710509070040307100b4031100c03611441a9400070003081015080d0346c088018044400500b014075505100103c00110180044e04000080d9030380c00303450f0ba203000d082503d4508180e00ca0b6000710503103100c414141c06017803103d0602940a00705003800da19146402079102c9030310003504040f030192035028045540d0b242071045004103296a40f040b44031241544a003101c480b83c80801d055007222900c00b004070310542000c5004e840c0c0d007030f005007007640ca034010402c062410b010407101d5800402d02c02e0704001c02d9500ca903401c052441000c010b1410640080703035403106012107640c4603606c2c550000359400d10075007001203442e00152000c41c1c181819403410840c0304080c09a00c01c9903400014031504040000b4081850402140c01845620b14003402c0c44100c1d800910814100100400c000c5040d20700c02c102815610880c2d940003a144d40e01034a200e20340001c19400c102041510b0003e0404650721010080701c407030200e44100d10705d1a001941200920 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 367238830 1250 367237580 367237603
    0x14060718081203060102160b12010b0a022104030501050f0a110c07120f050d08150609030703260f0301061d03060a050a15080309120a030507060e03090a14010e1e0f03 73
    0x4800c00c4041070810321140270301400074510f10701c8032071643c80715611003280c000ca07601c45005901480c400c4c4580307083d150f049803400c0403002001f07145c10348a448039829680111140382a21203a42c003400b1040884e881400f96003003122070120304100025001d40c0d190b2003c3d20a404155404862101c14401e101100c409642e6000c42211480c5042c0d5030007409148046603a0021421400c841c07501d03c0c1840411601c0541c802809050b5460850b980c0600c00300e1160080b0785280c00702e005180d150107081d0b00908541c501500c1081d00d0351304d004002040604d0f028464140c1c6d00a41e000c501141d00c0c00120b082d04043c00c10310202d50359950000503802000c40607607442582d400a500040c941c0d0010005040640094801c580b403882c8259105d81da034a900580240003410400c104404500c40c1e82c000b0042c0080e0700b0982e490b044140780003171140041600f102e000b0405204008000e580c0105100340f03c6c0000b600c0480385452101015210402c0d801a10b034012030404052401c560303070034070035080400d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 367240080 1250 367238830 367238863
    0x120c0102090d050c0301060f0513110d060e01170a0c0b16021306090b060313080a05120117010c03060503060703090501291507050c040b03010914060718081203060102 73
    0x1200c03414004c3c0d91300031091401d40203503e4084045050b80b440080c0d20255280507102c10344a0314003039103000050251043c010710400c0d050142c01201003041c05000c0c01090b075101500c0700b42d4149125001004884191904a9403000c22400c000607403c41c02017040b6a034400b0196103400c0c01d000508821582040b00a50012000d401d6602510f013643c40142030720002441000440044024481548010b55618007001010002140020b003000014900701c892840c06a0030001d20030b8a06c0b1900f00b02307030000c009078950100c038038031150003d01c201222513915140510409241c40301013500e440014041404051310b52001d40306000e025001005800c00b0311107864503040d200c110100b014046200d502d8481c201c0d507103008144c00c500c00306866034a900308020385150200401040014614020b403240c041d52580e10300d0021404020f034100d00100680044c0480c0d1401600087c014600400701c0c465040c2040d0003440202d0380080d0500507400c2075520140e076078071042d005038602400c0f0403c0d000c40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 367241330 1250 367240080 367240099
    0x108060622140103020412020f0d150920100806031e0717060c0f0313120f030b04060e0f10050a14010201050f0601120c09051005030126120c010209 65
    0x151200c1d072159021a0210b03408955620324203001101a840b4a00c213052131504141401009071900d104208440a402405030781c110301e5a60f500c0da0181c41c40800c0001140d69190301009002c00ba569421241020054074591209003100040949004c103c001c0100040500081e0740ba480401c510507000f14003005c03140d00e00342c81d81da4103039903a0624041c40d482039108041c9034100c03000009a241c0907020100383e080c2001c0781f034144050740e45c20061540e1080107401c4440004507007004102c50341c00341569160b4132594078422000d01030704c03031100310503005900c0c000e810400030710714800c3c2d030303070402c84041c0c150039039440d1701e20480e454038020703000701d680010501000149034007011042a02203000b03030024081c42e55184d002071341c000c0003103172a50b01041c4c0c3c0c1c0c01019014107544c4d22000d03031010320341003008941d500c0d44c0c0881c1d804030107100c0b49000300740000b006008016000240c030325828441c83e07014040c040f2350301406880d298112140c005026011840071010f4400703405075180c0000c05003040c0b04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 367242580 1250 367241330 367241377
    0x5061c0312270213090c0e06030c36010f031103150903130602060610120f0501060507050f0a171b10020304060f0903020d05070f061b090b030601080601080606 70
    0x103a0900b4030100301d00c1262540d201102416650059403030182d08107815405961605251182c40c18004200315494010000074210556684030700300c80b282c2d440300d01c028503000880c0740d140c0a82c2071a005400109070f151300400808800200d504281c9500044800c45285d240001c03900d810701407026002e1800b00c01082000031078000000e410443c81c070340416a1600d540b401c0030380e00c1e0001900c0503a042011aa0311040141c010f0403861060304912200199440303058580c101228800c1c0c00c1000001c0c800185901271101c204604042c0703511400c050201407505d50384000152820304155045090b000c5010790451011300c80200403812843e0513180742c1881002e025000754411078089030341718031b45100100903124a210b401344e6154160010035040d034110009840c290015401142c5a91459982c200011118005e2410401c0041d00d0800d61003200034018144040d540c1040009040c14020048260390007840e041c1c01c100300303081c0503050740c46450100304c0340d22480507170303e1070070544001604 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 367243830 1250 367242580 367242641
    0x1309050a09020315071b1a0a0e2506030e100204080a0201090e1b1e07080706140c030c1b0105130b070c0b19060f08010b0405061c0312 59
    0x7810300c01c40940b0304481410206180c00007050740e405c400520809062a009042e4801e654050b078024844603114000c60014030111140803201ca0512644500b1800031941e01005848031213541841807021212146001c8030307155450b44964801c240d112a008000150240005082d101d10500d003556107c2e00e840030140c0d9100301c2c100490004202ca20300050b9880010803103806a4142100301b082e00c4440701405080380c21501c0c00408204074494920283c2c1181310040840e00e128144042e03d684041c2401d2081340c1d1103008201d12084060304016500340400222a4002c40d04e40301d50340c443d0311800c500b40001c0c0900714003001e190310300014040c80c030308002035000c0c0c920b210703407550301142e641c07548201d442c54582e100040c058000700c008103842c421485000343d400341600000150b0300da9a1080c0702c0c681615079100c010541d41d6440300c0c0116092500401741d1005094440000d080610000100c003005002c0010b410840c3d8443c2081d400030881c0c000d0040301036030210380d020f5000d1008841 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 367245080 1250 367243830 367243841
    0xe10021510030f031d040605030604110126100f051c030507080a03050f060609034b0105090109020d030c0c0504020c0f150f011509050303030103030e240d021309050a 73
    0x244038005d1468502c013246032600901007a120301902400d082d85903503076541007030581400300328144215400815000c14151100080c580c40450b01024a0b00300700d004410000348541040e001038001c10024071264450005407412460141c59250480845083c1111103001d0220b00500d14280010400340d0300b5455040103015012006c5c0c08001522110104402803203140c0e042e81e0142c0140c05240d40030b2140500d882800751000000081c408403001c3c04010b400c080b803440000c40071100107a010302c88002d1040644c440032280003000b000c113107070700003404220040703100900300400080d805d42003114045451008020292003503444010f101e070783c1515140c1d10881c040b064440c0004241c0500a001c400074000d41e0703901039900f020f900708554151101c051001000c1032140c04000003405480820045008602a60700e0040e40100c103410000b50314914900c83c440e0894070b4110000400d10201103501103420325000680d10061715140c8404408164844141d5624080c02c000340794400e84c108 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 367246330 1250 367245080 367245107
    0x240509010b0a0e010501050912030f03190c08060d03030e01062d0b03010506033301080108030903070605032a030406050105010c0c0905070c02040c0f0e10021510030f03 74
    0x2407141030800d00910100103540e10410041e00711060040040c2c0d401032000b00036001d00a021191480700300508286158060f0421142c881800420401145601540c01c3c5c005000c610b0300384880c2d148448018280030001c0c0c011441542c000c0b030701c3e0f13080500075841b03038030340000b40300c0244015a503030700c6104600d141d28914068a0116030018803800e281c80141c0c002034900c0d00c4030150541e4200014461a0b1300010480c002d44012005051404d40c0300c0030204c046450040f51582070f040030340000419284040e0301a40403a030080c0000c0c0090b59000c140701080c1d400302d03d0071135100c1e51014040030740380d45150f060740c4018a07003120f00e071301e50b24030b4600952042c8d02400c030030711642e60303120300444010051070700244c5051003800050000c10181d411154008805181a448007061900054216a10380c4210000b082c078100d0079152081c0c0011000d00004003c84040b400b2160030080a5140d0040710481c1600500100c009807210080c6950302c005541c1120300910400940e24000e031000449190 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 367247580 1250 367246330 367246333
    0xb0d021216060e130e0109020d080706060f080c090405070b0d0501090c1e030b01021516080a05060d060b06190512240d02180c090f04060807060c240509 67
    0x1400b041082c0180d01038204000094000c001000302d910f41389000302911041e0042a540752201c600260b90340c4410101411300a00c0c0705580c2d9482860a101141d901d50301c4040001680e540c2040340c0c15003c178403da21540251036505680d82e031850658100310564100c01045900071441c2c10051803283d0245050700d403800710410440080e48416103c0b404056902080180c5003590700540a1280d0085100504180100c4502c5000041c54400b00f040454403034243e03888081c18a01820352201e501a00b00070350390410071007401d010f00450940024080094022502e80c1903072422034548504460840ca180d5003441e1005030124802451503104116a0a10328200400704001030b108240c1214814505041d00341f400407200248500c40c500150160384c17042915840b4422a907080f1441c9114020083e02c1580d503800c0c00c41008060300d42404083d00440c5041020320416000203001c005848150601d01c0c4c0d60000b81c6010210035841200c0c1041502c910200d180342c044c80c2d03401140c040e014500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 367248830 1250 367247580 367247623
    0xc010b010905030726031611131413230105070f021504060f02070c0803130b130303140c010e06190e0705040507020a080c150606030c0d0b0d0212 64
    0x242050b680c3e01300c2c0e00580f1940c03001c0d60004141160301c001c00d64030410aa500b80c17820306011080180602400890640e10100b08061484c141d28000d84420101c007a0180100f1044507032074840600302100030429140d512024041406101d1141c400b071450346003448e020301040303c8402619010b410300380c4100001c5020f41c428141e600340042210b010450b40d880403035003580e80301d85401d0081d150922110301c90550801c004404582c80c5000c4030b0103030201e07500442d034481241102124000c0580c1c017004064805200d4680034061f40040541200d8040c82c0c2441c01e0b4a81d010b0385440c912580314001405c1d0305e48010b0500c084004102d0754805c1440003020b50fa1284001c3c080d0003a1748607160700b00c0d19600409018803652030607510180d0080c1840c0704480000d0081d51714404d06520003032104030242c0c410b048815030b4000e10000154083c0080d18501d00b103040400c1c600d0b4070380c01030075401e02040e134460981d01060745900c9802d00700d0540003003000c40c14802103114a42c403444118108154040c141 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 367250080 1250 367248830 367248839
    0x602090f030a0b0403030f06030816050d020a021320030f0402012c01032703020303060301110405010c0303020304080f0301060e01021204080c0909010e1c0f0e010504140d080c010b0109 81
    0x820300401c000d410490f4084960385030364044004000b008840e01c846591400048007141c02074016180d14440485280102031050030014030b80341100c09201c0845d80290842c1c4010303200c0c0089140ca4448482d00480c0c0d90100b248260031000070740d042040760a80100400846981d0301440078040c6000b07803280301580c803010540d0f41000c0704075032271400d1020b0300c40421600d07940300c4d60080010325413204d0380902c50420b0b0103041c910100401c505800581c408424001185400e1044800103010b001c113a074a42458100040c0c41d80051704c02c00360a0650101c001803e10050340110b1f855a107441a105a0340c0d0386401d80a007a054442210b9801032040803054401070407080301320f13003e9644003c024807044401c0b03001c20100e807000900064041d500c550340c20111942c200111980c004041010650b4040c201e01c008246009210104003000021007212a0598000044505a40301140b9141d8140511004206100c1020b031005010b00d03800500540b181d907040d4010720b0501ea090760b038039440c3e5075039 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 367251330 1250 367250080 367250083
    0xc0c060b0f0a0b030603120313020102010b0f1f020a0804030b010602060a06420206070807091a0c03071a010603110304080d02030403020a12050304020a080f06150109120602090f03 79
    0x191980650020b640c1c1d1001d11000f219080030710f50000c80281215480d0300c0021662002e90003d4981c0c17034071015078605c1c1800310341c2c0a00460350400010f5031042d000492800c0080c04000d804600b159a00015440d00d902441c824041e01703200981007204079507a280e580c41d0582028209119010050290f007011507891601402070034122080381c05002d4141e00415404890070311882a002c1040d8502804a0303540031202e0319402c4131f600c083d000303010303540f0300081c4c054800039004100004214020000344a001201b800d09451101440842d5840c0c1d410103141c1482c0d4483c1c40c00103040c0c6d816407141c643c80c0c10780411442d81641c90b02d076401e20450303450340388040c01c0b8042a1801030480c2d2041c402c08802000c81da0203150300c140288100c03030003d219625103030b400350070f515100f42c0001d500004100950828050381d00081c020300c0c1c01041c0190b00000b5084c0c40d148007800e41c0c0f8906524008640d010b030700c20f00c0c09802420b100c0ba9940d56441161801c4002940a02d1046000310040062003500d40380 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 367252580 1250 367251330 367251349
    0x270f0604150228030603061b030615020d0807050f120709120314030a0204120f110d0f020f040f0f0608120909130510050702030703020106170304060315090c0c060b 72
    0x80080c00d00107180207900c414051503000c411820805a440c41c000000c60498001c86606e82c1556a8480c0d0b0008d401000509139501074101c0f13029801c40f800d0812a6960024940b80ea6a505251041c1c440d1503400c42103840b0700c1a00c802440081003c0b41251b408000480064056800ca840714244940c0e03031080c41e000b12250003070103808150349828509074560729400442d448044a0303001032034240c403002c482281060600f0140c1d2620f45440c25041084480010307020170b00300450745041c03d82804c3e42c0d008810111180000e0141200c48031110316a10f03140c000c40b8071100910018003032042c1641005008240c28450b580f518441c402102a028502104940e0800d202811041d50356541002440e1160b240d5881103485114140030340ba00f1041e1441080d01a1041c0c0e80619502c260508001b800d40d2019080302e00c0c240051034401c5038403e00001102c04071091414085602c2070840314019a103401540400c089034103013040750700382540c8a0034401156109480c20890032484100388001d584 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 367253830 1250 367252580 367252597
    0x80a0c150e0f120f1605011e0b010c17070510061d01050d030905011112040b030106110601150e03010213030311060703020310030f05010e10060906080c09270f06041502 74
    0x901c10000000304004d014024541910040c08449101d03400d03a981c20f0842c4c0380250400c6051030703e00702c0314525060318003c803003521009281c140a00700c60703610340751400707400782944d008480d400141d484d04006052042d02d0041c01c080c4810000159540c01c10707800d0210303600041a02c0d500003000800d00e071074080c441e4450381d90140d580141a03030800c0019101510540ca640340a44507552211280c444034400910181c500100065269450824003600c01c9034010317415001e503000800103001c29421206400d00242c1c0d80d01d042c80000100c540401d00910500d0101c0700603a544060200505030042041c1c402410a64205c0e000c0d81d690220440c04c900095a00c61242200d0301c43c100045800903101e10408c0b4042c40000620040c50500d140c40c2103007101036480c8640d00c54500f0415040103100e90802010040003419a0a1610b40040d05d0140c00034140c10b01d0100c2e8020550821000c01441c407020003142080b01d00e0b0189102c04241d60703a00c115000c80703020b0060031141c1c2c2c0c1c0281900075103840c3c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 367255080 1250 367253830 367253863
    0xc070e15040e07080a030f090503011808090607050a11120a0309030f03090905100807060e0616080c0601030f061a030a0215090406060302070b010801050c07080a0c150e0f 75
    0x4080007000042d15900b1140c940034803c09a01040725501442210031062090b120002d500f0050b21300074000340350720f40c4698030a914050382803456448124030002c2040e48192030350760b80e04003600020124003400b8809001441400f140d03a0811400c02d4008101c01021154405542c40042c44540e0790141c005000b00007944034602000003920030b0481211151280c1402c400741074981030302e0011908121060030b4901e90b61070302000505014030031580500641c4c54040d204d54060743c0807070f90510070b603155548015003550048051103000380969940d004c03240305980440d40d583c180403580465030f5400381d80d001d00e031007800e01c00c1c0c0d031400c18111541e100c00380c00b5194099881d02009581c140d1955004081d1404210f105031a80d503c1c450903010b4115a100140c803990305041c03080140ba0140c0105080e6850032050081e01c41224040d649001d501a501607960404000c00721000b1540c4070b0001c200758581c0349001c9400c58160403150309031001c8400c0740d90708101c1c0102242e03a142c81640800c6038 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 367256330 1250 367255080 367255111
    0x409020f03191b0e1512100e09070b0d0e032b02090f01081509070c032c1207030204140a0b0a0e16020703120207290d0b0f0d080c070e 59
    0x20f107070084080520074840144032200c01080309401c100c2d80d5120241c14541009298100600c0d088120764600c0a40a011020b54451819882140c0e030348240b0700a0b410002d0020901e00c0d240034443d00451008000d23807064030b48860107a110001d15140e100b00f05a0200c068407040c00a01125200303407030b0302001c01480010302d80403030070040d682c00d20050f10310160614400b0901005481324242a0300030346090390b0b0070b02c003140d081c00e0090140e14030b0091845850b861642031020341226001400c02090304480042c0c444810285d507074039010703d561000350418240071480007040c6104a006100708a0801b081c003c40d0000c7d41040502d0909001320700303102a0420102c0c03c00f4600c280504e403505064011900705907200e031074010508182c010001c00584c02108140803011045050141c90010b0b4180340c400b603220803d460043e13008038081c80c1411561450524510354682043d1691400301074941310080c43c180c20500040c0c1e00c200c580800a2181c02e200046460680b4480e85c4100c820841c0500e2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 367257580 1250 367256330 367256381
    0x62403070309030507020a030b09010b04090b1501093605070801060318152408030304021318030f08070e010e131103090a0203011406030d03050c0409020f0319 70
    0xc1c0300d050b0341601081010301c808401621901c855401460050040da03d440c500200d04d035017500c4d142c443c2c283c011400c06c1c0c1d546000400c004a4160026000c028526040e00c24000491b40107401d40d000c0e40c01c06039000c5032003403210110101c40060b4100c5049510314940c50300d088405844041c0e41e0400003c3c414401003200d10710a034042d4480c100101070030250241381d82c441d041800700864012000c2d91740c6100c0b8088032040480070040f40480d260340c6011161410819036240d000040c0041c2c0070f030071030041c00342e60700e03616600000c241c0c245190850103080c0d85081c014110442c4660050101e0000400f1030340c1d950080060384002003050790b580f1140d0841c0c0341440150b04c01101c400c0307851510b44140e9040310b03085002031071103150b27514020164250540101425600e078801c01c441000c40c080244180f07a100070070001c0b12403406041c00300341034030f030603410059602c03466000c003080714408101010314100120055000315600c111500c4100340c040c4c402c40885103565134104004042680049 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 367258830 1250 367257580 367257587
    0x30917030d05061c05061e09060f09210c06010905012d4e060c020c130e01050c03060105040608040303060e1e070c050c040e0c120606240307 62
    0xe030b1100c0e020b001d102861040404e5040407105100703048400f030300505c04110000000412040304030008800c1c0c4045810211180c94507600083d200f103004080c0030000601d608402c001c200780da42803002d00c0a50038094141c0b400b03400e030420080c0703402d070f4003881d800010075480c14011203058a0308844240384200c9003030100b10b000c811010051400303584c03844c000903041000801410450b4061000c2c0800b2070709296010400070110401200c0b081045000000c401c030b41d11804681c0c03554055000508600300d8035060b03181000c030301e50141e070181140c40b004911400581002c200c204d02d031402404507440303002d500aa640801c40d1541e00060040c003003005014410724146130024003c2c100040c0c01a00c07120f070850340000c1111004a61406481c4009000c0c411005455000805103040103240d521980d409488214445040c0d226a031100000242902e091250001d4079034003c00c1e414240340610440c54a0780411111181700d80d817030200c14142d4026141b45800505100501240707180c5c1d81c4c89055 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 367260080 1250 367258830 367258841
    0x120609090d0e040e030d0b0310150509060f0d05010e0c0d0f080f0408030c070f06260910020c060a06080d02060a0507031e0605040b0f0a030f060e150103030917030d 72
    0x200d40c001d4581103451281c1e2014001864a00b82c1d9206c04501c003072854042c50b251214180c90360220515000c2042524000c42c1441c109941d070480f007010064941000044040300c0040d001a40141012a0001044415401442004603030000c5d02d00001c40c10080010889070001c014101c4040b508001000502000041c8051480442190308141d116110380f0703e036400039283d2003940d41c042d4030180300c040300d0182e100380100442d1a0001c0c0d03807241000200310203914003c1100f403404084011841c00031081c0604810085111800c40d2540009861540d403518142c0300c84100b549055004200603101040402139000c864009010588800002c2401003000802810825561711484801da03240d00134203075480d9242040120f03065041c401044200e540031001c1c240309242044032640c03245c5503448803108481e08449890001007040c140200074043c0c04143c031400b400f42c11554000b5a410103c0c95050303e0281d030720b00700c01030f4a82e40407801c0403011110681469005026060702c040040e08103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 367261330 1250 367260080 367260107
    0xa121a150702370e1902040b07032109080403060606051612172403010b01020a17070b040c060807020109020f040b010c0b0a060e0a2a09051005120609090d 68
    0x1403000e5481d5404140c43c040015040440045011000d220080e03501c0c06401040e0414400114540752916641c201240f1940000505120b9150f141d1491098400b9018803215622402440003031a1860078107440d511070702040304e40343d14002e808030fa180d21440c140c94180c14130719411070840180c1d440d9100303440901009602000b051070f5251001c0e140180c140750140d82055500016286003482440289210701c5105000c2da00d0076100c1440c40e80d0001d1a5140d040c1c200b00c101800c1d201da001184100e01c640c25014003084821020700040051984043c0200c4440b540c401f02c0750303141e002c0c007203083e00d001100c041d5011034460030000991505601c45d411030380050600c10b60721a41541e0340c004400003180d0b4941038650f80d04080042d03404020049602a000c0d21003040307403007541710a0b00031011364014100140c4001c0c2100d420300c80e010b080410050a001445c0d41031048101d08014010340c01461030950919040c40441c40c103040c188841c40c041d13030141c0302811000580f52000c480c00000c50340c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 367262580 1250 367261330 367261399
    0x903140c070308190e0102012717030921030c030a0b040e0609070602011d03040b0313050304080d03060e06030d051e070c03020a081f020a121a150702 66
    0x400100080f5924014840c01d2414071640707001a07020440980680105280c250540e41003110603005000c0d80865008482d00e40c1101001d906030314103040740c560140707800803a00504000140222a6800142039035101d0303c40b80f10420149082041403020300003514131b428070280a2000c10f501c10a45d400c01400c070440640002004403800c01441c1c074100003030719841c15941264105100890707080c01101c56040c081026462003620145201da41e0344124421400c41030004408203204640103075410380596040390880c0d84a545440b00662900c460369030880101e0b01c1c1c81000075074003c514002c41c0c411000200605030780280500107607459442034018403003085103501c9030301682214034007400040340070b80c058800e41411441480200f440d56004804194041100500c0034901c20031030310b03034015101e080542c54901c05001629501a000380d200e4629003000798402580140c0712424528610840346c0c131a450b05920010015403060b524007a400c0f0703081d00c1401d03408000200d0781044406502d00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 367263830 1250 367262580 367262593
    0x61d04021605100e011b0c1202011103010602030a03063203070b04080604050c03031c0902150304030503150a0f0902031308030c0301080c040605010e0d0201020109050f07180903140c 80
    0xe5400d0b0500043c403401902c0e40b5500c201c410520542481040e20204420b0306010214039001d00141ca038400e000e10040c1301d07094203962100218802e4010610044a547e1410784a585941000e5280d411078028500000c3c541400000d544e190500e0b24000d50102541d01c004c4045100003481507401d078280140d07094410703001d001800e110038100030001062200c0c0580000d0801d8a003085c1070424a07013615210f940240280541540c5180101009010100000801403010300c080340525030418920b074442c00c17000c41000141508800194400c21100b00300c041da0346504010058201d20342d00aa0312240c00c8100d00b40481c000c20f900a40d04500701c03115000c003200040c0e503001c035283e00483d194810090003000410040d54100481054000708950a01001c1c1c200000240310400402400e482502c0d15486802564000c1d400032081c150040306540168140070562681c81800c0d1140b1000224400817520f0310342220700c10b0f0507450b685503480f807203045a1580c82d0308072078000d08014a020b0140b207 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 367265080 1250 367263830 367263833
    0x6010f12050a1e15080703020f0d030e040906020a08060306010f060f0507020d030201150b16121205090607020d0309110103090c0b03100303080c19050a051204050c0307061d040216 79
    0x80c80d440200007880f034000f203112428860141d00c4603200394001e100700d0b030201c2030900061750391440c00240031303400342e5034124203407103904044496541910b0201d4110307180264000501600d50002e221210298451808903240c5500b8147e40d0354091140e00c80c00c030620b84007444014425035002c07102501d10302d041814580d0580004801040302ea42c12400b5031342d102c681d104030401e0342d201c210007407001c040300604002d030003002040a02c1c00c50600134110b054444025000c140074100a10b0543c550a504105a10f0082ca4540d0b4904096550340050700c101880d10040a00ca402010510b651280c83c1050301c04800d80190060241c0d2001245d240b440a2000318103540190b016512460400a12002c0c081c03440c2400340050030040d20070580c1c12400c028644a08a107030341810304612139443c1c015175551007014101d80500551201383e24001c6000309100034030100180040f2900300072020b40702400d0344d03110140d42e05162a0101888550503410805080c9050350242c0450107a6101d00c91292086 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 367266187 1107 367265080 367265111
    0xc04080d030b04110c010e011d03040504050411030307050c090c070b040f0c05190806060a06090b0702061201060c0c0605090f04110702060304120806010f12050a 71
    0x2034200d40b42c01600d032644900c0071021080c40203a00e4401c28241c5501038040040440020b40c02d1030441c0100c40320000c422a40002e0600c021340c0f4083c50081440060b2a0040003510f460a02c850107854070f8a00344028641d4a2043c409409120001e00402051403005020303141009001d1003a400001c03900c148298126800c0b41c01300764140c0c0c81d458441c105800799003100b80c21014801032002902c030f00d18040300544940100f0740304143e59010500401c1076040c0708001c0020383c644800c020785046c2c44028179016001820603441c210744002c9141c17440400b80c0c46800010f0b0502c0c85201804202561803001e040e82c0e10702140703040b9080001402c500490109180702c0c960300c1e001c401c40d28100b001100c6d03c955000e80402d442c6c0c5854117000220351940b20480c1c000c103a0400000c1c06035803250b0400400e039900f40d100d0500d02c0f640035002400070000100f141401a544206400700300c50b9 = true := by decide +kernel

theorem cover : BRFrame.Cov 367086330 367266187 := by
  have h0 := BRFrame.cov_init 367086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 367086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 367086330 ≤ n) (h2 : n < 367266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
