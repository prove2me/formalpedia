-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0476
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:00:21.923978+00:00
-- url     : https://prove2.me/submissions/20e1eb5a-44db-4492-8421-51b362b81490

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 85431655 ≤ n < 85611511 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 85432905 1250 85431655 85431667
    0x302070f02030109031d0a0b030c09010203040803030103051b041802010302130503060c0a030608060709060c02040905060414061806040618150204152c0103181113050705041a 77
    0xb2900312152510705400007801d84036482c480302242d921410741e201d411140303030544904001000c0031030700c8007400807108154000f541507400c0c0d0003401030310020900784003aa5202c0d80c0d80d040030703510f41031364412506100480c101c00190500d454860051520614030240c07064140980c0194000e40c4001c40003280c07103010312400220303643c04002d1248614040444591540c04178a03025040d40c2194021500c19040181001452580122b038802268204c0c40c4c104514441800454001c2c50f0610000e0480d014050410003400784500110102c0c15002e000c48602c0c1d502c403580680e444600c040d0300a01e1381c00150120300803484d240c2110340900d84011070718075030524950740c142d00c0b03900c10910104400d030045002c110364a604040b507480e036141410101c494030b6a81c03030a00c01c803180e0f503a181d540491087c45013800592080d401401c03c0038220f41031100c004c401d0b08140b1819010b2420b10351180403890140c040c2120103000d0507000d43c030103031a440c0c103050a0480c7c2c82c00b14219410350580301d54040c410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 85434155 1250 85432905 85432909
    0xc090b120a0f0905250509040803100e0c0a020f19030c05010204050901030506090709050c0403020118080102030a0209090a091a18010218040c082a0c0f010204062d0302070f02 77
    0x4141c003640c4503800a00c0c1c403128443e171116a0107003a52802d88915402507081203240c130b48902003a40203900940b0035560395115601c0c1841001c81d608002e540390015010000000360050080200c5e0300590202c409948441c900155a050141c581c80504942981c0c603100180c06017100704005407050001605040d00c4c1e101103a070401c0c2c00d07802034036150300c0b03007082c00060382040c0000c0707016112100d0300f8011403800d612450500d00c40c62000078104030700c2000461140c032007070150201500f041d000940d920300b0000d841001942000e40b40910890243e80843d5082080d88101c0620951001401d0811204820a40c0900340000c1c480261201c1c2c1c1e81c140090404207200620301c080600704030501d0005d00106000c203e54a940390542031005007024450b0844810f10305040b00c01465085103141c4000e281c042d0140c0c09541180d12540c0701c0c2041300300c5045410b4001e007098652564810140101014600c04e520000e4845040002c294142141c0300b0b07480b80c0c0040c10464000c182411140030380d640 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 85435405 1250 85434155 85434161
    0xd0f0c060e0f01060e09060c03060d060b030105010f0504061e05010c170f0d050702191101020a0215031806130206030c0405060c06010f06050a050301050d0c03150204090c090b120a0f 80
    0x15003800381c0d43d02c04c42448020704000c0b030250892960402130100b8174142c8007141d964400504024420701d4462003c1d010003009801560b581200540203010a5a4800e080e180d0031529006141c440c9041c14000b15610b0590070090032800340704103c1c407004c2c1c2d1a01300103440d2020641d50603039401c0800c00443c015801400001c0441c041c01509059440d400f68218000f01c4801601348411500000d12030a09041c0b003491808610380c01994900b489514480180d1a003c0e80c03d0001350003456540c09000d01c00143d401552041c84002c0c50800401103980a140d2122400c6500b02c100c0c40a6041c0d807400340c10500c01071a07010401a001c2454207866a00044c070365005814421050f81c400300050210380c41d4050520002c0000c0c0c2411030a190700d0440180660005000300c5004152a049500500200502c100015034100b035040000d0f24529400d003000e9400b9000d540700140c18071071482c0000d0b2013190b01908450a864982e4105410501c00c01d003008409460344000e0703504c032003180c1300d0360030644 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 85436655 1250 85435405 85435423
    0x40c030c020604110d1a06030106050d03020303180c1002031903110a050304110402071514060a030213060e1305010509030405060d05090703150f0f06030c051003020c07060905030f0d0f0c060e 84
    0x800c82440b910b41f4038205401c0d503440d600154040e11001101c1800030b03800000740d030f0704000b1070f4030760515000480100d5498041607280d42c0e0b90203465001415000ca0300880100540864620103e0307c680c80c068054080d120714001015841400f0400f207034126200c1e401668100c1d10034810b0340b10f868034400000d816a0002042901d10a4a54020400c0c0040e64414030b801011410900746161408000042100e0305510000c0d00421003280e004c01e00c4104ca03403010001e03109000c01000582400700309990045921780e0308450540c84c0c0750118403080c50000035141200e000800161810481c03a03283d0700035050280c80815184580c1f0b02c0480010b00407611110710540c0c0203000603c02a4812485058036001c0d40300000e0a0300e0100f051020850481d00c22041d1071099904812200880e8030480080c402c0d108004141c1c0031320940818100d51120b800000c8403421401c80d80301c0316034000c005071280070480c0d0a5000c55040d044011010f03003d40502040240903d00001d55208a41c03407103801d220b281c1c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 85437905 1250 85436655 85436693
    0x7111203091c0203030a020d020702040603030e0a060318080c1507030e15040807030e0114070c0f09020a02250504020c06010806090f0601060503040c03060c030902040c030c020604110d 81
    0x100401501101c10021005211804004840000094000651a844050700618005800181c00d102000d11ba40480e60340c036a010348100f24040d90f0342801810740035000c004a11840030b0700000546540329002e4503101c1e41c008180140b65500682d00c525140d402a00807070b442d4060103a05504076420942e0b418840c0c901620701241001c0d002402604200c05005e441320404c02400c06c0c04081205542500e001c02c1e81070030a02d440000100050b0340152510089024840e00010040200b10307041080c01c04840d500c0303803c80d03802901d44190000340d00a000e929401a03029002451303041ca1108100d4075280d038220000d00190b0348070004a0181c0e800900302c14050340c842c2d001046180010000c856001110300c01802c00615802c07280d03500c0d190103209000802c003001c80800c0034055440900030041d0341c441c808102c1140d00c4500038000e03205040050348200c1c07a00c6503009005000340140049030040da405090280d595540b00e407100c40d007020519411040d18007280d0300090340001032074038032040303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 85439155 1250 85437905 85437907
    0xb0d030c060b03010c02060408030411030318030105010501050319050a060911030103050c09040503180a0902120417190507050a05030310080708010204030804090b010309050d0f080a060b04030803071112 89
    0x3560a10714161429010014042ea143c03000240640783c0c00308100e6003040d440056180c1e40d40311800c001d01a903034021a11507250100117103008215111104c2d84c2001c1070150001d1101c1c5e80e81390b0055980e03001c00c8545904a50645a03c0070104d6400d900803980030401e958005011a110f803040011204002904400365100200510902c00704110b040c030501c2044602c0e04040c0751030703a1900e440b40907845524030451138844030034285030364201148002e003884800454407802102500c00109000351402c1c2d4000328034481100c03a030b0402408a03504113420342c80e00d05a018600c14111140d0740500310584090142010800000d1400d200035070003100040b020100b0b29041c007080d58141300300b030f23070000045078410802000040c0d02070080e20111211070400058803217549005030040e1901140060560284003400e01407690080b0800d66595002c1d69841d8959a492401c242280c490b1f0081c059070110500081000581d40002035500c88400d1030f01620001000c801c0c5890003603e05107000c56030300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 85440405 1250 85439155 85439177
    0x1051c061e0e0705090705070b07030b0306040f03030c0305070203090111011d0309010912020f121e0105160309020604141306080703030f020a1119170c0102010b0d0b0f06040b0d03 79
    0x200400c43c03400036110407540c3d00c4007801c1010028109110705035004162040c00000030b4080760087e8001c07000b400010f410303100c8502c0c02d45016460740da2044021008285080498006030f8881d104d0f9910400b559001540740490801c0190741680e8034001000f810764a0b402d05070070a50042c44102485201d6000960f01c1d00407020000d0304003032082c3c112421240d0180c0d081005681c4581c203540358180165081c9a00541c00001d160506124051064120402040e003600005055100a00c10581110113610b0100104070803025500d10340000b80d407040c02030006005110780840e0401c1410300c003c1c26039200310030003e024001e458460b44a10220380099608000341904507890041e4202c0030703c09402d49010560b240f24422030100d0035540a03110b00c1102c500c0e44101040c80f00d01428500c51489401814034007925650b21150f0000b0b03005501f0422006054100115240d1036a40d000524444e60b0741c80b9502100c00510003000c50350322980b00d2005826035100e01c09c40c245494007955600380b0441e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 85441655 1250 85440405 85440431
    0x822020112200a090510050904090f021207060e12151312020304150903052d0102040807050a08010903020619060312050306040b06040602070603020c03070b1e0109020301051c061e 79
    0x201658401703805014801d030350010341603011003154690001224005510700079424866100c0c2e104050083d00000f0b01c8104250074a400200c42d82100d50030b5640d4241800a00140000415654100d402c90b910a01316190f031810400f9036107038414801e00800e04030303071000d80380c20301013090340040d91000d40c100060602100141880160381c800c1030341001c0c1d2149140d0796800b580d0b420700204000004162121840d01d4001e40c01c089041444404025234a454940350700c0c2c0c0c0c44461600c5082c5c82407000400000c1c0c2010f045c065400100c0c2c154002d0301c136543c5c074110a800e40303607003c3e10319080c9140d0340e500201c0001d20b8403401e01c001c0300941d5074660300c0b840c1c50418003007181c4440318182d00c81d000c240020860282e0000d803407400d40c3c1e940c3c40c02680720314a65041d94a1801032010003042c030b040500800c640f00c118215000301e98000441480315599881a040c0101c0c84280036071900242c0742c180e000c2800c81d0000c200a00507120381030008001555440400c1885a074400005c003050f240e0749615408 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 85442905 1250 85441655 85441667
    0xc030f010e0c0d0b0d0818010822030807090b04060305090105090114010b0a09031e0b0f06030c06030601050c1005090c030613030804080c0109120822020112200a 71
    0x5041d8030300c504129801c014039507280601071041e4505100d80c60300c00c88442c0d91500025009119072145c2911303200d8030350402e903018010007080340500160340d920018945111410b450720000f9600102c03d105020035840c101c8606c031006107a0360078042c40750400103400803008000c0000300207035030380010780d810301440003804d4a0010700210010381c1801c520744140c41e54940b946046a14413100303d660b41c0110bc1c410f0f1000c0e00550b00c040c105580a503000442042282c9250f030000b03100380c03000040d550b144154000d010009480844d0503071300680c4000f0070390821400075508814141002070030f00307448600c030610b0100c0d41d14410640315120014410411001c204000400900f100941001c0c034106109038000b0311010800340400400d40041001c0c0b0158600300c6502442d540300a22840d51103040c0311104000085450001688180006025442010f11039494207100c104a000c001001e4004450148080030f400004170341e118281008400001c451140200c042c100b00c98131079400c56409828 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 85444155 1250 85442905 85442909
    0x2041515050a080f041205090406030f06020c160308191707110c04140c0307030204080a030c0309050f0f0d05070909050705090901020405030a0f0f06050106120b03030c031b0a0b0c030f01 82
    0x10000c444020305c000900b800070702c000780a01c140b8002c0e4031403e001000401400c181d42c006852400003080160a010041e0010702c03490302c051301141e04a200102c0c001b00c05c0c60340c2d0300c8007a0103041700341325200107420509001420180c42c3e10b001000301c80c2c202541c5415190540380345011814052020060b044240410700e0981ca08a40801c040d0140034071000c44184014001003913103400200103a8840d0007a415a8007410916040f14040c154030b00e4050a04d003441708054000c10501100016540303046100c5c0620320a000e0125038044401105000c1c11181c804004c441e240030310303d008625044c06110300049a0b000348000c20b1424940024008007202c043e141c0356640c0d004000c241b110b602c00080c403411b0795074096119170b101100d5040101d440c0043c0302008114500700340002401c254454407095004521041c04c20100844031b041694920821504020a8005100c210f0729400304903a2100310450078400c4d10800c41d50741d0750f414001c03030b021581810440008000e100744a0010204140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 85445405 1250 85444155 85444171
    0x406050a0c09030303110706060312080c0a120c211d0703050706050d090602040e04110103060f090b0d080c0303100e0105060702130b090a02210c0702041515050a08 72
    0x7041c9480054010448801c5010150034103031600d14a082c8520014103e40c102900710301c0c20003400d600d9180803c1e01d180d143c007015001810f6103000c2003010041000b1107040300d02e00d899940c144051040c0304000b80070040c0c000d00520104980c5051000c0d40482e03c20302d8503100c214002800740c44140c201c41c3d64110019109005d61246d80c050000800000e018400e40c0d41d0713810081e45070440f103c2080080e04580790300506840c00410005407845040c180d0700d009a104482c1c0c03010110003a80110210745603841512100541e1044c00c0010008a0f4020640306202802c40c409044564490402d2903022440c040a560700000c20040890040842200070308010103000d4155490800055013500030303240d000c3c0c0310355481c1c0800304423100254824605040058211410f074604000c03654020f4200d81c250180d440014807004c0070007483c1c20034403072054281018140c106034182c0c080c4401030021106042128110000119407c0820750031904401c040e0340d50f0356500c400c0540014a40e0307030090700c460 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 85446655 1250 85445405 85445411
    0x60a1a030606090c160b040b0c0304050c01050306010306030b0903070b010b0a0518011116050102011112150a120803010f0e0112020d0c05060705030c16260c15030406050a 75
    0x1455603004120307140c20031801c40d66441d561321041c0010400e4400d40d240100c03c4a51640c014040000101c211403149000d200c0241e00d640e0396910416882c403003103c00400d903400450b2418940d6014002850308050180341c0000c060361aa85c0e0340345e90902c1666440c4080e44082030b07000802000000642c054948000010b08005940801802c18014101b40e0b40381e00007000d60504903640b04881c0b2450042100c03040781c03254034244085507800072250040c40d005500b0540040d282c2d07218901250351b0042000400181c41c1c3d149a10701c000220891032441d4441072402c400941e845031000c2d524450341c05001325070750b0b82d4980602c4c0c070390b440130507404401004614001000100602a03207481e40c0c94065078196054949441c00c1d0030f1000107508915440400400c55101340200000540294134078102200c17985541210f8041c2c50507020f01c141c00d49944850503003a02c0f07060701104005021410f804a0360000c4680700022281c000300c0d14401d0044402104000030b211003070103500d1300700d00504410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 85447905 1250 85446655 85446701
    0xb03060a0e030a0507020d0b0109020a11061302090405120408160801060509040204020304020a23011d0609011d150a030b150313030c05030d0501050a0605040e01230a08060a 76
    0x710b5102d0081407142402d1040200b417505c20754540c948a489081c0c2c0c089a041c1c12507031159188030003500100500000540748403448481ca4400107040c86c0a0220b00c40b00d202400c501307a0070041150f030003c10480e900c0c003410b000c00b00d248100e04094000f40c40c00d04042c104405a1050501440b160341d07000ba80b250381002c4003081240c540d502c035180c1184e0180c9000da82d07585c60380045406c400880d8041100100000c9c503034000c60404480780d940820302680e41c800704420001d203d00c1080c03012000d0b01d6014104100d00f240640c010003c03007000007009040341049104040005440b94802c0040039200c13240007800b000d1123a4948200890650222070746d00324024031800b00700180c0001013034100443e881d00303d00c030f0030705008082174805030b070307003c0107c039540c401100070400034040078480c080c0201c0c000c05000c0341c100e005d082590709403040c0380c01c5110305d82e00e0420b0541d61545640e8600d4240c0441d00310f0605140c41d482c500700d02030b0074040010105401d14083e608221003c500054406101550807 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 85449155 1250 85447905 85447931
    0xf07030b0f09011b05091306050a090507110a3008010b0f0909010f05030105090307030507020402071e0b150402090109050f06121608220308040302030f0c010b03060a 73
    0x4a030003400403141064541d860010060042050000c01003110007813400c80e80304d09903c000281082e8405072014519441c0f040441d105581c00ca00815a101c3c44090050201d84000d500160380580b02e0b203045203800c2e000280e010b0604142000540d01d141c4045403480801c6040c640c81c41240d0500145407802c0c070000400182140340600032801243d600151640c0c5c3c5001c1441a140031860003442c070a01c1c0d50f5201243d01040c6040d1040c14025401d120020b0b020000200941d0a03144c0c0544030545052059802c11000f90711009003140e8800504a200c00300c00c040b1040300d104144140070b22031660400c5000d00407002054400311703200390b00400246039a42d0340f00c00c65104613081902c2c214030152500c030000381d5034003c41c902024105644070400c5012039001c5000f544410311911185899104c642c00c091420101d000360400f00360001c01d050380081d104248140c2d000d0300910590f82014040c0c09000220741c800350704508643e455100c0110140f03002d00c02d00e9086074042000b040f8031005801 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 85450405 1250 85449155 85449173
    0x101202010c1b08010614040209010237060b01030b0a0510030504050111070312050606090a1211060a09051f1e0e0d0303060806071103041404021201030f050f0703 71
    0x402410400000c0e40d4504112941c80c100c140114001d4103004055100c0e01c190380244654450404c004680c0c0ca4200c1303e5082500c215034078560180d01601104000e1342d540c50100c0302100382d4555801b280c50200d01c0700012845082890b9114800219020b1490b40c001411340d105e025480740b0803444001e00b00800d5690001d10100c0e1034036802c010410366607605001d4010020040420340d000000100a000c041d440038415030b134052142c80800442d100c0b0401d101e000d0264000b21900641e1061040c01406500e294002820b0310038443e140d8000f441201080381c9405c03800c3c202010a14041040c080c070b14208000d10354084040403c40f2090740700d01c00051150028109a4100041404090701840d100300b03903051403014007508c81e4041d00d0441c60000e0080c442e40c49031252501508021a0400d44149114070150070b03200029070509050108038100914800b051f80e604c03c0d4200811120034010000c040e00a5020f0a0902d032400420b04045041611a11252826070031040f003e00000c1c000741 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 85451655 1250 85450405 85450439
    0x90105010f060e011b05060603060c0a0206010902090d0c06110d0507050d0e0d0b0c0a030c05031009020a090e0f0a0b180a051503011401080c100203030c070201030209090112020910 79
    0x8504840302241c50f200503a01001c80c0c21260701e913815003035a200140100012024014201901216000d68031340c0d0900c046802545a5100140c0002e40100b014a080c3c2e0040c0800100040c140e84491202d5070320400014070741e0303010b980814644030101c1e500150500810f86400b0450900703e21b8401e5994450303456000c444400780a0000c0745804132080d031600301c4c3c0300d1501940001180e40382e0510b000300340201d402808035400000d0821401401c0d4900c140c098038000c0345000e0206201c0380c20301903414060f4008040103020003821030400986008544121400769040100c414a2400c0081c186819a0714a2510701d00a24070b118151000500d00e00200d5480f55120500246035200c01d50b05201d85556016640e61560030305416050b40503941d02503c4c12034640c4000c035409218180280018105207511060150308240001004440e040c0d0041a00a105150040c0b90410340301c00100e01d24020b800500341c407280c124210b011030070112203080e081800034458480082ca894020141c02d5044 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 85452905 1250 85451655 85451657
    0xc09050a0302150f12040b060a031203050403021603030504031506060801140105040b18090105100c03031a15071e020d061806180c0902120c0f070605040803040308090105010f06 78
    0x10005460b8021010780c0c0b10301e09816459650317001d48503850160704006540c1690841c64200120300b01d131901405010840742e1044844100c007180c0a02a001410001c00a906600074102104100b80110030b1000103180b180d2202621241141051050b2456000c1001c0c0c00c43d02c0c03c5010302509402c141e089045500c5601c1c2c080950856400490310703401241d10101c081e00d800700380071159001c040d01c013140501c1e003940c0c0d016090382d0b034804100015060651700f002040b291140751005c00d1007034000c402101c24001c0301c034122420740c2000c503040452002620460000105582e004c001c051001c9201c900e484084018210b5041c2d00054040d4034070a000800e120355401200504607000300c0d24084440d0800c4007045030842c44074407080c91a40701102102c15405006000c110801903100b41e40c1c015510070034401480c0e684001c004110341c0400c0d074407001c0100900000c40003030b001e4001c20303120300c0c0304606040c4c403801c0c2454054041240540450b055174180750061100e05400d01c00c8004a03015 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 85454155 1250 85452905 85452919
    0x120e0106062003070203010603060b100e13020c01060305100615020607020c1318050d030c020f060609061201020a1206140102060c03060402071e230604080906210a0c09050a0302 78
    0x9540011460f5120350b01000350194204000041404a1a8048030040d070f81079030400503c010102003101d4101220010950014400c50341410080c00342d40503103032075041c0c9030000600b01d41701d80341d40d031070403414141490742d05445a1003440300320f080900e4018465140c3c0000d140d14248618080c2d1550001400c80d40110100340d00421035803207a80003e841c070003902502048201e1701d400c0c1103071101185103400700840d04224810854910018200111303503035420190140d0340707840040100c1160040c8c207041d03100701d9002d000094024203200601590340961580013140c01880d420800f40c880c1c9900c9440e41440c080c5044503070766004100103511060718004143e90b6510500010028024101701411150520750305000b09000d40361540303446070003071070030034410450740d542a481c00c0703121880c0d131845401640108000071304d0640074004040d4000c080c14100500030805c40180207400210040c41c110150622031070030b2191091710302e2107000d031801c0c000d80c5090001144103190288802402102 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 85455405 1250 85454155 85454207
    0x3340c081e0a240f020d0c0f090e0a320a050601050405030a15060f0314060a09081b150a1506020106080c09040c0f030b0106030b0306010f0519030c06120e010606 71
    0x34a6000b82e0310200b0001045482c1c0d221b000461004201c00e442c40340c041023500185040c0e09000f4003411040742e003603103400b01043e655030813104080d040380903910082136144021600c1100b298645155880b143c84d5000009280201505040e240b02914030b82c1400010042880103403400700e505d0080301e82048117507180c1a00d40d58000000c108a0b130184448208555000c020495400c40159020ba103400440340c0685415079040c086410700030004142000c1004041c910f600d400881c86040c92a010507105036982901c07882d18034000881d820b0b00d0321659082e2020070400306802d2040580402c2c8003c00005040c201f03110b9661100d00c035420f02c41c03141c00c00014108113040e400d40300505416501c03500520b54a103403c2d4200e2400303020b80e10102e41030030b4480c0341c54240011140c0c129400c40389500011854503087c44800412002610f04c00c01420074044042070214407094000c01c080c0d902c0020780f21002d04080304594500b030007112141d0420300d04012055100445e400010211400255221 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 85456655 1250 85455405 85455473
    0x3071d01050910081f060c06050c03070519022a040c0c020f0d170c0610121509080c070b0c010b0a030c1a070b09010f0c0203340c081e0a 60
    0x85c1324619107140d446402000031030059407000c05142c0981c41100c0c1840203441d00000e101d0b85020490f1480b00045080c40a86050380c59118680e002400c1c5006490070417052013407585d415091000c203a01800b5819101100605051040070a80c04e41490100c0e1842c0311580003950000070b0307129403031040030218091014004c036148001c08058001c101e456a07001d88801d001d48442080700d03030798018424034000084c0c400750000387c0050030f039001a071450080340a0480e81c00a10804409452045003446150000c3c0e20802c40714024000d41c8070100c0e112040000c01509507105480315901a4189000c10000111546103240a64070286400c84004012801944840c05105800307800344190781c0a0000c44034065111611803000d8107024800c03603210100982c0e1701d1084141140c5050074004d1507a080c01140500c00024a580b10701001003801107480e09880f01a603078000c0501c5401c401e100d040702d1070601c3d94000071005190060026000d2a44404850b031600307103c001814000001e04107080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 85457905 1250 85456655 85456681
    0x40203070201110c0703050105010e07022505030109060603110109050306010311011e0c0c050909061810020a090e060d08040b0d1b02031b2109030106080303071d0105091008 76
    0x100140b00025214041161300d180e4039078141c80241e03401d52802d400482d03581144003a80e44549d426400400880f100390300348a040021180d4104c1412090700c8011415039030038050300c80000d00070f810100740b682c01c41c10241c6401c00010390a905100c031480701040151404180181125004000c9070006c418190060b110f140010544580c0c0203130a86190034040d400c419000c951750302880c1c15440e80358592044c021540c0f0261f80100c0181c2c840070025005440203030104028403142800e80300d000403420302010591700078120360404035039004e6040c4464011050002c0d40f05404807800f2003240d9260315105a240300b03074080c0c040c00c0c5030005205c81155002d504504141c84000308041001c01103081c0007500c94200103009065002102181c422800000900700b40d0708143c1d048083c82c600a00450340d541d0361003040d5168240d500c68030005036140081c40550301c074072119110501d800000e00001c190041030007004905000040c41031040c00e4880c0502c0503860041e509003cbc81700d486001c0003040c0c0f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 85459155 1250 85457905 85457921
    0x15060c06090803010312030e0109020d06150f080706080a14131103120403060c0908120c070b0a080106171311030a060c030b0406050d0203030d050c0f0301080a031d010806040203070201 81
    0x2d00000400007081150103000682c1c0c00407165001c00400b12440071241c01d03160746903c082d40c051101846580070030701940c0011040c4c5000104030010030382d40d84101403891580c0d444a040c582010104219144e00505030642c0b207035201004005d01c942d481034100c1000d07006882c13012510000c0300c01e001000344050351000300e030b04001d0440c0c500d008042440015070b401800b04039526070030100c9504000340901c9112068410b40300c042d001903912600c4254080e08801011240f5208103a00041c010807400001c001c81070180d907030340e00300351304008018140304025105156034940c0300003002081ca2450300303e240f01c2a8899085420110042c002074035000340044003903c0a0314080d60b01d00a2a0594481d100c148001d50701881815502c00400034400014000603405030005c100050150039a40d20884d0302c841c140340020b0800039041e81c41185078009030400030956011307902d468185070f0401108a40c1c42007115a5031049107400c000200001c601422071406580c01001045040c0e0003900700c444 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 85460405 1250 85459155 85459163
    0xd060b01050f0412150e1b0607020904060501030b0705030424020d050a090b100305150a0207050d05070605010e07050a030b041e0203040209010e0f070c02030c090c0c1015060c0609 79
    0xa200c2c1d8440c544c03038942c009080c5040311811130420038003803114154055a0703484603d21010300120060740d522802c0d80420042110344c05031080103071600595a0000c4240a140944000502d643c1540b5004807403c0c03010340180c0a001d410300c1003000080300c455819203440503980141401300c3e003054198010b0701800c9821714296082008100d1480352039401003102030b00448001d8081c2c0c0390710b99055078015075400040c055030040b0f607034120300342d40079400943c01021901c001031500c685915024113144c03850b118200003540c00074a030028003015000d0103014041e51588101c1e1130a00c060050040c2c400ea0f1050741c01c0c140c4404c4000d11a50f103560110005a80001c80b41780b000c40d080401000035441164100d02c10172001c800460014418038803140700d5044a9102e40194440c40020740c1c40302d504940413071b4548141042c0b41d85039110740411902510a05104580720b4591041c4030b41030008415a941c0407500d803402960704405a019038208448140c2001d902d201281c2c103005c0007074400508054 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 85461655 1250 85460405 85460407
    0x11190201090f15140c1213030602070302070602010c0504051008040516180e0606031e01090501060e0f07030b0102060a091103030f1201120f060b03030702090705130b04050d060b01050f 81
    0xf00c0c000300400054280c42a55110100d81080301402c0245004042c0e40410300d601c40006821002c2004005145141003d2032550f041644ca41c0c0d00000d0345e1041104900513004042e0800505809004241a0010a06100342028200380125000d00c040d44289010032050340c0201e010b000c006d120040c011f460921f20754440789d8407408412600f03800d21650f21412441d144040341c00c0d03040468083e02902c0020003808a481140025807103040782100c10325107555841d280b42e00064000d1040d5002007071010760f602c07900d20302050030081400004140006050500a82860982c0d0100d082548a003424a0000c0e280b0403506011708840071940401d5018440029aa10b01d95a00070180081110a0405c981181e80f5002550300c68400410001c000301d078403c0c0075400140851b008110b21210160460f4201045600081e80b81c2000b5030b1060082000001c60000e001c2e82c0114200143c0060244545403a00e803c0115032242d49070600a0820361b1340e6070003c082a031240085880342c0c10340342005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 85462905 1250 85461655 85461659
    0x20f071b1701090c1a130f0603050a2a031409030301150f02030403080d0906150306110a02030f0a02070312170f07020a0b10050612150111190201090f 66
    0x95842001240641c403505040300030240a06541402414103030755120840c010703442d141903d2400b91201d0101d0b607420b500814495a5264250b040c1c070395004158a2000703184040c03408070301800300c40b0041c2c07002050600380201141c43e00e100503050407818091100703080c407081203404118020802102041c403002864011321003400b00000296042e1000c9061599400072068020745400c258404418090381044c0b000300701181d03010003e403c0318665105e011984018943c2c4480807200c44460290743c126a240040c0248840b41c82644542d0701000c802c54074100d100f03c0040d40d81d000d50750030159541c82c001800c0b03107001d20900242c002540c0c4010f4042c0032100d2403401034070b10103074181a01c1c006084c40001a0b03107200d10b185a980500d210350060413844646171154030000030010305c0d0044804518100043c5501c0d690300500b0802c40c10301c88030700a8240800d141c0c866603c03800c141e904105100e00b40c025101c4020800e200103940c2c203049402180c00a05c010b96051149910076030b446507210f580 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 85464155 1250 85462905 85462943
    0x3090b071218050304051002010c0c0f050726010c030e03090f060c120304050d0c080a05030405010e0f03040e0f01050a170c0301020304060b01080609040309170c0a0f1a03011503020f07 81
    0x508186e402c03c03680880d40991400040742241c2911980d0400544e41c0280c1e000170480300e12050310054014025280055118034140c1028003e20611a03201c0324070102c1e05425007020b10802494040a14081c00b60003807004c00e6503604d000d20051140320340004c03500a80740303580ba1811110449103003010394000d2218002e00700d10b6600203c4042e5042d000e030320220720a0602c1815594481d030380c810140b80c04c2140c5950115083d070002401101c5c1c540d600e11204400b05820062214015101c40085940c0d9050600040440c8409071142403071411810041c022681c950315814140c50031300744007861020b4078504403413504803200f42d443e4165100005100c00d001c0e05422202020f502030700c4201082d1904801e00503c00012100036000a820450078015143d00044000781d1450300012101c034810390f4400500c40e02c98a50040541c00d05416003003002c84440007410380c2d11582c10000904541c5402205035104141e5240d4004060380081c03441101050301003541c905c290000391602e4203880c0a00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 85465405 1250 85464155 85464157
    0x4060f0e041a01091203020604150f05010e060a0b03012402030f040605090915030a060e0a08030a05040b06030703050709020a170901050103030e0607051b01020712050304060f03090b0712180503 85
    0xc140000c0008a02040303501511744003082c1d095042d4000c0c1220b985940350201e00d11540342c0030980b1035440709100b1041800a010b1a40600401d01d0318880609251b800c01c8a0030000d54070041190400740010480c6151341ca440d10050901c3c42c00007a80115000700c22800c41c41000404c04000300301150101c1c4143e8004090980b014080e208030800303880740c1c040c0c0300c807001034410140d600d580030314101c00024899030404222000d0101c115010781340e0030303503800d600c07600115031410500d070780c89040100703200c1c003840119046003055015141080c1151281615003103203010f00d203550b80d00040c54408281c800e40c014440545200100b02403404d050090070f000e40000e220540009141d040c140c031b128602001144e80542d8080000c01c042080c100321b0340700c00d42d000700c115815030041910005898a0701c2c0c04100c0b84502c0b55025540e6241800b00241c002a41e071440d02d020103240c58400400580400386294010003142441c0c4030b101105c078000e501410304070b0005102114448002c00410034000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 85466655 1250 85465405 85465451
    0x3051009030e1e0d15090303020309010b0108010b030c0c030d1814010c050409050604022503171902030a0902120a0c050f180a020705010203040b090d021204060f0e04 73
    0x280d1520a500d80c007404003c02140ca000384460461030100c81034007070b4a04403408039031541c0701d5044140d54054401d105000c440d400b90307041d804039400108000035800c0038070800e1307492142400c010507154103043c8040000d000c000c200d840c08640006080c40a607204000751406000c10030014170048a641c01505104030881e02c3c1240c0b04102007101408502e0306005100405629039030b0750f4146131610803004090b04010305001e80140d8208060740c41d11150507400d8401500c4007181003011082d13460b0003000d04802c21203e5810181751028002e0f110040c1100c24a00d41030040056140d458a6800c4c0000f00f0440000941c00000d5440620340010081002106640510111840c1c0e60369081071024045000485a9214514040000e140d1111301d042e00d40059402030010304041c0e0694580c0d00320307842070f90b051340c20807440c40412100e400d0400481d182c500c103074030203060014030341662740ea50380c0070b280515400c0c00a5131042c40c801038801d01c0c4015209100070700502040c90b4250400c18407040d42 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 85467905 1250 85466655 85466657
    0xd080901060302030a2109150c0201030603020307061707090b070803220b01060e040b03070501030504080708030c070204050105030109020a05090903090301020f090f01020a170f0c060a24140d0503040305100903 92
    0x203205c000038094000d4000d10101e0311307800c2c620034030041108c100700c0307180014981c1207043c9a512000800940c03001c01071040500510389414480c401c3c1d4120500c1c11890040c1080d080003650300d414401c3c9076201007500e815641c81001540c4944a480b5158071103c602618040b1400840c418a01404202c00c00d00c0e0480303600ea102c0c241130b20f0b440d6060101b590134425a0981541c0096000c119551280d4481d0b0781c002e0046030440e0401d5826a0b40780340b19802907c0d145802103012544506514280c415030703004040440007040307480000e030301189014120348102031250a200300042e803074200500890b003103490014001c5680742580340c1780c18903d81203001400e002d40a541300081c0c45500001c2c0496689401010350340543c0c103400c80b51004d95000d4030181c91a4079050200e1400b4103020403020b07000b000c1c0000c3c0400c6080a100c94402e158030440c00c04907012850440402030044588290008070f10700707698080390310380c050501da4550311440e48018403d100d03002c0e0801070600f1650001c0d9480f41700b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 85469155 1250 85467905 85467953
    0x803070816020109110d0c2d0f12020f060c0d03061505070b0a020a020a020409030e130204121502090a030b0417190309030309050706020106091d0d080901060302030a 73
    0x110800c0f4201c40204600074209001c011007605240350800d0005404c520807804682e045881e51010180b144038034601f070b840c00213214441990b1240c5095180e000d4400128428249072034840d243d25205c0000c1d80181c02158422100300e85034682c4021110340103683c10403a400710603a20801001000948a100b0312240032603502ca10851052040300c08464102d0b00d00c400301e858030300e01c800080d4403840f090010762037450b60390b0b00140c9070350040041503400b0b91900c3d4003040241061000d4070040c00c02c0308104c0c0748100400e0044146010b0305400c07060304122044440d00d44161013000920139094055401000c2c0302d000000c01050180c0c10344a10b20401c2c0340700c42502d288903201c0701c40c0141480d41c4445407511170320150700762007903000c00b469030300a16010600e9409901d829041c442c0540050b00141d46884090242d41ca15006040b80c4d00c2180c103001d0400090b03250340d2611861010800300c200290b05000ca01c00003000d4001f503010f15002820380b040343d500c6180c444031484842140f80c2a4140d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 85470405 1250 85469155 85469191
    0x20d0b1507210c030809011b0305011d070f0f02030d0e070510021209090903090925020c06031b0c01020a030605010e0324280e15070210090f08030708 66
    0x701c01140d02d54403401c54a9219040c00f2998090b1084403009001c40003940da10001c0d000380c80f0800310440700004503514001b8a55040c000c1c1c00c1c00c0040d2030076032020090754410a00102661140e1200c2891400d8034002e0400c000d4000103c0c154851031040700566801c01c84509041c03500800ea9008480044880e0031100c040c01c9c605a07144d15000040136150707001448104000e051290030746a01820450a0301c2ca42800040080c0b40c014041d80c62400540e03407200458001813001800302c0c1d40c45483d00040c012000c4e5400044ca107840000e0421000301c1a91003503113501610301e0260340142e900000250b484103080c0000030000e00c40e80c41824000384010b880b0300c2c4541000b003000e010242d0403c9011060b508070003d0707419100d401a02640b8409800706090402038610303a1518840c1003403900c003080446a200d041072074031000c0c449443c1c400e14010140701100340c00088620b40c07008441d101003052001ea0410061052510304c0140180600100304070303100c0d40c0014503034031a040f00d890ba44c810390303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 85471655 1250 85470405 85470443
    0x22a01060e01030308150103060504050f010828080c0118030c110402090315150a03110a0501051201120c0308040b0a08010b0c1e010209040e15090d0c06020d0b1507 72
    0x101c028400503020030741040c0460340f0810701c407101001c40c0b00181004981559200c01050881d030041712a42030300b540b81c0c0c005008408040c003ea10502d221590813186112003405402600507d40500800c860380009500760004d0003901b1407020011801042a111006401e0184c55a0ba030104201ca0302601403068441d00d190070710a850040c40c000d0b00500c40d00c011403081d22001030003d489030514034840300740c6c500303d595580010301c0074612a0074041c03148040c0400b40150007806400ca641400310034081a29042c0d0307012881d80c11507081c011240071210381c0d4100501040c0039500060b025110001d40846e00320000030043c8040d40035030303480340c240c1d0307a841c18220098000c42442100759080b04045120040c80c01120400000311180014a86581400010704030b8a40c000c0e280702d941c111007880030048140f183c0f02ca901103601c1d40035016403d607a590061a100024900808140e40410740e0300c03000c0101c4c0d0010340280d0014280c4890031040d050b0010980d04648004c58030000b000f18040922 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 85472905 1250 85471655 85471679
    0xf04090606050a09030b130204110a08090d27090507050306090a060605091e060c0607020f030a020d050d020d11090406090603080702010503090a150c030c02010e0706030e01022a0106 80
    0x7801d030b0f81ea12a080142036644528034000041c00310350340e20010181c042c001d41c1d00c0e44202d00f040c100f030408465455401442c01703000b01c13000070408041d507000b00380ba0000407904030b22908544030100066442d070407916030b01c561044116401100038203180504101c03005420600941c0500300885d2203112a6071002038010a03201c1c40c0c002c034400142d040c001c041c4242800320207072848040c2d130342c15034201c98480404150700d42c02c25550704842e90711510074051300b660180594645504141c0255145c8058410065501c3c2280382e10341c001c10500040011f05c4410035810b951048000d22814491211040040051034005200d0948134070300e0b102002802172424419041165400703803045060000d250010359803508000c1a4013124011540c524001400900320703c80140011140010328507100f00e001030031114604054415a031404285c617010310000265102119030300c4c5400b00341c010909213224064002d8040207040c15040caa0790f81700640c1803c80b54000d412a06000b005440d9480030110b0700 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 85474155 1250 85472905 85472917
    0x3030601090303110a050a060902010e1801030201050d09020d03020d1103070506010e06010c0c0902030103110609090402090a1b080108060c04050a061101150b0c0714030c090612030f0409060605 85
    0x3048a10364104000f9000d25040c07070a10783d035441a130390069416100c00b0b0030700103000c07401c9410760340d06c0741c1c04402c560704900d99810f2803900741c0302c05034050f030030750300d003810f00401800064144140403464140c90031440d001901718982c05000312120101c0e515010350ba41148018450100740828000300c01050000b0903070341e1684d003240c010091a46000024420000003500c001c1c1040005501705011900c0c0c4013aa2000b080800300040e9a5851410282d59440707100d00514401c00e420081d4800b155158585140c00c82e4048520b03080d15214507030b212004161482043e0b002c0b401460690840c150823400d5107041740c040d08283c900c0341d6150100f40300280300d80d00500d81e00085c0311000b446400e116800c100340d80111140009200501032410100c031003d103030b10034003056400158801c1e143c40c05101400c000e102c004443d1700503000203c0083d440d09070199281d80601c8035900003507025554901c04049030b40080342a00e40d98000f000d91030006074171902078044010f090080000c0d0a600c69001c803a1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 85475405 1250 85474155 85474157
    0xf041a0f0603060a05040914060c040e0603070b0901031d0105090a0b0901020c06040f050114240108060603070e180a05100e0606030402010f03021c06080f0111040308090a0905090601140303030601 86
    0x64248410007000f003980340e00542d1f0315880308c110000900b400f001044c2c007501a40c03517135580fa2440d002c014041c12034000c1410740650808002008103d6010040c0c0d551800c0c02d00b004217424002c907900e061010140da20880407503003080240459048046032410286019210502031507690017a920301340d04c0f0304045018680d02560015001c00d904c0e800180e07034140b0480005c01d03104da0280141441e004145c0d21a0f805010041d0201040500000918852a02070920304840c0c540000003e00c5404004d02000a001c1e030311032054140d81e981131103203440c03400e103003400362440c202640c004004110444401c5500f00b017000000c100f4481c161060b9204040c01061b02d032a56640d5030045035500501c0c80d070711003856000d10603e61011044a04124400115480010030758070b8001c400d0b20340202d40314008085d9140600c91034100c8007900807981507a40015180342c0d9090405c000c10b2444055500c0600300e0bd10300030512101d0030340440c12504032030400a620f030242d4030781800c041d1644070940c2d1142c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 85476655 1250 85475405 85475419
    0x60a0f05030303180307060e010b0a090c09061d060708041a1204290415050106030b010203090d0c0e04060203060f0a08061306180302031b0106050d110f041a0f060306 73
    0x61403481184c1a085031407580c64180c90401319542d0b14101a110a401c0001c3c0d039075184e00300200c807804c10b158048018445014140101c0c0d0103480064061001c0e4000d5004001c50200d01919038851403154035090b120161103503541d09600d04011046400c607005110300e4503100c410a040700c4442c4429a075a811114104008c41c0d00c0d03607601c200304005070800700d0b109801c50b14a88140c201c011901c69101d90b00800c0720a5031020704000500031548142c00c00740525150035595000c07a60300105550b03a0b10020b480441c401c51083c00c103a03604010b01d0340141110014682000108442500594001d910907581d898490030300000300600c0704418004c0c106a0f9100100103142a5170302d400f10744115005003800142046402001030020b81c036000190090707400020308a010080404040754840134110081001d18200800101200e41400000d0400070a00505171034940e81c4081480300c0c060001c20070800341101220028140c415403916910607a8400350903100ca081c500100d80c45032400078903907 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 85477905 1250 85476655 85476661
    0xe060105090604180b0901090507020c0901060212090d0b010b070507050f010c0303180512070b06090702120c100c0e0f10080a0e010204050d0308090607111f020c1005060a0f05030303 80
    0x1625291001c4c11070901c10f41e8640450a045469080d09a8003030400e0300700c0461a807404407070180c5424400b004079030052000c03000401ca00ca0340410071000f1100b03444901031f9916004d0000440942040324003400013140400005030b003590300f600400c03000d4800d405892403a80d81c1c0f010441403841c00304403540410b00030302c1c1d0750b80081d2213075102510608202052003000002c45d2030f441e01d821138440300c00d08684000160103090040048440d98814011a045092f61518040c000d48454800c903407500108030126814078403003404c0c850380d1116103c80c08100032a6440d082d00500e80281551580e010b10f2041c0542e5596040c150101a030400081d16103500a4461291200040805400001c9955424840403525a80764012003500900aa4410380d46050034100d032070400c000a0590418000954450300c40010007198100401f10064114041180034030260b001902c035814080250b070103100c03265504a03440e68061130103183c00b521000c07040d070b84480c1c8000e1002c3d49400b801d5415070081c000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 85479155 1250 85477905 85477919
    0xb03060405090f0f0c0a090b130c02071505030109060e061e0109080303130b012705131509050d0306060c110301020f1204020315060f1002030c030a03060e060105090604 74
    0x3150014210000c81d1112200480140c1c100ba4030307100d1050158000d25a4043c3c10b06c0e2089181e00504040c1c07800b0000315200200003101c1d03d0000c036440a425032903c100310b0703286000b400303000010002101090441810300c01c004089070300c00d0013030142551611a0200304601003420151213820f01414250701015481c540c0030f078400051640301d0410481c030f0008225002d060024501a0000e0b50880d8148020381c0780c51880b83d10140c1081d01c446000503140501030000d20f0410f00c0201c0355440004054645049405211280070005030140718800d012600042c8103500c030300c030090301071000d071100d09403c480e085040d1201e41c4990400141e680a858020494140e0440000007006000601d005e888030004000740d04000c5c002021600d42004100c194103043c00203510060080c004010b89250420008415052088426000e0001d0b03080f00c5621900800407202a644001e0480b9103849101c40004c0103007200340940c0c4481d5001074041065540114151500c00c400200540e05090401c0c407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 85480405 1250 85479155 85479161
    0x11190312110f0f0f0d020a03020601030305030604091707020406061107170f0105010305100f020703090b030601031409030c0120071203090204090309060f0804050304050409060f1b020f01060b030604 87
    0x40240403034001c040ba0781c0d102c248204001540d80441c00050510042102c040c50300f002c8001143c1c0056402510f01c041c0029030114013681034035070608002d92a6294240800d00504481d0f1004010300b10250160703545c001c504024266041c4201d400703000c41c903103d0b6400c4a900c1140e0111100d1039011380402d02c40d20a04100b50000700000b1000c5030506d0b00c00f00017540c00d44400380e00940790307034002242c240031401c0380d0301481d00c0320300640c0c80035460070269940040c651016485845d0032800c0100103d1283d030301c0b0fa04040d0500442040c10034039800c2982c4101d48a521001c48040598a00141d0305070070348070b09054506500c01140c015003408682d072a40d048241c1c44004c41020990384200c65030059480d0701c1440007850081d5030702c0b0360f010b0500360054022440310324444280080741c410000000e000008032402c0d140300b50380c00b00c1c0782c07071041c90308102401e01c6010356610181060205605254041510316100103030b42d08507801502030608050880d52540503840e80028100005465828960 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 85481655 1250 85480405 85480427
    0x10807030209040e01050114011701050303161104051f06080103050d030207051606080a0e0307111c080705030c0d0f021903050910030507031a011211090d11190312 72
    0x43c0001c078031405001d524a08481c1c2c00d800c04000c04c117144a111445580c0501400b05000365071101680d42e5042c00002075a0340075000c044003074240c00c0207050042100311001e0010283c8003a00174402801e0801942071500c508121403c0e0300007000c0c0000810902c00e90350a4101e03078208020f0f06000b10098400c4020707500c003c2055803288144070700c0c40d11030742a11070114001c10f40e580c0d98031070718200044e103541903c010390480d584951081c0814004558801a0001c00a108489100740b0346000445032518048255000e481e0312030215400303003800000320040c0440f62900098500303004414500740c0e0a4681d1142d0b520050340541031a200910390480b56400280c06403d029003000c02398000540d0701c180b9454900006612503090101b880d405000c0c034801081e142000c00c6415812400003450302088000080707541341c0ba0308040d000b02e0810402c40384010805000e0b698440300a04004c006c041c90840d410f8003403001e411412609401451550050300e50210b110550204001b9003111758503800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 85482905 1250 85481655 85481659
    0x70b010b0d020c0307031e14030703050a06050423010503060c0d0e07030b1806060114251406040c090612030e0310020d0608060603120f0703050f040e24010807030209 73
    0xf0014400790f2042000071300341180c480d40d50706000070300058481c820055005103040900400d18040f4026000c04000e0325400f1040d4900003880390348040701840680150b0380300640162420380c040c000c0902116000b40e00e1004d0040100b0540d0342c1e2403e041d0fa4000450704081c11070380a1014840b80d610640004c0303c21130600341106c842546a0b2a9031782040402c1e1100a02461008174180c0b601c88103001d1154055002d0030f140c62011000098203006204110212103804500c6c18088681d0480320900c0c0146a00102d1400c5000c000210b159600c6134147c0e8155800198000e001034101854001c810a842d2400041c4884018554098076094481183c0c81d5050064000e0b0140c2d21555102a0601c81c400300001700d001d52074004010700300312018240600a0b0408400d0082003100c80048682c0304040c079040640e900c4130303070604944a0044140c40c2800d00c8000500180814401e10b04500403081819441c904084240300036020920156200b400309024000040b0428069400b800c100440 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 85484155 1250 85482905 85482907
    0x30f0606060412080906120105190302090c0c0a050609010e100c02030d180f0b060a1e140604080604030906140c0601030b060d0204060b0d0c050313110411030f16020102070b010b0d02 80
    0xc5170000920a80080a04150f128010b00c0100198602061341c1010000100389034103141d41590040748850400501441c0b5402c40001e648003211010020030212540240c140c803c3c07070a00003440c0c3d003c0c0003040920b8446d071040750310f02444100e15104080301c0301800d400071450100e5010520010303000201e000c8001855000c10000441c04801c40030110030701c2031030910700c1d40c035140c810400801d016030041a604100d41c901ea411070041da00a603819038051000da0303003c210b005e0000401c01e20031604500d81502912042c0010181c000c42200195421a1034820303c43c0051807901201d8080d070320302c003c41980060010004102c070300c0d070100c0d0082d9003d450b12035641c1e0150041400d81d001c55011880d040f0300000d815042d104188200c1c55141041e1814900c2d50421041141c1c00d1034034010701401c000c0900c070044410707664903800358200c0d05900508544902c0e000200e880c01d64011111000461780704005c648082d80b062003203800556200703605000507420b022049072260402c665004100da8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 85485405 1250 85484155 85484167
    0x607020316061b0314070309150e0a050d0504030c050904081801090f0605190929070f060c090b04150302090a12080a030b100c140c041a030f060606041208 68
    0x58034035107541c3c000c1c115407404100104030a0070000800310061000040510b0070380518001104c1901c5800500c200001c0410355070101c070440d9043c64000d0170003c0151289a10b11003040341c01201510490740218000503601d940c07101441442d5008840041010a042006050210300c4d00c8456441d0307081032501000807900d600403405940f07817581014000c6000400c0310414414a0b41e0b004e0158035041c60014003007490100e10b02901d28079944003a124006d01d1800d081c2c4071001c00255281e46800030b10104020380c035800c0041c020041440d0b07680006040b02c10215130020002c08440c100c40e6a145411550b00c00c0da0301c104d00030b4210b1483c10ba0300c220344101c0001c0c02511000c14901c07050080c0e42955882a07050006000c0754082246140221901107407403c00340e0300403895031041500004513030310442080322800d0401e0a005c0249a20615121261080c00800a00e04402d90025011101d4072001600701c542da41c1c0007150410391200e820841403000006d0b81c1c0010f8006403251041509001d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 85486655 1250 85485405 85485431
    0x402060307030b0a090e0c12120a0e0910180507081b070609051f110f0a0c020a06030f1103090601031202150a020d14040b011707031e030e03060702031606 68
    0xc0c6281e404020420380b590010a46d88809214540c4070304400c0780d44440c050300b500002521003000715001e001d546c5021982820783c0e8068403002620640051a10300c0f80d00d0b281c08812244501800384400d2080840b284251026141c45807038080d11003900c60501585d250311000e00c403940300000c0045000001cbc0107a04c0011150700138020510710441c05004405030600b900c000d40301c0c44d01806103801b0308110088200c1e141060440d41c03d440d003c0e00d056524030411000355080440340710001d4126141e0b401c00121240c2c168440c40d0b00c005003c10a106801c21240a0407c13400140e4100040740c11007401080003039002c1e894803440aa01d8010740754400000b0b9102c1104820841d1821070903034000800141101d520b120b0008865806255100c5506180e00c803101e10000500500510002d011340751555101c080007500c00950b480441504a40c1c1c80e4103426020010f80001140402c40c030104140c40c900d80031814500c103040b542d0040d410881c0c0303041c441d0440f046685040d10f4142c2d80d861906890 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 85487905 1250 85486655 85486669
    0x2a1b0109050c0108100f0902131205010e07050105070b0a0b01020115061110140f04050f030c0309040b090105010c0f030c02091e0901050105030c190f03200609090402060307030b 78
    0x10341c0500d010707140700c440450014040300d500410000c501c00d489003040c420300c0c200d54071040685070155801078990200000ca5000140c3e240c00421030102032584030f40401005401040e48840d500c01a5210903030746200644050140620080165a4600008540c4113040e41f0203500c40e4030510010030490b02080f2524107450140c2c00c078034000796000302d011048000c10400218103a102600400604506041c0040c060030b024182c0581e4003a42400b04060090801015640c40c040394280c035602d840000045650b5072003003d825000794200106005a8601144514101c400684480440d500e44c0e9132488101d8003102c00403401d000e851402980540c440c1160f107071042400c14018800302e2003042c02c1c551000c1000f0700803900c0e0b030704100050110f910301241c03103e043e02003551220ba41e84248090107070151403076001583e9440c0380810010520800e200f074100721450601700b030180c1504010620103c0e00c620781d6072503004043c40002c41e0040c00c0040c001e60b845001407070000740b80504500001d02c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 85489155 1250 85487905 85487921
    0x405010302090a0b07140601061b0b090a140106170d020c1003020c070308030402030c030d02190305040b0f040303090e071407230309010909150302061b010c0201020409052a1b01 78
    0x61011008074111b11a0000c01025002d40002d0600b51020400030610b00200582d26100526018286000c500359540801c0300d425400d5000401119400398610002e000342120322549000101841d1020400c11010804c480e6010301d9501403e552401081440700e940102c41c1024101542040344070740344202446054061331140c8880d5a80341014010140342801200055109811104050880c19000108001c41e80704407071907824220840e081c103960500965020050705880080c0c81a5064400c4d001441542c2c460388500c0100c54480711b403942546e8048511001007240c2001403d44400d0680141842070312840c2404480c040303e0f07002896031580307041d07048a01d0b03001081441c1c3c0343d0b802c51101005088a410304119007994041174910701c1004d40b1020380690b03030010b0783c007844903a20b64440000017108002842101c1c58410000d00075400b034407904d00f40a142c0710104404402e80390280d600e290f00342100c03005901344441c4501490b8007403400008094045c9843c10315281c005c1c054400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 85490405 1250 85489155 85489163
    0x60201050a0b1e0f010318050a120801030c0e15030114040b06060703021b0303130b070b070806100f110d05041401021f0b0307030f14070e0c0405010302090a0b07 71
    0xa15040000646055a40112980d407040c020707600031140c11032883c03980300c40c0d084080b00c204c1500072034800103070b00410204400442c0c0611345c5c0c20350000d204c80090b8040b4054490b4a0415078441a550121800c0b0400e01004000b603100d089c1c200284001007214540203d44400d4403c140c0e440c0c100081d084450040d40006080400000c00c4180b002071606980c0c4014152902498002c55035402503d0f6410841c0301c00c04a2148480d000141c0c90810581f50703200c00010146a09507141d41d241d68198100810407201100d8000004468078071a1402d40c0c06010007a081c03001c41603402c0070690301482049666000c12040c2500310b0100c19080103081c40e00c2d0080e40781d0941c2c44d4141080111142c40f10300740c0a044d036000041010011081d010820224404d80c0b0000451070019070000741426080d610140042003126500c00601101c04845503800851a08551030389030743d80382510180c041101d42c40030491040c482041154042d40040625000003443c0b109041d450b20b81108080e041840d0540d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 85491655 1250 85490405 85490411
    0xb07083106030c0305090304122a06050304050f010b090c0313060204090605030c0a050f270c09120105060f1002070b04080c03070b0301120f08071208161e0f120204060201 75
    0x18000c3d605449070640014515010390300c0c0c0f905040300184408034a060080074088101880440e8140c400e2009800005003604021419914000103215800954007682caa01030f014000b514004144a05000804041c01803411a03a55240c40c01c504d4000401191300c481d0914001300000b40d0501c0104041d0210480000d00c250909082c180707030030107440f13045028040d00e060901c00380d9600d03a01c441c03440c4803c0345c0c604841041504490108110710410050401511007402460010a0702421400c00142c405000003804404c1440c240d500a8a00c0740c1c01c00720380c3d0300e2403c1754140300c2d042e914101501d00495000d1943d4400a5a8a61081e44244155004045d1074461480c06001c444003c08035444094115410b00004e0307200c03200f40700300c01400c401c1459034a20401401009544c0030741d81268260071008190130020700941c0049031611031381c6240b07503203101050740983d14280008410200039500c0c10180b03202603c0080100038080c0a02c854505003110414aa00040010b41103640c008 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 85492905 1250 85491655 85491671
    0x90212060121171c020d0c030b0306310209010f0504110c06010b070c080a0605220f02040b04060506070f06050c04051806060f120f010b0708310603 65
    0x80401444000715102640380c0e1008000b20b040401001e1202180d00007507595411400c54070000d100b00281e0f107889540c00407406929281550748075200040023600c051010440d11410191180801c80b907000450380100341c486881280104801d04075240240d81d80e450068580000e04004026401610380c0060506c00380300d00e04141c000d80d0f50340103101c1080b90405103c41c0f161901d5035814095412860780104d869400e00240c5540d242c014110130b0709130b0700b0740c00c03503401d082021f85400c444801c2c08540b44420b12140c859244c0d103050700b081d00401c42d00d881d1601c607400c0101806a201c004d40c1d015480310400300341540c510300113051403032042580000051081c80c0c0f10041e20001002001041070600081180b44c440010b00b035101c1e24410000c40441e0b4030745000420601611140c2044030401242460301b000740560040c2c040c0840c410003030810380c0d80d500044c40340d00c200300c00207019040500500318004c0c81403c1c0f030741c40400030325130140e01c8a084a4100c18000d00c150300c0003000903241c43c11 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 85494155 1250 85492905 85492919
    0x504061710060303021e160801050a11030105060d020304060615050d060503070b030106050a0306080303100305010605040203150918031303030e0108010602070b0a02031b0304030507061701090f0902120601 90
    0x300c010703580e0042805202092654601948402401500e1030168907100131000003803d0900220010307860f0035504106064032070301458024141103a0b20703d01c552601383c029039074400c80c405680c101c900c003d1145150244000014000c1e40014104444441d1540c2020614004404c2030348601002ca58400391203c0900c214041503e00c0386c1c0c442c600030b4205440c00d12800400c24100c80c1501c05038100183e803559101012001007455510140140c0404001c3c450541012400c407801c61303005000a028a0380c032901004203c0c0b009917245800d003603100c000210a421b112010551003a20041041903d054804402e030440e4440e080200c41645e2540051082580200c454607000c2c4082c6846d80f440c0d0305090300a5910301c280d000c1d0a068082c0401c0820740c0502c01c0086600c030814034048030780f0680c0500031841d40c0e908180030499950003109004a0101e200d1481044007180542d007410069103400d041200900c42088010619900c40907040050785032410452a81d11000d400ad204e0b640c07401030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 85495405 1250 85494155 85494163
    0x31201060c0c0b0307140304080921010e06090a121e030204170f0d0302220b07030f0513090c090308120f01150c02040b01020a0b040812010902070308040b1005040617 73
    0x10100b40f810a105104401e42e2010018004204420400340d0300c0c1c0301c50820200030702580c40490b038003503e003411040005010141c40d41c00c20003480000d202391480c901100f62500c00490b442c0c28940c2c48444520041040c0b400c00102c04151401c110b030002d40c420100c4444414010300c0b44010a40018003000744c072251141841001d10000c002d002100c003980040d03034031790010041b20400c054001c110204808407000c00220001514003003001102c3d80d8556020703564110380b405402051070010415016800b403021110000c2a14020307041c01c1317042201c05002010301da0010410410035150100004035000010940c5100080b880d401c4c910781829030440c4248141c010504040c2a41c0340c041940b078000c02d500e80a907134100c4000c0386401040380100e181003140c1902078040c0c14064203110600084000030b129070300565a00031041ea80700c98204050380318003c4010000340d8503400240104640d000e030309402c01201c00400d50115941c00002d805d44606401090b403280c02020138040c4030300104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 85496655 1250 85495405 85495409
    0x1b08060708241c0c080d0315080a050a08070503040e01090b0f10090b030414060f07020f12120a060519050301061e06140909040308060906010207030c050d0302031201060c0c 76
    0x39029040a5401c40200d0000e00080e03c50002d462240118003080100c450300c80d41c007a00d01708048031041e8004010040c041d159464511420218410000c100504041598000140c0282c024401a00c0f540e0704d159944e400b20005483c540002e002c0410400c42030f40d8914002c010b070381004260003000d401000400c7c40142e0b11640704240c00c1c190700d00000e40100d40f68080b52000c03481c10361a56a80c0c24140280024111a605180a01c50070024104440890140110903680c01c0b03d0401e65000d48060781e45030680f41128042c0c6061240c401025200c07154994400403600010030030301d034cc0301d021130701007200044000c80104401d0003d01986c2024454a0b0081501e12210b40318400c1e400502ca4000660f8019101001b545a1107100381c52058000c965840710082c20140c99480c02e81801401c0000c180c0b0890312401500e4049405e961001448506a0790410b95041004d40350004100007003c80820440541c0400d0000b001e040b907005440c103000780103d0b01c50010000040c03400d038040c40426 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 85497905 1250 85496655 85496701
    0x1002070e040c030210090e0105060a0210060303050408120403170901020a0b0103031d0102070506070210090b030408030103030923271e100b030a0203070309082703010c08041b08060708 81
    0x15003801c110b007d00103000d49044542c240daa050b41c030300c0a18400c03410252035000320b06507030781085800401c05500c00020400c80d1000e0064490405c5241d2054030207201d1803001825190801c05402d40a0100030001c1c81c0c141c40c1401102c0a980300c0359908900080241d100354042462990707800f100134031103c6002c603030b00340910182008600380800104580211000a0302a500f502c207140140b0303004038080342c090805541d0301a01c0f07141a29014017a41c0c82404101c001914080f000120580d4a40100060318010380030a09288802001d00503100c0c11742c1104843d180d0390501580380c42503440c02440c05007009019062038018500b00c003e91003180a45a480080c89070032003009030300310322010b403504405a0310300540d0f2500c40b484224003828150310013900c969000160140c0002e01a9104040c00311521064002241030b0020107080705c4441110002090071000082d002660780704500140d941c03043c5400217400d4030340000c0c5240c43c030101c81e031001046804003485091881c40c141c07000311885e4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 85499155 1250 85497905 85497917
    0x314011409010e1e040c05010306140105070b0a230103051203010b03041b03170c0607030b03030d0209040908031311030102130b090a090f0b1c0807021002070e040c030210 75
    0x10031012403a44401407042c03200f940b10180100f0700020f814074403510714200c02807070501542001e0402181d0390314a40710b0301d408640343c542c001600840031a4016030964050b1140c9081c05c440c2e450b003150b0303658010031241c000e80d03658581144103414004148491415004200c1256042d4682649800d403a8501070b00c48120500c0108084c964170b20489a202d64800090013444030b060002410405041e000207203111200403c41c8803151744003018101c0030005008851442e12440e0003a8112419003c80d1a016041048100905031080c3c00405100c040500002104851903d070b00301190030a581d042c42c611590082c01061100c4481c0750050018210300840ca01440e010442c0888401d500c5020803050000c04c4000d42565105c0c542c00003400d030b4410a11106640100d6a00185818001e051290081d4034030100020407a58503442d4a56100001514100300c68080020310180010701404502c2030003c0403401c40303503000720f030760045d031081441603009800e42c4100802400e05400708010008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 85500405 1250 85499155 85499189
    0xf1107080f0d110d0c030c21090c0302120105010f090509070501081302030601090c030e031e0304080403050a1110020102070b1909060203130210020d02030406080a020903010903031401 81
    0x82490308445840340780021055940e80c0101188001d0500c50030706422084012920800100080d000503e04011590301000500c1c20706030152481030380c0341c144200b42009040c4810350412a40d018500321801044081c0d4415a2580080c00810080500c4045651103800400400c01110008005400c070001c05000d02d241c400a002c0d5a010248030f05410055a14045502c1201c003890601095030042c0540b03021f0360319440040e0207081100c04140020703217480198220000d002c0705450b582d400c01d01a01c10b101c162549604880d41018006440c0c6007010800080040c0f401c1120940d494800c0c81503920074401a001c015202144d4200f0b207081d1390040049000180403038403140d910141801040c0d14888110f241d20b4010000740d60001d042c40d20000620002808149410102c18400c80303c10446801c900c401702d80752580142600c02503402803009100c0035005681032075000e464058014181104280080d003501c40c40302c230540110303039165200e00007180706c0c08803079014064072402040122 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 85501655 1250 85500405 85500413
    0xc1e17040f030e2b080408010903020606030c0f011202030601030b0d060c03150506070201120f09030c050709020f0f0304020105070804140a05040519050901060305070f06180e160c02130f1107 84
    0x41c4002c0469108036a61444e000300181901620041c1541c10000c000705401480d000c0c0d524601900c900d8424450a03c01e0042442d110300b0011503190103a5400d00c3c80c43d00015040083e410103414241815182d8240080071b1300c900702201d0070030340070341004100856595009000c80d05aa0b407604001d4078400d000348880d4441c401120310031030b130a2810740c183c0d41d807203081a0001e015904810740400d040480d8a03041c143e0281e913405039140079106445035259682a030404a2046007014030700c0d03601c2030028404902c0c014001d998850f006040151a0200c03582e42e08a141e03006400c007600c009400440b0107240d0805a40c40806044190750800c40c034104501526500541c18500c1842d294440d4006100300100303400500003560301030b041359042600c1e02d114044804450044100142901c00d00041c10302c181ca07034035000c55420052500b43d0341c40358002c40c2d9a00204039000828014402140383c0141c0710340d9800c80c0020b034030300c000141d0440c1c0c150641c4c042da03c0315061540d00200a021b0074000ca = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 85502905 1250 85501655 85501699
    0x1107030c0b06061303150b0603161b02360c030a0513020f0d061d0309090a0213030f020d050f010209030c0d080a0e031903080402090603010c1e17040f030e 68
    0x260380c000c401110500206c89102000d410500402900010b010044c400031030500030007500c8403080b940700d07680124004100362125130030b40c01002c2e41c450000c007100c242c0401c00b441ea40d62030a541c5408120030303100841e5150310301d040540d1403a12004000003004290b22862041d29082440040c90607540591030300010914030380462654400c11482402508001483e40121070110034920321000b01000405103544a42120b0541c600900090000501a4100f842190348072843c0c0383c0403010807420354a0300205d40301401b10490b08078502c1c80402c00840d00030003031740030101004400981e60706002c4052504094110321000d0150507510840000a14440300380c94002c01c1c07621b09510314410f80b43c0000d245c241030110309100705e40254005424103a0000a45115600a42c0c603100c42d612100249801ca846400305040000c032900b00909046c0c1010a4803200705100d440d0800441301c01ca009010703074810a80341119540c0160140388105900a0107000b4000c200b155040900d900011464082c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 85504155 1250 85502905 85502909
    0x7090e1c050306010815040207020a08030a030c050c03030106050a120509070611070308030114030c090403030207020123122502070305060708090d11030f07140705040b0105070b04061107030c0b060613 88
    0x21542c0e1b2000e010307200c0d031200d6054a0a8640040c0b904e002e990b6594561601d03607000c4080b000001e400e20142c82d00160081040702d1019030110002d503d1a0721b4104201c917a40c0090034500d0400043d2101400342111a002d51f900a00044000d01166450f1150103003100c0340035500000290030000d000c20104140000362411195008003044c0001100303000281000a04040b10f9407001041e018031040c5a0f00d80c0c05440f40e81d00c01e0302c401070448100c80d07103524408101c9025112910f010000ea0302465480055960045403d1123811554a80001034005400c5021586001603014000410900108110b20390b0002a141400c64080c24085003440d115211003d9101c00d00c110301da418034900404104035852502007a10882d103410b007520b020030050700301581070112481500340200710f520702032160107641c0c0016141c0a103030114682d6488040c0c00c1c000d10a8408686c0c882510400000c114000e0104520940d19007039030310110b1401c01903204002d08024041c6c0024030000100c0f02c036480a40702 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 85505405 1250 85504155 85504171
    0xb04032004051501030c0e0105090f0d0501050c0a0207140603070302160507120204050c0702090402190f090e0f0105090601060c0501060308030718080601030c0306020304082a0114040206030105040e07090e1c0503060108 96
    0x8000d80321300c0400d001d90204cc1004115618100401010390401406030014019540c26110b0050341c61480c114580710310310650340d00400c00c00c0030568917070183d80200a0407480d20320007842c80d078240d1030303080c02e020b4980c5c8100301300d002c840068011413800d07115555200856490403800c0000d5030300460051031000f04000d006000381580e040da04890040180c0051140d1b0006240d41e944039140f043c017a01c00c482441d04a0f01c40c000072500505018080d01388078082c850300a280c030342e10f0a00d08644001c0008402d4826550b40c1e100400031a000c1c1004502c103458075114410001c0c013844049158028582c49205035400210042c0009001c1c0c5001000301e0b03400c100e0250300c80d10340c1d00300415584260017480300d94075485861410458281e00300144401000c5008003c06000c1201000802a0440e4001d40c003034420001800640340981c48801940d03405021a9001030b1100a03580c00c861110001010700d42c007020481c0f0b002510f04a004500e0b40c82e1b032800307a055007405030018041440c0070781108 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 85506655 1250 85505405 85505419
    0x311030a110c060109090311060403140d02090a0f03030e0d0f08070305090d030c15021602100c050304030b04050118050c0907110a0303240b04032004051501030c0e010509 75
    0x407441c0c0015015101000407041c15100c1a580d250b1000c0028940484102c001c41d508800d40350318136130040ba440c1d10482e05030b15200b030255202a058002c03548000f84400e5444e030309010185568889040070f801800fa0104995030550850502410740502a030105115a01400398480082e49201211003141c0c1d0005801e030726401c1030300d02650707680101628960080c0b00048400185640440e03401017143c080e18000103844941c811007020ba22070741d02c1e002104c3c10305942840050501c03205602c6842400c2c9031400c40541c030751b0385d12400c540c03140e031055404182203814001400001e105007c400d00c019075400540c0301e01e5030786080c2c60303500e01410688504041d4000400944c000c80401d42940d10420a580540340c0c10f18000e0020304c10000e4441c071001014102003200d03281c8441232015034075034240300f90170b00786183d0b690301001c940340c001c1003107206041500c0e506680f91030160b039004411401050220100d580c000401b207440480810b410440300315003c20b02640c01c401190100f64080d1950 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 85507905 1250 85506655 85506671
    0xc1e01020d031806090b040b1008120d0f060b130b090f0f0a0504020c0a11030607210e1606020d080105210102160303091202030301180c030b0a06021c0311030a 70
    0x1c580303488003c00040c0240d4140410502000800d86010703100700e1250035480d00c5601e07101a1881c0c0003d150003943d40550003102c200d00b44c01e00e03010141080a40d0312802117000c40f440b8a4410694102d940806c0c07198001003961061030f00a60f190b0000303070542c924483e04143e01e03400002c1d040b0000283c61401071042002c0c68859407210409074014040c042c0007590382e5480c4600f4160f9031849940c0c10b4640c2081c41c5003501162501143d424060b00c00c607075030324940d404003004030031241b41140c042601d041d94940c504594020107200415140c44210030040b0010f217001c4020782030541c10f5125500304602c0784014008d0703035514018000400342c03600c20120b44081200c01c0500902c0781c454104102c1c2801e00c4041304260b8035030000b0001a1140c44a54420408520140d076039000a01626180c618803410340600c0d1a06a880344602c0c10a41c42c01242d44903032030003c1742c1140b840340c02c01e000517000140d60004520302e81d600740360781480a02e03080003c0000900c40104a02000c1d01b4450010384070481 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 85509155 1250 85507905 85507931
    0xc020918062e080303060a0503070f03020609060417070501080a0c090603020901020109050102070803160807020312061c05250501140d0b1f0f0c0515190e0c1e01020d03 74
    0x40148020254045014030546500000e03607130b504221083c5205664450f0082600c1c2004202d11048451740c43c901c000c22400c40c0c1c2008155001429469040f041c03c1c07000284955410002442803080080589681420003000500800d0010030307001095090440f03564034564030605d090300b111414a4010b844040542c0100c0c0504481b04003d801903002050440c00d01521400550103103002c0f00000c3d208200c210000c0e101840d088603071601580061083c065202c0001c20102c1c0e00ca000100390f55003900318036140e40300320110410251000d03440250340a104d0046d18040c03018141280210244440c0b4040c0007c01c0750110380d80980d40d00c00c0c04100b04217049400e0b00004e00c034200041c0071003515030100c2e07040d003031980c01114400001442e40c42d6001815014280e02440c3c0e5410201410b02c82c6501720414808603400780c0f500c1101e90620380c00b410710220b6441a2803c0c54020009004124480f9007006409903c3d941118540c541106500c291681c0001d1035140c0b0700600c0c10301003080c140c0742032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 85510405 1250 85509155 85509211
    0x18030f02011e0b030705030a0b0106050c010b1809060a06050a0603021b06010303020d08100e0408180306130c0b0a2003040f0303050d150b030a0902120109030c02091806 74
    0x2044000b904050400c4004085035030040200c81c0030130381c112000c07950f80c1d108065440000600150101c0d05100c0103103c0503200d24001c0c0801e000910001c1100c81c0a003010902071003005444130114100d0200340280031009000041e004400c0000038040b240c10400069031484d114480d032400d00d03a000800c1c501151100c17a85041d40311100e4255840741da07490402940b1101b003a504c1c1e100080038403000a1089030403071200b00550b10090a01c42c01070340c1d2582d0700c1da080d5000414040007048e41d4603030304038280d070204016849040c1c0d030f008210560180b4600041003001c40d800c0055801428070003102290f500c541006001040f182850160110706079916083d4407468005032283d01846202109140d04000107205030b07040d4640801410300c218950b00f181c01c4a500de10b20b40106e0403c00300c1c2c911202d030f0700b03c510914001041d64504c10f824000c0e96084940005085002c903019980a80c01e500d000b02140b640000b4590300722012404600805440b480003d0403a420361200340340004030340c034400f4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 85511655 1250 85510405 85510421
    0xa0306080601080309010f030c092106050c04081501180b180406090311010203040c1422060f05090405191106070b011401090e06060904140c0901030b0418030f0201 72
    0x64260303010703561100c10b81030b140d62003c0203403804106040c0520f080540b0910903840f83c251144d0b01c0d50743c0c2a082a460781181401c10140c841c00c904551188030100b4181c0c07182a00500700c203c03a0b01c1d40c0e0791414200d1420510600080d030403c40e00c1701300402c805801d504661584c20000c2000103080040240000c43c0d50000301f0308000b0344843c0c0d03c00c0004010496205a010900039102c51025030508480f107070030b03444212030080c4003d1810300204081810440e07541d40c124001050600540070446140511103544000b544c44c8030f84a49007009840c104440a10190206030340707460440c81c01e40c4860361740340c0040c0d41a41c020110602c40d213013401341d001860b2100b6640205200e0340e038002ca09200a045a0a00440001c3c2803200c04400b0340b9801a0090004c6600b02244485a40e0312102005800c1e04103006854210b510386103007034101444904c8841c070900c5503400241e2106000303400141155000700500d03001c1c070310305110a10304840003851518170b680c0c94500182800500203040b40900040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 85512905 1250 85511655 85511669
    0x20d02060c070308120604050411090406021c0b1003020f0724020307020102030405060f0709090b0303090a080a060501050103090b010905040311030d0606020f06070509100c02091504050a0c02060a020a0306 90
    0x1d90b201004100101c3c00030808555804c4182405840d40820417003100e001341d400802141c0100588101401c10001c07140e4080d000342c100608061400100b0118515400a400340700ca50f5031074180c4a900e0f140305075529031569480d0440c1400c0c14010200350034850050b01078903030014152156040e41d200910070401c081888425916818034a9029010b5082503c080b25140107010006100740485800d0700e106181a994601040d0701e449108402000c0c01440c041d0107000c1000b2002168582d0b41c0780c02d0040002400070900b40032a420101c00b160b40c180c010504140c04c01c510440402c000b51a02c1d4107403600c1c044000b403076850f1480c0079158203182007000c005c0c074040881c40d0550105294804400c64403941c00751001d09540c001c2458458804503502030100d01d003444007034850705040c1041c1c004205541404040302d860703a00003418400040382c81818141c03240c80031100f94289400313074a41009060100f40180c580c81a80a501e0743c00c01440f44114650105403a0718141c483d8000c40028800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 85514155 1250 85512905 85512913
    0x30105120c100c060e0606060d020a030b0a060807110115050405090a0c0f090606051606050402061b010c0e010f020624090a0204050301140f0601050d02040902130801150f03020d02060c 81
    0x2d8001803c20032420500307641441c42c102d090b85600c82d01042d514404c0d04010f000300d25203071501c0c0e20301000f504152001020103564080b041541e4442a120794058038490711611814685008000c2c0025400c10b01e00c100ea904000c40d0783c0c0c0300c40009641c0400d03a81d0480340840d0f1036888244d00c074600345148030050b00b90680620006084034a2809a00a0780c0c3c402205000083e1661016a110710030b804e40900350000300002c260101c0c1042d40150f070020300c014080d40c6410444030591001062800d90500941d5607504115501a0000c200d50a007400038200081941ca07000c0020b034580500a0401a05085030032207090244c91081040081e05001000000d26081450400c4000d4115009480c001d43c80c204503034100042d80d854191140d490901c100034240d592a00450f002c1e0000d2002600c0c45809120100320752140d80050001246008a2404900d10b044441c0d0b0a503100136001301191011020140031f69000415824141d079016034581c81d1105041c4080341c032a01c42c414843da07160203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 85515405 1250 85514155 85514179
    0x303050a1b03030e060903090108040206030c16030f180510081909030512060d080703030c0c0206041d0105090108032a060702030a030b030607050a08091507050408120c03030105120c 80
    0xd019400788002013200400c403400b569070142c0081d80c07032159a100b540802e070b1941c0007a00500d8102c00840c1d110308144860f03814000f1441e101d490415008108801150b25041c0302c500c25940b0420588640604030a1003880341c5c601400b10b20080c81d44a10301040200050004685030b8400c1890b4140c03844e5001d080010034100e0030020710541004a075078000c03e00100200d00685403c88120350310540182072030b4a07240c1e459a05070010b1403881909818403055880701c80c00751340c400025000405100d500d0110b00820580220101401604554418000c0708014010260008103890244655000b80c034854a03480c0020b0b4180600c10300c2044a078440c80040000d02903022016004072040c545007032044401e0003042540700c440448000c8000780c802e00408800921030070310941c000d07000b00b00380c8005030a0200e110661980c00c50b40400271079800141008590b008115940c03043c9600001c0c54200076080d07058503201e22040c0304141c4500a000c4a400c0600803d012016425100420440b0448 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 85516655 1250 85515405 85515407
    0x10309020f1003061a0a05040b070519120e030109080a0e0303040e070201021b0c0603040206031801050103050c011101060305071e090e0115090207051f0f0608010f05011508010303050a1b03 83
    0x141d0b400f9070406060841c0542170084280001d886d0301c451192180e42c241810115808002e801c040410f890301c0c402c0400d4040d82911303008500f4005c90080101d4001d4480100d40941342e00c621859807402a8946503115001c036038480246e601001180c031b01001c2252062000a280d40984d800c000d201c0c4400720300b840101a01503006040f4103019030100100701646c2c03401251601d00141c0030744d400c880700704002401031400c04005d5612403404200400b0310030b4030035921401c482098004803681c0d071124905504540c0c002884003400700c6888002d1100f50f04517030711140ca0b81402e120f019a0380514502c04902030311602580c0015004030f013030402903064060030080c0030380101d031404181034454150114014202d802200d005a401c4002001d01c1d0580c80e03071003105079140e08070150300b05940d98641c8520054078000c0701f00800510002041a04448082c06c08481060b4070009080c07410b01081404075401c00c55107411a501800c0c00c58844180c1c0906880001c003440c2030010351290f56607030300105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 85517905 1250 85516655 85516661
    0x106090f05010302150c030703300e0127060b030a200f010f1b0201120c0903020411030103050a030302130f06020d020105090706120905030702030d110c030d0e010309020f1003 77
    0xd078000c40f280c1030b8022a85c05244080c0c40740075140300b601d400c100320020109000c0c1c4c258080f200c07001000c90307080c21909003911081d00c02d2502224921038680c0580ca2281c02c00740a400780b000350301d00c0300b01c00c04890001c0d10b10225a500b0b80003002a51250015a000d641c2441200269900000040700f1185441200904030000e002000c1c81503000074484190f0354420f01205492007610749030240715000111403202e2208202d02c08a0401080240d5098105000d000e498801402c94442216107800e500c100b2003941c0d09d20303802e4070780b4207000e00040000c01d0300080c00c40f007003a81604005039910070200c00089005640c0e00402c403408149600090707aa540021320311030302d1500707500810540e100c2c08011501c40e03400307103d41c00010380c20108100b60202075074011440ca5114008980c0382006690200782801d900320f51082c0801e5034803000c804100780c00d002d42d0307030b41da40b0480203008488400080501042100c030402d07030416a59010410454031100403c07581410010288240c803008841d005000e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 85519155 1250 85517905 85517909
    0xb03041a070203070b0402010e0f10020c0f040c0905060703050c060103080301170c0a050111030c070e011e0e0708090a020d0501150503010e030f0c1023060102190210020106090f0501 80
    0x9095040d000103410544040281c2e0400c560211046075981c0f1150011a0501c0f2145215a440100c42d4030720040750b5183e80c00040c3c40d0f24940c002c0e24190480c4800c2140e9452440f402601442c10030450488080c0c2c007079031910a5410441340242c884265060880e10b5000c1c40d00c412900d841403100100510851402070740c100c882c940080e074201c400300c103203071920345039402500c6400034050340040c0480d41c001c00150340c042c4890300031a4149000c043e00c6500e400100d901200d09101030350010720030310800150028494421950400000e440c0c07a488007505040182590300700400e040c0440c402000921801c90f24907002070076403040784000c1c24203c2c0203003859005000b4a41e0381ca600042c05040600a801030403500c0c0010b035003005113840940b040d55200d0f16038040c03c4e00406481c050000c0c074500c205080400030151101c044231402c9002c0c10601d0010340300340e041d50700c80700301425108000d85400504075810b070b44d0044103110b01c14043e4050305040c0c0180026604103041620740101c40c5c1c2c44581 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 85520405 1250 85519155 85519193
    0x90f01020a021b040207020a050609040b1816020f1b0d12020106240207090e010603020d12090902040503030306100216030803040c050a0303050304110102070e0108060f01050402041202010c0206040b0304 89
    0x1220f08800c20032003284140c0500941103c0a040208002d00d49003001e00004140a400412440e41203400500005541103540346032494050900841c80d41c0e002e207968284100303000030035291100302c100e1680e448802401e0040494650090041ea454818091511542c080360b10001c010000002038003a021a000703020b0044821008050b1104d86401c4100901d03115801515046040c04059000703090225090a407540d224000000143c803286594464103018010050744989050001443c0007125401040b40a005010600196401000302c0e0780111044414001410b0040426400c11890103500012042d40000c00010b0244078002548100c0c82501230040c081e44800c00c00010f08014000940041d10034400a800180c1c0e5500d041460a414012186032999498544803042800d0f0404211908018144462500c880d1062801740000726020340c24642008022210010031910190411101340189019034032001e0458000c1e20b03001c01d20554a1600e4141040d8404000341180 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 85521655 1250 85520405 85520443
    0xb0903120c0f090d21050d0b0103020306090f04020114031801060b16030c08070506070c060e0c010203160809030a110a0602060103020a03120e0d380f090f01020a02 72
    0xd40c10108290071240b2072010030b11002e0800c8580400c0c08000c51580c04216200001031030080b802c19000030701220f00d521544d48499541e400560400150381c0c1000b1000e0615005000348940c036981c03c8088e0340d00c624800100e646a17591400101c81c001c10040b40d001d841ea00000034400d5141100c0414011050401e0003400402da41c0c0704a40c020384101c00c952562402c3c11204d03080024410203851580e40d0003084864203240c02d6844a0742400d9081e41c0040c003244107400100200038190240200c810103104c090508000c0c80741c0080d480780701384c0c43c2000000c90300e10b500000308810310f01901c015000140451307180d100149042c00e81c5c0a1210f04040c82070807000c100081c49440010807a068036400750007100250700c0d5507500300240041c1c0030340e8018003218202c0400c0a482d1540720503c07440c046d41c1d2200407032000c420759001ca20801c0d1421481800c03030442514044000b481e00c240c2120741e0521030441595140e03480c41c14100a11030804c1c09500014807446441e81c0026207141d140c0c1d42442c02 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 85522905 1250 85521655 85521661
    0x20106141f030e0f0616090902070f030f090e1602010501300f080706050a0605010302040b160c081204030b0106091203030b0301062705092802010504030b090312 71
    0x1c00c0341840c41d9040420904100d0800061a110782c00191581022008039581900400400350030300c0320850303800c4e1303c0004260410a10070760204c1c46000504110004500e000e40580311303000039014015010f014851451409804240700d140d5040007480c5001442126040062441c206145081e003004015820b290010400c44055401e44560000ea680450f41429010800a03c48040380d0f00a8465084800c00d03280890b0b1880001c00d0f2461180c00d0000d0705190031040001120303040d40015040601c148014070006524000b21654031038070903800d1484203081d140c40c8250384400e4000e607529003c1c05150050503444280a001a2889042404402ea80311b40c822118800c0510071541d50303011050124000c00d009510466039450060700101e2a10388407101c0483c003400040361303d00d50080303150300c0c0c0d1000d00c0584241030f0003440d128040d103003e50458a06100401c1c880c07135175081182ea0004d0800440e03018500300c40082d684090f013241c10346020155107850b0740141c8101d1000440c18000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 85524155 1250 85522905 85522909
    0x30705070503150f0f060d060204060302071a01120b0c0714030309011b080f15030f0307020102010509031218010b040c030b0102061005010207090209040213031218030b0f19050702010614 82
    0x100074469091180e11364501d94811109801c3c0042c050300054100c0149054107003c14400c0c00107201400d05a1009a0b0301c0b20035203850f50b0048245220703048114402001480040440310001000e941c0280d0004c0706521960000076403481900c200820074200c0300085904208044080c42c85880060000c01c06003142000307403140b40f60401002000150700600051810741d00b0314000380c0144c3c0d0fa0004100d00c589040200b850a803140109540c1ca030700100b207100444da0309010b6030751f1014000713000c2c40c24405500c8404a0703859003c5d080080d00801c200c0300105120702548020580100100140103682080e40080c0003400005581801400b50703400250840e1308031a891400c03500c0c180d0003050792038907040507a0000d40040c00308036442a0208002c40e1080c1a0400400196001d14000b0f01d010231141c0006d00501d50f400000c10900740e2a5100300041000040502d0b403041c680c0709060f04c5036503000b44c4544500c1e14002c00c1d081c2c031480c003001d000109505600010680d81205400340f8000d040d081 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 85525405 1250 85524155 85524193
    0x10914060307030e010b04050f01080d0e0609010c080f03040b060f030a0b040204050a06050307090609060806100b07060212041a01080c0604030f0201020a150506011206060c110111030705070503 85
    0x1290a81004040000c603180c43e12a521a0380209070703a5000081442c404000903040e10380070344015024445100040c02584800d000c1074240a115080205079641c0c6403002c12140c2c050200b03041d041c001040700300005d000a2800719030f0445200035040b42e6074a46450700004082080c0c60807801140aa1107000c15407e0010b4503103040740e007020009a403031b43e59500300b0010f46001082008256120309001400b514100010005015421400700742581418111011901c09501002c42644a90280702a105040003080d050f03900341c544041e601d54450400002a10030030054034800204441000188205911074060242c2c00140d041401c0e42c1ea0081c403036640b03280b46891980b0150030481000040c0c0801c882c50029031060058960003c40b07516402485d031200401d84c800503885401b0070440d503a005025a003409090b6104002050410000906200d10145c00401056881442c0782c00c9a0103114418040e001150469544440600c0e0042c0c495000b44102d500a10400d43c0011700703020114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 85526655 1250 85525405 85525439
    0x106120b090402130219030905011a090f040501021303080a03050a02030c2b020c0f06010807063e0a02040f06080607080403050705030a1d0a24120212060109 69
    0x14401d40741070300c40d5020080248080304001024030f40c00c01540d9000d640401d4030640420040c0c40000d0700d02614108982076680041c03103c09500180d24080150340d032011407a54001d80b0886e001001940c962405600903c0b47c010711132070360301d61104000b042052000c001c10000d44142c1c0c4c203000a4503125400c0081c0d00003038500e15413600060180307441d00010b441c001c02000da0032110808920311900c41100480c0c2c4036200b041202d0304002d54201e04088200041070040c44154001d0401c1c1d49008001000e420303519450003041cec5401d46030b4030210203000302e960036203200d890f140714207510f0700c50740c0c066882141c003100300d0246051180f25000d000c0242310719003c56200f035029100a0350707080821502c0010041084013031000900c00503000c034500308094422052a45c94014103589a602c0c400e48840c030340701069110304960b031414032072840661080701e40d121000ca0f1354220200303c03d0f0261841080700300c3c05840248040b62a5000c55020b529160103030000782ca802e46010344400c10548502508 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 85527905 1250 85526655 85526659
    0x10f0b0a06050d020d06240906020c0f030a02090a1a0d0c050f151809180c010e0d0501050a0209010810080a0b0a0b0904120e01030e0a12030912080106120b 68
    0x1612007041120b00402c001c1c1500d0000c03580040c9400f21560b4003404445ea1034006241580c00d0101c255400e050b0301c10042d5140c0071a05022259501c5c0041c029990300c0b0002c9000d004032043c0d40c625010b074400700900e0b21140d5004184040328900107003803000030304039120322000b1b5402e40400707071009042150100c2f4850b5040791000014505000a0064616440c10556000900c954000d001286800040e003400745000322141509000b240030050b00c0300001d040380c042685070450604c0460000142009228028200880f48284010000307006407102c91000e040b55090108021290407250300a0250481c2601c1e00401c43c0c9401121100e4042c4600800d80664000103910010030240b14007103900009680012560940c0403011540100c0240d4040714680800302030762180d241c0000a10199481c20710b402c00001480b51640c0ea0f40d58809600034004185007800e03181110b100380c022040c82c0b80c100385016041c0c071354203130010b1110609106d480005519036808041e0a1031034015036428040c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 85529155 1250 85527905 85527919
    0xb090609061302010c06201909050103060b09040905030c0f01021e0a08010e060301020412030c02010f2a05030d020301030f0302150c040620100f0509010209030a0f030507050106030b09010f0b 84
    0x5c3d41d0340d00700249103008008003401a99190049120340300c8008000c3e20504151903e91684e40140c080c1c0340c00c800350072050501d4148541800120b0300c10040d1911544c00300c07004aa0107040381440c43c1144141c00c5411168003410112101080054004250000e02441c510310003003407841180b1007501644c0c0d0300030001142d050041041d00a003e00d440c3e00305000400061a1542d507444055102140c03407400c07004645030300d19420540d03030428860b095800315420600200060440098240349180100f9081c50114031700103018000e040065400080038010215541d58590030400c01510640504400611520032442044090200618007a81c24a52414213150920005454510010a40010768018620800c10100f82081007810084001c14000354160704040c07401c064074401080d1851681c01000300311516140001d018a84036044500040c5922143c60122180c2c86054000390142d03081080200900a840304020b00400540e0008c008001006a150055411502d850396111403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 85530405 1250 85529155 85529177
    0x30c0201180b040f14030703030f050706090c090516050a0c030305070512010f17010209030706051614030a080708060102060105060904150905090c0111060c160b09060906130201 78
    0x102840c07072111403000c41041a90840d4503201d890485810950160094101481e020048042104054081c140080d4080e00f0b4047c1191000350001c019490407030304200700003907090140403942d403042002c01c1d4071100d441d030f0f404e5844000b07030050300c0d0030f40341c3d90501844071004144c428011070403144002d20548038296038880e1514240c00600000f449641403020801c00501e061000701d8a060180040c0c408250350981001c85144031541c0c80d5100b442035a01c10008030b0501e0360001010400c4800303914155a80d19101d504054814908182c010031100d102c500500103040e01002074411304130f181e910440250b1340e074142140c0008007036540e603000da0070440040c4120f0030001700a00020703d0140010641e06510b000340c040031502607104a00312643c41c820f0140416040c06110450b000c2482c1c20390f00c0342d02d04c901050b2161005016400a16400580c03180d50b0402c4075106803029400101482040c03401168040c0c580b00105c4d000103441c0101030019110102c44010f40300da036901a99039803031140d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 85531655 1250 85530405 85530407
    0x8210901030605281a0d020c0717010501061b0b13020f131505041407080a090222050c0c070e0411030604050f010c03020f032a040902070b09010603030c0201 69
    0x5482645854101500c2d4400801e054803100d042c200d6900c182800341910460b0001038050b40320407504907013040d02d00300d08000c2c1c9480211080c0c4000030000100103030380302940c00c585403030440e03d9800400c180b04810401c4212820641c08281240c1c0e003521044899214500e0707a00d11041c03181d100900507002140405e0f00c24507100720442d0700c1c6202612a90300301d07040307100058000059170703e8541c0036030b2620800324413004c1103809107004040a03079040c003951031101c40141790802c008082c079082103113038000201080b8041d0080840c06801801070310a00018902e1191031310002460604000c0c144070208400384000c104031909010904050b04609e810464010350b03011001d08103540503400002e007100c165900b404400d00652040f07000f01025014074174441e080d940641e4214082c03620501041802080450440b0b9010750303070580d089044514044d0f000300103600e5403150001032030046004a0281200d074002c10080e400f5401e030707040c50b40d03e1709006400d030388103404000e00041b8603055210042d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 85532905 1250 85531655 85531657
    0xb011508010b040b16140d0e04020309060f041106040b03010e060a03050607050f0702030d0c03080c090102060414150a0b01020705060c0712021201021801091403060c0310050603041208010821 84
    0x201d50b0b2400c5c80b140740740e416200c07242000c540d02c40854541c3c100ea80c0580c48290071030034003400040c05580650440c541000000e0f1100b00041a82a00f640c20302c0000d804c0080301030b0004903a1000502c1a40c8407600d650040206030002d00441c45142d403100041002403405010110450b0341c00700040529542d1020308484c1c0390040c030070302c05500c00c0903c821401039500388180032020030300d0ba4421941000f0b600b401880843c0150041c14140010812515541d0b4042340f4258070be500b00c01e940309819004c185041c90000156103c0c034000443c4014800b002c1c01d141c0100310010300981c01c454400e504d840400506115208502c4500da02000c0100812800c0e0340c0c030804403c7c0000d00345010381804d15100c0e400d81c1e0010081c0c0d80500d80307032403000400d9a00201094080e040c501d50a01c48403104901081d030b948030141164202400c04000181038010980541000d000b0281210f078490a0030701e40391401c045102040340100360301100114804a00007407200350740300407000301e8034141500541e00c211 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 85534155 1250 85532905 85532917
    0x3020f121f02210603071205070302010f121514040e1b0d080301030606030b39041703030a0f0507200109021e0f0402180402030a06030c030b011508010b040b 69
    0x32502400300780140f103030581196480c8000010200181d01d805801c150400311541c000d000e01544c206210408500700107100300603a682802d00914200c1018000d4940b02001401d4081c89800d00d040800841c41c1c1030740200803030b404070841d114150707020002c11090302d5002054142070343c8450310007102c4c072164200281540e070018140d8104003455888001c80ea0384241c00580d04070b51588030400030485503429080e40440086080610741040c00301c08621038200c820403007140e1804106505a82c645d08040f00c0003018030616070b00c0100203641d0255142d8000300e40003072354140341042c3c1e50212403850007554401ca01d81c0d81c44140c24a11115440c10200c0c105132140000e6581d1030b414001611201e01c94141114101c3d41045c0c000e0340c540800c80d440400d414118000d90040c0220254051040f00100c1511401c4801689980d03402400070300404181e480a0710349441024000107204440c05403e0581d001c8000902e0305407465801540c0000b400e1103a0380845a04020030481c1000c49005411 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 85535405 1250 85534155 85534213
    0x60602011b08100e010617130803010e061201020a09080114040203070302150d0f0218030c0306010501030906090203060703050910060e010b070503190203040510030519050709090e0703020f12 84
    0x41c0061301c402d100ca00a0b1004d0304001c0100b54224440b071080c40185082a034000300e1514103684402c801d0756600341d503020610030141d40413440404a50280d503003810040d00c03200c464008644030303044048014004107107440341c010107520b40007000524104541c107080c0b00c1c2d1b40240060031418510707030170300130401c03800b40c1600d11406051003203190b088400d000b12049103030460070140e00c482c0142d41207030300c0c80c20079a4294400e51244101d0849620301080c5141151402d080016503603a40d03003802c40c080e080301c5000a60601030398040120058060f88118041c6114a0417200031482603030805048840c58007508200f4000000100090f5203904010007031244500c080e40d040052440041c8200300a5104200c0960008107040c41107080000590a1000403441c040c011420160281c0c3c65010000c0b11240c105520740d0001031025000b8400c2c1c000400c1e220108000c0c0800c03c0a145403a880e0a0004a218070004e060343c0c89a42303044007120400c05000c401030880100c08070441040000740d190055 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 85536655 1250 85535405 85535431
    0x31a0d120c0606030309060e011e05030916030b040c0b0f03040213060504090c0312021603020607030903080409020c060106090311010c020111030d020c0105060402130603020c150a0f060602011b08 86
    0x1100199003805203e0080d40b09840309286c49041610141100c2241c030ba003241001031410002040d6944807c030f001ca82001c9e820482d0f40da0710742180d9179003041c40c000592030500002e10780000c00c02500d01180be200d5400390b28801596616280e0480403840307110401e452090302407002c10058684414034503001e540640e800101540d640001c01c040d250126130545900d804500c041090080d000a16042010540b0142000506c000e500700f003421020b0002038010800451070300100350060125102460300641b9241e00c0315a07440d60701003c0d40c40392900b0300c00d41c02100300004489006410140039640c1c0410b80040c001d1300c070700c0110364810340904241e040140c0700d44401501c0406000404401113200400b6954140c154034213404e584000c2c1c01103010f144100808041504011000c4050b21040d18000d6598501c03951104d15116420410403080c1100d0018416003000a50102c1d52031818500240400ba40d141c2c4142e003211035188044070b01060000c01d40c114140314051159010030108008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 85537905 1250 85536655 85536677
    0x30f0308060105090d05010c0806010509030706080a0609060803220320041409160509060a15030605130e0d03060303081611060c12090c0604031202011b0807031a0d12 73
    0x3017000d1403400703041e502079550b01c5c01c2c40380403640141e4140e07010b01e0030b080c142e1400320704d0408240e03107404621a207001c00072140049500b40040c0d0700300c42d00400d0541401d0118540311820142c0f0f0758014500005054941044042c500c800c1842e91030889400c00e16808102d449030340c0c58500311042041c05644541d039203ca061004040d480a14017a001e101c00801c2c2c3c100025803c4901d480349500403d10603901d035010800c03c0d40e9005130120985114201824140c1c0901c0010340250215410a0358002008004c400903501154001100c0c680400101d48644a140e03d081d0f0854005000260000d520400080e45c61000c503514094003a0062402007000e4010108040c1064019600301110600002c0c1c030030301080708080310325001095000a403501a8080d00024028462484010000c088042040043c68001e500107004140c07200c42c1541340000746500245180c4040b19180702003880e040241446a006040c2c062000e000500603002c000722503117901b6443c800c40303042c00b01041306031025 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 85539155 1250 85537905 85537909
    0x1008100b031f0308041706010506070f030215070e18060f0103020c0705061c0b06210411030d08040506090c0112181a070905040525020708010204060e0316030f030806010509 76
    0x50002c5004d480f140342c42d81e0500703070803814540302d24a030103070345a0080d001804541da0304000c461140e0f6210940c00280c800520b0305034109444207000c803d10319860010040410b8200d0388950411908540000388948001031038450b0759030035200103400801e6400c1006440d4081c3c0d0041c01c44e400d400c000c4030b424a82d02c100080f410790054420b0000c03140c54080c10003032907a2500440c071810408a5016042042041400d4840340c4601c8038800a02c14203404202400300341c02104014400c050147c4200c0b4080308401b80c00f0482c252011a0180700310b82c001100030001244007404824140d5624072a100b0701c03d17030500035180001e9151456002411101d002071000200003200c600700b070092800900d0700784005054010641c0c0f0081c00345003031000300002c2244035003051003c6204001310b5402c0c44503410302207183c1803c0c1c0d00300da6650b41c4001000305045400000103a50700700103c2c211103403000b00441d0151120309510000b0080d014101842000a004804448d4001b0043c5001803c003954800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 85540405 1250 85539155 85539211
    0x403051c14040602030c0f0a08030c0d180609050d0e061e0903030310090608030a080a0504050a060f09110d02212e050f16140f181008100b03 62
    0xc880001350f03000080241c42070380c0900c100d1424070700d103c029014079925910303003092030710000307040d14110075001407104103860250380840700c04a04a1001c030130003400c44c680540144030591040c0d80b00e104040d103503c0d88030300c50b07141c0740c40640340580680c0c100b407480d45c191031000c0c20014921002090034041c00066803010400b0710304c10710f11101181019480c1421081c00c865098101546507042000170481036034220701000d03001584107400107066070762403c0a90420800d018000d02441c01c1030603001c8290300c03641010107058014000f09000074044020813502000b0514001e40221710302c9034101d0700203155004080040c3c00c0c0c40c2a1440c1c42412000c0d0030801050051201e02502800c4101400704040d200c1c4c103902051082d207015890800052000042d24446290010001081d090780e164070f000d1803e460411851610b50b688418504d07170400304000840c40c5d15806041c104440f6040e07240304d820907a00460184040e000d103c0d061521540143d8002007a412204151446408085001003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 85541655 1250 85540405 85540409
    0x204030515040308010602070b0f09010e0d060e010b030114040602070f0b070503010f050402090f0906010219050705100807080402041104030f050c1c1a060a0b030406140a020403051c1404 82
    0xc0745154907241c5480c1c050301321181a0041c20455010303020520221441c00e041364032001e804108581c481d00c81800413103d28118039101c541001355543e4500070050540c208030005882c200080c08154000001c0c0f41c200c80441d1307040940607202e40046070200b00254014441903014201e8840b1182058460800c031a10550f5440c001590000040003100c062076007100242c13108071400d600d000300d171000182050107000401b0b48074002d150042101a8020029030b42003000b000ca003015045194140151500030501c2114058808514250215071080c07000c0780c03040c806034590440e00d845a4080c000204054602c03100c28020400002c808910701c0007000d000d040c4140c0c02003920310944001d00c00c40c0c0ea215001c0d44521007a203606400042d240005104102c00300f40d081481c243d441c04006034a1500d590311040c00a040002440103001c1030350440c810800d450518541180c1750b0305079020480c0700d00d10000d030252300208840325405003404600781d040703122864503203c5c41c8555140c0c08990783c482d0b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 85542905 1250 85541655 85541683
    0xc06090a03170603030a110304050d05030c060108031303060b030a02120a0302151b16080a182903180d09080f0f0c21030304060b011206050a0605090402040305 70
    0x884080301015845006002c0c40c0028001406260922802003a0f503400380d54070690134001035482c6090a00010801d4900500c03004001484d508124148291aa070100700c40f882d031802648004038603070200000711198a210300c0302e07103051640b031501e40c04020440040600c1d410b016408426000d40d48403078420301c0d218440310140440201500e000303407419200011b11044001c1400c01c00800d603411410310501c2e070581d0751155950b40320401d00615640645507000b0000c1350040384102c02d03290300c205e5503c01c070401c0c0000400ca903601c030090702c0120815401c074030b000d1100e0400d002031001d911402541e040300c041200c1c450401078841460b801c00f00010080c800003010f2000c00c0200d010f080016a2400000310050b0499040421009444041c401d00940c020a6041c03c41d04100003140001102440741d00b095a480c0c2c00d1500d80301c4080d042460ba40760006012055807200e440052251600f02c070300040038200b0082c54103034181d90030740100c405968441c0d402d100000100d0b4081c404c2400740010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 85544155 1250 85542905 85542913
    0x603010605091f020d051b060c0309070b0309100c0c060f020c070501030b090a090311010903080f1e0613060e0c030106110312130624080d110601030f06020c0609 71
    0x1500d06100741c80041401c03c0314040c500401c80c2d40f2698000c41c80803c4010356191072544c8180340340940148030064408400c0e41e2003401c04004003144050f01650140c0340420540300c12554541c042045400f064a5488032a0404503c511a205141c2d0181050703084505201240e605151102c01c200d40065905c103a10540003e4080070a030001d00004006d0074003420200842d03c4808041003c0507401420141025651003441040c1070040f8614003461840030000d01904003289030080c442d590a460704644280300170042484a81e21038640d074107503030a00c43c843c4683c0d0780d00001c000080e502c80c502441e00951320040800c0c48500c50030394500c100c00d1120039035940c1d403400350010440401810032003450b800a00c880100c85809000d280d40200000203062402d11036030400800038802090b4403000c49d004540c3c1e040c410b20b002c240d05421aa5640141c1c0d02c0d4000c105011340e800484100a20351940011005200145100d14001b444e28010701006040100780e500c0345280c400b050b10b2007032a580c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 85545405 1250 85544155 85544167
    0x207030615060e0607062406030605100c060c091205031e0f030a0207060b180f090f0706120608010501030c0e1b0403060903020c03011107060501090203010510050a030b0603010605 79
    0x1058020680030703528072148040a20714110000700001009100c881c401d860010302d500502030b80e80c0004404244c0d05402c5140144c00c4040d184440555125100100742080700000e414502082d0001f80f2421945403980110055900e11000b081c2400c0e100042c4030820501050100500004d0351049203e640290b5031540c41c07041e103030101c40700d00b680e41c843c5120400c01c1c0c581081409041d02d400180e01c1201588400d05840d08802410100203040e81000d141440c51940c500b20f2003610b4046d840d180030700582503d0302c940040d10b6070621811050281e001032010006144900000d01541c030a04400103026501e8009260a45038203034000d0707036200c01c601e074140001d0311001e1006820070001c0b501800c2a8080b11440d0790701c1e014070b200c060f00080d502d1030104245402400b10b090816030080081024242807120025244c0043d0010b855040c40c0c0710011406584a1007220705980340101900079001d0345442c100c40d5544001c4090302050340307541c103407070b4036450704400f4501809554480a44030a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 85546655 1250 85545405 85545413
    0x303020114060315100b0d02120603060f07140702040609320103080702040b0d03031a01030203060d0b06030a06150614090a0b0d02120a020c010605090915041a07020703 74
    0x80544600c050400001c409210442d5400a01092044440300810103940d4510030501c020162550001260701ca0005403022607005507801020181d1881c260817445864250905550748002c90b03041180e48c5508000c80d014a00400366481d142255402075490400c25501040c00d540207540041c0318203845140041540b40142c070074000750080b0101884048a102101e0005c960040c400505110303000211582551156005091409000380c5148500d00840c50300a00030b15450308450350100d441803c29a40c1d600c02d0084034011200109010450103c980b203403007c012024143d40d5041c0b00340030381e500000e45140242101120914850301050b0302d4204050010010081d00300d410130000c1219514a60703903150b1410541e00c1d152402d40c0c807089400651300c0248202661040c1c8000d50100700807605600d0f8004080c0409164020701c03102ea41d41043c085494015145038640c1d82000c96048000e201c403410702d5901c0760103000440d96501c0a0100129402000d070f902d0801038100030b000344288 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 85547905 1250 85546655 85546661
    0x509062103042402030a080604020c0a0b0105041d06010b030a140106030b0a05090f0f04030323060f060702011b050a0209040305070203070e060102031605010f050f0a14010b0702060a0c0c09020403030201 89
    0x961010043c02e42c03540320404025224801c49104106000220000c5601c0b82c8076075040d60903116856003105d5902420b0300307010250350307030034480c0078803860800302d0030950309811a41d202d110018210050600c4d0342045a200d40642000b4441c0c04c07800d5446105450101148503018000e06e515140000d6000c001400d00034403d0080c0c2000d030003203d0110a20060070440d0007099807103180c0020803091a162032400f00e0281c8842403901103404003800f0752701c084076181d500e4140501400c40d111054034010b8002c0c040a802070b038002902007410300c40c440c240300c0e9050307140200c140d100b401542c586089903400650044409e40c0c1c2900040d0380030a6540c214101000780e080501442c2215100074504180001d41da481801c00e0204811080b42c03911041020940001c000182c0c501c009003c3c6141607400340c6840f0700c003142e251108905040850034a84603840c1c0290507a42980d01c0c8600c0d02040340c00b44074280d4440518101004003016100d40804d102403100009095121405a5180c0ca1828002d0035 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 85549155 1250 85547905 85547939
    0x80403030914090f07140a020709060504060605071b030819020d110712031107060c02010212030403090e04020f0909030d15080706180f08011409060709050906210304 73
    0x1421901e04403425614004010350081c103404d101c3c1100e5841d217004648070852030000c10003907078000c5400d5851540118481064800fa00e00401c0902c0e500d008000c16280c9501c103200208004211500104002024181c8442c407081e0703d00140030b9495459150607402119170310340300010766401c00c50142d07060000307035124040d0b454603922081018000366200d440c64071076402515014a9110105801038044007810284001a103502654807076002c1d00305041c00200700d0050103120151f02c1e50200c09025603005a40550341d0b00d0101781070200e58120b1480141c41641d1041507011264130a0f070b640e00601d4824030791140519260303440b160f0900245c1e0070401d0a1498003101c1d010500440d00005078620466045260044480e005042d201c541210310b41c11a5090500f20301000c00c5a42054100510760441e82c1e51000c015594400303065180d0310141e5174440040d00070075080100d403414031800c0d5040074000344080d40c3c240440c41d136071103502c0d141062503181f500b000c02c01700550a0380c0b0b424444 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 85550405 1250 85549155 85549169
    0x1e060501051212090d06050f10050a23011205040c03140708100b010908060114130204061b02010905030a0c090606020d020607080a090f0303150801060f030201050702030111070804030309 82
    0x418101c1209a494a69104100d40e825000d804201455130b90345162264214540041c0104458200042e12500d1444100c500e001c0c0140840c4c000140340c00c01d40820012105800e10301403580002048912100304020300040c108040171005440112881c460300b4091489220301800c140e1840c81d000c007600d504100454040d812040c010441a0004108264030001000000400116030b0740103981c0002d284d00002101d00c2a0400420300040d402e030020303880300088036a80240a03c00c0c1486090340b0441c06031000082c80c0d0f40c034401054000e03d100309a00d610504bc01c5651603202d50100f49407800002e0244d4540c8a0f80c00c041020441c1440f9450141c40c0e588040e200300042c01d80c2c065520030b03014011108001c0340400292075003003154081500c0c80c0c0c2c41640c0700210b491500340140605100009030090121301100081c1c104814814101201d8100c411f80d0202880e5400545482d00055410380e095525111440d505190a070001e0040f40c0c41102440e0300c40f811420010a0201941c103c45 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 85551655 1250 85550405 85550419
    0x4061e0f05060f040b061206060d0c021506190501050a0207030b070207061205060906120a0804060c030806010903032c030d030c14040509010e041a07020c0102190803040303020a0c1e06050105 84
    0x260344d0740714142203444941d007c000d410b4654481001040c114030039424420b071024600041c581306980d01040084d0000013400500c40315450b54810400d0164001e24144807826a442c01041654068005803401a609005070382009170b0f03030b071036159070400101c51203001a00490b005112540e0000c20002c7c0c0c5404040040290b4501503012509005020702003d21446032200c981000d2002004800601a032103c1219121652090050407800c12241c0480c086803030f0310002041795110742c0004040300e806948441440e0b07004a10301851246204250700c41182e00c420002850300c042218907817421140d03a00041214008000a1850004240d8418100e000300800c02195450410b928151440c145001100352607501d4010b9011282038803800c8070030490000c00c01c130140c000c5184664800e0a8003603a00440320300b00c443c20101c1400c00c00801e1040180b0100e80440c2c0300f1742c00350607403c12506090001803111b880b07044c5000c41c05c1d0a514502040090075208111003809018010f11055401c9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 85552905 1250 85551655 85551671
    0x20a0537110d020604090e060f060303031e0c070606030f170f0403031b052409031e07030e0a0e07030f05070c0f170d0203090d02030703020604061e0f05060f04 70
    0x11000035940c01c028401c0c11042400402d541d00c0c103048038000e01000d1400c1100d003042044d100e49420080342c9000c074002c00400020120b00b000708c2181d2081c0c07003a001c181c0300300244204044081002400407018242c041c0030041c001400c038402e0901a40c0035400040841401d0310305100709814070411104146003c1c454503a086108000341c80070380794580bc4c900881d9845402c0742000b001c0f10480648140308810f02c441d010b0300c800460841403c0070038142c0b1003640c2e400c602c66540c1d1186d02242030b280340d10301c22140705102a5a003c3e0104600c20302e030010707441c0c08203c0018141c80c0e503a000341d620080c040061122180d01403140c80c94030750314400188010310b4140c40c0500100c0c0b80c901c0c09402c04400c000c505003000300c0241c00305100e0f0650b51000b500c805800035190000e4104540c100000e10030220000301e175138000016252455855401000030795150340c1c400001e40f9040c8208408444001d0fa030406408141c05407140110186c01c0000b018600f40082144400d0503114140c01145010741c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 85554155 1250 85552905 85552913
    0x302030d0201140408030717010909020a050108070e010e19081005070e0a0302090a1b0314010503070f03081804020307050a0315060801290c06011a030c0d090201020a0537 75
    0x915504c683c02c000c079180c5a0b907515000341c9000440410300c64411002c0e0001051a1400ba4015072990740207844489909444000558010a060b03403940082505da11030000d1039846140e02916443d000344c4110300d024048880042800ba240d00300c10341c9500f00f800b00040b089828410f55500200030710b00500c50300b80d600042044124103000290181990400207204510b030f47d00310720041805031000740c1e407103240c0c4240200101500644000d6100d94040001074601d0005116000d440340000421a0680b0f1507407100c2455010441120200a402c001004140d440f440554807070500d81c2c480654524444100900300d40310394404400380d1a071414103000326684a000503041d1003c101003001c41100440314a076260b1901d0495107195100000e042c0300940000c81c02d035049031110300302d030142580355090310007090200700c0f260040d444080c070256100316125004040802e0041c010389030160051f0701d40500f880b08a05c00640680c40d0290101544141c902c0800c03100481802d8609e240421992 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 85555405 1250 85554155 85554191
    0xf09010605060304082d0408160b0a11070b0304031805040504030206070e030c0d050304060306060801270908070f031407050705150c030408070f051f032c070302030d0201 75
    0x405441908041410f038400d2403012075001b0b0b1030f400444106181c0040312120146030340103008858560003000c01c5600c001c030602d6501030a40d00844161410720b50400070417200461201d00fa90030b030f4070600000007800f01c0650000c60140c2e00a59416200381d09500ca0f41180740040d0740320303d014915280c01c010109a001c221950030542c10303d01b51042c20250400646000d429038200c40d40810400070090400100200410444802c1c0c1c5041c4502541c0b0241607030700d03210074850307802c060404c6c840c09a40b00b42c4001d180b502680f25070320000b4503803036146c60710002a00040c104440d114090008801419045107008038a141507400d0345103410304035910f0a803034032158480c650040d08120300c51421100648141ea0755000c02000301da841b140e036042410790b0340c4280d10402542c0b90200001085c2c60800400410307820080d40c2035003040da0600f940840007401d201c00451006000c17080e902201e8803030071500c0003c821515004140703460960040506200300e926683c802d41e0b250000043c00d12880300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 85556655 1250 85555405 85555411
    0x6060804020904060b03071d0a15050a030602070305040b03090c0117130206070203010b09130308090d050415031e06050102011104210503071e03020c0102010e1b0301090c030b0f090106050603 84
    0x613002140304802c160200e850481684c01c105040c001d0001e841c22903018a20809116803040b06061290100306520350310800007031702031150000c00050083c03010464640040c80043c0c42403030090b10702645c03500401103a4100360f6001b0303410741180a808215681c81702d0a0882a040c001c26aa000d0400b0a00c000c81c1d18a11078009019540c00f190003410341d607081d0f01c440c4800002500c090290710700224408104940400100d0200f9100c9020408178000043d00d50941f1846448841c03a15080400020100550100703250806880304c2c1c0c4000c40c1c0504c11304e00b4105a41843d804a01c050a05001909550b40046042405402400104007290003041d03d90314001408400300c46000c46818603a007944107a0401030300100705001d060850720b4030042c511200c0c90182d420fa60305000798070012400c0e9810192903000d0350340310000501e043e10361450301c2c0c04000001000020b411110f40d443c240360070013641c8180c9070040114100301500540c001500e0303210f1803035802001850b08140c0080c146000107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 85557905 1250 85556655 85556663
    0x40f030f1406091c030e01060f080d021504020127030c060f140403020d02010504031704031505100e370518030304080d060816093209030415030c0306060804020904 72
    0x200c040d894131315003c2d0f4046101061440001d11480782c0700c0c04000911001c41c4200c407014840d007400c400e44070344042174103d44444101c800034910b44803500111303800c11041c0b55030814a82c2d10307441c40c0182c1503a901d20300e005602c1100621201807910101600c0c010b1117041e144d0511404402515015500b101110107aa030704686a8104005038001207401d8000c5030002004541411214400407c01c807001d0700c1224446e518500008039400760420541300c1c01d03510750b0410901a0428041400c161012690051008620144270101069080d16442001070001504009040c502c2c0e0101000d0080c1640004460341814240110502c2d6036501d2000800142c801d80020804070040c024540000c00117204010071582c1100c00c4d040501c10300c101c680310b141201480e007420f1740c50304c50703007d07180e000100c6100300f840c09040c60000309061626401031120301c071350008000101d50705008015210002000360b40014080c9031118002c0c0c2220003940141041c000c3d1b40341003200503a50644540d5105500c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 85559155 1250 85557905 85557943
    0xc0c020f01090323190f1104020a0e13020d140f060d020918010209060c06270c0d060209121f1a0d051c020c0a09020f03010e0c040f030f140609 63
    0x524885039051030461006003145c2030b2180411403c3c00b10101440074841d00400782621810402000c110032441980e02d50000b10b940075100c4040d80c80d02a09210407030005000c050300d032145541e050030031030380b0b410303c0074840031803d4052103040c040000c10b041e480102071350341c10020b00564000946841c001404ca40c0314500245010725500e40c29015a15520b82c0542040c0d1142c03080d032100c075100e180864580030034010384810300100d00c1414420703003004840c42c005800c41095000500100c42180f41041d00c4480d000c006660302c60301c0f200128030034804458083c1c2a4007a155005201c29200c1c2d075000503070141442c10081c2c4107403210802c85000b010031a4441c0303000d5070601d0410f0403e0704840d48402140200383e00d190441e6008101d4036208102191215005602c980c462401c902a40540d03202055090005000ca491001c01d00c9410402c4c1102880c01c0035940c074814441019650011140c0c4190780020604120514115912690303821001d8a951f113040c0301c1065440781103c0c210070a82d40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 85560405 1250 85559155 85559213
    0xc03040f05060106081e04020f01030906111b1903020c010305070e0406030b0106020106081504060513060608010204090e03070321020c011b1e050306190503010c0c020f010903 77
    0x24000c00c104241a4000d06a580340d41c2c1d2a48043c00d413080803200c075104040713600100540400e05d20300c00c034403407030303004190700402c0985c82c004400407d244a4201ca2060b6918551880e00902101501c0c900021001450f940c0903a184007505046203081c040d684002c1100300b85000076004603030548564400c0c43c00281a40e103104c0300f103d4085401c51300603002072400c80301009114648141e03030b06031030082d00248070690b03844000650700c10013441c050f24102c01c403001140003c2c0650b000035410802900b1003015840d06d40c2c0b02e2400b02c8425070b11507000390303500103800c002c40511030003100028060500514102070064034017504403007012802000300340034422803482e00805035041e0740c844040c0704e0003048045880d501445800d901c0144101c04103d0040b0381d00302401044916402205a0351b54090441c1c951000b44000340c1440d031404c140c4000c000c600402c00751403d01c00e4100c01e101039510344010780000e00500141c00ca00710300c590f0400c8042901480420b03490ba2804405468041181011030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 85561655 1250 85560405 85560413
    0x30d02240411060d0c1b15020f070203030c0f07061e0c021210090b0a050106050d41090c030304170f01110a02070602071206020702130501061106100803030c0304 71
    0x80d02100d4035840032021070600503100c07045d80880c1006513a62240350b8170354003004080c1016100740c1c20041502c0d2050900c8501034075150064680740003070304469800e01c00940d00090031904007087c85110b50384040c041201181081189000400c10703401d08402c1201c1480348090328074203111071441800f9244000c4021500c8c0c1001d10303420b00005c941070750a151910000e14026101801e801d50307545105901042d0040401d106d058100c40701a140c1515059241d050400641030344045211003004079140d4008040b42180e03e01c803000180c200d011109032092200e0f40454a018200c3c100b0703540310445250103520000221804d60716140506068513001e101020b21702099100d020400b9401d0001e41d8080e1450180603200c1d8a41c00d8003503d0f030a58503007000302d80d0b6080e1481646c07810944c10f503402c0d020940590003841b9241c0040c1968035081a0301612030b0a40d802a44098000380401c1d400c1c45022406125072a00b042c3c18941c140122031a2027415641d030b000c080c0c800c9440d2000000440c1c204 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 85562905 1250 85561655 85561673
    0xa0906080103031e020a33020c0c15070b040b01050102011a2b050d05031e040203060601120906060803031e0907050603060d150b040e060402100f0e1e030d022404 71
    0x1944006207008100b116030011103d58007c2441245e080000150030030303590828000d95500c0700041009282407410103082080628042d800c0c40c403a1a070801102001c680c105010138440c0d4061481411030f549898002030071600701c0d20710710351445c0e410400700109903244960030b0b00603009080440c0709000101001c1c1e21a02c02c40c5001813980c070030a5041002507070420059440307440c4031040c030850b010003c5910601d481e0200c40095042d000314002800030740c0100349600030070390302100020f14920990344080440300c4071380028030541d001004000d459400906a40d09101d0b01c02c0800081d030812003a02e42c1d44480c9070080c1c0c2d10400e804000a00d6a407900000e0409681d0040342144030068000c181030001c3c8008102a40100d003415402c9210307480c009031040c0103d5025010503c0090340d824211407080f42d44030f440c403c100185030190099981d080400c505440b074500c400795605043c03030400d46402808003e400c10364201c41c61148180c81c4000b030031400302d5000c4081010f2075546140107145 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 85564155 1250 85562905 85562923
    0x20708030414010807110604060f021b070305120a1b03020a020a0e0a0b10021009150606020c0405070f09030f061404030804020a050303031603090c03020303040b0a0906080103031e02 80
    0x828400410001008100420640c030b1090342030325240100e44030310500b2600c001c000300402425901c114040790006003560f115000511000c200181440c12034007101c20600391030002441c103503004103401d01c00d01c181440b00c013075940005003000d840c11008140280100d010015254a8060120281c0e42454000c1c001c40304203a6000b03040030341082c0c44141001040340c055405032140c6240a16040d084c0c20020504204000e0355001441170780f280781c0c0103a01130040a00204e507410082003440003030100d240510009018503801400c5100100403d20044aa00424690030000000070000d14250411804815030342c1024004200b2080350400102070000b10240840780c8490100700300a04d540709036024085c5100302c1c0e40440d0140d907001055900c4c001510050f5041b8420107660804901070b91122191074400d01039200c6103540c03500020b045421541c0301c01e54002c0d000a2808119171300c442d010b40605207905052400c2e50460b1001800c1441c4500e0783c406511214005000c071038020002840 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 85565405 1250 85564155 85564169
    0x130608060a05040c120609020405010c080313080c010b03100b0f06070804030803070e01020d030b090c13030206070605180d09031205132303010902090a09031110060609050603250207 80
    0x100700442c04e103008048841c1c42081d41a2075180006c003048136950342c021102214030580d00c6146132041503c032a031003540007501e1652061a541c801200080505002d0b010090fa420000204412030805160910b00a02200413040e454811550071540c0c68800d980d0030004191819a29402d640c541020b40e841140c0018202800100c10000c900d0341c8259901e80f42102a8251003c042111800b030b030649000343c540350b0344201020b0008042103842c4000d0100000c0c064040c22a9a40e641c0205941d94042c02c1d042e0354840c1c8540070000030301c40e5805100100f0b28003070000c081380104504014012410390200501d00e40070102058a4a4440c006072088480b950049091841c3d0f510390103601c82c0180f43c0134144414038103600c0e851610f07041c440c100025030040c01c42c1189036605024000100010725044082c0501c0078201c0c4060001000307010041071030804001005403c0035409003412a40b07611091040c3c0c03042040091003103100082e00d03440c180e40b070400c40007401c50000981c104820760b0401c030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 85566655 1250 85565405 85565411
    0xa050f010603110d050d030b010c1703060909120307050313060e070305010c090602030f0c0312070518040905033406050f0f040503040605031005060403050d030c0203130608060a0504 80
    0x80000010341c02507046902ca00c021040c2c40c0100400d000c1d03070a01803107001c0c10a4006100c0814418000d811040d0090414034000c0c0b09100250303074011001048807494400b2a2020040101904111000310b4110441c0001407070208010301003001d8511004041c4001c00c1808400b06004001c1071644000d00d0398080d00600c040708045c40035590720b1000e44005d8901c2e42c24124219591030040340d80105a98403980074528020b17911018040381c1d80500074080092004001030800b407080c1c1910140650015503520342c0c3c403161502c40440d42e0310312400c2d05203ea031402e04020006100081140e003042070742800b501315140100b40c80780072440d880154030042c1c14040891004c006981c0d0042d885101c20188140d59600e82c01d030381d84041c1804070390040242c0c0c401c000910106020301b0285521501e542d05801c000e03a01c4601141c0e060b00720385d104980c9a40586c2181c60026051300581c1e04c68140c0d88000c0d0308201010450b91b4074001c80d445840180980a00882c0158543c2c02c0b031500a00000f030814 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 85567905 1250 85566655 85566673
    0x207120c02061b06091e0c1504030b0907030309090b210c090114011e0f080a110d09020108060103090201050915040b07030e10050304020d12030b03010603120314060a0e090a05 77
    0x1e113441c0e11044418002c1390150580081526207888030902803144550000e0407030820300401c1c0440034668100000030324605000001c000780d0300f4515144204c40020140960501e14940985240003d80005504134104945c425440e1209050108014070082e8668010a100400903003400301002099400152a00000c10101030340780740c080000400fa1303a46461150750040100b90303491403004100001d100e80075910507607442144d049400c422404000502c0d1503c840900b8850b0f444101ca520015840c1d8000e13400f950380000703011354800000c0c201403000d400580d000a1451154442c210300c505400d0341e41140194002059501401c80d2a101a6442c851820083d0500000c581070601c47d1540484445c0c48038401c9060328080ea41c09049490014070715036072052a071040300b05090070556510380340e1003d584d090059000540c007402d40c8803514003030600024183ca4160000a0400040c00300344041a00c90445e00e2088826034804200c058840b40301c05c40c10030030802000303272844c42104a5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 85569155 1250 85567905 85567957
    0x507140d0906050a02041e05100c1a07021e0c0d1b0f0e090708030406022a100f0806040b03030706090305090d060f05010e060d060e0f0312090708010207120c0206 71
    0xc06c103969281e20541c02000c101c02c0f10b004440300c1e9000d4541c21803e4080306041c0d203401000516003040c41a00303030f40c1c0c12143c00c2802504941c011144600140c1c4a801044205042104a21071a142d001c0241c1341121505010409000340410014880001c0c00c801c0c003203a8400d00d110f0745c003800c00007a0183c05969a80c0110440940a862542c40c07401b07884000076030a5400001c40d02225030a03006840c0b101d040d614894295001b000c04484881c101400c000340a66079506d05503441515900d03151100c6800f034000034058000103141e14021807800b88030503403d44d0b00105070751142c2d602101c003240b60b00445c901200c441c015454a2a0042101d109203005c1042540042c0240c01640c0e07410070503a80c2e501e407455499078091b1015a0001c02d10a004030114156070044d01000002c201220305890154214519580c00b51240da50141006014400300388414080340004054500080d401c1c461942c0b142c840301881c441911003804280e9042904640380e860517200546064130050f40c4070605142 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 85570405 1250 85569155 85569157
    0x1030213090b040e07030f0b10121a100f2c0907030b1609140d080c0c12160e1009020a052203080a050708120103030315090507140d0906050a02 63
    0x192081d81468149942040005401c07406c82c0d4011a01e014000b844d511180204580584603121030303618035102017140c885012010640b14030a400e0080600d0554102c0b01d0352880142004921160312101046500792050115003035844212a2060602488590384920801d0203440c108082081040048510300450700030202e80c02444070084580e42c0c06a40c1102c400d820a104002c206445070074485011003001c40100e03803001610141407143d407622399519a800410400c12103502c5008071150508000f592001180b0f403040007080c0c4070315810304544c0110050702403a86a40180800140407145002010740144440c00c0308568440482b0390092596024401c01891485a03051041c060212080d20004590300090502c1c103002c10228220740c594040c2c001901c0080d03061001c0c40300c8884201201d4000c1d4400d0320009207c3c0b400340100b400d020181d03880b54604515080c10400c03110341141824948801c0c043c0c68541d40c00c40c80ca2100b005004200340607203000d290030200484061079034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 85571655 1250 85570405 85570421
    0x30209091006080a02040b031801200306040e071401030b0102190c03030801061112030c120114030607050f0306040c0c050102130905180c040c090e0c07021011060609060103021309 79
    0x3e960404960b80300c0e8800b40c1a8440d40c8954401c0c60010400510b01c0940e54100e403580040250020803281c0030000c065070320035034440451006100000c01d00038070b85001d210b182c041300d4070b62002d860322518090000ea84040c800d85094145502e50090396a203a02c20310104502c4411156001d1510b0310506110507101c10794081140490500000031910030f000f90701316962800c1e818000c0466a4844d003c2c444650030103012800b10910500200c1c0d485468000414041c2c101202c00144418050003010326180c4050003010034001c042100040c000c85402c12294044001d8401152140c2c20600858101400e0900070704154404030320202410800b00c41c0070304a800c000070901242d240c50000a200c4040074030704a45035400b0b030300d200d070711414946c21034220b01d402c170304140a0043e5100045403041300102e4100018000c000360080c21813070a180d0100b4140c00b54503012044410103114a076942c50003074480b0b8807482d48000012172a0b031107501111100c8030300e0f941f903440203599481c024020340a12 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 85572905 1250 85571655 85571657
    0x905070e09010c17191d0f070905010614090f0414070806060903030d051308040305070815040803010b07050115080c010e09040b0610090503070b031806071e030209091006 75
    0x4038903c031898070f2040c01020300f04900c050900c8010340b01c032075070250300201041c01c5010907510303200350b2481c1a10100000e510741d20004094100380d61080902c07810089503400c1450218500801400096030054688070481e1110320003e40d03400310180001c200550a404607070b48035007840c0c00100050103c0c0f6101e401049141c56409854981108006542c002d00a040e900b550044c40616440b402c5a0005a0801d08d0741088442c800c200303459030a001d91064006403000c0d4421401005640380405c001c042000d5030034042190350409980342c480910040c8100e11411002090304014840f0030360000c01641c0081044a01459460400b0b41d12080d0030509903012031030200070180c60b8104481803600c900d034084d1900c6202e564000800200740c000c42081403c00c2407440707003c926910308000034070190140c040916100c0c645801000699140d602c40742c03901c0d4000c0018403010780d40003240d010f103031585180c4498154040310300450081c0a40398000b980940314006001d40450054150410303201e20b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 85574155 1250 85572905 85572911
    0x30106031b110c010c020f030a0602040e1b090103050c0d1401051005070816051e060115020a0c030201121401030c0501030b06041d18030c010506100f0c060f0905070e0901 75
    0x42000192400c0a501a4020103030f04585803407855907216642d0001c0240c8010070b81310440e40d01c003011910307140c00c50a046408a600107806e0000241c0ca01c150340e0300034520110b45c0f0f0500c035844070720701d4640130310b41a0034185602c40010500c801c00060940d140928025010000000c00c1648244841020f124242c00741110f403001c0140240300e00101e40c2c0d281d81005c411498111100903003607c0f11b40c040402d41d05400340600c50f40800b072118140b154050700c04c100822a0f03504154000c3c0c0c602c401e00340c0080556000e00050b100048449080b0402c0b03d8090800c4501306c81904560801b81544680100b4036068000010040168014052080d50800c5e40d0070041c4001d10028003095205600680480d0400304c010f54049001d007026865000840c070081130b00016054140390f14640000c02502003c3e5160010400c117424503103044005110399190007841c040000d00040c21201c2d106002030000ca440c0d41d9003a11490807034009442d515070045c100d64030669141c4450070b1401c0c054a81c80010b5007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 85575405 1250 85574155 85574201
    0x5160503070302060304021203040b0307030207030207060f08180f0d0302070605010909050316020d02040207212307050705030d1205010b0f09040e1c050706200a121103010603 77
    0x380012150180d0303902614040c5151516001c0260603004621290080c0c401040040f070f52040803c0a58002c0c2c11644025843c6e007014540682445a190860b03810481050145152140d104061640101c00d0050305400c038052500030500702400308140c00494030500160201c1241c1c140c0c0103001450240d0b004003c4c507601c0b0001c00041d07a980c03d0000d0710780c0d4401c1c0030340811136002d44a418207051009045520000d16a404138080e80c004200a0742e2a481001e207102d00d00c140900000b01c035006501c1c01091032a0700c0c907895400c1c554080c0d0b0400140300d001c10504100801000b440000e03000003411941072583c0c58600526040042031301208860500000040c00242c1800340d0b030303011598862450501d5441c4040c070004000860b002001882a40644103030b1204e09180d411031001c1c03a69500b640e0f081c00f41048025150061030642450071405400d80c0c4903028039007901c8001d089460b019035603901c40d01c0f00070301820a21480410340074000000090058050380304403580d412880a40700a02 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 85576655 1250 85575405 85575409
    0x10c0c080d090510021c02010b09010b0903010b01030902300304030c05030f0a0f2405070e01111501030f02010c060e0705040f05090c06030c0c120702121209010f0e030a051605 77
    0xc1da04d0100c9400760b44110700c0e0101c03a1180c055141c0c0040010310000480303054400014007405401e9010a0407098001900340241c2820302074080f0618081c03c0c14441c50a540d40425100400010007501042842001c28441000c8045141c0d50900b40c00449440702d40381c2c100740c0074400745841218030a105900d09081540c0c404075150a9030347d00301d03c1500426145440c1e6001d190002111007a8224601d203109840c1081441903e00072010b641d03078110b0900c41079001424401d100303480e10399030713501800c914120f45070390404180c190399000f42d030440c80c0307030395480141d40a2080b240c0050509003020100440d01c80002030610441d4000c03941440300305640b4075000b00329041541c41644c0c540140c50300d4001414400300454100480c003000ca4901042c061240f4141a00c0c9424000181000110340c829413422010340000c020150001e40241e0a072154803102c00d214a64116042c042c0c0c0361100d0f02c500d405918450b120310006426112640c0a80c50030035140d40000c0052440c25495140200310f40c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 85577905 1250 85576655 85576669
    0xe0d0c0807080f07060509010306091a010e0a12060b010201020906030a0905070506030106170601050d1e060806010b03010608040302280302010c09052b0f1a0a020702010c060209010c0c080d0905 85
    0x40500300003130b002c414103118044840e98081a082c034141500c86200240d110304610401c00c1d40d00e0b44044881c00300c80c507000014060400b440c1c50620074000d4070b10a0200c20390340c03807a880110742d00c5803002801070305e010700503806030051400381a4005c00110802403100d030280c1103400c0c0360f0301c0340c4240d40101741c640c800c0102c140402c0c016000069202440e804010001c8031100e85c001c04141030083c10800210010020380711000f50050001e007042181405a003d02c0c02604054a07090025000641c104224140c10340030510902e02080140c501103024540240041c0610440484200c0c2004045030301c0c1e0300001c0c480c1c020803030040d841c103844100da41c1d20030340c0d800c41621801081804600307000600e40045101f8040400020184200d0304c10005140390829041a4491003c0034586d005011110ba82d02d0b000a000344202c1c4e00400c550030050780e20a41101c1da02d60300c13000068981c000c100040f2a40d0fa412000240903030101d0300041140d140001d0f20704104030980c1d0390b81083c1c94844050144d9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 85579155 1250 85577905 85577923
    0x309070902130305100513020918060a020a030501050a05010e13021207031e0c20120d090203161208030405030d05012304180303111c0c0909050f01050f010e0d0c080708 74
    0x80d0360b00d000d244c2c7d0041c50000091904004001c8591030b60b000d0321090142002000d0f46c10340c0c2265800520a800703a600b5000d05030060004071450752947d89400006080c0c00380d40d00c000f40c40341e000c4d215548854011b0b0b0b41940c000b1000c01e1050281407134541c1d0050001e00001010810502e000e03c90064400b18a00070031603082550794844c074800100300d800f800e49a400c5480041d96000e003114000c8100d500340c010749640380040c0c07804603404d5540d0052500b0407681d81c0424695103888032003800400611001c2c90348850303005103100d540baa510700b005800c60140706003001d522410840001200300003100c000030300b4030802c0001c0f00100d103088108400c842403600c03481511102c0c15841d8000c2030180e40311014030480490110301c5c040201b84c41800d821512a0214112503603020f00100a9920860240207040141ca0030402820260001e81001205100f1f462164101814900440e403040203c645e0820010304020607008403440e00081801c240c4c00745003020700c00d20b540095065000200441 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 85580405 1250 85579155 85579171
    0x40b070f031b200d06050906040221030901120e0f01050a0b040902030703020409020f0d0b0907060503010e24030106090e1915020921011a010509011403090709021303051005 76
    0x201160046120f030119089658003603880240001d0080c040b640b20b010f118403c0e50088080d10440c40c0c079104000302c3c24107407114078415205079040c108041030000216501c2c06024248521403482e8010300340050b1900c500315010b24060314204d07603106241500203d00940070700e80c00348545124003041c00102c4442240c040e6042e480341e0b6003003015040a5004059060020f00300110b44041000810300408030500115045251385003081003180e003c1c80b204000d485640b034124599403411000d00080302c4040d01c0d4400070141404481030825103c1500002c0180c003030028400959078083e03403401440700268450881c003a4002c6511302c0070148260640f025408812034105103e5850b50100070b4004007146034205400e4809942801644003c10f189150b0071303030003c5440d11850101040800c1400d46c0d241c1070240c02d10060303403242c0e08100c032585540142c0181c141c0b00d40d02d0f0301d16107103044095809034000381e01c0012080302441c403454110060b24040c808035440e0840b0400d100c0d00702c0c1c4044403001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 85581655 1250 85580405 85580423
    0x10c0806040b0a0509060f0d0305030103061506091403012702010e0303032215021603120c090603020705030f040b07030f0f090e04030c120e040b060903060a050606040b070f031b 78
    0x4804c0703151030305d480d540041000d031118024901c000040340303846201e02c0083c1c000c58004401082000060b010307003005913141058501b0f2071450704201030400c440c0c60190f541c84c425044810002038609500000c10005400b503192543c00034107034455444403c0d018168001125608005000d080000c201c0340501e412410b1214122101200a403158030400340844500030b02c010480f122440038009000a00442e4810f40468555880c01400d842c40c90020035803a1400e04800080c0c4507045800c0008884e00c504001da40c504081c906581140301d400911310442601040104482035000090901076102c0c0c1c4074660030b002d9a03802690486d0044040d9400580d402c00140840c80c0010fa9058001e48a42003410a0208551380d01c903041a4000340103002460072030196166240a00a43c42180001e65015160002d80c2c00403a841c0c6400600c0d00741c8098907407000c9140f82e140c1100b11001081e046682c6902c0301018a0814542c20004c0010f50000f074500e240e8502d01c45104441d01c2081340e04c18064 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 85582905 1250 85581655 85581659
    0x309060a051b0304080901030b0d1104021303140703020405100b03070e0d1e05010b100206040b1015080403080c0309030a0e060d090510050f070f0e03070b0c010c0806040b0a 76
    0x1000780c000200010001050202d110b404200d9800c003550090344071743d40e010b44400b0b81000050840e0340e2026072a00c05c0c080c0007407440c082030340b5482c0b007002c0110654001d42c2d0340c0048500042d200d030701d55000400500e510aa200060140400d095040c0c85c400c4a0038001c40d00c0742040004404101c1c00b034026802010004a1186402201c82c0046018007601010411840f0745501002d1307841c0071654424000e11030a8030040020a00c120300c04440d0071100c84204805006000355a503400500062080c418400400c10f0050900b2001000307056414036007203018030045006110850640342240890104000314030160b000300c040d03030b1080407a03000131030600a419008070307020b0344c03212052a0800002c000c00c620250381800b600c2c98040c000d0000f0444120021500070031544000c00c3c11911001207014404a2030380701c1e100009040c8586000642c8021039070019003002c006074010340c00c64100007031444400e2019001800c48500315101d1800541d1a00140b00949801500b11903002c0074840d81 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 85584155 1250 85582905 85582921
    0x1b060901022515022b0f03021308010507020d0909061203051c020d02071707031e1e0806010807080408040b0a0201060909030203031009060803071e0b150a0803030906 73
    0x100155440e221103400501980c0300284885012000305680060b0003161642c43c10306a404506400002c6198204040b20401d401c0102034100518006c02010703000100c0300428031032008800301a140c000001c1005e8142020080c0d500d100c400c1c0d4035804165038407000605182180700c0c030000c0381c0d1203a0b60007000b2040390382c04892230707801300055200030030011740180300198461000d401007101407580147d071100c1e40d00707041004001c3c079107101d681c4103400c2008200203503000d1b080a42001c0343d0034a10002c804c000c00117443c2c10315000c05508030102c0b900160784c2c02c0d42d40807405d24080d40b001e88a060b2207031600041250441c0045801601400c0e041104000b03450001000300034504103407000003a0b00d41c503062100b00783c803d0070109500683c40030040c070102d4040410b0b5000100196501003080b5450301410b20785a004034100030b08a44500748090f11a58030703071a0000d1001d03038001001c0d8000e24119007003d400340641040c03079001d0704203240701107210345000089902400800008154540d54001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 85585405 1250 85584155 85584193
    0x30605070507140f120c0d0302070c091802100c02010e1201111201080105090303040507120602070213050709120b130503070f08040501020d1e0e060c07081b06090102 73
    0x45400c041000801101010a400054400b01042c29401916001d0796800a107898107140c4210701441d07103020400b189540380300043d00c80207c0e45608015854003203030300789600100c1d00c0b640007a20071401d240c218042011502d0b40002c40d141f00f110500502080000100c17008030151000901081454200e48040d00d0035202c0f41c2d07441e00c940c1d800800c200d1800c081000098018000a0001c0d201143c01844509403c0c0109603008107041c0045007503241907213406584d5001ca10138089030349000300c1400305128288e01110080b940180084003805a030680c03040042400300c0c1d000380096800d0f880801c8008164111f6007544c1e0f00000b0b620101e445400c0000c4030200c1c81102140c4034807080100c50001103c800098031071038010100a911149414000f900342800c81c202c04041080134800040c150f681d4050840030921546800840140c3d11008140c1d5403281030302c1c284040c0309404001600a400044078104060300b9044584032802d4881804114003e512200b40540c00035600040c5401c2d20714 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 85586655 1250 85585405 85585411
    0xd090602160302010509010e0111040e151e040507021212100e040506040605070804120e030c040f0905121303021e06030a0501061b0c050607050c0a0b22060207030605 73
    0x21000515121000390754166020400c0d5003200035035150400c10810703a1083c419045401250b800a00501d80981c50b13075115403049025218803c2c00380e40202d00e074001009101c172512500540792032401c40c04d00080e40d0054070000c8400f485541002c000520b00b40c808100a44905070001c4d1580c1815410301072100560700041c80301b4041c41a0340c8000500c0202c05500138020b03409030303000d0009030806062071800c0d21001002c407414440c40c201400006124420f100e0780e140070134039084115004602c000703424085440100c1d0f500c103092681601070702d02c1640c41000e80074401c400b19811001001e990800c5801040e03560520500a254100050f0038000c04110909401c142d65062001e208000510b180c1c00903113001d40c1c1c00d60307190300602541741c10205030008a4104103030300204454580d01d590810003c0e028040c0901d4022400ca0704004040200500c01600140b0001c81951180d80014090b0004075141d03990145501450171400d0ba98400704090322555030113000e101e400e5803a804040c04003d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 85587905 1250 85586655 85586663
    0x10c03050d050406020403120201060501050f090f0d0501021c060b0d111b011a040b0f0f01020709090501050f070c050a02010c0c1211041b0c0f020111030301060503060a060903080d09 80
    0x1002412a070000380d2040d584034600c81c020050f260f40c11800c0c0840d189003958958019a0b00d481401d01c4960780000580ea548425010391b036a5541944000c01c110300d40d00c0403080e8100e403620b01c0007010000190050308404041c00090000c1c040c0d54062030056030881d1245005040d0100a81401132180b50405c403143c42e50404206e03e080c0381130041c50000050403403084480c0c1d54450a10b203051240150350780c45058115010303c54003c44d20009003002020380c0342e8901c01c80c0c0c2e0240b100c000364003d020110080100132010002104182400d5001e000b04507a2180c4d045110000140143d02a02059030480c0c1c210b00200104d00c417950040d110221103040a840c1200c10b40c2d40028003004910750343c480d943c414104102800141004d01c416144941c40d00000c425001842c075001300c1e1301491684609070000a1081d1030365884c0016a0104c4440ba080006400008004903500340c100d00154080d07042541c0d01180f40d039603040100ca607100305000085c800c400c00c0003030420b52405d070f800100b038040c0a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 85589155 1250 85587905 85587907
    0xd08070507081207060b01031e09141504050c030f06041104020d020703110601060e0f010804020f03060403090f15080f19020c01060302010801050405070824030a231b010c0305 77
    0xc40d0001c42c80c10b00ba059410540783d40c0000c0d007a04002c11405100c1600c24203080070700200303055a10346822898014400c841255550380e1600600109401c038641c20704d03500055501501482501c0149802c080b50190b41d2880b80c03203101d02c1241000909000840e14020181820752295650000203c02204990394010340a01030615080c8080c4014000d031442601c5003080c032a40c001300541009016030050060010461540c040c80d102c20f0038102c2d42c8202441c0c03034000380c2e40314800560306054140540d5094402c0e0f2040200305030f00086400d050ba0446c48c10f20300b80983c4c520094201107840d02003070000582d100b0201e5401c01a1a060741c0e0001510703401000082244440c007401c0341c20101c0e20001d1691242401c205558000c010340e0f02401c0c0c295400d1000e4900300001030408030015200407040c0a00c011005e1021a810841030208240102074402000c010706200600300e0610130031442c903c1049280a50412001038001d29032070340c0b05070000c20580c1d180015114020006000c0e414450 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 85590405 1250 85589155 85589159
    0xa08090c030d030e01050906042001050409021b070b0a050a0c030e0411041404060302030c06030c040e0f0a0c0302120402060a050705031303170c1f060b03070e010e0406050d08070507 80
    0x2030144002c0350305101d039a8001460300c80e82e8a405003075440191142d24079821200c148004604242e03c050041c200344d14034050b000510100407200ca01c02d80d4003140066101240007910000c001c0000d40c1c6461005040b01d281645480c8014050701c5a1548400429810003440c02014000d401e0300c040315020341094500c0c0161180410140c409e0f2400030304c5104800501489074060750512181908400c0e82d0805c00f09007980e01007650343e03c0903c04e4621031900400090501e440d00340440f000b07460019295452403d00e1440c250a4070b40c155641880c042c24682403810081c0b19100341c1c0d015041424030208680ca49400b48040c030360040d400841044810825000071600401c001d0900d84000042446100c1c598109050521028001440100b10401840102d6580000c5040c8848d204003200a0400c40d0000420010001c540c06000511008000c1061290700180115540d20003a2207a10350208074404001c11101c00c0d01509601c4a01c0342004000315002c0707800340540e5842001180e2001e5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 85591655 1250 85590405 85590409
    0xf0f050f0616060b01080915010e10050a060302121e06040905011d0a0b010501020a0c06030203091603060b0906030d020709050402060c070e0420130903030912030b091b0a08090c 78
    0x100b0203140680345980c0700d051500d8107513809004194401140c4024251244031039080001130007061280d409480078030404194254029400c8100400c03000f0013074001c0c565242d1014010750413141c185d4101034011070010300d500040071130404009811540030300c0c103585ca210400c0014400c00a0130b480c550350361007010070f20f80c801403145010245998020091000145407642d03440134143c02041c11504648070360b6001400725506141699158100580c80b9903c0c1070780c2c40c1c500021184e00f1541c214084c01c1c00001d20003960302c207140d1000d050325600d0096980405060b03644103a007084a0043c1c0c00b005080000d9240d950209400034801411240340440254026107058890740080c013450750f441007807104000a401c44043c00c185c00f500c040713220812480c00104011b14945940d021541c403a11002c00301440381d44000c0c60346174402501e20561442000080c0100386000f041401200994080744a1358509400c40c00b55011130240b480c40e001c2d2082d011122404098141d1038a881020b1503070f0030341c3d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 85592905 1250 85591655 85591687
    0xc12090b16020405011406030f0c0c0109060f0c0201200f07050d090806090105090d0503090f010c030605030f0c060403020f0307090204060c0b0f0f0f1509040c0501090f0f050f06 78
    0x814412107901180c07840d5401000b0032600c0603804900c01907031001103180b107030b21228156035000683c01d1400f0282c0d80d40c041040864850080c1300c40065281100000c20400300e41d1046e061b0310354600040001d12046001a4201c038500d07411203030491a8041021550250403004101c1402104903440c14200b40d651070303e184c24507020400020031001ca0341481602410030045900420050091106051080c8029102c0b16001c0d0408104440000002c030034010410140305c1d0294150020000c4500000000303004104c1800749900c64080d80c1003070000703490300041c41104800d0080c4618a03007803440e820485490312040d00103815009207000001c00540030b20180008001980700ca89030b016052408020f0075400034012001544220309100310301004089080d0301c60181054485151a00c0c5000c0002141802c0140e5000c81510f040004110444500c50308641c07081c0c90340441c0700e4075101e03908400081030040d17a02010701c4010402007480e08031003c044805001c0c022350302c1d0050f080740700101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 85594155 1250 85592905 85592917
    0x15020f0c01020a081b0f031b03041b050a030503090603061f020d030f0c02030319150f0306050c0a050a03020f120411120607051b07080d0c0606090203010302010c12090b 74
    0x1081c1d6000c20380510f0329402501061780005408810120324054041c01c0741a4000c1e0805d00c10000b4000c80091b04d070001f1582194007018607030b40140d44900d02480c0c0803070911503c4c0000c8a0101c41440300291904050240000303580e4000061404c0010210500500341c20003864290f020075001031704010034607660b821055081543d4060042d168071128090292a0036518040d0902d10b4510340d491055800b2042d41c0c1c1064100380c895a92000c0c04405002a100150350b127030f85507016003800500152545401d5044912555003444a0f5544041c2c07565240174500e03588012030001c102030104039100c0c2d4010103e01092400c810306007404070032140d240d100100e60803110f41c2c0e8820710041403894071859141c1680003c41c0204900e1514000080150048145030141c10ba52404a80070381001405481c0103000c83c4002c5458040c8190f90003002e4690540d01558810b00c2c2440100d00011076000b2281a2a0183c54006008a290340e449103030a02c891a040100450a00040b40c4400f0110003000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 85595405 1250 85594155 85594177
    0x618040308070e0f090601030203190c0207050f03031201030206030c070b01090e0115030c06031802060a210606050406050a1b2307030215071712010f060807020a15020f 74
    0x50318038019501811440c1d2080b000e43c401e020b016203106040d03072605c04465002c5003c0c41c015840b501d950240c1c2c0040711b90721070490400d40c1400020710116500084000071141d00711f8000150480c440d0a0503280d00ca08090200d0552030440140b015040c620001d5410440030800e03940303000001d4072683d450b0b04c400c0c0c00c0603140070703151243e0715418031003400742005002d21450070240c03030b500e1651076640284640c031840d8141074840c49501000a08c41a8414035140c02420321030b9941d41140300100307041703140381c14003024124070300001414810b01d20a0805481c81501d138246850308004058801d90040005071003045002c0d400d0303803550040078042c220b28620038401654035000d10740c440c01e46410000c94110147d44030910400c0585c1c1c1d1030365130910000a04015550b500c0c90740c00c0c0340710310440c20381c6082590306000907800004c410446030395040300c0c0392400098045803120030880b0551001d03101100140c2c4504502000b1408580050bc6020003140c801407401078007a1042c265500011f03e985 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 85596655 1250 85595405 85595417
    0x90207300e031506100203040801090c030201090806040b0a021303021e0406270c11160f05040507020d030f061d0405010e030a120c05040b0c0a02030c101706180403 72
    0xc0d404a07086034010607161400c501800c86074000050686a00100500c074500c5450060b1020004034028000c503405061808020b0000108604004059401d1480200d0005011090020781080c010078064025640807800e19080e85440c000600650480a204080100903550020050366106440e400c8d075664007003d4a0101d035008100001c4032002c1d031200c03400d0b9012901d20900c41c00743d80204100d044500c00c00280900010604448040052105500c0f5108006900c2c80c90070140030f184007151042e90000284580341e40c140800d458040c2d4000c0050b81c00050403401080c0641c011000c410504d11000511302c4d901e0b1014000600c1d81d00164410000443c00d00c8207104080c09918611078070500110714010703040d5801018404000d00f0b01c2e00700342d40d88050840f140c0c45201144c00404400c1e070b03543e854803010750302aa140c90803107400728030900c2400840b06a0f81000383c00d001e00c8180e80e88900221011840c034441036800c00600e002c1d40010004508000ca14035000702d60b010750301075a250b07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 85597905 1250 85596655 85596743
    0xc0f11011b050619021e03090106090501080609010c0c02010e010c05010b031015150903120e03030d06090b1516060609020f0306030613170904090c0b181801090207 72
    0x591009440140e0700c280081c01000046401c0400355021600200d107400b071b02e0b41d02e41d01d80d04914014140f903080300c003e1600380700000500241c00981a030088000f00001c01c181090b5403010b0301c0d49050385100034080b03002020300080540c0200c0a42c10324501400000c41c01020b2080000e080085400b80040015a2a2512a2040301030b803500006040d00010006004090360b0002c0c1101c0c4035480001d207040380c84c1500100c22031007885452040a40501280d440d0050608810041d00c1a400b030880100d140084021540ca001c0800c40300449200ca181e6141c000c46400c034108910b1724013002d4840c01d45980c0e000826013624401001000302000b80582c41c0e040410405041c080082d0170000484400b0715158003081d400745402d0040140d283e421035480d502040800e0240510410241020500b0400001c07003400060040000d010000c0400c1c2c80580904100a003251044241d8a0312800c44d83c014003884055600400701319006d5010310301705c140a5040e482c41c107403080d054644021100541 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 85599155 1250 85597905 85597921
    0x11060a1505060310141f1239030209030709050406150e0f13020904060606030e0703050307020603060402070b130528030e13020f0c0d0c0f11011b0506 66
    0x40d02000c0e107000c450701883e606000d80d40f194414414010302e14019103c400020050b0b0300c280d14008061a50014880464443c42c40502010300c00f04558900d141030100ca41d08070000c1c802012400401c100f00000004800340e400c2c5c00b03552250089000b499400c0280c5805c50f901041514010714a412001c6403902d850f144c0501074441041b1000b1106107100070502003a10400c00d1300768042c10044004440d540c0d00c61076040b0307071210b50302c3c0650007000010a01081c00003035000b09050321650748082c0b05201b60039520036501c042500c0040c080d50030900400005282c040011908108000c10241c00c01131140c4607031031105416245012070440ba20700500c100041030007170340200c1540190805005189403120304980d241c2c840000c007040b114800f1015140c2d5a40340b800c20042c110441103440c3c0e14400c0400034136600a007000030440c8240041c1064030307440341c0c26079140c0590059102c081c1c48031a5840324200342e80001e1250610884400c007c0300011480010258980580000d1189041c8199 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 85600405 1250 85599155 85599191
    0x70f03060b010302030c0403030e13050c0d0b030d022d060c1206090f06041508030d020a18081e0111070f110103090209060d0f0203150601020d02010c1b0311060a 71
    0xd0202e05140c0103104100070004c800d025241202d4160030314a81d80c084580c0000c204081035954110f20500c2d180612480984501c050460480e5028041080b100b10350209981c8003c40d18200c4016441109a22680c9441502140c024403e2030b00406147e840150242c0c20801c044070320b80801d1030042001c0b40102011018680c10050941d06104d0700d0500300d0440030718170002094140150345548400402040a035803140081014100b600c0c1ca03080d048100c03001961002c0381ca00005103410480030303111201064410100c0e091080242a04001000c01340f074661008528400d03e556901d080c0c2c0d00d211444030080c0700d501e20600e01d04990f09402d14005000b040c0f040501c904040c50110000d00682341c80340055080b00007200c0000845d0464a0a4201000002c9000390180103c000030b0628008054031030740590000d03000d80d00c1d04410307244120b080b038000020a0000981c034900004c4402041c1c80c2543c200b81c040d24003080000c4410031143d207401400d841c200c0606a4400100202990581c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 85601655 1250 85600405 85600421
    0x412030804030f0306050f22050f0109060b0906070605092113090c0903110a050d080904060510020604020f060d020a0905040f0e0705060a09050a030b150402160b04050f070f0306 78
    0x10a0400c245806c0002040d06240d507001005e02a245110003030180c156004800000c50101d1141032101d450301d03941c4820410800c0c4501b01440d0b062641c041030040da00d80540c1c000e0003000d040103040142d50749440020b48400340800b50381c1d01900c5000c80319103071021004040f8041510713086603228620300051140400d00d0b0b002008a42c90241e403681d1a56100a6800449400130510703980c1d40c0c90b80001a5010b221540030030741c40325219a4003010081c2070400751000c07035001c03102000010340c0c0d1018884030f100b5454251005800882c00180140b42504c0d5030280f280000e0302c44c3d41803150f00011072049034440e11029001c2564044d04100c0c91805026828116400aa09200b1241c0541060340e0315001800340604c102c034042103076080b040c483e03030080c0010000242005025540da00701108024003d55116101d502c03d40011305482c2820f0084400c1b10241e4440c0c08404001a110440101c0c0c000d4401c640e075004c0c40040340c2001e002000440f000d868030903ca040d4851451a104044600c58 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 85602905 1250 85601655 85601657
    0xa0605120105010c03020307020103050403030b0a06020a0204050708070c140a2004050903090607080306041b09090b04050103170a1205160e040606020606060d02040e04062f0f09060412030804030f 86
    0x200080c03000017580071058802442c9c1c20300b0041182e03201c52500b640038090040400d03401c080180c000241e595800904078203000e001703071010001a1120030086800703900c2103c0d4900403134a0746503500c0001c1c103802c113403041100024090310100060396071840d00a040c0f40100e0076080c038800300121914941481010b0704410b4204c0107616280c0060049800e501a0920107004c2d10008030004910380c8458200c1c0b01030508006c3d000c0c1c00c990802c80c001d800382e403440c010904800e150614004090806200e000c2c16290070504500700c1102c400c0c019105940628040e2040012110880c040d0b050b040c0241ca0080c808401100002180d00800038081c00241d0540c91040c0d0078401e0810903a82c011a00d0f540002017901c401d035642c07040c0700080010344543c0e400940c80c1d8140078200411b12400e40d00807900102210352003140c120301e5000450a444101a03034907040d000c00c002c10500e601c0071100601151401403d41410203654492a03c1d0348d0105072400d8010070002c2082000b055800304c124083c40c101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 85604155 1250 85602905 85602917
    0xc05090609071d03010b090f0709080c0310020a21020a030c05070c170f16050f040b0a0603050703090c0b0c0111042403090506100f080d051213020a060512010501 71
    0x7012034010f107103a440c58010034443e2401088001141c80c00c0d00074042c00c1d0000743c02d0b01d401d030500104410060000700c03020000100206404219880042445640180700070010010325003542039501c001c0d4400c1421400b8400340c1820403826250300010011040005c9000588460746100044d0555860004c01d0040040411612000410001c26035042d60340304444c0300020b940b80125945400300614141000f07220b141101401807001c8084102950303401c0ea001c5d8070f12a6003805101c242c0c1e01c0d5140c0140d00003000c0d88180803540c801d5229a40c020b0702c614010031210f080e0703100d5911040454000320307200c180001d500c030b8002c18240200310f10030300d0038000246445d103000d4410001000107440007840d44094011014090310940200c1f0f0320503046801c0d0381c001e05000d860752000414a200342010b208000c440011180701c04210035030710f030711a038545c83c2c41c04010901d66203043d80010300440c20340354100740400158031103e81c180c000d0130135a04d41d19a28a100542d621171044142e20541c10480 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 85605405 1250 85604155 85604161
    0x40609061803080a020f070b04060504121b0b07140c07030605060a0f090e01090b01061e050f1c150602060f0a0513080d0603060c09061709061b04080303040c05090609 73
    0x1030b03c01e40c00c65100380020340058032541000001c0415102d0754401908011156050106012144d031001c0d000300d06c2407441644a00e446403080d1251541000001c3d4a062560385800110b41c00550140c1e1205242c030b40503512401c41c05950380030303400c40444a03900d03030f000310801d0082114030f224081d0407031001c482d841080e524200c008042c401d09c031300861541390b0f103a04440d03030a50001d405c54007070302e9801070b4442900c2d80c482800500d0b004220f49501c51110612000c031103400c0c025012034210000e00c808440c90b100c044504111919107900400400c40e950711407011054504103002d001900c05136015003441d05250b0001d8810b25409404000903d1030103041c1701032203c09040114881da840180a500c401725544609e00510441e40050300c01340c1000b8914a00c0d40e8000f0f41c5609540c0d171521007010300d070344140d01d0480d1a4022940c00701a50712010100f0004000c81014021045002d40e03003510303241c0c5520301c032030440d00141c40032138034001502000e210718606001001d6111800352141c41d03540c9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 85606655 1250 85605405 85605407
    0x40203030915070f0609030f080903090d020102070e01331b02010302120106120f05040b130212030c070f080615091929030d05090105030a0b0405040609061803 70
    0x80306040703000e40716065480e0342c0660300c1c1001041c2c81d0300302d400038140d0410444908011015200400c4100d00103050481507281d0076004498460084e50410000c60038200303418103000c61102d000600fa41940304030314001907c004003001b0782d4040e044000c0501c400410300007146180040600d00c0c3e4021a940c40e1011400c1580800010400308002640c2d0b044000d403800168000d100e000341c000c040541c2e01001051058100201c4004000d01c9901007001c54490700040d800c07200281c0300240321403582c81c00315100074090f4240394122130004290807500c9852042e481e0cd140d2000c0a21005c0d900f08880402000d1814400c8200401e005805400245414843c005421010154580c865605100803401d80140450084d0702e50022910410540800000c031041d56000080107107030b0340c44060358404003400c001c40c012801e0842038440c2d50a01844800540c0c8641005042c0c10600341d503808185000d507114003030301d40154001c10002610000c18182282900c034a0417409501800304600a4002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 85607905 1250 85606655 85606657
    0x10e03120703020f04120308162a030216080a17040e0601110c0414040b10180507050d110306030706050c0a060207020406080105010f140907050a0804140709060306110304020303 78
    0x20030714610300140d131164030040502e140d0045800207520126050003400070142c100f04414005e240c2c2c54607140d030b50400500100c2c1c0000f84024860300c070111051307250848040392a001d040803442401525003108201e82514040341003a4007a034101d42c000a400b00911010601b07680d0220624548149085d050105108036040b01900c021704024504000c142012400e100412034030000070420f102c10000b80501048442d01543c081d29443c00032400300c0c4070b5031800d1400a04a4036840369111a4241081c0c1e079100901c0014030030420311908101040e101c05c2e10b4841c1070340c01811100343c0c94603030511000f81490a00c15400c40c2c41031103410412a921507100040040c125a0300031405617565100384007240c00f505803a030101040d50300344000481c569030b42249410580e0100c64500015015039070401142d19420781c3c880000c100c08020f030500c8240700700700d4a90710501a45d1000340303101800150034584807081c1d12014030290741300310030310030440240140e40003d0302003440d0b1802d605281c1c0020303850b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 85609155 1250 85607905 85607911
    0x304140d0e0d020a0e09030a0801120203070e07110601060915030b0109051009091d16030c05011b0c0b1309142701021c0b03030307090902090604170109020102010e0312 74
    0x2280c000400b1010440d90341100144c040c06410110729200c0c00e00740c1d006540c1e60803121131780700401d403c0e0002084421101d0000d680c400c0d0000c00501199190440d0b500041d80040e181104102c81d07484035600440040000c0760090040b580c403080c40034545042c818200c450402c9034004c06040c0780000c00319a0f0b01103160350565400300c0c3d07411403203680b1103820794007511641d0140030340d5410085c0c0300001d101c50724043e80b5038103080020b030f400c0107400442204124185e030000400e2525044420310940d481401da00e00207103040d500d0754004146680340c0c9480c000e41e65002081007003000170040055403503d40710000030200700e001032140c03070f11400070040f071010010103444403100c0c2103c41c0c9140d07407059080b201c40c604445000b10350342c0919540b1407010315511490120407030700b45018a100c40c280041100c0c4108002d40e40c001041e800c281410010390f0080b9403840e4031010130310020a0703040c003440034060301c044880000600491386200180c2900d8041003201d685402c140404201f08004005841c1c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 85610405 1250 85609155 85609159
    0x2030f010608090a050708010b0307080a080f030402010c020409060c09080d170702030415120606080603100b01020127021203030402150901031803080f0105030714150403060e030304140d0e 83
    0x141e66480e8080f00b0b00d89900d082e000b826600c102c060004004c10194006054000280c0c140c500075a00e4034101070340c410780c8610040c003610f01000070241c400018005103411510500d42407144c401d143d00050f06a80480c401621050f07561401d0688494201da480d10080c0404000340c8648076880c180a400c048012010008400d481c40000350a00d2003070007100d0182080080c60f01600841403801401c0c11001c0311032208e01403500740042000d500174040c580c441c074001001005101c01c0d0a00e611f018286204040c1d0540d074071246a000403880305c0c85003007440440141804c1651580f40104480c03004151006980e9800c20400e120268841000f07541c000c035640b00b00c0e04c2d510b040110040780101081052403030a00c0220003034100301039020b0607190007000640224082c03662940c0030943c0307418540c4a01c1800c140444103116003814050204d50908241d00c002c00e0429503642c850303400355500d1000c482990740000040000300030b11101c401074440008001007600d402c1e9520f0150103041e030385088e54 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 85611511 1106 85610405 85610417
    0x30e0102150106111e0a0606090902010f051602061801170705030612102406030b06070212010b0d110109080c1003020a1b0302030403110402030f0106 66
    0x341030080d89411416003640b8001c1c080e6030070144186000c4d2a8010348103814a40c4028034085007840c2940e41c06480700d81c901d440e00b003044400316000064060b18003400e50b80586d0380b280c2007034003502c00350030001d54aa2008101143d0200307003020080d0300280020b005810413843c01030020720b20703600b0788800410b802d07071038844080100211240700000c1c500740005000e5103000d05c040350741c03071006ca400d80e000200d18804a1050f50005040c185520111800c1903c03d0704207546503000500b8540f40c100a50b02841b80011004d1140d880c010384a1070741d8441100e85040300398091600100d0041656a800005103400301070031508410341404038000d540d0002e0720300c0003c0341034801c0540003003d28441100301f01087e070003034010450036002c1022550480240303c62213408280780602940042d0707100c61444c9841030340300c1006a900d50045006005000300100300101c1c007810b450941c1004 = true := by decide +kernel

theorem cover : BRFrame.Cov 85431655 85611511 := by
  have h0 := BRFrame.cov_init 85431655
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85431655 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 85431655 ≤ n) (h2 : n < 85611511) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
