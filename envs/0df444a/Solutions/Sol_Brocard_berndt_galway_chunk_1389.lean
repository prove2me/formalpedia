-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1389
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:44:00.903499+00:00
-- url     : https://prove2.me/submissions/2701190b-e866-497e-bc79-48e51672582d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 249640287 ≤ n < 249820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 249641537 1250 249640287 249640319
    0x100b0307050f2118072420031b070f030303050619120303060501031e0506150309070806090a050a0f03050405030a0308010302041107020d02060304061d0102070201171e0c0f0d02180f011413 83
    0x20800940d06d6640406d10074164809c14403004169070300c010402c20556270203580060942e80c3c54039000c80d5944900e80030807002031040ca0803c24401303086001083c9601903846490b18503010380d805020442d582c000640850305002e000022120800019040d90f60141d0131150304000060003c034200c000c00c5820440581060360348080d240c100600c108180e2400b00103294000007100054000101e040e56015070304e621b01c410080850780f060141c181414002c5054400070700000d810381d2008036546c50014490760302400102e20031480e21a11700c0699905600341d8103a554054000351005010340c00700025900000c1c41110141e85a0000341c12007035405801200345428139001503124105071002400311042d06204900c0260002c0c1081060f04400d482c0d091a50510307581c601241d00d40c880c00241d10b22840710f4001d42c021340051b0502c12003406074001d01c0c48943c50030001c103121401170f04000f82480d26407101d0340019a00d46044100c4050300c0300400c50505201c544040c0e85545800603a414096 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 249642787 1250 249641537 249641597
    0x5030d050306030f070b0a080a09060c03050a052a070f020a03261207030f060e1504060e06010c23011a0108100b0307050f21180724 58
    0x4040107000860034208244880340c132629001e015821308001003000d4500071140c05034100080b08000c111071030041c2d4009420107400000500102250900186c0035100a903421000c0e60725000c0080c00c1942c10a110340a40808600d600415000090a034501c50700401d00c1982c0703507070508648100581c0c0e0f50402c10000c52090312280510402c581c003441951400004414800100b0008a400c0c006280c0320980d205041e42800110700ca06c0c580c2900081040303400076200c0e00c2140c07003403001c000c1c1c18507055000c601c800c54060040b180c07035208600d440c1e842903030020302040b50100703868000746100410303008001d80890362202d0700c00750a00c2d1031300b0350300c92100c10344084451706855206941e01510480d0700000101c040318109150511107010340c0300003024001004008150920036400318030407038511800e420b140e95402c0900e010142042d02045c0c403a0540d4002c150200c0d1340039503020840d441140e464213680c1200d010b0840c040030206514058000800c20081c05140a9001b0780c1404103070494 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 249644037 1250 249642787 249642797
    0x312091104230a0c0f1b0516080106060504240c17090108060916051e0d0b0307080a08030705030c0403060f0507020d03140c0d1407050d0507050a0c110a05030d 70
    0x540301e905505804030103080c040c219130810b4082c00364242c2081480002400d07601d0010219182820010a0b000b03140900402034060b00382203510714280a40d180b4240c0e00c0b41c40003000829650b41094846209074407410309284510164403240c00c03000d0400600741101818843e552a0403030380d072103a8104201084007014040801da902d00c951384244015030044040c0e03214003032410321240a08030b10740c1c0f101c0f2940811078005103c8a100001a0381c8540c5400c02403005074440b00da070410b1001038110b00540038000c1c03040b040c1c00258000b00050880151b504410381c2c0d80303551a800412903180d8001007005104010801001002480c036108850b065604c50100140c1801c01080090900044d2020b440406080c480b44418128000d0180c40c4c1240d007880b0181c0c3da03500c80b03001e094090040080e58454040c03802040151440e040002070000b81d0481c0d104101d181c1c0c90100940f2140540035480d000500c0d404036081c000740300502c000415000c01403501410030b66490001e80f4041c1102802c0303000407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 249645287 1250 249644037 249644081
    0x7050a0b161506050a2c190e0f010e06090c041e240b070309082413020a060903050f1b010f020c090c18030a020f060d06050a09270312091104 62
    0x700300c1c1c2d010720350003060046d0000f1801c00500d034400342140c0c90580344031243d46241c036a02c21030041260b4440035104900a00580c1c00e900503003a1103150072190034189000b036141c1c9442c1490144a50480d00002050740f0b04080e075603c40c0803004201c08540d2194001d003002c61801d0041c7c5000711507000340141d440070b5035295140d1500800d2240581d10442443e4014951000c804905602d0f0490502a8400e640201e680c1c500c4100d8401b600850040e400010f2100d0210b02c49521180c00c03000c0d240540100c0c0d00b21079134078442d00d41e60211003404a5038440c10304030f000110b40c46045154052042403040311307654106c00b00001e0008000f5100420002e0000030131281024034901800189501240039022000041d00401c128698200c00c0c18854500001c00c5025030303045901c0800500000707003240c070348103031206100002002c84118541881054940b0b00c0038030101c1c03241c03c01c0103a9040c3d0f2048000991007441c0c90290003030180848400040c001c41d0411a11507101c0e0210b85012902511059 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 249646537 1250 249645287 249645329
    0x1809050a050a0c1e0315030b0a27030207050105070302011e0f140907090506180705070c140a150504080a0f0201030c0206040b0c0a0302070203030c07050a0b161506050a 74
    0x21900d00c078054007030240c01e81130b001d0303046070904080c1408070003810003140c42d28001c007920201040304e40000380043c1c4c242c01880181001c0c1d0303100d100c0030823400e10081d8020440541a880c981940f010080050780107020901007035118001400b6014070a00000c15607000301c491026804102d800540900c81d80c506c08610032003598002c80030020610b404d00103160502407200c42e201d038034074003c4c04580c07910360010803030607141d5601c082d040303880d460070503100790801d00b20080190f40300741703015280c16006a8005c54a4580802c4210161000a200010b868500007115846070101c840c01010310205010008940c20700740000c960f030034450304102d40c680c012440094115005410b081d806c5502600802000070ac0c4a03082a80080410b41c58540301d400d429003c070064820070000a4141c0008140c103e20018001045400d54104a50905200d07899a1b01c91520f401121742034001c0001c42c184c10804aa00007051007080d000e410000b04400745c440d004074444006951185610341040307a508009 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 249647787 1250 249646537 249646541
    0xb091e0606120f0403050c06040b04020a050a0e0601032a021006061b030c05160e060306161403060a0e010303050319090804050f0a03141615050a1809050a050a 70
    0x202400455903641810018a00190a8900244480d480103540f40218090500403800d69643d041040708030707142407030f00349000081c10006440481c01140403c1e00490300d4a090300a5401340c03400d002039002140c0e150303801100038019080401a2011603c1c4403110a80d680e21450201e81e400303900106002003a03805160110f418580c0420100800341c0b02d0514915040040d850718035400d441d0911004480d0b050407403c0c100009140c03a698108040009034074810401240e02c2418201d05951499507083d1001c030700c0c800b04d82c2e0698000b502d00c00390100424820809140c02c00c10107841c003046c403074545c84c2c0501b803510b00ba001517000c508040b00300400c8600a14000d03240420410060242501ea070340d41b5150f5000743d0040074030070068110800b40030f0315101d01d480300071504080e10348661110344c1903080d1107802c0281640380e01880b51101041c52030704002c09840c2c1249a540c0c461526a07007100450348080340e0751040040ca540114002101c05450142074002c0c1c489034400516401c003140c0b2801 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 249649037 1250 249647787 249647791
    0xe04020c010605090609012601020d060909030e040b060d110c060a0e071d01090207050f010504061506030204050a0902030402010912200102150a0c0e0418020f0603090307030c060b091e 81
    0x4422240c1b04014030806841e107210440042d001845a0b00444441d03030500d0180c001d981e600fa282501c3e001001500b0143c41c3c00c105c110b140262510721110748003006220039074020400d66038101204004502402c03590740d102168088560307032110300302013007058100d0230024255802402161182180f0809080c10f01c00030b401032901c002800d1032030781d0340801f18140020500c149000c0a5000c90341400f48031042c0282909080c8a1000300102e19203840c000e4001c010901004a00500c1004046400d038003074421201621801042d4070142c51a00b00d02001a6200410032410010460000a0303c010320f14545000c1c00d1242e11100500400e01808010301a21126524110342c861001140803416401520344c000c45146408150007040c40c0c001e5031040d085c0341c64141c1262800c8010f000300d1000d0b100c580c0c50b85208450340c2d0a003403900010000640016035025000350030410603140002c1c01000c1030800a441180c0200d840480c41d07000030b001c030b0310455170b08000b4003810708020b41c12100540071907 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 249650287 1250 249649037 249649039
    0x6051303090f0f0302060d0e010c020f011a0a05060a020705130209031204050108070c050f0a051507080c0f1e0f031501050a170915071e0c120804030e04020c0106050906 74
    0x764516211460b500394074079200c06805084001147c014406564000700c0d0003160200082c81000c0c003040b0300030350f90b01501603803004035413070f003082a070051080d2000f2041400c0c0080140411b5820b1208002035503201c1403032503056220351400059540c950868410410404030001616003001600b4503007041105c00842c20f40f048200b00500250307821441c4035811282c03602d0160a81d0525140c03040c50980200c00b1421103214046083c810030100140104030085d410b00d05100036116010300b0b49200100b0360b049039481d5010b1001c9002c2604403009404210541600f840031854009841b00f032580c00382580f408144000403c001d1108210800346014810030f02c1c0080ca0140b0810707008004481d2500e1442070502c1c49008181d440c18100500003040c503000b2031206580c00c0c0160b0241100c010006100f1480c012a15a4040a409a45004e00d10340d00705010460000340d1807012102088010421030502c242e40b030b4600c4d038079111480640448124032000107885403c0908010301401c0003000d41e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 249651537 1250 249650287 249650309
    0xc031006020718020d0b060f0903010b1c15140c0d051014040b011224080307051c02030706060308250503070b060d140c09090d09050f0402070605130309 67
    0x420010081080c1c0500c40c21040342c00580f1048111181009401c0c05801b1a50100000c20000040260000106542c100480c003c0007100100400c1c0701c090594131294000180c5c40c50f18840105402c00c601d00a60a404000061107070201c0d002841000c1d000c0e1608480380e100032800d00341301d030a1441b030f00f5040f0301115400c01d003092a081007843c0c401e403d098640e00807521000e400c69146d028883c05048007205400c184401c600542c1c2d0722030b40c2c80881c0d41d5484444c0401c6000034000700003008039041c1741d03000305c081c2a102546102004000c028840d6070400c43c4010031641012031568810340703010718400c800c000d985800d26540400c4120b0301e0089014900b109034400d030001900041200c0c4119070103650080655900000540203150540010309841e0802c0c0b410300c91003a02055825644008407400941d40d02e40d401c54556814a81d14442d020032a00031092140e49001c040640420b100180058038100c156034845060320415600025440102104541090342110807000039040e05007117 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 249652787 1250 249651537 249651539
    0x5090705091e060903100504120c050d05070f08160605071107050f03011e020a14070f0332040f05010201020a1b060207021c03020606010e2103120c0310060207 70
    0x3480c00e5102e18982c540c0030010302088074261039250a03524111002001d40391071005001414002d024110b600b141c44000704c1c003003d84028054000701624940120040c60030f03c0340b1213415074a6030700c541025694403624181020001d14400000c008146000764829a010074519090065440140242050100d079921210714404009108000c0759000c959004c0000c9003480401d004042c0005081c0400704001e52005107490707107800402401009039905298010001101019806898030080203580301c50100d0700800e20507021146098142e102e00701c1c0111480761315002d601003c1032280c20092011504010a0307984c2120740000b4503084c00254038240c2400001400020070030595030815140440700c600344245607050710a0154042e066190010445503800384040303000100701c0051040d50b000581d154407a0f010000c580001a01c2204056000e00004a00741899000707a507a41c4428050012224144a40329008407000440c450b43d84c1007000040c2013209082d041a425503010b080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 249654037 1250 249652787 249652789
    0x20c01030c0e01180b0c071d0112020d050709050702070305060f010806010e07030e010c030e01050a1a120a02060403140f0703031b030c15150512031603021005100509070509 76
    0x603201202c082d003407034920180501d982c140c08a18449401010041c4008a030310010f0070000540c02090314020040314130a20324900302d031441e002003405200b0780c82c00b202a1003001800d00040c03208003036200361b0581d150076484000c0036048600454400c0c0040e4400c1c103040042c07200a001d00383e0000c0c10f081c0050401d40c100381740c1a5480b0418400c0114040142c03001a002c0749c420351140f10155514002403040c4100c0301d0008018200821554840d9482d01001c41d240c910507114412600f07551240c1c130f040000b000300c20031100c000400ca140c0128000c4220441c01030303407680f0090000d14850b00150359103440032143d051070031045030400743c0e0070303488050148040b0b5000702080004104801e00c9040070180c91030203d031031172003542e4000c0100c842c0c82c000d50480b00e115005074a22035030182c00a02900e5641c7c0401c040c1c41c2280c06580300540040103810a42403260006404640c080c1c0100c0345d0f08603401d441802194811100c24000c00c2e0081d400b4015850015241c507041652840e0603030a02e00024 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 249655287 1250 249654037 249654047
    0x304080708031810020a0314190b1c060e0d020d09123806060906070803060f032a0108040308070e28030512040e070804021306090c020c01030c 63
    0x500103000c1d07010100001d4000c40b00d0301410203014030b03140c003035501094801c900d8002030b400c421000307004241820a1004042400c68185104052444081b60036180a10f0741c3d00040101048058100140510600e44400d800c40c49900640c4610000209002040906070521492030b9030f590442d08903101c0f84030a04c1e84100344800340c58000c601c06440c51101d10302024446c444800886198040420b0f0b003950055500b4170810780c005290029078030f55102401c21690b880307841130f2554030240070700660b00880c4001e009180d11000103801c01690000ca84002031410304000c0c05203030400790380c80c8401100300d040e1011002c60030082c00c100801d802c2559020b030042d640280940f00308441c99248002990300e481c3e00c20001ca429980c152850300e4074004018909081d4081902c05200f2954401308100340a021903017200c441400b504101d4540b08001c403001d82000d04160307485007803074102c040903450328440e980c000c2c02c1416000400403a113590290030001003040e014103052030128000c9841c2d07000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 249656537 1250 249655287 249655297
    0x50301090c051204050609070632090a080607030c08041101030b01021c09080c060a090e0a0b040c0c0209090a0c090b0301020c0d020304030c15050a1b051501090b0402030408 76
    0x214001c51000300e2560110394601a80801d00c0c400c201e40003c0c40b050101c0030520341d018a00080a0300e0555440b0902540c060002c6025034109422181c800d5001d40e05a5400fa4142c9154900075480e002c00000041c07032440d400d0304081d82e150044018400401c1d014400c5070140d04090070308192a18050b140d2154440d0140f0600d8140354032200208456071003030101c400904080c00340c0321850f0074000c1e401080300186000c0c91446104401d61410b85c5d1800c0c2c0c065034501c01513603031405101810320020a000000282002011503102ca01c520103543e05d600400840141c184c0d00d24030501c040d40104070a041c005010424035400001c6000c01241015003014282c8051880c08954050242c011900a108000c1003284a02032060741040041d404002001224020641420090380320381c40344240400240da4140881d008101110034035004110b50305600d002c0540c1c0d808000c95640b5401d0a1540404084da180070000c0014064103045100d4880f110b00700750380440c110329040d035400301107100f5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 249657787 1250 249656537 249656549
    0x120601061e020a060b032406040c03090c0302040b03030f070506101401080403050306010504080a260310140604080f0607031503030212070204061205060f0f0405030d050a0b0301110c120406050301 86
    0x1c400054101c0c0c0c81c20403492400590200d154480300340044031a47c40c074171050302c00301d109504108050100074800c0c010604920f400011401400385560308010041200021594040c04140600c5880061402c06041c00a0040c00500011310f40b5404281d6446802e8202d40110b0b49207500700d00c1240d074090001544aa85410300175540d8460000503640c03401aa480362446100d24941c120800800001d0160000011700e4080b21400c1e800005407120301048034180e401c803a01d4482080039210a40b0320402001c0060300041c40e0541706d0804504001c11300440743c64687c8113905010b0501d034180705482400c2010307015040c0030b50079a40c0094841c2d610100001c02808080f40183c1950749a910050003840c070f5904c80029121079140c4151a103804661150200c042140003d421117228032605100f241d004028526002081000100400003d0080307501305070744580d01101e9440911980b1010001e80caa20741c0c684194890003440c08240210508411344244010049140c210f07040d0390550342 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 249659037 1250 249657787 249657791
    0x8090303041103070f090b360c0706090605061908030a050906190c140a030e0904050109021203130b04060503010b0d0f060603051602060906060103150302120601061e020a06 76
    0xb0000002480e08032581c028240c08651781c2030000b2040f06580c02009500415505600001d5207024044100c070003e03500c21b00c02e80104400c07809150384082c0a994001c960040302424018580c503040c0c1155400d61084072140da5500902215203000048110800183c880680c04641090011a10783c0540300000c4203201000c0703552207182d61000191201030302c2d81d5036041c04141e00104014005041070b5030079103c0085504280c10800408507000260301d415485150044100c0028807400345030040c03043e2140d540e160501001651a01c48109481d12841c2c019610781100030320b4030030956055030112500c040100010400d098102d02500c0c11504c22004690301c41104040300d1010308503030380215500b00d00c0c200e00411002e8041d070101c1e0251110854151040001440981e6a48000e8a400b041d9501280015001d9071003908840d440005040c12164042d40da5030218003600a80c5941c0c10454215000601015602c081112103507604001d651895080d5118080d403250108000074080716 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 249660287 1250 249659037 249659063
    0x120f1a09010b1002101a0d0302010c0f02070e0105060703050910020606120601080a020913150c09050f0f0f030a05152a0307030c1704050a060c050f030f04031707050c06070809030304 80
    0x413506c030002c42468800500142040e18103454024028820f06080601017262445507402061000402a00b92080c032003000c0ca07a6400c0004020030f07500041c5044042000c20840300e065619841c444040061640d0028055070402608215000b19003452507000c80e40008010440005d0005000c901c6c3d640588060301d807074450f1590f42d9807000d081c1e0000340c054080c80c1c5507411041d03a070b0360004480d45841e81e0f038041a61303151030800104443d50b00c0b04d02d5009042480f494094a490001c0b5504c10b80c00030304a0341c06101c244c0e5070900300f1482680b501c1d07860308400100410f901c1322a41c1c0f01c0300748030410108141841400b4044016001c09404402003690720711003603060a00a00d00140d000e10b141920280381e1038240707407455036440650f070120b94060510310f05038490341c0200c050758204202c60408030f046945d100c401c2074840c07800030070903020001401410503502c201c46200502442c150360303400b40e5820050008615001001c3c02600070025a4002c1001c1d400d00030044d41e0308258000c00c01c03001c1d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 249661537 1250 249660287 249660311
    0xb0402040507050c07170618060609090102090418140d08010603020a0210111b012706020906040303051809251404261204120f1a09010b100210 63
    0x6400b503130f101c070040b0f07101c0c3d40000700f01e41190600d8484550b0820040303510384d0765805174120440b0314101c5221110303400503002c510b00b0302c1c0003a2503982c0a0a114001818a140d0000140640b482c1004941603c1e081c090000180034999035684041c407040c500030001c044401c00c004080c610140f1540d0b040650215140300e1a0740300384202c07401d00ea1418014804610301500b01c540f2030740f0048292600c0944030317003c031044a006004160482e4898006500d0000c0c050380500140300603984102c9405508000390004c41c0c1e40d0001400145001e030350f5264542030610305081c400422252281d100d1581d5000f0060006100c0c41c8000c0c95900101031820b9034807901c4d038144e80c98110921010391840011a0206d500800b000e004004c134001c1418601c0440391402d503594950101c03402a20b6a00d00401c0300b800900c05038122500414807d4103040482d103a2900e0b54540d0201401c1d08012031004c00040c0b1805903402d00603581001c004540e00541c01400c4107020750790712a0744004205440e05c0d00c205400e5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 249662787 1250 249661537 249661547
    0x30b04150204030c090204053d03020403050313030210031e0b040b0a091505010905030312090712050a020f032d01090206030a051e130816050307150501120b0402040507 74
    0xf55804600401e0321034442120030040d411502903e4015008512564400c500300c0c0096040c9010346c107208001e0009a4641444844640030b1003024941c0805c00040040c404000400c030b56110070503201107a07411881000b0300409000c4880040504100850074440c2030340c03a400b49020038141d80081d907040707a840410054581c0c01907142c1d100d90115000142400c01d5002449030718510900200d0795515000159044440c42c0191038043c0d20601081d04040240c0c1c220340c2d000b005013000c4402d1507a03035104490000c00c040a0488250b000f00f04040c0850901c000072500078a012406443c425681070101062100752001c0e800041c043e06c40b414045942c00c0d400b0402c2140c02034038a5581c2c0ca843c1000c940a0801035448504640084090301d00210190310307014001c00030031241840044590701c1751701494010450110b00540d46500d4040091020002030440700e125441000c0c004c0d540c0004d40c4c040b544140d201003201070415189600040d05801d4072544103a0441700000d5549990303900b122 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 249664037 1250 249662787 249662789
    0x9060703030f02160b090a050c15070210020a0302120a08131502070b06100302040302060316210f0606021902011101060b0f0301030b0603010b090a09170a030c080c04030b04150204 79
    0x4a0ba00c005060030307501502e4541280000e02503171101e80c0c1c94aa2000d20b0b65524122080948590481040c4400c1c0c0d282c44031952440004a0181c5401c1c000c081c1c0000341803542c2030030380c200580d020b414405c0c2010340602c21074005024070f0f18a00e0a04c00900e101801030701c4010281880c5a5042d60254200030107001c040c010f000c3d4032803045444641c03900e8070742d080d004181c1740c0310310540f1410034409a040c441c2c0202d500303880e80038100901b07685a00c495800c0d03d01000070610144464152072009005405e0000c4104452042c004548406204401812114241c0040045403c06c0320502030106080c0380c0c21040076420301c0c0442650b4141c800041c010013031600f01c10313400900015940100840c0c58091410b030303401500c40003a60349036035007014204ca2503a880103806c180c201c00007030342038001c9501040c1003074007a981c203030266001d28507131618550013482507101003569052030488107a403146e00150301103140100c0c00d241c981152200050301d03100802c01041034411010f181c1400101e501628 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 249665287 1250 249664037 249664061
    0x801060804030c060f0b04060b030921070b040818040b210106090504050a02010807030c0909021b0105090f070f0803040e0705070c0f031709131d070e090d090b0906070303 75
    0x200040028152006c1e00a04842c1840303581000b0001c10030039200c0c1c3c01c5038010641c05004061030260200c042c49584503010600000080500803107000c00e1212107090300c501d114500c440c3c1e40c3c401045001301c2000c2d0070300455016520b0810310710b0158130f40421050060070740c0500c80308440350745141e10380903003000d410110100c0c3c1000f0034401001000624003d00364800d8070380704010703a10180200c04880c050080390002400c01c0303008014500259005190447c0780b03981700010481e00110190a448043d10484602d030b1001c19540480481444041c02030864036180c0c00c0c200c0d103020805503413801540120905005c41e4030101e941d5034000e2085405d000c3d40041c0741e2070f41558a084640c485122440140e503c001b100401c444045a030500f154a0104010403045407190000a200010140703220090740c5e40c1070070a030401c0d0300d00c000c200003801400890f10809040c40c00141d81c03030070312031141400340c01c1c04004481446080d00241c1039405080d0283c034015110848d90034201c1c0034180140840c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 249666537 1250 249665287 249665291
    0x1509030f0c18100302130204211403040605122e0303030b06030c22120f060606030b01050d150909050c01020606010207120807080903070b0a0806100801060804030c06 73
    0xa0821100049281070340703020215010690780502c1141c001c010101161002e900d000420403c0c00180b50030403000d038002c0c1c41844018102912503031500329400c1d0154001030500360030a071010801400c0e401206884203010090f50400345480c00280441c00380040d014403e4043d032000655071803044c403880c00b41640b406400d140001c000b141943c491a05800b00b500024281220700c003450505201301d030701800095070071034540050b101c244030240030200c03001d440000d8034841c00204140048075051009000d00000d03d0f0b040490701e4440304031012988807900381800d10008020503a0080e0075924400c5038503502003204e9622807240700254000da00700d12038852404c8100410302c03a0000b900095075200781c00f01ca0b842d4076420016656035000b803103035030b0105145280140009080702e0103800d030544a024031609004000001900f4460346420004c076444020070014003442d4028152078000f00240c80d020b1005c803030341c1e00c0142071a00500030401413003803002c0440d082603c039240c5442590340104007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 249667787 1250 249666537 249666553
    0x30603160323060114090403020f03181804020a0308072402040314070509160528020601090b06070f4403240a0e0c03010e0903090f150903 61
    0x48403650000d03202c080a440000ea10030001d000d07400140c07207410313207140800780d0110106800c100654408002c00803001c40c09028078038100504104003911300d100080c800144040b00c01030901920121900d11241d50f01c6d149001d000140e25545600c100703803508245407550b03c03001410072201c05050300c16010181c090b90003060304914850340c05401680c6c4141081500c5a020046103680e400240c0113980e0f00a0881011490701d850501d4690700b55403090524900b45028540c81412001441504600e0b0b80f000104003116180d052200d5405801241c804001d012800b0740410303058024040018050180c0038410828004940440148120131035160255855000c0c1c0181d1406685016100122103003840b02003e03044140540e841001c085070030100707407c00c0c280c1c6800c0202c400800310350080350001020903051110813000c0e2041051180b019542d515094030781400f9040100b50b00d220fa0030a010840712640d41182c40da106450403a50340d40002000b00e2034211354801c00c40290303070501c10b182c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 249669037 1250 249667787 249667793
    0x708040b030415020304030f2003070602070c080a0807030804021c2f06090d020a0b03091c030902130b130c0e0f031903261f0b09010c06020306031603 66
    0x194840e52250710004003424540d03500300d099000a440007000704031428003030080d81d4854040c0403000c40b11407002d9a4603a12703d0b501103040d0f502c071840c162145030b0006950b078103002d000780c0d141008041c0c2000900d41e4135015100d034205408bd1440c0101000075040100302550341e80c0010541d22030314442240000c41407490b2480d00ba0725001d00c40c03c1c0e103001401520502540b0441c2003000c0301c0014068a141c2850103040040d0310002c0c06080b684040b48000118100c00c5407406140700e02940300081500c15594088280c40341c910200342010181000721600047c1c4075144190300004c3e02c400c0116044901e080000d010041141c0710b031446501d0034441d0013246074881da001c1c0304407405560180c0741c0003028040c5612003a40d440c11032803410306011f060001900c650b00d55000342500c4100511442148480600009001d446203168450328015150060b0103083c001c1c4000e004441015152101080020f0802800000c0240c05598003100140260310103115414010b9443c2060f0380410f52646 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 249670287 1250 249669037 249669059
    0xf0f0c01020c070f0f0e04210906030605060310090c0c02060c0109060605060309070308030406090c03210810050f130609240f0302040e030c01110a2a080a05070804 72
    0x8802d082503889810000541c1d00c0040e18420b0030707101040320060030603003040c42c001203025015004544421300c40f410315800007020040004c0300421580c2e040b02040c07a1900040990f41e15420107485003608000744824140303210003000849484040c0441c0b00d40106030f0176280b11482c800069000200014020034200044d1300c0010f003607124072800c0100545a0050004070300049074080c1150344440d01c1400815802c8000e03550040c492034003c10706060310b40d2028004031040c1e008417142c00c0b442128504d07406440840406030803440c03601c40a40e2400d41c80480d08101c06204a40c06050310038801d01054588404100c8400035a510a000042c2c4d00c0902000420008000340440c1c0c41c0d5240c0114080f1100e44e100d4115084152060071070b03820742c0c00f0000203200290209003148802c00818441c44020302a40401d1000d5014140e22460305503806480c19040310003500c1440300074204840d030014041350707068004da000171006444000c1d54005442500c510720021f003030007101250000d1a10821 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 249671537 1250 249670287 249670297
    0x10902030a0501020d060b0304170f040b0f0901080708040b010311010c0506010b1801020d1d01091d04111215040606030803011404060f03020d06050604020f040e040614040c0b0f0f0c0102 82
    0x14110400c1515680c500e03c0103180010b0340d00400100301d14001c08441551031014084bc0c400002c0381a2070980c0d2a482e210083c3d0003418460031003000403030075030190f68105510710b41c030050342d081c040c1803881c00340d582d0f000d54a014000149086840c2079a01071691040c00403080c001d6119044510030758442c40308840941040d5081400d103200c00203407200380c0d48045012000d9220b00d03120314060084840d03000c42d074082d2081a842c1084180303c3c0002c2d182c181080ca001c44039040c0725843d02d40781024100307060300b2034803e100c2602075442680f8500d040540081e407403061510864841425459600e04200a040d05034006041c42d240800003145143d1004100040742004079010005207a650050203806192884081c0d44445103070300180c04101c1581019038492070080c80141b400403d00005126504a60080700d0200985400c200802c4613901c1100348002003244051244d241c19070751b582c0400d940e4041c88502503004206054002c04941c2507030515946036000039285c040c80300c0101d00079085 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 249672787 1250 249671537 249671557
    0x1104020304030c1b090c090503071205101a04020a0e030114010f0308070f02041d07051008010e150907020a02041808030121020d0308070f090b03010b0903100207030e0a14010e04050405010902030a050102 89
    0x40d1406c0001c82407403a94bd1114110f9001004c0c10444045c1d50007900200344d1280c5281e002c034030602040305030707580c0c80c4010f203402003d036129003519407003440c1890b084481c3d0392020180c40044000502c004843d2048100840f64420720306561400a443c5c150440d0005400081d0441c5c100012440c104240003000400502e0070011944c01c3c1d03503500100100688040d480c40b002ca02e4000046c0703d401c0f00d8801076035002d0070705044523446c020b00d5404240c3c11402110210016008041d8017011884c00e8043e000344810101003000c00c0d90f01d26140d9440c2c4e0311061107035000f00b000b07c15420740514000081c20b4002900144054084502c0f0308000d41004021a107000000d0460415095240e004255010545500c044043c2c216802c0007203441c00b0740d2110055a5151050150070040100103000a04c0c4451003551042085061102840301c83c0c003003030f0000d82146042205101007a41c0c4500680004d0b2800c96000c1120344075410002d00500070120065058000c00400310107000c1705400400b02c00c00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 249674037 1250 249672787 249672793
    0x450902030a09120f080a0b030a050f0601090f110306091308030c0913050906150d051f060509130303110903100902090114090a020711030304030f1104020304030c1b090c090503 77
    0x264a240c00c55081c0c011a00010201c1c1c5401c000c1b90020090368000c0010401c040c1c1202c41506150711400d10b4180c0c0d1040466299111100601040c0450701aa81d0495001c0200b8443c0c0f40c440f5951012501000304014002d0081c40b000403052005080b60a00041d0403c00341369032410569102062648130b003004602850169004551122a5108880c07062071804042c183c40c2c2c844080c00642c1e0200c0110481c0d00014059070100400c4042c420303c0903100392150182001410b01e8a1007040e00c010b80c0c083d500c5a0010300c1040108a030102240250590500c1c000850b080c11040c000060300403690002d806200d01e40c1e022030075002c60752110403203034000c40c1d0b000300e40d0780c1c2c1c1c04011103c40c1020005981104104011540e03a185503001307040c030b0f6072040309203400089a1002007451500300390300558103403001031040d005000900350000101c0c4c0b815603003907140d498180c8020701030300304600c00202419901e99410350001c442c00c9a0f00040c211002d001d10850b0030869000300700103070902469100380 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 249675287 1250 249674037 249674063
    0x6010806150901030515030d0e0901060c12030b03190614010801060b0909040c09142a090f01030e1e0c03030c120d060f1203450902030a09 61
    0x1240c4000d0140c00340710561841403410760725100442c0500303400380c0010344c1c65880303c1203849142e0301841082414445665004801021102000b460a00680c8010113101c140c031501404609100b24140717494501d070902048030b80e00070300424034001002c0300d500141e0b442e0b18000d00401640c0d4204196508009076030403656600e8001e05802c0b90528402c09100020401280c46542014203440380d2160003607800258090390340d080340b0142c880d441050b868000302d0104000034181c544105083c41070740070300c890741004550288882180314032005180304000d03506400031140e12a82160405810b000140d40c4441a10071a800340d6005500c281d9a85001d01031002c00103043c0001130b04e030b49a4003400201814134410a0511580d0b0166480070307140d40c3c403840d01041e012094581f400c01480c1140304401540500d0034001c2082001e4481800702c60f901d071401b60000f032056041d0b0342c0d003015411081a00319130164112480381080f540090006d60020003006660308565024020040c010380000c2545 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 249676537 1250 249675287 249675289
    0x105120706020309010c020406080703141204030c1202240c010f023408070b061309030c061109090907030b06010507030804061122031205120103080a14070501020306010806 76
    0x20380c080d004440041c0d0051091480540c8204552480c80c1e00190002640b0340d1a03e10301c7d403d11105070821380d00e40c00000c5c1000302c2c48004200d602e05540d51028458206420740c0d686811184080c070545c4081e0506040d023005554038a0200c1c140c580881e401d40142c844032111118007a0480001312209502e0031b42c1c1c0c10304081c80c1d40201c07444911030000342d030300c21181440e011103c41441e4140307011985e032150548001858017001404074500440110a15107000710400c465070f0b9074907106800490502e80c0040019400c240c0b0085020303404a00800c04041c003c44013403250044940c0c582d8407070072010610025100229641041e28040c141824403562442c0040d9800c0c4540800200007502c04c3c800500800c040d07902c0305020444010318ad41c68005142d5864003082240c0c291915000c0c0c11640820801c40200b4640c800c0014900b005424102c1e40807441c252920141b002030202c01c0c001800d0707660140b15220aa41c04604150000d031195a10b0600500031342081358080e0110340f00130f02040d01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 249677787 1250 249676537 249676543
    0x303180302062d060d030504030b090601030209010b09130914160f090506010c151b051306081e090a020a06110615130f1104080c0102010501090504020916140a030203010512 76
    0x480e03807108100c030b10f6515807500744221240024416000c01a05100110002e044155514040d607880d0703006111039410345c01089018001071b4040c804a00341002041c403a0303101c3c05500d6003d10000036001030301c03003145d040c6292200f81c120b003040e03110301485410b00c0c4034200640f501030503100d102125540882e1a00b034000120f62080c0e40e05804140d55034018000a13007902200300b040e151101000c11300203d20404000c000100c8050756002c50004551690a001500c4000000f402e01c0c3ca041505420888080c2002c00f400c0c40180600d1443e01c8000391a00e074080044d10045540640036030391040d9964401001c0c115000304400e200d00401020030f109000303100c0c0d25440f9210040c05005181800aa542c0c0101007003600d008103a5111512840d110586002600003031a811020701802d44030b000009003103c01c1600040c1302315140105000143e05d031011410390014201c40c404e1103030213a814007501c41a2229040403c101c80004225a525a05801131812520261241e040c011003207212583c03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 249679037 1250 249677787 249677851
    0xa06050c0f010e250e0a0c020c04090804050111070e092d070501051c0e0d1202031e1909150b030a0b160504090608030910050310060c030318030206 65
    0x51030b0b038010714a0040880c071140031801000c0803c05804000c075614039040310340c108106c0d510809907991704c410f40310184d018041c00003141c1013158104020801359880181070300407401450704000ca80e82c0b41110401c130403c208009002ca01c180c000c81c5207001c0341c040c0c0d500d84035640803032880303d0010780b69403041c0e00080f005d0302d071001031801400405060a004407101e40008003c011140440c56540e00358030301c140301b00d10452025802900a40c05840c4000c0c010a00004d000f1a845204004000c0402800d1044858503405440c040e46a519180d0045040074805034010036218079000e40c100800c0002c642e90850650102d0003400039031901f604040d100c040c0d402d030160520010100089600794100007540064080b810180c4c106030300c4007003610071282c140e000b40d045907000007003050481c40c046001d02456021484c0141ca0b51800200c4611080c24030305c03820040c0050351081c9030070103010b81c00403940492201ca00d14160852400c000b9551501a0b0742c05652a1205025600a0154040642d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 249680287 1250 249679037 249679061
    0xa0218060a0812180a030f140115050d1103150a0b0a0509070e010c051c0201090b06030106061d0102010207060207060213091104050111071d0f070207120803040c03020a06050c0f01 79
    0x503041a0000e081c1d9401000c2c2d030311411703134030031903a0102000056a440341c101300107010381e444c0b01090509480c500d003122100a440d082c0703e40c451204114603640d1804d014203090380009203440500510000c02c0c81c1c01c1ca81c04009d416030012804003c071021490303210445c0b143c41280e04140075940e0304240a0b00e404d055440f90000b0b4100d414070040b95008050400505209100701c80c120024110340c941944082041007006075164080e50040c0488617801e01e402450450003003104510384400900050040807680503e422010540030b0b060317000798165600580c1003503082d55251401e00e0044000c0d403122910112400c61100e0214110005200d0452a90901c0d6540740c94107080c00011765007a00e190b00908640c0c440c08402265015031280c083c51050300707552a00d210f0742803865680d038041a0040204045500045003041140e0144512402007600b0101761540c98895080c01c141413001e0360006504260740c0c800c00114654490018203c03d040c40081c3d038056071018040900380c445600d008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 249681537 1250 249680287 249680323
    0x30909020310050618040e0d120501120b0403050c06010f1d060604090e0708010e010608060915010320040e03030a1119050f0c0d020c1008190209030a0218060a08 71
    0xa02c141c1c04d0040042c14084440c0b5102000100524009810768411480000d2190420205111100c0e04607200120254001105110030741c1011020300002c00c0420b0082e280c19000404581414010070440fa1418401c4003950a10342e11080282e903905024420f1301c9415104184004140d1201c03501e1601543c0c1c0100040d01c0d051604485001400790005a048540036805000443d40c500348a40c11b60308031403400100c0c400e071908520b40c0c18040d0081800c4126009203008102d039411500f04981540d600c8860303440b0f015202511000e0604180380240e8000785032003901a941c050003c0a035110302c0c60144280121080642000c8a034000c0980c40d40d42c81d560700d80841125030240001c1c10504401c1c0e0001030415410a880170310f04081d0042810140e000b217800f01c800c0b030428a8404061400c10705008481d81030400f2540401c19910080c0e0010700d0340419044819a010b0150640383e94000b440c9452040207001c201d0302c0140d013650301900c17503807030f0b21000601d003180400d400125103400054 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 249682787 1250 249681537 249681539
    0x402061b34231c140d05120a0612060e100b01020c0603070c150e01060501050a0f1812061508070f0315060b03040302210c0a021c0507060804030909020310 68
    0x100c204a910304014003100d1494a00000c006403240c2900000b00c900c0d03100000f01d024035504018425070b03515600c07104503802c0000e80c0c01459400100301c68203011944c2c0c9074038090396221000c0005001c90741048019103030528240041c8130035a08010032403006502940c41a51120321104116450700345041c0c0560003403050f04516280000103181c0c8840c9608248203248141d40d111225107100508144c1e50a50325001c1349907041007449a0009000c00b802c2180c0b401d080d0b200080c0c1001e054214040030048409807641500f413183d94284010315503003c0010795489a0301d402e0b00034110040180c69456100704c2c001a06510004d8000b0440311002c0c25204858116143c000d003544044041100c4142c650400040c2462454021403113203000f075000d800c0720319100c020014201080e80c000c1e200b4000c180400c0e01580c001081d040801a07040b24440d10003014002c0131685810601070150040c0202003000810070b400030300ca00e200318403035950f07a02203580303070344400303040703002c00c1d91360494001103050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 249684037 1250 249682787 249682799
    0xf200a0f050a03230715020c060702060d0905010b04020307090504050907030f0b072d031802031c020f15060108010b0310050d030e10050406031d0c04050402061b34 72
    0x184000707800b4031100310020210b07004d403991403a001c0207500c094035001c81d00c04800d0604d54140a0000f103450212221407404070903400207201c07406103040200c2500d91710040c030310410000354000b2000c0f45010b04195141d280c105c1002d000086c0310f10034035000e030b0f05050010342c40342c801240c0f54081c5c95124800c0300c40c82c0749070344403100019002424501400b242000301d800b0406840c041140d001400c5080080100200400805664120741c8000e694400c0803412401660b0200d040c50b40c0c5916541c3c850301a0741820303070807440d10440c260702052a002c1c2030040450b41002c684d4081c0320703010a88038101140d030b80e035403000b0b2684000c4030800030240f25200203001c18500a01c480d003801d0701170b1070102564404c000010b15a2010740c9000303030200c1c500003003c00038a6018010360050401d8180302e00c981180c41f001294440d200b00d25201d00c200d03502c900040865440c42c0a94000322517035242c2d070b03400350700b04000240e0b41c2c03881c06c0394244c1d0300100c3e90214180d031001c002e891010740c0b4036658051003546080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 249685287 1250 249684037 249684053
    0x330304150c18030606060e03011b050c0307060504080d060b070b130311060f0106030c0309020d1203150602010606021504030f0e010917010209040606090e010b03040f200a0f050a03 79
    0x24103400c100200031903441c2c62141e0001c1c080a940a00d41c0041c00e2881c0050107444501c440540321700990501c002c0140b001001c4680240007546400c040d035445021013512819881075540c0185091b24020034442808900c0018113018907100300100300b035945605400c03c15000da01c0004010804c0100015940c00141c00d41c0800148030b403d0051204031041e91a5041610890314110690449001000129414058440d070b15016050400ca5145035401146028001900103004550300b8000381900e140700754092008040c1c40038600c10100d85880f4028040c0405201e6075006210b01151000d000d405032a090f4000c0303515444140c034a01d008103082c4c070084488032a013414013608500010710100c000c44040c011418540c0016030b82e21402c000c00003261144d4210000700140c030780300ae0108a1507241280d06680300c03041050380329a141d29103500c40c0ca01c840401481d031502c80845211300d6040402c4030000d01e9088414440082e1602e040384404291849480d030721900f00442040411108 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 249686537 1250 249685287 249685301
    0xb09010504120b04060c090b0a0e0f1c0b010f05060901030e1203130c09060602060c030901061d0402240405060a02100903090f0b09150d0b33030415 65
    0x1030410605060742c407107555188a01140d0156a4040008104010007a0034403842c0a0365134641001c448403403c0c40c040440c036004245011003031124400d8030840540d80c68801e881046401030002038104800000d1800d07001010000f110010001c20003c5842c616200c030003004c0d1030b4060300c0c030360400854800441c003802c0946170001d032318040e4000b64003101c1020301c025032003a4400d910100300030280340382c81c00020a4a038030424130645449007c3c410035034042103940e0000031429480e601ca4445a184a0043c10107038090081c10041d80c4407001c40704c1000d00740a201c1d81c000ca0364914481c2135410550101070303100b1802c040c800b070100030520403442d124000c0c02c24038110b07104840f49201d450305120104c40c2d0041050b00400c8001c0410000c00c0a400c00350406000e00700162820152840040f4804d011900e43d070710b40207080410b281e04081a2a8050011580000c25014800032603083c41d40403c00740071000d502c03103440c11034001011581081201c2c01258400c1d0080c220b10300e1a4200c0c4000c06d04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 249687787 1250 249686537 249686539
    0x80f0a090f050d0b2e0f050108060d11190e0a0c0c0201080a050703020c070902030609060613050f0111012a0c03080a090f0c090e01060906030807020d080903030c0f060a11040b09 78
    0x60f40b0180700001c917280e0400d1000e40114400402c0c0c1d40c28a84070300380500041d400141000500000c00c90540c440e040310107949507010b040b012110001a0004400200c154031005441034941000239424695421290281c9035a19080014480e864021104912510300103404034916101080a12100c1e50210760b00a2a40c0340c0141000c43c0441c80c80c1c1004200d50001c00f1158000c8280112443c000c42d03500c0d04001e04503502460b00c5004000c20306d4800c2e4510540d80310b0f0502100c945816400b540c80051400030f800000c004401c00181150420b002030585503001c8020203400c0100e80e4000c0c50b0035041c00e501600c1e400900c0e82c4d0b07440d4981c050a01101c044805c00c0400710000001000c1e04d9424000d484070740740104081401800c4c203802c64100c0c2d03000d1864641080010404918a0400c540c00c1d01e03010381d412a52251036050140141c818503061039094030001802088030b0b14007040c0c000e81c0b04007140503145541c4418804c00240d40c6040384008000078200000c001658100c0000e00b99104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 249689037 1250 249687787 249687811
    0xf04020315090f0106080f101401090c050909040b0711030c1009110306070507060e0303010e1f03020916030f0b01020c21070612150e070e010c080f0a090f050d0b 71
    0x421481803403c1d070380d19a10101e5103601c080201e5072211400e010000c0ba80510440401107274181e84203010703821006110303407103150380d603042103590652158086410120002d840b031003640c10030341307028620f100003101d13030000040c0069020202d40c400071044850f2580444010104a86114400d04c018000b4a0080740c0041c01c00079500802d0b00c0902c8494450943e68454540b1541c441c1030501c00d07180e25503070418481c0c00400040c00f0070680c034036903039802a2044507001c450042c0a061401c12480941000e94800761300010081c12002e0b0302c0104556100c0ca507000d020304241c0c0382c0a03005a0755a080858003503003143c0a4a000d0303051050250001c3d442400400c509007003000c8189040c5082d0703810420000d034032418880525010342c0185505c0000e400c0c0750407940341c9480703041412a04003604440400c0021410007100d0381c810312450741140c0d001150f580c0e941034060720060f55584100303602c1c008518080400200d03401c07c604e10b2000c60320080c25034042404644e684030744a1b00002c1001c00526 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 249690287 1250 249689037 249689053
    0x140601030c110f011508030c03180112061502010b01020304080d0503060310050a05060a1e03080310030b010e070f02190204020703030608030a0905040f06060e0f03120f030f0f0402031509 82
    0x1c020400c0c054191000f8000080b101c481d000c50098418090304220581d50081001c6c1c00c6495000080320740c003419018264407035400000c0100c55508001078081030a9080100220740c100d540d011015945407580c000700503400103100103a03140d0141c0d1040c4200c940000e013200e80c2d028068401140d00200081c10354010a041c1c03003c9030103c901c1641c02e11030aa0b55402000720300d052000c070b218050a03240342e90503480d14680944000c090354600008203409000300c00f042d00204107902c490082c0d980000302c03c840392b844c1d520845080100300c41c0300c4002103600c2541940300e800810708100840c400c2000320300740b441039000d04c0069408000c0460405d6035469002070b00c1c1000b0310240120b40308503611042da4514010800054809000408040c0c80c0780805c2000340d540c110302c1048464805442c1c0c444c0c0d044a02d00000c1c00c2000c010200040c83c10b000800ca841c26504c00004d40c850803000020010903202c44c0300b17943d584c660442d80203403d54842c0650308444160040c1c216403003040b14003162925 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 249691537 1250 249690287 249690317
    0x2604110301020909040605010e06060403120f140c0102070215040e01030f03092310030c0c02041107020d14010f20090a1509090b0303030411010f05072310140601030c 73
    0x8510211020348101c2e40d65001444000027070417103260000c1c0200c900c0350030700c5d0650311020f03051105400c0034810f01000c00d00c15440b240c054140c41040307034610032099480311200181700d8080e51068404030700c14100c1c9005800740401140030345040d644001c128544681c00e40c2d403129030070441d00c034040c0c00340084c1d0b03400060108008900e800011030315055802540c0004400d000d07034410300040b12024181400003400b0159408805403038041d8046034089012601c824000c480c5114000c4003942142140020030140980d01310b50b0024034407028020001a406a03c00000325813070480c075480c070350080384102c1007804c00fa40042c102c000300040080303800541d035030b8524030398003030702c1e03601d00f004c40c000c100308008002480c420ba05400105070085d614603d0942d0300c0d12040c0e0300e4510308a040c031000002c0014224441d81c10303aa03c0c1e560080030202c0c6040146001d13007030700b1b0b15155244441d01c1000b016400440c85401061010311117441103004c980c0f10400190090584c220103501000002500100701c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 249692787 1250 249691537 249691549
    0x607060209060d020405031e19030903120f02150705161e060c020c01020705060301051012180b07170606090f090f0618090709020913020d0c26041103010209 69
    0xa10481c3c07001a0760b54508020b2606240310451441c403001d01075071f00480c0d201c40120b401e0064968105845207200c11515080c0d85075020f580002d0850769400c00050034880d00046490383d2303a141d540072189090341090b18140c81e00c80c21940d03023001460500802c0700d400c0a03680c80c10201c612404112444a4010041c440b49135120302c402c0c1d03203054603604c0c0311201c03e030140300300700354a9006e00c06014500d0426010819a1106204403405026482020b10b50305106038420540020305000901100480c8141c02e404003000e0207054804610801c003049a1034060b680394030b0314060144800c880d42c0e8400042250640201c118250080c0c0900e4075804240d5480b40414400e101e400b10390121030800d041480607800c01c0d4003e45183c0c100b90000d002010a000640b60211440810056595510f0502040c25440d01c03516030f040a84c0081607003090718060341c212025a5045d46d4418076644900c0d4030400300b0240c4400140403001e8810f002c500400c0c51000c80100c0c1c01030140001d8501902e010115107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 249694037 1250 249692787 249692797
    0x2040c08060f06090108010506070303060302030d050705060106030c1e02030c2e06030206030f09011506050c0c100e0f1801030b040506062b0312050a1e020711060706020906 76
    0x80c100c00100300242c5000034100070082419140c0e241808520f00001e0030502060041d60f11841000c00e40208240c403c2d003108014507805410303111040080c2a029109030090704003211039009a10021900078440e201d0110390280d190b999140070300400a14070144071006800c1c0e401c41c002000450250784041000140066840700346130110210303200b99584030901004080700c454180081040541e4841040d6a00b0010b00140c5003040e44a590380103004221445020416040c400c0c00040c42c1500302018210281d81c0000fa103001881e06010040d507890b06540c1d0801044c0100d50030f21a0341002d04042e0107048002c0c00c042c40d40c0025680c3c00820400c00da00071507001c0d0f0080d08010802c9020302c03040740c1160054445c100e415242140d01108950905241e036040700c0302e4003c6038140351040c00a00c2c0702e000d174030a0400c50340c10281c1c02840038180000740e10b1404018540c018141060314800c44111917003003d0010481c2100d002004000e41c0f007103001f034406070313024030a000c00b0b5507540d40200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 249695287 1250 249694037 249694061
    0x12070e090a050c0d08040302011b120503060306060a0503190501140109020a090602070608190902090f010f050d12030e1002190e010305090a0201030b04020f12010e062211070204 78
    0xc03184402602d040c61a2203002102140140201c80341000010268000d035030650b0b509090000f1060903044060507000c82c1070402600c0f003d6105584866142c2000040d401001c090f025107100380e40d010701f8080019a030f0301c185900b590210241000310050620a813184502c00c00012513001c4090316041e03600c0303400780c020032001351b400a1043c680b60f4008004400809890000c0e142d214903040d40a02000d4008000710b00440301c2000940911029511a403002540202041c1c03190620303002c038100c080024010307158240f60b245400714951031b2400d600f8581c5541700058000400d036840007140508206001e0704804d210711400080310607141c0c0054940e401d0404114001c0f0210b0a44c018010304412880340d06261a050600c50040008205040800d4081c2030102e40c000021000c90000e1064466820141c40e012554048102c40d8400440c100c800d0710200e00c0c41c1d07403544403c204000301c1c11006103281201c640e40c544003100380ca8224014200e0811501ca050120680201e025103a02503464 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 249696537 1250 249695287 249695293
    0x8150a0e01080607080108030d0c05040801050f180708030f091801031b0603020403022d06040f0312030507050a1d150903060a0612061806020c03120703050609040212070e09 76
    0x600642c4401c00000f075200342c0e6460503c00a5240848103903c07440790000711006c083e11144d0000740c1500480440d40182840002000145044190707000349040c10303100c0304603000c00031078140d00c0c001002a1500039107000c078019615000c0c060803109060b911100b04280c01841e00801080a080e03500c261707a00035801201d10440074036203481d460b240501940c100806252040c4000d2002d6110b1801ca00740d000c900c0e80400003002c00608100030344070241fa1100e40d1100b40040c020030480b4003110040700f260304c23812070103024842031241a000e82d0401c031805000504103000d02c0da0075600c03072904100c022840c540d46802d100003c3c808240c1155180008038007560b0009415189410704004555204855180c00c2003a541040c03001e00110001e20000f401440d01c0c2c0b03848004d1038020107403000099620103030440d0744d03030b000032b13019034603034202c0d1225a4190703102c2400502c1182c000c1c001c0603c100001443e00f00c066681d642081140c500c00c8002d80072174413551401040c8060f8522035540548070724401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 249697787 1250 249696537 249696539
    0xb0c010b1005120105010903320706050a0210020906030c030a0b130209120601030b07210603030305010810090209010902030411101d040204030b070f050c0307060c110115030308150a0e01 82
    0x603452160041e8030171410098044d104002181101c05150500d20700c0c0143e046010030070000000d05040102c244500301e000390400052855003080c01052205c485400307072052906003070b140790101d0103245c2c0382c107400010410004d81514071900045920640e40d000002e0755104d4480800c0c0030041100041550303560010f1519034506c0c00040c1e002d11801490000c02f81507056030f0700d0313080c41c06000c0d107008103000360042c80c02140040f000c0182000b84142c5c0c0300300465583ca060007006000b080c81400007900a0f0000341c05450028002d44410580280105d141640b034400c0d10002540018410380e5401c0c6104507414080da00c0300f0090a0708841c03035454408c441d0519190f107031140c4c0c80c007119511403841000200002003c42e240141c0c0309100d400d0803900074a600406a620f03225089040080d4003001441c00e04000d1154080d52001e036850303803040342d20000d0401e06802c0362a444080d03c0040e07840001000081d02c102c594561040d481c41181103030380aa24080b032a0701002d5000361010314050300c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 249699037 1250 249697787 249697807
    0x10212120703110f0d0f1406030c040209010e120601030b0f10060f2606040b031f0e15040317071b060b010e060d0608010507020303040f0b040c0e070c11040c090b0c010b1005 76
    0x29110a8010040c2c087d5850a02e040000c5e0303180c41c501c050718016600401c3d51000e0fa80915085206003a020780b1000940d035202060944aa0003400102c0e094013204001ca1503081040260034480c280c814004003003142000b00964135580d560803102c04011019403044200e15400c0301588560b00408000103940c144203080005403030b03103150b4080c0070f64007800800d41e1903181004016000c143e112400598a55060f074045d0920044d22002c0741c11309501c00c24401056800ba0460b0f54448168429100d2515480c1045500c0c1220310800e21044003039012140100301c07144d21568400105042144c0200751507030124000745c12420281261640e0b0300e0081080311828014039a01c4501c500c059442d514040c0c1c0e400402d400c6448000e80840034060014041110b90f0010700060080c0d00501d01180c54500c40090001c240b0007011141403210403040c81c81c0381410300404a070400d881e02e0761104d0508125046d0a0b0b03411140307000c07006640312002c000d003030b031074841703044400e034440b0796540d5501c0064407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 249700287 1250 249699037 249699041
    0xc0118050307030207080c010e0402030c04080105090a1e02060a1107030507090c121407050313080414130e1b0f090a050103020114210c190509010212120703110f0d0f 73
    0x15114046c140c110b050502d100760781c0305203201422442100e006859844200000d6000d000303a80086800e07610f400d0034007421403030004030f0315641440b4020081300c034201c616a0041b88014443c0c0250001414080d010b2514001c451580803c000e40f000c0702c00d1039681c0e48410f89801c480f036200c031400035502c40030801ea0b5640811010b552050055050112001101c0781c103162031002405481000300110120321078186505035000f00319084848940c6990300c40000105070107e84079070074412104a014210f00507124054190503420400181642040150052101e829060002940070409000d540110b42c0ca4260180c080e031200c001c006002d604510000d05807500002d440d110840c000e00c051f0134a4008030ba56501d44058400302d441d13160700d444900742d0440c051900740d83e45103140d0b5a1101c40303966200024000c1c2c120240d0031035401c0240c1514036039440c4141070340c81d10b040c11914006110103000b6000104001d0313407000401d18103000c029001c04035400c4442c0b2034600a4445238600305c3d0701103c1c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 249701537 1250 249700287 249700289
    0x41404020903070302060a02160906300b07050d1b0e0d080406050f04030f0501050a1508071e2301022b03051012030c0b01080a05070306020c0118050307030207 70
    0x162011440c021030302000a90302e800b1480002d05c509030018100c084503209100c46d103400e91549808078003031070325001404041d1640340030b0a441030390301c80040104e03020140b2500d041c20505425054000802d6110b24210726001400b090a11404000400c0110f034907100750aa800d00b008003a00c602002130400400c6a00c19a104500c58080074a0401c0411b000c10200c0c0e00311403850510a55681080883c40b596004543c00034112a514030842c1040c0401034020f40e2066407092401c001c4c0c0000000c21000c090114050801e20ba44004070900c00c40041c0c032450440402441c0410700b01c40d03510701d10012310b05e0064401e20703502c407610b1044140a580400c1030010016002c41040c050405080011030230440002d203d00c101a250400301c2c56031598810307070002900f01000300740400307800c908000d080a84000c10842e00c42d034281c2e0000812000120740841d1981d07100b0003a0800301e00c1c40d11020040d420441c8445200d55a0b000314101c0e00003c109926002131081e40515200e80d01070802034104801c1d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 249702787 1250 249701537 249701539
    0x703091707032d02040207060906060b030108030d11070c08151312030902130e031b0307080a0c150c0f030e011506030903171e010b090102030306040b030f120414 71
    0x1000c071080c8009010940c0c60348000800414804942142e05855081e4245861001c0c0d00240300003815005d2080c0354210700051801004140203e9548441200350f510007482940890b800a000c4540103040e07540000710480e5041c1481410403003e40c440d0001007080703602141e07180d48000b920280c003081c041c402e01d50103a004c61004503951040c1c0c888400052004400204241d03070344100b1021503580344c0709072140103240c031001c1180440c14800581d80303511010360918109504075461010303071000400ca0709420b80c4282090f00748860b18000352040e11070200700b00c2e41c0c0e41c1c200f08602808070f590b00c0791a9206545507140c1044448040d0043c040324210301d0391101701d0741000007070b90503091004d0300c0104864447c0b41c0080d500003107003002c40781c296410b00c425049111100c00c0c40701c401007030514031003151003444804a05990b00c41d150403182c41140450b60160300180000f030442d140a600002050001400382e5a905001c00a043c0c1408140709000c000d03c031010a06103c40303171640c20304080000d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 249704037 1250 249702787 249702793
    0x5010801140a020909060f03030c06040c05120c0d0609020d17040317090d12140f09210604031d0603040510050703060506040506071a100315061d150607030917 70
    0xd14000454005d4030002c0c216401120120346000080d1030410440382001601015034650381003506c2d0610121080c1d12803503101d800d00340802100400e0106a064880c04000c0c0001126401031361000080c00c0c07184401c0c0c2c1d1183c404403000d004911130b94502c61206202c140300f10b5540b0308600e0003403c01d43d003201d02c580c0080428001c003209501c51620b155150b07600010b0140403503000d444121155007000074040700c21640070800c07440d08034042c0040c102c43d11086449084800c11446105505120284002642d40c841001719011038001d455081542c61099032040c9540404008901d60741d00c181c5081710182d000c86802414560540315690700560a89818080140750400182c4503000e203009084c81070200041e8202000000c45408642c0340000ca250030651828400a081024080c40251030003980303141d0030540340940d4070800c000d131600b056401210200a0313510302d8080d8002015001700d0f0494929808965860401070003405202e95a4119064104601074969913140392000360298 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 249705287 1250 249704037 249704047
    0xc030501050601080c030f28090c03021212040b07020303091f030510080705150c07060801061101140403050912161e060f050309070e01180c0207061d1305010801140a02 74
    0x24914180f101d8011082103c4a5046034030720204023404c11281080c400344516004080302080000048001103d000719107400703190080171403181d110340c000084210035010822044c0010b101001c0909512400034080302c0c1001c1c0c808001c140c0c2c040c035240714041d10140c3ca03009042c03241c2d80350240f142c6c05105010408825407510420380d0b5160064024144118120004c4298009400064a60340420324045401060381c07010080d2103a04280a0200010750545003649100740501400ca9041e003084141041c99841e0f85045440f90400c031075030780c0c0c800300300e0403020402d6004101c44180c00102a559581e100c0c54011415892a00740314203000818807507200f0410389402c60750160b41c1d40760508110350ba903540c030480e0324100803540d00301c0040781b2468000420507103111200d03403103c000042400c01000c4000c0e44207a81eaa0810700c20040041c814040a4180758440b5090703144404000d090000c1000c1b00314802d00a4440c00d8000c5269070b0b40d200058072880312254201c0342c1010903400114500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 249706537 1250 249705287 249705301
    0x20111040b0f07050d0c051203061e130e030a0324050103090c0e011e090b030604021e03100e010b1c06020a121a011e0507060b06070c030501050601080c03 68
    0x14090361040c2030724204003040303014030b2402c00c400b11140540d024080e0340580a09040140048401c144140c0f45031103000f51000c0c069000d00300310790181600400c13040c504000c0e1181183c0d0205002001a004002c401072484145028020054040903040c00385031190403501000f411180301081040985000b00b003541819031944003418140c400c00c0c07070045031404048c2000043c47e4013541c803208503560340100000300c414010081c01100781c40441298101545c8501d50f80030b0351020440680e242d0400004200103241c11040403110070031544010903c07c2c005000030741007403404401c00c84291380311618201d0700340c020710409001d031900300c0348000011003046040076401000c010090410794000390481440f40210308070b41d0900c145440038042c80400040c0d00d0300c1055201c15071804101e2100d10502130340c2400104070044800355031141e060807943d03154000901000030009400100070041440494000f4003034402440c010750001c6140d0034204001844840000c02c1c1c0c1c17682da0b1080c020704c104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 249707787 1250 249706537 249706571
    0x12040303080a0203060303040308030108030a0806060426010e0706021c090f03080c0a0209010b090a050a080d05031f15110703080a081005040f09050105090102120619050603070504080d0201 83
    0x240540c001130322961385001091951140e60000350180c48040000203986200000811100038a681d5240c86c0e038603454184003d60103640201c1c080300780107403c103540740e1200c01c020740c014401900000c0303010500e182c450f40c28000baa0308480010b0b000502404949140080d42034810300013440c00018041c07800441040c0304110f0701008104d081c00003503001d5110020480b408109800400042e05565980300c42e20550744842a500c1c000e241e01800000d540c03a207001103c0071600790902400412945510442e80e40e80f0003060601101e100300d9100765130303082100941c0e0161443e0b60604440b003543c3e200180c80840110b0a01c0b01607400b2480c24400030b100c00f4144c2d95608403505044586840e00711440e071180201c2d401040e0040d1510300c8040b00303070340180c115004041c0510020803954848004080c282d1040e994601200400744020901c1030511131b0000340031885483d0600d122649031000900c05910a4031b0031000508085801e00c036580041c4603071490680680001c0140740d04101240c50703 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 249709037 1250 249707787 249707791
    0x1303060b19030b18060f0402131418100f02030403020f060606040302010c08090409211701030f0312050a0207030801120209390a0305010506031308090f0904060605031204030308 78
    0x841d0400035008512404400c0091142c0c1d00d84d03042c00c0d02c0d4a807500030b440c80c0305a0700c1141c090f44541d04141c00981a5009403164200c44540485034804a948102110380d4034100d2790203501461080280400f480c0e9036030311590703030b5061011002580e43d00b42810021710f03081d05540c03010300c141c2200b01801090781e6180202d404583d030a00341206421854103041c801801142462900681451030a104205040742102c02902e9001e968842101d40c42c1011541484462442100d4a0b400001480403c0d030300c4561101c8140f00349850b148000e0461060030a9440035200152070036001710b0030f0000c0640000c0c0c00c601512441c0401c054000722a000607168180180c4185c48034000f001c80c150031a07a0700300000303202d030000540700c0d18400039080b08501658021550f4400003032811002044614042c0e08807401404c588000c01812a02a201d0883d5035101d14a440d50106400e40306000c540c88100b41ea034440c030b004010010301075103000c05040c20040c8030f00403601110340420081c80082c1d0000121a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 249710287 1250 249709037 249709043
    0x1081b030706021b043e09090109091103030a11011103060603070c050c0d1b060504060f21140a0501080d02030d0e0a060905031e04050a090207060603081303060b1903 73
    0x240c0746003201010800400325261821349013034446c4140070b4043e090301c148203411307440410b1080c03694285054543c00d5001d05c454160340800f50f8001042610301e181c00c032020309030054090403030500c003400010b450745d48024143c3c00420f03070071707218808200820310800c580341c2c100e01001c3c0e1071450503d0001d1070301e00c07004020b80240300081a0300710600804001c80384007800050640702a09886040801c0d160b042c00d06031401c501d0804c440410654820f46c180c030119003450715601819000311406940c1d1600c01100c25002c141d80881130621100140a040c0070304000980301c3d107084c1000f40e2180280d840c1600408603da00c40302c0c0b104075880d4008201c481505849400040b621461480e0038288480140080c040c182407461140074041d010005042c0c049040c04812520100745840c1200c2d80914401d0070740c41144024204030391425900240040c038421400043e032591240c0d5094040d0304050350003c0004a00c00c001d1003000301034403d9101d601400c540c4003041400c0a64000c0c5010341d140002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 249711537 1250 249710287 249710323
    0x215070c06181202030909100501093c17120405040e030409140106020601060903021806010203130b03090106050607080726030103030e0a060507211701081b03070602 73
    0x2010000d00300242c00c0340c0880e44141829070141c3c64407002992a00040c200a2141c3e0034030700401c002c1c00c10341000c8012210182c443e242e071385291200580e10b140c11030381d244404c0718600d002c001d4000d40030707018059000c10b18500000000d0030451401007224140002c1d0f120740d4090b64204040d0710f0f1450a8074111030045802080c8000b40f9100380342180180e6100028280c20404540b603983c940c04640d5050b10265800c4610985e0703540c000300ea110046110107504001051a402e4043c01c000740941d50000b81801100d10349480110540890a01c0c0d6005a40d2000007005012104e807083c02060700238080ac9034424200001510f42070345911545000601002991a00320301055180e404841c19560300280d0030303120360352414064110501c41c941e1a1040c0400200422158020010359580c04d0700706144c49605a4000c04400750720f00d0039102e0b0001d003c40c00c145185200048038400340601102c0025000d03090034456848501001c1d5810310380b194200a40a10072107600140c08006c500b01000c072 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 249712787 1250 249711537 249711551
    0xa0624090b0a230306090d1407140604030201060305071712090d0c140103291207090e101a0d03050307120509030717160209040212010c0f0215070c06 66
    0x40c40d40070194007445503005443d1114074018550070141d50741c16415401d980c11541c0710307a0307101d44a010001d41c00e4040380900c1826108011098060425288a40750403041e0100442c1d0b0305140c0300c022201200143e4441e4402d00c01c1160031f00512009200c070240d00d5408002c802d0209460f00e2240e209140c1130740b00802d440e080c0c0e81d54005403000c000d4104154603078968481c072461145100188074240868285486034050354030b0f016171826981e400380714409001c14581c0810030403000500d0040401e104000e008502e0200c1403040312030054140300100001001d14101034191140c2c40d40119030500c2500181c3c1541e02c0c1c4548601c07180d03034140381190381d035610303d202074401040c00031100e04c03000d1038401080340b901c03000001816040d00413921490340308401d1415400c14401c000d001042d0241c604000c1d4018100700708041e401510080030310b040f1011a590103070840e0004e02c114400516840070030200503030107001d0160b031750b04a01c0300c2c40114903000e10b01401220791500b004203401c2e030b5044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 249714037 1250 249712787 249712789
    0xa060809100203040f060605011805130e060c0702010215010e011503061a0702041a0319020111032b0c1407030302070506010b040f051c03080907030b04050a0624090b 73
    0x1040e140e90300400e001c01c6407642000d08100b041d6184043c0101c0b8200e29101c0c0c0401c2540c01546514038555a6180c032005840c180028000040840b40c401c0d00c00c83d449451a034101401441030b148180341c4141026114031890000a10f0b1045810315900307100f600c00c0050002c400c80100c401e06455481e00b4815200f114514210300402e12580801e200c207807550414107032b041c6440003c00d0700034000c40b01801810306041e50f1007900300350403040981c103510000c2186403041030b0399031138503142d401410071003610310900104174210340c024006c1e21011845915031808815010303a0030621001c20303450400140031032007000b074030b0401d450004103a001c00108440041500c25011200407942c4517040d9609560348084001660300b090040d0820856110000b1034242484c00c0e0010800c404002d04070b9080c220781c4c034190307034041019088000d240036081c2d0201c042407505400901543c032401c0148403052242c2046011262010711880d404010070652071401240d484c007031f100f80c502c02d03100064003501c224 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 249715287 1250 249714037 249714043
    0x60306060c190c2d14031f0b040513050a0318030f14010b0105130b0318190b07030b01170903190e040c031e02070f0c080d02011401050a060809 63
    0x2400d01e810480a80084000c200f5841c1c03104040b600540340c00400c490780090039102e048280e03040001e440141c0981044054122085812030803405401d580d50b40c541c2410074054180951408039580e40c503840c444c00c4c0b40c1064450f00c0d61203d03000703c581c100524a07548141e250007405102070100070b4070700001c03c0d00e504c56840b45801140c0c480328074600040d10b031501c4d6400000c4402280055480c202405003294080c0781100e00d0b00c00c0c40110210014107008012810740c0025154401d1003a00d4501c0c080b10f0541003101c446007010030480d14001200502d0f1108403030100510b00c10806003031060345c11869030442040214411301d8645500d8a44c0d5100080d03103140180007541d08845404446a89410703004203000318801029241403100c41d000e1070050b01030f10301c12001c01c02d0f0348041d4a110748000105501608003140b082c0c2d00001e440306552140f254410a58015200a401c035560210605030244030b40e60307142503427003070310761300d541c5440d000030300e07440300da02c103080034802d440340011f00d904c0c018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 249716537 1250 249715287 249715303
    0x601030221041a0c04091107020a12050d050918042d021201051501050307110706050307080f090705040f0f09081e04080d030e0a06090605100e0402060306060c 70
    0x120030003268184071099944464001903034143c07041c07100561003003072816503040002e10594904600d980751030b19004940000749090500909845070038442c4100594a1150290080400321405101c3d01551700307105051822200141d002c1c0310381000001141c1d2141030403851031901900c03911406039200e04008500c60b074140700320600c003500052011103092141035901d0381c180c000e40b1000c5504012401d905d003210400e4a41c2040c2200c1c1542d056083d42c41130009660040752840e0501e0ba500041c40941d141c100703d40c014001141001c4200101da0741e11000095100c0f40b02001d8100b94103145c5000c3d0b4840f00380317000f041d00680d101c454140440c00c0c0d6030000380040003014803c020f44841d505003d0780703e40008a00348000600c2207000c4054407034190941d2b0954102c0f402501da84603c0aa0640007803086081e152210b001d80e221840114045201d015040c0b1300603003001c2490301e071101280c00c941010390000b04000d1000c070103120160b12190180c80d800081901d00c40d0356207041440013460002c1d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 249717787 1250 249716537 249716557
    0x31e070e090f0109060b030c040302090405101416051e03100503071401110d0905011214070e0a0602010905120903030708070510050109090807120926070e040b0f06010302 75
    0x1d45400d11000e00559801141224001d480401030552149141110381c4030644803051107100030310041c00940b03466600035410a01c40c804a03401804414612003d50340c40c0c0e1400c10750300140004002ca03012090b010b4031480300c0c140c0307041c91405213100c2c00c8400c8a0002d40511030250710200026103058000303802030010342030090448080301e0351040304004644501c00018002050b0035002c4068180000704240c180700c0700d440b0703203c081d030402c401103900300b00e641814000251138081511442031002d107518054421a039a128542c41c0000612042c0c06035548a141160b1601d11250041080480e543da0024407040c0601e6403242008002441d50103103038000b51000c4c0740040c510742004000100e2a0031100c44000a208507a40c030050182150803140000e4554a0100900c40000ea40d007440d011262072a810100306154803541e003511807a02003500708594540c403880700c1d915808104500c030028014500007450a150a5456149514024112810700078022000c00c4c02a0300907019070b044424 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 249719037 1250 249717787 249717799
    0x14040f1104020903010e01050109060f180f090c0e04030915020304051207051903060b04020702010c020402090427030216082503060c08010311010206010812090f100302041a031e070e 80
    0x6d6114041402000c0030b1184079807841ca01800041c202c05010050343c125200054040c80c503040c0c003412000035002c81c8101c114034035510000c00000408a41c80341d0050b0440c1e00890b0b55030b00d4145005821107003190401c114148a586843c424603a00100b00d8041c1c1c3c3c0c1c1a02c0c245081011180ca0f80d00d021f42d0354000c00e81c010712a41c501500c030341031256508222401840144100c58042040c0001c0340f0030240040d0000d9841810140582002d40040c131580700041c10001da90140d1080c1d2051003030f220a00c8002010881e1410014103604012080d1504a02c103240070080b0310307248226039902e8005401d90b0764648486100d043c038160305600350b40150f800020a00c4444444900248514400d000c00c5450088840b540c400035440010494140c8e40040700500710684403505c4030240b500411865070344840d5606000b12103856550a1101850040d180561103d04002c00403942039980c001e021001c00043c000c00c24071031704180b180d0100180c0244c0e8104540c072a40350442c4c1030f081d00828030350409 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 249720287 1250 249719037 249719051
    0xe0a0e0a0507020601150504060318120816020304240c0501020c0c01090b0a09030305030916090b0f01020a05030a03050a020c010203041b060f05040b0a05040513020405010314040f110402090301 85
    0x144141c01480c880c02040d400c3e143c4607070300c4900d4100300d050342d0782c03081d00058401c4c401480058000d40c40001c80c290140032001d2100401d541c3c0720301c2d03d00d140c0c01440005131800c007880402e034107015070640144400d00280d41424100100c289814000203c11840d26031b0010702c03105010b00440841005035080b500070355171502807a50160390380001101c0e41c1c1c0054070703000000076107000c18400d0700c400094950380c1400c010f2441d18222030580015043c0b00b0640034414070b0b1811820510000c0c40100708031071010800b040d0790410070144040e2400464195000140c0c1540040c501108443c10300c100c030308002409442d00241d0170003e00440207808069880001800180311188504010f500000a411320605407140404c4400d03441c4800d100c404074800784000c2c0041c40d0907001038001c0022078a0058181a0358100041403840c5889100f0030b1164009802d00065a2501450307005000032035110400e4202999010b1004034103010180001400482104099607190122a881d00008000384204 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 249721537 1250 249720287 249720301
    0x414041e051e0c010906080f04030e060705010b1e0a030807050a0b180106090608071208090a0e01030510060e070f170c0d050f0402031504061e020d0f09050d0e0a0e 72
    0x482d0a841000d41d188200b80070b040042d80700f1000c440503a8078541e43e00d107080d15540780d039003040d01001e0401c90038071640d007a455600d40c8402018207000350140002244010003a01400006103050147c403c1d507072103101100b80c058540d001854100c0b07520010aaa48044508103103042c220800d800901800351041401f4890315410341e01c8004080600003004407940d1840c080c01110007611500070190420001000081e0304003400325010703030255001500c1c003400800060000300c40e0382c1103000c03960340d10070061061200801050848024007841040500d00780035600b65030b00c4000745220b0401c66940c0c1070302c0106100b002d100a402c50380c41410350442c14440c1c41c032001d82d04540707030300e07110342e807038540041c1c900140e11480600550300038001d4400c0800c02041400d05074801003050b1142900e50b80802c050846100e500242d40070510300040e1500c029110038001d54480f459a100e0340341c1080341500100310042140d051010880c10310000c402400c00101c0c080035055403082181c0b0080c10304010705 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 249722787 1250 249721537 249721573
    0x30112030305070c11010c06201b030f0403020906030a060e0f010e012304031701080a12051201050603060f0d0606060f05040807090c030e010c020a03020c0414041e05 73
    0x224921980301807000d640c0d00c00003120004424040a403401740489160303140340d409040031000b0903010348000704906045c02214071582100f24803907508054000b500014809003180c21a600030480d0015500c0d03c41640c08407e440d01840c0400780c820641c4001140c020342d020044003100030341c801014000e00051201058441001d902c2000d043d509011114440480620845a1004d40300da039007801006000701c0340c007900703400810031010b100700e45100b07a0202c042d500301c1074028080440202030300d030094035000816a62011070601841030030f100048a0720852000c0034103640d4156511078580d601c1c040018500b480c60070010350405084002c4000b8000d560f000001601c669449091101c0105a0201c50b944079510403031100e50881034050001e4031081e00078001d00003c51801060b5040745008407400c443c107040c1c0360409a400952002d0070181c0501c105a64541c046808024124030742d040000c0c44c8600400092010840075002c07008541c01c10030481803147c000381111010300b980004414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 249724037 1250 249722787 249722819
    0x6150a03201509060f0703020a02031e0d030501080c12030d0207060204030507050d0803070e0414091501090e03041e0b120108060c091f0e04020f090a0f0321030b060301 74
    0x4018003501001407040c0c0042400c94507040c030060489803a14511705080d502541110000314214003409800e80090780d420481000680181200b1800d564903100b80e02d8941140608190140340c188001084041c4010911041a510555048071410503c2600307a045105101580403124400b155540170302003280e015009a80c0703d40100c3d04401e032500c0400006400b4280002c004141c03c0002507201445078404850740c100107403001c106460300c0010b800c9603c408541d1078006038421000c141948070341c011f1141c01895050750411143c3c02c540340580d10b070b10442c00b4601e840075236172952a4000c810f203200800140a4245034a49031407011600d825000001e209041091082e00042605d10602c001250710311900109009581c0081d03410580c8100f00881c4448244100c40300c01000c0380c0c841e40001c1441884000d03c1c141e90b05c00004c02c001010281da0001144288800c5050002800b80c41c9510318200c0850205402c210000e02d0131405401009902500b14502000028003136146008101c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 249725287 1250 249724037 249724039
    0x5070803220806130807020a060e04150b04060513050405010f0e0a020909040f1e030302030907120b0c25050607091d0105010f030b0d050607020705030d0206150a0320 73
    0x805100703041d90306200d00300d5000c1c5804030b410400105140c20710310b00c52500c055200781030003410540700e500003414145507640494086400c200c1c0140c1e40d450a031007038000b0040140040000a82006010121401907000d42c0f000d01c01e0008100d43e2240307065101d58001c2a0003482805031b0f41e103c0c5c015001a118906c141380458042c8404550901034500958403a4603000d0b2641d6010350351510780741c0f511440541c0030341d01241c00020755496a01c3c48203484518601986000d80d507800e0446100d40313400c0042d030100d640e000e41c68100b81c001034210080f13a0b82042d0025100340c5c9030041c0c451030000c12030b480080c1c007041c00c0c4402814400c10a020131101c2c4112085d80303401443c6039071900b03690844060b4004000741c002060700140140e40c001c043d01350310700b00645400038911181c00081103048041640a980a5126400f0042459810841a4081c02080d0041d0560b1000500082d40c1e4a03009001100035800000c241025a202c8100c048020b40d00501e8600c5480c00c0c40381c0d50f904200c0003803141 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 249726537 1250 249725287 249725317
    0x5040906031a0c281707080f06010f0c080703020c0a0e090705060307050d0c05040b07050f10110301030609020d0b07030209030c040b0d110604030b0702030a0f09050d0803070c05070803 81
    0xe400d040300c003401d032000d45880f82e00040001c00010410513403580b4842400c1c0901a5446141c0b0100740c0030ba1142c0d10030b1200b501d400000d410305201c46041c003000101858100801d0b4a0300f604c91603803103044828030550240c186a00c0704424a000c0e4108a0980300c8150000c007841d000140c454041e0002c03500640c241030540300d0150702c03a01804168442220601c01044082144101945141d80007a03401600d40c42c00030304040d01c0c2c5150620680c0411070940d4180d01c04000d20300f40c07080030b101e410f4440c1c4a502c010414143c02d4036541d03045000500c0080c08455940d044a0255203c140b4400c2085501c4000031076186080303203002e0000e4020214485c0240b20307000e451a12828648030340791840710010481100c640c4195a0b00ca1640c446c0b0001580103203040c4030001c001090030a01501a4507290007440d194408c03040300070704011510720404100065608100070316100c42010219540c0c04c04c0b0040d0352030342c620009550100c5504001030051007068800514558040040c0103c02400446 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 249727787 1250 249726537 249726541
    0xd021615110a1d03070807050f040504020a030f050c0910141021020408030a02060121110904020102012a0908150705032e050406080a1a0705040906031a 67
    0x100508441168400c907201000070095003103420701811503040b03107203071410502d0f25031601240400e0425a00794080e010b143e01c1800c1c10f000070710b010740c2c0b68030b1044005e840c00c000c0c0d450320b6000908683e04d10702c4090444500d000c840c00078408140081d0f860f1900c080c20036001405c0036403000a0903980c2d0b21800c0a1480c20b6614200305142100015a4024003035844031003031003c01d0600094500c01d0b8072000001c80d400c100000d444c0c80240003401420381b0341d80282c03107190301d85285c620520b452418062201c2004800a100140c010030141c40381c010b0541c0c404955036500d1005078010400004210340307162003440324501e68044615014507100c803039900c1312100c0d503a07070304d05039a00d00d11001c0070b000c0c4115100001d404076100b00059540284101104882580c0a02c448888004507101107059210301d04014005030415004410045c41d0000007005044020340741d00090204004c80c10307250040160100f440b4910031425180548054801003003c00c0c0d880c904000080c41c400d5082074440c0d41140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 249729037 1250 249727787 249727823
    0x821010e060303070203100e1e0d09080f120a050d020d0b1f020703020409230f0615030d21020414030f07060212030402010c0605070e190b04060c06020d0216 69
    0xf0994000b194040c004040c80c480d804a504050701d502c40b540c400034400c201b0520b54102000c02e80d030001c04100d0010700000503840790f000b410303496550000710340b540c00140c030032040b810001400100c01d00011401a12030103150021640d82c8250003040305503a0010510070458005903020720340703031a012203101c4407003140a055500c44000900710200960000581080981015089036092901c118001c2c01c002c90701d0358908030400744a15a0041541c00000e82180400c6e00b000210307080126110100011401000026650100c007460300c42000031841d1034450503500c404c040140390052000644d10365844205c001001c604140c04c26109100306500c980840070086107801c1a00d265901030442d55034660011102503001400407030400003100410004911144261409560740380c1d0717600442410442000a1015002501c0e1110319812130b00b0004040b040c3d0407501181c24500b00040b00800c0c0341402d10080c09a01c80340450540000f0351454500965810a0032141c421882d540030040841 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 249730287 1250 249729037 249729043
    0x1e0d0806090c040e09010207050a1202010c05030412031d0304060507020109050901050d0f0f15050609240d060e0a080304140a05060103020d0203102a0e0f010c0821010e0603 76
    0x500d010504000c00c0205002e05640404c2241d80b22070210700140c5042c09941d01c6914084600c441a01d80d046000d4050342210380c20300401d4000041031801500310f0820342c07251600914600003a505060307807990850003541c0c20201999181450006403078645a030303080d0141041c0d10011040f03000071901503001c151468102e015038140c603070107840d07a804c48a4907998030f40b080c405080103a98554040781040c0000f1083c2125030720302a2021400b003142e040000500070fa18001800340e0207002c0d0000d4a40d204071710301d0207050f510700d402203480344821113860805400511002c00c4c0341c1070b14010454440300344000c0f070000b18040c80c400c0090070701c9030142d103920342e8036103440202c0200503412030001000546880c07041400b1071400102618101803001038510200c60004052649004424405071620000d4081ea2500307061a401e11401201400c0006074500e480020310034140700c0c1062860b03051154060940f1030642d112000e111b0308030001c2c031070702d07070041000d102c2c54508071400c500040f8641404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 249731537 1250 249730287 249730291
    0x90b030a08092803081801050c0a03032403050102031b0c060a020d06090c0906021c081803040b0f070204060603061412160303050c060a0b0d0308091e0d080609 70
    0xc200a9030408041004120358822050340c22140c08414040d041c0d00ca5465a0081004511505c5041c1d5601144400100850589111507051010500081103100c40c003145500748a0343c1458001100c0c110001800705000c1250000e40441e1071714800482004015030085020340b0301c000802029180695421010703204450000f140ca802040c085000001ca9030080d0000c00c0a041c0c020542c0354403065007030101d850743e160b00c40000303000300340811400d07030140000500c5c1c2800d00700f6410141152400903000b401c010f80300e100e50458015060401071030034801d450203051088402d0381d46400750b6110031b000d5004200103034811850440c002943c80c2c064460030003110302c00200200329140036400c0040d0084100040c80c6540104905414285c2035039400c2c0c40618800e07240d16031101c6900607010b190080007010104003030f00d005c2483c030160f07441150392800035a0514044120b5512400c0d4541000e15181100104100c01c4100002c209800701d00c1c0e0103951030580c0d42c40072036034907041003180d60345003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 249732787 1250 249731537 249731543
    0x6030c0303040b1c023105060c030a08060d0614040b09070e01090902030705040f0f05100302010219081306080601033804060305030f09090702030307050d05040204091407090b030a 79
    0x82241d440c541107045408080c056154000609190404040c1009040160b2a64040c0e5086c04294030000561084002c00b800c41a100c090a126641444035540c0c402c82400b40300380110100000c116070f452808103d0803607400803060166200c04000c0031032400b020784080380e103002e1890004415070720004060085071b004911003032469207090917182c01454002c0d001e0f6054000d0104c0403580703450714007640c02c01600105000980d41c202c00c44070001c480c00030303180b0040300d03100c00000c1015030b070700143c0ca0208580c2c034004050315560b5071400f49050700c01c80c85c5c207035800c011030314000441642011000d4800c0e982030300c00748101440d07144001c01064042055040015070407000440035140740c800c0c207803c01f03005040000c3c01510380d01c1d4645580c00000d038003849518002a4441141001900c541e00030700c49000031810f6003000c000160a41c01002c1c5142061583c0708001010f650ba1034020544c1c1c1d5801100c0100361891541c2d00507140c2c00389002ea52482401e003241c00e0344c00d00340010060703003242d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 249734037 1250 249732787 249732809
    0x906070c03080c21070e040b1302030601090905070509040506010e1e06041a070311030408071211040f0e0606030703030e12012009030705040603260c0a030806030c030304 75
    0x28140d5002c1d0307910341c40545604010401440700c0224001c08105400c443d600c0c1c080381c0016458001340080c0004410380c101c0e8012401c0125202c0b4644410f200740c484091009000741c0c0301d03a18000100c0f02c07101154040b4490904140600030465082402400c0320403041e9010b100c26035071000155082001e0f11221500311030704011103401105c0d0344e80e4911207200002c003003034070f0107648031080006100d50f56000200c041001408204160b004411181d41142c2440903608162820301c2c20f5407528a076102d64400412080e118204001d100f018240000c24000d1040220340d07014081500144400c0b044882ca03440b40c0b10200760907240c0006c1c0c05040340d60666521040d020325509000c1064038a05819115648452005e25003001251900d40c0c860302c04410592202070090400d441c0070441e42c42640600d28002050010450fa400d003890341c900001d03002e1007020b40d08e101c40d250b07030702c56040310f01c0709802a8441241055400042207006407421004c035a41c41445c0000c05480303204621650345900 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 249735287 1250 249734037 249734057
    0x11090906100e0604030501060f0e0405120a0e040216061413020f0613032405070509010e010e04050a020d0b041a0108090f1009030f031b0302070203070f08010204030506090607 77
    0x214021039003071414001407401501400c500c0010038000c1e0001d410840303059458080600c6012010b03e0448000d2410000001c61420103403100c40e00c40d518085014502040024140380e41360044801601928000e00304540d194a15403800f000090342040455456040040c0085455501d07100d6a01886c040030341240c0c1c02120fa400c00007a0700802d6207054210b1001c0c0b00321314010a03c8074402c00114019040c551205e8000b4205800d075690015405032050301e4002842456031f440010b4500055003800e184940341d00000c0181c0310001110002c0b540141000c04001003105541c015010142008805004400034581008207440c0413504400039403801000300b46240d031084107400d4000311074000f614280c544c410803850034954400c0304801e1050b1202c0000040507070144052040b20514901040105a81d408140c50380e0280e42040040680100c2c0344800d558040c45040c00912074080e010100d80d5032000d00601075017140c070054409005090003e0001e03003001c10100d10075045503803126954 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 249736537 1250 249735287 249735289
    0x50a1e0902010c020405010902071203020c06062808031b0a05060c0313061407080901090209070f02030c070305160609030c05060d0905031824120a0b03100504020411090906 76
    0x102a40c9400340c0c10810028801400340e129481054003a1105180160703840249081100c404054059002d00701881000300c0348403000041101508250121100900110000120030b40814031010040c0844004080013850550000040c10340003241101802d9040c102003c031901c80c04030620203011a042040000c1c1148072138002540d12500c00300c40c0042d82c0210780ca0b130400301d4000141c05107403000c8000501180c15006400320382d22481c00d5000f03001c19aa25408a21482400b900550910414208004c1918001d100780e62040140604035140c20356a800d0841e41d0350008200110707115500310b804580a885001e240040e02d03000440c14040d68030300b0302484882d611006800800d641d40d5040b4600080081c00104082d54100c07146501c5044500100805d4aa5a5080c40e0211a002401d40c545482d020103440c400b0011080d94092076403000c1050003d007141c88852640b60081c1595115205003a62100c0c0c082c40c025602007081c0044041d2881c1d081c0300d40041181d001480302d000800d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 249737787 1250 249736537 249736541
    0x7030b1011071404060e090c010306090b0102030a0c2a0512010e0a0f020a090903231e0702031501030f030212090109210212010b090a0203100303230708040504050a1e 73
    0x500d4000d0300c0005c880c1e90341c0044410512050354a4040c98000490405196915000b01c1000d0704440d94100034401300c110000c0c2d564031a002c00b41c42400a4504d0b003400f40440c031201c1c608946480304c08080384031043e02a0003007c1006000c3c1d00c0c854481c0d4140451a110140700d10500b0a40941c001c01009000c0d40716000155540b90f01207038007010640d0080780c102118080d00d41154840d495000305100450031900040701c40d0b02c152031802d541445100310317650705844205207003109460102c0e52400c41d400400d00b04079255000f0340c009040d00d4000820800d43c0c2d0070005409000b41e080c3c0325500340000d074022241c440c0449540c001600f90300c0c240701c40c1600da03403a507801f041040080040d5076203550128064520a9191110a0f5910741100300e40d41460b0b803200b80d020404440851852525030030004000c9a2070101030100081e20609a42c08030448601c240f80085600066480b02c3e04ca1030034814561060241500490404010400729903060041c50a41101210102c040014002c03501e80 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 249739037 1250 249737787 249737819
    0x702010c030e0102070507120c080106090e0c040c0516170c0307051c0806060f0c010c110d090b0f0901050d090f02270c0903120f030a0605090114010807030207020907030b101107 78
    0x2480388170030302d400100c114013403203034034000c3c040c214dc0440c0034146084100e0510140700d0382c05004501f04a242c241e450317448012540031100559922140d88001e05000301500c1c0c4044000c1005400022a0700090a000001e000102c0c400c2080300d160708125900e8440c00f502c00f900c80400304148101242807441c2460160210752101000903060900b81c44581d400d4030f0203c2c2d401808102003518914038890180101c0140d5005400c2c030320f9080e4034041c41c5800a1144400c4405803410125400060b40c1c414002c030355004c0308680c000d00030b6038401d0400c012054508141207106a401c407030203030b0310405201260744018520303074111030a641c0d5211600d000ba078400c600c640c0e81802019419151204050046c0103541c010803221522840c240c2d90700000c440403600050701c0303a1980c100421500f0034928408480c42428a81032406481c0c4c0603042d00070303004145001350b000a41c030041085250703050740f14929410342140d1041700104810010745840c0c5807845000d100340c0082009204e0a40c0f500e011913 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 249740287 1250 249739037 249739043
    0x1b070f0e0403030906090f0209010b040b030c1b0d080a0b0f060a0e040b10050c0d0504080703060b04201c0c0e0906120105041511040e04021c0b0702010c030e010207050712 75
    0x2c500302c1219a5017804032000d02500311000d0244018020a505040440c24090504500300b0b81c078003403d2017944580c80c00001c04021050b1400540e0010071211a101510a05185000ca481075007015801400314003013240c00c411406d14000346240e47c0d180003070441000900141c044c6141c201c240c03000319441024000e440b41c00c1615072503042c1d025290604406220031495489507200c60110a50a0628000d11141c008000c421300c014080c0d0380c001b06409080b00e03404000001c241040c0000326014000f1031161400c0092480f980800d110415001400074003802d5580100300b6007040925400c5522801e5403100203200040c803d01242002c1c41c4c815000700008101508004024401500391241282d048800068400c682d042061071401044410780640f59507d04040c189110b014107410001d0019100c0c0d018803002444801607e802c2e0700003035030480101d200c18901110042e010340b10380501580024900b4860402c040418800c0d540705aa0090107015400d1416414814203141c00e0019 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 249741537 1250 249740287 249740291
    0x70b06030f030c0a02091f2d0906080c03060f1302030c060316020f060403080a1e060b090a05060301080a022103030f1602030304120f0309020607081b070f0e040303 72
    0x3004407402040a4800b03002004024075039a60148180065400c0c00352103040f0785400d8602108010300805a01030564002001266012840c6d24540e14000800d401484d00490750303900104a9946a81000b81656210f41c00c503021010070310180b41e5039039002c40781e03184d0304400c2c03001141c0a05214002490094001001c44120f000e201e0300142099009072181494000c0d410b104010b03031f64060100241030001138000e40941d180030f49000d0f21440009000c0c00d00c06079508420f04848045c2e44c051218202c022070308000054451214a032198011003030248512240d113800945880e201044034140c1e074041d005080d84c07078902c0d400d100400710b039502c08004131fa16520740d100f05214200007940c4035000c0d10720a03031a030341410400c0e002c030740022a1419007150010010440885d01500305050f00c021117180c80a214894414120020049018029480503000031100207000c00b610251640341e82101401d47c20903016018540c0e164200d1045c1c0d928510070010401020000640c0c10740d1050180c140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 249742787 1250 249741537 249741553
    0x20703060203100504150b03061c050a030809060a02040b0d1521061404020120030c0d0908060105060406020a060c0c020901240203093f0d0f050708070b0603 69
    0x480d0203a810864100032410a2440d0400c607926090044654148031041040451801c02d11150000d01c802442e2a01645048100701552542040781d60071444c7c120040c3c40b40449640b070000d04002c000c2d6500241e901c2810045101c045440c03080340e04880340d80494604d403605150078200900b4031203605e490104112403000400b40602100c440c0180e4036030201d88415886481d24104442c411102e40036454110b408000060740c02c80800380f0341248011040d12502c104084d038610718412000341594a00508102d00c08482d00840a00306840d56030050f602641e0b220001d01c4100c0c0214801d400050b4085014000444c5a641c0301e20070744c0d801490040f044032020b8021440303810342a8894000051509010044280c00c0103942d20070380040d01c0650301d000308010004500300a6418543d16000e138403660b00500307900044103080034414904c4004030a400c00701000391070700c1d07024002801003400c0b060b01c43d10751486041140c80180e4020819030403c002e0762900310407250012305858062084c202 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 249744037 1250 249742787 249742793
    0x81b1c030e01022802060901060b0403060b0f040c0509011b1205180d150b0108040804050f0303090a0f030c0605040605120901020c2d01150504090c0e01080313151e020703 75
    0xa000384e03254044040e020340032282c52030020300c0d004000f042d02502c1c0c0d01d052000c0c0462030003101181e0442e50054008a12840040c00003401849488483d0780d0091600c120001070a4010014105c3c0072026201c0200c91000c540030084e100042010042020510b4508140032500500140814050099204680111150100301c007900c80d2041603400082c2040d103400810300740c0c01001c00204081ca04200d543c00c0c0382d555581039014a0241500c40e200303840c00384001c3d840070001e440d01c0d8140148481c81d06983c0f0600e002c0000c500b0300084d90365004400000c42d4060040c001c440c11244143d07a8103142c00c0070700c003c5503c0f860018041145554007040743c940440c008002e800305810035000300741302100c00c400d1520398010051040700c04e0780e410488905040180300400000701ea030f050303c01090024032460200030f09031030707500910841610306d0000706a000000000d08680c1c80d801000190b4a0b803660104400108505e82c20b4000800003850340c903000000c1c00d4640403625142c01120307443e41c0c80e56 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 249745287 1250 249744037 249744067
    0x302062517040f0501030902030c0405090307080f07030906020a0503160f200109051206040f0c0b1201063b0a0b041e06030504021507051504081b1c030e0102 69
    0xe11100120740011609004041126a00d03200806090804000c0d02003e5800b00740c4400e1250710440c460340d6101c0010380c80e681d092003144d001c954842c0c0c0503640d80300b04c482c07081d0142e04041070603000580340c444007103126800001d103140040e8224000318240301d03004c009a0401038610300100e454103210360f0b41a00051490b2510304610200d030404413407580f080c10006282d4a6180d000501c01e80c82d030240140034100c00303d40c503070f042508102901311841c10b5042800c1200070f2030784440021800002c1e50030360003c210744168140c80b101e544482c0c480d02490408040740080d1030300e1081e0045d407046049100e4540140d02c02c08088040d03c03503102070707a031000b0940007900168488089019401c03118094244203440d41b2000d00201c3c2402c111500301034000c514001d425204a280307090f000101d0000303002d020042e092031004080e10100542c0380c54a0070707406035089049071107296241d402d14004c0341840880c1965602c002e0864501d107003803213542c08801820300c0140da00715a541c20000f5190300d070003407 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 249746537 1250 249745287 249745313
    0x103090b040501020c0d0504120305160507030c150c0816111c0b06100801120602040b0703050a031d030f130e070c02190810020a02030c010603111903020625 69
    0xb078000142c4511700340801c2800d0100381d007401030800004101c24071210300c0300384081070815018a809500c991100c20000c055800340100030b009440750810010030016100c3c410400d45030b40d00302813018a1390101040e142a40c64100003848044240202c090700b04034007000070032903401908141c000066017030101c0c14500c8892243c940404650030241d0600600c407445503008a800d5406456000808100401702034040c040d10071100c8100700c146040c0a243d40546026010312040150b5400c43c1e03160103080c13544294204408a03090042c0700f0010701c040e5164070714110a4102843c40c11403d4025400b081e44044a000c00510380040e010601e0044082c40600c5501c00392a01075119209004108088250a0311480b1241910209000b0707004086469018000f84540241e2100c14000c010790643c004c0102c180c000d9840e0800000030700035541c10140d4881002e484000440b5107d40300c103011903030a40030294000404100c410440c40c00e15104c0c9100038500700c204100e560b803503655240c41c0144 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 249747787 1250 249746537 249746543
    0x31b080c15060f040509030d061401030b1905130216120e060c0712230d030b010e031b041d010905190b0619090c020102120702070b180103090b04 64
    0x40840c6040301000100403200d50051502841581880e01a00180c040700c0f00422507809691100003140f03104c0e20070815160300c81082e680a101a0b6254000034190a08181c90795000a041451510503030504a1102c0841c2000b60000040e260406003071104401583c0d201c2c10485501304400002241b0303040d03100b1505480f8082d040c1002078010340040c284540d25001a1041c4020420141b841c078000031001d0484005052100b403c0c21581840740001b940084c00485000348000c100600c1a4041400c040d42d8880ea1420081c5511000046940001c510300035905540702c000301036002020015061070052b002807000ca55502c030400a0515010000300d0b1840581d11880000100101885000340a03c000c0d02648403440e030f141c5640c1358100020f49001d000724150a496010700045172400c001420400d0000d210151018034000d00070761180140901c5d403200c1308003155800c1d02c0410b0b0740d030860b140d0406c204d08000900303480032000d84201511038103269940c031801c0d0010351025102403280740 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 249749037 1250 249747787 249747803
    0x1b0c03040f050a060306050306010326121f0b090d02120d0207030b0901110d1d06011404050919080a05130f050f101b0302071805100801050103020a03030c031b 70
    0xc5002c00340700b0401801d0b0421400e160804100307000689000901a044a400200c948031401e81103030070540c0c0d0400c25040c225142000a0113410340d149164036070340100003181070720f0040c82c1003a5010222000d41e00a00c0d550800800000c40e882c580390080c403001d903000401c40030201c0c400410043c0740c00c08480c1d155015070070403141002803200304200c0c00d0784546100000c1c055907a04001c0807190b803140440080714035598004140901d10b420b9070703000b455004070084035070f9546c45c1c440c120310002010701c14a110300d081c2000186000c07030110311024040c43e0303040718000c0720b030395540e5080301350f000340052108002c018001c5c45840f04100102c80c0080201241c00c620326410002401029210b44a00c14024451001d1501880340d0104140c1025003880382450400f043e203103000c070704081465000e140c000b141c0000b42428820316030300180c020701007144540002ca07611355400c0d0903034500344400703980f00720604003c00209001c3e40c00c10359000d01c28078140d211206e2107610386085051480c003c0c1c3d0882 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 249750287 1250 249749037 249749039
    0xd110d06080c24030109020f07020307060306230f100203070b010605040609090510031103070e16080112030e06030a1d0703060c020c06040504110408030c0c03010b010809061b0c03040f 81
    0x1003010700064030f40f04000070f6907404000d4580f55121403807106204d04559182d0001c0c0d1a0042d40c040303001e6860156000341922031655036448006c0192401703020b85090203101c1007081080320813030b82080c0400c15018100071102d20146040048000810b081c110950004010a400085840c82880c1c0070749070544801c0d40322402c0503002000c3e004150420400d0503d007605011021401e0042d504c2100c0c3e12403903209002d44054082800e121407540041c1c01484c048052001080c02c6e05120aa061440d55550115a9844005003403802500501070042130000001d59004e042c02d0006503030200000c00081041322910100c48036003c40e00c100710030f81e604200d40a20400200780140c1161803020700c004d000c02103900d00000e402c2d00c218031030240f06e02ea23991030080c11000d10f0b0b070030b40d00102a180c05680c5c581d1070304404503840758048852144654130f80000310348150f001d486094028000c02008040c1540c4031011000303c0600d110841c1c460381c0c4140540b03502a101000200301a150401040c3c0d852 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 249751537 1250 249750287 249750289
    0x140c0304140d03231e0703020d020a0c1106030f0106030504031704030e0102071a160c05210f070e0c0a090f06030914030406051e090411030115020c060d110d06080c 72
    0x1480d603981c18a44000060f05000503201000003440c115842c400c2245c00a4a9400c800d800a100b0725035040c003064000f040c0084490340041a02209501684190080300d082c0360400059110807908400c050603503100610078503110b50f00c8194494804d0821250340000021640c0ca180c900300ca04a0000b1483c0d483e207200780d42e040c0301560040030402240b074507100741d0f00441d03c0d00307000e004564a00002d60036901c100748090f1400620041c40301815004111400c846d40b40320b0002c3e202d400c2c040c240f1840e02c441440000026450b400c84158815081142c3c40302c02d5a50341075070002d0400c80c10031140d000c000c100340514030502170040085441c000b50035001440c101c1841e00e19011015180c0e08180410003c2c0782e0030004540380d107485d203c014012680a480101d840740180d1074500c0d0031518250040050004400c001d40c180c2e11315014a02001d500b00800300e035500101175a443c5c005000780b12803121b02c1034540059070b400c2c080e25021400c01a000e1140e03021150254408610f40d80040d17406689 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 249752787 1250 249751537 249751571
    0xb0d080a05180915031902090c0a02160801060302010906020a0305091c06050a05160e0604060c0c27060506130e0709090e0d0e030601120308060f061201030510140c0304140d03 77
    0x202d01e2400c1d000504c02440350f00008d00e10080185040c200c44800554500440e200b0b00c007001c10390300d100052940c881c0d22021898021704c003601049011810000000c203c40303000290a01c1079990643c0c603d40f1b060702c884c0900a040c50342036207130b030030740354504110400095444c002c00f40310310040f039000511032a0414045501c0c01d00031052109000300342010b456035403541800c9805444480c10000b42c480d80620302002541200d50003090340c1003030b0000120a8100403010107200010285060103215281e4041191900c038030300c4001140003401c1002c01014046031360b234903440300150411000301da90754403c640a6843d44119601d10740c01c00318940c0d1641d034000d182400e002030164000c000c00e40c180341300340c09614900140a01804144c80010700150f031307001c0201d0444030002d4000d80e1960741d040400e43d88907600780402c076000d0142c040c81c401d8207400f5101c3c56684140c20030444555880e0416008010fa1002e441540c9409401034051900c8404122058100703280c2c1d035000600c0903a002200107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 249754037 1250 249752787 249752803
    0x607081303170c040305070f03050d030c0219020411120a050a0204030312200a0810090209030c190b04170706020c010905040525050d0b0d080a0518091503 68
    0x14a0040350404001c02d502c982c03041409210601c800b0065120310491004901581e403008209214031440480d05128400040088911a008507559400c60103001e6050381c0e5215007020060b400f0144048034602551000340c00c0500142000407941400c2e501d440071075200c072503007000254a11090159000c0d00388074255101c051030700304504003411a81c005103010440445410820b84a50704000d046511904100c6894007543d1910f41c1c7d01c50032040540020300446c4c2c030a42d00300f80d081002804110034000c5422410f001030207441c07605202010000b142080c40e2404500582280020440482d11030041c0081c01c4420f00c0300e0302510080810310310b4801e443d04500c0845d00010701c003514a9030048001c4003542c0d0221804034103603541c0342c810280a60414120342000042600303400003103411100a0204a0f840340c8240801100501809404c0d80c00c18030040689104000001308180300300d019004405031038600500f8522031b8400542c11501c2030362603c10b00c44040031314074a0341c9400c1100203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 249755287 1250 249754037 249754051
    0xb01060c14030708070f14071d060f031c090806010605040509010f05090a110909042009100605030c0c030403060f060608160f0c1401140c040806060d0f06050405060708 74
    0x145020f00682e0340c901c55004218008007140c5079490411300308243e29001e030051040a100b11200300d5610415585000c5d03198001e02e0134401d6120100b8000c2c241824020700492000c1c00a00c55141b88481a0000007201d101c1ea00802490300c4020468a40c20b000e039600802e51981c1e0a40c66500300420003003107101c1179001c80501900454104401d4480c0380e0110f87c4841a00d9002408400d0000b000700342d4400d45119607031010034070b01084104041541c00c1800d2100502e0490680c030b018100784400420159200030342030402d9502004024440c400855100d11910f920310b04094560800e03e1954000790001c40d20030380c0700d01040c4182040c602c0351200601d035601c2d0811f81420b1214160014004903455102000010300031800c185002e00c002585072603004001001750b00003514070a0080001d6005000990134450100718440d07011015102a644203c3c0070300016111502003011003840210216100316481c141b03a0f0201d183c900c41d2512450041c8060469440d00380c50061425800030000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 249756537 1250 249755287 249755293
    0xf0f180907060f2a120903170a050304060507090503060a021804020f090f03070521070504090309120c12052d1207060e0106080a15050f070c0f0b01060c14 68
    0x5004079440004d2104d41c4594005092807080e10b0380e14800f900d20000c40141c030f01e035501a11807241355807109022084900400845542c030000c400e032417086106a81009000031414000320300459055030085400240c2d81c101030740042e55420101e41049004c50b1110030b0347d5404242140c1005001e8403502254004a0782141340415665040f00c50340200c0038085c0c0134002d0613124119a840030040600509030040c100d40902c0041801400b20810002200c642c90040360000111800c060291a004030b0b0701d80c503400b118608004841c948a441001c054441c501444070005241c8101500d0030310050107070f0007401c440c05010070051140026071000309510111365040c1c0b80e4041c004a244986c4100c0c18952540e100d41c64203024002c1d0103801505003441d482c0603030000b41e034607001400020305840f600e04c00904070b000003804000c4500403141ca0841d0b406102c00078103114131400503680b050780304281d40b0300d108105d9192150032600c00d82001003c078180d0000501405186038260784050414801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 249757787 1250 249756537 249756557
    0x1c11030910051c1509051e0901060f12020a030b090703120f02150105060d18051b031204180b120d110f1c08040201120908090a0e0405060103020f0f18090706 69
    0x3101c402e82ca144a502041513036240480d0387d02203188204411043c400500d80130134101000c505008003594400c122030030120240004401764540d0080c80c484c2d400900084800d131440d190f0742902c1000910740300b51750013400300201c001111134a030222212581c1e90b40c40a200c9807507502a01c4c055600e10300c1e9541c1c40060004000c2d95650308111a054101598040341146071420501351940c0c0c0004010528024500c00708501c603143c400c1c54414581c124200c0e40c07a509440000c6d8403512450142002060b001b240030011512990400700c151007014020500c01c0c81c1d10b0100a0030183c161490780c00260002d0f04004c50031700d042080a8422101001402168400c00304203401b00030202800e0041c0b0000d200007506581c0a0a500310110300d210b2800c0c010420380d458040482d07031008140500c600b14003600070803101c070f4000285220300d600400030305150b4215020892042034801442e039014115810a003510744480c80c03000340884001d801101c450a10419103800c100d041d42204c1d04000c100c080c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 249759037 1250 249757787 249757811
    0xf140a030807210905040e1c180e091c0f1416150902030c011b0f0c150302090a061b02040b12010f1a09061516120f02010c021c11030910051c 62
    0x8800b00c00581414282070140a40d200c42481c9c803099805a02d50621003810418a0080415101100c01c8114a002c0d00e034612001c003603d241ca4400740c0d540009000300c180e10b100365a200c004110641c05c01480040d100140d69680d80701441002c008824181c848a47c1800c5084c10401102408001d080c01d140010001d24400000441c3d01005000740514003d0311003807282c00c080b8130002c0c02041c1c15411a140c68520080d010350701800d881c1d401820b24040004050703206030030f4181e010fa18105402c01000440e020800a484409041030b401007540c141c843c00201e00f4840c2c07034684403015002258425120b250424001c072a000d0660180e2211303420010103950705084440c5000400800d0b5844500c17010602e507401301085001401e1a518448001d052500a004040c4000d82c6e0303802403200d003003c0c810407a21040144161007042c1d207080c10146449001d90141c109404110003141e08049000c0e0000c0c0ca40407034421803a02159000540c03983c641c40c003510f0280c9204450030180b04045081c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 249760287 1250 249759037 249759073
    0x31505010e090406020c06090318010507021324080d030609090b070807050c07091a01020f0316050c330304050a0b06030c10090f140a030807210905040e 67
    0x101181d8840c6031082d001904012096064915058602040311102e2502e01d558031765a9010300d5250494059480703100c03c3c01c0d84640105d031304065002d0040340d110b0000354003032009401101d01e0400480340241c540071401d00d0440415000780583d400801608035980005012558540c2002400d02d0400c000c03030004c180242d414540041c03680c03404005941d15844d003141c103406980446800c80c050841c00080c0781950380c211070540c0201c0071000200e41404d800591355022448003050b0585c00030b10040c006d551001c900002440d0041d4240c6100d02810350008120109140c48411400702c065490404d200031014400030103000c992515103035051540b11907030b95002151000780f004d030034000043c43c943c50500c8150902c0e040a80300b10303816030a840010b8540303a06030003507071501c018400703002902e0301b1000755076a0310300b00c00f5142d29041e030f00710740300c050346907003d04402d4a1661100203801e9503424003821808600c0d0b400d5403501d519a090a0801054811601c981d00c0c00b40d20086407560008102 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 249761537 1250 249760287 249760307
    0x322060501151e08191104090e0604051e070504110a0305060a03051b15070f021c0308010308030403020a0c060903051b10110c10030213080d021c030f05040f0303150501 74
    0x140c02c000c501590781118400b00c000c5170040c2e650303e40c0d06022030426007015040142090303403001c51050098a80340861650303035420450b0050415808802c41d10741c000a5407035000703031061510040d9041c40b070716100424180c1c3c80034580c2082c400310000d41004650b51501c03900382c028804a488440c410720b50344990707680e00800c6122218030b580c42d950081655450240c90350340c929580010584496043c03c02e4940308400396000c1c0e00441440c0e80e505201a00000d030091000d9041e1600680da03402c40d140c0d500c01d03410082c021800d40c41400e0211012400801021000380040c0d0351f035940040c00c51400303c0c00c3c0b5040210100f109901d032032000800b035a80c0f007215010b025461509410f401404a0190b01d80045d0a4449410180b214105100030b90b05070003d1554180314034420030740b155110082d40d41d0328010000c18005800045009440c1e8040d002143c0154181d4500401c40800b20079045085032001e807000c4400040326401601019058011a12040226090f194415190000290905801c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 249762787 1250 249761537 249761597
    0x2a02090c09010509150c010b01081e0a0212010e0103050d02030a090501051e0301060903060e0703030512041a0c030a05090c030705010e0423040c090b06090105032206050115 76
    0x100c0c40801d1a48210305641d0b2a000c01481c80141d0410340d24005440d40c00301071a48115400d081d99a6615401505280d00501585c3c6003e880d401b007040e42002c0340ea80241c4100d0003503800700000711588801c56129406003074500c43c40f0b082035145142084c40c01c6500340c02e0000707542052102c0c000030f9410200345412100d0a0034003696642051000582031040c0c056a4603040b400480049005a800180345003580d10a0702c0412425800c009400d540d441180300040015404104a00c0000e41c1d80e910a41c000c2d105070f00005e0300720f4100c40e2018554500300c40300d806c00c0f940130082058a4a00740a03058008071320b007000e01301b41c5e9080e90104e070300c0340964083c1e181071000c241c03410354803030322598844040302c0302182c0f244d00212600d00f446002c400060300c0c15140811402c2011400e4003491003880080c803c02045985400c044c000107543d21b0304001e0014003808264582480600c4410355801c01c80b61003418001469810040208600300c83e0144282c1040a55041c001a10942400b00b0003002c0c3c07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 249764037 1250 249762787 249762811
    0x901080a02030303220f03020c01090801021201031101140301092306010e120307061802100908031611130b04050106030905030318030f21070e0d02090406110a2a0209 73
    0x10322170011003000182c82c0780101006020200c000515a0104450420040980c1d400d0540fa9584001500343d000d492102e4824050748001000083e018010f070804444060411540c00200901e840145400903401169869183c035800304442d1808180749410307110480c00c0200c00c1c100800000d0152102c5500d49005080d8601c40c41c05400e810415101aa940620240188200c040306051400030b1a6000c0340202401241c01c444c15004030315110994101c07000641c2410203444103416028404c0100343d0700844503045a800b552a01003d03141c4000f034a000201d001310146d8140012580140d12030010146085c02840000d0400301c11650803a850000d07504150030006181419880790601c228801c1c1d030b00140d4900e09080c00d07000e05080d4851101d5100c070300e5440c500300351404246012000ea10400402a01e8010310307103c0b0a1980190080300c001031401e480c4001e0701d0099014032407140120385009000412240002500030601906410b001d00240340340e03000c03d00d20354003c0c1801402e14 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 249765287 1250 249764037 249764071
    0x90f0114040b0f060a03060e010b0307080a050c0d06060815030102190305041509030903032a03110f1b0f0f030a0201120e03030705040306140105130f0f05040b01050901080a02030303 80
    0xd95820583c0880c004001c2c080c0da565454044042c004201e91300c91129120640300000940c0700800c0c098074803640b2662035000303066980901102c01050001c045a40b0304005011131551184184034800280010f0f8030b0340c84c00c504003060f40703003003d100101080e03109030300400810000400b401c1a01000801a003400710361501c482c5010140000351701556103240d4501103c079000e051b032200c0c2200490b40603840e0103101084003810b00800c104007800d81101e02100c02c83c0c03c0d000901c900f40d041908403050040c0c40c0190100c00c01715040c40c800025641142d00501425492854100c0f03258003003500c229048002450240042521141e5496001c3e0500c100c1c8030664003a000f180c0c1000d01ca15070300c441500d9881c80d000e83c02a2058115000554031640742141c0d072030800c1210291981614001040862103032100c5c10380001400c3c11000b403108181c0c84620101007224240100c90081c0c1c071907103d000c40f640c104424018000c005178050709043e4002c0da07510780075171408400c4039000003201c0401a241c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 249766537 1250 249765287 249765289
    0xe0a06020c131b0206010e0a020918090102070c091d01060e130503040803030406090c0e0f010911090904120f050a0507060506120d020d030b1818190809090f0114040b 73
    0x344007108100490058502d42c3d03c40d41da0380490014103958a03000d407104ca0b61146411042240580c1c1052034110684048098064030f20302800359100c8595800541390000c0d660718501c42245036800303441580d0700d400450198030411980703451401d41d001d0007040000e20f4100c0c1c41a0348d0101500c204101314a110700c820500c0403d01c1180c01410b0308404403a0b0380d00703040c507211005002030003054842e28040754020a0320071081c8001341c01680c180106c55507603424490440000c110007844503200510803c40c05417140c8400500d148280d018003001d00007410000310142c00c84d81e102650008011040000300e10ba03c0e000000d407507020307800c148009095600e02d000300e800d0502c0ca014080e224850180003505066000a604d810110396640520000f001c1106000780349100101c1c40c40440c0034200080c1f840807906d0b02c0c01c118036417101d04070754400710341070302da0801d4500082e42518a04400281e00801c0d050200702a90044c4454641d8040ea6140421148001018121051190362120f05031059 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 249767787 1250 249766537 249766541
    0x1109040902121b090c0c0d1d0a0303020a02150313060f090f06020d0c08060f040921080a0b150d050a110c0106060905090403023a08070e0a06020c13 65
    0x700c0d0301d0706040f42e000380b440030050000e8940c0c06503454402d03141140003c40c0c004070001552a20880c61000740359204880d0000d0b01e04580b040400508480d44000c03074a01950384028003402940650050f2460101d01c3c0140424032200e00c90902d51980f0030014850184083c40180d18000d401c5140010500d01840088000d0001d904c0060a10f00710039a0003810f01c03510303a000f0482114103180c10850b0030314903001030301c1d060700880714079a00a080c2011344040e030030f0907000944175612641101c6041846007006a44040c4207a81e068005403008041040d008098400c5500150013102c5212402070f40c0000d0214070b20a00c0c000d01070042d21640490b00c501c4254010800011041c1c2d421a00c40c0e158881c2d56000740250700c101000035022030300000d401e040141ca02805140c069015088101031031004440d8000c030380341495040c0800409801c401c1c40a5183e07980c100c1d1540d5030750304079420305090042c0000385034400d0310b1295025281c104011070300020000122802030760f555110401c40041900 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 249769037 1250 249767787 249767809
    0x6041e08030a020306030f01050f07051c0903050702090f0405210c06090c1302090d06050606040e0f0402041a010f0e1306030804080601170607030513050d1707031109040902 76
    0x118808012041c00b04181240d00514491403044e8101c501e520316000416082c0c0b0340c00e49488103410000f601041d4032910030f0004049401c80c2041511203903800424071812074250490a4000a00c0810ba5000710b117800740e5880e0700409490300c14526400c0a07221140c170b407107840d1b04c510b50806d110380040c034074021143d0a0720101103a44068404c10f1030303d5070007181c54030a00469544100084003403a80801d5507882038076041c0b80c003c0c0580462290554964005002c09014958001418400020304041c9811490b1040001d2010040c2600701407060005845041101c1d01441480320716220150b40c0c040d410300312055075440d0103e039030760001c808109203c898200207400c141c05d04a02000f4000c0b442d000304101e954070012903410341e98034403041d00a00c0104203054003039005a03012482c201c0c840c2d0015500030540b5045130b090003c01e560380300e20f4140a401c05070040f0301c4400701070081c11306450095074000e125007403c0c410382d14092001107044c886c88402c14820f0355600807a1043d5191450454 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 249770287 1250 249769037 249769043
    0x10306051206011707060e04090309080307200a08031603110a0606031202030c0a0b100b03041202010507031104030212070306090b090111041406091f05090102010e0a0506041e 77
    0x1941000e410100242c079060240a907a24818002d001c000f22400c0004684049503290b03620102e80030300796010803010703000040007502000307400c0c000031460b144240020b0001500c9010743c100d030001d030740b06c078040418108100244600081c210400c02000c01200301d0701103901451580542800a1409488074110b61541d0012807084118480401c800c82e03111070b0503070340501601c200084c0b002e44126524030a40382500d1468200c007030365034001182c0e05030fa035800c1408600030700c2c2c07180c1c2c40703c0e10441170f034008880a80c0d404051000507030000d031f02881116080011460288031804111214032058401c40c0b100030302401d030840005003044800d0040e54040d50303221074103111b0b210b514280700035075650a80300d24080354030b0200b03000107040110307003110110b40400d000311817040c2c0ea1208011300c0d07410419a20b50040c046180c0202c105150400340d10524800303440b510b40f50410b174000282104e0300703007441784800e5200d11003000200b803001940c240c0c0030742e202c840d108409420060002001400c00402 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 249771537 1250 249770287 249770299
    0x1514040e010c02010902090f0103080a20010203040303021c0501060e10170901150b040e190b03010c0f02011d03030a09050a0b010f180525172403070f0b0901030605 72
    0x30b41c00c0c0d15810f4004d8010140201d51400460300ca00742c02c00a050400e03c030007000100c08100a107a500c0c0108500d1551481c030b0180c1103603903980e1400c0c0c2820399000b02c82c1180002d40c0054980340c081c440400c0c08001c20f403607000c204115814000c011300340d911503414880c8540c8035503010710012849002604007034084c900000c10785013400c44016010388030700486110743c03c244d00320204030007030306038155030845a4410801540d5101d036070098484d43c1c00020300d41e80f00c83d00da09128029403000d00507801042c1480c0e84400b07442400400080c00c4446103001400700300e005440204500000000352a0002002180068212a01c1c50b02c9803500380d403840000c0c0115248400054054000400c0d203046503086c1f14803070021820108141c2c00c90700100c2c0d428640c0e809050001c0380c4026030b14200d0a04183c1400c15013280c2a07000140f814140e0f080b1110118260886011f4080c2c03071070805001051401a0001e0001e01c2c00d0030f411780000071480c0039610092001049003c46a03202e600f0000c0108070103040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 249772787 1250 249771537 249771551
    0x60b1507080903060117120a11031303050601090b06070b0a090f080c06010e0403051b0321010515120a0f061a0a0305070e180a0207060e031803011514040e01 69
    0x2215076190420b603021071107802004000103a503940d181540c540c5040301c2024051602c15290404130680007882c3d81e9041140344116950914020402060480c03007402100c91400c7c138503c0c28900d0001e058020000840c00e20308050041e89400080d600c000c1e5100c2ea400640d54fc400340410010482450302801e0032100c00072000074004400000d01c2120b07030761000d0302e120ba030301d6070010002ca2030241c2d00103000078420400042d141101281174184030200d181901c0ca05119561004d40c00c0b100004074120700d0600c4e4004001c00e1410418500c01d6a120b00e52190400344a00001d50340c0600086c14540c42c16210300d005401c41805a00c02d02c081c00303031108004000d64064550b54026081180900042031920021816181c09541d80c01500c036001400d2555003405100e040300c1040c0080c0104c1b00880d020301410000941a0051041d40c0c62041c00441d00c0b5003188400c640384048905015010341d14091074a091340c01c07013900c9907041d25800c0d0900804131403d0001315000702290f1000040c19440c02c80c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 249774037 1250 249772787 249772793
    0xb16050a0320031f050105120a0b150a1d0a0803040e130203100c121a04020c100911092805150a061809150519030b01030305070303060605090a03060b1507 68
    0x229213840a40d103004181078907601d0f40015541e6200f4260199142001d000010780300403034980120502030009081c07511100451600d2616079008007403000d01041e844840000103d841d54101d060000c5e0450700c03805564a4800504c0c0c90384070794000c101c0e011080f98002401d10740c42d400880b28259000c0c0844030481d52010101c5c0042c043c218400d0001002a5420881a0503c3c00f030720302102030345941c40800c070f08058200002075001c2c01030303c3c9481c01420806081d400d100d200d0b20103080d000c0c0d0398124455412030200600c0c22002031128078840020000020540d00d1003074100d811044074107000541d902d40c8200c0600415040c461940d0000c105040440e03090f07404080a07230035800080d451313a8060f40710414a404d80c1c0d01072508450702084400e081104c0d00d01034000c1d11240c2d00b00901c6032101c03912038039101c40c0300380240c0060b400b14000159040030551b041c895400108018642a400c0c28041000101e40f968148000b43c4850b44510707080070181c0c0c0b5040100c84000c3c04c014120340d900003501d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 249775287 1250 249774037 249774061
    0xf0618050601020f2e0c09050603100b1206030c09040f0201080c04081b01080a0c0c0213090c0b0304050c040c171008010f05010503010c11100f060905070c0b16050a032003 75
    0x486003d241e03505c400010f40842d07860041360100365494542641003130824080c00b031180c20080180c00340b0741c10707000000f5040500c81d00510f005030007695060281c2c034215007030514040c07507110450700a201060400022800300180034500583c24a401c81050721f5410721150030f400303250030142080c000c2002d02c010720b025214254062400a80310040a0b03900c003503400044907440b1075903001080700984540010325040d5544c280e20265100c0000c6e103106107859047c1c1404807600718884090000090006200b010402880316140440b001c1c0042c000003031004094102d0144001910000500443c6804980f040303900c0c0a0034241008001a031042050320000d881e0031b21131140254a05003a14617107034800c00303070111004400001000803040780340800d4001c101070320390700e184555240710210760b0340c00078010345020b0040d540c0c800d05c80d1025810000541d12000c1d09120100041460710841030380c0000589684002c0d60400040140d540d51035520b4800c2c864404055079100001003001c603007205 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 249776537 1250 249775287 249775333
    0xb0a0c050106080c0109060810080703031205010e1006080402030a0204150f09020a080106050c0a0501090b150a06080106050a02070302150c10050c030109090f0219090f0618050601020f 81
    0x914000c1c04034540d030700c9000c3d4544c00b800141030b000651011b018440c0600404040c1e402240405903003201c80d584440d904d0070034209810807000070b511800040e041401e00e0180d9030140945070441840c600305270649080c40e440be48100d400b40b22161000030103540c0d040c00b440741c440341c026000303001110540d90800d207403102c0d60151a644211100021036450034920a07540401056111100641d003044c2050b20143c0101c08008a140316005403074000500078001d1000d601d02c02c00190a5500380308040c401c1c40042c141244c0e0045541030707402c2281e16403082d5158111a414104281e94a41001c0c08074107000310390300043c0d000b0000c039045000c0035001070000c106008445003038551400741010048140c80044d01c60120b0001c0600c01070103125820390000e48420b114402001414400394003040c0038480c585104044250704c2d500c10010104a4003407400200301c42ca10030802c03681402003100e160602c003840c0c072106503504c500007100b690003046036081694041c0b0031500070034041e1032840507003404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 249777787 1250 249776537 249776543
    0x1c020627240709170316050a050f03030601140c060c0a110105010f0305120301081b01031e06090f090b01030b0406110708180103050c0d0c0207150201140105030303040201140f040b0a0c 81
    0x40043c0010b06800b1140c9008030380c44110b40514942141039002d0290034005410540d07042c0241030301080007c404001503000300030180c0242d600c910780b22001421301034005514209094040008082005021551075404200d01d89a942c540038440f800311201010b2040003550b0350310740310000c54469040d000b5142180d100c0c6003181c00c2c40f501d0110000c22400284582e4a00380d100388402103510700c0c011314400016406240008d0f82c0d003034001039191ba903d00342e05070702030300c42e80c80e9030038004101140a8641110300310601401410004c3d518814641740506c4054108080c81011904005440d08007610201c84981502d45540c451305110340154400f0110385292010070b82900007650090040c1441403885003000e0381040c06c81c0c0960b80c050a03150010000310700582c0d03030120312406440c0300460404129400080d00300c42d100c01c6541c1d000410f030440c0d4403d41c014002c2000607030b0f21280c1511001c480b6403a1540791075014001c0e40c1180110741003500c2602010880c50801e42d8031001140b80d41340 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 249779037 1250 249777787 249777797
    0x152d110607030b0604060f2a020a05010914091005090916120b06010c05070e18070b09100f0c0816150e030f130f081c0206272407 57
    0x8807600180c04580d034100c0703031a41141040c0010032200d40180c800080c904598244040c1002e4200004800c0d1000000c0303111404c8102d00c0882d00f9810300c2d08600002d08801e0030213000d00e41c146051980007480e65100b07284540e0303240001415241e480c050400003050040c004060904000c24000d031201103042408490050b00700e40007401103000005551015040b403421007068a90380c00441e4030020b41d510076a0306100740350000401d460390800b024070404600d402899040041d81c19541000503941c44000105002d005504a50f514010710307059090303d90803e10842009148140d0700c40d206200003030500b54002c5114010b140050002d508160700c601800852242409032540480c1c010106000c40d542c414011019498155001440207187c04441011225030380d03040245424072a03003000003aa00074942c62402c1041c420300000c030081044c0040c100918007210290449a0810654401d2004294240c0040f020501282c160b1040001d0003c400b542642850300c4032034815100f0b00300140c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 249780287 1250 249779037 249779041
    0xc1d070807030c0c0b0402011b0804090e0109021c051f050402042f1b060c131d060103020f0d0c0c03020601060201090c0312020321061504152d1106 65
    0x26110f84591900f81850f515800720300111910707502d0001800500c12418440b020401702e503a1000c0f080b2400540340b007a0411aa1541880b03602010388046071f6911046a06080c2ca60300182c0e64800d604402036000c1d9440903142601c0c0c202203103044084491324a5280341041e2131342190003640c20043c81103000751000d02051040103180003212040e04a071408004901d201031007003143ca200140101c1204c80f81c0d8500d4403140e081c10905040056034800e07124403000541089070043c501c4000010f00c4038410303000501d512110703031009030b090090800381015030004a00320611404802d540816041c40d004102602c200480500007181002050f8003500c101400095254414051500a1070b40f08906844152640c1d503102c6010f4111041a019400284038035100c03000700c400031107000040d23402c06000e41d04180041c484540a010500c00449104100071b02c144080b0401a101d09100c0e4a0161016030200d602504c10103440c0800e060a00b0f1040108403900d50301080da0020b0034000c13020780702c4035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 249781537 1250 249780287 249780301
    0x12020604021c030503270f06040605011205100e0109061b08090c030705060f070b0c07060501080712110a1e031103061501231603030e06060303160c1d0708 68
    0x8402c0400d401000583c00300009074544440391140b07620368881c1780e1201a00300c0f803500f25a050081000218465900440412050103241d002c1d090060003014059492041c071074031341701e845114a450303500b00d0039103800300c41988810941c0050681034004004200481e2a10100d6490070480c0104000142529000c550031391000b041cac00d03100f0a002001030491a242c181401416000041c6050119000340b042802007045408083e00c19211030401c44d03990b103e035190280c1100c906802514940c0c3c803c071000c1c8284200b240c4858041a08032072840200c014030b0380010200c0080340c01c02501c0117003030300100108004204c24134003641d02c00c480b0002e01000c29010305507940401c8032800030710b04094083e125254001e00450140c42802c980064079211803104418496001c824014401c940c8a00c4400606915104e0b0405090240300075101c103007444c1e0006907890080200d0300c0403024481e00c5a104110a00105500170440e400103039400c034104d10403410301c51104480c981c02285800d0009010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 249782787 1250 249781537 249781579
    0x12030305090601230a170106081603050601030b1914090c04110403080307020f16090b0603070c0209060102070302031606020d0f0915030915051005010509030c060706091202060402 79
    0x6980560201c060349213100c042e90804070450300030302c42d00101e0f5088046400810000002c03444040c5100204043c3d190940c0c05151400c48541030b01241461442800020700201d0400c0c1100d40008140d0714603211481800013113114048000000e528081e000e211819660345258481da2101080d11010000e40c03080c4802d9405900e5100100c4008201c184001040300020b1500619a44119034100302103c410794540f817030030709411191502409003005984420302401282402c2540c09a00318100705e680604000780070340d00244100345007030016103264401c1181400564000701103c2c04039010800880c030380e80140c02204014050022511901400307114407400c0c0c00104e54a40182070300c0c2405d0001045610220358040503165481c03e4080307400c00c500c0e5841e000880c40c001519050810201c0c680040710741c4024180304040c0f0004200f560003003040e1800a90542d8103c2e901d40c11885c1090007050380c00c8000340300500601c101e50302c441e80000c9044c8650b2003502c404035111590081256 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 249784037 1250 249782787 249782789
    0x1090902090112020a050702120f060a020f2b060e040203060603060402030d18050a08011d19031215080d03050a110301091d121206060f090907050d050112030305090601 74
    0x80030500400c3c0e034488100d101c1e4010808805075103000c0342407490580c00a0040344002c09c0e40c8903258000b60325120301c001d01f80010327170f0801000181141f4200c41005850071501412080e103806900c6c42d03481b24412030005e501104c2d0741c0426841044059218044a040044141c0e416402480b900e030000e07400f4100040e0150089800a00410551035021030464034901080281c0500c0038200e40002000d03104d00341c514010f08507440000c1036401410b0509142800700454403030703141d4000052501f12182004174a402d030f03030301803030000c04106190520501400341c050300c2030341c00c00c4207403000500c004021030900c0d0f04940c0c5580030f10081d260001e01c10181c0e0075038045c42203d0313001000100a0a80c0350760021000c800300ca05241080c44041d60b0b440d040408516848450032000039106c1c8031700000300106035000031308640c803c0c02c1c01e55540780d00c0401e002c0e5144440c00307299600c02017000d07180160b003a10307070840e10300006101c070f0341e12002081d4000c2e02d15207048010a00b0500803590745400070078664 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 249785287 1250 249784037 249784039
    0xa1d0609130605041b031401030b0613020408061305120906160f05121b06010e07030c050f04060f09060305061008060609030a0b0603190b0c030612060907050109090209 74
    0x241805500400c0100c11141041c9421603203030786107000229030b00e440c0211482c40183e9242e000d55402c103000c000d0103584242200034251111000107000255065860707a81069003500d8003c02005020712080081c415a008081a0b12494080140d00c01c90000c241240300c0c440d4065840d00c1c0703914120301e441401044c5034180c0c40344c400d1208907030302e05544d4001010140104813010841101e502e071181400e4400034000410440022501090702c182400b0b40082002c000081041d589090913611616201074440c100f0503817039021403682c403440354043d50742803405020301c10340e500d0380c07030002801030f9000d6003143c0007151444400250642c000d10940c0c0c07207080d01030b01058404c68000411035500f0300c010003565106005121700521912304100035201c0ca0b11a070b030014813a00f406001c040c43e00380c070000a001c03105562101c6174001039240d450700340c00180c0c0740600c3e81c42e41c13034480004000600c00c07040c0f1100c5211303c80c10002044000100b14040352800e894011255450b10622030070380c4203413540c007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 249786537 1250 249785287 249785299
    0x22110307090b070309050418060b01110307060b041e0504120c110121020f121305030a030c170a20090307062001091406100311010818070b0a1d 63
    0x20005942c0c1000103100b014032074038001d0002600e810015044410b080440f02103640205080d00c10000d1600c916807c0780c0090030250010f65101c9100ba60300e1140c0b8000800c620303112540d13100191101d81100000070388085000c441c582d404030740035000307201c111400e4a12611003882d00f0840c034025190004002d400030484c2c81c0301c80d40e42d001512502c1e00303031410382a03510b03660301c242c841880c2901c09407071450b1032060340d11f6a822040010308109040030b040c40398030440f0480b09200007a0000704603001810903060200e0803416607c02a1761154250b5202d5464240307840030054003440300d40c03209003e441504c0c1c00318a0001c0321780c4c0120b4140100d03030540d505940544d005100302d070b0141b0080030a4442c82c0814642d280800502d1034251003940c0c40807202e56054060103c81843c0034011990700010b01d41d003c041691454540b0300c646060300007520705128505011908088041c0814180c000e280421100344076030f41c815450043d480b07819400c0004070030200400941e2140102c4e428406c200601c1c03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 249787787 1250 249786537 249786539
    0x908120a0510030f15020301080318060f1b0a0b0711010c020c010801090f1506030c0f081308030702030910110d0503100b0913060b0306040e011e02090f2211030709 72
    0x40c1207000302c0794136081e107440300b14424010080505000071406040041c01031511081206d03d402c0c030614107103140718450700cc10f000f02481608098143c45511140b120100d078103001c43d40c416401d18100e90b001900410018040000035604030b0041494408903400804c64140e000008984440c2840307015400206000010407955586801c001c044000c00e01000488860045040c02880302e2640241c010944800080398040e40040401c24400c6d1300b0f048c0b40405144c00e6840c0140e031850400d00404911010011541d420320070416a00503080141100744203420440001e0075652035902706001c83d01c2841d141c40610351003134065138081c101410b0b401c0c80b2103090101c00c1000c1e03000315060a1700024404003103001c2020768051140181600e840c025500e050080600060712282004030406070b0502e00d0f00c1c10280c181d03201d807c2889610010058960810400003a442401003501c164031600d501a01c1c280d00389400c04680f80301d148010100020610b140302907400c2d0000f184d03101d022401c2540 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 249789037 1250 249787787 249787793
    0x5270114090301061d070206011517100314010617010b0109120809090403080a050c0901120902060c0328090501020d0509010302041d040309060201060f1205030d0908120a051003 78
    0xc080d0a94280040c0040b40f020b440382c3c82c050a8414144070b00304961300321001d10070025018044607000d0302001c0e501500c3c3e56108003020704001102d01500482102d20400502109000d0b69a9000f03558407034100c1120030021054540a07002d81d000f00040c4406842c000210300005206003006c210042c2c484051451402c000d43c410b901401e8420707106080d08210f8000f040d961107442501c110320035100c0c484241030843d030003021248000c1c490f02060f2010000c1e56003585c3c0207925a03c04100c100004541c0050340e1000c2540f81c020124818118880424002c0008001c10508005584411442c400f0200344482c1111001d00510566002d600910900d8a60506c201c00501550b030043c1030161610340c0d40e2006002c510707244800e10310740010000500c070816070701414140091032144002d00401d0300b0011401c40050592007080e400c03030044140c400800a050041e00d007041c5404c2e00410202d2110305010100b40d00034142041c441910400094150f1668410540a50040c440d01495581142c0e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 249790287 1250 249789037 249789077
    0x615040506030c04020a0801030311030f0d0c0903020a090614090c120a0902060409050105030c03070602030901200d0e1903080d020901120e16090501120609021f052701 74
    0x150081c0c0e014021419075480300e80b0b6500017083c500c07440e1f5031007841c69071441c1402408a0b0448400424980042040800d00700059041d42c0346058010b50009882c0d281d104159800c046940c0000e400c030f14640030004010546912000403610141c0510240860344000c12140c1070080b503076100c8010081c0940200b290a01a64590129510318005520074068000030495089580b110680c035440c0c60051005050510548003804015030090510320700f000e85c06500c074041e10b00000d0400c515901c480d544a0840e02e070448038281400c0c00d07030f00c0d0040b4425004102c5600840c1081c003d044e9202010100140002600c2c216600a0191400d21b107091402d0006584085034090400005080007280003d561050070b20418242c00200f20845175a50240b0191410b50301452500340340400402c60080d4091401d41241c0d44144009a40c20380c620010340641d104561400d1041e468640307031040d884c3c00a000b0000741220a510a20680c5900d040c00342c80d100781d003440d900240c12800f0300c1c00c4285001d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 249791537 1250 249790287 249790291
    0x1501020102040f14062503030f0b030d0813020402130e0c0406080115030e0607020106050405130b060609030a0c06030e0c151606020d0c050910090e040305030a0b1309050f06150405 79
    0x1d0031241340801140071030740c2846c2c4035160800b2016030103602c032081541512400c040082044400c0c040e40780e001e0000783d2180c002c3da030907006200d04400080da03003803d14001001c0403a401041151145008801e40300d000c0d40c0c902458203d1140c00c008612134404c080152030444100e944e1340c440341e03130918445103007204404500600781500d84240f0303201c1c40018000c091040c44207500001e0814600b03010031042c1c0b00060b00024100c2c264a20100115a2400060794407082c1504c2d03ca0f6555120030100c1d1408048000140c241d072540385000c50300580c542c00c100b643c092080100c4031141e002404020203621030750078440e01c000b0204002d0711205040c81c10a0a83e81c098140141440700c0200380005445440200b21300291000505510780d162516600c00700f0140741c5040700095003402480503c00101500160a202c0c011001407400206030700992488032002e080c10030068182c0d5904c50181010541c211024060016410600400060040c1c840c8840c001500d43e0400781005102c028100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 249792787 1250 249791537 249791539
    0x12061509030a060b0a0510030b090a06081e330105150405191e031b06020c0105130f0b07050607020111090f010201090203070e040b01061e0e03150a02031501020102040f14 75
    0xc50b58000800d45d8580c00f50b00c101d281f06880200f1140020000c11506d0765000700091440c03441c02d40b01340800b010005000f02e2440d11285020501171040310440e1070850841c0b008000b01240041904c0c12039403a54078200c0307a80c0c543c662060280d0b01c6600300690841d150300d1080030320341d0901c820000d91905c0032006080d0080301801075466901ea85841c90792040084400c050120140303020000c012a101180e002ca401c894044101ea5081400c02501c0b00110610340341001004a52401840c00d00b44002005120401c0312240040c6e8075800f50185402c401001d4505024000c00686068018000c02c80c810030070050b42407502c0060741c20800074618003481c01d070442d982c402c0c076400141c400300508409040300d0408a905441d042c83c200c607564034140c22000c00c01910112080820030300c2240590700e0352003400c24001d40d12524003c645003008120400c100d598a000c00d012285c9481c0e40154013420f1091002504905024010380c00d0f8411840740a54881000004101e80d001440c10b0210800d8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 249794037 1250 249792787 249792799
    0xc010e0609091f080a1104020a090f0807170f06070813050f010504050c060c0718020f120a0e0f030301090c1e0e09070c0b04021207080312061509030a060b 68
    0x4141004184140c01c203e4101c411a240003085600d2201d490b01540e0040002d00001c201302c01d03840d50340d200710b006401c00c46805660040780f501c07800c40c00f0f07a0340740300501b2030351460300039469813488542d03603480a512030911490300a140781c0f000c02c1000301d00f004d1810000300080680781c4031140d00b00e0300d0b00e200601d010030402150483d1000035000b84822440803941100106190426040c06801d0410501c641071042500300105d00e242c84000c1402021601c841d407a4000705402d124010019102d03405440c10f40110005071a001d910b080120240a0f0300b0180382040302200740c140150780d4000d0080140b9155005100400c09240d10350868007202515240c6008040103500710500180c800010b001c010408a40010802c0c0c03c104c04602e60003007a0303103003a02240c000d07504c0b009002c001c003500c06401a54000c1c88040141380c00c2010030014081032044a560300c0c0d0180c1e00e1140400c09271840c82c0300301641603522086050b1a03040d2012414020042c001e607804daa52180700070045040c48503040340c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 249795287 1250 249794037 249794047
    0x60a03080c0d0f0c0506191113030b0106050304050d03050705041203022a030318060c0609070e0a1e0c03090803010611060a02250f0f030306080d032f13030609120503090c010e06 78
    0xc00c00c00b0189c00e000240e1540c4c08803803404c42c6000c80c0f1b42d12058020b641000b030140100004a04006100c0c0025a843c0c24001525216054202c075244211303000700d00700b030198007820010581d00261450781855210710043c3c0030f122a101da581200606c40c2c100350300d944140710351201070201d0568200c0943c0000d00c802c1c03400c10360080c85410040c0407102403419805c51841000210712180002e60700c03086044042200300b80c81d16001c415813404008600d861503452007e074811070300a510030030b640c0c0d40101e219900c030340e52050010b01746224010b14a80600680c400b292040341c0b0703802a1030100006000d20071404184c0000322003800c1c0b00c14003e9501c509080c0d03045010450030320301031654a01039030300810300c9808e01d8445482d1009000c4048101031410035440a0403490159a1016100302000182515a44100f0399070303a028191881c00c104041c01d80c000308109881d8015034403584204a44441c08401c000160703a240404c540c0c1c8040ca03080261400410341c811b0005050048000301458208 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 249796537 1250 249795287 249795311
    0x509040225050309180f0708040212070807050310020f0301030201111e030d05060f030c040c200c0a080d05040b0f0f130f0b0a020312060a03080c0d0f0c050619 70
    0x2920740a081964142c100046403040e80c10492292403184500c2a816061800c1814503a04600c000614400401c004d18003c28110b503103410398000344020103000c490031551103d401300e482c0c0c082d5210b5507100f48641c0030203101d142d015000350b802c100b0044941c02e003160710f190010740d016402c103040c082c100e00031007540300c100c03c5582245001420340000155201ea09801d1360008a80c009841c075840740100e0740c0c00904070b644c001058024594181c40100e4450075501c42030f5032101411a440c5000b803811805050101fa00040c40e9600803001c8406001c07680e42c49504580ba8400000b4039400207404000030b000c0b103050398004061041c1c400d9012481d00c1940c0c004580640c11041d0403000c824240001080700701b14200c2c44102400e10044820b15040f560079000c4d50300c0c45040140c40c1440b1000c0005101c69507502c420350019a001014280e90b00144002076031107680c00064038010407440d9500c0140ca901c90390f914001550310100605c10b82e201d4030404600c0c0e0a081c0c81c01c21000740c49803481804 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 249797787 1250 249796537 249796597
    0x9020a080610030201030605120607030902120a11090c03070516030207030c0b070b0105032415030d11100204121401061a0702030f1c200d08010501180605090402 71
    0x8500e52414802c10b5503030861000509559113036100c0c511480c04000d0007650303c83c0100e03000d83c1003007090070001030034402403000c02c41140c0c3c1c60024140a0240190141c20721122203181c1c00c0500b0101c0d804402ca0307940c540c1d054820b0006403800c0001440a000549002d049445a00b407418024011580c995581e503440209900b841d400c10a040702000c43c61408026050002c0c1c0c0c050074044014140d02010020300100d640400740c0800b015504c90000700d000070304481000442e00c0409015241030254009025014051340302150040d845440281281600340d442994156480640456400e115545407190380303600c510500c030020f543c0c403100015403040f0f0100c0c0701c0412a03510761041c4c0311040e03401050308000081e4030345082900090010010207915020505807030156003806046403008484d1322480c2d00120700020350034454021425201504a24140c2c101c4200341d807040e8120100040c05050f00720a0310034600442e100f0700c01d020b07680c68641c000e800c980750500003141540d960b084220302d0b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 249799037 1250 249797787 249797791
    0x230313210c020d2d0201120b03060c07020d1203050f1810090302150405010e0706031104051504030f110906030c01020703080c0309190911030c18060d0f0515030f030d09020a0806 78
    0x10131040c82a12840441d6041241c04d40d48614030f40e02040000038110110341c4604000344001c03440700001a55101b1961504041b80e461504240c40307650f00e98201c64007900404060322540481d44810b40050066943c003000c11030408a03000190180c600015880d501500301a50100c1c158002c00340884181c0406012880c4210302503c000b04490042e00f03003640c1800e119400400c200360a111400109556000450b0201d40c2d098540c07420030100304e031448545000d246c000900e00408070390305805100200710b030002000802c036080701c030302d031115004c06944250400c80140941c0003018200081403280e809808210318100540746440c1c9210006911040070200700034807289110428002882c01e0b11460b00b000845c400d0141c5181002481124603000300f544126519250545e5a070283d200c5100340c591542d0403680c140001400ba01074107000d454100d4180c0b481c002140f080c51303042e00d0001040c04034022500042c42c6071022041c60030f4043d02d01d0a00030b90700000c207040c0018071407108110b128 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 249800287 1250 249799037 249799103
    0x305060403080601080a1a0d03180f090606050408060a0f150b030f090a0215030405070302090a0c141602090408040503030f040906060519230313210c020d 68
    0x1c011031400e24009041200041d0550030300d249441c40c60741d1f484801c7d01401400c40c0301101d120700d9180940c9000c80318141001016030101c24520301c0041c010200142d090180e80c0ca800f401d200032900c0748402c551500980c8200d4001b0380c03107000400c08a5260751700a082041d800000030a8078801c180c254103443c449540000e55000e0008104800e07200e10300348403604401c920001e070905210b9500015150048407070900002d180003c08a8200705040001500550380501203900380c0c40c00c0c40c1d414000303101e80a11080410100c1d080e100403d1088070031a0f01c900710340030703203060180103039000c0c00400440117000711000142000085155941003001d0240035002140880e1349600300b442100903180c0a6000b50305004c0c040c03007110984805c40720684c0254a142c80d00141003c245011078181801941c03850110000c000144400d2140e05504003103640d001d4080341006400380204610f44d00c900152000000e000c98510b43d0051510b01d00b94104940100c41c940c9007000c00d03001e4840d046444282e99 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 249801537 1250 249800287 249800297
    0xb09070c051905070b0c15040c09050f0f24120610080c130b040f06180b0a0b070807050a050714130e0606040e070b0c0304062a08090a0305060403 64
    0x403810450104030404200d1071406007400d07038002541c2e880b5950a0240200605614082846040303190100060745da43c3c0c81c201050412070409060140d00d94100380202c1440c142880c00086030700340e9902031b00b40500c2d45c1c41047d50540c0d880701c0d000842201004004413202007800503520f840c1e69410000301d000d11914000e00603a0500c504120000300684d8007449003604064080040c0350394083c0e208003104480c00001c14140250390000c2c00034905000120000d40ca41203000c41d407103078502c1003c041e03d89080e2041142e403d8585c00c11003280f0b5107114070310740780304200031410006030f020380a0020b051051b403ca40c0e500d8002d0b0340310303410000361b0f800075000100f40c40d05800a510f4091152600303510702c11810499200510b0416454200043c0200d008a44514030704950143c01c01220000b000c02079810340d20340076110312440d1a03034081c1c8245000100d800c2a044404040c1e0007080400e0307496a0300d85010920319640d81c2142c2d40242c50030300d070310080c2840b000020500521030130384114403955031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 249802787 1250 249801537 249801557
    0x62001020f09030c011704020409030c020d06051006030e030405122118060708090f030c12010b040c05131806030204050103050f0d020d1409030307120c050d18030b0402040b0907 78
    0xa0519044903181181c1c100000f961006c45150f4003003c4184d0010380584000c00d4000e242c1c00d0035201c50705d48135802908401104040c20500034203030b0180e406842031b0024581c8450b600c001c124203403000b111440d1400d4004004c200300c0b43c500020710b440c800b81c41506466812442d1581e15018803e051408003103a14000b800d24244100d050451080c0503084a07a1400c08400f03480d92121406502c440c0c5000e04d0380c9203414400360341c080003801080d02c0000c10344c041c0c05a01500b03a034080c102050f031603402281000a1550005d01413029110310180005030542c980d803500d500f0210b80300c490701a00caa143c0c2e4030705007c400b5843e00d000765406140100e00405072600c0d51500985046d0055520000319088616a407400b40d40c040041c41a152421801c0e640f24041c5100107400c0d0305c1140b000414880d0105688510150020240c88500f8010000d5a070360780034424090391900034841c02c5d10090201400e007400050200c040454000d0300113080010080026408200d12040644543c4046644004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 249804037 1250 249802787 249802789
    0x31a1504150309080d02090117160228260a050403050c0d02360a0615080f010608131505060f030f0a080304032601031205030907062001020f09 63
    0x7035200620001d85820049203c10b40c503a52100d0207490320013882c40341c002070380c511140c1c81080041072844210085014031306011005500074400700b8950001340c01002c801d03070301070b108582882e0b00f410022510078043e045250740380c0d0801802d902e805550054001603950342c0c030210101905001c01e140c1c03143d03a552070850400350b00e4802403618031846010782c3e07034003280182c0311101914605840d03018810801d44172081031f03080c01d0280001c0e9002c4043e100d0708010482e074064002d1002c680c030080d03240c181c0c1b0300014401c942e4400c0c21142c40758401003940c010059a4400e03c03403140c1c001d13020ba4801d0b101595958541100d91045140850300a840c2d5003445414903000141c0400700b2002c400905100b103a48442039201d00800c1006810004080001010715001b02a15882c40c0201100034540161143c5080c904034030a000c1501d030b00d103013410380f003400b80d000e001140d00510440006011070351411404503500c20340e04600202400d44583e001081441c240054645444800c4209032074185c064 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 249805287 1250 249804037 249804059
    0x6030509030306010210020d020d0f0c030506011b0210090b0d0f15061205060f03061018050103020919020408030c010506040c02370210080430031a1504 67
    0xc0c1900c01035070000c000740410380c0e0700021050700040503440c1c09a22078032102e280307100078003607801e01c0481c030b40c10001030917003466850b44443d008055603181000580c940c200115501803031a84903000c0c00c1d8218030711001503d09150301c0c21908186240080c461500d0b92a00207594010b83c0c01802c0490329685c00c0c600d10801800b4203900824000c0c508034000d450844002d001c05071900a0501483c2c2c1c84012034400d84030382089400d000005000c842c050308000c069000d041a00303100d10110482d285102000004403401000d049a03002826003406441d0081c40b02e0b51034181d19200c0a06d17507400c0000250100040c4060302030880000000039980c0740500034001a15160b1400d2011904040d203141ca0901c2c9a00c00b00b009030984203c3e074251203281e01e0200901d2441100c02135444441c01c40d0602c0c1c195401442c06102d180b040a800340490f00840d0904e482848503401c2605004032501d019010740d10940c0000c2c1080d036402c1079200c507103030f031400031074040601c49101e000442c80008060114200c05 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 249806537 1250 249805287 249805291
    0x20115050306070207061107090e0f0d0309080a0f031e0b152a010209040f0f150b030114010509090405060403020f03040e010501050a0c0b0a0605030714100c021216060305 75
    0x140d000e0a140d20f44503500944404007800b40c0b0f0284002603001c4200c240c01044001c000d4480210100050042c440303c007036a0f440113403503c000600c20041a5a621481780c02900155a80144040d0510014100c00c1d01e019400010301c03801c040c1c3e035040c19285404030803000e01d00c0c161f04c0030000a02d100742c0001e00c84d40000310981c00148500c00c00226007801c0b110048099031a4400c48415072190080380c15601a1003900030280c2d00a08006455401550682c40a10f101120341c600300516004001d540489541c180b1642881c1c90082c00108030b00c41c41002c00640716201450102d01d4424148000b40305c407041524181c681c1c1e8498001c000400d50100500b01e1785042920040d400c0514040008071892414010541041004542c40b10114041e1100f1041682d0082150301a07241c000e26241c01001c1600c11203100344030707081d000100c5244180f40001c203040301030040500300107600003c0e16140ea800707070100d0b00b0642d00500010032103000e11034000071000746070b802840ba42c504200142600d0740 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 249807787 1250 249806537 249806539
    0x150203090c041e09080d022206020f060a111b01060501020c030714010c0602190e1306181104080a150f05060d0f0c15050910020d080a0504020f0d0302011505 69
    0x43c0219a82401c1025a1480c3c152011100c0c086000891032505030b086001d07a40741b0582d483d00215000c0304022a01100c0c01e07032400c0c0080da0400846d580c003800c80e03481820442d0300d00f10390007400102d03407200459009003013411161002c80b4a0a030811200d4501407080700e141e0314140c0d40d540303000e000c29a07052018008540046006101590800c0b0404201030001c503445c905201100300230408010b0560151090100c0070102018241c40300d41c000741c861250b40604a00c030300c0e00f80510307080c00030301d501c100e6060b249107050074907107200f041f4601c00041c400108220031215087c403001a0130602001040b01041c0f04141d1076035800200329421060700c0e802c960f01c180b1036007807604101098851040c09136241da0003900040e00442282001300b55822290060080542144084402540c1000041c6003c0a003074603140003440c8588800c07a1911021000300002400c0000031500f40b0240380c00498005000030082001e48900f040051840d2500340300c1100946d4481101c0064400e032000c80c2001440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 249809037 1250 249807787 249807791
    0x150307050d050708060a14160e06030106170a05101e05030303040f030801090b0d020607020a05090106090e1602070b0d270605090a080f1602060708031602030403080f03040201020a150203090c04 85
    0x160240ca008030407004283d02107603c120368141039012711407000390312500b41c060801075895031680c01c0101010808107200b04103600030004103074003580c1c9114540c499040403440794101410301c4800c0e810410300d03103603104e01509400d9001c1116502400254001ca11803d107195801200786001f0303100c2134050340310704183d5107805040d0344581c0b00c440c0c40e400565411a00c559803180d8910014803440d82da9001540c1282040b00041030079600301c0804029550340301d07034485d8503540700e0580242c10540300707140300c0042e080b0a804011140115018011082a014022454460851000c00690211103652094070200070040b001e004903841803680220040c005843c40014545592249215588407001c0041001403444015168240c04103036160f40200764580d1041141040d00303068005646400035440781c01c03442901f941c000401c403402c4a0b840783d415802d2803881c5102058075000108242e040d0301600301c2c4140081c40c50003100d40ca10b44e00d800700503200e081816046107403400810307005000328 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 249810287 1250 249809037 249809051
    0x61d090a050309090a09060501060815041a06070f05060c0304060b03060f0f090109020a031b050a15030911060a0c0b060609010e09060111030a020a0611040509150307050d050708060a 80
    0x801c0802103505004080d00c8210303240d2500716144004080b01140544903a140a00100b0200c2d0f00801440c0145ca0020fa080d1403081031008110407101028098815110b014503006c0d540c0c01c220001c1e101d441c1c0288006081184152145030822030219861058041d00204100802269203e03420b8510015030050403e807a0070032402032580e030702800034a9032084400018107440000d405c2001095809402c1d280c40c65aa483d0a000440c02c3d100003066054160380042801e04092041030200d0302c5105084041e030300c3c100f0041e0010304070aa8107550b0384685003e58880c5440d000c000b8002d40c604d5548512019030142405003c0c0c0324040d00840c407410007003181555981c2d10200341001c18404849000840d121b080044c4d0b210490112125100e000c04154008840d4020680d02e510318082c4200b4090511078800114441c4601d004255124a0320b001244014210102c449443d0b88041c0c1107a517400c2d00c55000844805c01c20314201e0f4164051401481401824000a40c10100d6408148084 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 249811537 1250 249810287 249810293
    0xc10170f0c0d090c090c0e12031c180b04050c1f050403020411041a07050606040603150b01020708030301170118020607080a0c2108070c030504050121061d090a 70
    0x288103441c0c401e80c0741520f80300858140b120b1981c2c41001001d0b1843d08001344200340801400700d034440d0344401e11590454410342d00686001c422503440303400700495082c0e82458802c100340100401d030301703e4110010408030702d03000981284080380260b00030300040651400742c0c410442400140101c0307241070254004005030f034603000002d039020350790704607404140214840b80300701e418019540885014004190003072a07610140e4001d04009000d101918260369513042884181c842e40c0c0300040c0f80301018175800000c0304855101d912070301c0051040d41c0c0d500d0356900c4564a942c20a1f00024605034409400b101c00c8482441030b008200c054800c1801003440301e4001074a54010040e020f4030f00d1500103602019180b0551800c00304650007030020b40c00307144a001c0c03003d000464440d14408540920081007206010718218100c4a50654407145000e04000c011140b4041c050340e15000007640d07030701007200d160f400e0060310301916010000801c4040b003074852440e0721034082c1409840c1c0d0001007415003c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 249812787 1250 249811537 249811561
    0x1c0203060c0a020307060c0306170102040810020c01020c100c0f03050907030215040f0b0406121505060d0b04051503010c05120a020a1e08060f042c0c10170f 69
    0x100540c1007111070345441d00103409900394400c502004260515100310301305401d81560088007a40d448103d0790f1000d9480070a201e00300d11582c090140c459208214091520071190010450b00110f074002504080803410b51620302141010413580c915203582c3c1040039035512980d04840c0c11100c1c130f001d0010342041450f050b15941c1d0740c0006405240e580464407512110241124002c060b0940d0551034039540e40340860054000340541c800041d10b440d2181c01e120128010124150414455034400e249001c04002265002400d03c507000d60320b030590448c41d9601e81c0f0485204100b0380e0034844800c64002e04241c02c40c0c08611a900901105002c21070002c508a007107294000d503e1000180c0d01d18200c041603941198500440d00c6268111044040c0785a0150b08140a0502a00c808100700741c81d0b010001501c1d41e104a8040c0161480310f45025810b0040002d0f4010440c84140da51a1000c040800c1c4918035615051010a0002601d240000b41d0f494800b03038000c480c0c44451101c0e040000744c00071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 249814037 1250 249812787 249812791
    0x81003031b030c230607050c0c040914072304020a02060c0c0c060a0512010603060605090f0409060501030b0f011e140111030406020f0c030703050703030f03020d0c0504051c020306 79
    0x740700795000614101800389084100e203981003582c4079442c402c82e040343c05003498240040320060103a03101148801c0c0c01035054540545855000d03040740a47c04041c0320003400c10311400c0d188030306c44903640281c5a005000030b0016008440103424018920fa107414002910020400e005501c100803440304560f001c21031075004205078251a0b90380c4890301c401d91814100b24005d81d4043c00002c1e03800030058004004104c0c910301d440d01005a83c0e83c0d0790b41982260381a20850340400e0b003c00c03640c41249403241c881810320350000d000040c460100c0d1a8031007225805d03041101d003e030075070741400710b401420070002e4010a0003000450038911804000358141c021441020380c2d85c1203140150440c0d83c001c2440c0680c01034030300300f10703501c517513076460025580c1e40840980403180c002d0201055031410003041100a598001000b01440c1745035960481c0d0307041180d0071354000c0590901000450038000d0181a400c21090b50703401d51a01e007028104900780107003c5070111005201401d800050314040b400d59 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 249815287 1250 249814037 249814067
    0x30503040b0a090c0603090218040506070c05032503170112021201021b01020d1a030d051c02040608010608010e100608062101050912070510020d060b0c0c0108100303 73
    0x10045442c1c0c0301c015409400c2d900c600805038111040041180b03581580414030450086509a2045101004480d501e6a0a550240264000c94000b515090040c43d98000e910301c107804903460281844a048045c100021919401c00704100d07a540c1419400041296440b018800001441d450400b1618502203000002801070a4500c42c4d45140a8298107461505451503c0285c0c4081003018481c000d60012101114851038801c03647d5111501d00c842d80c1390751030054020244002560070a540340c2c7c00c500c500c4144c44441000d0200e1000c12400580000c1c01c1c251070b2400694104140a051140141c0092403c003c0313410400c10001d50106090048406034104168035407940703c0480d06449901d21981d02d40d1503840d503a03140d480740550020784030302313511003e0f682401070b442d402c4140761240945c00750050344220101942a0410b60003412320034220f580000e00c1c1c5075102c24121154100c42c10901a0317070840b01c0202155600301c081643e00000b83ca5003040e00074219075000d0014405007803a2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 249816537 1250 249815287 249815303
    0x30306170309041e0203040c08120f120a060b07030f080c09130c0201180c080c03010c080a0b030703020a0b09030d1404060c02060c01020c06041b120308091501170c030a03050304 78
    0xa89021400302d0220f503000390812011741d40ca02e440e003008144000c0b02d114441251243c0c2540000c00383c102019100707045607070101da924081043c4410707022544050510501c3c565162000106080f00b0360007404c0652107a1601d0222885544024040c96070040c41c00c100c01d4420050f039a02c0341d50f18108030030f0780c446030340b00003c0c240f59544089005050030100107641061003a0618140001c0150480032200244111031400800c0024103090382d0b084141c00780802d0b001c00105400001c0c5401c4403c114402604480007d03942f034000800c601003941c45101c0312200004c1c48501c4d0b0501307000410042c842805c0c00650941114690300e01d6200f81d00c0703680100a42d5644000455503030b00201c40c1c01d00396240003591903070018090145c0f00d840c2910129960522150285282515190714900b01d4034110081200036a03152000e480034000100ba0142078024030403803a00482100c01842c2c0a402a00e84c030768600c0031050b024910300303401c443c0b44c50f219902555031040080da02004a0754130a6221a507 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 249817787 1250 249816537 249816551
    0x7020d0501061502100e03040f03080a0c050607031b0e062b02040605030105030d180b0a0516050f1006031e020109030807121205090d030b010e0a1203030617030904 72
    0xc0240103260b107800c494400b0040c40c1c07101e82815400907085682648140c81000400040c074003e903600e210780d00c240c41c80280c007403500300040f44411019144034003040c14483c40441060381e6441c10300c5405c541c41000f00780d4800c10a403401403125400e2230501058144000f002c00501c0010302580110740c04001ca11005140004421402c240d003000c030702001031000d54941c0d80324100500242c0090240034028412008a100c0c0a0712811064071001040008103079840d0610801200641c02801d11405200c2c0400502c1d220301c00c0d02c002d049600d80100c002c1c00d0805162206281014031281c3e9284001d42084424400700e13180222041e8180032048502c400d20600d840140e5407403c903544061b1121001050407024040781401100300d003081541c2c0c7c030300082c40301c4090310100ca41c103498090b0795501880d032410320140641e02c052000d082c14101501104403900000308152140d0300501050b5194041c00000c06070180510805064800700400d101c043d043d03000c981d00c0c021000030520841e11050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 249819037 1250 249817787 249817793
    0x1504060e010e0f0607030b0307030c030213021b0606030c01031413050a02091006030f2702150d0b0909010605030d05130906091b0905030309040506120307150513030507020d 76
    0x200c0340b24560810015034203840d444001260300c0301c40803034052020a0409030522120315011849205403079219081d803000c181503800f8031208084203010101c241c0d03420400a00c10049410401500542250050829283c00f0040c98244004205800c0c141401c191048800c401c4007416984d104800000c01c074080c0405041c490300e040714100c0041d400c002c28200340210050301c46403c0c1c0070358245440601290100f00d1003001120140c400310000c1c00500386062007119111280c091416000a001841c25007950384505520703400074240844440d07480601034000e04000152560110030f600081007007074981408030382c8030a5170902c118100030000905c0f03d0750002d44040c01000e003143c01000c001c1c08da19510b40034004c0601c80280d2010410303070118002c442d8821030140c2c0569030702901440c1421203a100f030101420303000e400150710000d5041c00c000000020005851001d00a0380e04968140000003194203c40c006048200b484000b0361145000c65040b0049941c420303030695181c001d901d4181 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 249820143 1106 249819037 249819041
    0x708010c021501180914030c071d0c030a0905070909151517030c060412110a080a050309030d0912030c02010203090705040b01050c010903120501081504060e01 70
    0xc005200a490142e030784403030407420f641c0219000c2085c0e07030351b402c0740c00c01e00c420348140b50710204601008000c01c104140040800e038100a4003440d9540000e40080300041c2035403041c020020100701840e1095212020785504002520406911000d01102410f588a41690071605448800741100014400d02012a0030149403844c071501d081c02c401450004800000c42502044c4803058650005104803480f0358400c070050100380300c52040140581044200030545503200043e40800108550708407051016a414920b40365501c3c81078442c90751007981180c919103030030641c400003080000c000d6002191007c0e10f0a0140c1600980c00701e08070300017100c07000e64139403081000b0000d5007000d5002000030103041c0345c02442d1000161401d42541c0c61b2080460005460302824070311035100d44a0b46014201082c003500700e43c2d109045114550201800140540341c2d10290b01010190035 = true := by decide +kernel

theorem cover : BRFrame.Cov 249640287 249820143 := by
  have h0 := BRFrame.cov_init 249640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 249640287 ≤ n) (h2 : n < 249820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
