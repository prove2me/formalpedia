-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1645
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:01:51.594847+00:00
-- url     : https://prove2.me/submissions/5afa441b-b51f-448f-ba6f-701e6ea3101c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 295683453 ≤ n < 295863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 295684703 1250 295683453 295683461
    0x30c140d02040908210412121d03250803060f030f0a050705090606070302070303051305031f05010f21170a0810170c0402070813120605011a0715 64
    0x2941c040c1051042d000319091a100e250030012610a4113110781000d1010380e01440d140780d108651181c1041541c081301c00003140d08010815004400581d00c881c0103c003500e036102c0859201c0799641c0203641e181c0c1410051203400c0c03281d203112480782003201070400000e082001a281c6c019410b0703d03500507101003000040c0c0342c004204d8907882c0c02c1c003030b1600020500c5004580c400a81e1829500d41d02e184e00d440b000d2000c5480785c000f000d001030f0450b03001400020701c01c0c00200348040000d05072002c92078480000904080701c05842c0c013407007a03200340c02914114590040e14010902000c00c04c40641c90580450303c800d0001c982c0040c00006a5510b0081290701c6103000344203864107880c0e0751a10134011005e001d0010559408501181c0c2d52000142c583c2e4032803106125052490280442e00d48020501010350840c0324229881708050151540d11804208800010304001004820115080c02e0680403a031060700140308541c90b810282510340c0105e03040780e403401d038088404082c81020304004c400070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 295685953 1250 295684703 295684729
    0xf06041e0c0b04050f100c0f17040b0301030b0a0c02030a211103090606030105060612060a0306050705130f03120e01030f02030a0c02060a02040617070908070b0315010801030c14 78
    0x10040741d03034000c1185469200a4015694252944960761145004000303011260601140000d68501d01c03070070000d0400c01da00d005191040c1c9158a10014083c0c0841e5160869005900c03d40707004001081884140000780d078201160340010004003400c400c1c000e481e0f214401c4880300340b01c1c2011102d145403114019598940d180c5d02c804115200c1c6240349015070b50f2042d00e800d6074a02c588808284c040c98103208240c0a03210040c081490b101031809000200c0c1002041d181c1d20200000b4004040b40c050f0144520440485d60b82994600d013208181d60384034a250000f11420001a41c00c1c00014418130707071562184010300b401c800d401070741c10048000e000800054000e090000c001c0c0415000d85400001d2240b49940a80f03000d9560300c54050300300e006038442c8000084144540e2042c03c10304120458014007185044c2c20b4558540c1c0001c2d00d01402c0c0e40c031050301ca040000401040ca500403504000c41d03502480d041d0460f51464030790040c003a00d01c1c060003c9000d86842490000c1d071b0781140307030405 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 295687203 1250 295685953 295685963
    0x60f06130e040f060c0206060924030a053a05090402070c0b0903210d02030912030403170708040b01050103110c1b010905090408030f0a09062a020f06041e 68
    0x70034606482c02c0d214203044102d080b140e43d8101003035000d1860020455070310420014120081e07940d40c0807020744065084007600c2130345e40c801c10000421500d041c041d01c654507000c1c20003810111840003011071440b450006540000100c005a854042a280c5071101003071130b40e241c51a12601c103580094024805c02c000140204108800000d10540450180c041c0c15030441c1a210061040741d0528540400415004a4540100b080604061440d40a5500704281c902101e5940200c43c8030941c02c1e41c4161016004505c09410b0807106003900c030740b03456001c1524a4000d080d41000d503907d084009060051605150700d411954503007400d50800d581c1030304080000c4407406a60020f08514031107140030403c1c0011a09040403a45082c500c007420300031584070002c2850740e60342c1d45e10850b4041000d400800c40c20748034044100892454001d0480c004102c00802c1c20a13503010480000660f20041000d00f950480b120340509503402107412948260402040041214002590b4560301c41d1100001c01c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 295688453 1250 295687203 295687229
    0x9210604061506050421080f03010b0304020a140f04090521180d05061504020714102901050d0609110d0c02031602010c0f02030d031a09060f0613 64
    0x3400969000500e42d07201c40001c9600c80c81d207500c011189031180d4090100e40710444a1509801802011401c190368010000d032414070a086122807295130003070303010000c008404800e001c1540f8018540c1c200030040040043d0041004c08003284444890090305072180707580750079910038000d0521910400d078080c81d01499207071001441d0709885810a25404440e04141240802c45080200c0d003510225080401401582d40c0c4d090b683d0072140011071130700e401a4003480004002840701c0701c01044110036802030900e1050044d224000c44001a440d642c0702c0c1c14030400c1c845445103e404495501c0020b2034406c0d5920440344443c0040c1580b940424000c6151038010b90707810300c00700017a0130f08440041c011702041d85056400c036520b0041d045088442901504424015070180f007000c1101440703500950980c00c96600080e0a128140c6021004651602c0081301180115905410180d0b821266142c643c1414400309402402a080c1d0600990000580116090b196009040100f2502007aa0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 295689703 1250 295688453 295688461
    0x60b04061e0f18021b19030e0d03020717190305040e1b0405061602090103030e0909010606050307120e0f010b120109050709020f070c03110405070e0d12120f02031e0705092106 77
    0x5040d072404401f80d0008a8070b140d0000710b407500c0c8040614454042e8002c25116040408250205200e07001310883d501c100011244040320354121a50340074000d440365a140d81c6019080581090005e042107642c07141c000300c0d08009c402da101554191141907034043c0e19040c4131603000c02e00020480002e944000060000010190300031414803101e1025030b96102d003601d420380101d00307880701401107a0104806100084145104210040b1200c10f100d1000c030307100c80f5004056040003015101c0b66020f0751255004403280c2000b20049041c5180c0034000c0180e03451a4450a4031202540228101c0e1500000e0010742c01c0c0a02080e201c80039000800c029585a40e031921072401c0e16104034003800349040000090360346005030215030b034070b803805050601507444554401e030720914504809014001e4005c064026032000d4403070751280d0082600e0050792820301032100807001c040b5114900790804410b003004100c590003410b4450b1280b0a980e4886c0392001200c2203d100d044040c1e4004c854407030f4800700 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 295690953 1250 295689703 295689733
    0x90302090903031e040c0501230c07061115150a170606011d0906090c040b040611070902040302010210051b07150b03190f060b04061e0f18021b 63
    0x118081c24079007410a06005184d2040403d0101c03c90b00502452070f00b58041010b0350040b0745c1e4521500207406000b5a5000303004800810b03800c4520845c002ea80400c0c0c05200c0590003100320001d0100b810028801855058500300e00300384018181407031504090906c0b2805d84034400c010010b451040301e00c4003210254910160b865100b01c4a2900241c808000024034928010700c4d20300b0140c000e45160503c1d82c0d00400c0c0708440c5006842c2855411040100090703154403040500003402c5580d4a09211001005046207040c515400603d982d0f4410001080140c0e000104020217180c04030b230103d12580c3d00c0c001001800101c0d5500e060040d000545082002020350a0b44019103000303004001da4000207040c0340c2e44007a0b281105540040c2100114045150f41f100742a40911800d4045003030880000890280c0e01150f0100c6101565401d924a2619848000c400603145040007911024900ba020803948030344180390010f203d41c0000c11681d441a00c0c028446001d02580882e40040540041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 295692203 1250 295690953 295690957
    0xd120902150d060e04120c030c0b090c1203042706051f181a07060605120601030512120402010e01022a0f0103020315040b0a0f0807090b010806030a1101090302090903 73
    0x2039501c070546080404a0002154a011401145c00c000101106d01c10480142e410380e0201c1008c7e41400307070203040103000900c2425150f10072007801d409881201e0744603040c1b01c400040205060980e070030521080c40100010591142c1c80320032120350740c10035821000305400030541034001c0c0f81c03c291364000d02000b82501b0340380703141d60395042c0e610520f02511004d0007030101c410364081c200c4c8030790880b00368128021400010740360690180304002030040d030700c0f030018088a44407030803100a900120010014084240104c50030404803440c1d90f8039103040450101203020000b031000703042c84405040c0751301d180d100f00508400d0030280c038400da03005803288100c034140310801c03000c0700c1c410503445181e842194881e0090b41d02489030350100d80352030490801080301600b0503040d03941d008a84032000040b044c0c6208407007002002420007500080341000103070030a030b41c00d800e9200e060017101d03018089151400108012a26013113010500f0461002c401207405010035170020b98440c0138078091042d00c00c1e000c40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 295693453 1250 295692203 295692217
    0x14100309170f12010b0a0905040506011202120f0c0a170403110f07090b0f0a090e03130605030601021c0507020415120507050a0e0c0d0b040f020c010b0906060301080d12090215 77
    0x21620700f0780e07a0f00c0d00c0c0c0b94003501c5095840390000766415802c00050074a500000d030441d8050401150505a44450804917003041d01080084202c000600082030000e01500d43c00080f041c104070f240500c21080a0100402000b620f20031401c031b03900003014503118001c0c420302000303242c0545806400d015121a91240300d80111402c039840c16030080003170b190249281600c114040c110b411014540030300c1d00024541c4000da4401c03400f0400c0610f0f0100c10f1000f0b200302400c82901c40c1501c90501070002860440f4102008452408456411150740e400c01c081d00c07031301d642c102e40100c5c460103844195041c10b0f8943d13003c0300c0a4450009a4020440c0114001040d1175040d103581c040304e03580c1da20000c5405000e440e114168801000310311103080154004d14a102c60151001c51600e00c803070015401ca82c05903803d1001070350740e4038028482e8a4a5410301d41c200c42c003194004d0440d410040c5403600c6207224400300701845201c0d80b90a00010807500030703031006e5400404681450311149084400d03688042 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 295694703 1250 295693453 295693477
    0x3020702120a0c05010f020c0913080a020601061206050d080a0306030605070504030303050c121306090c260c0907051b060c07031e140903100504060605040614100309170f 75
    0x44011134903500c650005070400072140c0c0209071403801070041c0040b840000e880b00c8000040d0085070f10100d98560001d01000c00e155004140d15071601100509141030401e10213040b82c1412020002c95507490386000e40203405ca00101e0741d42c000c00e0810b038010101a4401403480d428441045042c54002001d44100ea010741c400b44040c0c2d41d400c15961491149424081d52400e141c400700741c0015010082c0c14072103220310303400516900f075522043c2085040b640151001094160300b181540e40031401120010f03a0b03113008007a00900140018030103a00103102508018010450507014070028040c200b0000c56081520482e0030034a400c0100e503403000c0429804580e0401b014031109558061005c91400326980c0c0e120042040614080309030b121008180d4588501103a104010700948156406503105000008805140c2418801074510725440708446c20a2101c1d00c000a449140401c0c009078410302d0b00040748180b924025220b0700000d120441c0880c40441c42807544843d2030003c06035980f42d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 295695953 1250 295694703 295694723
    0x30c09191508012d03080d0b040c0806090402060d0914010b0108010f030b0f040309052e0c02010905092508071e0203120901110d02041d011a090103020702120a 70
    0x81c0a080e61850801e2158802c481c40c00030401c9102e10141c0c1130b00074629060b400e410b40c01e90b52516118007980000700880a0070360381e5100c4001c946031a100d0707400282040d05003210640342c00c0001540e0590014400703400750000003903030031a003d190b510104120f40d000c10280314141d02d80120500074008904d00501003000c0000200d21800802810303004c0703950050101905d42d42d0746140380c003c1d28010340214280064818013141558680700703d090b00070b01071084c6440c10310303e03d1820490719042c01911001d0000070705203400945d0b404441030055810941e00b03018075443d19920030b0341d48444050748841c102102d015042c201680a40c1c820302608141d507803101801e08540790002c070a4810f00b00640503901c100300b428261070b6160282e980c018101c6000265540e01d480075090558070104401300460b50004090141e001a440e0041c5001c102141c501500d40c10000341550400394000450210240840d506545e0b07031207034048601c1c0c660302400c00d5000d0074210314142c0d541c00080c201100c65020b2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 295697203 1250 295695953 295695989
    0x207030c0b010e0f221a04020108100506160804030515090105010b0301140103090309360506030a03110138030a050c041e02031005010f02070605030408030c0919 71
    0x540181da800303854400c4c010106503c5101858540d4407441c12034204074844200c0c24800b050303000d074404000303020340c21000704a8a4244001004010010312104200340d42040034051516210280c078100f681d1a1015034a89086082c818400c0c095075000038140c0c4141403000c240580c1d1041d500d4081c0c03121800a2020782d07205e1031140114002401680d009841d090038180040d0704c240c2101240354020f060054015844402c2180c290701192208007503601e112240d02c1e4074146004960101c00d00709002001035040000c0007039120f100058000e410001e00d0207000391699020740c0f04c01a40d034518820040d9038030b503440c1c071851070688014100b40700c911040d401950504010404045056104029141c030b82c410008000003820a0507074900324440880d000401c01501d4070065002e600d810740b88141300e900d000300041905512007404021500f001008121031038121058941003a80b10b9421500e81e515a2071744a882d00030501c03c0d40d23100d143c109148850300c0821940c0b400f551500e086264403004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 295698453 1250 295697203 295697219
    0x312030501271d0303090c090408032710060f140d140304050415030c061106010902160f06090b01050418120302090907030b0901060c11010c0212010207030c0b01 71
    0xb441000c0303455280a0400700d0542262a103410000708a0b08001040d501c4448155a4520100c820311540d900003c140036280c1c200300f12805840d10111005079151a00c4c4e550f02d6050f000244c40c04c5034149807510004419120620f04401515092013114034082001c07440b50064245072040c80f07015240e00b24041044801944421000b03180a41101601c45060f0342c0c5003284100c04422008030701082c000410300d030761030b40035006424810301c030340415050031400c4c60720420859900440c140b02d0b400d5410324000d40d001c24400e046541072280180c82e114050000c06403075889041c010441802c030060b050030026541d0061185074000c480c00705040c2c0c0c8a07001e000440e010045000c00080c000d101802c001142d140312401041c1f0140790160034138208a02082c03a50b40282c60600210b03484401c0c00000341010a5110b004041918110892200d00d485500a500d41016a5410030a02c50b0580f000d41d03c8069041490111041c002c41d5240c52509004008200003138084404c0c2101c2c0e400016001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 295699703 1250 295698453 295698461
    0x601090e07090519063f0e01050a140c0a0c0f06050901061403070b090a03080403200105032e0f0902220806011e1a03070e09160c1a09010204031203 65
    0x60750503220802906c40f29000511600031031451110f800d0381c0d09034101d0130910100340000054101c190007062002004610701d007035a0f40145040d1445245c01c246c414550010256550802c6800d04d42c199078841c64042110b41c034200d4100a440c80309942d403410100f09055010510032a0000c008028854551411b643c281042c5910598554005501404103844404c0140f4900e58010001002d15503030350740340c040d0ba40242d07005480218060840f0b103420f00d030b006030520a907002440c0691440c60011850080008005220507803007031040d00c1e01c0004403010007031002800c441d514544405035942c042c080603501400e41103203501d00042e14200e42000f203005103415140700401401c1c040e130908154000304500404a40d104e00d00c0b0817000501d00a40c10aa05210644001e0042c0e0340d1a0411002e803c403108401454090326401d000c019075041c0e0400520740000c41850445100580c0c5d0400180310005c903514000071490082c20706c043c0c024154000c0003142e11864115810700c0c0000e509070b04035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 295700953 1250 295699703 295699709
    0x8030a1a060a03020c070e160906050703120506030f3f040e09100204120c06051201090507110106080a020f0108070807121803030911060903150601090e07090519 71
    0x1200c0d06014002c2c1c85806a000390038840054002c50ba45d00341c5d140302040c100c0e4820355080071103400100b80440c80541c018880005404603050083c5000f840e550001c000500c12005104050398940115400350740c103001094003d02e4401c1150000b6034400d078000a80d0503010314203072411804881e0958550b400b150742440a2545601180c141454000d0b0340c00c2d03d0798001d003614407501800201b030541540314400740020b810340e400040003514141c507000d40540020b40005050000620402c501403845001d11030640350740c4d500204158a61500c155240044641d42e40c0311035080100c0850000000550142c1d068021552906042c1c502c50054070303282d000341c444c0d000103004040042c1503240101e042468400012078000742d840c812410802d021403810f03038220300203a10b42141a0500c05045840450071500311746052034283d182c000039a0f2801244000b030b10400c121000030b00580c0c003851f40c1c58020310300b0b41117040c06850034020082c0001d031240a003510031119600b5550070041000f00307031003e0b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 295702203 1250 295700953 295700959
    0x111905060706020703110703150c031812020c0a170d0c03021b130e0d02011a0d06090c050405040c0305060a051303080a15081e0c0312032208030a1a 65
    0x68000a0b885040c003a61000c4026024024001c5120b0107041040003108004c42c0940c5142c00025880880c440c107032401c111480c0c082504102ea02c045100c00849029040c640c000b0056000c3c81d408070381a4100520000881c4c1d01020b81d400010302e030203500354240310b030031502030959511910004055035498807603e40580141c0c8800d00000304038131800104520500018036a034501040c105c12001a80c0c50030403002c00035006004d00401c026024081e02c8083e40460747d0248901d4070003800304260004445000c0e001c00c0e119040034090010404000d0042c01d00508180002d06e01810000c41007d1248000c4443e40302d028000b80031030400d880340a000700c503070311103200c1e180d00c15807401c45e20980e010384045101e664581c03001440c068400314084c014a0040080c1035400c08100d500c03045c0d90003000e0b04078016040303115102e00d55540400c190300d00074252912a41c817500d0f4105402240c01c0c10105c0c10113207000400c3c5410601046101461059a001d923051024001c85a841c9641c00c11000d14150 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 295703453 1250 295702203 295702207
    0x7080a2c0a140d140d0e1e0606030601050102030a0e0a030606061e03060b0412050c0301060806011518260102070506060a05040b01080a180204180204060f0b220306050411190506 78
    0x70740c0044c4030061551851001000c103608000c0079000e4188800c0324080c0c6894285c80c03101840c2464140000e035030280044001d08929890400042c1d22071141400c9a400c0054070304020700301c0d41e111014035016613000001041403548424000d041800d041c41006c0f0810341c0484025a090722078003c4d68241c810b03400005081a03d1b20649000e0b1015004045440d800303070b4a1301846070b85091080741d008000c410002c001c2c5515141c02c21094001504550041184140090145801c1e44a240003107030451b1001c00c540c00b41180c0b18088101d004505000503500014400382031280020b0403d004032001c0b21016045655070040000305d41542e515107000c1510b071000a1134540d84c42e0702090480083c0f020b015889082c0b0b60004046840c10516210401c01e82c40c0c0110560600c0d00ca510041e102000c141c4844500f000400d0059000300501407203d030040c40300100041071034007900d100071944290203100c80d080510349000640345c0b03025414010151419001654144040e07010221440549018 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 295704703 1250 295703453 295703477
    0x30801120f080d02070f06140a0e0714030c0d081e19030f0f1103040b06040902010804151508031c05012108070c081b0907080a2c0a140d 60
    0x60b0541121140090096090000300086141c0c0c0018070f0202c0d1061400203a944507401c0009851800500105406803070a240c0d0501094001502c000703480c4803c80450a01070841300281c60501d04490f01780e00004144045d000300f0540c0f001400300d1021104030f004501040c0395030303140d4600914800b0b01958480708000c220342c030b0095100781078100a8540202e402c07060b040d41d6409030b172544044500c0c0d80300b001081005000201d221141c001008403002d02c070050380740c7c00080000d60080c002900200d00031209155004031984aaa114619620500d11150b51505e4407034032a00180c0b910007030700d01d6095440808003510f1140e00d0503603400560441d4810b82910076828429103814084801c0f600c208810004030b84070781180c00c002c01d10034000b00580369600f400740c00030340c1d01c0c2c440301d6014242e10000d0100554002ca005a40003c01d0240021101064507100b40700860450074510000150402c0608076040881d12240b180e014a912081c400302d100000da5070340301407011410019a80180741 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 295705953 1250 295704703 295704713
    0x709081c110705040213140a05030604080a020a060f0911101202220902030103141203011802070f0c06030e060610050901122c150a020901111504030801120f 69
    0xa035001e050748080b205255143c1000c50101d81c002d044451405a040d02c2c20070045412080c4400701500580d01c50146a2400c40407c0e540c0c000a040100401800306800c3c0441d4420001c034a806500f0103c180702020200940000502070348500751110603802071344030041c0c00c014001c1d081d42c2c100365072064402d0715140c0c081d10003500501c108500c46036800c0101ca283c1031485204e04058400318400607682d5140d45400034090b132402c414085180c03c80d5454181454924007501d0440c0d41e1000b104c0c000941260082000380306040c0000c00c2c2c480f0340322130b200c20b0001c52050041500c105407410000d030390941302c440d80e445d00101c0c3d04c2c0e98410a2654451040391040d0007410707e03404181001011100f50014100584503040c4030440300060004445a4107980c040194801c4c05820b40038201c802c110001019042000814503400c864001500c291183d04c20703250410f00b0141c580982c2c3da00810383c0f49075801040b0a403000c3d00003034040c9001045402214000c0c0b54080c0d031244008480501c00d94135 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 295707203 1250 295705953 295705967
    0x60402030405210405060301080d0206060a0e010603180f120e0d0c050607080714100b060412020904020a0504020c03031006110d080a0f180203070806010f0b160206120709081c 77
    0x200348048024000016186c41d418061400f03001c480c80a80320750002e0030002072a0080003041184280e03820320303040015400c140585410b40b8090315000c601558141451b803040e455002c4003c048040600500060003501003241805035140d540c1e81c9040c82d06d400070812005c4d10480080c0c400d441d00032041120f49449002080c481d840740c45003c1c142100c41d200d07507003140f890051417003198101d150006084101c0d84500c082c0d0b0b0608850407410a402c106501450381c201c110003d0180c07468001080555452461500003410014010b5503564180d000030740d00c075002a9a40c241e4034000c800c01056082c06030305035118800119006011560910508440110300544890b010542d90204041801c44502490105421640c442c40304100540b0501d4584852a4452103070383d00240014860545000c84502c11550070760609602c8a05d428401640e40000c00300080d400b8000059680b1040c1120506034400c925903250041c030a42d41d814850b44402c01c05080742c00c0c240c1c1800c00c4492450041c0e41d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 295708453 1250 295707203 295707253
    0x31b1e12110d08060d05070807060206071d090a0b19090506030601082a4b0103020a050903100e0601150f03020706150303030f0b06130501080403050d050f01050405060402030405 78
    0x103034014900151b21642c0c1495601e03002084240c00c070080c24002141c041100c01d4118403145022859150032911052280d0040d1500f40e00c100c01e00c0740071960204507a003041c440100000c10400081c8102051104103519034840c024585050000282c0c451070b000c120070703048903400405400c20200c000000c10404034a016496180442c0e0035100c11551599034a88211030800c0b08002801e41c40b4680d107031000c6280e030036901180c0c501c440195041d021780e0002034101d03102c2802c0241c1c96443c0f0101c20b031401d0091840481d0544940d07041041420300d6900300002400c8814207490203641c95201c03221340030000c0c59000300451103030070010582030700c0380e401401c16a005020009403044952011200c6010b25841134000944500d18800c1c00780c114803c07a411400c0c00c9420b10300d00340701c5950100e903112103480340314184000c480c005004d01d4028030448a0038001c200d804c0003d441c003160f1020102000b8007540380628a0800081d05c2c6080030b20851b40107075002002071a81120f1503e0703195400581c02 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 295709703 1250 295708453 295708459
    0x7050403050a0807060b040b28080f030a09120f031d030f010b090a090308011a131701050a02040501120b06040503010e0105150d020904031b1e12110d0806 68
    0x4000045074040c01082150340c40f0b494003079518001400c050007a900c2c0728900c54442ca280c901e01e03a840380e48004400c0307a1180c00d011002100c00d02d421020203031240940c003c05450155482001c480c450120041445110548030b8551240d21143c80d00524001043c0040c040c104503014003010a000741401700900c18824020071641354030b200170904100c1c42d0901c8140aa45408520407a440c10f850125402064507008010180039500d00810645045c402d0400b821842410705001c1205241124110610350b210340649603550f410559040c40070070784e90030f600d51070301d800305030046181e00803201110380580d980c0c00148600b41d00e10004081d85c001b0503900c540d0801000031617840c213014404c540b924807000014213142202002412103003103000c05209a1040003038100607079614580b19001901340c5841c00d5464180d644c0c210322543d401c80b0103800640100311203444060b1031200b00c0100c0c1d204d41507441e6429684034095410603c000d030b08002c00c1e0043c1e0b0704030002e5803142c030119504c00d03002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 295710953 1250 295709703 295709707
    0x203041406040513022d090405090102090d0312060609050f060a02010608010c0c020901050409230f07240309030e06090406050a0b0a3506030a050729070206120705 72
    0xf40000808600c441048080702a802240c0c0b0300141c003003054240301603050b03c5c5d184900a180346601440e01d110b00020544540d6a54011500f0710b1001d6040d1200060041c0c940703041034100b42406016441c0c60302589072014205100030900500c19201c040890b5400b074074104004424104008031500444150710442d9a42d400000d20700c0002d0068540d24540b9481f0440da0f080940188618940140c005070f001e20b04000c00000010541c1c1c00c41d840101d00e0104d40311400c100707800341d181040c5c41c02d081601140b19004011410007203500782c52503611100e803401000f030010004140c00340e5a40e004050003040e0764080385401030801e42c000741428200280005500d9445000090b0011966007012580d4000820062401500960307500300807046c0740000c89e013000e000041c14000c03a01c10f8100c1e02040c0c0d4001c0c04140d8503202000281c9202c0d0b440019580c106413034152045001c00c02d6083c0941054031307100380d0344c3e400c04810200c501254010307000c0c62503e80c82101e41c400030000038040d44100442 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 295712203 1250 295710953 295710959
    0x50d0e032b030b0604081510030804030b190b030601032303040b0c070806010b070f03030f02070302210c070b0306010e1002010b090a0527010b030f0601051906020304140604 76
    0x82a000700088201d0380054100d0340c140700d800203040300e444000b520300408080100b0301c1082400600012414056031b251000c5983e011000d07000d040c41c59000a0460002040c04801c03c40313100d00c4a480b0b80003101022000010b04940319064550b22030030070381c0641000006202207008500c240e903505007042210440d0300c03002041c00c0d03d503a11542c00b00e03420f46400b1800080d403503000d020344401021124000d0200d03504000308600c0a104600000340f80001c0f20340c4144c10540250030000000181260464440b40c090401946038035040d0303035192000ca151014120b503011908156040c01201d10000e04e891810040c83d103030a035001404240c140710802e480701c0c50a5440200d090742c1401c11742e001140c2c4101c0c00c000d100e100c0d8405011007084500306001c101358040e40c1c2c10116070300741103407001450f95040d0101040c01000b0b16000281c040c041c4401c2d07401d06000000d0801d040b510180c4880710b0104400410a03149002809070341c0041e04200020402008010704000d85a100207200034506a5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 295713453 1250 295712203 295712233
    0x308070210180b13080c03100207110904030513080318210616020705060a171905131e030c03140f03070815011d0d0804030503030405011413050d0e03 66
    0x10b11076120b001146000100c1481100d082d860358030003040c0354001001d5000c50a400291500301c110721525200da03021901c10103100d000244040007a8014049103070a050904005044d41d0202418004890b440365000518100000c00c94507900ca410410900e00c220840802140d9403080c92141802c5500384800ba55450b018420940107116001030307081c0b80c4e0040b4001900f82940b5501080c0f0603582804180c2d050f682114164008840c2c00d0007403205551084401101000b011a890702024500010001c1d07020651300c5c1c00900a004051250070203c03d0420b056060244d00c40080000342e00880f10f1300028064001e68a807116007d4215041903001140100242c00894011000500400078800e074001c44034017400202c00203180142c1c2c1240348092030481007060301720150040400d4400c0c04103215014090307a0186500030700f683e0f42c03410315090150203084400b010b40c07016914900807401c508054400c0d0f15082d980200504071400340c9080645040041500f010307014041d01d034515207041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 295714703 1250 295713453 295713497
    0x6090a030204060b0c100e070306051e0c0406031103010f0b0708220306061706010b0c030c01020c0706020705012307021507061505010921050f0d0201060603150308070210 75
    0x30013002e411548070f452400500e03290440300800c105e155850700042c44411080400e0034001c0d00e0b0441004903454613412521305030490782c02140802c1030383d154103100140c0b0001d4020411600c5665052007070aa01100c01c10440c40f080c410440c690741e1804d4200010f03c0d4000160010700d02940683c1d090103030320035458602e08440c400554600070381c40d0040c400c01840341300d200c000c1c0912648401d803000c80703880f01c69038511341801402c045c0c2030089000511000d0030401c40c0e00352807040f002992141c2c0f004204d207540e00c00034010000540100180400c403075100311455900c210035080791004494000301000996444042c003a07801900b845001041604410010010035100310400540308991112200003041c05402c12030401ca100d0008000c5513600140642000d0440900c0c0941e00368640b8003030f0710707004000c2007010103030242000304c2c1403194066019004607203441e1400c1c01400344601c006000e068840c003000b40109800c0c41000c0241c1031a480200c09070400d4240060707622080b82c0d0140d541 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 295715953 1250 295714703 295714709
    0x402040f0b060f1306142d0408030d06141e010201090206070b0901110c0307021507060504030512010504150e1005090a06031a01030c03030f022503050c100e06090a03020406 76
    0x40c00020500d00c4c0345288030071031000300f24601e0708030404e0900c240008103034801c050185410105120301c202106070700179401e00e0001e10101020340e46a0740c42e001d0340d807603030000300160700c0440c036241e80051400001c21100f01c00ac0d20082c850a80782000e400c00c10b60131341041c02814115940d0704085801a11b03280c00500ba4140280414086803a04403e51801e562000c0810131102d002406030910020002054500e841d0341103a03050030304000300841903031714000c120000d85040d00741010b0000b4541c0150042c8842d030380644c0b000e02680c0e02d0720300740000d036a4180710303031f080450a14808000040c40c40681c40e81060301e2010051415507290000342001e0016a010400c90f40e55100400030412810701803907501c1c1d903211040e005985141c90b15034400150307200c05020f0048a00d40a101c881c42400502405103481d03400781d50243c1f40f140010035541c1c642c0011546485400c25410481c5041860f468402d2a80d0b910303110105c0002041c0300c2140c11200c0c5154004050358004001030791a80981406 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 295717203 1250 295715953 295715977
    0x50a0f05030115060503160c1e0b0702070506030f0c0d0908090a06031a010c08070602130e0c122d0a090b01120b1b090405090d03061401080402040f0b06 67
    0x182032008050850b40c120560000103104103000f0003c540d08642600c0e4040b0030b003448412a040920800d0326507503803005000307104101403000c507500726025001c00d022050103640d0030140f80d518080203a9450400740151640240d06200040c1c5c40e035040031003c3e03070003510090100d061203036003003500c0140d500038641103070080b5002c03c484080b42401000100200264a8203104842000e00203800c180138005029040201180c00072080c04529012100540da010004660b41c080c0c404101c030003078070035005218030303000c00001003051408a0703000e5550302c180d1104186a551200a28003110b034400701d401c414007408841d900d501080901c4011489401550008038407070110385000b1062010503007007201e603000c052034840b000c500e280030450f41c07080f00880310b00b43c1103103074100700541d1340208280180c1c89414881000004000451803040c0040b40303840a00100d43c40e00c500701d00d103011071004140000c15840024003d490309400205941d821a280050f141808c2008101d080d800a03009201e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 295718453 1250 295717203 295717229
    0x9070305071d01050f030402061e070201030f020708090d020a12060605090a06031703100308030112060c0e0d2619090f05060307030e0c030105090f010f05092104050a 73
    0x100542c024600040c0450341c0d00e03840c042e04030150000b801c2130095611000794800084009021502d500c801c41c4c030b8418900d031100080181c80d40c001801070f4040d0f40102e00007410403400240284460090351078880d4030207811410854140c00b8003408418641050b03900003000700001658440c266414024a80203800200b00f65003044140150454084c0094402d54074120302080840c1980034090313030031103a00c9c910907600d03140d2242101800364103030400f620120000000140f030141c200d01c1301030070030710a013400d00c0351700c0204d1015a04410548040f40e00444100640d038005079030300750030720f9100c1482110f0401da5003902c3e10344070064005070140180030003041200e160303481e0001e14043c010000c01c1c6007503501c0c50801c0c000c030300203000140004003030640710b0099000c070000c2801a1660302c0d002400820041c5844800e280d40c034001c404181009500c6c040c040c0c1c2801c0520300860748101d148000900d1007224081b0b25044894241100340740f1104c00303010105956461060036001010305c00c02d03001e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 295719703 1250 295718453 295718461
    0x4080304020d210203133f02060f0c01050f010f06050d0914011e020406020709050702010212040c1d040f031404030c0608040b090d020c010e180109020403060b030312040210030b09070305 82
    0x882509950020340c9074004d4480002c1f40c0d114981031030f040c0316801d080f881d600c0311070610402c400d240700108001d52004010400f02c00c510300d404040e20307038900e198000780a0703900c80e51641d4030782d51020b0254909449600381c0a1004900402c000c5c400980038940002c2e0510554407000100000450100c1040c2d44900c40b008199007043c1410001e41841001189007a240c40e501a51710303003080c0b254001ca240c451000800982c003e506854851500103501e003035500c1c09141c6011007110302e0040c0f03090b085035484146541005010326500c1141e2180d9041c50908158800381c1d100102031120f0071604604020103c0080c0f10400e000d0000c1140d6214a01941400d02e0b104205d0400201094041da00407091410601e0b40001c10700e402380401e0070034060f100456000b01c2c81c660b2071403480e884029081030001031880880e60081003101d0107001b007000010080000c02da12031182c8130301c09841d40060b9000c10058500490f09aa40589906000070601030503008034140d484101d50b100d010994503000c01c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 295720953 1250 295719703 295719727
    0x5010e0c0c070e15030a1b0602030703080402061b0f060403020607050702010219020a150518010302040605030a110904050f040c090b03030a03020f0f03010f14030604080304020d210203 81
    0x25000032a480826060505441d41140c2d9120702c0d205040402c000352004c10800003000d131000450f404041c054401e020140d007400c05424180316080c114842c213500703001540750310100944031075541c03550b1007541030b80313450b0204071140e007140360342c01d260b00d10085a20108400400c590300310042c54030050209450700e400c01034205a4020044006e110f0208140130050780e02003018015089003001c2d03006d141703085001040c44840070790001001502000109482d49070440098188400c511032001082003180b001141030303005500c07900703001c00d0b801c0c030106a14944030703004601c140d145950010b0a212030328001500b50b44090721150a1049039070140000e100102283e440030300040e0a0034415095403002080d500d204411100782010381c086014044418103008688040c0c040308109916540c58580c12000f00540707108500001221001640003800d0200d4001e00c03036034202c2c03a41c1d401d6070307515000d00c070b41c078512148100c40360905d0082d403e102c500294404030b00f400c51a8019503d0300d9244240c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 295722203 1250 295720953 295720979
    0xf0813111201061508010509010f090e10060611060a020a0e0907030b06040b0913140a180f050f150702060103240c0504140609150a0c1502190f0905060319020d0501 72
    0x8203006948c40c2d40144030504014008004941001070300148000c41415945c1c01e0655234803003501b00500344840041c0e030aa0005150740a4090725007610700e29160788040d40100d120360f0b90f0070804070f44e400c070091440745441042642e02480074140072480400304030000c1c1c1c1d10751082e04100e40651001c65962000d040013100002c40c007041420401504001150380070007524000e20000c01c250715908180218011050903d80a5900c9040124078076854035000f1745800c05c0915a04051040b42c0203100c043c1008009a03001e81c41c41d4018040d80d90a40e264148803008100c614001c04440c80c540d082c40480070302c03800c0c2c41c40d04c3c2e030b0303484a85640c02c00115134100041080b246200e01c5084c410b03440142d56801c5e80c007500a2038500d4141e580d000c0000155010400c00c103001d0000d05401d50a07083e00348494006056560842c51485056020a4010380d4800b84030658000003c1641d801842107041810043d5004801c0c03004107081d540600c8154420b0364044540061980d88540c0108205a00c030b010f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 295723453 1250 295722203 295722209
    0x30c0d0506030f070b0d020d0f06091b0e0918030307030f0b030f1207020d0f03050c01050117030a080408040b04030309050a060503061c020d06090308070f081311120106150801 77
    0x101801040c084403043c3c80d1344a200e40503481c1c480c0c0c40051403071000700326036045a03403d50708100c05105440080500354014000c80c441c0811060402205a04040001386d03609050b08982c3c40e60800030003030745c3c140301c1c201e40c00034040131120441c08081c4000f400e0400c017641c49680c00740d4000c11400201080801507400e0b0388403160003a03020100703201304041c0c0815401c0010340301000140d202c40c054000035002120002c0c2c05000d400f16003480d2407d056000e0010113003200d44000911541c0d81c0c0311820340030580284c81c801c506400a20a000c4291300c507852258006c2d01888009040649408484c2651b5110342e004030b0100e28030000801260400480345402001d02e410114107526100000c2248801440035140d44400501d01071400c6548034022500c0c101e400000400c14084c140c0360180c00450b003500c254020400b414041c00d1070501c030b451594410794400141c1c200e0021240d8828050300828000290301c60a100c0c1055481d007030034407885004002880d00703228100c07441d00e0702504482041e0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 295724703 1250 295723453 295723459
    0xb0f090f0610170a0b0c03011d0105060d020d09060c0f26180a05010203070518030708190c1d010f0608090c06030903120c0405100e0904110a030602030c0d0506 70
    0x1400704010001c9010501c0200c450050035500c0380445990700034248039409800034017200813401440581005000614180c840884951100040840141810220901c1044e5001004100c1d1130203004c843d8000d45038000180078080b50702106980c0b820190b540d205a41000501c1d801d0303e0b0380c0c641d58004c03924020f500214110035920507414021101840004200000c0320032422040080d43c9400c02c020b49196030008000c64a906146a000b402e0350300508250080c610950300a5456140c00f003032070b4003100d01d00801082d450b18010401510b503030074024161180106072100144444103a403402c5c2c10b102d614000c00c3e0ba5581803070014685032143c1c0d0030500030800654100000d01030000f42006122030120740382c0b0f44075030f00c00611600e544220034400705d00c40200d1040c00304400400d8050801d643c01112003003041d40c1c4c190303400c1b9030784115060300e154000284008180800c030083c004190b60040500195411038994036000e0aa0b803060b5100880100005024004190700d03208040c1c0044c030407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 295725953 1250 295724703 295724713
    0xf04090c141507020d020904020102070810020712050a020a0b060f090103050309010908060403091e080a060b040c031107060b0a05090c0a020d140a1404050d06060905010519061b0b0f090f 82
    0x303138010600b0074820110081c010140340021400b903a0003040303280020714141c003c40b048100780542c6040650881075046801131003103412403c02c00e010b88161044a18154000d00d49103040e030b110710004031030140c910b81d001011006030514035211100c485000c0d40c010002590f4a410090006000e48016888250b00741c110105100019611018403411507840191402040c0b0000070804e1501c0c0c02607100c18024400c1c900c1031020818583c0180101c0c10080350108029203103084290281c52240c0d440032584481000300d040082d00076840303c48016405030449140d55203481c046500c00c4000c0e610310103803490204050b001603504024848825840d8500781055503d00c521061050040c80700c0c901c180545580713110110030100081d5002060001c1c05446a00b466040100041c111030041c141013a0622002107500d041010007000300440315031440c44028981003081f900b08040c1d404c114246040205410081200350034030b24012401d151032404281402800c00d4a05991050398051035005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 295727203 1250 295725953 295725967
    0x8010506030a03030c0e1c021003020a050906281e0527041b050c0f070b09010f03140a0f1d030a032408070e010605090d020f04090c1415 60
    0xc02d000d4585645400c0125410110100c180d510100f01150280c10404031145c01c525078083d82a05041d1500aaa5507401090100012000d0344240c601080100b08204140c00642c1881d10080808442d00040755644254440c001b10417140e850b038106000540c20300358002c41d00310054240c020701c840c0c0c1c00d0039480c11600f06000d0405c0c0c00d404c005560a0801f843c00d011907500c0b5500700c144640302c1034440122410401d80081d04941200c0040b05040c8a07202075640d400c0700000d140300c160784001c030721311f400c0031004d6004441c0c000d244508030003016200c480f14000d40040354015401480300406c003207000000a481c51049405c11044158203404100820000d850003104650070702072140f9022400c02c21000da20728804030094071f08080542c0043c1c0000319a04045810004d50707240d9100700d2000c1c2d87c1c900045030140140321013560b0207101902070304010f2400080d5520030300310280c0007003000101c54540c40c0840d10658421504900c034540081c0c2d552a2aa40014401d401c03940c81c2d07428403071 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 295728453 1250 295727203 295727209
    0x603120a1205060315011e09050f010509091603030c0b0c120a020d0b120d1404030b0c090409061e050709181113080c150a050a0c03092c0108010506 65
    0x4107a2126548507940e0300c01140c0e681e2014070901c0d81040b1040e040d0030f02075944600020590034541005914030705907040200b20b00c070b818008c89020311004601410542d003450100305e0800406841c030718151080c2403690101818002c2c2810065010351100c1c0e040010300d06003144020802007100003d49000c200c1e40340c1188a090400d900401e8060005071140903001c4640020300d54808600e61040b6692900c5070044000101490160a541d44900c004032071000c0446d013a0056002c010078064000d000650758030020b402501c00e41100400108803110039885080031169019640c0d000000403602d1078180a85038040d80343c1140c120f1400442d00c628240c000060000c10150240f00b96884500e045040c5082d01c00341c440c0007c0050040701c541e0b6440c00f03405e540d004c002e814240103200150461840c100701500391000f0441644800d840c1400e401411149000c02010481c1400141c2002007000c0b2041240101d02080c0340c1c1c041500000c4151402582c210160300c4040b003681048100710383da407 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 295729703 1250 295728453 295728467
    0xb10180b090a0b1c060b040b030705010219061b02030c0705010f021504110603010f06090b16020d0212340303091211040f0902011704110f0a090606080603120a 70
    0x142a40c2c100251164504000881030300304510a0720460100f214180c003813000c1584098040d0504840c108103004c14402031540f40d4800d0307c138160268003e609585038010322150901d16403481030304002800c00302000f040890744c03002010100181c3c000300d850b4100d81010010340f0040c11090030445600325425038020b540d0048980e0344601491140003040410000540c408018000140019102e40c0c49906c80c00200d1203034840c1c800042c0401c000028842d00311002c80f0400f05d108000030882010340d40030b01580003107a0f08100c0c2c000c500c5188480c003000041c421180e404d000c2a81a051002c00396652400c7c1d1030020059052441109104000294211034200c040701c3c080c100714003000c445800c0c16410000707c400e00350780007801c054900004207001e5000000061003629128455070340707090244e050b04011540109000080800d1290510b440e60441c20100001011002c2c2c103500d49807140d040d152640d00c250080303000348050050340d02c1d040c00f046800781d4a040c0030f203090200b00e00000f0082 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 295730953 1250 295729703 295729711
    0x60f2304050606120111031e0f0105060304020d03120e070911040510030b130f02250b07080a3e0c0712110d1203060f08060a02090301090b10180b09 65
    0x1314102078003040b00c0c800039000518820940d0030030790f0702d81c0340403080e2001c0002028040c02c450455180028041c0d6500340f0942e05841d4050310581c15a99140d0070b01102c86140b000680900c1440120310340181140d000b22075484c21600007605503e07180a41041c01d50b030403404250000c1030148814855a00d540f000e029a081c5680350201d0403032030040c00f00b001005010314419040b420300010040410b404c1d0003e04403100d00301c803d22400c02804100c4900c45050301c20090840c0e01c4e541c0422802c42c400c083c030680201009100082c019141c0c1000c0200314541001d003041c0d21442c0c3da055459a0103445076540c4182c0ea540c0f06868105608012901c543e814011108080443c2d80c003401804180784581c0780c0c820b005000e56001a6060030039203403098900e55503400103410320002180200d8020543e8044ac2d00960040030107071185084200607421042007150599640c50003803020640b05100c441c002c3c81d14210343ca070010b05010700c3c00300074100180c3c0e00e0161820482091034544440031580e43c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 295732203 1250 295730953 295730959
    0x70e0906011b110f10030c09051f11031303050c030f06061f0c0804060518040e030a030f0906090c090509030412030c0201090b030a1a03060103020d080f07060f2304050606 75
    0xe0380b5000000c0b850000a110729400c9071211700c540840326010340c00710307000703011030b03107462004582d20810051107140181141050210100b01900164041c142e0050440c0d007400680341000d48400040303903002000e902c00d80391580f1940c09000e00303080901250103800302400107441d043c504000403d0030703015a00542020509008480c03944684900d500c6001c595006801c1d0340d80f04d03501c40c3c0c02042900800e0030800d400826442204881c6014800c050403041d6500c00b41d42000e03990070b4140d00030100d401c0900000d5460320504000204240310744040c0600c0354440701012828054640c04907400100b01802c10b5104100a004a14864866012040d410718200303a4542052004890f904140d0b8015a44001d000c002d100c0140c9094000c0e0500c4244c040d00d01100758110010135640e01c40a100180d000159201c111005c201c0c22401803143d0812044c0701c4d45031000b180e6a90f41101d484688680e100f80c0c3d9400040910303e1020003008095801d1040b100705030038503840350368a400c9c0142c141c900c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 295733453 1250 295732203 295732223
    0xc050609090c0d021c0902100e01091a0f0d02040815040804180b031b01020c19060807170103030201090b0f06090c0307121406030708031204030e0d0506070e0906011b 73
    0x30002e0140c4e0100e84010f00a5081c010b0060342c584000700107080751280880c807d202d90404107040e244101c0311802500c4051399880c00300780c0750050b4586c02d41044110315041c1c05041001c0c0007002e03025001012050000080140d65074a41406e007410600000c039040380ca040c50310103000c042480076003504c05840301c03000c40410280041c0041030062603007644580e014010000c142602d0341910444810004080e001d40b002000f4000400c00049800748100c031161100c1041401543c1c8144080e6a001c0450300b02001c049466411000303000b40300340d2040700140c0d1501c40c2d000401003c4000346810004142da1400c07141421000070f40c40c207000400001da030040102c000340100744290a0103030b06903c1407004011581030101f00d0503448400301da480d4040d114900000510a000004445001c10040c01256460f00c89035022200780d445d886605a10480b4204013001145c001c0c810f030b0b40120003030307112210401c000340300b4002c1c103460041603241407101c400c00949000b64400e4200c80ca00d23500c208028 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 295734703 1250 295733453 295733467
    0x3040c0302040c2604021e0307121106070503030621030a030507032d0c020a051c0201090c0e07120204082808070305030a05090127030e0301020c07030c050609090c 72
    0xc03045132800307916400340742c81309100e0038480406801d458081e500035036080c1c0f04000310b003140461a80308110100c2c4c0550000c0d0f000c101180391914030310366451081e1400e400c08603030900082c21325044071072300351041e8100000b8800149488251000d0f2840075000c01c2c8158072010f0101c58a900600440324103060f00e4200090070203110f90301c0545140b4800103800340945418100c4035085095500c14902146041150701c1038034000030b92140c005030b101005042941e8549009c0c1d0341022103401000a540d21031030400700050104c62071074050401144d29201515140da0b0007010300614021b40c4d40460300c100405e02c44641c001c2a80c80070703c4070700f034400c0d1404075280c400c1c0103080b0800c03540907204a002140342005c240c6e00600650140e42d180b401401240c07581940142281c4040840b80e001075155009510700310081d404c2c0180140c002c0c02e118841107000d2002c00d00ba80d001700010796554103e44824810040307004d0301200509402d850850400d400d910215500c40c0000d0030341858114003040c24 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 295735953 1250 295734703 295734707
    0xf0f0f16020f0f010b04051f061b0204050f06010206160509040b030304030602180a1e0611010902030d1806051804150b0a030f11031b0a1404030807030806030303040c0302040c 77
    0xa6101000b410201c8081d140c1e150030340e0b8001e02c800840076100e5420310010170300d45034520742c030007114136640c40d8020300151074004141c6c3c03460031a104101004680d0003030040569540d114261013082c20070035019039450324800082c202000100385503201c110b0703041d6038401640d1020580b04401401c3c0d0300082c0d00664440060f1940c000c5500082103103000040e02241e400c0040400b1130412030982d01182c0168403101c080c445270b0308240b11202c150300d1081c0c04001309031003004507030001d80c450710000413140c0050f00440d08042200704503e011410b0744003429204c1070103d0149004005614046081c02d480e0f004d1458031100c0306034064881c41e02d40d8450745c0c90381c0c034540c103400c02800990071003a80d0300000c41c03018016094035413683c050540740c00240028206840c1c100e0307204800d1008107000c400903145441809030402c01c0c800701009516103e0440b6018114001c0010354000c80c002610b4044606c0e00500010b4000c190074042e40061040c440012010240700e4141c0e0303412900450010301354031003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 295737203 1250 295735953 295735963
    0x123031602161e03020d1103010c02030c0d0507031b05150c0c1509150106030e010b010309030507030c140a060203090622060504080d0513060b060315040911040c080f0f0f1602 77
    0xa941b120034801c0b804100505030502d282550015002402060701210040e41c0364002c005908200744c00212003518002d114100504000d403107803d01d214101d84c0344d181d50341c0d203580d110700403541ba81c0155503024200280901c0366610501d2a0f50fa00d14204942e8034090312180000001400d01d46c09501144244809000465503030107550743c801019a5141c10050142103541310fa1801d07940307012941c140303d510a0042c401c00c0c40e01030300c0b401e02e40301a56a048a048682d400f00341c0340c1421290040d05082014003811402a0103407d006da00e03400d22051071400c0001c058540f0300141d5030710300c040d1f888800006420b01002d401440c00a45a9218102840c1c2d0740b25107000340804c945000102300e03809604509a60110740241030801040207800244a038a00c805e030b420b003411108070401075000346415005010003d01c164200343e81454010085410b4401d099040800f00d01c0e90400c0080303d40c105642d06901040303007818840c141c100303200303080c11058018241a411038110b9440da0507590003000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 295738453 1250 295737203 295737209
    0x605090f040c0f17073204260607020c130e0706050309010f0515130b0a0b22030206030a1a0a09050108070909120e0123031602161e 58
    0x74090341c0d41050b40204460314407407100000c03d0315010301c0210800d42c103142c68450241c980364075070341460000720007207482040010324040e01c40613200e010001c002c441c0a4401880c2500003402c00400c18501d030317500304000c5501204250302c2802044075155001a1010030301c8070549079207103110582c0d00940050070000190f00458402c0701ca00080c110380c00001503200c1c40c4440020440300e6522440c50701030300ca00351a86101d410700b04030360340c14500d088510751482c030b040402d00042014034500441c2140d401544030044404002c80e003104a002100103004510f801031100403d00781c00c0d680010550702000d0042c251540c1d0300c0c8d400c5032071035801900c030401144004085942c06982c81c5240720103010b007400342508030300440c14000b4181d6801d00400740160381c844036843c440b900d100c104071182054813211504000320005403c229078240c0a111807020029024241e40e0724215030310082c01c652a00c81d030021907004400301c5001c1200030003000191403900c2030003032001807580500c4510b00301c590 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 295739703 1250 295738453 295738459
    0x213060f090f1d0a1802010807050d06121a0106050304030815120f0106060207030305092b0303230c0304020904050f0d020a0c0609050102030703030c020307060c270f0605090f 77
    0x1601165054146034454145a03201003000c026544e080038510558070f030706000044410304c0d01d00000041d03000309a41076200816181413030030700614210000540b11240e01016141c82803030802428080b4038507441c20851000650380c6410352626000070490b1100510142c1004100804502e21111188902004040003450500303600400c0c4081d5803540406400c485c0c9a62804400141a600200f80c444c1100c0d0940c40c1c00e41490140014000c00c113000e86821056192041c402d003003469140140e51700003601994002507900d0000032800d25041205204208003481a0200b042185d10b082c100c03a07000d40d0540b00100790791075503c0e05614120b004607011142c5c0c018040c84201103a40003892a100c140181003622455a9440303094079041032138024140181c00030010710300428040c1e0440d2040420031b10440b0300d42486a110350040743c0e10700000c58005042c03180003041a080860421700b42009070300e9600c43c40c030700d03000d00c4110b40d92192203404140100070811007142e40e81c0101d1440c5003240a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 295740953 1250 295739703 295739729
    0x2010603200d170901031d030405061b0f1f0b0d061508030423060304080703050c0a020604090f1506091512020d090b01060224041b0803040f090213060f09 68
    0x20500d24060f03800c00d10191780040d141c17a000c00e1200c00440090785c081e60140015610709403c02d005e1105503848004190801039000c8826400040100700c004500f000c03000107030100d500601644041c050600321050509421320401c1c0e20706603261581134446940c40380e000101a142030300080503541c2c00754007200e014000840d0005403624142d440c400c840d2800003543c0b4006105204000680c0030a0724007400000050010000182c000d0000780031300100081103596404e801d07070000306203501c960010b414164450b0022102c02c0420301400c0803c880d00c043e4040c40d40d041c800010708030038891080c040501200f400c005051401629504881d1068110656854001041e0345004d80004c041c1121600c0001000051040c4003150f030100c4003c2c240b0600040540000d0302c18900003001e44103480c5001068003010030400d4204588004004000156440368605070b503008141d070480e48034000403130041007090480c0081c03e25070f4050322114201902c4041e0702500c212400c004540051002c1808 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 295742203 1250 295740953 295740983
    0xe04020d060618060906120b13080d0213051e041e060f06171b21040b4c0b07060605131404030c060209031005011502010603200d 57
    0x1040f0003d00c9034280c0d00500c10666140030f100110f810620981d24420140094800016601c9620b071750413201c40d80b01e2100a14075519203964580c041203e42007100d80c000ba80c82e020112030a02c800081004868111314000101d003480c802d0b0300d035441180d10440ea12840d2482e213244206504803500f004010800c0303007a44a0010304140115802041c000c103640c035515119104003000700500c80d580c0450381d102c50808400c81082144c00440c1d512407070781c0000b40d02c0c0740a1000e40b0200340c0704500803101a54a42032081565200910b10140701c1d5034a0900d5010000410001c05104821071000c0480b042044c101c0d80d0400f0403032104c0e001449808000074180c82841019003000c401d0750300498146230501081c4810504982c0360911070f08620140200150100f07002c2d0601e072721801d000302409850803952400080c10654410200c0e0442c55480c03005102e041029021054102d03101c1c0005c000050842d110152540303082145449036402104000485440ea1180d40788000d910400c0d1080d2804 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 295743453 1250 295742203 295742219
    0x80405030d0e16210f020604050612060f040507050714070e010f03060509071802130b030a06060305060f09010302100224090f070605030c070c0b0c0105010321090e04020d0606 77
    0x10406400c90000c2d00800000b05441104041248500c0d95428040784e4000156840550018814109a070310000c103000c0020940c445900a242c4880020030301c00340b900c0e00404120300750011420550140746803001708103075950090200c0712107642101d02c00300400004000c5601e400b0060300003500341d0780ca42000045d41c5030702c101410196485940b007800b40760b0703610405982e280518481d545c425032507807210f003a90318000c4d030003000c80300050702155860980780c03515100254001da400354440c82e034890040086a50521643c0d4002d04211105a840800e800000d07040304418040603115410190303418810718001c1121075207c041c3d0345603111040544680c0003018080403503d60f0351500503441e690460081c08210102070303c4040c3c40f101c0c115141c5103072254583d00008400c452a8141c80004a64100407030302070020310075040004206581185000750310b03094030b10313a0b06401003170400c10340f00e1564000d41003071306071542440304042d15075417400000c00440c0002d0003d00030718a403400205a43d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 295744703 1250 295743453 295743463
    0xb0903100e0f0d030504080912030c011b0f033c0e010b1f17070302071401061518030303090614041b080a0c1502010209150306040513050a03080405030d0e 68
    0x4100141500d010300c102003010703401e5030006c0350000c1140c00100702e8100c1a26209103000034900d03051013103906002c0c0e6000c08908583d042c0041215488580b10350607012644410b0700006daa000d03242c1404102815004400d840307050020013282c410450001d94800e08944905100845c00c030a0180700d501ca2800c03245000b00a00c450039802159440c3e0402d000210b05642c4005082a540d03c4a10f41c046486000003040b0380900340c1d00400da020068100800d89901c0c2c44240c5c0707440480001481e0385007154001c08560f10302e000c0303410b0080303121840d20320810f0b6000503400c481d01030402094070381e19454020020300d82c080c4c0c410b220107817081c1440309003c10318000d0051241c030b0745080e052040d142e80034241d86a000c0b010081071a98450b000340f0000c0811407043c2001c0809000140c180700c1c03503070009100d03c120b100c0031201d900408404c0011500e094001c49420200343c0e24a0340200f08942c0360141c81e40381c800f8025003801402008602040800c0040b50410400f0170801c208030744211000548032 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 295745953 1250 295744703 295744723
    0x6030509060105060901080a0507110a0615060309020d0f05070e0108010917310803190e010c080a05070c050303040b0c061e16121505100f090b0903100e 67
    0x5807140304000303e41414194121440303448140c6030001144e03240324003907001e03010080070102041201a07080c82403180400c066014079114110200d0380044810740c000d100340c0381e0389c00501010301300300079440580c4841041417042604403a03c1324241400f818410b2921302c1a41c0710f04c001035101000014007000661024504500c202b108400307801082c088042e4601403804041c1c0005990b280030401400c00b1140b100b064017451a503500341951f141e01c6141142c208070b04400c5242030440198401070343c0420351403018002400c00704098111500c92040d280a42c0160400b0700000003401014030a002aa0304000c0100030308070796807951910720203021900005290f135158407c0d0b1000c01c0008481c80041040d0444500311401c2c142e6512089030a0001e44090130000c0c400221003004100800e40201c0400461100c0811200d509e0031042c0194920245203840801081c140d0180e6040e602c144880102c03503030410250340714050310780064200340c491101d60750401d250003054881303108080384050300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 295747203 1250 295745953 295745971
    0x5031204170c010e040f09020603040c0305120304030c031b1211010b0a03170a12090506161d0103050603010f0e1011040f0b03130506090f0601140d060b0103090804060305 75
    0x1e0203031000c802e035201c2c0e803110302c41d02046210200c103606040c16400b4007480c4c01c3c2c4401c080740e0114103402140e5180d00c181c400769440d036420381e41801409410441c00001c0c10070001001d00d5490a900e00030840a131042d4010300308411400c1300507011120640c03e03602581c00003402c003c0003684400140240440020300c42141d400c01407c0c1c50341e451f0462200f400c0720741028804440d01104104000c4640c0503e00e031000f80700d01c0c04105920f10680348140060148100e000300f41e1030500381d00070720035a10780000940c208540c9281a841c50ac0190341800b840d12003c0c2008507054540200090141c00300302c41402070706162070300716030400d0b1000481c0b518040780d19504100351480003481c11028441c90290184a104441301004030306070450003180c1c00b0040201e05003001241da0b980a00340070003555407228590051151050050b01070000343c1c010000c0700c801603407000c6040d000c82d00c5c6c054004c0c00a044030341d407501442100e0b40a0b820034082180d03c500c455a4940d107c8601800402c01a10300c184 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 295748453 1250 295747203 295747229
    0xb031021021302090d0b0a020c100203040201170c1b01020306090a0b06030c0d1401060c1506080a03080406061502070f060c0b0a05090c0a060e0f030a08120a0605031204 74
    0x110300100c00892445401500c40b0702c1208210310118060340c49130280c43e4020501c3d4036500c002c1000b00030242e025142e180d5000d6610307000d032503105160481142071400d28a204000703020040c2e0304030520f20300f55528000720f2070103a0341e0341000d100d00d8003030448407210041c088490910100300c19030080d0b104031412210341a403510b5804a003000c8810303509031140c2006081000c5040500007030090038001c2c60001008c0b070403420325112445114420391002006c00d1f040c61007e000c00418032812031a40440d1903040180b5840c00403020b40e070340c841420140900070f43c000400c5c2408495003001c1c0140c26181c1ca103148041c08090000c0da01d00c807030320808955803032142e0081202480f80304010f4840381c00020300301c015100c01403482c0003000081d141354040e101e4109450500c1d01e4030000c100c001d00d540c0d21000b070440c00344e00074007005c8107803403c550303102e504104400e000040580042e130b28203c4a03407032000700903660514001c00074140382d00b0040e8144641c662600c82740d01a80300070010341e002044004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 295749703 1250 295748453 295748489
    0xa140f04020307171f06230f1e0907020706080703090302150601211e060b0f0a1101060b091302090306061005070b010b03160f05030601030b01090b0310 67
    0x486884140c0d00254076403c00f0404209003202e10300c0c0010764003450b60640d0340104292021900c2d418078621080822038495500f0460320000200912041c5011500010345810a200103241102d4001e0501c2c070500c180d040756082030024090101040c1d4000d41030700100c1c2018000a5500c2080e07210384c1c0d0018521000280819100380941c2d0f03011545500100b0500c00e0001c50080d68850082042d4108590700038550940c0e940c2603460b105612682c0000650030052080c0c0030f22031000010800d0380306007464800c1081c60347c07940480341101c1102c0c0680d5203409503020103da060b083c4644964035503007031002c041901e07042c0303500400200504442a401d9016054070001c20382c06945011981078002400080b65414400d0200b583d200c050b01d0483d28144560381c860350440710070f0b040000300c46000300c10803900c040c09281a4414003543d080c084c80205500c00014518480140802d041580340d50b03080250781d0160800744040c3c801039401980340e18015081c440c0110b100c1c4602200060861409 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 295750953 1250 295749703 295749721
    0x50a0f14012105070509030618061008060c181008070e0f0f0f011e0207031e0c0314030d05040b070e040501050a0504020723030a030e030a080f0a0e060a14 68
    0x101c0300d01e41156403003594400b409241100500000f8848018010104200745c410360b000d11111744586803848449040880c0c900c106031030440000c140008902032000180442e42000400c3d0b81e2290901c100150354a41c142e07400f4038a92654440c06420024000215481580010a00348184110b6540c506186039403001c0100646281e08082e03080140c2c00a00c03042420700c591910b50f10b180604100030048000e0448051009090720400e0041e080454280200710b0f2000d5094901011503220445180c52512869007070060341c40000c1c900204815214035840e4144123481ca48550844100b01a1900b804d101d00c08400480e914400900361103070b10190707490688071350782c12f0b80c8020b0680012a4104000d000c000c0d40a031400b600c222035081002d80c4015040d1084c00c2c10704101c20040c6844007640d4030081c058509000c00d4611640045c40400006d40d4080006580410a00d02034240d640b140da8400c002484c100314030020318092074003000354001b000c0c0c0200d080c00140380e901c1c41c260341c0c401e00a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 295752203 1250 295750953 295750967
    0xf0c07122a03020f01120b03030409090c080601030308011e03080d021b0106030c09091505130c0f1a0a17010f0f050102070b03150a330e01120c0207050a0f1401 70
    0xc001c0d4000c1319a221021594803032180d002c49000c0c40e020010748080c0d0540040d16640007603002c81200c940312003419080018048141000b824600000e295550440c0e5018080b00300502411034408002080b03808080481e400e00001180c20107000313603480303e1200340c5001070740c050030500d02c0102c14072040011801e0140b18101c1180d803c110341d020107905002c0d410b40070304258071056540d1003450150307010005c43c9201d424054000040800300706440c500c1c0c84009026544d0001d18089002e007820449200d44c4010b04c210040c03402d403002d030750f682d100780261000c4498006200d240e01d004c000108056102c3c0030074000365855420001d001d29910001207a80c1e4a2600584008120500101310b00e491326050344180850700520344548141c40c0e07410070a0500d0f000b03204550386250300d400000d02080440161280307062610b41042860078074000038050840801c00c42d9041545e0f901c011503214400c3c0f009501406005040d007a649686031100d0007c0100341c001c10010107a042c120440070746c01180307 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 295753453 1250 295752203 295752209
    0x40509160501030b120304080109033f09080c010501031e030203040513091502090103050a2a12060303020307060501050402092209060207080309210f0c07122a 70
    0xc19006051070011405021410701040d0851341705c18510000392414405440034042ca040002485a03490500034108544100e6044081d20800000c03d800e612003100200000070080c1901c151205803110300000f003545100180c040740c0c021696001c4000103400050480f80075074140e07070002c4049070400382400e505440003400350b442000104101d04001c1245144015200c50010300c240f402e450b00f02d1100d20f04078030021540d60000d5800019a0140b15107a0066a410030421000703216101d9800150344c6440d5003401c8000e02400001d0091281c0205c645007443c448061040ba0ba0320300d4040c2d0b680d0003801d4221a0f15040c04004109400e2510a6403501c4034000e00081d03504020003444015001201d902c500d9007030303c139000500442c0d034a000a05000c1c4c85099820713560f2804075101428005400d01446035442c560032002d4001e18603200b614242d22068050f40d9031030b440500303680e2a0060560160900c4102c2248800c20320a001c0c0c0c15401a8000069920340c0f90441882000d111803240 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 295754703 1250 295753453 295753483
    0xa0506070f020d0e0409020319031205131b091a040614011b030c050109030c0506060301050c030a15080f070e0a150e040f020405010b0301080d020a23070b1206040509 73
    0x40003550514800c900713809080c90040c01c00183c0e80440d40110f81840d03001780e00c1041c0c0842d0410100109580032110b841d0b125110f10007084603080000b564100c412180b50013400202d4110514080720054000580c002d00c1419001c024840403580c14030700b08015042998819860310b00c000031005240c140702a0300c403205075102010405401d145480c0071a05074030950400082d8036003000066800d2080c0e40c2c80b5400f035160719030100000d1920078038042e4020b00060103030341000140211580d4505c2504c0d0404a034170380115940c1d42002c0804d498566a900c00c1e403c074450005065822000410340c4000c1d96000d905428455582c1c083d1a0295049000b0703400e24054203e40402c1599100900c09810030311551040058003803507000102039810a802c400c200c408000010058024200b01190034038410b40040c0c102d0040310745030b2681d41c035080c04032010304240e610301c4a00d89174414000440600310000c011070700d504680d80003c0104908540c2540103a1a00d008202800070008120184e0882e031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 295755953 1250 295754703 295754713
    0xb060903060f10030b090c040b0105070209041511030a0218030a12050d06090f0f36021f09030611030108100e07260607050301050a09050702150106020a0506070f02 72
    0x2c40d030100c0016401400e03240046000f80d0040f002440320041c09010704485402099003000d07034402c01044980d50041181404420081c0e64016110720b141d080c0d125412910903045a203121220501034007081c5403014406400204010702481d8580c0070300380c40b0180c8a10240241d10010074144e03a403d403500003070480364200d4002d0038450b01c2500140001001c0020102e2001d58400002040d14042c52009008a0310740030784006488c0c1904c160b00b00f10680300901024045548006000d81042030000c45141e0701c180c81c080b0030340d19941440c00f02c4003d00000001a649017603801000f0000501045400768205034650401072202402d4a0580b0403902c05481d814061210402c01808001c00700252070094140000d000c6003440c0c260790a41c03548240e00301607000300019450400c48010704040c1400802c0c40148495183c4030822010b483c0d040e5000a03040d01d5241069103007040c60741c0c105d84900006800030500c83d50124900005034407a00032076030540c40b11b02d000d40304c0d100e108940760010703440 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 295757203 1250 295755953 295755961
    0x30f0b0301020f070b1f03030c031806050417070308030c030115020718090609051207061104060e0d05010f230a090327050d08090a06090506072003010c020c01030b06090306 76
    0x203032444150801800b0446c4105290174488850594071b59510030b4000c25075050001c42031542010b9140a4a00c0c80301c603c5502c1420300b0000b41450069010798520504001407801c08003004205090155400541650300c03442d25100d41e1a090b4000d0085000040309046400300305800040c945064560103e80d06d074402150070180c0008191303052050303030042d032111400c03004144140040d030182c5d07016000466a41c4401c0c2810016039843c803d4000b90104100010006581d020143d855002421145032040d0036140c20440c1c0501100300039039800514180484072101031031121074101e42c0402100b003042d65a5015404211495888050041111000c01c40b42741440113030202c00183d8900485440642c49901085520701104412030340020000350000540c44c0543c00c26004095614000c1c00150611010880d14000e00700000e00303110040001c15100040040020024400170b0000c102407406e40d00000e603240300b0140c00a0109251008055103424100e0803980a038401400902054803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 295758453 1250 295757203 295757213
    0x90905060a0b0d0b120610050d05060c030711010203150111160312051b070611060123011103120106031104051f050c030a090f0902040602060604110904060303030f0b0301020f07 78
    0xf1100440103071040d0380d0b0801060f42c0d518420f608080e43c000e0401825645801c13040541e034444150805445032054040d0000052000101c49034450381c50220140c90b038440742d41c241d80a031310350414140c0b03070750001c03080002c151007041c00404241c20036a14241c02214140865444500030340c44003407018201313079003440030960290004010f215140340052070461407600c281c0c515101e110004409401c0880100b06c0c0c1503003d140b00c04105075080160001d0f52400140102081001080c50f1403e400c20300362502d03da00072104461115183c0c0300342e035624983d05400502d001424001c810109103446c031010010100e480c1600e007502c2028158100900001c141c102007084004818070400c1003c0003506060030003070010340208559031322610303403081c102020300502d1250b5030402c0c04500e1051204100c032641c001aa66007080b0140c400140003004080c0041491143d403401039041410580004205030b81540024240800e1517401c0050081c40d07030800d400c0c0c1c85004514480881c05000460100d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 295759703 1250 295758453 295758457
    0x1106060d02061324090e0a091b031208010906060512040804030f0506100504020324010c2102190506011a04030b180c0108040c060c0302030c0f0d090905060a0b 70
    0x98002070202e820100c90b0705140002601e603400c07403ca400b0b40f01c00d1141861425418070100a0814203140c224541491150781d0f80c1d90006181141e0182c641344800d05020708801c880a203d5941540b200c5501d48030b082c580645c492140b00340300002e8582c400007c0c2c1c070001740714403000c5c2d560658a1030310b0510085454440c0040150040d10810020080080050340c4156540541441903018001c1450304080b420000030313a9610841c0103a004004106803036a0701428400c01040501c0d0f00300302600c000780101c8001c40134903001007030803821a4501000c080007508518503024540d00321880000c9409183c0340f00301d48800c0c020030641c0074900500070b00071145030f01551803080d160381c24241070350b82d00d0f8040e81003816540000440403140e02d410000f40144640d540d00700007800c001c69681000c1e40d0307442c0d0010052184000304a5a800ea5508040c401d20440b424030b1180800c071800c90f803044036045e071984084000940801e60501001981034541c0c083d05100703680003040b0003202490321000003015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 295760953 1250 295759703 295759729
    0x6150809121603021905010c1b0b0f0c090d0605060a12080a03020f0f0a0302040e060108150f03030f0c07051008010b040e040305071401050106111b130e0a1101020706110606 76
    0x141c045d500015600e5040d0342c208024440c043c90010499080c0c4000c00b50619100003c60340c6d0303c5d8045001c030804100c00e0300c40307181c210030108030011517550346e00e2010115008080e84164840707007000ea04400d1010300e03007125005040c1110b181c40e190303588880f0180300c1200c88200038a000c40900032004040e0082d40548109a075040000e464511204086942e5a0008200c00c2c0404d90204080c03100d00e401a009990000342030800880354101030446c610140e20030400644147c24210042c4d08684051040e41e41c00072040111648410300ba030115500d13440540200c5001c2c0700445081440b06100700c0400d4107c88219030510301d42410300100d0010b142c1d0040080e400d0181c00c02415000a0401003012440c94211000045a5041020050003846a4991100781e60301034240b00d4540b0344040c981c2d440c101000c49041c00018080c43c00c18000e000010031407441030288450301805d1003a00c8600c01c0207101309a00b0f661701c9544411b401d0328600c5800044021030342c0904009a050b0608817688000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 295762203 1250 295760953 295760957
    0x501051c090f120210110f070f021c060e01050c1303120509090c03090f010b030312040c09020a020f0f0d0f0e012c0a0b1905130906150809121603 64
    0xa415800d031180c144400c0f90428103001079001d8003805050200b41d1091464500e10072021600c0c020010354164924040c1101c050501c96100c0320701ca0440d903581080c002d442d02c08503000704801c10710b81031190040080f0042e812155080c2400140541d980400700e807554801041d51082c1c0d103084d03440f00381003400d4000b614000c0c00000c20125405507a500d071a0391013000f00208096491401c040e540c0e041c00e086140d900d500c2c0c1e04200c11080e0310f5a000c416500304e0001c074030f02c1343c4459075281000d03860000ca42d84200c009078030000340200d4580e07000c00da80410b01400800c840c045d0300c0d00007815685a403641c00d59800a0040b04060f91a10b1041102d5114020145001082004054003504010a0180c0040040d050720300307494020f402c000302045d00810344142c1c0c071800c00110302c0c0e000d100402054100c004000e00010449034030070400081101034081440e08010203503e88035003183c88140c0f10000b00204401900282d00b5200009070030905071005140103080040c02c2800c400007919540044003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 295763453 1250 295762203 295762223
    0x9010923090a0f140c0102060c25020d0302010603171c050a0b0a060e0f03060103050607031104031a010603050c031003020111030912070f080d0504120201030f050a0f060501051c09 79
    0x201040400c4410f0641c140102d494501150040044603e0700d05405200e9042d90008410002001010030950b141c1444c52441d000c0c00b0000303102c58104403d40890001d5002c1d2440300070505041d0705500010070340c0c1c82860040e82450400ac000310103400b400c0089880003900c3c2c447d1203105402034202d19044082d100010401e410243c0000d031080b401034003c0030010f005d400030220780c1e05d0302049c6c40c04018030a034003403c4e82d035045031a0750f9150740300104084141512000004554a5008122002107401c400c03100304070340040c0b8040e042e1100038272070100081c0c28000440d440c189402c0890303025150705003040b00078619590040d201400444800c3c01c2902040c04854820b481e0b00f80160042c00100020303000e400e0a080b058003140000e50403a52641e4070092280705400d40020440782602c400f110700e95403040861004034091706039100710100c07007420700042c42007000ba16044900c10201140060025549400044515000b0b580700c0f1581c0e11200e605001da000107d0380501300751405080750034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 295764703 1250 295763453 295763473
    0xc210d0b060d0e01270f0227010b2206120f0204051903170405010c0314190201091203050606040902030a0204080304030525050607030305190e07050901092309 70
    0xa8111509081120f8160751504500d402070311000034051000b200d400441e20010650740c4450399203a490004c024040d4611512691808000101d25000c80104000007940d56071111500c1315550484402c0003003242001c0804000201d64208800c19924140ea0744501c420940614002600e15000c51580103a8208000700385074881d081003541f07809045a4207001e052641c40c1c0300e4003180008803441400c10050005000f103030ba0140240c003145401d0303e400040d905440c0184855880762041c00703d40504110080381886806410010416008160308a14980030139030950a40d001203071380c80c6e4025020001804545001d502440d040300041c0300041c18241c035005094910307401500306980d0780c0d01c405840d41300c00e03410040b1007004010411405151516010104040b8002c1200080506072120000342e22034003180c03d0f41d50107611310201400305440c5407240640320302c298052039000d07610036000462003580c1030181c48542d07055030328a0610080700304030f0140c0d880005400e100b214002c00c032804d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 295765953 1250 295764703 295764727
    0x40603060c020c0901120506010b0304060219030603110a0e0c07140709060f12020603060f03030c01110307200a02011437210506010212030c0c210d0b06 67
    0x110180308494004000648102e030800c1013105050b4808080600750b10389042c00500e000c80c040d41112120460240c0740d8649160000c003030f01508a440c4e07000341031544a41c440e07540c107400a0303003180e0107007841c40000018481030040264146c0520400611034901080c035884480d00100740140c010807440d44d00032020700c1c2007404c01420758445421141c40b64401d00a1403040241080204519000c000840e0030980c0480c2890000030a500d10a554024400c616a1403c0c011500e37030b10300000080004410400034814590010743d4440d0000c0c0107844400c181401920043d44541c4840c2c00810740c11000d603004407003083c4400490f00240e0740900c904c52004100465004850301d40e42c2c0448002e070300094290003003816001d021401c07c02c11000302c84c940146000c12040e00d0b4030790340000c2900d07034035440140e180184814403003c85920010030010100d68410141c034084082c41d05039022119a00c00e1007a49590400d542d401540c010041c90081c104c0b1a0700103101c1070320191078541440300441c4c00c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 295767203 1250 295765953 295765961
    0x601031209050a0e090d050705070608060111030a030903030c030b010801120201090e071d010503060108131e0807060f0b011e09170c0103061e0311040603230c0a0501170604060306 79
    0x901102c250100501c1640c031024802800c90281c6c1d860014146034071503e590740d03203150a204000c203010942020031344903441001d480500202070021a5556602040c009000b084c26002c2940028600000e00140790300c41e00400c004008140e5544070240d007031140b008420f2406100803814000001000035142040948843c4102d040351117044080401180070100b00c0341484025040020400c10086142e80041c181d42e01300c0d240c200202d006c1d8055160101c52202d2050701440e210601c40102410412920010140907204150522482911000b01001d460b10030b4415408202c0c801d549240e540e0042031029600c15051401d010800d80e54416000c4001602e80700945a070482450000d141d40c050040c03800405075090441d2215004480d4408421900e001c020310100c400000d180860b039a41e0130190240d80c2000000944050081e44000c65011080c4048c1d642d0284000c420320791b203400300b5410212541038451015007020316000c0014400d000340950b5200c1d9079500301001041540c42 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 295768453 1250 295767203 295767209
    0x506090610050301290a03081c0e0102071214090901030821090d1409060a03023007030203180706080108101a121509060a0501050103020304050601031209050a 70
    0x20282440342041d50000c48101c0c1c55401043c0680c3c10700c1e28030307042c0c10036540c1a40c2e0000c3d0104405007480c85002c00040500005500181c10804045800101d005007444107042403e0003e81c01c04c400d500010b8240e00380d01442e40098032900070b0200b69441c05001b10b45070035100195080062800d148440002d04d25123081c3c01c10340d80700d0804a010392405038601032038403502510000d0310423503213403c4185540d6070440c3c0305000d041019091b0300c90000b614020130345540c6040203003625141e01e04442c004000390050f02da034111351502c61917003010b450241400009c11100c4515000201e60b42d002080d80690300280c054621064581c145001d035030001d00c140c0f0050511680c690109501d48121540303024035500c01d40b0300183c6484246066840c2c03041c60514150002e842d04801c0751102d03031150741022a42e0200c0b6402d08141001c100c2040d001080e040d100b180410020002070f40ca8100450490000b110010550350040c1c00602c08a04143ca4002e421685d40c0361440304951188003240c3c007030b40c05078 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 295769703 1250 295768453 295768471
    0xc02150a050d0b01020c0904031107170c2404060309112d010f1b03030b090106030b040c1403040605040206091302040302100203090a09050a02090a061101050705090f09060d0506 78
    0x3088800c11034001d0f028524000800340f0003015404011000942c00540240009052010810b045001d108090101000810001003c05900c0c5d540c070b012a619080e20600c2207110314142540094802c400c4003a091528440080a504042c10180d00b03030014600c40c40251030900205866824a6840002500c07214804035410010910042040041540651221810b0007100f000003c5002d07072010041100310200000c95801c4059403d082e4010030960440030f0300503280034004104e00760190818044110251020401641589800c80d01d49920115000b588032003040450049a4290096a00180024180303481c00c0e82540018028400705a040a00550003003000c0041d440d105028401d101e000b40003951501c00540001151448280541502c0740c2e921004621342c095594190f844500c5c010f004020502e0703c90381e001d85414002202144150300306030010b8000e03445001a81c2d5100c04c0501101c4402644104016180d04e00034001c5420442940c0030102095041203400e0040300f501c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 295770953 1250 295769703 295769707
    0x20306030307020405041a0624030c09090106051e03010b07030f1701090b1306060c020904060e0a0804082518180b0907060f17040201020a060905011d01090b0103030c02150a05 77
    0x1441c0c47d070390070302c0007030100c0e02c03d900401142c61800400c079406c000071217400806c113031340799503030f4046607994080c084006800410140000c100c40d90010000c1c04090112000050000c2041b4120701c80c600c0240110502250203000d480006405044142510112400c008541c2c030355071000e400320014240c0c044001c1503201ca4a0712003e00b090000d00500c4440c8110503c0044d04014003d003002824000090107000341c0c4000400740500d030f80c00440c000c2d0494041e50041c140509205107160840d01030210140501641c044010300c000100400b0100d0b007a00c0e0004151800305c10f419054200c81c903071403440c0c1c4ca5203606080a0b0f03040c05101c0006105856041e8282810390246140140c540c0080c0309004d40c880c1410809a0801444990720300015010105c556a6100403403c0440c2508001e02d107a0808008600304801074125003030040c0c203400e00d40000300445070050b01307a071504807020340313001d41080041c00424464000100d4250000c1c0135401c01c18100030b1040c03896842500100b0002c3c2d80 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 295772203 1250 295770953 295770983
    0x200406030e0a020f0904050a0507060e1e010c060c0203090d080d060812041a040503010e01090506060f13020c07150203030405190b31050f0c19060302030603030702040504 75
    0x5205404481010400a007240b4803281e02040880d8004c94200d0b201e0305280002904110003041030461a139800400d49800303a0741c030f12000d4010b05409403090b00c81e514048416071759035020f404503886014142d5441400c100a17858600c02041088500740840c0800c1103c0d120751b031111464591303560307c1412000d0f07903030507241081d1040b1049508500015040102801c40494244003070b40d056074001c0b4000400c0750541540b821451086501c0340d80c165003044855244600190b03c8101854060014bd407600d81e964020003603032640404915501030040c004941d041c01595010300148400c400488609544904510b443c0e144041b1807140142c4c0300000300410840b060082d01805101145a2a40b8143d1555200c105510080c0050040c00c4003002d2070a86d000d6034035a081c0700700202c071403040607840d450600c940c8401408401003038501c02c031444401c2c1402e006801014440350032a911101c1400c000085019602c00b500751541440207129480c0076a649200310743c00366100745900c0b04054a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 295773453 1250 295772203 295772207
    0x310110306180603060403030c030609060603050901110313030309060b0603250c020a090207020406030b0114040b060910080c09030601140907020c06040b07060e160501140c0d1101200406 82
    0x729101e0380c9410120b42030510a4544000402c1500250305080106a003140e8076000c40042c1526401501400d00341a80098616010750103c3e01a2494a000380905032225000000301e03c0301ba2036048111807455485804244030b40d1151407440d1240c50040b9035115490005510340d0001d9407950310031405c44501041c00c22140c00040d00c061010b00f011701c00380c043c980001d05041d0765845070703c0c102a00050b081085540c1d80d44000c0c040c0d60300c0b4a2080d2a5612030008440b0f840a075051980228684031446e9000d00d00a01034420190008200c045c00720b0205100b00c40b03c41011300b1140055a041c0840b15982c1e5003803000c0c40c040e18148030100e000c1c0520800b00002014040c1000003075400c40540014030742c5640c421281512900742c0869507418040c0703416001004401d4520050b40a0b01c0f15050000d110b1010070812200240c1e20403104100110040c40c051180381d2290714160710071805e14004600500c800030300c2101c0c0a00000306440203c903c11000a18100d444840c2540000d041c000ca603 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 295774703 1250 295773453 295773469
    0x20d1103092404030206060904050c040c030204051003050105060711120609030a17060907050a0903050318010f0518100e0301020c010b0a061805190308040e040309050609030a110310110306 83
    0x1107901e04845600f8552006511000301a1040340600e440d10700103000e004080001026060000e8404c000340800400010300940040c0285403040e01c4941e0b40020851003802100e050b11802003825203051002c0d520000100000d6688903003104101d04c07403980c0c0a20074030800744182400005595a00d40321040100b501c400102d2081400c0410814000d0a0b22020b42c129403003200c40c01c00e5681c40150880c280c907118003e030710040a80c80009107942c2c01c0346650f00c01081d07076682030f2508035204200078001e441600840c080190304000c1c200d18039410345050b00143c0511070550911041a07181d0001080c01c5e40d12142c0c1c1c0c40c4251f03460b0001080d40f400c03c00180c80050019107801c600649640388150040d80305440341c24841c803000c49a0603944030703103501240000c5903c450034035540c5907900c4210f055040120350507404079682950000e0581007503012100b0202004024044800c615510b600141c200203600c0c64040c4611120102105000e2180d0403240110307144c41c9480307180100c10440d00d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 295775953 1250 295774703 295774753
    0x9050f100501031a0c270a0303021027080904020d0e01140a0b060a0305060307090c020d0e06160305030709180b040b04060f0302060c01020f0a03051609060203040504020d110309 78
    0x20081003420408089850b1051b1240b000913040341c200411080c214180e0000803030480c040e40031030346900000406400185d84000150311402c20b100445071007600b001c4207854045054080052003001c0c50000c0e030b0403402440e400c94028401801d00010312280c00440b401c031030425005030f40d2081103110303283c102c0402e640d0006401c2014006680702101050300c0c0d01505c290f41c0281511040401c115540500c550000340440b14410440c4070303078020000f55180e011103010000314400901e00d109504241e030480e1032407010040820603190907a0740844040d030006149408100c000b04010550920100906044500400002c50f5440c9882d007000100da030401e001600c9a49090410441e41d603501c07160b90b0403a034048402540b1812142a601e01922400c03200603501d58001800019031342d016441f0b50700070144d0651201501c0f402400655414409015800250740217001c100950b14003038004245060601030082030b00b1780d0348011000b40c0d82065504100c0d41c1c1000c501c5020b40c6104200d10030761 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 295777203 1250 295775953 295775993
    0x1030f03020c0306061e04140f01030308010e0105010804080a02101104060201110702090a052206150b070b0f09070806040f1703102c10030b010915050409050f10050103 74
    0x24140000043c2c0e004010a082101541c01d04001c6e0f429a80c0fa54031170803400004209541842c0303070440043c940c1c0300c4240030407008502000700114284583e400c0c1c4c40d041c2e40c0e041e195540b0076103e64a42e16413681241031418210312030000101c0a96410f400307041d1050340e00c41000d6490360b0a01c0c0d0081d003520b1002000c88041c0005003c0480969155525690000003802c000101a160342c000d440124004e20b0300c003580c100c07020a10208000042c0e00030700d1070040004942c9010ba0b1559220381181c4940390024001e2031148010510b1542c0503071007942c01c0b01c6143300311159240d03039404190800104407002c2c2c405004221400c020700110104400940b040d51111919518001c06807a46040903400344042d0320550701184d101d5403052801424881d66503011000d840c0c9045040b000c603140060004036000f80201000180000071f9010b41d013040703024014209001800c00c0d081c48001c00300074409070b44d00d10410348030305203d8406102c00e14184181e0b810114982d070460400c0401c800f030000c02000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 295778453 1250 295777203 295777213
    0x180d080a08070f18051c0b13032318030304150216090605010206010b03040c050a080607030e0105011a030901060b0406050c0f06010f090b0a0906060e040f0b0108010b0a020102040e01030f03020c03 86
    0x4c04540000c2d000c2a00c40403a5450400300354a10004000c4041800044c4511610001d11481c0c8110342d09207560b00b03106e992400003604030035110782040794000d2009110420144410303500307510254082e04c003050018080368242580c609003410a0880c400309070700560481202164100c0884076400701a00101c4028003610b0715010000f91b507010144510646680e0200c007203400c121708003050100804c4001e007840c102c1502c030840c1584a5800340c0d52000444d160500000003240103000340c40c1250b0005a0516080c0526501040039038001491000a556900b50100c0d43c15240000303480070707216030740e942e6450f010160030607449c04c204a02a000b00d51300c8040100180b1626031036807001c1e01e441250101b8101d018801191000c461500200600d034100f88010030900d80c8850600c5058104070b50a00c0301c601c540800e038045030043c442c03150009040000502021420b0401851449080d10005190a90b45c9192013a182d9003a00110781d0203000c07030a44028554104080e0303000703d03002c8004e04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 295779703 1250 295778453 295778477
    0x60a1107080321090a02130c0f08090d030e19050d020f0a0b07050f07050a050610090605060a030b0102240103060509030a020c0103180b0f010305061308180d080a08070f 74
    0x1c41c20701181e000f1407200c001100001e034a0303010501081d01d6166015150f00b81e0030300c42c1195640a00555005000040d0280c000c1c08421407180c0342041c0100b680d400500b241a207030100880160010f4801c00700e051140303a94500075000603006000741c05004d030018140f2180804402800c0040f0640240401c0e4401c0d00d690020440c6c0c0309100c0e800003210700340030340e0b030f049480091940c43c01034070340190481c00f40d82000018004003041141c0b040c0d051207070090403541c40e40c84510031107106c0e002d281e800240901034500100d001e81d1080b01c5144c014011039115003c110b07a00012a58980003080300c4101c4a80100b0422646010301500b158449002d90304041000c20020f41c2c130640032118604149d12148100c1308210b4002031441c080f42c02800d00c20030b61801c40c00c090b500034404c0c031040792281b2601c400245d02110114134540e507150300044261800d4068100c540b06640e900e11301a80c4011181003080c005031082c0000c02520b640b584540080c0d2410140240a84144000070b00a209400e4890 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 295780953 1250 295779703 295779727
    0x130608010e0604050d0c030e040e070e10180209012a17091c060e1207110303030f040f02040f02071104060e060d060525090311040c0909021602060a11070803 69
    0x21700544800341c0f40007000b100300e0b03090456201c18140312103600b00b483d200761400e81020120303942041c3c03080c501c1781c1041900c484c052030300c20700203610402204513022200e820840c403031600140003e810500d08180b03005a451001d11005030304900801d40000c20202d8081040f145e01c502c2031600c220900000d041c444668086140b5030f0300000003007112404150301ea810030070350b90700c4202c031350090404480c040c455103d08000243e000c000c0545000080d1005480c1d18030700041200d01c1454000900c0c101a106c503501c1c61034070142940c1c101d90080e100c030215044117544d07201801002d800347e02a441000445018442103a2140e000350a036401448108041500c42c0700710361090f81d9100100042d00c1d5603103142c01507002031043c41e16141e010304611b60b4851541c080c01c1ca0040c0c90003030162402c404848010030048518030480c1c500400d0840d40304000a0040d580903100485100c2d00c107140d0a04540d000900315404bc0c4c80f8800070504680604c2c0140d84100500c0e005030406000440c0381581c4039110b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 295782203 1250 295780953 295780963
    0x2c1506061201050d0221280c2702070317060d0507060f0c0515060901060f0801060c1b0b041703030108030906130e010e1803070f0204110405130608010e060405 70
    0x41e0f113001d00c100140b80b8085407901c0780003100d000b0242c01e000160683d0140520b445900030900c0d00c0500f48010701c081012403900759807603802035101c0745040d802442c1070401e4482490480c0038010342c0c006412100c003024110300040510320b1003075550090415500c0c03544a02c613840034081c01d0041c0700055280000400018100c030a587c03031818803400341110079100300ca154141000043ca02d01605400c41040101e0040346405000200e49100d0300daa2500c004070b802c0c06e094500d6400040b52000100138140c01260600180c5015005201c00d108206292403142d81c0140d0020030745501c0003404211941415107070421003411040510325551410580c99034901030515654404caa001559811244006400400820000c80111040e40e0350300b030300300200c081c04c0340c010411400200503050b20b08804000c4400056101c484501d005c14240c0078031004000300704608000200412010400ba6283e040c170780021000c240011038400d00300480b02d403c1d140072520703040c86980036400f400002100450 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 295783453 1250 295782203 295782209
    0xe01170c1c290409020a0e07020c030312010b0d0906051f0605070309171603050d020105060109180e0c06070c031a0c07080307051b1608060106050703032c1506061201 73
    0x1403200c2e0481500240080c810030100a5101101c00c0002900c41c5007018a00e200b0700064007662500c80c4010145916445202203600c0902c01800c014020041180702030a9032200c12040061300c45078560b40d00003141ca0980304110140c008400d00594800f1440104d001340140e07150140c10b00c0101d95000e03000c503980740208081d04000401080b04801c1c20480c100048101c0003104828a50300d0410b030303440e500300300d407680015402d01d000950305500031000740e811208440c6401c28004880b4500d100200795a42800810b8010000e4a0700e590b55100b02500e8120300491aa00542c1d1861a0503103140c0c6580f0605003250390900c08200440700204295000720b604211020307900da0320390b030007103500f40f10b02d98007010f407011103114000300d0201c00220420007000d182c0c14083c201d91280800340d40d40c2400d200b1200000c2080101d04006440b9403c1101a4020241009107500b081321a043c0384500c10404007074580d0010b082c40040089400340980c21107001d4461502d4890310048542641c14140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 295784703 1250 295783453 295783511
    0x70501140409020d20071502030f0c07050c0301060f0806090105091e0a1b0306051014040e0a051002070c090605030312091f020405030c03060c09010e01170c1c 70
    0x8142c04c040f030030990300814040e1101d12003080c1110404a100c030388613000702070141e5000c1301c018455a4401d03ca842100d004144549449005981c0d6018060310381e4003410040320740e402003445914a07520309024450180c9208030540b00c1d01802d03c403000d131500700000e18041c40c50b810b100070700138020004100350b5009541080400e16540050195610786800190001d10480d0803200044201883e0606078055911600040c80691142e0030068080c0380f160041c8242c0c401010b0540c0c20341d14156000b03c51080c01082540c0e070182094403050704204240070311401c80c82d00001d0440c02c002d55242c0c01c0c4080c21640404008490408010a50340d01901000004c995040c0c40403a0f0500720070401e503062406d40d50100944850a001d03141c019401c80d1141d50702034441c03800705806500d00450250300c644202c0b800581800117210045903000c0d01d60444505100c4c106070504030607400403c00768812002c03010056511118440810203a110525000c0880c40c64050921400046200090180c21101d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 295785953 1250 295784703 295784707
    0x105060703020f0d08010501030b01020a03021f060302061602040506030a0803270a050129060f09040608060405011a0f030a0b15270708130f1104061707050114040902 73
    0x10300d07090345421214404010341d8810016101805035100c172180b41660421303a02401551021801aa17030f5800f007010007009a0000440850301196091501008030501c2c24007161965a9401140460303120450358007485c00c075468248150300f00350007403d40052090303004002a03205038903640e1090001911141100324545244528280103100c0740807544601c1c3c0685000c08900d140490003010b013110100400202ca501c0e0704001100052407015038030018107202d01c0c00d000440c00c105140d0000c88119481545e9240c042034401c41044107610583c4910000200401441d00764180415914041f510400c010204159036403008200a03450960000c43c2c0c0c1e819840e1800044051603019804580040090783d100c1078240703510381a13403d040c2d2000d1440c095525603000807a2440300c00c503011a60a8040c0a074080040c440c1c41c81184818007942620b040c84400000003410350f071869200c3d5800d100c0311401c1226402042c0200e400a02007401c02c202c2c40c010340c5002200500552040e54030560340 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 295787203 1250 295785953 295785967
    0x311151b03090406060513080102031029040f0e09010b01050a0c03110d12060803040305070302090a0f09060b012d030c1101050915220209180f0c0102010f14010506 72
    0x100107650341c0d00d0000340107001a9445178401441074101007001560007041200c00141c80c40e040c07007128040c8000c1c00d51850303101d003800d6040341c0002ca0b0259106d503144800d2502e0292040b010041d001500048103880c200c07500c0e0003500141c881010303000c510317164580300360141c2e1a0b070000200d8001000c0b908101c0820015420141e0700d10a03071440c401700d1400b4101034481110340c0191801100300c1030301020400d10f5111200301c0d03628092030000422562004000f031001d03142c10b01c00d83c1c3d840000502c010505c4181c04004138143d803040d210441e8560307202d050303c104540c1c01c50f518400c3c0c5101c501c842c400c0564080d282604541408110030103143d9210940c8902620404041c2c0c92141800001d11075805d1120815580d00c0500300301d403103680c1d02d2030007081004400110300c800c220071185496100c41019000c228003294003510254500a9045110a282200780019000148040054920110031400180c20344190b003035071801c01c0d03140840c200450442e08038203e06549059505036102c0b15 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 295788453 1250 295787203 295787257
    0x706050412030e03100c210515041e0e0a06060605030f160311120a05090a080a03020a0306030203150105100c0203060412140310030507060f052b02070c031115 70
    0x2e82114886080c2803103608081c035504112461110141c9181c7c01c0341659890064104444c001d64070a21000042402640c183c986074200c031694011002c0801c0714074501c01a10380031955003074500c901c1508001c00e04c0061010500c6a01e00906040c103104d455841c3c03400c6e50340c8500398010b01d5040a20035101d100303211680310b070b400144049403201906640d94402d0340c02100d081802c580b110610790921000940010300401c41f008181d51180105081c030307040364000d40294000c20f100c58100769443c40d000001d66010001d40041994014240803654105821700c1058140171001c9400d000300704e0004001030b00c0000341e040e400b60300500c000a00740c44960703046412481c00d841d0050041d00c00706c11700104000100103001164890421107603c5640d40c8025102c2060050312100426030901c06589019554420840c1040c00460009646c00f091701c8000100c0c0c009030b60031f480340407898000340f040000314500c3d21a01c20702207514010345240e0031044402c501c02d214203a01c1c403010100c0d8040c6580 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 295789703 1250 295788453 295788463
    0x30114120106051e030c010f050a03020a020a020d1a0a0507120b06040905041b1203081f1701020c060901090506041506030602070b0a180209060d050708060114030706050412030e03 79
    0xa0042200e490040c0c007420420f41e406280312005d11901450703000360219802901134240f809000d4846a040122008003035000f5048210902c0c194010108814016a04c11031403a1031903105801001d1080703626286034003002c2000308480c207207500c0c100900003555003100200f020058146004103603107443c0c00210f14240620b5000f800c6c0f00303041006001c100010008804090300c0c070b40c1034160000f036942841c5825182c20850103401f20344a00080b64240b815420009405a9604428040355071f607806400b98500c00d040e480205c2e6503001c6807c040c040814446250044000b80c000e00140215895181c0ca0340c030b0182009060700310720b0b07240a0b07003641c00f500000c0c01127800010454540c0490b0a005001090884020351007a1416580780e00c3c170303c1444200540c103500a0414207542ea60390081c80f1030000c0c241310036201813245000000e03442c5820020303540a000c0a0121500343c5807004140f6103080c08036000b14040c00740500090102d031010403011016960945008040507400d640800d00f41 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 295790953 1250 295789703 295789709
    0x2030304051e03100606021002070c09090204090f061d0601180b0307120609032c01080a0902030604060608150115050f1b0d090803090108190209210111030114120106 73
    0x1401400441410f074081940405d0468403541c01b919501d24510f20034804138801e02200070803400c80c028040c4a030311050780c03108046510240000034003004507105e4000d000400281101d146464605107040070008105294801420200902c51135043c00c83c400c010760b4000156000455544050b00c20b1a03804120000c0182102401650303040400d04141c0d000d41540740056000c22400345180c80e0100101108010514820041042c4644202c1c011100c4580c00740140c4429901c6036601400340c3d038180002e42c01140324020004445180020003400c080c800c050178031041d10000e00402046101c40c0400811230028a0083d90303e08000c08016558001c03901d961540006c2501c88480381d920024003103000303808549910300e005a54080281e0703079220715194140010040c0c030104140310303100304a03811141c480381405400c0ca81040e0100c1c91801940c0e8450300800102003410088490a00c02d09a16070000200300f465581040c51009015018841940c040c0130754082d06004a84294407010203 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 295792203 1250 295790953 295790959
    0x170406060302120d18080d0c2301090605060301020306061204080708041710020c0c27190507090515090a0e0a0f060b04080618010b04020f0d0b0102070302030304051e 73
    0x3030001e440c0070681c0c4c410a4214200204000c440e0510301c440808080c00700704c500007401025841443c1038215a8503103400d0044403806100d0308641e44490700d0111920102c06071f07000014040040d4113100060b0340000c3c000a004e43d20400a20a140e201d003811202c2c50401240c04054030380340c1d0b02c0d0040e405c6c03052000140c401c51005c203002c6401c0f84c100c0d40c1c089212002404448200c3c0390609020300b01d1044480b000703456440307090b1032005420130340c3e025400b580001116000459030402c107032a854070200c803096041241d90140282043d8548600e070f8212201c0e2505a001c642080c003c00ea00d1040481100320052020456810a641c1c800e9007c0107800d43c02c0401d0030743e04000074414050408030000c80302c0c85080c10b602083d51903c0c03005030b4044842180082085484214544a540f00c0108450096540718420090b071034546000404414010088150f5504201e051078012904821202411034005501c1000582e40001c1a02e0680c0c00880d0301c040303d00c0b409060282d13900c40304074a40e60 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 295793453 1250 295792203 295792219
    0x102030c07060b100801170c0303040807030c060512040611070c06020715110309010c0c0e0c04090501050301021206041508150f0916060c030504031a15040c170406060302 75
    0x400426100c0140010768442d20050091840100411040c0d40748480d810740042e1140004004a8103100f40f8810f00c148400103403001d4440c0d01c40801d00716401600324203038a0f803120b1410000c0110621840b4010806132526074107181100c007908a100402030405444c2d41d80307411031343c100d49440382d04440c05640d00c0150200030316030750741029465030b2a03445081d000d484d411002c480260b02401d00200030020480181d490281080c00540300800c0702d200a455810f1980d9010a06018000c86640560b100381401526546482e040005480c0140c0115000703900504c0381850304040c3e401c4507034100800711408200329000d511408544a1031380e01c085860b00ca20034442401d000c40c41d043c280180c910b441e0491080d51520342c80c995808158000c010205c0d90142e04110b0980b040d40c1510500e4446e00d4038528103a40ea8480c2e4501c03c400064040d50000c490080c09541d1510a404407002c22095805000c0c0003407104002d4542c01e101500c1540c04141c034000203040001079400310000c2c0d680104180 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 295794703 1250 295793453 295793461
    0x203070201031a181005010509010905041d030a020c2b0b061201181b150804022e020c01021218040b041d01050a0504020a031410050114090c120c0a11010203 69
    0x13000d031102a00c121900240811001c1515482502160385501041e11114500c501d050140402003c1040701110040e804500d280001e017400d1004181071451540101807507a880400c219540303079013490b14812145007004010b0403000c1c0001c281444c6170000e2610240d5550380021074400c0c4515052541107520300042301e42240d09000c11880250700030b200340341d2140407401031881440b5490007510b0143c8601910030078114898009194081c1c8081c007070503c8011500051100300ca01f400340c01e202d010603000c10910a642c100a0b0802c0344200f44000c141140c0800d11000703031071045011704000740030522607102440c1c4a0ba000703080904d1024208000d003030b041250402099414204504541d42000041006039030175000703c034080c0b41c00a10003007400340f0319034070ba81c0e0342c80514000300f505d4010f55070007160000321480743c58024004000c0b00c4040007201d80400c034549030700501051074403c040c0000761418550b415601e6012001040c000c1d50f541045800303440141e00200600307010340c0000100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 295795953 1250 295794703 295794739
    0x503061006111c0c0614040c0510020a05100605090f04120c170a03150e010303080c0304020f0907080709060302130b0c03070803010f0f0909030f050a0c05030408010c0e030604030203070201031a 85
    0x1484c04e07140a04c0c420000b00101c8414146181400e4402510001c848001402189084061269040c00d2401126413050651740c600c0d0404c0c0fa2140740d11801556a1810001d90918100d0198005040401c10b02c40d441c00707603030f010084140c0351180e00800c00c10b100b01504000540c007180c1582c191000300b032a00c8e01c1c0744900040280c41d40041c66010a0941b031700000d51038281c106c8940c16250b058880003c81d0750352154120903604001c00983c2d1040102d02d8203019612030300c50701c9004269613500d482d018500f07050081d040c02160b500040c20035104100c030780d407241d03d88180002a100ca2021281d95403074005501483e5001710007000c2c2c501c1c18000000101c4105015042040f0f035045004035161560390b04000b03003140c1e100080039012a003100406110b00e8425030080418241500341a519000180c94182c517541242e044103125070340d1040c0022009400c1740c0704440c10381d8110002e207401e04c1c007517070002c0d02c9009005000f03040c140c80701e40e610b01c1c40c811400e0f50444a000a01031402510144010f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 295797203 1250 295795953 295795967
    0xf010203090c0102160504050c0d020711270f070302040b0f030405100c05090f0a080714040f060b04230d1a060f0a0e0a090803100f0503061006111c 65
    0x80110798490500340c0840c81d40082140003d007050200e131705100c0f61902040c0400390000801a60651404002180d900030300c510241021600905044090300807000900c011103000c61656009010042da5008051100890540d4040300000313400e025500d441c44281c0280c025501302c0c02001c4400301e0300d2190030502e0700c09035200f07a01440403036100d24494442403044580c0c0092150004074104121000c60801d0594006410ba003d0140140c445d82c800082d8104ae089410921220482105840341c030710301401448440004408100001d07864640c5085141c440c41c4100034407503103e250350b209102c0300341019845140c4003600040c0004400c0ca09403503c0400100300301c00350b1280e44007040403424001002d010030700001c0c107075105c01800d101841031034040081075500601c2c1c0700d0369100c000840380f0b4080d41c010780410b0217401d592428a91881c80d018032941155010758000c05c200500580340c40640c00c201c42c0c00e81800e042c40301d07040580b40e0801d030764000148804004111540c94036540140c0b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 295798453 1250 295797203 295797211
    0x8031e07140d090e15040c091e0914060904020d1e110301050f06090612030d09060204050901170d0c14060412020f0f0709020f130b07030806040903020a03030e0f0f010203 75
    0x3903440c8000303848001e00d1007100b10648510032030741d44d82c2100417403506243d440701245900c24240104e010b5912100f04546003000c1031090403800c00b040341040200440d01810601c0030058240216925001c40454540100140040e02c09c90041c078400d010710800c08401d100100c52400c001021011030704043c44810740c0000c645000b5032070701002901c60b4409118150050000515040c0c40d0785528041007200341e03800c000c008542c00704200300c011001491159214451042c080036032200d1405c803c021020005a00c11110204000700002c2d01d9840842c40c80f00c00512820071800c11b05040c1404102d02c25240e01c1a0b106100b41018001804056080740349440c80a6003120400580080d04035101c1803003944c8a8210360000b41c003480744204640103480d205820102e95030620080900c8000e40403010f0703208412400d80090040300703240c0c1c0824031550212064800380809103807603500a55504034104081e0070036a981ca20010202e42c01d01162a000f1600c004445201c0c54101c0d400303000354020313170f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 295799703 1250 295798453 295798457
    0x1060e060108060a0b030702010e0f010509010b010c080d090c030204021206090a14060d03020c0603042603070e13182307060f03050a02040909050607081008031e07140d 74
    0x29403a5840341148900c00c00024110095032481c180103404250400307041e1400f95502e5030643d4a08103010400d440d000903050f400072516082c07039800c1301d085507906511941000740e08407510010500c1102165111642d2050010740064141803a40f4403003100e17000254407500000e04590042e60b1040d486000b0401213071a0b58494882c4402e8200300d81c0300001e8030035071301a40c40c009000b0b494907520740043c0a000340191400c0c40e103c0c00000d00c180d841110200d500c02100388082d41c940b2502200c0090145278030780c03114a58104100058503881c4844440e91041e031074108401104a01500955030700c00b0300040303141c801035907450511210700683c1004548017000b141c61960110340001c0041c00c5910903100c4024030a04020221301500004040d08800340c0c00300400520188540300302c1d14818000c0000c0c2ca0503080c042c90017041c4910181146007a004089028001d0034400306c01c40c1c0c0d803010809c408464040403085484a280110703a4050581c2208030026011000041240c001ea12616 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 295800953 1250 295799703 295799729
    0x1a0a060b030a05100807060c06020d0e0f0d030c020d0e0f040e1b09090106030218070e0a030b01030b0f09030d0b18010b0703080a02070305180d0f030e0f0303070809040518030403050106 81
    0x104034051b0754030014450320700024558194940440c010b0390040c1801080084045501488503004524081c0303602e551a046034480d40c0108021607061213164032121091001e1f024400505000601c080c1c91004400d01c20405008059800d560b02e60100d81000028420303240207041c0041d403015045003109500b070060719402c000808011043c4694400e403130340188403003c8802d20080c0350044501c01020300b4280807894030000310076070360101e555000714410031a076030303296055140c440e0f00311001a1000c01d0002a007414041c0f00040401950400c00391200d000030180d1040000074442d590310220310200003082d000101d18104101c008101c01402502d030f07000103440312580d40d4102c2c898100060005003040c080140c210361000c650302d15002c00206144400310107a12002c051000d1010110041827a8120550700c1d03043c01601183c00c058103c0c00f40d4103014894845064911980e000b551007580d80c0c2e800107541d4500c48012004080d080c50171642c4581c1c0300d02e0181c2c02000540620b1380c0d0740d012 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 295802203 1250 295800953 295800959
    0x406050109030f14030c0102040806071e0207090f020f0d06091103040f020d02120d09050f0102030c06010b0901090f030510050606030603210f070f0c090203041a0a060b030a0510 78
    0x9000c2078048a600062282c500c0002e5203c094007254820100201400200500300c0c004000f40060800303000254040c00072420100c50181401041000604204010080c0075440365008103914007110300661002c10240019032440009214140281d40c4080e804614403203c08003951002059961078403041080d000105800702c0030f40004c075402402c3caa840c50701400141030a10101e05046d1000e80010000d01e030381200d4905011a00140d800010100e400c00c2010b89040484250b07031000c00e0026610341076845841948541050041c00c41004000481180d9644038140302c4001741403003000b540c107098892503c261120031810400984509220100340745260040440340200c40080c0280000f4410711001c0c40c1c420702c01d0034804003044080c00740507403603c8140020501648988000b080c5641c203840c140354980c10301d800001d0745600c1030081000181c2c000000781c846a00300f00da07612855580460820103032603140c104548290003c424805481c81035007029028111440040b004130391 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 295803453 1250 295802203 295802207
    0x40b090c1206040212120d0b06160303051006080903120402030a0506040f150510030209060d1b0509090d0e0121020706050f06100e04021605010501060e2701180e0607080604060501 79
    0x80481b20380350440810080d0202c800d09550107080c03403220240c100c030305100704072811440b8140c07600c0055002c40e4232101009450b020040c07940c80602806c1c2000f10140c1005454151340780904400352071001483e201080541d942004207203015039101d01216028941b0b89003090003204288802c940c2c1021002c6d9040240c03000d4014948031314074000080c51000d2a40c0c003041319062015208507086903d20242d80c010aa03442c211521680c28040f0901c5410f00c0e010600c03998440080907401c1c96005061068609944008807035540700d403d103480070552103c00c2e044d0030b603000107252501c2e0542c40000c03030b24100304441c2c00031440b600652a1007404c4ea0341e0700d42885801c0381130283c10400150380c0c401c10a014642507002d032980f168815030030071100620b540c3e21402c545082e01f0510200b45841910034107450074121503903490f4014090150240c0700300e0100c01c0301c40e03018005c580400b0a802500385c61442d8503400644841c0e5070a00b1641c2d81e0500c0d1502501c0507106445080c0528103041003c01c20794 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 295804703 1250 295803453 295803463
    0x20f010e12030403210b1c0809090709080d0f140c070902030916090906151202100c1a01050a09151502071d0105090f0c03040b090c1206040212 63
    0x14082402034100741845200300d10941d80010b0084041c005500f984d0111030072160414000c4160f04400022080007140070030800552404d402c100502142e4903120014407294241d55003204284d5440845480c0c1d0342003035a0034802d0380c005130030500c50813109104103548088041c40750f100715210000c05404c44002c24186100320011201c007070388884801c01c44c050311075008541c001212400e42e0740c5900030107042800d000a541c841100e458841c050081400064858a21a50410100700345c0603440c002e01580e0000090101070300c1900390340760920754070340500b075980e448070f42c003400540d10350801d80341410003c0c03070a005880c05004540004545488503126045a41c18140244d070801460403d00180140800c15110114000c1e2040012038040060f0080445000311408049a6041409001e61240000c010a9001c0000f0062150a0b208081201d4002d038002080c00129071302c800b5407078540100000f42c40d802200c502920840b19201144040c0034601c04c84a03072a00010070942c0b00e07030794 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 295805953 1250 295804703 295804721
    0x170f0a0801090f020a0e12190b0a0605010f0c08030a0b06071506061128080408030307030506040204060f231603112e090b0109020901120608060c07020a0803030a0c020f01 75
    0xc06c0780b030008130085180442d0b450500b00d641302e0440c0d0350916450003002d10700e412158202c40229860f414051070210364040c04000d49420302e0040d80d54401d8100041001c0003c89002c2c20003c00000441c100c4046608960301141000e4009681c40c132203403400d8400d1803043c424a0b9505841c109020920900c6428a52559144003000300200d20800d034800d50080c54500d6010501c0481d01d072441c00090401c00904001c01e4018091a00c07450040340140640b08000e028521480c410041400710340c1d00401d548850000620740041c2c81c00084c0d200e500c0b01400c070400342c1c5084030b020502c4503203112071900b81d85000c6d100381e0310003849a102c2c000d03280e55030f03010002e40210f1110307021826045140045540345010f028400c08a003e0740162900c05504a013a08031121403900010742603d1543c008281802130030912804000403483c1c1034100d0f1311040e01030106140d60400003668810345d40c503034080341c016100d813509aa650f420880c0c0390000415201d4190b4025004a80715550100010320900d009 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 295807203 1250 295805953 295805957
    0x14010f0c0e0f0d15060305060c0702150901030e0106030b060f04050603030403020f010c0b011d130c0512010605030102030f010611070f14040e011b0206010b040501020703170f0a0801090f020a 84
    0x2411401c002c000b0404040707180341e0b41225540c0a10030114604c0e103810700600a68400c0003031010f00710b042c1103090980052502c804000100f082c02c0040e184c0d03403134000540360300c0c8403d00d4803601c580380120b000d0140507403124055820810044103000440041c1409a0022500d01011000f0007003480b00b50b0f00203c07a055496042072004001509082d0240031641c48149410180c140e004d5540c103c241c0000e80045217001c8030005c5501801d40380000140d04080020150004c100c0c450781c403112004130350b0184901403c541d0341181100d0009401000103400c0041c000d6451f0328002c1c140b20b04c02a000d10951000401c00d1010248000010420505460001c41003d4a01d81011540e140b000c0f081d42e1001e401940c0c41110f00c2102e80b0071301c9084480200745121100074001c03550000e141050607000362003161402c02c0100416a00083c0100c00c4940c84842c1d2801c103200b02443c4501e40c001c8600b0000034550015040c5029541706410a050310440e150800500080ca40e80d04224002c0c2c90507a00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 295808453 1250 295807203 295807217
    0xe010612060e031213022407030c050304090c110613020102030d0c05120c0702040c051317031308030406030e0a020a120501090501060b280e060a05130314010f0c 71
    0x101191107600042d60007201c202c112850000745041c2503241040c22a22a09000c450075003141c01c42c680300007039414081d55901c010040c4a50a005025513115818004040c03000c0d903103030701c0104001070050718010441d800c2e0400c8002e81148bc0a05034260500048002d8020301c40010356004459034101112034040e8003c42c140444040821300030141180b660051003c180100103050040d1400144180098001191110f0141c410300003514145441d0409101091000300c42d4502176042d51030403982c2d4a400e4224840c0240842411031081821541410840100c08144e00200200070012911507a80030840b0140042e07907c1d0301c40300c000b18000d52054030448c2c01c0003080c0303452001c0d0a05a006030000100a415552210708540383c3d64070001e0706110100d042c00707010301c9068004030503a080c0361900c0d46c1d010704c0341d20003810189440c0000b4404c26001c41e4240d02e1f50305c11020780e83c091000e400c551102503124148051850785449900e22158200780c11900607030080c1c0210344c5035000c951036480c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 295809703 1250 295808453 295808489
    0xc03100b041b0824040c030227060d09080702040606110f060106050a0f05090a032006070c120c080105090a0611090a05040c0c081303120c050c0904141e010e0106 71
    0x30600c22034a04c2ca0111001102404600a03035841c4103140002c04580c40044c3d0340d526000d98001480111058261034044840000c2c0d1680c84100c200d51710940d500b00c000540000324609541c0d28021040c010b07401c1894110042001c54000c801144041c200c3c02c1140c01072003000031459580c4000b400f030ba030000340702407010074610350254910240b511200c0c1011402c0440c0440440ca008280703a005448010040e64a03450b250340440b502c2010744400e54116180105a840341c8010801c42c0c4241c110b8000044000030503c000c0d44181c0e03000e490981c1c020701c001c2c105080000c1ea5807400305070640d14103140525401c0605411421035003403100103400d5102c002d2404040000414031010380c03000340054041c0a40000d10b45038010700c0414a5625800c0265055042c4620341329800741031241808120b205143c080340000581420307940c130884421015503100d00d04408420b40342000c4899a04c196132899442840400103541d4900d01400200540040004038909170b500520400313010a241010030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 295810953 1250 295809703 295809721
    0x180609140903120601090905070210150501020a0b060a05061b19111203041a041404060806011202031002070501051509100608040819020d02060f01050f09090c03100b041b08 76
    0x103503101c241410030356101641d45c47d6040c145d9804403101c000603080000d564411032541e22803400c0b813441c201055491181400700113941e90582c18005048030342c0c40c400240c0c2ca07607510a0050040e06015000507202c08041c0340b40c400a1130450302400702c030f0080103043d20080c1e80c0008401c00d4503401254a54003156100c0a10428030b0510100580700d00040001203404100001c205d82c080c0d224520696a561910400c000c1084000d01c0c001d1155040010400102c0000104c5605444030b081c132006100400e407002916281d4901007020902e400440c82800f882419408139101d280a520541d410000e88000c000c00a90308540001d1036106400c0c0174803203244a4900305a20074031882c0b0052826401080131504240c0560300c1c0c100690000780560030a1764148031081e003042c540291035400754103003000200b0080030001240e0007907080c0c0000079000c42003000042020440502a00e484c1488004000081e00c50202d80500440c2000c0c040d40450540001c001840c0e4426500c0d88010784451442d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 295812203 1250 295810953 295810987
    0xf0a1b03180501062705091513020907200f10020d0e0a26040812180405150307060903050c0907140d150b070f110406180609140903 58
    0x294484181081d061000500e0901c1054080d00c2c42803c8241041300142e40100350841c48100c00860908040c240b04804c000002c011804040c208100c144943d41c00c0307151207550841d020f020354002e410000b440340640d0004560004060b280410070590282801d07007694070f4590f00c118007496071101209803440300a55018164104c4562030100341340b45400181131400180030416038903062010442038200c007035041084038041c1d403045541c0c2010b16018810340c0741e0442e00c0e082180c031000022a041e0482000302d1000d06071000600800c0241842504070711f4641d24000c0c007074000e11448a0201d10b0342d00512420040700c0e807040007004030740000c6003030244e82035024040c441030001d04030801c0c491600140143c81c2003e480d82c40020501d03485001250004074540c02000f000108001c139a01180d2694400084a0707080303802c604d4020070240114008054543c41010909000e68050040d032019400043c00c840841e48188803200b82c1000b0445c107100140c0b1042c035140c0c0100b01d19000c001030420 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 295813453 1250 295812203 295812221
    0x60c091e0a0e1504020c030c1c020a1b08060906010602010e01020711060f040b07082a190c0f030515010605090901090902010e15120702060c070605060f06120f0a1b03 73
    0x14180c100c0308041020401781d800042c4404e10703940000c82e0607440a0b03010030503d0302020080c00459000001c40d10007940742d1203442006049400e64190222903a191500d00e080104400000c0742e21b1407503d4250070351208820f003d80d000550801941007456907050080d58000c54104142c000881c000e00100701e00d42d80b00010b0803902c20780c240310010b480034a00002e8442c1d240540840f955659603107a01d184040414028001084940f82003a00d07603120001d0b20588214000d1560b08034004c803030401d8101c4000d41ea200100750704003a000802040400704113001580440c400d07001c450390b2500030a45d441e005001c01e0382d801a09040040010190a0300003050b100e006040c6600c1c2000c0c280c010904181441426020700e0500040000740c0c0043c0b16100c550010030f034070140140c1e00341007034000350920605601a10040d100d0303021844541d02e803040303601c03051002441e580d0f60f9607a80c00e151410010031038070394180001c448002110440140101e00c1440030500b450600c01140d030b1426001814102 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 295814703 1250 295813453 295813471
    0x60b0108060405160c230601090b1c0201030203060a030209011203030e12030c0d1e0b130e120a02010e0312010e07020d0c1203200301080706031803030c020f060c091e0a0e 75
    0x918a0009000d06c2210911105082e0014109960400705408143c440c0b503440725000380c1040303403030314081071803d00e19076805542413801580d2512810000780e484501a003000c0c0d842040c02000144104012200e0542144a520140200e0300a81080307a120121001031a040e42c0082000428101d030341001003032a1200048002001c41480042820b00000301000002e25683c5402c0c0201c070386001c20710001907a0030071606000d0301130041e000703d4403101104030341d010b00714010039400f18181c000e410040030940344a003283c1e02c3e16020011001100c2d001e10030051000d13444400b20b00c0992011540b030444c040700e91114030402103d0342e604823142000000d94020155208e00348584240080c40710790554699240598403541001540c5013400342641c000c000341450f0241030700103402d003801c1a48201d50503040004146450040590502d10680d03c450110300850041104c580d0064020b40500d40c42079072030680b6000f01800080144a0005041e41d00208059040181005101d034540e8001c1c101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 295815953 1250 295814703 295814723
    0x507020f010b041401060c03021005090318030307022d0607060c0e0111060c072a06020f010b0906060c12030a05010807170312060105190503090c06130603200304060b0108060405160c 80
    0x14200044610a0720300c330880f6040051616100c40700410106245c1c10304070069841c0641701d600180881600c0401c0c40180503ca400d0001c60010078014012500d01c054100c03642d813110352901c034004001031140b04000c82e01c40002c0c484a9441070400300d10b05000b0000a1006881307a92030300700e407a0001c000440b00034200340300100c00030503040040c1501259211260150a040040103418008541c5070b40000ea80b4010410100303030744402c20107420050940c1d2142d80c0303d4110000070b040c001a404811141e00b000428400d50b0011351f800541214081410f8a4555031162485044150502d640081940c0180503c0c2401a0134822440d008101410000c6c50200d4144820118035410301d820008075001004202d0070308010b1006100706102128030b240303414403d2008641c2c180c00c170700038001019a5000c10b11a000c4800308040400301703005941c030352640303024a000360113001d090121900180300700c40803d0300d9082c280551401010080e80c03a8180403146a803c071915441c1280940d040160 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 295817203 1250 295815953 295815973
    0xd050a06030521272d2202040605210f0c030601090f09020a0207050d0305040e0c0d090807020f030a080306010c0312090b010f080c06070f150507020f010b041401060c0302 75
    0x41c0c0940201310b25003083d03d104420758808004d10580e42e8210088101140d807420b0807020a015080c0c08450811a09206004991154a00c2c4141c0107075045591510000f0003241c40f540001c060480704850202103501205030b0101a4103d110540e1a06130040b03038200400e012070b8544002e180e102c01d06150414130f0303695611020481d1122030b032180c0c074030300c2d0b00144600d2415030601400700586010380312407074840e40540e13000300584500d01c100802891624007085c045100380040b502d9134015450140240200703400c00d980c4aa02c000701c101d2003010310503459003141c01c001c1002040940c10000940c1960741e0030006444100a44000318100109841d001c0b000220622845400c14021006966558140003008040c1d00392a0080400c5a001c62900303100c6565500407290fa01d0780c0700c42c2d81e0624403203a1030002e0000101940c0e90404900380302c10071003010b0b400201c00000d00e80440003409204160b4091004a84030030800a5822440c0c00040c0030140c010300403610720318805e1045800d4488 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 295818453 1250 295817203 295817227
    0x30c0405040821070e03151602100e0114060414150d060905030903010b0a180b0409060e1605040e0a020609060c030d05010608010e0708150120030d050a06030521 71
    0x104507004200300020340034080036990104524502070f0081c6c0080081003d040c08034228400020300c1c40f01e2188859181044d040c4c401c0c848000071041a03481070000c07030318852405018100c4034407103071030300700070880001e07440d1070980100e1030700106031012a559078072882c0c1480340c45600c0c07452050708219465000c07030020755207100d0004001d008501441e1100811300405094803921036000d07202d290803000c14052148418081c415410100000149100c8001c2c0882d000e0450110003502039031520b83c410811034008210103c1c01c2e1034082041840ba5150340c104400c54441e00b6000405501c00307064500142040402000c000c04010802814844001d03401482c540c008808014610344840c010000d003a0421030144c054141489101c40500c0e00c107200a001a2004162111022071140d00c1c4c4856401040a0114941c840c4540c41c141021012000c0d6070b50f100c0c40840310094644000a4909c2400384100400d980d03005000c0c1a040721580e48140107000b040300c2e1a80709030010000710500503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 295819703 1250 295818453 295818487
    0x9061002120406110d030207080319090b07210513171b0703030905010302030f160915020114131119080102030a05011809020109180608010203010b0c0d050405030c04050408 76
    0x2440350741d101d0341c1c404c09000032070400482664400c103050040c041840002d00b5501904d50201c4803c1008002d849810001006465070183c00703491a80e050083c066807035405004c110030100d051032504080020300707000c00100ca60071181c000e4101000000300b0f00003030391120300042d442c038114072a40c00c0264002402d014500c1c030031199001c2c0d81c00702108000301600001c0d14801090309003030031811443d0002000a1880c030091500b200303e01d1035a5140310b494001d94002c1c0c00342070507004031741c1d000071700782d4010b4001c03c01c04000280c1011031000040c000d80080c02038414043d4080d09074280743d210b02c1c0a1005030715401519044402c207d000100350384d0000d1003d50b201c0c80d0000c00c04107181d450f15079104100c000c417480300c1011078103190241c00580d8000d6442c1c1d084034290310200415158544c080c400500081d0000c0e485940000000108844550081c2c840800c0c8141600d03098400c03214151080c0c496441070b00d030141c20070300300800c251410b80d1089038840d0160342140d10b4000c24400c0c2483c84 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 295820953 1250 295819703 295819709
    0x40905090304030506070509060f03070302160501240f14120a050115050402030f061507020d050c010e0d0309091a040207050a03030b031f0903020f0a260306090610021204 75
    0x6648040b50410900ca820030065410001505140303182c031081310042541c80c07140301e10740e1601c40c900101058003907100e941150040e00c2c003040911418107461030700a02030215000c401024603d50071400e02001031868403070044641c41032030007400034034040030414281903101100c2d5200c0495068103502100c07e10007a00031a201d00000070b030240c0301002032051b480b0303190441406544144100007524034102c90007034009401301c0d06056441000540b0400520450000a40000e0f28480d01d604001d000200c165060400742c83d5030344a1034800f01070103a40d10001c000500081c006810070851145a0b500800c00c5000761404035055a0039800490241d80c0007420841e5a81d10202200041c954103120b15413a20400300c0180c0a8481c0d20b01c01d021400511440c140829035668424008260003000300e8009001c810041e110002c185040502500144464100c450b180c040c140380b0241d14481c1c02c03684507160007002440075849481c2845a0200d548101d4819403007042c00040039801040003500c01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 295822203 1250 295820953 295820971
    0xb100207030309120213050916080c0a0509131101090306090302030c010f0c0e011416030c03030f0203040c030f05120d060303021009020306062718060f0601020705040c0302040905 79
    0x200391851400900f02e000e598041c84000e40c81e50600401a036400c0c220860305c0c80d58103404101c98031a00c100d1424100d81c84506801240101d20000c1d8048010954030400c200889507e81950366500c07d01102d050100c84070300255590788080c0340018440040014a40e1040c9410884640c807983c1d10012034440c0041500542d001040b1585100c1090041466503040f811040c041e00080c0b40002d01a90701d030f81030050501490f0150806041c0c152820380d180802003000c0816180342030300300540701028649040e400079041c103900300c070315242c140216401285e204e552881c00342d2854490520780c5041050860b494003480070080848412840a0010a103160b100001c0f0240355140c007918201c201d03a001625030b4284006000580d40c042101c1e64007240680d4107292a091492046c40c1e01803800560038440c0101c4c030144407641e07004401500290180c074003210680e40785c40d480740c0b0894800b00c074080c0c0140d014103402c0c0418241340e000b00d00d085605060141c1060344039070060080d104119080c00c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 295823453 1250 295822203 295822213
    0x24040f140f10020409051302031c050715061a070b06010e0d141b030a050709020f1315030e010516030e0102070f1202010615050f070821090705060a021506040b1002 72
    0x40280340c811541c105403810244001860548c3c00320791a100500c1e01c0407910441c024003209810302901c00c94003042da00c034004038036408400c0701000090106008528003040780c49c50315518000c0410441c0e0b50241c010600b60010303520345004407203078811524110741000002c1c0300400010a0460213200680c2c40c074000c0d02100440b01c2062000d100d100703031010720a5204c10640320204001058400c02e03a4583d400150f030350000425003603058810158607492030082075900080e0700f0b071605d998a0542105d5502882079540002c0c21900342c500c19036002c0114044900b070f12a815020fa400b0944a03018030001606040c1c0c02d40f1050402201c001094428000410301d542160b682071107104040e00408800701d4580d59076950007400350280e1040c240c200724000411000740100c1c40141d4184003076408484061442c0080c64a030850300c02c0d211003006225200c40454903286c80720945060f2215540203040341140c001460034112000b409c500c0c0c0160361140600110b480d660100c110048458000301 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 295824703 1250 295823453 295823459
    0x60e13062c09010911040b010504050909010b030c0109030308150f060a02150c04030c030803100e01140a0503030a050706110d06080318010206010b0306090405120c24040f140f100204 80
    0x21001000042002920381d1401c1019000262010303200a42e13050181ca0010307c5445040058030309200d6600050f60223000641000044041500150094403068044c0e5800c09a408011740b0a8140c0707000090100b01060000340307002545100310040d504008000d400e0300800c180c0840c01e290b0051795500c0043e000349040c0b0b012070400900751a003180c25030a650340b505103151100c2500005c2400000d0440348000089001459280d4403000685211058604256560506c0c1c0c2c0b820140340c6141e42c0541d0404a00040350b140110540e0074090301030f2541460072025550310001440c0803140704012020510010f040c5070050310441c40500b4503900290781c1c400b100c1d40c1c0301c4204441220420b04544c021001889407032240f0040d0b030740080e01a20003080540b0b40c0d1a1075802d00c1c103c2d002102c000038000c81c0c3d408900e040042c1440803410400d88040740b40301490103801c0d518100700d50203444510f81400380e40005a0801d0300d0440d4458540a603050101801b070b40314240b501c1100c0380345007180c0206080c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 295825953 1250 295824703 295824779
    0x3010b1e2110050d3801060f090f0b0d02070602040306060e09060408070305090d1b0515040e040f05070f0906050f0303030603150604060b0d0504030216060e1306 71
    0x141d6085038110807030703014003454480051800040054002c01c00788482645404503109500c180f8075402d01000440f0303540140d8100b016403510244252400205540c03e90f44525024030407400548920716030580c056400e104041a00d40d2000300c00030300341a03080124a0104080f4030151010318414100800d000e81781c5070280d00c14501c0941106519045a02400000f070025821181110346c5418640e4640d005140015040e80c0b410030007070001900400c00c0340500340040020410780d001103551640203030101800c00100d01071405224500014800481c0105c0e54614803412124418000c50326401d0321220b04804e0400b080c4c2c000c041150702c0c0d20341400546030030340e41d43d544d11a095000f1400c5241540c0080e5541c2401c0c001400c145c00908041201500c542c4c200e00c0103030205d0001c2c00c2d654880d003c2403400500c400c40b0700713800602581030006500c905940101c0c2c00c0715166612910142c1c0100100014002c41c0e000c000344407030781c401c400611101c0b40740c07004608001480a03030700d500c00a1340c94 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 295827203 1250 295825953 295826017
    0x19091b0803041401141c06150c050a080d020c150a180503091306080a080d0612020d06020c0c0d080901032004140301060308160c060c02010503010b1e 66
    0x80804a81c01c284418440c04000d81c119a6242000340b804542c1d42150003c072401500c5480c04441001045070f209281c00301c0749400c540211500248611031824070030200719003044604c1c03c000c040750020342105010617119800382c0001c1c5d010040c014034000742600315615064080341d10110411044040080115035407180c100301c0300c0156240103a43c1c065540c0d464a038490101940d07c01c00446d0035030780080c0f290754021800741c6090b40498240c600542004400740d04100c882241c0e59040610100b28107011154501400d030740580f10303080d003051070760300c1c00701a40044c910030106110700400d004243c0e0303441080050f840d00440d5901d54400301c4a00040559090341556444545144a0b0803055140c0500700d808440b0190000a44d00d2842c034002405071004d40d00140401102280001403101000f0300b0320100ba1207043e140e490f0b41e0351128280c40d40c2c1200100a40450b500f403004001204850005294480306408104501606901c000c0308907080074020044440d40178042014a00309004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 295828453 1250 295827203 295827209
    0x15130b0105031203011502011b02161d06010c1104110c1005190b03010b0a03080322030e13180b090c06030603070b0724020702180403080f19091b 64
    0x101805030f41c0e50350b00400381c092006104101c1c980300348074201041c01d4400c2d488000301c2008040f040c0102c0b81300290096803070001300da0340f0a0360b0003c1c00740060b00420744c0040007000740410008420b41c0d600c030001901c10503103061090768090085403c91030b80f03548500c500300c07c6411a20502e902c0310710003020580342c0300c0004483c4401503d08000d100c064414005604041c003218600802d88400c6240842c0c0500b14241000c0d0f040400c10101000f04074004000e1881504d141d030301116401103085040c04d0882c0d5074000500400c0748030308090000d0600001004102c4a2403401003032442903d046880071203100c203419909100d09400f40f00f1525014440400010400c9805030b045d8203007e0000303034887c0040d00c500002a00c002a04000700010f10342c19104c051002c030408140c0488041c3c01030003940c4100c078101d120701d209040d50070079107150002c1039000e246c240e56440c00503070700c1f0141d1000d6020041d0031100c048201c041184002000380c021100c65900c03852400320f1254222a55810152440d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 295829703 1250 295828453 295828459
    0x21e1609051314010c170f160507060f060617010f030308100e070c0516050102060a1d0703080403030314070c0b040312020a030b0a0b040317130512010b100e0604050105070515130b0105 81
    0x4081c032200070b07001e41c00346803c00d03c0c988c1c0311a808200f21030107564501c22610001c0c0b1041c14886107a1420704164026400c8805a882e0940014100b050465025400740100c2c1010403100005001007407042c0c1c4240d0744200603010300001c00d500c03800b0f80d480400c0d04881d00e0002452400340903080010900140c4401d245d040030322282e043c10900044e4842100400591460b66504441442045858a0304000007101810742c0c20740d507140d06000e559a8040d01081d800301303080952040ba000b10341c00c0d0300c07841492150381d01000712940399141e502ca483c01810682c1000301c4410145008401c40c0b00809201c14180c80c000361207544041480004056030f440941c83c1c880a22041020030b40c040014200000700b0300c8540c3d9108070100e45207044420680006811110b100a01b107407580055000f0400c1600440d0041c91110040c00304481142c0340c0804a03070040f10510041013154010005010300f50300c00c0b03050ba0b507100c6246504a900440c100c4091001524003400e11050040c0007102d14090a416 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 295830953 1250 295829703 295829747
    0x2e0501140a270e0304030c0e010801110306060a030b0411030109060f05180610030608120301060215060f121207050102090a0b03090304060806030f0706021e1609051314010c 76
    0x16880100c2e4840c19001c1e0a441c0798032075107240c5035030b4000d10448010710350104600c1c00e0746031034840c26003d906003400307030300b0035036180c110f110b86101d0207a03068a00c94880140854070784107200e00c0440280016405040c0c20039103030380fa128210315540e000345000c2d20506000160092801060071021b04003640154000c111590101d004403c05280712503000340e0035500c0020440514800318000c006951045096004951580482c0750500000b141220916821034000c0402c0c3c0c02d140c0004c9205540071948040d034240c440a40c1e02704011503001c44020702c015696003500003074040c0d0391035015243c03c40e031030303507000418941614000a0074006041c0c01c0003101d055190201d01541c0d248914090001800004000164142e60030081c40320550f20706c0050f120159910000a542c3c1c01e103903100c40454001961100700b1014001a01a1900ca10031042030446450f101480c0c00522000d003200340d000381030191000104c0d00724441e240902c030312080005081400b280000f014080340089e202d08903121 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 295832203 1250 295830953 295830989
    0x70e011e0f0f1443060b040b010804020112020f041e12170d02040302030a060905010606170a0b0607080c0309090f090a141f090b0601020f2e0501140a 66
    0x1290300391a1100130018103180c903403426241040c940051400540c0210300038004580c1c002c100c2c0421001268460501485001e400d40300b000107481e454560f082c00240c82d10000f90241d03104018841d0502400c1000501c0e020058000d400727079920581000c4081c0e010a210038034521700d8462541e0040a410240d60140041c594030521112400c2007082c40361800810070903041509070713048400465004084910403415450044040e0048210550f05546407101c001003040c01030342d001c51803010302e036108041039407102c10000040003005400e50b0805000d01824002810410062900c100807000540c3c490010f00c1c20851f0001005004040148041060200c10100011b50f101c00e16401003030304040350340c00c1c201c041c6483d04015940c800c0c01d6010485e00110a12070b801a81c03068081c100c0c26045948072401603a0300c07100859110066842100d401a012400050410070340a0300c1700329000c21800310800800b903602c01e030080c810424070f0201c5a4182c4c50090100401402c1444100003a112 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 295833453 1250 295832203 295832237
    0x20306010b0a0507170f04030f0b010b030603030702040905150103030c1e02011706130f0c0318030807080c0c070e01090e0703170906091e010f030212070e011e0f0f 72
    0x25054009000c00c0304017880e40d0358080d040d401c0c1c5104d0140d642c50345864a83d2810151420750003c04295603819501002007040f07903850040300d10a10003d070040d4039004056090100800a40509541074010700300422120700d00c10241d80e000318025620210b80d01500d06148103030381400e108101000c0d260301d91070b1006076005052102d4621443d110060180c0c0e40901046c001e40107801e03e0b81c101c0d071400e40e0313460000c1b04039409a200440181d070b041020801030318080c91102d2000d10041c0c040307411080001c8440d40f2615003d40d000c85003154450600c008845101d14041441d0040403001c2001801800484101e10a21141c5003e460041001134690744580f0390643d03020301e01030152032002654007210340320308044800c0008007400310005000c0600315068041c6080144600040c050059205039602c00c4c001d030303004052500c44201141e11100e606480071625490114180144480a810a17820301038081003540710f1a103034800f03c006103510003040200a045020140481140c950000d01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 295834703 1250 295833453 295833457
    0x60501021c03020d0501030303061a0f0f0708070b1005330c010e15040210110c0d02010c050f0d0e030a0c0509090c0303071505010e041109071206030c03020306010b0a05 74
    0x8071161501c106503508004110081c0c407540031a03903c1035040800000406506920007011103c0044502d68646404401401d06100701e94440719020070a00000030800301e85c000420000b4030031301a003441c08401760380d14007029004590714000320b491100100204d080072000915040030a910303224440303201d5261a0014043d00351408080d00d0049069800030720254400c3d8005c030718017030440b513042464034a541409441110102e024080e0f45201082d41e41c003c0010b50149070000b0003401501c01600c080c03180040e041c03002030741008000402c0348007081040c03040000c87d0200d00098107000d55410f002030314200b100000d450082d03121030405804114066411400d55800312080e003595102ea41c01d0340c0c50b1071004078100d9403601001643d80c0c100811b60100c0403001031001c201740f0040e80e0324191614090401c4902800032915030001040502c1c000e4140c07503000b180d0b401c1100c800020050800c0854442d40c2046a841d44043c100b0b00661034100400c5005140c2114807901c0c01c400302d44010154 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 295835953 1250 295834703 295834723
    0xd060b10032a0e120303011508160518060705030d0e0c030304171e0706020c1807080a06030b07230703090b03040303090501050f0105120c0114130e090606120106050102 74
    0xb01d14007070002034103485182241c0d030350b440003040e26040d0764002010070740382d506c20f00c2129600b0120700b220f0015540203039030962240d00040380041d1030740d55403001540c807540415503a04040f540b4925040e4582da40601a15220b40100c0046445510b030048280842d0080104803a480e804002140d20554002040b5801d881c40c0c0c010808000070782c03c40341c520704a80701e0be001105001103401341440c240d000032030400b294540c5d4215041030a50a040c01503070415501030007280c0429000150060303014514241c3c0000c0c2c03c1c0750000c0c40d40d03640e4441c0482e000381a0741c1880040c090111000d40544084501d0004413889400540780020f26613014007443c08501c605a160b001c04800141494000d03444458510b170014001e1100e0f2030b0240b00b80d020b0003000d000c1c40344235082c032001405c1c030307034a0000d902e008041041e10f400706810b100340c0c40f01005422030398041d50b5040300e41d02d01160403110a56000d0007401e980d001401d44d42003200c01c00019803584901c400c1c450f0f00d844820003080c0e0f4005800580 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 295837203 1250 295835953 295836011
    0x302091602030f2d09060301150e0d05010b01030f0e0601030b0403050d090f1202030a020c3001090b0c070b0c0703120c090602060c13170a020d060b1003 67
    0x61000c1900180e0031406100c5100070300f0400842c9001c00c08003402400000342d0f4198507098011580211380324003c1c080c48402c540c001c002440140040c1110a008416005d491308001c0c0b040c0c900027000501c80e072259442203409035183c14000e100380d6010b000740014201c1102d070a114400a19505596504c1c0c14403010300315a00a0700810145070284089031088508000140100b08081c10300c1c041003004200f003220420b0160031120b211900c04400d039140c0520943c00707040008e000d00c01708841401d0155132006194101d859000007413100c40300c81009582c1080011503800c6090502801c1010300504114844800b000240b0010b103002c0b041d10391048600c004e550b19134446080445001d0500311405a042e841c1070b4141c1042c580080042c400c0303529942c01c44100c1d56800380d5400c014000c0e0710004034192094103041c401d0207190b0310050000542101207407003d0301c56070001100103100b00400e8405d41c2d9540f182c18903504010b4444901050607042c00c1c007040742241195100040c45094003c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 295838453 1250 295837203 295837231
    0x20316030e13050603100c080624070605100501030207020108070807170c0304110109080a020f0d0501020f0a140a09090b1519031506051b07050907030603051501030209 74
    0x405025049010000304041c1402c0840040100024000c003000d03501203101e0700c50080c080000b003c1500035901e080031140d642030542d8840e4020321072950f5940a00c0340d148500e0049541c8031110b4403016001c050301840010800342441e03034084404070095040141050300401112000d0b0342c21160f925001500d1703180c076030f46a82c0c81c1542251040d90008448003009980014056080500c40185000c1d5004e41c4199004a45810041d500100240304600310740e00100106400f500d044207036000100c82c0906400c00c0b4140790f17a103040c2241d10000b0f6101c0fa10201060b03072130100d648110440480300c0108480e902e40708002101a00b40d0010b84205c0d03904036118105800240c6803601c0c445807000300c0c45074540e01c80068031100d402c5403181841800000b40b50082d0007000e92101e014a001720741e0551540c0303180c0000c3e5103240307100908805100145104110300021251100300c0020703c68492a03400150450071441e010b820a6442c42c1401041400000103101503515400040d40024490242003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 295839703 1250 295838453 295838497
    0x110406092619020418050705040207021305100e070212120903120f060420040311010224041a090c01050a21060e060604030807030302090a1203031d0d0203 68
    0x4a80c0c1115501404440c014521282e00c000c284542107025184203c0c0c0502800c10a00300500e80b0105901014101d90f110390010001c904140d13004000c0c690000e40012941e120080e0000c0589106a41000700000070441c1080180e440002040e00105c040c8040e045043c003148140c245070180c900e04210390f0f8010700115844003420000c032a518504d45819040318904550f601d80c002404a4415000e642071010b0b40d00548108400301e440d040c4d400850034100f60454039020b520040b0f5054880c1540b0900b110071412000c65414070403071042003440f000b140d00c0c0519001d13844d032004000801102e086001800308410780404c241c0d191190a282c560b8640420f11005c80c0d03041c14142c500c0a13030024035009400480310395040031b42514101d4010107041d480b08010300c010f0f4070903448003408040051001d000024820b400829507a0f01c01480b03115100e03186c01c00c1480a0290850440109a071050307091f0f194040b40c0c01c4400c4c1c1e540b000d4084e00d4103213000c0d0806504c9205825280492518903e400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 295840953 1250 295839703 295839749
    0x6110a060b0a0509070305071d030a0809040902030f0f010c030605180c19020109110105190c0602040f0e0402100212040b0d11030103051e030901120c11030f040911040609 75
    0x800020f04008094810b02d0422000190003004242c490030300003142c00c684130540d02441031354a80742d0000500206200e000390f0300c0b40d0103d40c00c00066140d0140d150703c0c42101591f0704002424030400b0510140070381c0c6044100c51401c495144186009160600310200403a55981021092920000490b1601c5988600400b9030710f104030103078001e4980c1d071040109000742e8158090510184500c201018045048005444170301881215110746c0e15a0048410380354483c0081b0b142892082c0009808e081c0c591606d428482c506401c00701003190301c001040b0940ca00024000720064440c00505484090540c0035111481140120501c0c000002030b0540b13440700c2580450101502450040d88a503100c0c6010fa072540c1d203506283c03044100c003082081c2c03141404421100e01520503165484d2130300185d010038000d05980040b090600600400d0650f0240b01400201700d00012a04d0103541c0d00d0a01c0754443c22690504002d941042c0309000c1809a5904492030710150390381c1c110343c282c05001599070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 295842203 1250 295840953 295840969
    0xd030c02040c180b040b09060c0f03030114041a03030d1a0a0b1314010e1c021905040c0203040e0c2b0507030609090f2018090706110a060b 61
    0x4000d40142c908280004882d91242d40e50700390048002c41c4a01c00d03551014400c4403030041d40036821a01008004151035482c1141c01080c111500038103444004400c0814141190026488030040307101401c0b40003000d11b414440c6100d40c06a8007100041c20030741c0c00100f6607074041c88002c0f406440c2c0d1440e0031494203d40401340c00ea0040010318003401b168446c52440e0150304440b00d0320215005d82c0501088076010358003072501240060b550b0064800c00c40082000640554103000c5058680b84800d10160315440c1c00003d96a102c5a22040d01501d0300c414803003141d103d02e0301d070b8003190000d2100f8003032001c011078026000440c80f11071588981c5040f054041010401620f82e00c189004078134141e0031122900054452103054038100000e540c0d035800c06082d5814035000038020740d03036021075400048a10320071004a12030664401c0d0b405040707902082d08880d140346884030303c506034002c210120000308200c1015000343c0c58040d10103810f0072042c41d9207451064004090f1910781001c0310064840d01a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 295843453 1250 295842203 295842227
    0x90105070605090c09060a031e0606031e0201020c0d031d060c060a05040b10031214090a030609060506030726030f1b06060f031f060f060801151407020d03 68
    0x1004015604202030056910b11000b004c0390700540011000600600d08501945d003241e4111001e40403281000f03803200010b010221048400d25070741c41c00400814010b02045d0b24004d40340542102d402100d00001e460b181e030298500d48103110341e905e4200001c0c0d01139410102060310b60303600b0300e50794001000983c5600550503440b605101c2d120400c14030301c0700754001c140183d001c0c000c1d00b00380ea22405030070b00800000b80000b808040e41400c0400f1a00c3c805c1140013008513407901e00303070b003000484030004054000f20b50040d44c101e600c9400c14800e00c8080e101c0c1c00d8000f1001c50042010911b0003140e8492003000c0b41ea02030003121884681c0c003260b03106104032100a410300c91a141d4038170b410036440701e140040805403402d62203850002603c2d420282089456401d0040c01080d2401c0640d91300307112041485100340c0c0c2180c6a01d07000a000307000c900c6100141409440700040f0b0360500441c52070503400180554100429440c0146818040e2b10890708550340585400b0100b040504003503c003596120 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 295844703 1250 295843453 295843463
    0x1211030906010e1e010e060307080f0d023c01060f0f150908060a0f090b04140613030f0f0201090f0c090e01020c07170715030c0912050c01030209010507 67
    0x42002900000401e41c0d03816202210003030801074642148a42c0014000714110320401c1101c80140071041382d80444940c8040000e040350000d07511840214108002d0b00d889100d9948803114400e141c036010711084a1a180c84410700c80320801c40d42c552160800c5851100f41c2103490250783d43c400d0502074018202800f20f50034100b04007a5202d40314030f81d4440750321440503900d40c901c0010107e28030488c04d80f402c0303030700c103030010311041d198442c0481c0148000894440c44c1035603462034500080710010f0540c445c90142103041090424070300554104074000700550b1400c4600900c040002c0d40228104000c8012407034070440c07498024005074014030301e0390400b13407446103500716807020004850041001c0c3c0b01805001e00c111040101400c2c280d02403040f800b4819001b9110a00c10112003e040c4080390390740c08101d80f07501d60341d000301e00010301081c8041c00c0020b44a240d103480071394001c4000c400800301540c2c0c40030510f1030741c1c59503900e401251815504054000a01e10801d0384140c0a5030342541d084 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 295845953 1250 295844703 295844707
    0xa2c06030408130f03111009030803060a080715170915070327020f01050a270302060a021b10230f0f0309010c030902100c17030f06090a060807061211 66
    0x28018521800545200c11100210800050300c01b905161100604d40440da4541110460950790381d400e103030700003d104641281c0001400a903042c401c000580040c2510840c0c1036060442d014020150042401400d00c02c900384010721001d4075002a0b06000c0004401e4040c00948901e00210044c06040184404120542c43c10044260070003c80440c0103200321082c11900300924019140c40c0605019800403c00301c03a02c0c0c000300003442d0790300310744900098a101c05440d01c07a070028120740c22a405d14070042c4c3c040a000b000034081c140d20104003c104403441134801c803003900300a03da05500304000380c0120825165840c9540d14205484400e101075002c10f13249d04010b1021a556002183c608050307608054150385002d001e4400ca400c07007034000c2d084c000301d41c21402e0150790021281c8411204c120786900c00306e225165803005140034400300c0061000900f4030008228640c00060203052501c0e107000300800c1081c10001d0342034110707480c5042459400320030000820007000319200c200003d100c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 295847203 1250 295845953 295845959
    0x30904090312060f1a09060702150d14060609040f09120f0e09150d050a2405060111060604090c03080301080313060f0822050109080a2c0603040813 65
    0x4005152205450b5400c200840380c0c0d0754254481190b10761061103d1040c00a01501c0400303551030040603440c07000307480703a0303d0f00d5019400f08034155080c3c100300308881030105503040d80784541d010728000001c82c041d0040c204c0c2090000207a05100b4910114811603139030920840c003080c541c118208180e00510000e000c483c0c2120054101040d4003444000151040b1300c800b49854070602980c0103803c20b116440382200d9120071f000e2142c2e600c072410750303091048010b000009400300c040307c0284042180141c2d1007429080310b4405803103003d0081c0b4188043ca145460000c540000d0940e40a002104c020441c00d8081c1044031005403190005400200000004124140000024500100100210307145595101d008540224103041d1450014035850080b40d2100b44201d007d4020032900100503080d8101031355644c0c00c40b641c0c0241201c02071400b0400d00405e17500890400d24011303030040401540460780a940c0c0c03549002c0c000040c41400003201190a01440c00103645a1440c2020700704c0c48591 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 295848453 1250 295847203 295847207
    0x14090102030a0e3f0a1d01030203070c0b190509030405032404151107050c090714070602030403170106020703020306060d05060a0f020f0f030f1005011d030309040903 73
    0x4402c89054a880382000d460f003410900001c0c4010005030b00c601c1d11031142c1c18654101202c1600715076842e800040621041150090f804010310700010300b0380b07a9420112030759042d080181d499004040c1814410b000300a40e0f5508807210080c9581e0007011150150b99075a0784c02c0d00d000710140201c0c0011300d05810400e0a60000005105845048048a00c00620006003803e0b555584203d41140030700c04020800290340003070818aa624480f40108103143d00340c6c40e050003600020001d44040c1d20041e04950541401e084180c0c103c3d5403850010000b00242a00700d0251103201d400070308aa50003c0040c061520600d59401880c2244052282559580e44000c1d51164140020b80c441c3c05a840441d1040c074007080c903103408991141c050310607961220800d000800c42140a40f605603001c010009814910100400c40002a60f1040d52241004001d807045140000c0184601ca00e0160042c41a83e8102d150f14400c0403850003c103103580c500c10007190950203182e00054005003030180c1541019 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 295849703 1250 295848453 295848457
    0xa081209030f010504020d030302070f0b0f040c0e10060e06130305030a021002070c12031403190515060f0d1e0504050d020105250315080309010917150402030114090102 74
    0xca04504a6003450884203400b07003215019500258407210b144a080d0009020b5009441c0c240d0158403281c1400703040b5240c101b00b0701c0084480c11803c0d00380a040200b0049004229406480c00550701e03602032601500c1002510102e0080780140611086403502c5039484000b02c0b008040c035015250144d9a881c42c0481d0b42c0d80103420540098010000b103031310700c50610b1003511426a00040c0388100302e4a0204104a03901100c1c030241c00700000760b4400c4052011400c01140241c00d07013500070900a8078400e0b040200c0300061b00300102340700303614443c61480d41c0304c5065031840541d803c0c655545900101c10900240a007181541425000465210b00705000d030340058403541c024026501000e46080d07040342203807400c40340d10401c10140d41300d4901507503020b487c1c9060300e01b903401e000a80711072240e84c101029059900c2040c650f80001030b800ba25580c80040e0070002d00c0c40310840e21111000c90b6035203445500c950a1030366280d410600040c1599001d401080c0c006600e00c03000c04035401c0c0f1440c854042c1d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 295850953 1250 295849703 295849717
    0x60d140304060c0b090604030e09090c09042a030515091606020604031d0a1403010b0a0e07022407030203150405070c330908121915050603150a0812 65
    0xa00200400031741c3c07186020a00c184510740c035540340030220244004020071803002409000705845411000c3d0850344035110725a010764020f401104160040070a52201604507560340c20320544808010000101c0004070422898070600c01c0612550f500c01403c0d2502c042c03c203a181c8051845030000402640104920740111f000c0d580350340541000360080a107030030000e09025005008803d04020311070800d20071244c140d00040000c25100120340002e454011142c00420740e0094030300c01c0c0700c00c00e0703010400005400d14a28900101c2208107074081140e22000340141e0a01d5000000030300340107280c0a40214080004200304000d040051000b004e99a10000459200c48020001417490b03010f0064072030291040c0480390441c03255000444050051200112221001844500c1c139940c070340266248140c0c0d00355a00280c0303900c03008483c1c2c05c1e1141c100c0b0910515080c00f8041c0300a4403440200c0f40c4c00001035004038044815900131070001011540040c00e0317030044014210000c19404010420 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 295852203 1250 295850953 295850963
    0x703050a120209130b040213090f0e0a020a210c24021603022b030503070810120210020a0803010f1403060c071b030c12140f0303060d140304060c 64
    0x4454a00e0081d04100d104007016141d02003100c1150690318a4203400440c2500000750015082c60083c800c140312106a9070002c01060f0b0f181c0c8450405c03c02280305900502d0041d0000b002d40000e550042a60056180540c803e02c8541c3c6410b0343c00780006071801c0d040f846e4040408030201d660303030805184004000010365298440207150755401031000548182d103400c056a280b0300e442c40d5a00b045070070b00d801510681802001440b1000c4c4444d031180720320010340640c81301ea075649002c0720001c0c01c0034030060402d8519403a0b41003e0011804034401e81c841a40c1c140d44e8508900240d45050b481c2510210000701030030400400828900c06100d0a001185c1a017014502e103149907030105500c803003040728255481007051010b6400304840270028151221108101000e56460380c860f4006c0e41c074070390004503115012000c03c004021201c450303441c840fa0304601a2a83e40441d034199910ba21020300318a10070b01c10003070401c1c1840445006400141d1910301200d6665950b400c0c0a08504505041911 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 295853453 1250 295852203 295852217
    0x504020d081810030b041a06040618030c03050c0118030804050607140d0207080d110c04020306060d05070206060901120201090302011d09040b0a0c09080309061b060f15040c0e0918030703050a 84
    0x5040480e603441090b140d000808e214107060074510100c4401000b50218031803500090746c00808110a03031042409540114098141411848009480c891751840400052513182c0c004101048800c0162000e9690481d9259610603981c18040da2030b844140b01285107010312142500700300c0c0c0010307000c012120144260740e13203a03010040645000312005802c1e6455000071965005a203016401594460801000c42e401d2041d8000f540080b00d000302c41b0000568000d009010342c916040030f401d4014000d040000d00c084010364002030080b1500e200c020f0600144141c0d881c024043c291102c00c05a40141c80581c5614190520b041201e4069403c1c0800c80c0c41c03c100388095030b01c2682c842c000e0b16001c100451070704100c0418402640c0c45441d5039142101b1030340c030b03520020f4018450355014140d075000500c0d803400c20106400b412000c4008283c4500d2411070100c00c1941c02410071203c8a0b01203034802c030f035030b03440c1d40c110110089a82800042400001230700ea0405400401070402900155640c039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 295854703 1250 295853453 295853471
    0x605220b1908090a0506040f0f05060109050a0b06091003150b0c0106090c050c122805031504061202040e01090c060c0501060f0608010510021608030406020f010504020d081810030b04 80
    0x7a140d130051031024156030456000500031a8105a07481c0a89104058400b030106040d22428100303070003070700500c01f031750745640502052175000c2c00b800040040448815160484000005044418002010083c107845000014962115908440c000c0210800c0d003036482200d00d4a0780e000b0402400360881503072400c1c3e0091a424490790683d40c840120800501e42d8010003030104105420040714400c3c050301d200c80207144003403240030700f4110040c1e079199241c0303038142565081c40e889811450940218541041084910142c1d0350310809190181c4000a207081410078881c05403400040142c00c00c0240c030000503000e5844200c103222a8000c1c00200511500d68020b00b86c000c020342b10b80380010f030601006000310b01c1c01100f24501c242650040b203074402044001c2006048056002c0f060070b80000c1020001650103004180e030540d01d280080189107401e50005401000455014180c003501184d11001011000d005080541c2c1c0244440d9018072802402006446003600490003117080040e66 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 295855953 1250 295854703 295854721
    0x303021207020604290403110f0d03050d02160203070308030f0f09030417030d05070203190905091513050a0519140f0a1413110306010605220b1908 65
    0x1503044198010f080500d007030b00e095807601c403500d0511002c080580c43c0b0720300c00e40d801d80c03648002c00c011803041c030464624011040c00c00400a61140b2128081d003d101d03240000240d00c01d080f5628000a1f404c0180c4032064018003202c50403041900940510030700b2404001e1260030000f0314480e18224827140090355034444042ca0059069416040c2688148000c0c403c4250104a003907130b82d0100d03801c070303810101070020200644006035001c10158000142e110a034040880480410784403074104041c0451801001c1150000000c090301c04d0030b0800d041c03000d80c80d0388907043d09092403801c21080c0050306002c140c080c000c01040d200c1040c9a9544d07101c1c80c0d000c40c014001c03d0010380c0c00d01c624044030b07942c10304c031640c00200060a402c08107544664041c2032303046500e0300b58003820410810407629030700c9240c00c1c41c5240d800e0050520990121004002c038651041c1294010840050640051036044c484a40003a14940103100c1600c400700341c442c200e100100d80c1d03044400302541c0310801521440b41e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 295857203 1250 295855953 295855957
    0xe0a080304110414040b060108060301020705070506030c040e0108060106020d0c120305151c23210412111005090d080702030c060703020a170406170a09081303030212 73
    0x4009010620015000c28402c800e00d00603801c0290010601c10090090419203030022035049511701445003d11400c0d59011420b01c1e4001c00c243d0085107007141036180e903540c038412842071a219600000020b070091040505440041000d09800e41d91561592006902e84500740244001440350450840c09184104440c01c09c050300b01040800303050218600300c025003001009840e00d070501e2408001151900000008ea0142c1c080d00e84a11142c00e241c010f002c82003003403201412120f54190380c0c898200209501030940305001205405078004100050035002d00e901601c200744c083c110101c18490726044180d02410101e0368824010300d505402d854034000e03068403035003000d40d0000e0354000036283c000030001e0307a000508407079500304007000081e0780b60304c4040e00700d00680112070010100320002082c5004d4403420300d00542854140704004180100c15034801e0095540140841c0719141e155000c050280d80011815541d00c06040a60344071401c944800c80062081c0b0301900100b03807040c01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 295858453 1250 295857203 295857223
    0xe090c040903022b080c03040507080613020109090b06160309120b01060f11030a18090c170f04020906060d091a01060e0915060304022209030f0f09060f05070204050103080d0e 77
    0x6510001c0d4941c48245421b980008100300c60303910503401c01060441c1c0402c0b80740d101d00e500d1200706c03800480d80e100040c001009540594119403d044200304a651208180c0701500d100c2c0c0c0341c2005031115420700315041038196201d4400601d070b0940744000d0041101045042c0c40c115100c1c0440c1000c844000c4942700350340e00c5481582e810a2050458203441201c0410306020b022521a410981300c45002080703039003084000e8040340781889581d1040f2295540950b0145c148000e0903200e19203900815140c810003017049100720000501502035614a40c040001180c200049802e44840c602e0345003e620801c0c000d940c0402c00d10f030b100500070301d0304c00b01080c4a043c55a1000c081250070106000340e607000a80200c1c1e11a035801a9964001c0c0201c000d400b140f10138160101c0c1034251b9042c09084040b400341080100042c80340394000881d0845203000c01c8966900e460501c640aa40d02207a440c09420f40095000d41000000800d2040b0040a044c603e681d208041201c0713a0281005681e5192041d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 295859703 1250 295858453 295858457
    0x610020d021c090305030408011d15010e13140f0106050f030307020409060b0d0c060f0525080f0d0603060c02070312120f0c0c0b0f100e090c040903022b 67
    0x1080300d0452a4020900324210ba642000c1146903100c1d034445007141c003e174020b9080d0380e40d13a06000300503500c1d51440b08079501400029040ea254264080c00424005010341220380c0c0c105c401081c0c40f4414683c1d00b144d101d42003040c0c07025080080c018281c4800030041d281c0119030a140f404200c600c0c040b01c0c04041100010300451400c001d070760034400645502c078019645a036487d5a440f915464581d042d10200e0b115001215070b140c2010703009090b0a8800794890100b080512206c80000354039032464840d07000d1000c1c40d000c440700d50715105000c0e10410001990000c000304202c141d806083c0c005100b6603104080512010000d104120b940300348070311024207050100d03074a2a0007103000d078641e03022140c821403010441c2c25001003100203031200d0004110000b10305280751401c1c404603104507900141d0b511481c00309410002c044029801c090300604910042280c0442c841000030480b9110030900a0000e0081400a060281d04c440464140788407501216106000c031900b0f0030800f1034421035036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 295860953 1250 295859703 295859713
    0x80901020c07060c0c05030a050a05012009040e070b040b0702040e15062107121a1b0a0302040302150c07120302030a03050402180406060609061407030e0d1a0610020d02 74
    0xc20000c45501c4c25040040d0f900d2041804045115181805002d031010700410041c1404500343c40c1643c03c441c41024512040000340c808403c0e1442c0100c11114035260449000c188091030036042418440507500c26801c10030300060001e5000042d4001d410070a00840f001c0260820110400d0303100d416a4070081070700714003400000d10514108e03440102c4c82d03c040d42d01000c241441d866580c43c00e0000c0d04000c04070225410800c00b000300341d0100007402d00f402a140551820b10340d42e41e00c02c1080d5004045411070011a044580c0752103541030300c00a5400a00aa0b660a08003c0300001948032a801c0600d41c000d40320003141c2c01c6e070b01c084206002e6a0540c003c51416520a03811001040d0280c01282d10910310320451255003140b0070a9130240d40a0403001544070710b801c8000d00586055400b42d07052091032004138041c41d06140a481e5483c0d05410400200621000011004055070700d0003021388001c210b14200d2281417615803445008159603090408a6120042c2d90741d14101d656400103a001b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 295862203 1250 295860953 295860959
    0xe090601030e0a05100f06090e07030803180303041211030304080708030a0204080d091e06170711030703090e01051c031d040f0506090f0f01090b030709090302030901080901020c07 79
    0x200354041000741102509840080100ba5100e5040585410b117030300c091a240c40b845401041588649001490310100420400f560107040b607440b0540c4d44006081c98202000007043e02001800d1400b401403020187d82d9a440c0a1900743d102d4102500b005c030004220a49202e102c040000031030f401150003400385410060039a6030b841c1141d10041150160613001d20001800c60000c01c04050460540d8a92100c020300b420721961100107596284c1355941c104000402407660085c00f504905260218540c0d411368074141e064504100e10382c140720151000040407000d060b4405184801d4480860680002d6640c0c5c2e420040c00701d90b084007140302020302c1d6904800080c026a0001da60220040400d030103d464900002c040f20464082801500d49170f03810042030b860404803207036006500c16031501690030700840407900c1c0101400348510301680c41503841110b54003000043d00900e45100c007804106400e00d0002d481c5d4100010701404a141440070a080300d40c10700a407203400e140310008001e1a41b0b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 295863309 1106 295862203 295862207
    0x14040b07020d170712021f02031b040b18030a3801080f060105040207050c011b020307140f101409040207020907020102120f070f080402011e090503010605010e090601 73
    0x83c1000000462240000c00c2c45103a12440040e02d0b5611042b19005102d000400c00022071408100080d1b65442040140200d2a40c403d0150b0905160402c0c5130b91000e0a8200408105003103610f40c00108000128803404141030003102d102124040192004807000e801a0100390418120703e0396010081000d1401040152011840c08016885660700c501e11000021304100c2c4440b40e041c0002c0300e6811082050f034004042d291825540c200b034008440c900c0100c940540c0e1481c100390742c01d103001441e42000c42c4443c0c580d400d030903241c0c4121001c5540803010f801e071311981c02c0c4601d60147e2a0004100e104001e02d800060f652080c4480900b8019001032440c1c010340b0060b41007100e1542e1003004189010f02c00c0c01c0c0348070151500d20060701c0d050a449015651113509818854900754851911011500190002c211454407507004444e042d81c0c41000c41d8001d40c0000114240d54 = true := by decide +kernel

theorem cover : BRFrame.Cov 295683453 295863309 := by
  have h0 := BRFrame.cov_init 295683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 295683453 ≤ n) (h2 : n < 295863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
