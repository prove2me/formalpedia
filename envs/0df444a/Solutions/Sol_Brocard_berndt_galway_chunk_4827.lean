-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4827
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:51:56.723973+00:00
-- url     : https://prove2.me/submissions/dc68f21c-f9e9-4f41-8a48-de18239e8f7b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 867985611 ≤ n < 868165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 867986861 1250 867985611 867985633
    0x807060306120201110a060501120c0504020901080a0b01020c0904051506010f090501080406020412121e0215090c0904080a0905010f02101d03040303021e07150513170c010908 77
    0x103042c003824540607043c450003001101c0d140406006024900350000300500695968260348180301c03540d40400d541d15514034201117007500d0540205c1e10050030596a100b02500c488200c040200f00440e842c83c1548a5024003400549800011714451401000a440340d1042030241c0b0414000051079a0304102e0308000700a46240c102d09101c0c1628020328109101c4d6441c0d10707080c0020700ca1604200115038411410404005022070b40742d84400d403030360300c03542c00122182c3c0d44100701a0b240a0240543c12106102c962075010000b5194031008910071151000da44502241031198141d500b42c814400000340c0c030084680140c0040b004000c00c2c40c1c005c0c804290044025101c4000c001c09543c89903c1d4482251008000402c0303091000d10001580d555503a2460301954a00420984c0a545004001800442200403888104030703403110074002103448805000312000d6100481900c046901d000c800304821540b501e2038925500014014100071800c0800900101e00700d038002c003025444a81094 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 867988111 1250 867986861 867986879
    0x203160c020904030c06180f120504050f09060f041b03141b0c010f020f1c0203040b130327062709020a02011b020102070c0e04020a050f180708010807060306 69
    0x16800f80d0586040d082c41e81840ca0000d000d008620150b8641d0070a05800364180080c2010030400c56209200141460310303084c2c0185c2d0030b801f582c410301d41e001c0002d5044d0015420403840d1154840d0001b092510b400d103140002608984032607010010b00c40c402110218032030b81620a00c205150b0000403074130070b071400440b003003800c86a9191811582901042d115003043e0250401c90000da4882c03419500c13203a4460030008036810030941404071809012010100f0f0707145200f01c80c080c9412006220542c1d0704da0140e2945481c00c004100c0c1084004100900140240c120b50b264600421040042480c903001009041e40e80440f143c5c0e035200141000304270200c21a48112046400604026032203090070982a80100080010700c80b00341810700c2d400401d0356040d40144080c6101e540d48008094403a41c05001c0e407001100c0007900303d100540c00b4402d41c5840341c40801c00711802401601d00204084e40d032004950240c400402080802c00103105400003401101d0240416240401480f45001880c07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 867989361 1250 867988111 867988129
    0x9100e06040e0a14010c0e04060b04031e1a0103060b040b280e090607032306091b07030215130203120c011407020a0213291c060203160c02 61
    0x160310031030b50354041480c40c000070b10848904507041400a070b092406150303654080c281007402100001c01c02602c01d0124075003441068141d440c2c0201c91350606003550344408082d280c00710a0040000014410800201910147e03c1e8501040125610b154914a0440c060300c0007507010a201e4bd017410711030802503c0320340c48404201a04000c80710032180c5804401070041c3d060300b01c52000303c80e80342005035103000025000d01841a80c0c2d410041403117030175013481050300c0da43d80091150724810085010380c0340000416401c807642106d908070440031843c038055268801c4104501503041410791400721112118925071103210408503404083c2c8645c00a41c0300d840c0c81c00d000078a000301181c8010741c0582540703e880c0181c042c98102c0b20a0906501c0650385524002d0101d2250442c89000d001c1003543e4011b0b03160300c02000e8864030014104814503c1140c44c068441a040382c44903421400c1080702560480b1054012040180d9030b0800d110701c207400031045c101d8003062118a20000005880b01c0042e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 867990611 1250 867989361 867989371
    0x7032d03201903020c010f0b03070605031003081c0222090209100809010e0303070207031718090405150709050a0e010b04050108040302010b030a1a070e0901060c020111030a0e09100e 80
    0x2d0302c002801d2200580c0203004140d2114029880c01d44410301551061b0b10400300540101c0c112040203507140c4080782d5512080f903260038424002d0358104001789a45000e405130400c1062a072801e0501e802c800d4049030481407040c1c03000c022403601c03080d4107010f00c403c1d1ba001d000708807400e600d0000100d02050000e0041135102302000749100004070903c1080d408502c0d014540000c0c3c0b40c2e00e080c25080259900010b00040e00c110403040d080c03400c3da820480c1100c01c1402100e004c04580080e010030010319003030061082d02c60b8000c041440100070b1150703840c0d40c0308022070307210a9243c604010900419590030b42007800c02d20754000051013608242d00603903040720400d18020b01140d072a454200e02400710900c3c2c00e5018440c1c43c2203081007241d514444240082507580100b02d0fa0380d41ea4007203501200300f20030035030003065180040c0b00d050700c1886902d001900604010481d052136901c001c3c5580c1c03210b003514000525600c403c84e901c0c501080016082454245404940c3c3c0c184026034003c41d6028003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 867991861 1250 867990611 867990637
    0xe0f0403140d0b06040801020a090b190f1b080d06061107090903090905150f1f0f02210405010905150d02130e0405060f091204090207032d0320 63
    0x100744038000683c0e00050b04141c0050322998a031a0794407112030103500300c81141d8001c200b00e804040f407400300803010b980e0501ca0030b10b406104401c903240305031030322801907000c0d0302000f02810a5204800983d455600712501c5036024079618046480544129006134012808102955440707242400f40001c40304103a50580d94006000c012514081d1000540c1d5800840388508004c10044009108003420005c08802d54101b03104039685410003e0012a01b102c03a1094650000700d00d420610500070380210042600413504100343d0003078050b0020102d120020303a0303c000060309024550780f21103c84010b09040e61044500040651071400c0d900504070202076142d4046a000c204040ca408014000c00055100401c0c0341400c0c244036803901c6080f504540f240e01e62002046801c43e002032000040c04107410501c0c03c040c01c146002010303500c004030503001c0009010030200c00a09103007540701c40401c0c9508004101080b08006020b956890a203440c030701e40c8440c0b10715890740b06d00c0100d8800c001242 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 867993111 1250 867991861 867991867
    0x71406160b090316030201020702240a08060301020c01020d09151b080402031e01020307350a23160306050a060f090e070314010504182d0c0e0f040314 66
    0x14820b807842c0541507640a4a0340d500c13040c841815019401403400034000d03100398110b0010305041e00d5101e090580c55031a071349020014044003a01c505517254000e50000c0000d4a08031b40301000a0aa800c0321000311481999481e000040040144800e0000c00c280b0340e0900c880c0303018090030118000484010014070104500140c2155000d22071600c038120032100440f44021803017110743c000e4104580311000318030340d40102c00c4a9281d00a000c07100c44030000c0b880011002050346039a0314240504034a07900c0d92564407109000443c0c80710315070b40110a2000d400c0da80341103040a8841d103000222401407524100d000c1c40141c8640346102c0c16209142449168681040f5084400b80072540c810185144840103000c60b55505800c4084402801c0f40460407d91321801040219505c01003072910f9a070f90103248070005882420b0a0f00312a0350080d04804080c0c3c1401d05070122180b4000171544d10000a1040c0034092000b10415000071490501c11458034040d900580884c45284101014072008 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 867994361 1250 867993111 867993121
    0x92a0c02100e030601060504060f09080705010e040b0628030207051903051909050103061a1e040e04030f030507020c0a050405191104061b031706010504090905071406160b 75
    0x203070240542c0c0d2480902224015139407090010038030340240c0158800a240207501c000e400d8440c03506c10b41501c1120300a46a450300c0d1500546442140c492129000707170b254984446103540780c101402802030000c20380390b0018800e1000c41c44109000b050f80c41030520500001c0f010450010391b2032005000d0721754404000e03010742030540c1c150003120450b06c11040d41c1545039101c2a40110200d04484082c1c809025254582c03081880b04032000d02c412900e401c0500c80f1900103003810360034880d800d0080304000d01c2d10751202c003c1c4512000448054000c510580d02d408001d540c5481026801841c61001c0e00700c1c4034445001075055070003407241900c11500c8202041c2009081c8401e59400646180e0801c440070038070801035000c2d0002e116150204201508840c016102c902d0075039800f17a8140d451103054ac4202e24450183c94005e03010307074100700c4240000700ba506804e20031200314500600c000e0941c186416142030407400c6100c00c0c98001c80090040101516500502d011145e6205c240540d00743d0316 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 867995611 1250 867994361 867994367
    0xa061104050f0a081c12020d14182d0f010203010515040302010f0e010909090f050607030209031c0302040308040b130f210519140f03090f060d0b0901092a0c0210 71
    0x68286941d1b5a58400504400015aa5030103103d10010303205100310940d959001c1c90400f069040d42d10f030702c2a00300f0b6002c0000c0a103580460807411a03034005009200d2107030601c070380c60010b8441100c403070b680d40000103120030315011921030b24503005000314600d4182103070b00081100d002e00301c00005209020a4180803603015a071940d0240401c602e08120614080c1004024088894002c2e0303480d000b41c6000c41d14051181c02200c44060f0041e0080c041800150488080d420070035030100c040540c05d00000c400503209034000c20013468961040c40d11580da8861414202c3c41550186000c540b00c90010004284114440b108a0b64641c00310501e01c04203042890a2200100d278110010602c0e030750110420030f0303403c40c10142c0e000c0d1804031002101c00148071a0303244590b42e512a80075a001418441902e0810002c20728480c0e61003001c00c080045034007082c3c0d402000e0704a09507503034896001c109103d142404003082001b6489003035002980c0001d024090703030007030503020f402001c1d0088a07041d5070340 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 867996861 1250 867995611 867995627
    0x314010506031b04020307031d01090b0603060609010303120f0c0906301802100305041401140f07120e0f120906071103240703051321020a061104050f0a081c 69
    0x2a1a000007c010809c03502900d000300b8801174200d8040300f00394007003070813810002001e512880d8060082c610340e03402c41e1001e0701c400003c40701c41200c090320350000710000c5a075802f8155101d803e607180d03441610709004010b13040036004010f074030b50302c00c40c05102982031a0300442c05440703c07001c06002070020f0340803140c0c030020726840001035000030b01d035444902107544c160b01280c4941d00030f0342c150100c1103034408240d083e038191001d014070444d50000420510f0015160242d0042450b05241501080e60b42444065414042501205411400704021405018041e125800c900d000c0428a0711500e0000202c1c14060000080c004036000b0710000c00d10345041250071505121728a0904030012142c00c00d8800c0b002c101e1705480080d0030440441d400c0c2030074a52195000d0703070003034907002c803400c1d101c40300144002071542c900e01f148180314000001c0b4000d442244408902815081c0d41d86081c4014040e259071003446060080c59106c0c410840301101140f074600c5801c07201807a4480d0701c0b8460044540c11 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 867998111 1250 867996861 867996881
    0x6061c06020c030a1106090703060c0c0516150f091206020705060424050f0f04030216240806011e0302070206190201060504110403020904020a0306060314010506031b0402030703 78
    0x1480000c102007a030400201620406240c1c0e17848003081c142c0360a810b6240e0704c0603100900c15034031504040c0700144060704010005201464005800800341d25100c3c07901c008800c034000078180552040c00601d0b5a21a911180c2080d0b0800d40e100003405c640c000c00610003071181c00c49072440400d064041008a404903500309070410200c8031a801c3c28242000840f0503490b51130340851416840809101c0c240c003c0318450132103141603082d190380329480e0400d900f82c02403084045006041c1004280d060892140001e040b084210801440461a50310110b09640315010107025900040040a81c0c1c4040c40c50110300c14034050003103105203001d081d40031340910340c0001e521000c08223200420101c000c05020a96a10303034001d0001c650f0342c009200c00c0764405100b00f070540307408000610260406403249070300f042c4040c01d8119103640e00e071582c00c05c4940c80d400c1261054109041200444c03003d0040a4000c0d0f0114003901d0070311030307600c500c1e048603140d680c10301e002c0d5802000040f8407500941c8560006 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 867999361 1250 867998111 867998123
    0xc130b0c0703060c0206010f090902090a200d0b0f09060312070c0e0c0a031a1c0c080a0b0403020d020c0105030a050a021612030609140a0207050f030c0703030e011106061c 75
    0x1d410a83d0019403210130901603050485000b04000400400342d01581014ae6005801e00c03030640c440c0d10302000501900d0004818825401c0e000c50b1580c04140000d1091004003000025001c0e00d140c10440311500d90030880b4442e20104050000f90390700440c0d00c1341c00c01503840e000741c1e41c0c0038203140c01c8001c00c1c0c15034020000e000040d402c0049007082c40b4002c01700c200d5241e604000b28074000034849585100c07042c810b83c1002d0321b9840c4800c0c01c180194560025070140b2850440f455440000910780000110111414855003051204040d010041202100410b0005c3c20104180c400028110f000c01000f100c603d5440d900442e81c081e90641c12120458401414484100000d050094040c4040600c450009280c810009420300080c0300700140400c41041c03030b04003500c0d1140010302940001c00123443da402010140e440710f450420040405941e0a00a0580e2504d1760801408103012810540d050005142d401008280b02043c11070340040c0c119180c00102001c210061081c2f41c00c0d0030000d01d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 868000611 1250 867999361 867999371
    0x616050a0c0f030507030f08090703110121020409060b0c0a08070609020306070c110a1805093d0c0806040915151e05220212070503060301050c130b0c070306 69
    0xf4564880010850385020391120900d01410003c01c0303818410440b2051200c0c3c209517010f100061a408034400d040505160002d40809101d441030b005d2031824101e21005640014104520f48150003210000d010340500e2604202c0c902e450340b51250f54080008001000000703841081003000d40c8106032403a00902118203a1809060182c021110f880082d00d0200706e0081424952901114170000d032038541d80800c500c440c1080e0f0316005481301401d245c006006040490700000c0b85560043c02d01e1291605080c107120154030b0400b40c0d009617103a03c0030605c1c10240a180402c0e0003c03241c0b5000f4000f580c0c0083d5007285401c011014281433060001c0c82c60410340080a00015081c480c0242c9a032400c0c0000084644070300039001c0f40c0c040c4a52600110322800c0803504a156140001c01e01150003809440d1201414900a0041c002c0b140c03036001c100c020091000364202480b400344e000c1d0720402d03490300d068011000406500b24911070b05180140000d080c03020a2801d000d100019070348800140b00b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 868001861 1250 868000611 868000613
    0xf0a1407080c16170c06031005090c0a030b0114090618030133290403062a1403010b090409150e120a0f0f0c020904060b120616050a0c0f 60
    0x740b601058207003d84100c0a181000c15102141550442580060307030052500c074103040140415a00018041e40d003003150320000082513107600e90000e11407200b003608182e5410700208081c04a84024020b10f0400105100795a035046008044443d1040b00712612610394030176142160b031602c4118441c5170507508003000180b0510104004d00410803a80c003000c020403042c14107200740d014540c420079000210103804400481400d2141070000b1103a500700d280342680340e84502081e83c0b040034884034103036809421840025031850301030500102c3c0d0b180103582c0c40305000c1d006102d400103000749210000000744480c2c482e940c81d03101304c04040d404a40d41c00c0d6020391340c002500800d0342d0303440518140600303110304140a10500c200d44240ca01c130f85503070702c100100083c221002e140c95000c0c0828059000f4104015a4034044980e101d00c1c840d0b00e01103500d241c5541800700c1d0043c0c501c13203140c0715030142040c41068085030202c2002c0d900540f03411a00d50030194000ca0f40889240c40191600c1500c103100c070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 868003111 1250 868001861 868001863
    0x5040f15033e040203100308030f0403111f0506010e0409060e06061009060f09050409230a020a0e0a060f03111008060f2809020c0c0301020f0a1407080c 67
    0x446402c00160084000c8002200300d1040c991440440c8911081e480340703040300600e030960195410600b0040b072525410b0f1a90b54644080e4000eaa80d0a002c513503400400c02010703842200c102c4c1040101010304080c01080443e400c0c1c4000002d64200e41d0f035110800100076912030100c0f0080403034001c3c4184004940c508202d030003091000b074145024000d0100140160400c00c610146503e065503c0c41240b500d0414203c0e0781040004d055010041d500c20300181580d01c82c000c848106000ba071941045001400c5218500f055804200c2c020b0380055031320300d0159660b008204100c0b10311198120569807130003c2c180040800d90480c241c0e0419020010042c4105d4400c04414114161050795201e441080283c60031481203500e00d0b03004004144020003410405828003d07140180c5035150050b051143c11000310711190409108164041501c5814034810411080980d1064008601e49180f142182e121481251a03c2061000c480c41d51003408218030308030f071002a00421080d80f181041521b207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 868004361 1250 868003111 868003133
    0x1092d0308151e03010c14030c031003170a030c0908030d0b0310091a060d0b0a0c0c05030c0f0c0604030309060f050418020405010806041104091a10051c060602030405040f1503 77
    0x880c2c06580303440c02201b580742c02024503105008102e455030b0304503030300c18485140d640c0c002031841c00c25183d621000400103c00840044408444108154540700903901c0141111030303e00c028010072420300c108002c440303008012500300070100e100200300e0110190100346400c1c941c0c040800034034904140d00d024850400740404802045030f0b0910138a07207620003003003404031000e03001900c1710004e000401c04c204003030b60080c0b441da81d60742070404000720300d174807030f41d0864010711200d002e81d0300030700405c040841052108507220b4504440550406003943c80040820030240101001d010b04e034294048064010003d5070014610340e0095056151903010100c0a50494464240480d01040226003c2e2409000d0705510404500100e420640740030b114001601d0920035011403000e17580740b404842d445c1e07030114154010040c1c460950355000c00000340f00f0549071103041c511552800c9000d10138030340c2c040101d604403101205c01140c2070380d0482a810042285800c0740b025007245a0740001041503841d25 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 868005611 1250 868004361 868004419
    0x406020a122d0c06060b040603060e0c18030a0615060311073503010b07110a030c0e270a1b030f020904050a0503070501092d030815 58
    0x528070a1400910a55580d04441c146865818100705140381030008082855020a41481e0400ea0240252610011030345107400008006400141c00e00000350513000d460300510180b5181d403050305d4070000d4220140107160451003010414500c05516980c10019489215085481044030380d0340001d820842c0042841900d01181c100000552001c03030580070b0b41c1d411a0401f192007111442c20414000001105d4140422407050485000810007424040c50207009910401c56076802c039400c1c910408a003c1345802d108101c3c0040900021b891a240002124092041004d043c0c941040d92444036207161080801600c40381c0200040303180c0080d0030501540114000d042c51012040665800c0941d400050003100354009240700600340b451340e040d40140a02c0c15240c501132540c0c2e03410300790f51000d03605943c141c2d1564400000d00820710320847c10041400440c140007000c18001105507684200c000c0e00303121801c00040e52250810031807519290005100c442440020200b45051642c2280 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 868006861 1250 868005611 868005623
    0x30302060c09030a060e0118050102040305010b040b1305090a0b07020d0e190b0f07020904030503101211010e0a08010509070617220f020924090103111003110406020a 73
    0x1000c01d941c61103050844125a0002c2c0141c0950b40140d120580504810003986110350741e241e4440c42e010010310003034040380d4420310000d40c1d1545141441c3d030030754180d412507910441c41d1825010407940c80c9064200001e565000c0440e0319921a0103040c1007031014200607029181517070421017038950100b040840340740551503c49520980c4424440407248445441d00b041c1a240390901049000c030001c0c0014511b00f40c01580f0b808015408a00030010984040380882c101000b8080002146180c00d40604503c4000c50f0f003e04a548a0603090a00b128441d8184010008880c026449000c1b0000191603243d000303002ca82455984c082d501e4200d485604006001c410a0700a0a50be00e5801c0e80070b121035800300054070060554a40e40b400c840d080850f000c040c584404001600c4000c840da00c11046200040152041281d032a08200880301200d0311582c408401407001410260041c0041c05042e9141c0c00707960003048090340100103880700381000d004045400170304151f0000e181880148540 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 868008111 1250 868006861 868006873
    0x20d060b061309052518080a030915113a050d0c02070f14120607050904060503060f011a1303120201062108071509050a06060614040e0402180c04030302 67
    0x520b8140000201c613018580982800c90442c201034810401c1c10201d02c4001b00c020481903507602c0e150303e0518229401c0f0007003403450b10100803100403180150a200241d0420150001c240d07500d40b030f111140308484440c0d410481c056103a0100b040c048000e905c4501494001c6104003420016200c1c1e0005c500318040d080c00e1074101e80c105840031450008492881881d4540103080c00004864101900d40c49a0441030184d400b800c80e250810071280130344a0303600c2e9541e40d40c000380140402d4542e207800c0f0a00a07072116003400240000041d950341100c0fa22070180c00c51685c00031a50305c551003155035100c00c2811400012007803100c401c0300400382102e10740080100c80c0da1403114107041140c404985403804040080341e0f0114012500a0242511400010300d1648048448504441c4102e6080c1d95aa204105140812806103d010041c0a250805820300d1043d004001200d228038014260745c05080c6021404644170340140004c16a548040c0c084540350180f00c00b0202e4029220070380c010300c510 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 868009361 1250 868008111 868008121
    0x307120e011509061d04210c020a120b0f0a0b0301023403050706021804060e1905090a0201050f071e05150708040210020c06030702010c090e13020d060b06130905 71
    0x9204e1601215043c99149400d241032110112130b4120050040e5a0901c10803c100c0c0340b10020002d00c0d410302000c0c0c84201c0c006005005000c110482508400e030141c4032a100d0001007243c009486074081c1c072380700d0510180d6031207080c010041d000040c04103070998000b0131401b00911415540c1030850300360840716299201d01101e10844000c0f2200d003c1c02040c0100106004214240c000b000308418041201da1070039802c4001c00c0c1110141e92040002e42c00c1c02e002e02451850141810b1a0010210700c140803508049004544444800300024140640020300360310158a81c03080e6034520782c11883c800f60390105030452900740e442242044030b072401403400901c440000182424000c084540e00c0050642d6190300b13000b1602a86407141c820351258801c0d0307100660b122070007584940034603030001c03810230640358010303012000e503402202c05810302108001403400300d8100019842d0301207a0603c0034000e907007031420051a407100a030741c0200000801000c9000014000300c101c4e8000f171002c2000b5920 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 868010611 1250 868009361 868009379
    0x90b1306030f06030b06010503041e060519061a072901030201021606020601031103101d0f060121080d02070627030804150617060601081012080307120e0115 69
    0x101d130200a10f000c58510208a041d44144055a0310034030969400031001c0704d00c1920710700b000d403198046a00a441e48104050640080180b118003142407500340f103050701b0000d0145080f20841c02581022002240c030b80c0c24404000c40c412098021079000100c400400c00d1b100301c031600c0034041a409445a00351100046003c000c07400100e501c6580503043c16401e5070b032000c81c51860008402d07810f120340424003c4801092040480381440e880c2c4622000c21710101d02c500740024002a40c42d11f0304600010040000054442c44420b141c6035030100401c1c02c01d180201c524048c03500d0381c0e1105840030540c1c1c0100f1495503c20074060b0515118410035101c0c0031042c007400ba030032610080029079828089000203103070340c81d6443c50410002c0301141050701c1d404460301e050304405140c2030552004090000650300300f800190070091246015144600f402c54440c10441045001000c00800000003460244500d400c2d20301071029003c2030058102651034203018100c028403003001580c84900005094130 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 868011861 1250 868010611 868010621
    0x1c0b15010f081b0f0712090f090e1e030c0610030312020a0c0303110408010c050414060403020102190501140103030f0e01020d020d031113030f05070b160f03090b1306030f 75
    0xc030b44200429044a4650b010785036410440c0c00d01c0c225102400f82d44001080010342d4541e100983d075034171007401c0c07034230761070f50b441802d1030380300303000c0b091604001c078040e040046409031501d5040d003240c86511741844226451480389500707502d002e00541042c041c04446e520391050840f8069501c88090103000c55124040380705900c580e0340801c0000c0c10741c00c000780c020f400205c4100e01c481d0000c0d04042d0707174683c4c09003951110a01140018400101032082c0c000c02c584611340003200740c46050030181160300103940d41e9010304190b0f90f5103c10b200502c04010b025004052040703170000d80880c03596501d00d0042e01700703500e0341601804114110018001944000b55421074641d095001b041403002c401400d40081542e00030b07444480d082007094210f1807001c610320030000c601c51401842548101d04200703007408420303081390449010801c10056055030703e040b802070498000120f017804e4100b0b4a0143c40443e9133030700420940c100420503a496182c103a8070241200c9441e2024000c1080d003002c0001164 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 868013111 1250 868011861 868011871
    0x1d1005150717040b190f091e0810021c06030515100302030304090506120a020303090112020c03070503070b010f0e06220504151d0d180b132309061c0b15010f08 70
    0x110407047c01c100144a000c9400740e002c0004644956564480c41c3d4981400d02c05181f540c442600024040310318000704441440c0b005640c08100031031401c640c1c80e5600c6444149040801403040808a06c542c07580c43d08031001107034011300f1256100c1d615240c02015007022140e1501c00c80510290085464020994080c00c0782d0080245141071400300054810761f01003031038850065400e120700540813404000070401c81d40150010341e103c542c946007a0528a40c1604294260100d8500c10016100c20013480c036044007044074810003440048200c404172007450003a103118542000d09200c244005140e440745040c511160a002c0d843c9600d04441418001030450401640041e25050301c891266000c2031000030760f40d4078040e50702e0751a00d070512140c10405c02d02c10820202441000160011401c1000007181600c07071a1004001c0300c002564030740020074480c01400c40c524001c040c5105840b5403c80b4a80c0102c150640f803c0041213006801820201607000c01c0f00a100954454011420380d8032031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 868014361 1250 868013111 868013117
    0x80604141b04031707050f16060507080c100617030f16020f09010b0d060f03150c091802070c0806090a030f0e0a1d1005150717040b190f 60
    0x19110120720101d104580030340c0c160010350900000c0001001245110b410964840c51241c41e8009401c21a051591009a0308100d80c003030114031040c44280101d450032107109007040c070348038415401d0049043c8580a0070402074012040103180010640d030000d001c2d0343c8920520440310a80200041d0369200e141002c1c601341c1c2080c001c3c071400c100112000035030b0310720280c02030151000402c04030b441c1c0d420a070000103400f040030480f481c0789240707445900014810040001344031803458035100c02c0303a02c904800003c1c1e0303500c80181d04415030098030044010300f0101403962080d041c2d09910f4009400031501201d0001ca00d250000d401d503c0011703064003a030b451030082c201c41740c9a03a50030740b010441b500e8003605000f0301d501008c200383c5d1203003400c2008000d100c0c0c8803800d0728242100190940703001849003400031840b40041c03144d03840b061031202002580ba4905a515203050520ba142460340c2e00385074401d4140010040307104911100609003103141001d1120b121040b150b019502e00c007091000c6000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 868015611 1250 868014361 868014401
    0x1c06090b1806030a080f0d0506040504020d0f03090f150201060e0c03270a1406340e1306051005040312050901110a060516020a05060f04080c0604030201050601080604 73
    0x1215080d103400c80c2d0491802011180010305035601c0580c640c02503118011a40c001213203c1101d40303084d005640c2d06c41c0c0e00302e40400c900d02c0c1960000c0c07402117400310043d01e46003c07141da00c000c1500500d152030140110012103802c00d5a2424103003407012480840e50f005508100c03001a001c0340c0f0011b050700603803817000342034296a5040c0c26403c1e042100751403c01109031142c1c25081890040c412048100c0c00350101103142d24070f10f20b0551502074040c080941c00d5400410303855030100c0d40c0440c840c241655014011841703040f0a421641c00040042e1030340d010181d08d5260700803140c81d5022408a44055608208200301d00d207003520300340654030001d081d1000c08020310b1000c07803007071000b4000c1200504105201c0c081d42265686031003a07034a411102c0690790410710008481c0c0c17180b94100d14a8510091000d40500d549183d01c9140113131101c810108c5050204041020040035644410003030b004440d43d40c41c0c43d043c02030103800c0c03c0d242c20b40828625004208141001e0089515290025110043c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 868016861 1250 868015611 868015639
    0x603050303340509130204300f0201110c030601091d06070207091e0e07080c0f012a02030d0203030a1109060909040303060b0403150509060f010b0705010f021c06090b 73
    0x70303a5034003c4c2a0260710049058080c0740c06241440500060704800c0e442412104942c0c0079150708004100f1400074082880036500b000401004040e0405135080c80c1000a040200041c20300c0c00302102c0c48254580245000070542d50f401c0e44c8103400403004500325008401c41d52a5040e00c0300301c00d80d510310043c1c000050a1182440941040700d00340704100507410803800b40200c0d001240e6141c1b00c2c0310381603000854100b140000800c52580b400c403088621040e103058403000a00240101c200d82984014184458810160581503444006401509071108007642101c0203490741e100320344d860001ea00d4240c4805803d04500c0540307051607805007000d484c001c10002084120748005100f1820552540800303d43c00050b0310103000194450b0050741080120f0440c2e080585400078002c50031a4851402c00076000075501410b4119103179030941d9940c0d020282080c6015100340301e00a40e1f202d000280b0307200e0314000103403020003c1d1140d8108000c0b05440d00c040c9015680d0b0030000300e602111b002207440c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 868018111 1250 868016861 868016867
    0x110906090c071506080a020916230706140403030c14070b092d060f1017010f020301060c2f010e06041d01031415041401020d060305030334 61
    0x842809032035020300403a0008045402c0d2401900000069000306c0c000c18210700b802d10700b20707401100d013000070880301d400a000200442d02e840c5091a44200d0140d191001c00040d404903014039070480d106208400091822045101041c2c800301d000a10705962030b23400510402401030024419940fa914000190302c3d0081c102c0c1018000c80000d00070307690300d003042500c4d011030b4420040d00c04158052040083c5031a41c1042d400030124a4001045c00400070a00700380c1c60300e00301384c95483c1d0035084081c050154081c0180031f5601d201e9a514800030011030000c1e040b000e00141c80b071081c0625a24802c00303400300d0100a03050040c200e408400f032000d001c210740c011050209841070240059051507529803801101c0a0b080d15642da0090001c1c00620900c0141c070402e1070f001d00031701c000380f000502d840810b50301c00000030009008a0006404044070403803e40450700188051501404650740741e04280b61260b106030380e4286d0002102d0712000040019003201040303084000b40c255406601c0481c10303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 868019361 1250 868018111 868018117
    0x60f041d090a060c1701090509011a0d17160506060f04021306030b01120f02040503010e0d0f0309020f090a0b010e0f0a14190902190e1018180207110906090c 69
    0x403020700c042151880098640c82c5c1c007482c0201101000400c0a042c510480c508503030400000002c120f000c20003902450b00c40d400120340e0030740c0c80701d10048088000303c5070040fa805940c42d202d401c0569038003820184a00007032a2805284c00b00e545941c01a941c90030001248102ca95a105090020b2410070030385019a000e084450030604054a82d11580390064084810b18050113449a6020505100d6401c09120752030208111800070a030042a40f5006000086a0100001050b8450059900710b4503000300c1048481005030640080d420215080d80180208884103400105079085000940c50b2858000c0514000540903102050a01082c40c0702d1050341400950800c0401d11494ac6942030071842100900b0540780050719411000c607040d104004400c000750030842469506200d40e03035070003007403c21000d4904298801d185407148180300200d43c2e80c4a80c0382d000e2000701403800d003016600101055481025810044580e010030481e07034030400d645140c0c1021240000688a02d096002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 868020611 1250 868019361 868019381
    0x280c02130905012c1902060f030a0f0c02011b030203010b0f07050a1202060708130b060409021207290a090e0a09170406020609150601031505060f041d090a06 69
    0x115422102c1100050700d0700e14036003c000090459065040404024413017a4004080f40352592042410358001980a0040500551103010b0000200c0e003500c0349940300c21260081c4a030103103c25148803001074000c0c107254400310b00007107800c05100585803003403085078141c40c41c225106040181e1400a101e20b600407020813607203071040d070765007030301141d40682d119030161902d0380148030a103402407005000600241100c1c03401810482003038002081c1c480d10b02d030300070001c0d40e0004e044110b45c00080c0c01115594400030042c0240e82022a1404050071a0300a842c403e4104007600d501c20405010310384035810480c4001b954070340303040c810702d02071207a41c0d6044000300d10040f6080da900d03291741405051810405187c081c0020701044100d80501150b980090a038024204840c0403c50b42d914030b08c0000c04540c10980e03100001131990340607003034040c09003201620840d11601022246000c41d446070050390600980b0220f00603072110b9494542d84208000006044e00000e0f1707540c0e000113880e860300d03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 868021861 1250 868020611 868020613
    0x12020d021e1609050717090a030c030e090405011d070f060302070305190f0f0305071d060d05010e0603010e0a1e0609020904060b0a060908071701020f280c02130905 72
    0x40b1688641c5590840300003900580000040c10308010801411000700d42c940c0040b03d00c1068200700801c480410103c881907054107250880d00e0302c47c5000c80c0c041c90040b01c803030fa002c0081410702c0284001580419603000040010b40852440300071000c0c3e45104611403c0020704804100340542c0e0300c2a009800ea080c405d050070f604181550490103004a03c1324031074800a0140c0040d106210381c4909907641030040341c00c040041d81403c54005107940d0b61002509500c0a9075000004070342c5601d4111240590090810800c65844040f400152007050f1101c1d4406d60900e50b221003441400724801752621b0780b004e652030450125141c055400c48054a0030780d42569240d14100250b10307484400c600c140d2143c180001c03200c103690100300c0080d5298110104102e1524418051803030005a10b0707080da10340c0d00803c1da40000200c0c29501a218102c03001060020118802294007451040c0000e2900038804044003010200c90407515506048006903001420a80c1e201c1ca81c9042d5007e0a4028000c0b0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 868023111 1250 868021861 868021873
    0x1d1e01201b0f0a1110030519092d0c0e071d01020c0405090c120705151c0c0c030815210115170601080a0201020c01120612080712020d021e 61
    0x80ca40b00c3c1050358009040d201c840290181100034501005c1000b0b1080c0c081c142004207050000f03440f02c1c0c15140488213050295140d0341c0b04240808030740c1c0300180a40180700070450f20904a10b41d001c40c08581d004950a6074150380c0425003c0000140794485c00d19070380e174551100c1d01019980c81c0c42000c004014154065404c0a01490715a1300030076110f00a440010310b40401d5510038020001056a2808002d402082c81800503070707900b05040345203040344102c07a500c601d99010350803210b40d600418a000280b410303520551564100f071003100c40a0180d2240d8400d65198142e000e0f01c040c107400403d42c4213141c0b01d18007599078820410b4100c2c489035000005803001d086881c0503c0c6841640048983c1c980c0301c000c200d00f47d041000901e024100d01000390055000341c3e80081e5840c0118545a030600250b40050038071500e4650200d40100180f0340c90b114000107e0900026680c4146000e0791801e205041402d42140000b83c51414051554000c00c14220f505904441007142010b414071140903031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 868024361 1250 868023111 868023133
    0x31f03060204060e010f170606090a050402030405010902090705040f050907050c061821040509090f071517090709020a03200c01060503060c0d1d1e01201b 68
    0x103403014101030000d0341c48071242180d40b0800501b040100803090750402c00d581100000280880314100c2d004042968000c0c4c5a6080000007403107640c41e60800c5070003620100070001440030542209120b1030096442000507151101f040f00e80e44160302510710750041015003000035080031643c1d55440440b82c076055041c4500501c1403030810303005580c807812252800c1c03050003501005100050499552282c4d11400c0c1d0680e070076403c0c10380a10322449203e40c46020004800c140705008502050501c501540c0c041a25a207005102c2c655800740a00041d2089860340c00c11010383c99003600442061008026684ca010401400307580443c1d000c40400d0303100e008540050030b0f407080d607040782684401040c0c1c0300c92100c08802d00311581d030f034486886540920244040e104450048460a0911000c003080f107010103595062000e2000c0c058400d41d00c900e18601c2c0b09049051302d0700401c444108001d0245150b02d10044000e0071203000324601c0b5000400440f0240f040c501465840750b0021800d88902c5421 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 868025611 1250 868024361 868024373
    0x1c080306150f030f0f0a150e04030203130f09050610020a020d051006030302071a03070f0c020406031a0406060509010b090f030717060703050a110708071703090a030306080d05031f03 80
    0x700703950403022084c22800b40130142c1c40308a0215409500d14004014000c0c0c0800c540055408520a82680c80da00001240c1814400e0003201c00c40b5005451440000c0da50b40315210415100e80300340c074102d603e0100810320b05d141081c0c803510007007550340c01000485000d070204801c0f600c0380d00e4110f07010300c2000342500350000580103140042d8080d8014020b0f80d460211040044400100d21450300b0400700204a0b62a80000c21210005007605e0001002086440440e0003450150030107886803007070350b032408546a0707d90500361095208042c18864155030300c00b0300000754401c1c010303c3e000500a01c101095810120720840288a0040841e122242c2e9894012580c130030b00000b0b1901600221304009445425004807034019070480000c0040050744540d0000c24011198005d211944c0081e505041c4168004261444c0b0f080b00d003026a01d00701010b51940e514001c01e422008241000c100055020700400e44440c5043c00351107040c03841d942d80c140b21100110020010103501180c0f6008004a01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 868026861 1250 868025611 868025617
    0x1150c061b020f0309091614030f060f1002060c0d020d0501080d0f081303080a021b0f0f0601030b0a050405100207050d081501020703030f0c0f0c03021c080306150f 72
    0x51030301c44400219024250082c1400420f031000140c6900801803c1c06030748400054a0f4402d1200740e0120025503450400c68052070042024941014040f003032183d40d08011042c14007584044852a4403010300c901800b0080e036001c9803010242e007100c4006480251040c00900c4500d030000001450100c1c0355000c802240c0c400e070010a515448078910554640c1c000120210018143c2007550051030040504558606a020010300f00141440864010001d540644200700b80115095103081e000110907696101e120641d20308510540c1708045031483d010036940c2c10382e0f400c14600c444d11703514001c170030f0050036002c1e0041703030b8601c82e800703a90003945180e00c00742c1380c0e45126601400c450203462600500c080380241001c1c1c0c00f032407980d151a10070780e00000d00000b1a540340c03c1c2554011501c11040d0707003008034494040d0104030f0402e11201000582054101030301d208854519542c10424a0640c410b64441002440f00720b0420100d5414501241c1140215003c1122039107004510170707c03010f00d90 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 868028111 1250 868026861 868026881
    0x120603060203040501091b0f140a030b071116060c020f150703031b09051309050c100810060c05030f0313080d051801051009150e010f06020d0e010801150c06 69
    0x203507541b04c26204000a12089009403440403080ca01168148030a900b44c2d514035125280400e003a030b0000b2005501c0d2007581000035500488001042e1134841000381c0b01c107180080d413032058000c134441110000c1a07035003100d0640340c0d00d51352044541655030038000c0d40050341c1c074090340c4480c0201242d0410080c01d0001c1104a11a40d0041180400f580070401c41c21002d521010602011910900007500c441170f5501d11ba80300200f0204005503241406814581e00351855a0014040440d0400c5580c01056850103a07041c00c0b054500300f9a06c9608803001504000020702c19002003000002d4090601d01840d0410b1600702c0d62464120b80c0e80e100840d65001c5000c03c809240c03540308005440300d964110703a42100808009011601e0003005003416079540b4080c1170345484e6140d13200e04410318800030840c05003401036011180c5584511340c0c0e0f261081284152401031050150801e4002d200c1c4041e03e00100043e1102c00b0a6401c150480100400046c0490704020320842d402c030105003c0d004007202c04c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 868029361 1250 868028111 868028113
    0x32704090b10090b012105150a0b071416031211010203010f090e07032609120f0f0d17090309181506030408030105040c18080714011e1206030602030405 67
    0x40c0c40c101840d0160382c0290600b43c14080070a51012018078a0905240c0311a8920340021f495607800e07894080c50701c1d0500d15a07402038900d40e070100c2c0412041000381040d50003010a250184903800005031358040140a5030300d030300202c0c0d20400015002d8000d203150340f45541801d45000590382a5242281c100741d109101c001c0d0038890401c5400b104d0301c100300544010101820b2268110b44a030012811a50009104601c030b2000c0c0ca01c40649040075a04401e90080481490348004c0005a1356a008034242d51170301d00451460080c0c1c4400010002001034068645851004c40641e4102064000a0603046a400200001882c80d5500d40030100382e80d5200060b070340300381840c84540b840c540180044c18014081042404040ad81001c2905d0454000b01e40201f1100510402100c12101c604141601a0300c0c82d1408150000c0c0818102c00b900d0072102e400c03010440d0500110f07490030700d01401c0e111f10b01242808050040c4180c3d003180e95056a00404030b80103a1305e81c0e901b400c90307004540941e12 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 868030611 1250 868029361 868029391
    0xa030b1504060602031206060a0903020312070b060117040f0303090b0a06030b130201020c120a1704090f020a05191e090e090a080a1d100509010201050603032704090b 73
    0x46107014410000030b0301440c4000c6003030030005204030f41168005040a8880c200100d03114212030311600459001d141d02800b602c0300b0100203200d1080c5038003c0c0078110b9070b20895000246495219142200401030400e15804c5140c641d91070302500d602004805508140e292403042000c40c8c216102c4500a09000400151107840e504111240900c0036003107105003031b10010b1103400340c0c0e40060421a0488100c50800392440c003401c0c614900b5411a0000345410380d03e180c0d18800c0080b07803019000b240c0c8070b83d00a00c103076802041004101d1040142072404200f06102c1c00b0b04019000e08040d0740441d042c00c0ca95032288000242151900c102200540041c030110402d2001824250526402485a90060440c88075907542c162085c06082100001c000742081240070124083c1194480c03c10b01401c40f03020552241c10003482d40c5d00081d500ca02560a24020440c1070034000700310b61080781d219140c0040000280d490343c8405100141e06d6600c5521040c0c4d6401003040d5035100c0c0c1c010541403099180c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 868031861 1250 868030611 868030651
    0xf041a01120308060a181a100f0206060a0614030a06091802030f0c03060403140f0a030905061302030d0c0312021306020d030e0304060c1b030503031b0310050f0a030b 73
    0x9000044c0040d0242040c02402c004104486030141c00351854200080303400035800341150030408085d10266032050819010440c1310f6045440400c43c07810300d5094a450b0368604040c40780c0400ea030b104000000c0c035995450000003851002450b0000005000400c0c6103548035400c0c07040d102181311400b075952000c4c14050451034200500e100c03c060840152072607204500002e502c84130000c002400303201c3c03540d0000f05110200c031704860300c400c014000c140c1ca4031000c2000030010081c0e103e003180c0c188030703a60110780c1c03480c40c800501d504140c2c000c00030007001d590b0740b5041b940d40120300c0c0200c05011020900b104400000c0c000752400c0c1c82e441d0141c0386c040d2704c0d01000a01d400a40c07201001458540705000420f01d502004131001d541c82403d18190041203403500005c124042400200c85503503000d400300c06c0000c044004c60140c1686031201e410500801c040182a10044c4c1d0038401e00c032451902008a424a810480400e100c010300c014043d85d40ca07155801070401c100d40c0840c65117900f010880c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 868033111 1250 868031861 868031867
    0x1e040f1b09020903010c02060c070803061f030614041811030a0204020301090902150304030e10120e0d020706210504031e0206041b060e09062d04061a030f041a011203 73
    0x40c546c030301a80f004120781d082049400c01d8074410786038060100c02c40040000c480e5110100290681c0408280300090070021260041c0144128002d20180f40c030303000d103100c10703a150600400e4000c0d007982600d019800d4041e0b603a411b0720203010a68a41500406043d80003503a04c510107503009000160011490724800c0c4100300c110783d4811007100e10013005200340310100b9032014851045540c248c0c0e00e50f480c08003452054558070003189211841c0c038140700790100c481c40089104500c040d40307502107801c0d058a9407810f40311491100d8417a0292612407081c044807103440d07005031f50840e0090800001c140c041d010a0403080302c0025900300984c0c00182400100120204c038800420603801c14080d14509100c0024900407d99941e00e200b1380341d034008038011b07503030340700c20441c4441d4183c00e0201044080b0440d01e4000150003044d9101d14500300001840704492154000c0c00f2409506442c615500c640026048560113401511401081c0d501d4080c1c2c15440d4641c140a03082005011450044d245402 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 868034361 1250 868033111 868033121
    0x2b0318080d08040b0408070204020a030b030d1110150b0f0414060304080a08040219120317040b0601050f07021512091606031802040c0906081e040f1b0902090301 71
    0x565140c1c031030329004201507071002155400c5584000b450080f81c4903810541c9450280ea40301039482407000482800c082e8050f403010710002d10980990b65412004171023603841c4408401100400d400698002e0000c40d51540700034010450b200720780401d20b46500150090fa00a019285050100010140002603070320b5908280d11a084039500c3c598a855512124503000350340252040c4900500880d0456030b81c104420107045806081018141d9501e02d80300401076402c01c00e83c0420003ca004070700c1d0205107850310b44503507000121603039107071a15001100c140d4012141c6e101041001c0c441b49005903613641081101c00442860380d5299042d031000e6050b0a40c0107419400c3c2c0b0340c0040d4501035094050b2080e4000c81c2d515050000c1c48070181c1102c0220480742c99002940103291001e585500c5030025041d40a4650b103a8440b0069521113002e481000d40f4460074400303000c412000580040e44180b00d03032070303900d20a03443c1c02c4a0f02d003030100c0c1003c080c003150001c030b0725079070041060341c0181001d06c14 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 868035611 1250 868034361 868034369
    0xb0117010207051e0c04110a17060901031b1805060111030a2f011409060f07020c3f0d0c0c0e040507050325090603030503062b0318 58
    0x8601d042e5141d0703203140d600c0d02c2809500010f210b422011018415041c40017184510300580207009000d03000441d014207a01907400240480c1e51040c1e000302d41c6016042070781c0300e0307500540262134990860300c1d0f188103101d0f02c0480c20520341030603070003040040304075000c8091080d10000120341c0341056400501036106894164419900c14407201034030075031040c507855200b1a900c0025210302d10000c9507009910707241811515640c2008103600305a05101d840c00e00c87d00b0f03403030140c1d00144c5916441d0101c000c0141c5100c4016408180c0d0114030b03150600c01c1004621407000c62840142100b400d005520480208622402100208103000d0000c14001d070b00703800d002450020302131015035071401d290350114028a1802982400001d080001c00c07c5024040c1000404440c00804400810442e8040310607180b014403001e042e000034905030501a004c107072503041d100c044c1184c3d2888103100d4181c01d560a40c0500c60362085440031003030716541141c10040c0c00707030765022000c0e40305a440160000e62644 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 868036861 1250 868035611 868035613
    0x81501030b041e060f050121031107050604060909051e15030a0c0e090601050102031306051303021807031b09030209060f100203040503070f141203120c040905090a1106090316030b0117 81
    0xc1c4803200444140a2308111681030901403031480a4100c40307440c0241a4012a410010000d00480c003242c1103c250070456038042420b024036a12800300d141d5405992818402c0300c0b0845c00480e10203000c06034946803441016048842e121015152041c1c400f807190301c001d140b5441e0300288a104003051108502405c401c0c001545020888203107404082c030f551280108111010904401c054102446480110740041031400390361090070b85900740090540c0c2000219140c0781d0004144003a2001400c0710000da9261b0544807891502802519003004000304d070f004412901c00c420950321408071500da034016900540d201c034101030901d480d0114071740000b9040c8025840400894050403810400c3c22010b43e007031900d001481c0c1d209440e40c042c410066841c450f01904000304c2e058032201500460380d81d51000c0c001a00d4522560751034008240001c1d0160000e10395a08541c00c10b4070040c101c01c8005002c42d04110714a03070b14504a101280c2084404240340c1004004980d1289815644d01c0b880d00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 868038111 1250 868036861 868036889
    0x902060301090b030f0f0309011b0507031202060106020f0a11062719141011060c130b0c0a1b052706011b0f0317070908010501081501030b041e060f0501 67
    0x1500c1d5901d000b90043d00c1c1c10000341c2b40c0e1003444000c1841125506d02c0d48102201c10300f58480c5004180c23441c9422410b4014440c1400000f038070340c40045d12203001108140030300030702c070b2880c0c40d1b1240034600e01170b1103900003208120803003012400d844030a06100c1400b1a544143c04134108000d0581840c4044000c00c449110052250540c40082003442d5a0100c0d041002550b542c8002d032400f941c042d46601c05070080340100102c010b02c40000300203054480040c1c80c100e03911078010300c1035406088282c000541c00072008074002070b20382201010829090402440180e03445000a80451600f030310100b480800c1c410100301c0c8155000690707003202007401e08100390319801d0600c1030800d401180c0a010b52813040d0100040c907006040c08010309600440c03201040c074080d50f014010b04c09074494201d1640c0780500004040d03401050805503800106400c7c0201e91844e20b42c03461101c070180c015503064028540070710305110f02100c2c41ca180303441001d010801090082168040310380580c03107059490030b40 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 868039361 1250 868038111 868038133
    0x1c0e060f12070224010608060405191d0f1e06061e06040302100804020102101a19120c080d031a01050706091e05060604090c05060703030902060301090b030f 69
    0x4401a181c6118462842000daa80c485508030310300b0300361a1000e800035110513080f0700b002603459115410b0714141d44445455403551010b1004554049606045a000a01d0b000701c0f000c080b900160000c01070584d2002070011031404131400c180a01e1000c41d61366200519401607800300f01a0b40340303550504800740544d49000c03004070700c082040071070100c02030495901c80311041c0d8940040e14051a000342540345811747c1440041c220382010b40381a0b025114401070385140038800d0061055a5481c0c110f040d00050f1480180f210034072201b990300c8003051251001041c03054504080800c60360140e00c0c1050309a10380b000c4181403203010380903d003c05041c60001c1b640d01184800400c8600c50a29201d43d4803441410200004c1c20040001088e000040a080003010020b017102c10070207020710142d030050b0b00c503041040122030201200400c29444210100110301d440000307008142d01900303010510000750f0f80025002c0d40240c200d0300c8034641e40c80b41c1003c142010400c0c00055609000145007000b84 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 868040611 1250 868039361 868039387
    0x10e032a06040503191a0406050a15030c0b0f0403152309030f03092a010e0f180c0c06011203030507030c09140303041d0601031401030b010605030c07051c0e06 70
    0x100c00c441001041744241c59020000b83d078418000c050a82d484120007800c1034505000501402d54036048204c0c00d018840941c0414046003100300c96100304026201454a080c1081c0d94002200d1510001400c4c00008081031190110362041800c1e07039800660105070644d540c0d45a440740d03a1403684a0302007410803401c1c0c00b00000311905044090031140c0c89640b00301c8290310b007601d0403940303500c00490744a2800c00320f400c808600725811000d807590b0031400c00c0c190a02c800700340c40001540d4005030300c0c0c481c50301e00481442090341080100b4407180c900080c0211039840c042d0203070700141240a0380c19168050603810b2103443e420964038034052001c0c0b4184030300180124924080c80424200d82076000384569000c00c121402041c1182503055503503003294286000d51750844085001c43d042c200c115602850180d40a41a6940190307070b03c42d0307a402c00c581110203801c01404d210801703804020f03080104004101507000c0161070100460394900000c00184944030807a0060301642080c0402e03103980b01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 868041861 1250 868040611 868040623
    0xf0a0e250f0f15030f09120e0111010209010e1c0f140111161106090a1403100b0108070c110604080d0f08070507030503040507120c090606050324010e032a06040503 72
    0x200c0f519000c0340d408070184c8008014034042c00000d0611300108151080c854120060420340b0740c00f40c03140e500080c41500c0310780c00d070320032800310f070b4002556a451401c00385042d146520101c1d605000c81030701040a940c402c0074908018030152581800038a012241b61024000c0001021040f950740b814021320061a26089c0b011101c018803041c03440e190623115440d101c00356110120f0003003c2c820743c41d0b80e03295480903201c0618000b60113801520317400000205107001d101a50340d4183d540600325a038492081301c400071454002c40e508e03c1c803807280465565681c40030300050140c60015001003550410003805c02c04a0503400d1007841886401c200b14241c125003660710300b80d0582095a942d690702c1c5411420700760540c000080e442d082c21441d10504c201000d0f003030181c2c1c0d000b07070003000640c0d2035590a0f1020301044803e000d01c44281d030f0f8100c2e004481c0c90310841400006040c200c00712181d94000904150007580c00883c07480c00015240e0302d801c6800c000070b8101205032501031410342080042074440c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 868043111 1250 868041861 868041899
    0xb030a030903030c1b0b0714010c0c0b040807052d0a0302060610050d06080102040302030d030b060f160f080a090506070b013c18050f0a0e250f0f 64
    0x100032419542401111141000ba00c0c0d42101085201c1b5210340310090b082d0030048094030a1070f011045600d21035030501ca1791450314000e807120180d21000d079982d90713480c1c0c2004108440400e01070100400042c0200580c1c0390180c016890b0994042564240a0400c0020302107143e0ba0341c8440c1448000c203401052881d0060f60507680b100491401300401d442520505501286203498040002040030f41036000e40140c0e807084017a9041c05401020031003e540c8084c0400b54018820000451480c002e1002001580610700d422060f4059039240c100c44114641380654a0f11000203541500c29400b40c41e0700040d0808559860a1030079907100c94890340f00c1400b0758000040c011240402c1500341038030b1210038461810035818080000486000000303418130601c4000220b03502e80490b0000c6a005881c413a624011414601e9078503d100781700501041d0843c114940543c3c0b0002c0d60b035080310011009426100c00b0105540c07850320b85051441641d990040300500704c41071041c05400d401c038104a032a9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 868044361 1250 868043111 868043117
    0x6170604030807030c0e0315070906052503031b030e060a1e0213030f03090303020d030e031206190905060a0b03070c06150504020315011103131211030106180b030a03090303 76
    0x380e00c0ea11061b20790481e83d10805a0610640c0d40350418130240e60039040c0300351499622903c00c1a951901540c15010355a01003c0505d1040791900389803c1036204020058001c1c03238003003245800300d00c14030740000f002c0e0a44400681c5900ea550700181c1c0402010350001106102040b031600c9015500414507103030801a9030281d000504040c06900806c060030155402c0098400500c0c010f10b000f5202c7c16040c031084001d070050560003100140a032040b00481d0a0f80070141d854814a0f002c00400c54100411a607070201003030300c0322092980303a0840e03400130745880c20002031103040041c204900c01d183d5a0108403000010002c1100c040d0380844e4061759030303034060000300703151a19442001c0200070039086150018030100400056031041c442c0d0460300303002a2518004803040c0606107459124020702401d40c8000e025003000030f0b5210900c0c0f070500c00d000310700381e811008079000007900392480b6500007220140c003400047c500d441a8803480510f064102d001301981a00e41c0d901402c204440d21019040c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 868045611 1250 868044361 868044371
    0x5061f050f07080c0601180b090103080a0c23030918072a020409060911030f030f09060c0d030b18010f05060309010f060807061202030405030f1e0c010617060403080703 74
    0x2003043e110156020100b001054910b1583c403401c0b0401c40e000072800f0240b40b00d0420800740c0e0a4180210924140d0750091b034400c1c5040c24802c8180c030fa940a0200c100c2e116000845490050203042d07254407100841c40c4060340c0d039441c8803002c0010000034803500030305600464003072100346500881d448040c0800740903100c9440c00c0d0742c0b0790130310540103a0002a400034203203840e00b410040381d94418800103100f0503000c8618400b80d01815a03c1014462190107540b08010300780c041c40400002d030590050040c13506181c223801e0700c119400c058291070b1684c08251100801007452400242d004440d50304805061700941c9003858000c500010340c403d03e801000b001020030222502074200750310000304110113100840d52221440ea0b034042a1080c28006101c000c840c070b50003240384c02140d004540000045081440e42d1040300400d03800110349815003900000c1d03154410821001030701001c5018030000410b44d107000d07000194148000c415400d543c1103d0b0070840002c0d003019150350002e42c0741c580055 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 868046861 1250 868045611 868045613
    0x7020f03030606191101020d06030606060813020420040b0301062d030b0604031a0405060105030102070c05040506010e0a1d150d11060d0204080f010b0103020721200105061f050f07 79
    0x10312041d1700c843c00b88041d400021420305001e02500410200c900c07444041056507500e900071195910265001e0b00b40c0481741840402501c1c00750091a00f00d180e1126003505d40d18001c171022502d5002e03a010b1070b440c8102000400805c0d41128810b21088002603031a00c2d00c610461000104d090800c80c0172080c190f9541000060781c603003105031405940d01000150740d007420301184080341e00044804403281d20401e80081614101030003030b80d490079804880ca101c40303420941000090706004058904000034110b605040e0394030341189e60010519100000083c00d4003100c840c020030300041c00c2c1071140c2a2156100500d071200c0190415640e000400c0380007000020000882502c034104c4501c0a00380049400f0440705004107400c800486218020004c007281500150b0590150190290058800c100c8410001418514040c1e07041c00a00d40841070807140c070242d807810b072640c42440d822695220100030050501b5540445845c840b01514841102c1d00000203106125010780e030610010b0214640e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 868048111 1250 868046861 868046867
    0xe030c1503161b0503190306060509150f03100f05270a0603051c03140906060d0f08070309330e01110f160b070302030409020f0c01110307020f0303060619 68
    0x402e088208080f10411140c241c00d1440d5290400e9014550b0a0036a2a00302040c501912521040340c18680781c02c1c0c1081300590400004141c44a00341000c0b1508001c00da070242c450000035441070308000e0b000c030100707410002d0326111045107070403150140400c40d1080f400c88901c90038440e40300d036111008024039921002000701400f240e03071008009206205001030a12542c0400c2441415255810450700700b003c241102098001e880511003030f003101000ca41c071801c00414002d242e41c050400c154a107846c03a82c4244890340100c0e400e5000511714803051000f00e08800c0701380c122240200300e056029050902018420360074034000320610000101241480c0d001d85500c08400c0205425582c00d60a01040301d62210482c071040703481d10a46410102c3c0800b0010296420b042e05940210300f05410100401d0080d03001d408105800081170100f1455000d00740520b00c41c1d09030008905880c1e01304160040e142950018804046030401d00400146803100300580b10316640c646c0c01104a244d91440036 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 868049361 1250 868048111 868048127
    0x30f030a1506020d0e03070b090f03030403081c0f090c0620030c06010504051b09090a060909060903020f0a17070804150302030403172a04090603030e030c150316 71
    0x101101c12801800054007680100707500c0e40064907500d881c2a003140b80302c1016106c920502030403400001c01d000440c0d1504200c014811160806400c032441c0a4503a11910700c15000907d220301e003030001c0340c4490504411030041c007031343d880d4030507080c0040201a40c4041d014081d42c052102003008142907a40d2160310040c1104481c0d4404007540c2d0754500d500c0845459500c24059a8044c90508000c20040b01849001c400c080203106c0c0f005081c420700c0e5040101480000d032554000c03a4507100d002c18440c401d449080d00d1540324004c00a01884c440c50301a081982100c1780e61607540001c40c07900701103014111000503604446004690783e820300d16000005001e580c00c40f03031101c0702510010041d6038143d40218001c07030103600d07000032000d404200140204802c03075001c511a00340705081e0045a00703c04c61041c0c580f5481d81d1701401c0603100d040003800ca5a465000768001010a0500300050800b0301a0a08005099030000051081c802c1704140501c0080d0008200b00703142c1d0035941d0301d03a10445035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 868050611 1250 868049361 868049381
    0x19060b0c011b08060d150f0f0203010306051b18030102040f090209190f0506032e080f0718020c0c270901020c07030209040503070b0103080a0f020708071a070f0309081e030f030a 78
    0x2300652520b038625940290802d0008480c254602004a0318000c000384108100403004503004d440c284180c1c6c0680383da4501202103e415640074400814076449011450010b00916140180c80762903120406c0b10658a00e40c4201c540c01c5030200030b204c040b1440307c403001901d80030703281d80d5030b280c6805201583d82c1d99502001400034022034110100b19401c20501c0088408142c102c2e42d1081c4c1c4602069100c101500c101c10348510b5440144a04c00002d070040c003d08800c0341d05580103008484003043c1000e00101094602c07240d42d035104480f16211810b416089403900000b1410300307005122050703650b003c1d0700000c0d106054a100080410604104846d01c00e640f05407451103559680c9085495904618a1032010480b0785840d84000340c400200141243d4074040101680d030725042d842c80050b000b00000c84103842d000c108840c00b141c1000001c1c40260300c40d6460000d8a0314000c0c40c6400d00b0410380108841000914a018400c01c001094450b058000000507603251140d0100b64018121000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 868051861 1250 868050611 868050641
    0x908092214010302010f0806090a05180f0706120213090b192318040308060a0b030c0405010905031515041407030c0e040e0619060b0c011b08060d15 65
    0x8410200e109021032024103d80c801e0300c071181c2c086c041640680d01400201c65841e0044c0700d103000240c0202c07a03038204e550041410303044000101030030000581800040c0c0c51000d085c2c0e202e40010800300b0f5100d01c4202c02404500411070806194442c45075007100c0511418100580f9642804425610038842401404a81c03034680d981d039a80e10400c1d2000c0c0340e13a030603445401c0d440602c04140c0d828014802c200d02c59504242404a0b640d50b07906513560040501400e030001d04100340441e5410764400298000c6901301503060f291850318000420f643d290340c12440c001d8000400c05030011424255a94103d1404100347c4110408940401e00800c00c0b100341d28000d21042c02030000e5260990b210b1526009a0b41e14084403400d030300140801d9031641d055158282d4004e500007108039900840c29a003d4200034000700d14075a40d4030016400350465404040d5a075034802103001c420700014081d400202050500c00510310b03100740000c030308032560352024201c2142084032500d400039543c0071101240180c2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 868053111 1250 868051861 868051871
    0x5012c0c300105030c060f12070201020c150405060a090827092409010f0b03040c09050106050c060f0f04140a0c06110708070e161119030e0409080922 66
    0x104086070312030070300c910350007401208099980707403c3c11400c640c948082200346c035140076028202446115030042554045540c244941900900140940f4914840c9440d008000b03052600305103041440142c120b0130041c0c43d00e28860002924482950007520a50300c0f00c0c0400200d8401c010103000ca001e603a2036103d6000b20800c409122410505c21030081d0401d99030188591200900c4410301080c01000482040e4200807c02882000e00030741e8001c1c03140f05400642c0d43c0d12040030040c1e034401c0c0c0003c0702054010800c0841c0c1c401c1042820752049244500002e141040b005501d5035840107400501554200e98000d049034400300311003040076070312082001d4056980c520003000c24413144030682d95401307460800166103000144850950b4600c0c2d4030402146c1341c03d40c5400241d8400070307025003804000f450707006501005110b403100c1c114181040f5000340001d4034000b42000c013040c4000d44a02e21b00f060b404007060150043d9202d2100c00d4a500d10060314042c2c100d203040d64250084100301c1c0c03c01c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 868054361 1250 868053111 868053187
    0x60901081f080d0809060a0b010504050618060f0a110a0f0b0a021306030213060207030b0f092107140d09090f0617011506171f0e0a05012c0c 62
    0x42016144140c0b406011b44605880d00080d00040c0c0b4620042c850010314240014002031070030074000c01e0a08ac2407210f41d01c9c0982c150b0301041441d001406005503070303500401c8280081c0c1d0042d18240d13004800c00050202410340d40e94141c55292565405070a00041d070f0300144026141d0b82c11500700711104444214010364501000380a9880414140740400a050300020202d0001455006803030f803000408089603504511001c0102c0010405410f41c410414004511080d03e89800c0300d101e0040d034000d83e1000036080c440c0395502410783c080c5507a44000044004641e02c40303416419240c1d0620080303241b007503680c25030300076100c0c0703810540d200220300c4240d6010b1301e015440061842c030b5103c01c000b181ea44d00c100a40d0b1a45e0384181488810802000040750b00405008601c8030145400300325180a807941062088180201c0340300760f04aa6070001481400003406107154210442d20f013581c01d60319a07005081d003500340544607600b400c0c404100d4002d101c0d8104240400195038801c03403080d208075 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 868055611 1250 868054361 868054367
    0x80714012006070e030a0c090e01090b01030b0f1b0703031130090607080103140114010b1e190e041103040c0905011a0f0703090f090606020c060901081f080d 69
    0x410780e010f03004604201e943c40054200440d40480700364200d140e9020b5149008500009050344460300215556141e03400030026104001140c0618043c40300d01c0325918021200d06aa0799001d0a803c1b64548000708459508003180c080741d69856040c038000c2100740b070a18054640e4060b1285840031450b049410342c088403e0f594000b80030003400000b1200c21b84403c52601e885400699001c030010b0407003001480494550346640200400d0340000180a02c046800301c40e040d18284c0020075180400a1200503401000c038a08001c1d0236140100307445c1403140041c04044900281c07500080c4402c8060361459656a60f10014050b424800d2466881c03409280c81c035206a80c0f8041c41e208946444000301e181b800d603086001c40c0000c00d40440b071070001c202100445c690801c100442c10044e441d00d020500107043e2101c0b60051241c1100440c4041c01c00c14040d0034a421844c12a020324028041c030002030f030b803040b0035941001c064006021084a84450518070071426082442140314030034010b4a10703a4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 868056861 1250 868055611 868055623
    0xb0702330d11040338161e05031b04080307050109050607020d020303061e040c020714090f06040e150c03220b04080d0608010905030901080106090807140120 69
    0x64210010001d6402850b00720040380264040908115000c207011504a65603503074104400b19001201c800746074001600c481c22480480d00501200b019140801c0d50030380100072190003c0c0755060420001112030310082c014007004022598021400d8088100011424111005002d1110651340c0e00d11040c00c210b4003806414108489500c00d28001034030141c4007083c80e4104200546c055032441d00c40c1c2d0b00700401a541100170103209804140418410340d102e100e445c0e12856250050841e840c03500c038841d8800e500c099656402078511101700806151007a07816640410221000110807284900d541c4c43c00d20010040e8040a009c2000d01080c0d03920310020310721030036040010b100381c200c10001203500544d000744002c06e41101c141c04140081c150030301800c00c000d004140000d10320f644000a40c00d452814409907410340000030200d00c50359000b030110740503040b40e007400716101d49058603550740c54042e80b1813803203c0341c101c6039448220fa00c1015030081e00360122108044a00801401c282c0f036003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 868058111 1250 868056861 868056877
    0x24090103050c090c1201030807080909043002060426040308040e0606040302012c151206091306021602040f0b01021c0c0201030e19050f0f03040b070233 67
    0x620f00100203185580803004482e0f0034114541d0741e6031943d1a55079066400c0c0c201e0602107460401c1401004199110340808038807560041c418008150420b0741200f01034485420f600203e07845502c1032501da9600082c8654101d40c1c0450345040e54000035044013615050020703c10321548000600000b401400d40142081d00e0b050061100141c481d81d04001841c0719074480203010960100180010381c00c4000524400707243c2c1c0140c420740b030341d662000071404180c107008000c150314041035403401d0403081d1400d0b42e0311140c04d0355000960f00f40000d800c5544068101c0041c410b60700040c040200d60103404407180c8450b030103072013405035403000c007641c1c0b024015000071071f4014030400780100000510311003400b50142c5141c40c0d003100b461154004501070003001c0a0700c03038a4407405420320008445106848265030082c00038090303111001240c241480d158281c540d03240e510030300c0144845075900003141c02e00ca034101c50b0603600074080e10410048001044005200c49101036004000b0364054005124079 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 868059361 1250 868058111 868058119
    0x11d01060f05091f08030301060201090507050406030c12030201020c12040501084503070b220209070518130509160305060105120312130c0605030f24090103050c 71
    0x2090700d03100380210a00c2184100765101148001155001007000946525031802e5900c0c0160f1544802c0381d44d256500a80c4600c0060703544e81203807028880c003446244060001118280b05807450b60701e03400040c65941c064030340d4009041c03202c481058004d604550780b42d06140107565281101c060340306200e80140c450b40d808120308000140749a401c6000c0e604034500410046440c0031819070020240c04940d62001c003102c00f1162a01000c054104040c2080c1ea10541003007120746010600000017150a03509408601c9038004c188005a0380c008065034064503518209441d05c11b10155100808501c00d41140c1140c00904202c4109541e60843d600c01e100e05e9044840701001d0f900c00494001c080e20000d01560070900050086180008003181400814002c032804d141e10090503024181c2c042d2005004000d0b10a44038042080c0402800000c05160401c0c50541c44d04078600e1050042c014031008290310303440c1e03580915080c0b07a9001c00304082c0192510040f5038492a20507907540c0d045003081d02c2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 868060611 1250 868059361 868059371
    0x111611010f0503091c020a0506360d0e0a050907020703120504120602030603070b0c030406020601090b0102030904150b0c031c020f041806153612020a0305011d01 71
    0x2450b8051401c5901540120303009151802e01035091280310f078101350841c000c40c000d0206034804124104403590260842c03240d00100300b1a42c0030310201c0c0b01c00c0b4101516000c402d610040c00b0310400401c005050003101d003441c6076110301c00400540c2048903500140d501001c00b80500900940c0081d088055038400d50322940160071150056039940a10b00c00c000362200c030f40c10f10710300044040c0c01540c0c10407405401c80d079105866042c61809508400a89003255002080401c212a8104600390040c143c00100300042031a41000035100c2c400c120304203000b26107820424100e120784641e004000d0062017000c60b160948500410380380c0d4005d240150150000009420810b030740c1384220f9001205081a40e1f19141ca051700c4100501089104004101d54500e000196141a084884800b10031690b6840c246400d06030140c044110ba218918440340c5203060035100200b0703500d1500c1c260341030101000328890391fa1000400050241c1c0004080c0c0d402d007000e034000ea8510b1400c41740241c4948000b801 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 868061861 1250 868060611 868060637
    0x2009030c0405060d020423040812070e010903141f06030b150a061b12030504031b022d04091415150607030c17030a06050d120311161101 60
    0xd807001914942d80c413544030411100103240c503038006441e80003402e19440c01c50609001e1004500ca045801740d901490014001841208000d1002c1d80221a4100890003482c540c0000b0105402d50200800001302e00c22007a00c600e00401c91070900d21885840310501c1c030070b03511890f0050b1031584401c82e0183d0700500429402814900f104c10020b03805095070740d5043c903103002164480745a0316182078034a0840054000301c5c907916503071810f1203401d440114003401c0520700208100740c282c040303110003030301c00c010030005a48681880c1c9090400f00c0480d00000c9150304038010360482c4103034495015240c102c4050410a07501c428800304a1403c00381c030403590241400c9094201c0c00c80d890801021820703044030700780c9080009805524041d2414001010b1107a942d070403600224802d034001080007004009500090f4040ea8000e03003025928241c1d0500035543d41100c0306210000002451344034502c10b00a5210107069882808107003c4600a00510b4240540c03d0000c1c99480d0340000c0092500d01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 868063111 1250 868061861 868061869
    0x319111002040e070c03140d090b07020613060515040e0c030d081005010807050c0a1103010b1002060c030408160809040c030c0c0f210915020705180a2009030c 70
    0x7412a40702c1c2c0c100b90819650000102c4005d10080e1007101800483c1d4400c4801446280203403221059005000a241840c0c1c20145000c42d0014407503001c651044003080400f11342c4649005489030301003c00304081c1c907424800f00d00c80415002480d041071902c020040c100c3d600003419050715905801b0344902121014003219282d0701151515501015800d080219501c180c841c241c1c011801d280143c10088151480741c28000c2081d01901c070070111210505451500b889504d04500e004c644181e100c0b0070b202406512414010400000010040000303000d021181c0308494052480c03034180380ba107800c1d07445d02445e15080035100c1406680b62a42c3d000044d402881a0038600381d40f626440100d045541d40c84486142050046888900c020680c0c0f1010b025400e07130700300a01c8240c5403031205a06102042d014540c819000f441151f00c105420445511034260014218204070013200306a078810140354041c0c0185920344580b801c02c440601e80041c01c030300241c14643c80440a5a584511003c104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 868064361 1250 868063111 868063117
    0xc02070911031b03060f12010b010e19030809030c03150714090f061c02190e032b090f091e05010f1403010e1e0d0f1409030319111002 59
    0x603416080f420001c1c1c041c40c034440d03001d10740c0040020409043c0d00340c040041a03c20b818840c054503660f440340340d10440e44d83c0064401140803426034201c4851300181e81124818000d03480054040e4000054a10450710309001c00280d012014045603001c0708103514960a50704c0031070703a80001030140386401d00841840030454100860013000071000401c50002c000c1180e0101880d2226554034811070f249034607642c00682400110007844141035551085d02400072102003140500ca034004034212108400c41c542c0940c184901e0b94900119240750310030955490003290041101c44480020014544807603820100e00301e103c825240c9140000302000905551081c01914120210410305103d00204540449034214008001144110810f03002c40d05050300f1459072001440c14100d0100301010400c400c1c0d00c250410328002500d00d512400041c21144000141c2040d14000603015200c0c1e9820415603030414080c8076140c0c0d01c0210513001038186445c480412045001d203c0078507100010910135 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 868065611 1250 868064361 868064371
    0xb0a0c02040f0b120c040c020a0b010e0402010908030408031801021507230d050106080f04030c0b07030603050d080103020f030a1a0a020c030a020606040510080d120e010c0207091103 80
    0x60104128596800c01014011040245282d10b03942c810004030f80c0d4031041002100002c0d10f001d000403558040510041e074040204401c255405000504000307100028042e04403500c5c1c07034a0000300c0d141c510040310030a909500605940c44085030200329503070b007c0010892401c2c0d6400055180190600598449880e180203040e4000e00c2d00004410500540b1001c1a04801091a04c01c8600487d1500004e800c0018940001580e80d40103010740c60700300c110140c1000150401024601d055903004210140b6404010028a400341c04103e01500903044000039660143c181c444030740010717800812500091100307a104180403242449070b4100400c40c09406034003c01801d2030040040c0f0100041000a401541c00e01d0742045030f07456400060001e4804440d256000c0c1030300b0308040d02044181d0304003402d260154074040e68200142c0c400094800c0707116036282400c082c51030083c02d00800a00c0d10408071099035080044e00c1d001d440d40030407444103550b0484010407008100401421040c001268 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 868066861 1250 868065611 868065617
    0x609010e070c150b1816050408120918040b04151104140a050a08060a0b090f01090c110d09061e020606151c09060c0e030c010f14040b130b0a 62
    0x440c4800b1a5040b0b00c00050360b000c010000c074014100c4070104600000709907090304400705c40030130300611002c9202000e2064640d8541941400e040994654461501c0d18415500c01c0000a8801c2c0c50341390050f0803205410f60580900c201d00e1b05003460306884800715800c40e00b804e4003481200740000c00e031284a02000c19905500c0c28213080c50010500301c81c20b18001c0d5070102854800159540d83c01c08c130300d00500b0fa810701070080782c2042c40015043c1c4950790704041c0300300024420030201004402e00c2904540d0040f401141c10050004203880d07940c0928410502030140900550495800100c84c1d41102c0381540e0f59a1070011540c800400703010b02c8800440140c00c030348046140707440c1001101f4a0000701c40da5061030218103003492866051140514011503480c1d03c24202031204034401c021260001d420026120381c841000662504801810310b41404200d101c50559640f06541050400c000c0d4464143d540340c403000c400b40f5a4205c4c500301c00d400304040e1804200305081c10240c40032141e25403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 868068111 1250 868066861 868066877
    0x90304151b060e0124270c0302121e04150216121704170304021906030f0c080708011a0403080409021305010f08070302250c080c2b0c08060705030609010e07 69
    0x1100002440c0780a005c05610701e44082411b2003c2c0d1804d1040342c20148003600d005030340c0c2d60713030018088403c40c0040070681c00f00e250056028510703001544040d80543d01820b200e98140201200000902842c103d00a4050301d0320020001c10032503601180986405450302c46402d402c200e17000e403a2550031030b001005000729608041c061051071012f1a00588000d00701e54807143c03040b048440a0040d5030200f00000d03154a000c4103010510701c075140100030700e45801c0c14039103008480035050f44018030030b00d03082e03103c0d00940718817000408003942c1c05554800050f80d41c1d6585c6800700c3d0083d4005417103580303443c4108003000503990702940340d84d1303c00c0301a52201c0603240e07210f680a500a4109407111000c1c0300e010000c15030703c18a0700c3c111000143c402c40840d542c25080460f240c1c81c1c03144032044d00e8014664151240010807a520000d290369641e403001d8241f001892500c1410080607521030010752140c1000c0c02880b9400602640c80f45500b81c0c0d1070a22603985101007805d01809072840004510a2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 868069361 1250 868068111 868068119
    0x1006140607140c06031e012c0603010f0903021501050406030506010312090504052e081e010e150a0b011b0809030c06040909030306050603090304151b060e0124 70
    0x600c01d140d0442d61500c1a1043c109102002c14141d07401150aa441c04081100850004290503092800743c599120030443c0050300494031400405100c51100b8034130b51100010f0350540c4c01750896400c900c0c800f0410b004800082c50040d6881c0b00a808029169251a00200b02424240f00c0c00c0c0072240c01c4002407269910755212002c0c0300b18002101d13820441c2400d800b203099101c5001c0c075401202c400030b0300810752100c014500fa08013000e0421601090904004015205001400782e02064a408a1941c0c400004040c0380c0103000c03c4800003d9070050b0100101606a00c0504070320400500405008130041e402c01120400520520418110081a08035000c2200440a030485c0003000d1308039001e001071080000e0454200344d00c00c04049403600e07014010190b1601882008000a503003031411410b021040030780328000d9002d0707010108480811020740f80e110381c507203003070320b00c54400807883c001c3c0581040f9004c0c3c0149601448c0d03542c200f04402a806002d00722444800c0707891031600c01c2d401d0030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 868070611 1250 868069361 868069373
    0x306060304112d0109050121020d0e0c031902010f0c060f090b0610080c070609081306030b011e1707050f0f0a0305070203040e0a050a1d1006140607 65
    0x101a006a661000300c1c442036040782c807041040070080f4280316500110a98003c0e684104815291007107042000e541800c002c140d820007008401c0c52101d84055101c804000c1858000b0300804189051040c204602d00852201c0401c1e0542c040409030282d0b040004a06484101c200c1c00c1d04000340002c0014613140307034192003035111309000c85c4110400b0038054515080c00056030038007002501c0d21084141404180c4c81c209096001505290414445a26000d0b2003010355015044d400343ca01515400e150707080024580403280403110445071000c146840e00c0b002002440030500140c003045910074400ea0840385441d00d01100e40c41079076040303680da00c81842c41013600b0020f414801805030522100c0c14982520010f0010140c0c4e0118003a12803040800084c25104050080300564104000610088858140041c1d001e010810041000d4942c60241c50040200080b611000c2200d056070100e0440003240c1d005a0041d201800d11289443d002c4000781386900101e0070f94060400c105803000260 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 868071861 1250 868070611 868070617
    0x212041815081c180317090f180108012304060c0e0307090506030706090b03070f09050a030303020309011b05091207090204031a010b090f041503081809130305030606 73
    0x14000054000030760b0703522102c500c3c080d45295040140a0110103101150780d20402c1241c448030503424084003030b03240d03449203246407001da40e9200c2c3e003640001d51351405803204583d07048282006028030352030810a4500b101411020f000d010f01d02d500709401881c00d106244444082c450199000f0800751300caa40d110310080c00c188420310705000141075108041e0360b06011000c0241101000030451b858050109400c1c030819401880c02d100c0c0e41c0c0d00500044040c2c106881c0e101b1f400d414040c00c008002441600c081203580e00840e40000500004030401d541034020718014403520b0024404004105031010103501081980b00000d90188014140ca2628006c001d4012600300c05454034680c0f112020400d9910580054440d0203046403180310054080311068010a948030744103048c80380f00400180c064240902d6140726a0702c50141d000c807200c505005400855000c003406070b031942c080640285075031542100601c03035211800000c90410300328640302500340c1e0565656156a0320002008000c1e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 868073111 1250 868071861 868071881
    0x81807090608030a09090903140705010605060412060b040b030d031a1c030219020a0902030a0f0f0c030c170c03100807060309111804020f010e040203130302120418 72
    0x48254400012210800e10034a4050302c40500659550651080e0291400707050743e000b02c12040c54056564042076220082041d036441502903160303a030b170040c1056805080c1076004550b000c88001000140552440d1041400038400c4000f40129010181040120f074500d0040790b8068001c01180d0489501c61751241c8085405070706840c840c5403440d03000c03402003500c4006283c2445002e2100006040c0c0400000700c400c0b4800c90394070000c4100d90302250200c203861044405131074002c8046200160190421003040b805180c0801801e81a10851000f8001050744407021a113404000062a4403e40d0858244021400c00800307a0310340c0e016200c00e5a1008042c200300351080741000c5000b0f441841020014017282d035012680414600f40080d030319401c1e2021603c01c15160003203907044a201c41c1c51581c0243c044480910062204006031600084c1c50030311a03002d8400010050020300131840890294000e508030303852110081d240c56030b1ba116500405c40c0c244814039501d0506022500a6500d40b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 868074361 1250 868073111 868073113
    0x518070501030c050c1b09011a0426033f0f090715020f0d0801031e030201231617010909030504050a03061d0106140910030b070225060818 61
    0x18080c00e172004c1c03c003040c00d140050512104030080c020f51402d400558050047c0001c050401c010344049103c0c41c1c031452051402c00d04030b0307080d0400c8004a4001c4600c506100100b540d5032820a680b118034542002070011004424950042139009a422010322681c0c0b01c0c110811000d441389200c8400001c001401c030091132140b4400401c428002d11840c00e1030708d1242d0002c1500c03070b564030810390424001400d0780e810441c01b140100040340080c105800341c203260130356070108040c0c0d07414100d01412031100030244103c21901e4020307100800d4040d140c0b08652500d0000c0b10080c1d40e0350100c0d25030840b5040350462400340401804800c1240d403200d80d030365101c6e0410718500f40d6204080b8202003115842074454035615110b01402103807400030051b03c65402002086102c2c00c02d03d40f80c003030822900549010310f00200018041c0b90b00064010050358000324801c3d0a03181c103210081d540c11902c251501294a040045c0c1c0d00582d200950100780c410310303100d5080c1540d4404200400681c010f600c2109 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 868075611 1250 868074361 868074367
    0x11011104090e030c0a14010f05060117070e040216110906090103200d030e0102060f04170c120705010501030309230f180f0603120403080909060604090204180518070501030c05 77
    0x30b21394104850001144614810b00171409400700403400c40b86d2021000b00010b08040030000d0981c4e0240c40c41c040c4010a004200087d01c4811007152030710b600580d607980040c800a041c8004202051207084520b119444480000000c0c005200c00030006581460b00b18413503c005000203402110081e0f9050001c0c80d02004141440c0006080700008040940204108407102e208950f41806910f03480369424000c861642099900c02c4983c0b4041d2460380005c80300031030b881d24068418000d01d45030420f505d103000d84991007401c0c400d000701000e00c01240800c2d600c450004070011523182084544009280f00d0340d408445505200c5050304c0c41008070747c41500301c40d41195040302e910225004000d102c8601086250107130515240011105170a000c884042c401000050030107800c81c2c90850303080e2041105c42c1c417010003181c49070196030003d8020a001050100d240c026000c0c40d07044040e072107102489a0340700c05400030400428a614500da981001505001e13a500940100c0e880742054602145 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 868076861 1250 868075611 868075627
    0x50c0d0c1401090f02040b0d120815130f050f1b0f0f2115091b04030f030509040f02090603040201080414010207081804021314030102120108060711011104090e03 71
    0x403c43e01c80e03002c200c454040e081444015402c0a00c92510000d005030750400c481e40c11030b200e100700c2c4050b50700058101702c070043c0014040f554101a080400c0d1002d00300c0304031500741d9501c102c081c1003942c050b003000314070782400240502980700a00b8024020352541103002c00340300c100300785660310690807490307510001c01840913401e0304038004218001510324011009007140180244014019241f410717480c01d02d000191217642c88203481a008214600010403513030008180a20303e0107203a04c040c2204110b40c1c02c1c0c00074140c100004216645c0101e6040120716118250130049026441089030801d4003130000034019400b8524080c2c00900440c40860f02c42d0000305901c0c01c1e43c1c0b102070101d98041004c200d940700401c07000c03420858507608076003e41c1444151080302c00391400380e11542e44c01c01c100c0e43c40689a6107082d030413510900c0402e40c600c5d62544c0c44641d419a648029280800020720030042d503102c10906200e28000364804420729894149405c03c104090074010000d03074400d01081181c04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 868078111 1250 868076861 868076863
    0x50c1504050d09060e0604090b040f02030702280f060506040906020c07030b0a0b09070507061103040c1701050c0910090b0d05040c0807030f120c1709040c050c0d0c14 73
    0x610440c4a9001020b10410540008088071840d83c080003e000c1c0030a9080720300d603a03040a540550f00408400601c505030040041c01030711040c0103021800744004144a512a408141804d1400c14a2100c002040c1c5541703502c1c58068800310068010809a4105c00c0040c1d01900020b405c40343c0104045001344150300c50108a910010b0a40c409912000041082100780c1441c075a201c030700740e40704001031000300020451041000b088001007042c000340000811007650f2064600031561040079859150910704030349030000c20b000c1c1001030002042c5889003070505004451060300b202032500d04204814090001c409504240c40041c0000c07613001091595500c000741c440005840d1000c621030a05040c00c440400c0c443d0401100c03a0084031091020803c0041508407507a4040360740c80307012040d210100d4440d0840c201c02000038a0b03100f654560129403202800401c1f40071a004c011342040080c05440d43c0c070542a4850240d0070039440301c0310803405031542e0f80030307079005c2c192888a140080400e1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 868079361 1250 868078111 868078153
    0x9050607030507020f0109082b0207121707020c010311040e09060114100905010509010e04180203160e130c030c080f0c010c03051227010e010506040902060703050c 72
    0x10034006942c400810908076410040c4001840e0208020801c11450f51100b1445100c2c11012040d6043c0c0c00721140000114030f240d5900f038102c2600115101d240c20300d4034401c40d075a0888050005600300550b25641c00507544042e010b0b210a0700105014003804005401801107000e0359030302d0030824000000e0604660f42154850200d000140855604045203511114440d941d20344c01004046050910305821200c42000c2c0d81c0b090034500d4403940e10030700481702d645180070025002414081881e156018143c13160318114801c170203403848082c0381d4201c0129104181308101c0d44551750b4010590702040c100d40b003020306005a0b03060711901c0d141d48034904207603032591015402e6800400d030b8211144060140701000d02c03091074180e5040310f141d24010700e64061920042041507441c00403c03a00348100141c0702014008504110702c0309201ca1406009122003502c0415a509110008201c1d1915101c0c7c20f41041c1d00408090a210513134400b00c0c0c003504604201800c521401c11302c410328601f4410f903 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 868080611 1250 868079361 868079371
    0x3020a12200a0c061803022802150a0201201b0a0503040e1504020414060922060303080610020a140312040b07110111091002010b151b070602190204090506 68
    0x8503c2600030700c0c6002d03000c9880d80211100141c030480b081d10006036000c52000d2408401218086090b8941e00710191582070028000f9030100141e0a2045402625000b07040820b030705400030003c0b080300146c000c1e003900b054601c1100b04402001165406000c0aa070300e00b090030304d8800c45d11042856035407a40745502a820400d0991488030400000310981c1e900c43e50701d4a410344055040515181c101603101c600520300c14850380e00840c00c0140d6490301c1c2d41040c100e003402d9050144801c2c0c141e1410b0300500d038500040d00080e1032000062441c0c103200b0001070303070b1090302c2d802820344890070788414050366428444601180010802c119092050050301c5009034003030b0141c030701c050a0440002e07020b0480d02001180a90510352451458030708103060300d07100788083d14641c400ca50500800c03801440b04084066204641c3c600c11000c00d9000d84c058000c45075204030107400c542d90810311560b83c0e0324030b1080038010381c40001503208441c0d02c14030720705400d0310203040494800c000d5540e4a041004c01c441d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 868081861 1250 868080611 868080617
    0x11e090f0b090f0613120e031f0b0a06020307320708010507170f0606030c070b010b130e0f040219030b0403210608030702060c070803220603020a12200a 67
    0x204114010050021607044003171400748520072142c4d17a03600200c00f03102100c401d050054200300d5250948040c81881c40158241c615103c0403c0600c4a0100410744103012502070050b4010115006c1e000204130342c05aa00186450081c1d425040020390508548803142c0c46001002c1e2a1540441d08200c09030107050f6210022a40f80340100009000094040d801e40c50401380303405104103c1c08140407070b07402120a0340c00036525a200c1c400c01046105034680200a504d07020000030312403062130050603118a00607036560700c0aa0700c1208100b513040c191424507903000d4090200b4014a171140350380c1360b040c1d01000c80450183d40c0780c40f420710780c00b0120340036004606215007800e220a518074408942d00203a4004100d0f20381840d215680d00d001d0200002c0c0150070000300e22903044810840300f00100010300c1200d41e24800d000c44030070000240411035907030003200700c4003040c80c1d0300134003c0d502c41c4d80e040d0742c0300b229440030016113201400755003501680c41c074000300381c90b403225044000034112914151 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 868083111 1250 868081861 868081873
    0xd2f0409051005060417240403140c031206030606040e071e0f090902121f02090609040e0706020105091c0c03120f140a0203060f0603070908030a031d011e090f0b09 72
    0x5001d00c0c28400045116a44045801c4c2d1f04203007040c0c440d0303682d0f41054061038000380c40d14001d05448440c1c8101ca01c4120544400b24680b030705124422195032050100382c05865081c0c0301c004c14041912002110188a900b1010301030003100c40d59241c0500301000a030308001d0329a03542d15180b400c410f0a4200146080d03c1e200d0120550510342c03881c248585000300100380c003160050407024402800021a103919400051a03030b05a82c516003524540307500240108020042003a006076640d085108240142d42010b00007851680041031810000f041c100c04554100f1440004071703038081c05008203c0500140a0901441d4450361254000030000e0364000107050348039a2000c900280010f1416100a004100308042919100c6d081e02d68420203880c0c2c4c5803292187c01059540c100581c00158103440045a0400600d6040e00800502e0b00b400c025040c0482c0c564102a00380c4406640f401c2e4001c400703880f00340e56851183c0c41081c42c0c602650603004000790175940d6005103c800d0300e142149074450 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 868084361 1250 868083111 868083149
    0x510020a060623031b0f0111010c030c140a0807110a21120203060f040519020f34200a0b0c06090304140d0201090306020d2f04090510050604 62
    0x240403c0300b01400318000e00c1c08070039041e40c03840880e692010f0140103003540c10300021a03900407110005072a500c000280087c03024464010b00501c080050100026404410003d1071500790040302d55a807041e81d02e84400e580d44140c103031195900144110540e100c0c490041000c40c00c1d0041d0010450314040101e0240200d08900601c03016003034070343e10101031040090040a61701c60844c00600324040d50085500e5403601044001c0c44c04591643c0809400000c94030b40120400005045002051550340c0410302103401d06100004804400c0f08038610042411010500e441c1100801001151a4000768495200846c2104083d5400080e2040010404180d40318040c44542c3d807081c048001141040d1919912100b0101000c2c2d8035030007424890184401d44e4443c00075080a0754020350b0544d1781d0748082441c0d400030451002102c41c00d0210721159035054440c41840404950301400c26814182081100030003441c0c054840f041c40c403ca101e000641c1d0f142d60010300003c258101d41c01080c0b40722 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 868085611 1250 868084361 868084409
    0x30c050c1903080601140d051f0602030301030b15222304020a170a061806290307061d0307080a080d05010b1306030b220e01140601090510020a0606 65
    0x701400c070341c0c113102c151074106c021000840c00781d13001d0000c42800400c040d2240c03040740f2102c4484d8a9140151071034408003050b89600040154100c1c0c0c492400100681d543e04c00014a040c08050000d61000b6902d49120a41e0410403020310304086201002420091101d40301412190b030f4205051b08990010030001585040c1c404c00c4010100040e4142c00222600001c54890813850f6005220550303c102002941150941c0030a00981c4080200825408100010081812101c030001c00341c5100c0d07074000b07142c100810f0030300c101c640c40e840d20400c05969604030f4099900c2c400e1066050b110b88140018031040230002000c0a038001c0301007564035240d801c481010344005030000030f0041c0c800c00500003450f1004101c07a0899400b40790011311009501d000484007803c412188510300ca00c251010720780c4016078000f00341004c004008000050340f07080c4880c0071350800c80f81d0501048240000708000d061002007800031000314070503148060016a41e1078200c0d100b13500030380355004810140c028010340f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 868086861 1250 868085611 868085627
    0x4207030c1b02090402100309060501090204170114071b0807060e0d020a0b060d03051c020903010b0406050d020f03150c120702030c1b03032503171303030c050c1903 72
    0x10108941c0c44031000a600800c5030110f0140009016034a501c05100c4010b00c2644100040e42d40401d003400301b56900d04182e000387d0058000d40c40403286034829190703050414800d040301546900800c419681d2402c60664032240318001813564108505005000900723000020320300d26110f40400110700e000d40b0340551034a21904001c40541d44007420b2030380410b00d4031080e140d200d00220740c00c00d20814503142c11030b03e6000b81c070540301c400d080a81c10540b22031241d4000d042849030590007004003550000400050310755611a45030000c21486030140507050040810129000c05412245040d0111900e07108504084501540a81010803440c0c0f41040344007525400020510056041810303000300d0944030049425278080800c1419140c0120361414803d4a1650145c012003014120360712039449542000880200c0000b14140b20041c625060f00e103111740143c55202040c02907001603a0180d0040c00c0801600c004e00070144070f40c0f804480200204100c072840c810324001c03400100c0c40c2c0500020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 868088111 1250 868086861 868086887
    0x40e0109060e0c0f09010c05060708060405070e0904081e1605010f050601050306041a0303071b1217030a1e1b02030c280614090f4207030c 61
    0x4542ca4003401801201c2d41d0582d0054400321310b44a980da400c41d40143d0310416150340040042c05420104050b20760801d612501c034640c140c90a0041d60303103414080310000f000e0703403802c6d510500b0303a0042004960031001400039012800c60449032603249000300c1e242c1d60032a140000e100c41c81e003c0e510042103000c1c081c001004001030424800f505204001820501008000c1c80c001c540c0c801001c950074840303180314030304000c025080e03075610101801c080c07080146404901410b1143c2440020300301d0340070143d0203d0213800880b610f03803d08950200301420341c0042c18140d00227841d10400c0381d00007281303170307114101080341d07940080c059600c501500d40024a8103d84810b641040c00000e800c04004103044107284c0c41410345070109100600300010005c0f071003001426007481e052101e143d120030520241d0180c0e840134100e842891040d0b409544c0d903070200144040b01e5007400c1c4400e840c2011071031348003c0d850745031a000f001c55019003119003824004840c07010000e922484c52100e0940c10286082c020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 868089361 1250 868088111 868088129
    0x804050f120403060b041517120d02222103022e0c0f090b1c0c0512100b07080901050c0f2401080a030f051b060411010f020616030b0402040e010906 65
    0x9070144101403901f248a0b03109003084072901c0c05004103009400c1c02078031450300107944440d8a81c01c4001035a4001e40005550341d42500402080a8641208104000031a10040d201e1140300c2c0d0300400c40e017202002408220154844d04a524480f140120026071240e00c0f2100740d100845c0c469080c501c19142c80f002c0c03250078442d800621003902980010400c055525556124cd59102d81303a21107030078940300c0c40e10200f15a10b011000f0004552000c0189848001025000859112204c4418408030f09102e4940c4040c820003800c1e00050f8103801418000c171050410900b00428004c1907070030b01024880f01c40c1180c0100701c00b4000803580030004001c4410b0a005a030007036042001c4030b96180d404401c050240101c4507000310340300d03104038100c543c0ba0000ca080b05209074071482003159244011349040360314188103001850b107540305200c0e510f407122581d0f000301042e8a0b2240042c1a1603210600401050f490b10b016140544850009200405001d44089100c0d85000c9a0790200c0308150041164 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 868090611 1250 868089361 868089371
    0x13030f080f0103060e0708010f02040509060a14010c0f0212010e07080111160c030804030f0203070b0702130b06040b07081e0702061917041118070903030804050f120403060b04 77
    0x8400000c8290305503036100c8070004502c2e05c0100f000385000026402100c841d800c0c9072850080e4200b079009001104d00c10742d001596030710b0b21001c11101c491036010b0781052039030840404a0942c800d11030424202d009002c00d107414101a0082420845916511000303691111441144140c0800c600002800084020403107e41d0b0a001001c803489140040c07231401c1d00401040050201030030103c1e00442e40725815698842e503038501452060500801a80300c0e004880700000c8102201080303030a03850340105512184159443c0004c0100400c0921640182d0203200200701c1141280041c40319501803078196803200c100050724062540e0b52400703200c1c03059051010b00c0c0140c8602e001d807981e000d18142c0f1032249009804040340c40001400000c80000554014401480030311070400f90001e80c183c2c0c4048800400c441400c803140f500703941202c0041d0400a041011a2080150940144c4210b043d101a450684c1006280c00ca0141480e0030304440024100104a43c0c0e114101c0b800c48207440603c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 868091861 1250 868090611 868090621
    0x901090b10060507141203011805070c03080402120a0203010c0215010f03020a150509040c080a0f200a020a050a03090609080106060e1002101b0e040504050d0e0a0e13030f08 76
    0x8028044c00c42c0c010700c403806141c0e0310002c03440140110151040782d50b24490310b944e075030b50800d0301d0b04c1e44a04964001c0c03031401001c51400752240f10740032001c070f405440d00c6445407603a60030700030b14a80f1550701c00c409005229070100142da0a000702003410f407040e80101034241154131410440c40042e4094000704121840800050300c821801400311210a04141c0f104003141c501a18140b0914098030751040c54000c0e40e0341e07065041400680038080700b080421101800760000c40c200d404c241c94034000e0030344031080040680d0603240107207440d80342c1c4d1041d02c41d1a40541d480510704034514000b203002c030340791800501541d64404c260310000c0a504000344202403800d00054a400b00403040180540e1800044c4140709008218089203d2000d901c10080110005680040c58849202d07600020f40e0f1480e00c16120300c2d00d801601d018a4010f001341400502c203d0702501c0d02504c59520641002083d000080d90348078030324101f0310640c1524556602110a4a4010402d014004401c001e2041c2001805 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 868093111 1250 868091861 868091867
    0x503070609180e120f031503011802130f1e050702030f070b101e090b040c0215040204090c0803040603110c0a11010519091e080d260901090b1006 64
    0x1c2c507000010180040d140c0200c0710a54241004491030788001203002406400b0600000025071007610800d81e071214001d030120415087c2da01c800f01c2c07070760500c2400407203078003501d015074030040d5009140c3da0010310761100c1c0140c001900c00d210144e180121503410ba03152504564010b0b01da00600303610145261825443c00140350780a4001d01900381301c8075200040f401010714444401030300c072684d054500c00001503940141550380d40602c1034828203213030381d0704610704141c044e100c2518810b402821028a549010301c2e54180002e0090368440d85030795408000c2051004134034081e0040e607010b9680c0368140007001c2d09030b0744050143c441c0c44c0810040100c8401e800715100c591aa4040c4280c1c45100d50308004880714011200700c0034403c0113001a00011310707008049001159845100310b212001c14003600081c00c41c00d80320742c09180d0455010540c0c000e100b5034405240b9000840c1284200700008482d01903524103d800b681a0ba54a5580c00305014080340d20036880240c800c0c180d0b10580c00c0602c02 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 868094361 1250 868093111 868093139
    0x90204030b01140618010306051206101a0d270302060f0c0315010c0f141605060a0203040e2503050406050906040503040605070602070f0308010518090a0210030b090a060503070609 79
    0x3203001c0d01c041018115a03c00e41002c230040c84010120781082028621082d11600240d40681152201c445c000030002142159910482c2403c1141030400b040c884515029002c0040c501051440c4080c03018160741c115440b0306c50a90080e8000c001f40d20b0100390418040380b010300580824034040c010080c0380501041c004440010a00c2d1840c090595803600181d00707403021034000d0000c02081202500b04100141d614420624500e0030300300f081e9201c1c103009880c0b0a150360b1500603003080000b40402e451124031039400141b0b84000d50305080701c0718003401c0c0061255042c0000a0b0311b54040c8802d1120a002d442d42200200c1c0c00780042e0309040d5646a5240300b2481102c09118020a1140c20302c411a0b0590b01030682100518071150040e2030000e1500c0d0007401402d1007100003250b04454083c0d01c69000d4403808400380141510340003034003040700d0780c0391011000042540b582c0c402c9440ba218204814004c0035102408144a070401e4105070a14083c1e0304180708101c07200d542000080400510 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 868095611 1250 868094361 868094377
    0x70e0d0213020d0e1b01030b09070309050a05071404113108030c031b031e070c091a030106061d0904140a0503070209071d040c020309030106090204030b011406 70
    0x722501199807900400064040c014414421600d042083c2c01e0500d80821250a000c40c2a4541e060000c02c18005500320b40c00b0312031064004000400082906000780e100c907202d80d009104903440d01c0c0301030752072510f401fa20741c21407001200d000b0b06100c0e07141401c0c05040d2080002e510602d05090741d82411441041c0b04912403011030800d020b00c2e405400ea00e444a4001e0f1081005903903640d018002d046a403607101003401840c00c0389826030080b0078040030003502c02c00465010381005541c0340e440051240c3d00440800c0d18a038115410020303485c0c0547c0700341004100300a0060303c0355400b940405085442c998090018000c1c514070540d40e441e034940448150b8102110104114ac6131810400411100b040c42000280f15058090042c0940003025113500745c400c032138591300b607500c81c1011a920300107941800136413801070314810191b180540017a5520b03800303881180e040007043c00000e429524207500081d965a0300060510038450b804030818058403103840c06a9070b101300b400101d4014455204 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 868096861 1250 868095611 868095619
    0x30302072103140c1c060b161101080415020c010b060406020d02060604020315040213080a0c0317040e060d05250518011203050706090f1119030201020607051e070f0b070e0d02 77
    0x14070445c100b8044c0e070082026021000d1002d85484010301003000303c0400c0e42080ea502d98a0b001d05900c43c7d84038102003403281e80d1041e0081100c01e0a490303000080e4219210042840d529143d054800b52a00c401810040c8401c0c0d009000760899000041d00b0b04401402c3d09001e90b004004005850380c01022800480c40107850040e036650600f203141001c418a500401c20740e007e102101002e10000070b1484083d0380c0030b20b80d0040b0b2210007442c1d082c1d09103d41c1c842c004070041040009907140c40c1010040001a000300181c40044404440214a40000c0070032003800c5415440203120078108580490b1200e0364000c0088699414142c4101d540148450010204003001540724100000c07030300302c0f07000c042d4440540c1403140f0051400000034440161001c1c01032000640c051031845082c001d00c400c607074068000e08920340b03480304115a01d03800034040c240040491001e020020022a000349105401a0030f400c440b803060b0f2900b01c4202c44050005000c0054400e6810407036541e05401c40c100d650704513 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 868098111 1250 868096861 868096897
    0x6140703202a100506010906020a03090306020706090b070203041a0909012714040201030f090b010b22140301201606110a020c102a030302072103140c 66
    0xd104441c040c0c0b0b1415140d4110b0040b1030010700341c01600e07008203014003404d0300d5540324540c45e004100d03541d440c1c0900140002d000201c041003c0346c0b00d5401010744034040c940c085040400394441c840610b9041c0c80e8000160700000b400c008991110b002c48500f103a18844c0381f86829040000205034a8040c081d041d1542c090740c0c2101c8108940b880842c40c104500038041c043c00c49031400311000e407001194281d01003400d2030348241e0158654070800c01015030000301c6000c10307400c1008129054020940d0407421ba5180210b000e0301b0740d11074001400410407040341000405141d000d040c2524890025800c540c90803510500040000606856010403010904850025141002d501030000038034a600e83c2400080e82c2ea903441d1703010655070707007000081d62440042119842c0441d0b44011910010744604152035455124042128061551034000d103400741c24000c40340c48102d030407042c412041c104882c90079040c0c50f001c2d4050003007a0315101c03120842041e0b40342c04c000204552050702041000303c6601 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 868099361 1250 868098111 868098157
    0xe060610020f10390806010e0d0807061a0307090c0302160b0a060b180105090f0301020a050309011a010e0d1b09060602070506040501090e130614070320 67
    0x2080004080b121100c12507a100800911200080007051081d42c0d406041426545104a980c00007000307600601c0400c0e80102c103800021207602001901490420000c0784011007559201c010085402d8000e01a09503104038510b81743c01160b410344080c05400a000d02840c0c402e0360041404011a03604420103d17100c0c4020004400038860001c100717544060103000030f0203200080030080c3c030a684180c0c1c10009039440d101d0500b1310b40281d00b1600b0002c680041340c034074254400c0001d812140b40281078150000380100000b82a0703086441d00100085c2c0c040200310080c81c0c2401400c0c04100d640c03525010150719900001c10440c0d0381c0381e1443c001c40c104402a800c010700e4880c0071000c44100e070401d02d075590701c444d583c3c0c0182c980c500c1208014402c50001040e43d142c4101150301700c0c1c0c0c050310703140320b41c5140003c1e150b10020300408085840001c2408080890024010260801412481030071186002d81002e000c80301d51600c00003078a50314070840541084d503202114052000040341e5130080c4a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 868100611 1250 868099361 868099363
    0x7080f0408010501030308070f030e071202040f06090e160303020a060203090a12030e0f070b0702120717010c2705060c10360b04080d23010e0106030e06061002 70
    0x11075024454541c68a4000018142d020107541d00a02e1607170703610a10f502d00701c0300072401e442140c1d480d0081c5070000e0710208801e84009000d12821440a400070500b100c00340e00100840f686544040122074689800c02c5440320300f4004e42d44004940c0d00d110b0030071410340d01d0007036540b804280c0040107250300001152040004106001645610103140c10400031640002009440040c141034401d1044041d0401d802070040703010710944e00060002c0e0305000064081000080c80580190810b0007140f4001c5080e000c5005000c0e4070010b02c1c0000700700c40d00b000d5001000012001d41040703400c0c4400101410107030343c842e0620110340040300d13055155100c05082c58100281089075400051421b814451841c1ca4003030720000480e0306202da640c101800101e08403810062200c0244001000c000040000f0f40607006000a0200c0d0b43c800100c4604054651045003141d1124828210400d401080081004c6c02441e014220914043c420544648010742d515640544040d11405440c2e4198a51a00c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 868101861 1250 868100611 868100617
    0x30203040605031816030c08030702010c02040b010c0c0b19050a0507031d06040e0f0c0f07060509070e0703090c0f1409060d02041b02060915040b070e030f070f091107080f 75
    0x1d892010b032100a503030030402004170031752031108480701020782900065150b408070640d010250103854014081a03503a081100502401348080d0601010044140115041068020140070020083c90781d4844603001801101c4684c02c069080105c00c1104201055008043d42e9500e5418109006103241d90480480303203442c0c00403501d402460102d0001448100b00d810b0034080c8080d01040c60003902e407943c81035442d100312540554540c00030800e2000184095003c04c0d8091660b100350344810b6101d409049800e1416104100003d03201d090b03050512241c0020f9000078180e030f04034162028a080c10800058161070f041512407138001d40018800d031514415800c0e0107600a008001ca03150155051b9070514041449074014132034200062010343c2d001801c0d20140d21009280390003907503266180e41014030010710032400c01c03242c102c036002d0548040184640c2030383c0b41c00281050b24180b07011401510351542c80b020895040180701ca9240d01190200c03490b240d00705a496985004602200c02944 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 868103111 1250 868101861 868101901
    0x4f0314071e180e0604170f030c031905042f03030f3a090203010207051506010f36031709131a09062101090c0b030403020304060503 58
    0x4421004001148600110075009541520400700107480d20381e0890403c03285905503844655100002080c04203450614501501c014000c40c103140c002940101c0303446410a541200e00d4a101100b48400350900000162444004000401079403400c0e84031600c0d901d08403140180e02108840c3c1d000170f0040100d5060081c01d401030106e0b996000310150a00c0c05a015044241c91000a14400ca0700140c02c0a140714402e5007004030010096444d0466000410b04000106e90566007001004e000480501c8448904402885200003503d0b143c00050300c4070101c0b184003410040c031034140c2da0b241d4408940c00007101002250403a801851400100c014101640020b8441200c41c000d841c403070210349002708803907102681d009940049107003d100503242100e808020441e18491070003100e0400e814015441a8000d003034825a6402849040000b0440350485c5040d0b5102c24144d401c2c0440b01000c0340040c0140c01d0070619614080e103009490340120b000f18400c02c80000701040000b000e50703023000c0e604 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 868104361 1250 868103111 868103129
    0xb030106031407090507020616050a050403020306040b04050705030c010c1203061701020d0c0807021b0310060b090909060c0301090902030c04020a020102030f010801020c0d0c084f031407 82
    0x58001c80b4815540e5400c030710800c4151401c0000040c0300c1031001c00c0250003904001020480030742c1c400401d0320310741c105001074810031005110000140e9001c1166034042c0d8052694a81c3c036043c1801c0103030604405400c414003d1303003d600c50390f070b6990340085036514554011058409080b059242207029244a84c031502111401e404c0c081c0030140107500420b21011045020015010190801d8030003410444147d005070b000280400c1401140a101c20104540102a039080d0395041c1780c01c80442d10940c0020544100101d24074810303042040545420140c0400100624500fa0107004540e10050003000b40f55915200040d0840d107040110200350306c0e00820070b54503003400c00402030007504103c80e05881e50b55018000540305c903043c4200c036049503a900191019500301034003620381c001c0140c000c8512080420044208805072050190741003a804d9580c0028050003484c03424070700494103607003a5403240c500d10b2400d01780c2034168081100d910048070745040040ca0403146c05c0c48010f511400e0a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 868105611 1250 868104361 868104383
    0xd0807120f0906030510060825020d03050a1109060a030b061603030b010f140901200106031217070c03020c03010f0b03120310090203090304030606090c120b03100b03010603 76
    0x201907001801800030452039658580d015a0310703e001c40966a0a48454881307403d4242c4c02d1250398410288c01da4883d00401918008944000c2c0c003c18103030400d030004006800c0802504011903150090503007240462506020715001555020114400c0300f48440c842c01c400280c02200e42d01075000100c462000416050b1182d8280c0c00e6404a800981c104400081c60300c90090255030040084540c1c40c03415548015104410100504540d03200300c0c9120705102904480d0400c0540040382e02c080c1c0b011000c00414014a14076103003000003c80d031584028080c8181c0110040390742001a158031000514008001e6441414161b081540c80303c4002e4143d420047c008100c0d4a4980050b80d400742c040d01140c076415969038101c512800246d03048410200140000c002001d0303d90050358100c41c80c1400d0364501640e0303580c0e610403501541e1000d20b00a4442103130004080e04140b10303c0c15004004400d0041007800000a910b50702e1b0b0800410015541d0124400240c809502c00d201556210f00404e507 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 868106861 1250 868105611 868105643
    0xc0f010501180b060705060a2f0a03050721020918090c0f0409021c0302030c06190c0306060c0605041e140f0d090605070615090906060b040803090d0807 67
    0x10b903228800200915424619006001d08280c2c0440b2030442d00400130780040d4a40c440c41c072001c0d21001c40e070402c0584000741c400d0321420824041c1e0f80190341d00d4904544c2c0d04000940034013540c0e0003c0601046c0183c010b9540c40d001e14002601d5200c030141c5000594400032000050320395000e8a014400c0340400c0e108102440b440003c2d1410f024804540d508514a210420402920380411000350414001005050b0608119201c0d01055203e40103690420b070050540c0c81c900314084a0303440d400480e02442d8441103d4078807500d15805114501440424203148005d440f2200b91440140f07001d6031040042d00703001f119841107404d60000441c0c0181316109040c0f5580c20300c00140c001903140910f01010600fa41c3c00202d000d07075841d450300d0702c000e054501075003036600742c01c41e15041d624251203007844000c21400b1207034140038000d520030000300801641444000c1b03032001c0d0001c80e9000000c00040c40694000825200b020700700b142e4a450721416468031401500910200804981072035903008 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 868108111 1250 868106861 868106879
    0x50a0e0c1312060e01110f0306310c0c0c0e070c20040b0409050c0d05010e03042d0303090b0a030908030a140c030c070b040f0c080705120f060c0c0f010501 68
    0x1001d0035005010070b0042841d1260885e00305d40c41da61500d944014100070198800c6454405140d000d03130700070546941c0f13050108025001c22500003040c00080c000c0c50764582105824810b00b18000001d1601a5090440d03549000b48038215014024500050300d0008a4052007203044502081c0c0c01503141031254400452865070000c0e1613401c41c425410441c5400c1c0e542003074071801c0f0300c0f260000300500401c035401c0c05100440d4102c0c40296425501d90301184113002003000208020035000e4000e00c0414640c2c9000320003824040300ca61403020b00b441040002c6540305103a00140e03071188030300310b41c4e0303181801003600104041c200080c001580070081148400301503020310180300031503400b07910765552414000c0712840308540f011f00ea02d505110102c0811680148160304c24800d801000303d02095485501c044202e5a100560ba80d1103c0418002410039000200c62115610003c010b60445a89800c0d11080d0040a0005261003c94240c000e0681000324001c05540c480c001c02c01961614507030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 868109361 1250 868108111 868108139
    0x30c2503030f14150603040305040e090303041e03121e05090f010b10081506040b030f0103020f010309020120070b0a090311011e120605060c01051f050a0e0c13 70
    0x15100610f0704140030003a801101040b8460401c4000c440540e0484008000142c0c10242080d41082170500002c034202c544042d509000d525184010341d00c911b414544607a421110380034440c4001c144946d010006a001071003100c0c0407004581c046020980100507811128081d03129100180c1407105101c404100403031303201d1100781e1807002070240c01c4034501400014407082141310300061910340040c1e0352150f0000705a0a000f030050283d46040d07030301c00b104041500161340348a502001030004008624181904040600307081c01c06211000d0241c00103413282c5618080347c2404c1010500c2090481800c3c480480605003c14080d42c4400c030702c2500030010500c40c001124440b03004084a900d43d8000c42c1c00068031200f018400010040c2440c04640100003401101e12240d1108408104c0d6501c801c00303800d0a401e013030b00000f01490001d11848001c61640304201040020820520090b120686088152440c4106001c001e464801041c6071a1258003084880e060381100c001c00c80900c141c1c0b10b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 868110611 1250 868109361 868109381
    0x1203050735030a0606020d05030c0a02160b2715030406091a0405061e060f01020f070b070c170604080f0d060303050403050610050306060f0d020d0c0f0902030606030c250303 76
    0x10400c54242c80301701c107903a40c513544407905000c03910a200155407066018000c091500c0c2920548481c1101b0101e07024400d4200d030803182114401041c1c8a1030400094182c1821001d0303084a01c1c090710141005c11150111688540c503134190000000d000c0c4003441d005240b08503072006441701c9203540f003050204840c43c283d82c01c84150003080c0114804e401d503502030820081c5994280300709030b100e00302080395800c40d1258881c10342c007903403c0c0000328000a0101d00d0051403a00c10782c6a650a482c03501e40f040301002e4000070350781000c1441d01d0f00b14850019019034000da0000c0516590381107088614140c0c0245130100d045030303007000c3e404002c2660000160007100d100307500320703241a1140700003008400000e01a0681541c0a00006141481c20f0b2140100c0281d0152000c84035610303e4010561040711003405a5400c240108208618998848110014030002600314210308010002071011300c00a031a1003458440800c95181d2220640c4016000b41003c41d40c0054000252034080c000e0201c0b030103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 868111861 1250 868110611 868110631
    0x31b0e0d020612041203020f04050d02180c090f06040f031704080703060b040e060702060c0a030e070b0c0f21030c0c1005060108013809090a060e01120305073503 71
    0x42288174850090003a640c0a4440120080c1414105000e000654101d84130503603002da02800144900b4255a030800e0241000c0035006680c3d541d070388284800c210740340d00c00501940d010031080091082c4000d00400340d95010b00c2101e403040c80351000d45568052a000074010303000315040041008165030050a8a1505440900c44000c03902c0816032202021641600560010340010314418170500c020207000071170381000206c0e9500d00b1481303031a0040a81020b44c1d401c6001420504a880c100030381e4035a40d03e640b000703014a01c6400c3c2041e1146084003d00003100c038011020400010210f41612015031684046440000004903508080c0006441180c00700e07504000110303100340b074112200000740700101400110f0410042014448007a9400081e07000000e200701c0d41c00d80e49140410740607a600700004240d5904240e1a03640200e010303400100340c4075130705c0b001c00c001170b8004c01aa000a03401c43c001690240f41c2500c4d00144890040108031340e81d0b0506990b6402c00b0000c2e000e1805149510 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 868113111 1250 868111861 868111883
    0x216060e100309053a0e03060a020f1615050f1806060f0118030506010f0e0c09280302040203010b041a1206060a030605030d030f0c031b0e0d02061204 66
    0xe0401d60888180381e4001d80a070b0004001d4041c3d40900880055a14400c8050000e080b00a201c150055a40617107135180050410844202203240410130140c22072a050000c500d4001c407811085010300c00d02450300502c0c0210343d02c90042c00b041c83e484594180a881c01400a071514a480d41d04986080302d10740c1d80c049401c0c41c000700082d0001050303071192402510085050800000545100b200d00000d2070186c84201004800a1002e0090500a0851780810320500d4101545d81d55400320040c20744041e10002d00036007822b07945030023420240305010200d2003600266001804001d40c5aa040690814000030000500d106100014422110006441c0c030400040c1d560b2008244078400c102e0030075003d09404504a031400d900200a0401d850a002a91300d549501190402c14800300f0000401e5554030540142041d80c0200110417040d86410425007441441c18404241c03020020020028243e013849107548900c10001ca0903900102003903118002031880007501c1e0700480d03003191104464 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 868114361 1250 868113111 868113139
    0x402030c03220c050d0807021305090f010207170919060e182a250204051e01270501030f02180c040905040f02090901090215130311010216060e 63
    0x80314403800740b0761080003c2d09262500042140c022003030442628000020040b080050743c1d60643c0d080340112206000c50b461a094450300d0611807103482c950150b900401c10240014a400c0000e4088003e01003280d4881d0070440204040014010410480e2041c0c00d2010400036000310040441d40012501c0102c000420380c0d2403010074900740c90242908516640c840d10640442c540c9051004030504c00c503082c141002400c00042007005005080c00592810354415402c1501400342c0c841e046160100b42d10866000400002c1d505100d2450200da404a0b03240c000300c0041d0b01c903071106040d410140300c035584904107105007440341502248240c3c01030190f14142c203031202daa1480380701031000032400c0500d400d4040c0081c100003481129802600010f50300140d0b1a07035203080c010f0440000028461040c1d2040c01416980c0c01c041c5400070905000070182c8440d0901b8142c16070390b009022103852444030740141d14285140110341c600d045010b030013040c03059000b007000201c82800c44840c5102c090b1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 868115611 1250 868114361 868114411
    0x50c010f05030109091e03030c03060b040302030a02010f051911061e04060c05120711100b0f060d060803040605070b130807060c120501170114060a061d0402030c03 72
    0x14010150301085040c80100003880d00d0f035004224450040103407102aa9901001d40500d540d070b44400c0300031948da44d44031100d03d64180300f580064041d50350418600717825a00044d40d81c00100000a042005065428401c0b6104a007640c60301c20401c0103050010b541e00d44090420402d08241150360700c6014005500110398481c80822851011074110490f03c6035212000a464003c1504040c46000c20280705801c1452101c0751190034550b85450385040c500c000c150034171143ea00605139007400d001c40340c0b030b1566607410341000c4500304448a560314100e40064001030106540903100500010500181c3d258000c1c00800d856407043c0042e2409581da08159000200041000340c1452024441c02d80010410340c404a0a03544501340003c00000750b6954000f500c03c26040100030009220307940601003003d000d849082c0d404c9038401106841d0580210307040002501c900302c2088408100043c070b0f0722264000e24100c10002c2d006650300d140c80f1040c540c0541c02594904668aa020004040424 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 868116861 1250 868115611 868115627
    0x20402032805010e0c03070c080310080d0207080d120603050304080c280504050a0b090403110705010c0809060310080f0c0f01020c28090f050a060e0f0a020a030f0c020a050c01 77
    0x901c582c1340c0c280c0c5842e606600030081d00010035010610694208100101c3d5031800036610404408500c0d11210f410202101e04081c140c0306040d040d50320408060148031004203800d80400054606101800c1d96420f41e540079203040c1d0700c0945207000c00a4041000c44c2c010488500800080e43c01d103102048000e48021080030b00501802051031240d81448076103040c1d005250040c0c0c20481c0469542170700b00001d80041d10070388089020a004084007010910700b4084403005050034240004281c000c0c0d101c03004180305002000b0300c5503200200048040031311600c0301e0041c1071a0070848072016041c0e01242d0b038598a03462060301c2a140c841d1390140f190302c0010707401490403024100c40b000d5000d5401c10303401c07445400c0c41100303202050140410070607100d2140b2190156514070108841c1026900501154600d03000f4403004c0e0f24010402004040d09250640c0000580d500180d030f03044104d40482c028a080701c00b0182035402c100a1011803231b80040d0341001540960196001c2080440040d90291 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 868118111 1250 868116861 868116869
    0x1c230a050a0623040207030507021809071a030414070339120b07230304060b06090307030807050705090c0d0b06090a05011407060510080601062d090302040203280501 73
    0x4508101000c1d01030130250050310300035200e0b04025080c02c40c82e5002400c4066140c000740c1e041e00c580010861840001c000c0040144038441e0b100e200c01d00c205540b0700341440300070405025001c003d8685184444100899001540c00044203d044900c604e0040150b48404c001d5503107140809000b000c13201244800c1e002206d804500c6d0404449856480400c0b07001c0c000c1002c000e00c40c000c0c010040003201d207200c03034900364000040f040da0b034505440c000003112040361010f40205803c2c001417805440c002107000030f03642c0181c0e84588401c161b240251908580703801041d0880109000d012481d01c000016211000c4000d8090103041c00980500030140030380f0b060540d0040c0480d0302088254041c0c60302c42886406a083c0c685040c282e81c9442c415102d09440071400b050140304100705032441480528090709203450702d003075444030713503107103808030040105101000d0205030711071050150185640030001c40e4050b00035500c0c0e207030500c50041056103c00c5c030ba41207052440724a81d5004124800c481c169 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 868119361 1250 868118111 868118159
    0x102120402010c0501061a0a091a0714210c0105060d0b0a090519050a14030f030411010302091806040f02091c080f190e061c230a050a06 60
    0x3951250011580c1402030141a200e07556254030100b07504030004900a000ba951950075039403402070b46402802c10000c0d600102103143d01c2c038002440800b00304100c0c0d94860b0402d4441119074846151070b800c002e9518520201800c6840c4060700c41c64004c030107822504001d0b002081903550f0344003403005860701c0e40d000a05404e09200090680480c40d400050a2070003103003114109194003103001c6643c0818034003a5500c1d400b011911040000f0202c0d40039440d684840a50306000e0b0424100300c0c2800050030060900306c0801c0090480c0c1d119a050302d101d0300d4010600d2029113442c0340700c2030600382c00351a2302e4001ca00b025280200800303503000b00c0c1c3d2a0035000e00091002040c0b0135010b03001c140e584a046801500070403a0144002c0108040d2200341c88038520201c1d00203501c080a0188a0986a848d0140c007040c00301c100c00710700d82010b901940d0121407010428088507400400000c4880b080c6010400907001800b01c0c118650340000d12030616602d0400036692200c40b82119403c100740c405c3c44c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 868120611 1250 868119361 868119397
    0x10e091903200303040b0108060606070b0a0f09050604060609060b070503042903191a010e0d020a051002100b0a0f0618261b150c2118030102 62
    0x2e1107034072032000354400384000041c50b40c64001c1003400c1d940b0070b441c140c3d91079000000600881e54140101e58020740b0444040d4a4580305941e40032724400028181599207690b005001e01e444101d07040207911036401016143d580c5040e180000c01820b107801001345040c5050408142c0e69014400c0382c403180d800200440c1480c0c42d001d0310340440c0c400b80110f403801a000304040c24a000403140510b0181e1221110042c541c040700040004560401e00058000448038200302e81698114a2982084034261078840300094940081210843c1c1070b440107400c9400082c904162550218024104c00c141c0001032100024950402170401b20328001e0a0032605507841c1000704601441d040c0075041121000d0164040d641c120500c004058003521010f200031101c0400d2206005104844c55143c5030300b15a9101c510f0007012412811720720070401c03488100012041c00e01e1204112501e8000c6152020b10b5095403c0080d100c116004242d203544002001022034900d8a010300954003440e4444c000160 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 868121861 1250 868120611 868120613
    0x4111210080c12010209030a140c06090d0f02030a080a0c0b06063c0403140c120d050912010c110607020d120506040b040e030a0908070e07181d010e0919 67
    0x200d02c160f4040700c80300b10342d42004200d0a0340c60510400b4461805007030282180400720404604003280c0d0745032144140003c015808165903200750948201c1c1d00080328161035031a500c0841e02d040381e032034405080f044010408110182c0c0c070412100d260341c862903a882c0142c85510a0208901950845080c40c12a52803210800a0606400d403d200c103c01101c8800750403091401070f80c1e600607081511000a6111901801202084030041800d4147d44030304c0b4600002c1e080584890000000008002001844a0155552035503d201445800c4000c20411060301400b034010302d4400c0d14051300703000c2e0030000f0314001d00204000e031001c20103848141540c40d01441400c0100401042d040e4800d0b130702c00c00195191210321400821900303a000444d629002e44601411001c03a0b5407000f101130b070003880180010380c4a050380b190400d03013a0130900f1070703a41d509201491078410707034108a440907a4500f810703075204002c41d031003412207168882d402c03125140e0425898581c0340380742c21440744038280d0b02454 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 868123111 1250 868121861 868121869
    0x10e120a09030804030602271f2703050c030f0312070c150f0e0a05070504180b090d0e0f011d03010e070905220b0703090804030204111210080c 63
    0x3455444500d840061261695684602d54003e5001510704a5000c6684030b0480c440c141c4081e08185200503000b00001c1c074400160103041101d8000c03001c000c0d030b0a09401e066025000301d0707081181c480c000c1a10354589107006440b0950303501c070907146803084080300125800d01160761050052904003941c50203010854448091401401240800c0181d402c10800b00d8000014040d98400d040408103140411942c59401c0e40e01c6c8100000d1241c021442600010300f00045071801c03288181c5010410b440300340748071124803622040207803200a41d0410041c22000105075407204030b42c0d58892070100e8000e0028408110742c6140c580d404100300070070481d00310800d861024490080140081ba880120600c0d0391700303100c501d03400f00d00550b40364010300a50624082405120000e003400001d0a030b030041d21030258007000581303000e090550354281e0000340200c10040703401440e00070f00140301e211400c4040340442c2d44180702c1d000040c0248008030316070b02c907402c00746011504118024441d0a02c0c40c4200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 868124361 1250 868123111 868123117
    0x1a121b06090901140312032409010506070b06120d121103060d0b0402040f02220e0f0606030403020a06050411130606050904021309110307141218010b03120306030f010e12 75
    0x195141c4642a08406e039001004011441400042100240f104421290900186550000c0c038842c540a034018000b50725131030280c8000d2500070500c05002d440e0f0710089400c608000c0c1605400e03000b00010303828a69002007180083c2c1c40000c800304462651402889101c0c00143c0300160310101407858403000c900030200240d0030074001840000d1000c0c00446c12012640707c2c403207421800340c03079200544a905400039042c00415440c442c004643c030340b0182d09192a1002003d40740300380707804004113050500c20000210600ea20a8042209041605000b41c151350705004d070710b10a20314001000e0800845010303990455115442d01c6042c041c5100802001e900210b8800c5604d0b2035801e400076956040b03024100302c200203407517820b54900f0030000c01007900440f5100f01020043c1040200d01d0700d00c0c1268000c1e844021050070076010045180104d024002028600340d0501c1743c0100319100303801c01c400441c080c400481c1241c680d20705a580c07140c00d807004207420700c00d05e411806101405a40f040e0003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 868125611 1250 868124361 868124399
    0x112020a060f0315180e0616110708070b030a06080307020a1a13091410060e01123c06120b0408070c0b03151c061a121b06090901 57
    0x1001c12140142243c40112074071645c00003c13001d014824024507801e8074402c01442d50301c0e400180c0038a240c1608030b80600700780c819100c0c1c2045080300c00045440401e2024801401441007035035445540d5040e100c00c00e41003a62001451b52400000180800340002100c54036a07010b4101c010740741c40c04c01d0400585018440940303040310704200b044401c11902d03020f030014144801c0d00007680d00f186c3e480708405c5900205041150390307111000b401580d4020700c40d03180203602441c100c0b074850304081400c4007410159030b40c2c449111244101084940c0c00b1046460b0700c0382290501114940380020440a03070b0204e00c2a1501000300c10303504004101c600c00c21a40c045d01401d10300746060360765510031141844640c00300a0000c40441449010071402d1007038010400111800d20b2552089060405010b60751480200020b5a9048086101490182100305058000c3c002c0001e052201d40850b02c80405010140e40202030700100c83c181d00c2c181e400d84501d1440500850f645a00b400103c1c00c0f2101e825035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 868126861 1250 868125611 868125617
    0x203061807090204031a070309020303160807020a09090b07020714040b030a051f110f0313060b030d0c06050901060e0402010f090302100905031b010503190605091e0112020a060f 78
    0x9008109807225000510046200300841b03080c100714200403880642d4040d01c0703107040609000d540d901683c0d000041d0f0b100b41e030080e04000300310000d5180002541c414810000d4102c00c050740000742e5101980c1c4240c115500407030341351035507640d03020f82213854923610f0240810360388401b201442281421350022110480107004c6500e2082c0c551245441c09030340650903848001c06030041154184140a200c442400a0b20b01754100805900c0d20340c0c103800014071042010299400540500400b03400880700d04c00040c041d15010361150030018004c0c41c01400585403503081801048103c001480f8407400c4404d074003400c0c481910345500440d500558003402c3c204110103010048050b9440781008a40c0318466159071080030700d080241801d04402d100b841c5580c001c9620200d40590f0088100c81d03110643c01000c42d48150364403450302c020151500501c0d00075101c038041000e1600c1c1088001000044a030f50051076a90f80e261300310001e540014002c0d003115200b48c08002c079a024139080140403030241 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 868128111 1250 868126861 868126873
    0x30a020405040804060909020a120f1b03061511070b0a020a0b01080c04061203080406050c070602120f0f01080d0f0e0d0609061b17061203070309050301150302030618 73
    0x1800040c01e80d03209960580d40c031030700058108020b41e082440000204440903096040c000d1044d4080c000840380702e240410607480e0b1203680b0300020b40350f0200f105c40fa40080c1a40c00d0009401e002001083c0e24080c0480b848132484105641c83e00500f9541039010400000f059000d0034680794000703c0d00540100f030194415866141c2c001003000d20700c180600f035050000c0c4000d111410401c011780706181d0041071866001c40182d008a640b0220491740a50800700104d5681c81c0e10390040c1940c803412001900c80303440810300c1e032405032000c04c580307001b010320b03c5180510341c8903140c0d04040c019080c450503401e44e10150310700406901400c2045505642d40c10410f0030701c5843c1010a0341070194441c21185036503281c805c3d20802c00702d48903000140c0c980c140b0031a41030a031102c000c0c120440d4101002c041c0700c10380c0f00140c140e80e80d410440350710703403068000d998483d05070780b8015000c5c403498001c01d4071039424010010004060480840c003201d4000700200b480740c403034200c40210441040c1ca001024005c030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 868129361 1250 868128111 868128113
    0x906021303030e011b15200412060b150711041b0203030402090f0106020c01230703050c060a0c0e0f0d1211010513030203090907090302220c2c030a 65
    0x5080c0303090055000340c60380c030012890900010000354009090009a05082c000000400d5680e00590300341540d0390400100058510880000005130101d000c407000000200410201d619008890f14a44284405e102c21202081017040a010310b40744610380040a211480c08100c800d06080c849030400750002500b050046692103c007500c41280368050780c80001403104504046c040168064a103400114040d4103014000b511600003c2c02d00b41000740300c0070349100d80d800301540942004424184c07199145c2c850700d40a01603400c078420610301e5014080000b0580300850050300d00007091941c80b04094085802049a00d4402c0309041d50044982103a0764001052000c512415589035168a001e00c03000e840c0e800c1c2900c1c401402004c9c0c4654401d0050000398001040c1e60920000303d86584040e511604103c0300c0d03540c107074006540840751310700800719144514035610001c020201d00707005480c104481640c2c0c111080010064021002442c000440755800804c42c2c015002030039240c2d64901 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 868130611 1250 868129361 868129387
    0x303030412050408060c0a02100506210f0f0706021014180c0d0b0a061a1603121104061b1a09010902030111090405060102070f060f0c050d0f03200409090602 69
    0x10484410300079440c001f07101c01a540e010091913010810300e0800b0b10841c40c001012410f000d0300648200385900381d8503050011032000380b0544061100100c210362500341d001e90040d0f510f60036440740c02d000d8000c44112400e001480d01401810003003c0000a4480e140c40c0c203d032010102c036203008011800b030031810840c2607071441106000c4078040e55801c1100d09000300300e002216403552204040b035000c0802583c1d21058a0107803000c1c0d941c01d1182240204050905070f50951001c000da881c11468501013019100c040805041640e1965075280c50a0f941c42c2d81c0c10300c050b5100800604545441c542000218107648507542d8030005c1c40001080c040715940c086030a40785a00a40c061000e4042107522080c00c0c41d2043c01da10800903c005c0450600d05582403403103081c1402000100b0140d01f40c121175450203004080c03d02a800300850b4458228120001c12502540c04040d00090408207800d0700d4440b03501031700c039500d12003110b141d24240c0b8124141e40200400e0400310385040c0c09000c00302c44152 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 868131861 1250 868130611 868130623
    0x516060e0a06050c04050d02040207020409120c051204180c03150905011502010b15030a110301120c05010e010f1803060914060901050c16110907031d03090303030412050408 76
    0x1031108000c207890503003860a8015101c0050084034a18001d000800c95942e8480c00c031281a234041e2001030352241c07103002140240032071880140c4544a4504a080c03c5135000350008842e9008500340d070102c4080b4072400155108507c240c401c0d01c2a903607194102c04e10b05900089421115040000c2e030300504002030b0403d082c41b03900c1400c010350303070308010030400144821401c03002c041803008112190703000e0002040c0207a400c07803c0d0315070800400001c80e0071102e17602000003004d604041c552a51307500c3c0b800341d04034050500121001c2440701d10014065024081d20556404161035407040740024003002c0f5110158a6a000f10f065140100080840d0355449040306150003103460f10300050868003414a4820085c010201c0e42c0e2500c2c3c10000e03125210801e030381e00c0010080426001800c2824440c8002110081d21907100404000f40718800350160f2041d817a4007000e00e681d03101030502030740d20b82d02c034040c460b1215056081000003800041d50035055007030000b400d0034803d0a01d034a4041107031503e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 868133111 1250 868131861 868131881
    0x23120106080c010e090106050a050f0f0d09021201110417031306090e1f0509092a01020d0e03061b0c010e030a030b1c03030b0f1206010311031c051606 66
    0x3801400c410056541d01413000c00faa1101505c101038154500000100345210f09501c5404002010038580c142c80c06583c201d07440318105c822482d80b036802255600c80145000d00c0228425940d50500600103c010701401d004501100c090f030303041604d8003410032103910b2240d481420394081040b03600151800343c2c2d800030290800d035551004260900720300c58141d400281440124201722962100700f030101c2030500b4152201981c008100b61a10030915103001045016003c400360803503e101c454106c1400040d8100d50240c6c00c41d0000c103021070080e0780404c0c81030071403901900002c1c005101c6603807040c00b800c40031201010300351800703020035016821141201c4002e01c0d0303500006403400e54168140950340324031000704c0d08071142c000f50b41c6081d601c50103910b50003400e258649030030426542e03a107508900681c5016007000c0750f0260b448c11040c2c0b0392009010440750545000e601030340300c0c24000392554041303405942065034400100400c4e41c0c01d420003060902c050b420000e02c01c00150329400340024103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 868134361 1250 868133111 868133113
    0x15141803150714040b091c050a03080a1a1f090b0a020304030308060f0f0f130204080102070c0b0933120f070318061503021504080d092312010608 64
    0x10b00348448000c08084088403242408003003800148011314448040f1401101c089600c0360741090b1100c10080d1640c41e03864007400350300424400e4010b058210410910a0742220820861035410041c0c001040c0c1c4865281c5411100707a00081d003541040410380304500c01541444015980d4031484444141d01054584005800100e41001010b402100250f0850b00c110380c41c800351420440418112103e90080900c0b509120128682c103803100d003007a50703003407401100565545845181030b50107540000c0007150400d0034107000180010411b4182c52121000800a059082519039045080c03000c00f000301c0118415130030101c900300346520040000c2100100da10595103003c2c91080070191008064000b1b140c10001801d0000d036400c03d10612146d403000c80004c0c1c0718074a00d40410800c40a410080d08101c0c03078003604040f015450003500031030303d0b04022a40303610003101007194940318600c102a800c500400b000d002d002c1120032029980e0101a0270a000c08050403074082c2034801a03800f0101da = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 868135611 1250 868134361 868134403
    0xe0106140d2a090819121e050c0c09010509040b1909030305040b090a080409020c101103010816140d03182304021c0522060c030615141803 61
    0xb41a00304960000502100010b41000c0c504e031804150200d00d42c20009140b40181080402c4a501800c010112007645500b401640c08050718064503540c08088041c8103407040c078080c1d14041c81d11401c8036040c6c80740544000500e48980d51511218071018185001400d00c510345106051154845c2804480c0a40c0e40441c0303500700ba00f45078404110142440c04070780c01c42000718000c40c0c206000c4a044920340200160b40d04202c880060622921405100c8143e044c0400c1c100c441341d00c18080c0d0b06994100050303074001c201c1c1e001181000c4480340701c1d018500c411711107401000d14101c810702c0b90351402420048540c104459032804104016084404250be00700364003c1c00b10492050f000c001082940d0840c17804070010403c4000500305008a162140c5900000d40c03400f00048181100200e0051402c03050780c12403030410064414000c503040024070301303480094480800580314880c0c03110303a114100b01c00c020085000042e40589030071010b10001941249036602c2c100076280c550804607881f511 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 868136861 1250 868135611 868135691
    0x290f0a05030a0e0102070b24090103050f0706020d09030b1b0c071814040209040317070908010b060f090d2108011409010807120302120c0a0c0e0106140d 67
    0x10403503a440b841400113a1041c0400d000240d040341003ea004144400010b4005180e0a5403060509404140c190800d81e050b00000802c080014003a045040140940d564035441d1030302203a403486500381c50380c000b4508580410204000c00d0070107400c1030031102e00410341b449130040700c8800e0344510722492035980300907000c2100b04034580a40c4100e1301042e0061280d4403051951448114020b00701a21078021074000c641018002e52031402c50280344454100c40e45041c6901421100b6103100f00b01c100c1d400d2042420303507813401404881c5090400c850503401e00e940c0c0018030000e00106441114121040d0b136100740d42a440d800c2c0f880e0303c0941643d54103410360510582c60070804003c038045000344807110050118601c0414100c040d0b48162148680079412030404a20302405c040039007041e07800002c0c54608800001c5041c40c0814041d03000ba00072140c2d11324020a10083c00d11034800000c2000c82d6a0a441c1c10300401000d01440001000ca501c00c564840761102003c2c85108544442401412030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 868138111 1250 868136861 868136881
    0x9060b0c06092a1309030c0c06300e0115030507050a0f0501080c070b01060e01080f07210b0634020609060a030e072706290f0a0503 58
    0x50784000035002a200c4444510440e0900c480140880441c0403c800c0c050700d0b82d61180e20309521000d40c0054140b0444805050184c050b0410020640b0080c070809001324085020312114014600540001303401424440e03030203540040e200d1396403075a0b81d413590080c50001109000c1c0044c005100c40480c0c82d210f2a41c5003061902d1311541c0140c0c00341032824002c00005400d107030345c04100c54003800c0080d8990b60700032051403980700d0030304010410b01e02c0314004903102d548501a03200f004001e1b201c80c121038449901001c0200000c0740d440e00012103101006031054a00c40d903240c0c015507061000305030110000b000071516004405801c1c1c452130030300010541c5d00015440c000110101d52081c090040310303a000300b56588250f010390b0b80124ad00249000d80288654406d001d600b11035802c1d60745031510b600c110801c0340c06403c6080500404c11190b0040a07526106a008884906549408021560750ba5141401c101c6251100d004e1085c82881c428940320002000a0302c80340d940c440d501d1410a07030013 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 868139361 1250 868138111 868138123
    0x1803070e09101a0909070f03060506040b0102062a0c06040b0906180703031d1e010815010c11010c150b031501030b060415050406030b040b01090b0102030a03020a030609060b0c 77
    0x40a6607900f070500110340401c0c41035040c2e0400301c090b20070307040d240d440400c050b00c1c003503035a0700507038509007900d0002013440255030089004d80f800311401e000300100d80004990710001035602e1070001c1804a001c80d02025084035100c0800d10300e1000382e0529403c0a441820300700c0c00c68040d52201822410440d07042d01c00e00610703901c2020a41d03c40340841060022550310001400000c043c00024503a194515a92480c10300c5100360041140d5031450110804040a00665400a0200b03a0890100d9550300c0101c040c0340c4c0b4900107035211206081c0c5138883c80074401d00c01d044e15050240b130300c1c8048040740b0400c4d032045820409070030100c0c1012168044c14601511a0403000d41503907400d00500005004682903504400304503004030b54030441e41c0300400c0c0c1c031551b0380c08140d0242c5040c1001040003041003d40c0d204d14002c040e0140180c1c0c0e5220b0b00815248140511401a082041301ea050140a580075080d58403442ca00007680d5911250b108003154510b40240d0300110380401d543d030700e6000030092 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 868140611 1250 868139361 868139383
    0x20a0306030c08120a0e041d0c092d0c0903030304031d01080106050a200607030b040b060903060118091707051605150705010e0601060c1a0402030c061803070e09 71
    0x82681d0160705030403607800d001c5c501201d0b007081384100400703042c0c0e92241c00002c442800c40404110000c44075014680e604001c10341240a041c5e8900020044511800741010b180409050503000b050220035400c07020760000e1041e030302007a041c8603103240351310208040d602c0b8500c070751100d031031403000c001d4019507081c1c07036007195410485507a006020040d80402914080242c0741040340f000c4a05400f408440c515000000307000e0700c140300405c000e66606402c0421411001e4804120440000081c0480c92113076015480d00b56100e080108807407090702d84003d40404242c140050704030f889a64040300e06080d0b02003880038000104403102485001d01440040304940c0d20710030b807114504000f24404081c1032181c3c0074018004a860b0061010270f40164076401d401c1d60958005686801000d0324801038600281d4103003183c1c00002880300400e11019005980003001800d000c0b0301d00c020059507a0204071211460000700d0b030703030400c0740d20300704a420050311145802158500c0d00d02055407410512003c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 868141861 1250 868140611 868140613
    0x90b18090f090c0411120a0b1518011b0c0e15090601080103080f0708030a0603140303040b2d391902032502010e04020a2f01020a0306030c08 62
    0x40c04070000001a04a15000d4159004203110b034010311140841d004503500c61090220100410840601030ba1100e516900111030b850b0030100e9410244000e40160309080f01c020120a580b1200d56019100c0e0b0033607407045400d00e0b4500d03041079660540303440030381e1300c103c0400c482902840190b00c03000780b84000307a040c25281074019103040d40008045d8041807001403c1e003180000d4852281e010b88040314030303560700000c0665890400a41c11001001c0754401903d2441c01c08980000d00034000c0100e03401030382c1000e07c02c40b164403980b4110308115644007056088581c0d02403540449514051154403c044c2c0c0c0703d840b50110b10300c01c3c0400a6034840c0c4418050800c0d16454244000450000c1d50552440c41d0440104026000c0040e455480745250000c8501c1d865403410b40e44048010001003110301c00c1c8e880051f4020b809003800107901036a05030001007480e40c10783c203905026184100c610701e2440540c0040110f102c005250890340318066a5000980307800d0280240003604419000400c0004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 868143111 1250 868141861 868141891
    0x80706030e0705120d0f1103040806190603261603080a050901020309030a32031816050f0301061e050a080a02090f0901060312110d140a0c03090b1809 66
    0x4e0440d456611360800d0341e09102071110100d009a02c01c1080c0901e01c2820b00480360307542d403600b64a5507248002c82e906203044040190500700020b4a0254100300d0f41d108007151548548210500d000104110320b41140040034000354180c1c1e54683e0204480f17034041e032620090380c10080e0405080d00d078005c00307541c0b150b030040003840080075000003107c0381c0c48054a0700c0d030014600c01480c260038880020300f043e0004464040c0203251502800254040c000035030581e24003501c0c102c5038589461503c103140300a024280c40030011404d000992040446c001000010040e0300d074100c09990340500c01840101002c0c4240600050824070041030240403900024540c8520640c002210b8403001000100074854807001b04070308003400d4100c003002d10707403012150740400000c2000501e2025598000c403118422904807a00c85070080c1302c071404c0d041d41e101800d03203810284402981c56407900b940440400920041c0081d240d000c6402805842c03103800c140182480484040145816000c0c2c640d2603205100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 868144361 1250 868143111 868143139
    0xc0905180c040c090513061e050306040f0f240c051204020120060405030d06051c0303020c16080a0309050105030c03010e070309080703031b05041815080706030e0705 73
    0x16a94115080449010541d100301c0841110304e50b0103503201e103403c900c1e880886c0d64054015040072043d12101200105a400e05142c00d0000d21164880d80d905900f140003c00d02088401c4008840b4900842d112601103000da13850342405050100c418010619000c900c010408080c01002c56a490360320f445400c00034070b042103c1020b0809000281400840c00903c410100b22100391300c1c022016006031803003840c040c2009900ca40c0401c0480d8643c914007a0049001d00e040c1508000b0080a613889803480c50a5940540003907200c80341022461080010300c0306464072007031051026086200c06000d074150302c0d26000e081b500554014038180401802003008402d000302c25613045411351600a0066141c01100f940100043e2901a0242400090480c2451b4250700b0640c039401815200145082c0840b5040701c550003603004090100851a580000da00c945412016041d003661900000043c0d45400e140d1500026038400b00111b91140d6488078200000c0c821b400050409841880c410408 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 868145611 1250 868144361 868144363
    0x20d0f0203040e060102010b0d05150f010b0a14040f0308040515190e0109030210030b0a140d261b0d0201060b04060c060f0617010e0a03020d1d04090c090518 69
    0x142c1d004012242800c180040e40c144e10075040103034030300340140c00411840d02130b061154569a9041d1081c0f1008801001f140c590091280b00b103040322441c000407810310005d840c0071200032425090002504205000205800311070606000095100d5101c540d699858901800b0558403803000f00c8040420601ca000d000c00501101000c1408442c64502e02d034000b00c0c401030320621001c1c1c00c00394200b0362000e6186181c507011381c8482e2250504032250002d45683c0c8076103a001a400d0807140360003039810814240021240c004603112120304017402107071841c08036460100c5410120001d002d006415110419202040c040315040924130720003406100e0428000c00c405100b0380c425001003081c010380e0700c02400b4940d80030040ba02401203050210030340d40c40e40640041d0700710844a0141d413a202500300c080800081e0340c1001545a0080d12444107103d1051301c5c050b40310003aa41043da02c030b01d017451050f60340d4416a00e04601c159502040e00d401c000c42001120f00040203c0001c803d402c28240b08458 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 868146861 1250 868145611 868145617
    0x7110307030c031b0806131406060f01030207020d140309090108060c0304080f0c0111041a270607060c0f08071701090e160305010e06220206091c050706020d0f0203 72
    0x2c0c104404ca881c0012080440d002d9442640c48403181e03004881c00d00000004414110303520070302401813081c00750020742440791106001e544155000100d200e8001c2d00354007a8002d4000c460004100d03114891301030701e4040b0030541e410480800d40d0400550101c481c54241c240b80e01604103140202a58600b80c0d020003c02c0c40301030000703802c040e000f140742c8400040000855042d0010702c0300a10001106030391149050300b1900481e83e20070110350440b2031408011041e200d1031404050340c0720190b1240142c03815540000d54003d46c01040810819011a03074a0040b00300d002c20a40d2810313101a21140000c20880c3d018140c5000c0015401008504c0340140b220a07040d11030042002a882a8191a007803400c9070009c0b90212a650b490000010300406502c600000c2e030010040e01c1940c0c1c0e0754221030340b00b05040300d50700804a016803106400350815101030003034030801800c4080000d4955004003102e83d80003c08840c1c50784410303001d01100794144400c160803c242d0034900710341c240d82c0d0000b07901e0340 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 868148111 1250 868146861 868146863
    0x1120f0303091e05160603020f0313060608120d0f02090303033d030c050f030304031403040306060311040e010203060127260d021c2105070507110307030c03 69
    0x42e2110407040510081200d403294500f046a0f115102106600d00300303444608401c0c1c4c910b00343c0c1c0c4000002803454041e000712a81120745102441c95a518120201b040090340ca206481d06641c440300072850560812a50000240d1809081d40364454101c4030025510700c652a60b1000740107001d0413041ba18004203403508808011604c0849060380c800082c2d588010a80010714401003002d40307032600c5006a018429240280643e0317040503264400e0000b00128940b0303c42c0c151340100410008180b00c958080b502c15080c20a0700c0c645603480e103135503003034520b1a0400d5443d07c49001d00c0349564545881032142c03002010000354190301c1c0c10000680507200c01401d01d10510000003201c00748011122a0401501c0c0c03e02c0741e00842c40c23509541e0480850180c0450209226041007001140d000007165000c001400700101e41c00710709814200d07409440d034400300151160304a030031060362149014507441000940d13034050322915107060500c1c0180001068a0080c1c205000900126010f000b10074152 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 868149361 1250 868148111 868148117
    0x207090606050403171612051b010e06190b1314151e0a051005090108010806040b041509051f0b0a05060409021608030901050610022b02030d021204060501120f03 71
    0xa000701c0046d002800285500007020360a1601c40a80950741102c01b9202e0301b4180414185801c0d5100f0141e42280d844a491244036440107001900101c120351285024403600c000105140350740d5000b1500006400e01c3e80c045003625200900d4404811000055010010444c4130990406640101d0040c00c0042000c6154400009a0000585645400b84010030001d484400ca000701900e0091850300811105400129654000542e414002030114005d6401084401c41919103980342886031040c2800085034540701c10074840404d00911004107203181c86014000440c11007200d1404803410200041d101e000841c500b0300c1b050b00c50f2001c0c1d405544041c03000582d5503210840004854a402130001c0c0390200c000100100740b4019004680650300942e110a0b40284503a0141c3c4c903150f190240c4220419940f101890120780700444407840020303401664030700480c05030260242c0e480501685030120151003070004118a0b44905401000103000311030401a0701d81c4e81030000261480d0107020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 868150611 1250 868149361 868149367
    0x211a10140f0d110907080417131d090c0d05101a090a0b0f0916080601110f0606030f010c0903030309020f0a090c02011401060918140106020709060605040317 69
    0x256032180c15600e00076000081601092003958640200c0075141c40c0034141c05500d0460100d082540140211802140d00c01091900389408403c00c00480c0c0200a400006020b041800200c000405400d0000300201c91080d50031403600300c0c034030351604240c4d010050040c44914400c0000c244041014214056100004502454200712050030030211190b031540c000003440c144454241540d20504510b032081c2c5071032030310b18956010051074020032903e00342240b210000b40b04a0707510452265500500504009040400d45d51545207850a03007001200783d544040c0a100803840c1c10000180e030140d4890080c0401803420b88c2c02094506507100050a041e181c032a400300315078620840c20402100508640c40321660f88840b00f004d0000c0702c800c000554030f004143c0c440d0302d00b40301303030241030310740c0c1d0b846803402e061a0200304070225600e0704203900b001d13031340310304c590580007400300b4842c000c1c815980148251800d1840b030301c007100c0480e4000320512004000400002c2c100f00c07a0803403a10800038549403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 868151861 1250 868150611 868150649
    0xf080907121a0c040906050d11060d09211103040503070312050d110301181a100210021206090c12010e090c0306041b0902280504211a10 60
    0x18009814520064080b01c03038204000751851684060404c464079004180701095844040c81084051200041d01103284090143c4d4a130800000402c9485000c50700082c42e07042c940c403113030302d103050803002c9401c098509200d094900d0703031000050090442440107103160a14000c0003e545842034400240881c58a0402884443c01002954403110071002c003400225002c1c124464183e20034001c02486580351911044116500d1046080030700e80c0001e4540300000100401044200172900322086200b40d242c4441200d49078000751400c28031841c05107480c0d040c110104049400000c0010706402d90070700c440c1c0c665680e2107100604490082c90402c10300d0316900380d50b03800d10b8000742c491a0503204403020b100030000c40e06051440c0b81c1c10040001312b910348903004041688640e41c071400800034030003d001c1e15401141c2d00e4100e05416404d00c5480c2c81ea0b00d45640700c9000400d0486001c0404001500e000d00c414441c82c0c00d586102ea5190400c02c1c03800d28030b13040141200f8002d900d85d03110700c22100c407 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 868153111 1250 868151861 868151873
    0xb060d0b150a030f0e0d0e0108060409080414090106080717060a030b0f0f070e0a0504020f040f06030608103b030c01051e0907031b0504110a0f08090712 67
    0xe41e000414890301d41d1981801c40c06030103018480100e50205151200d402c65a03040841d50340e61419050b036a85a02d030881c4001114681005480c25520581d240341400c00540e41030300500050144500301319000b6105010001c90103016841384050101a10070010015031000d00c210010403000745408032502c403000031802040c01c46c4c200501e101050018000c14402030400c0a100c0d00f04054107423a59501c04c2c0d404c0b608180c00d00303c0b042c0c0048030000c09100c0303850300b50003400110005034803086c10140e444501c1010918144c1c00000440c0d0345003005d014126061099680d0740390001014050f140b0364012483d425032600303aa140d22400455841118003500c41d454a0004e0140422692150350b01020b55000304000da8150300b10084100080480180d11280705109001b035002a0001d0340c0f6607100d0b200c5855050fa100840014054400b00d401c2d0f032140f0840f03501b02d01c2c001102d52501540280500f0056256282c401444600002c028502200180803826079103001100d94034600545800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 868154361 1250 868153111 868153129
    0x2150a091806120f02030714030d031e0914010c1b08071401020d0b09090a0c0e0915010902040e090a0818060c0a0b040b24040c02160b1c0b060d0b 64
    0x8071004500c0c00d540e40e000e102e03544881c0c82c0d69500840654030095608c2103c841440b88840f58190150400c101411409000b0b40c001603030f010740c03503010050070344d01350038482d084650222003110316079601100340200b440c00b441000a610845e09141c02c0902e00b40750503402c1c041310488010400381000800e0b030104050000c4c0303c034100742d80c40d009540b40c900f20104030000d0301c086620b0501078407008002400783e920024203214499048400700b50715074100001d5640c0b20308014094511845640304100c040321000c1280c03802450743c1500181c5650801c0c011010b0780e800501804440d9016550510125121000301c0f0030810190f41c034907d20281c50300205105003e140c80c0204a4004da0744032000344000c4034080c2d40315500c1003200c82c510f60343c2c0345800e11034055035400511422442c4420303004a410907078482c8480c20a1070040700c0092105411a4451108a8100d0842241d011a00107442d8120003030720100501039481c103020303812440e0080b4040c1d004600090003000d07200c000880b4603407560000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 868155611 1250 868154361 868154369
    0x602120a050714102004210c0b040e0105030a21030905070e0106171003110619110c04020c032a030a020318011b0f06020d02070f02150a091806 63
    0xa65202c00b5510358110348a240c40ca40103180103007850040750162904052001540d08488501401e00d8200030f00e000307c200429404004001c030702003059012902c1c4900d000014440400703403d075203505120f54050204010784c4140e010b80e01c40303250340000880020445031203030300b00d000410040c0d41000f000c402828109402034010700541d040460720380030f414502c605a603001e0721030703a40b44800c2c003030000c0c010031341280c441030481146102800040c440c1c8003c0303c10f91100074551400c01414111303001403200d04211040100c0c1c1c0710b8100022400e4103012111402c075080310214200040399510302c0d22403040e0b0245006030352304120483d00d0b100c2c00744a5100c0104d81e501c126525076401c0d2030043c1d56940305803084010a400003034220340640c8500d80b66940450510040b80d01140c0301e90b140341201400d400100d0b000c94003030241c984035034110310140c100d450145080317082c0700f0014014032000405c1400d8119450400f0072103401e0341c0740c100442d04110344456400c00d00b01003034054520020030443e00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 868156861 1250 868155611 868155623
    0xb10050a030609051504080a0c02041413050f010e071404020f07051f110d0203090a05010e0a1a010b04060c03050c1005011502280204060512030309160602120a0507 72
    0x40c08014803065074000c5410398840c2048a084000b498910540c03010100d80040507004200000f40a03188940c1c04000c01d148013070000301c0c80e04081d128101076403c04980c03c504404100441000303011003000b80d0380041c440c1c40000c003c08081124095228882d90003100120b50300402d046c0020b44440d41100c20000d0b52452081d00c6410501d48140c81d20981c12807050310352111074400d50b25a4951080c0680410b070000a02d1a108882492074065007000f807141466014000c01c1102051003030048095100b503000140991314201d20700484c1c65640d40000f10444111400103101e00003004049038140c982d9070902c074400e0859440c0840e49441200010b900d03d003d41000521000b02540109050310341d2001c2100e0107200094040f81c1e540ba01484844501003000710100c0d40e13013030101030340074680c3c000340010030410344540c08241c1d0704c2c0c00c440038080d0983c000170401010380428170503031055190103205d00308400d15040d4002d584a84000000c5a110000990301d4191405241111030386a8062 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 868158111 1250 868156861 868156879
    0x304150e0307261c030b0d0210020f0d0c050601050108040203030c01060f1503020a0905040e0f0303040b04060e0f0c061b0604030306030209010b04030b041203020912030304050c1c0b1005 82
    0x7000940d089a546010500320b0340000c4030f900300400825480880409040a101c0e48403442400310045c000032001d035904141d1001c00580542c032145021801007a058004294055100200e149044603880c001d9003040841e030a41c0001031404161740d03045410900c0e18180c15112070001a0442c41a460f407540e480d03107440300003d815200031020f9421954080c50000108404580a801f6417068040702c50010b1080f4005006900d410b40c0804848484002195410b8100c40002442d551041d1001d50305064a0402c210400c4841d000355061106090040c1490441e0386480c241c1d14200503801d244200c0740440d0404140c114503d000503031807840d5044560600340350401400409a900099010301044c400100d011481d050455044a5110044004690b101d4603108004112a0300c3c9004040d0200081c0201c0d41d01e0710984040d200406002e941e4901b80f501e41076141c840c00410190103101d0400c4500b6200741009000004035800040c5011103940b1682141c10241c02d9400c00c1e54481c3e00b034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 868159361 1250 868158111 868158119
    0xc0c030403023c0901090c120f0b0301020706052203020d0f0e040615020106080705011209060b060f03191b030b0a030b010933060f0201020405090c0306210304150e0307 74
    0x20407000f404508007541d002c203450741c82d0740880041e10418503045011440111600c4412001980040d50502c2510000141c0c40c1501001030f099a1001c01c050710510303111003d00c4000e20380100000d03403002001c41c07400c11044490340c0180d12010060b031201e007403003081d081200038640520038075040e09000903c03c01c02648c0b1804c2c034915000340d03404107000542c41d005000c14800b000040390020b5510507101d06008030b1a5694260140040c1041190581d40710340074440c0070786443e000b400b054006079614503241e00e850307004904c40d06880c0e005072001d60b09200d01d4002d076411304001c2d42000302e0546404603e070500301020072540101944000c0100364450b00019400c2c45950004824040d0a440c2c00c101340c1c00e000001804c07140390061140c2c484200b07401041118020001006100d03242d000240c241550368001401401d401c80b21014050400020003c9a1402050f640d20220030700c42c42410001c80315268942d00c0c041c1d80201030700031552152044600340217554002942c8030040440382942e4903 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 868160611 1250 868159361 868159459
    0x14010b2b0e0d111c1205070903050f0a0f08070501150303180501020a0b01052701151e0c150605120307330b060f070c0e0c0c03040302 59
    0x102a28401d694001c480301c110341a403250b0500d4000f1010440281003107200c604280c0480d19040e1004414000b004c000c3d1860f0f002107000d110f104c0c4990380c540b2a21030b032039800c280b81010140d0340d5100306500140303039160000c4d1451641c029071079000f041380c5131194041e14011b401800742c00004250015184000001c141e4806000600c60311121040c0004568810040e07948170100c01d00140311041441c010f005d281091140202071074100451070703c6544240c002624401020307040000244032018002d600540c202600c0399021510f1402c1c184580c0807020006d0400340b07003200c014940a07100c000c0009501c0e50307812610190800604d14145410f080d0a460b5890f8004003048451746210148a181c01c2000b201e6050a1201c0c2c0b800c4011040f910820b0500030480901400c0d4441070034080700c1c10100100001d0307c2c2840c03040b1801400c181c02d01f400c422800d00c00402c207245044081100005e0303401c010007640c00300c07a8103a82c4124280b4006266207400280074040d0b0080c138449000e200e540c2c040c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 868161861 1250 868160611 868160621
    0x20f040213060e060c0a200d0f0204050c03060d03120b19050406050f1503040618200a0b0a050f09180a0501050915100c0b07030e01060914010b2b 64
    0x2800d83c0325045040b0340701c0240141d40c01400700402850300001e45000210f0364544020301c0110320a6103803a5807410043c000740e882c0c04480015035160303122201810850415100d401e07009124948400c0c25071503c41d0015600c8003000b1001003c01c00b1060345616119a140c0180355140070080c000d0001200309080e070203000d1030503c59240314504056000600b42088140d24040d6036002e0a000d442e09000f003030b1010743e83c0c00940b003214030380e40d1446d45e03040818211007209103a501c20341d20881c8a56410b2402007020348051506032152108840c100666410001103e114202da070401d142c40d254908400d90807405460b9041d0303003014a80c11100c80f120401c071805407060120020402181e601c0f0340500c42400d0044511580d0601e81d900c41080d030f1303d4242031f5515a04450301d407044015205688801c110041651a60041798491001090454017802108003405030304608100080728880011100724061040d003801c1800040e90102105074a01c01a040020804585111030301120b40f20000300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 868163111 1250 868161861 868161869
    0x62102030715051c0b0d2006070803060306152808030406020109030f080c0306090c0910090512060c030a0513170406091d160309060501091a0a0b16020f040213 70
    0x3d400508940d803821098460310b1740491020b482580400b4403075480400c000d9030022102d80c50b556503210a4401e5481341d0040c1700350352095600c141ca0f82000012f041c078140300540300c504400c0c519481e00c4c80c19183d0313000180c440e0f140300039242620440c90001c0300b0091605d4001c0069400001004202603405400041010303100e03a03070705200d5401c1944111103007801560000ea81c8001080401c0386403402101040e001840106120302e00441c2100080228903010103032030114002c110104040d05d806070340d00d00180c0d030300d801401c0507103044a402c0e8030600c8010300080b00d407a542c10100700008504210141c40381c2e4040c2c1034105e8100c024981c00c02542091080b4000500d03040000708485e00e6800d581205480c0c50581c2c0c01c500d4566040c0c14800c0200c52080c0c0e000c00da171743c054610124806004140c0242007020002541079519903581956482c0b040019014884588041103c01201d50482c0d41040d00c0b0345034191103410700d00c0081c8841280b905010b50090011440403080c041c2c1e018035008407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 868164361 1250 868163111 868163137
    0x30f020d1532060a0306080a1b060c1109090c030604080c0d09050d110f15041a0a02150603190503090108100815060409022d010306210203071505 64
    0x544452548400141101209402d80060569840680c14503030064524400c035810085162500c0300c6115180004591094a441064181c3e00c41c9003406260350344003401a13481c1460803000c0301d884041402803003040c00ea004521150010302850402d009005140ba002000d032015414503080105098201030462a1140941c950802c400760207840b11000b298000360070074500010903242d0018000280a5242e041058243d202c0100d0740c5a214060b100e201e40c40350030f500c2c4e6051a42115003041ca0140c1844211010071646000c43d400240c244041450700100503680d039580c0020a080045500085100b02604071210b401c01c000400036007034405d02a6a07410039030340d802d00c0504402001d44078240303181c0c008600000040c142c4100141c4c1c41000a400818500e905d6404240300c040360310349075034800807071010882041144c0703041c0c1680b00071b0034039040c0005400d0070032592562a500c40d14a07000407a61401c41d0854400703200240c02400e01c4554003042e800c0b603000191196011102c1f021403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 868165467 1106 868164361 868164389
    0x51e06130e030a02150108120910020c030a060b01030b0102060c0406030b0a0305031206131406010302031302190f060c0c1406040f080325050d030f020d15 68
    0xf42c941e00602c00444507049200c03112006030007000c080d800c0a022a080e4400413000d41d4500e0408035100c0f0181c405500c801c0e407504404405d4107400d8041d15502c0418007540b03500c24107501b072007030701c00340b0512401000480e2a01c80c116005003009030240000e200b8240f20b03511071502900090000da02d5240c4075154540366410a03030082c0d10b0000070302e08204060406405020350140d200c181400282c9c01c0040b1010030300f200820450401d540071000540104000880d0380009401400d444010310290030314520258440c0035514180c806028001000c82c8241e1030075010303580003803026500ba820006103000864501909070740c8140d0a201c08240d1400c0c42c40c1010040020740015995044100508a044512500c040d041361032010722200c082000032826810204003441d00013001581c02e0300c500002c2c080d005401c007106160084814220f260000a0011744016540c1d007030b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 867985611 868165467 := by
  have h0 := BRFrame.cov_init 867985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 867985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 867985611 ≤ n) (h2 : n < 868165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
