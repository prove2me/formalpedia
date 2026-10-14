-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2911
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:06:42.551986+00:00
-- url     : https://prove2.me/submissions/2da598db-1feb-4e34-8788-2997fa9ea450

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 523381294 ≤ n < 523561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 523382544 1250 523381294 523381297
    0x4050c090603040b0a020d060308121005150a1809050405070504020f0406081008030c2104120305090f0a0b091203040f0611011b1e02151f0806070315080102 69
    0x500c00200814915034960361040c0c0302c0c000260a1130700f4181e00344420b0b00007106a100c0d03000554004d8240030f89400640080d2840b0840081c1562542d1070007400c10419038881041c48001e01c5030401103a0b854008111044803400c1e6500860f240c2c2d160390640c0015010304c00d5100c980224020350030b03a4203054868003404140d125074140c04015100c1040108002841146074580151140c0e40034208190b95160b0203245800c4102c401d8400c1c5c00052000d000700c21402d200016000080c000942858505803103080c8042481d00c0c044c0a2200006200b061a6124490440c00c11801003050032565203850003501143c004030500b41c0a0490981031561030f400000030780e000c55120040401c80300d41003113002c84001100552808843d900d07140e042c00008002c1612440242d1a0740d900c04015102a98100b01401134203421025500102c851000e0350203515038440d80180c400d120380d14060215403205c00d400704103500424903405404180074255074075400015509035419030703400c2484d0b1540e0065080703 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 523383794 1250 523382544 523382557
    0x901020c0f0604210609052802060909070e2e080906150a030c090c14030f010b130302090103050d08100602070920030703151e05040f20070204050c 65
    0x202c1400e00042060791810403101100300b220780c2c00c10844082982e2040161580030360112030b41d03006031042d4085456801c18180034003071408101d408034076542e000310380980301d820780c3c2d41e005044c180006480640110320f280700c0e005001e0201c603004900c25045040c005400b42000d03442e440b445d9244003109206031111030045110001511068a52003441c841c248248440c446d0015441c48000002c110b05a25200080030513010115140007004802002d14210240300310801720140140440f0036201729505041d226425041c5645072100310000c2c0b81100c90341c1c4000d510a41503c008030400101043c0c01c0700e09203580c0c603060316988440326440c003541500d02074407006920960702003001800701e4000d00c00f6108003150702000070040c43c0306020303e6030045076008003083d2540d4800110400040390000144040524228035940c0301a004a800c80148240d41c0324a4549025071882c0b021a0b0240650711031707465000500e200344001c96000ea800c600c1c0141c0c4103525000c005440005034200301c606 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 523385044 1250 523383794 523383799
    0x80601110c12120d0b0a0608160809010e24101203030b0103140106210b060406030e030c0d080103050c1804060507020a0c08100b041a130f09080901020c0f 68
    0xc511820340c0030b0008109012107607103890320645030008a0429058000c1048052000d0f000c80d844030448280304600340d29a2007041000150410408403068010083c40105040d290080d90340e101e40896501400003601d4404080c0540c004170402e903039002a50380b095142d6444810390540d6000e0011980390124032401071064590148000003174842e9008191110741410001032604010146040300e0000360445070200d2808900708407240c074000030f01d45c1286100c249c14010040c40a02080c024001c0e0302c1041c0616481e0625a8004c210078019980300b0b20200003114a00e9414403002411688284000d4a25000e81c4a80c000b05043c41080b0a0316400905560061910745036280802400d0041c04901103004180c111800a000c6210f064000c1404400501c480e10446008000310f84c01c11413094481d5140c450014440d9a444010840164046032100c501e14021640d400c00b4081085141006a14120f1035208100d01c50024000d510b00070b0342115401101c400a01c9210207031000201e5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 523386294 1250 523385044 523385053
    0x801060911030c0708070b01330e0f0a0e130218010f14061201170d08060904032d020307030305090303151201020702090405010b0108060612150402040b0a0f08060111 73
    0x200d112186400800304a1712030329485103840c1035622034640210b42a08184a400d2180303100302032182049000d91170024041600c0d4500301000384020300000c2540d8046030103081d10029008156a904240c00002e00b201c089140c0c803450501e580c0220b4082d1001c0403403181070306074061541142e608101c075058400f001e200e07076200e9051104040101c400181c041c0d51200d42086040520740c1411052402040b81100c0031741450b03036118006042485000d00441000038850030000940d0300c4402e0140c000d60141002d05010001c1003124000c03454201c9050f031401c5110020116440d400401410414001da83c01c02c11038952a4a1548a1005861948148030590309280a6181540f13100d10414450400186007200a40c0851240c05003181d081c1d0340c50350354030307588507203542c111121652050003284c0300d41c0f030048443e0210140c10400740c404040c481c02d00d040500c00d030311294100c801a00b5010b9415480f901803102c010098004800500c001441c0740380440d402d5400380b800410b46504c14030180 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 523387544 1250 523386294 523386301
    0x50319080904050406020d09030e04061d040809031507080603071a07060c0e03010c050903010b0d050a030e010912050d1e0f05031905040b04031124040201090b040b04080106091103 79
    0x18060191003500c2c569420081e2000011f000c2c4550380030b0314400c1e21113000c1403a15204100c111240e6a000b0303034000c810380b4401103c1d8503030b10082950203903102400b55281ca006001081c80c0c0300d000c1c04070140c1084500244080140c0200d03055226076800c034201e428103511242001d0f100051154038121042d014401c550024110b0b41100322024074600c1d000d40c03440851030029047034070850781c1e24601040001400745002d08081c068100303486000c0d600d0988600490f41c03100d60790b031041080030301000240013110041d0780c81050140000e003600c0f509100030700528201191036080300405140880c4941c200744d240030f150010031072000070740f98555509040c1d0401e400d5400e0f901c000d04203101002c443c00d40700c145401c0d920400d03000d140101d07214107003803a003450060428004420b1540e1150300c5180c0354150300c4603240391a0410641d9600e01002921a840144c0b00515143c02c4003a4180380860b001c1007120080001d001140c4e0101c00905c021503031030842100300c42041c02400c10030034041002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 523388794 1250 523387544 523387549
    0x10216030f020109050313050f1f14090604090c020c01020c01020706050c070f08070f0b1206040b061608090312091e130f060e0609190507270503190809 67
    0x3400801009000200b004c50700d9581d21030031580031040c603442d10050380d0000d000f503080c50700030808035400940303100e68849001e0300c04044081e40c00d00040b04100100369540c0d2403954035800d0301c4d601c65001e4920b075110780d22049402c2c003924403030300c00701c00510982c0c00010303056100140c00140e1000607005440792505015080b01ca40d80103062080141c8070318440040d2105200488000506030b200c05803c1090520800120741c00c120f41c45600c554005000107083d0820051003a50040412640010355203040000701d4002e025401c061308504141411550074031151030024050304000702c054524241d1003111103840e03800703041211500050f91201005009000c01d21000c0c101a008052942d010b400241c03400548074286035100d40d081d00c0d8031003001550840d440060b044981110b417201d1620b40020038802260207400025542a203440c0800d000780d0150001246040203907004142807400300c02d149044080c1440703482e00900c25091400f140d40703041006801116404994585440c04030b01c00c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 523390044 1250 523388794 523388807
    0x71b030e13180c06090803040f0b132c1006020303040b090c09010308070b0a09050a030f0509190e0901021303060c0e060a0f0e150a081909051b010201021603 69
    0x3540115a0b107441c21102d08650050790b00d2910b1040310002c4056081c000e00400c02c44031548482c82c268000d000900400c407441e4081c10540e91512141d50b201c24070381e42698843c0358a640800c1002011001240385410280f54050640719140881400ca40b12402c2460a007007051060310300582013400400c0000b0700701c1015603000a04403040340c0340c070307020840090103a24080c0e00484070b240e4001040f070200083c81101e90b0340481c0c029030801100200d921080e0b211a1207181c001d0401503507214141380d0601410546e041d42c003010380560403145a0782031700361898403107000302250740301c906001441c2d0032414009c81e4107552201e01034001052850f925030740544100a055000c5c0720707495140114545521004d40350100842d078504041e20030701c16014041c3c059001c2101d01030f401c016804464500c02000322407003510a4581011168bc82030300140c040d10b1015012250395080814950030b210740083e2030683d00c213110000b000140c00c0d1200682c200e124030546801070840400017007010901856 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 523391294 1250 523390044 523390069
    0x91a03060609032d0105070801270e0717010b0f1002030c0102030709140d020102071a0c0708030705060705090306010504180606030b1605070b131a01030803071b030e 73
    0x5000d541450300400019042510f80905544405141c0c01d404440c4e5000d030220980040b0b03904000c10160900710801445400140a81c02d018816040d490501480303940111b0b03400740700000c04108200d11100348035180c0d0040c5c800d0101a8010766034500854806100f52106041c00500035440200c8240a0007000200301c00d1a00541c0410302504c04016020300041d8403030f01040d6550b29070f05040141414142d020700251038000c125884c1c4da040141d0f00003c520059171050141c0c00203202c0c0d0b101103904c541c45500d0b103810343c9000d00440000d0041001000c0d007841441141513419a40da0104c0c00c5a03580030301d910455165104c40300400c020309151b4850031002880021440d45445503403184010b84200fa841103a2143c050390410402c160141109400b01c00c2e245080d07480d00c2c015407100c641090016102d0314035840d506d80d550082040740340e00c4158414000603812803035030b900d0501d016180c208891442c0400d402c9001005020500010380c07117803d40c1a1100d010074185102445800382544 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 523392544 1250 523391294 523391299
    0x90b030309040b060c010618141902160f06090c0803030c091c0b040b190c0c020f0a080d0207060207050121090303180807060e07060903140102130b19091a0306 70
    0x10042141c080400703000300802341c200a04a102d94a8401401004541244800096500309141031212244440d098407000f0940310324050b03241c607402c1416004040403100001d01030520244408104020303600110000c1d4010060018030f00e0f640ca40f015100d1004580080319a4002c1111407400d2a20507503031405103081802400030701d0031503510546450401d076000c2d21a114410100b010026041c14241103090030800207105000c0c8101e00500303060382e5070700000e100e8214805c85519540f2400c0d9994010800390b0304a4641c8044220040d40f200031502a0030300601071644042010b500500002d4030890b1441282607400c080040e010300182030b107807011000c050b250b03103070305050036203010324804182d020f0884107607540c40b54544801141d005a04801c05074001c0913007004010740000d291401c07240c01c1044407801558101c28070340207100b06c4020802051001c40003290b0114184040c1000d203804021401000c00c41c0901590b820285204902003080724072800301d04400e07007002454000001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 523393794 1250 523392544 523392547
    0x206160e0d141207060911060906040306110702100903030f0509060a1b02060c070513091703040302030c062d010b030c070204060e010603200703020307120215090610090b030309040b06 81
    0x49480310460b544401c4054031705079202c400903010f1020081c100002c071b280c100c031454a040c00c8100400d1180c052880003402c02030b40c45610200c230142c0303c001c03603080d1640201104c401d80c182c010f000c0e100c8419800143c000400a6103d40c074524000c80c11966110380040c04142403145421046400142290003840014180c201c13020040c0c6808014000c2e181d040d1016084042c10901440100c4590070a1940400e0034914120003140c0c581c1080301080003c9504c0558969681c1416844c4d84294586e00d4420f200e640c0403c103041c022034002c222030b849041c4c15040000c4808030200c1a800003802032404044080012401d2100c5c254010f1078a90320150021500558428040134001d800340e00140110307458074000c1340c26408115a0540381e0400d000c041f400d081150300c0003035403030050302300060031049811105941980200040510b40c1c54502540b4543d02e042c0d10341c180c80e4001038800c0803106440203000325541c640e6018160040c007001e40158104040c3e107007000040c0c0004013515400110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 523395044 1250 523393794 523393813
    0xc03040f140d02071a031302012f010203010608060618040b1503010b090a06050a02030d0506010908010f1a0a050919020c070605030603150708070c11100206160e0d14 73
    0x405000b6060142000d8002d003c42929020350b00350042c040c40045031080302d080040100034000302800c14500307602881d141020450500000312a8045103141c003107562030340280d03079030300302015001181030380c1903607035943e8148d02e8040510119009802c915900d40c1d107403446403110741c1069800b00c41c102c03200908000007042000c01010b2140d0080c2c020b0916584001070880d41400d000800c10300400c0756180c99480c4c4a10184001d440c1c0c01580d04c1054003030340f1200401c1040e840780410401805101000300001a0003020400080c40560b10301c000320418203030303c806c0c0c1e880c0031070304001169230142081e15280e44054060000c5115403808050032a801c1c416a08184020441d000140c0620b460720341e0740e4100303c0c0c01c1526000100e8076045003080c60340200300c4865030000700690843c10754184002c2601540c0742001c07401e00c3c084495038110088180101403290b0014190380112440841003603403852011046030080e00b004056074218140040c1c84002650844804618101d00c60507501d1986 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 523396294 1250 523395044 523395083
    0x2309061203041a0c070b04030f120e1221030c0703050705190b092506030f1b0504210203070b180d1118090706050a0c08040323060c03040f 61
    0x10700d0001198180104e4241c18018003000f164000e060982403660420340f45a40c0d240382c42ca80d0890061004802e20b00d030130b0350b50b80140d55080c98800010164280401c2c0a02515a61480b03401100d40240c1d5030440003956140c20011240544039026104d0314020031510280c90b10b0f0f1021030300b198903101d4a01604406244111902c1c005481910b410109041806a451421905100c1624818007130701f0182110036100c02108c040303070128100415a07014190814009084480001c15211000b030b2025800c04d9000f0021300941d480c52035a002191005400d1103140c00800c8002074159004907014003c02d100f0601405007801c104046030910040b280c0030804505044508542c95540408002e100d417074884114082c10f5403101c0100f851385401801c00d590f5608903c101c40a1041c0011201007807845850304010300c0d0342181205a4885d600d160002c1d00015500030701c214403001c0000200030311404203d80c0d0150110003001401c2d6201c0d52140110b02003c8071084a119085071f4003401c0c0d54 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 523397544 1250 523396294 523396319
    0x30a0f06050a0b1c020d02060304051e010203071e200d03230103020d02060c0f0109060c03140f13200307050d0f1e050a0b0a050601020d02030712020124230906120304 73
    0xf248140050580c100310580c600c3c0d031000c00cc21001d409a4010f00400125a0748079480114003820720400c0c5c840d0400b0f1100665519201c085010320101f01004100c0000c6000a480285d000482d0360800190050890100781d100809002c03100700303040c00300100003501c0c00389410b10740c081c0000e0803580b42826903c0150302d03001c000002802140d450300645c109000300d030311603c451070040e810248003c0000354050711034188000c040c0c101c200014404229515104600107254903485070301c070070030b520b02a0f81c40b006101d0801d2480c1e00c40c3c401c0307140c0403c0034103010303d2022003198130107010603110285507280b0801103440b400e80381854507000d100307901180301040329811807400341d2184a49428070700b40314802d4910080c01c2a0655000107114000b00d0741c000111039070550016119104600804000c9015060600006400c205c0c12804c12401d03100a41c1068111114100c82c5090390303e05900c1ca140b02c00704401042d81c454512000901141012030000d03030401e4440c0c0c2924541034a80c1d01d100c101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 523398794 1250 523397544 523397551
    0x1205090d060b03101109010309110402042d0803030a0908121e06030f031b01020405041d06100b0a0e040603050303070e090a060509060111070302030a0f06050a0b1c020d020603 77
    0x42501d40001440e14241030100e0403111200d04c005100c440d0090200d00c2c0d0340d01c14480e10034100b40c1d8544c1c41400b4820044c003100103020b80100151756036640c901c603496420a00101c0d000740a00100c9034641c0c0310304091b18010880d2481d40165095540c4d0051300c1c030040102400070b175201c4000b005800310314000d40c0303100c82c40340c1c00380c901000700c0ca00641c10560014400400c03041c002c0c0e1101600f00c4103d0000001d454106050702407000c810003115071042d02a000380c0d840f958202d41400380508240d1001011101900080422603400e0b6541c03084584052081e0300c1030f4070200000f005a00400c600c142400350004a01030800f10306039a60b560350701d1440d40219480e0001a10542a2441610303144108682104003503009000b081c0c1080c0c00128078050103069641441905e002d400c04071501840450021a001825a0346083d524141044c00701000300c0100c07189481d1a00003120050588142c04200d48040d00b280c04000b90840d1417940314414401c00e9034000078804903440180d40d80e8006610 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 523400044 1250 523398794 523398803
    0xf1914032a0c0109090c03090605070206160302070f11010216080c01090914130c03150f0b0306130201030c0504090203040c0603050105060307230c0a06090b1609031205090d 76
    0x109141c02000e20503900d5070907607910040750000400001c0b0740ea8007960310420b442883c0c100140c83c0b140360381c00350028100c9140040400b41000c0c208849950041030451054a030320028603520f10384180220101d200e459801813000840c0644103022500c16003004010401c1801100c10036410900100c042070019480b0035820303481720302c13a140e2550744036010788010001b04d03000b4030000018907000090050001c00c82c09030305802d05042c20502140c000b111000b0364004001600745805684e804007c1c045207940d98441c04c0c1040654082804d002035110b00c5258240526424000aa8011009403e00d03040000030000203000105000b1128801180102d10402c00c544031245051070103030946005034802c900c078690500400841c00e800034001c0c040a8840400c600d510f03682c10031000c49034080c80300b41d09004d01c26884900c0030000d0302e61080300d01034010801e840c0290781e0340451803802c402030a4207a0014074103c8042000900480d50068000420300b0130f1801c1ca610080450403260703070380c20142d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 523401294 1250 523400044 523400077
    0x40f0f030e06221e140409172206051b010615020f0d0329060f07060b03070b0a02030a080a0e060906040b0604060506190c0804120605090f191403 64
    0x211180540003c1001813500c4000e40d160b5a211040421000c2850f105c1d00c0e200c40e40250508041c1d58980c1e101015071980328141c00700e4041d0001c4020180c2d0041031100002100c04200422030400c81c0811101b100c19135501e491a00c4480703998200c07044106d83d07001240f992220804680c1d50a181d814041d5209070768003c100606c8280c070783c43d160845250583c02414545044407440c151249070500c21001c0c610079000d1483e01100100304c2920840b09060055100440c0103070030490207400c1030490110440031201c02c241c56504444003031050b0004c400141c0e20801643e019140a042c81c140d000f4001c0c040000c040c0605480d0130300305101291007205030782001080104110355084400d801c01401d076404c1000c1420280490603038030070790505059040340885911203040c0b05102c1404042c5c0c4c00030031140c5076a40c44c0200e00d505c000c89841224081c0c00c21001481580c00090311106a1090341d0091004000e004810265805000d000381c500700b1030504011201e4a0030001025000680020003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 523402544 1250 523401294 523401337
    0x2160615080d2601080a080307020a0b013201050306040f0f0e0604031101090b01090e0309030a0804051005120612070b0708130519090b0105130803040303080708040f0f030e06 77
    0x4910146490910f00c0a50103c8401405803800c005061a18650700034915a03882e12410020780c50200710a0004200020341e600105200c180640c12004e52801c082066060141d00c00d110b6200004120070300e4006002440014098503094001d09c01312440030400143d844030a42c420401d0b509600b2002c101ca034003003000c0c802010740c4011a1044850400000c01844c031450786d8121440c0018414056000c2d1030341c5c442c25041c9002d00880320941c2c0c00030220788a40082e881c2548050f0040c0c41580d1051907442894084140100101c03210782000c005c400c0855a600010450b4622a070030000303c491203501000305501c5140402072080f03d00494020b0348441c085000081e400450f50041402100c030782c500d08407103a601c0c04a020654074050404aa0a0310701d00c0104c0d138902480700702d40c042c01c005140014102d030002c0020000d8a000c1e079520242035480070001d6420a40a80d40103005640041d050300119244035404003c0d58803074905208004400030000346150072200300c8005d042031001c80c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 523403794 1250 523402544 523402577
    0x60109081005100e0702060601051c0c0225060e0d0f08070c0e13111e060d090c050603070c0b06010e0603041103010b0f03070603151212080a02160615080d 68
    0x160000380104e600c3c007a140d00d404c8100a44442028103842e0600c40b000c14440c0004864290202c1030301c2010108000080f4440c3c40250303110180d80d00f401100038003401030301d8030040101c112000d58090b5158410b900003248180000381904000a03038090007150803540c00650002c00a080003805494400135190900040101c1c221010b170020598064945000d00010742c06101d01d6030381c580c1211a0726003c6c0c0c21541d620b11840705036103c55403010000401c205001c18030b0340005080c50141c052510115180d0090080d1840300f6100c4070042035501107807100160440d40210361159062510a80d034a4400e0042210740d00107403012a109140d9403039111042c142441104007400d002c031100d0710145c103404c02081c3c41c0c0c00c2c84e0090204154899688078042c0c010040210010510304843d00c006406a061044c0801c4000d02038800041040000c110100035900a84142085034220b4041c404019550f40d4001d00c040f082401210b112a03000088464080c00040f142840c5c0c1e0300c83d0030007140c0000c01d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 523405044 1250 523403794 523403821
    0x30708091009020d1b0b0d02070516030305270a0f090c090b180a080303090d020637090c03140c09010f0909031b12090501080915060109081005 63
    0x15580181c600c0d0059840241e90b4600c070080a45070440302940f00728202a5542143c0c20682e008020151400220311401e10030b281d000782001405001074401801451a500030500c42c1880040c0c0080e40c01e0080b882c041d050b00c1d00c55200800206a03000c5014140000316010308a1030b0f0244414225400040100070214024494545042e203803001500303041240c031066078000d03400c03581c90204c1020701e0307460a031702c038110080007030504042181e44034076191403000d5690050f51240e90041c050b072804111403401040703000c0144409400d80040409482c080c0c00324031003080c02e4040d8010740740c01055003c201302c10360304405580103200c1a201151007184180c44c044a40c1c1c8150700403900c0700c0041190324000ca5071724054581c0c1880203e62140c19003803c0780d4080d4a00910080c80c140d00600104210b502110003408034401d40b15030300c800390384100666003410102c078503480a4100c0a2510300740c0d501d00c04040c0d0300c40700505013403c106403030b0b5104500d0103008503032941d0103580e55014803103125941007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 523406294 1250 523405044 523405063
    0x6110706061401121a0d061a09160302092803050f0a0215090d140a020a060528051903021b01020c150a11031e0a02040f1701090803070809 61
    0x71900b0080c07481100000d00b07803005961240d4009540d01e107600900d114800b04142050b000802e09602c0c4c01503810070000034131001c03001050710010400c1c61007980c00c220740b1051240140c001d0b840754051003a401940a94050320740d855120040342201003140c181000001640d81c0c0c0440c50900030703800c6103452403604c0401d81ea881d03500da10403645080181da45500c00143e0003004002075444000c044086103048001e000000c0c51580c0c05003e42c07040640010340058514001c85101c0030a6580d0300055801d4402d01c400c101c05120341180001200403811301c007150090151070a6450280304103c41c10b591140c0d04c2070400000c0d00000c00d0398442c5e44101101151407681c1f4000c5151011003440e050303645209201c540d540b01c0c109400100b505400741d00a021a98000c10f0481d034a26160320703801302c09030070080021054078816021400a8504c1e02c00c1c0d0742900d0380551228041030030030343c006925008212450090350340300e84008000940000155000340c0c400e0b141d00040d81803074a03c40d81020200f5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 523407544 1250 523406294 523406309
    0xe04150207030507020a360f0905031905030609160e150c060609090304060810090f0c0315030816050c040204031109011502060112020d0506070e042004060810030611070606 76
    0x20802114018403c40180b59060b04200c0c0329940a0000e014007c050042c0346400da03102ca141103004014040040001c0071101070140c0a40207100001c4819916404152555a004010b07140025004c540d0000550b880039101d0400c80b042d013a170b40300010748841041a190080580c0030400c000c3d00e071000c008060300301034116104860741c40c00d86203460f501c1c0038034800d4004000c40c08000c0790101050304501c902809403031070148800d4840d1000000500076040e100301c0002c0c60400c240d8121030180300701c4402d07030b036011102c6032900038600d48114901d0f003490b1040c2c0d11409020243d641d1940c540c401000154415a11140740414590030481969416031008000c141a1390540c2e603165030214600381510140141202d20b50340714004100348003100c22000301716201c0c4030b052012003070f0405146650610205d41c240031220382c103034000c40320850031041d460800e44148030501849018810300d5a028200754000c00c1200e079203440344815200c1101c0c1c0a0401c150000310003044c05410b0041d240034013041d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 523408794 1250 523407544 523407569
    0x6040b030a35070f1e05070e040b180a0314120a051b0a05090d030504030b101a0a0801030f030e03071502010f0209010e090a0e0f03090307120c0e04150207030507020a 73
    0x1c1c1c07210b13030121440c048010f00b003080d007081d0804203001c80c010210b1015008001c84195680f10708650221020540f404d5408040801c0060000c04252aa43e10030840841c0508812501030f074081e5040003041c2d014810000091001d010303910a074444036445510035500c0440c05041c03500c02d11011100c84e56011b880d2480070004c60082e03a07005070844840c268141d444c121410500d0130221454001c54100902c50841002802441d00300060300b082554ae428050703403883c0452428003c038130b02c50080d500303012620080040006c64412201c1180721406030404140492070140003904190182e00145100c195840000e510941e0911440c2c1420900038811840d084420001070190351118210600c075980ca02c00007690f5200320f4004201c01c2503040c1c100e42d5200b81c8000c1842e00c07600403880c828001c0c890303400002a40c103a440d1b500d012498200007140b250b1070506c02c1040d50780b2001001602c0440c0640b1048078841c28602c0204031003030080d81c0307154856141d17104100300e000c0c070342d4031555042c01c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 523410044 1250 523408794 523408807
    0x110d0c02130c051606231008030307090e0603010e0a1412092b020915090a050c040b0a030605030330101202010c0507080322060806040b030a35 63
    0x8200044a208200c0710054200411091500c600582404908400368480540c6d9001c1c0701055400e00b64000c22a0030707500d5190740d40301e0b101d0582d00d0108442d0031000a02c10135007000442000750201c0c0c0c0181001e400426012500f070704040c07a025030050215800da0180628200c00c0000f40594002218421b5886180218200010300412003490b42d050510842c144a03201c0d1165140401c402268013409601d45c40c580344111000290000026601030383d0400002528404c0f9131060038071031306402c1c203924142818842c0440c2190031110b03203107061682da03580215244c1e400b04090034903482001c011598040c2c010404030700c0088121022103400d49290280803502c900260000180c4034100202d01914490b400100d40c0f0101003031014060303005400c004101c41d40044002c2c04039040b01c03421340c0c91800038100b807201d03803014078800c60000403caa008a451442c0c00e4010903203e120080442d1400740745612000b5074500b42c40c04822680d09900801c0d120000c10035031611801c1d100c1c0b0391150401c41c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 523411294 1250 523410044 523410047
    0xc1d10060207030314210c0a1101020f030a050c040305030c07060905100e10050405130504030206090f06130602040312020d030c02031204060203040c030b0406020706051006020d030903110d0c02130c 87
    0x3501110217800d00308011944a0aa10410921341c90009034025811814103150b440304100c0d5000c0f5485000040740c0340d102d250b400e101402254044100000514034540d501c510010003070174083e00410540204020000c0411000c1010b0051600c800c4044c10100340f80840181c824441544018020f0504e00140c5013801e41240704666960401da541d040c629030303500c00841e0103103e01e8110991007071030000d1952061000c3e510091080303100b0307000c0303580648450b401c00340d961501000010056014500041c403103d11034403050040c910462025051548954401e040b401e100d901c06001a8818090304e90001e5050182c44607450450014618040c420303021460000030003000582016000000f0600f00001003101c80025904081206d01e40c0c1801c0c83c04802030751000030f050b2051403c04000c80d0034041244010003c6401c950018460b24501d44e2098000e052a10819020300981d4044800c081d203061183d44903040041e59070306d00c0340c1c44500c1008085c181c0c40c0303124052246050700712074007503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 523412544 1250 523411294 523411307
    0x15030f1b050703120b100905031204080303070e1305090d17010803090d05030705150a06090209060306130902120f060f01060503190603121e0806031002070c1d100602070303 76
    0x40d07090f02d48013036118090607050015201006002c1c0c1c120310701c414411040d541c0503100c0007d940085040d92074081300726200a2190240f8007444403550030400120798054001c003080800030b072000d40900f03031100d506100d11302100c3e400c0758540002c1c4c121007040940709501c8005030103040781c2d200001004c0d506001c0b240765280075a0540c2d43c0643c90720711202c014007008000391001d00754030800302c80d81441c82d000d042940181c2990390855850a0900205002c100f0b8002d40d0840b07000540701505650b100c40801a100c00400d82802e0030543d100e88110160b1903c2d0440c1c5e41801420000700504414008490300c1e0400040244042c8803c000040c0a10b81e885001c076030b0003110380c0c65000480c04204000d0002462240d100400c41c0b01c11003500e01c105a00811421180348040300d000810165446058400c21401c440d180d5042c0c000a40705c443c110425405444c40c140180840011640c8940200e0421603d4071280305419080340204000c3d4860071602d036015000c43d2000d44580c600d941e81c05040c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 523413794 1250 523412544 523412557
    0x305090613020609100e0a060c02010804020f010c05070b0306010e1905010f050f03010e1021020103051302120a0c0515030705030403031e090201020d030212041b15030f1b05 76
    0x246450400d0190a65868a05445004c2c100804011503102501c80250801000200407401004045800500b150046000c1c800faa90103840f141c21544e5540d0811400001c00340005051020507407007940410000c01c9590094000e003100b40d0381d40e040c00000901054100c040803841f1307013284480c110045a00305108400c0381c00a00b48250645645001510140100080c2d60f5140c04044000070b02c0303520030000b80b406192100a1900029100c0140002d17182e030600c2a048941d020050040055129500480e84000340c5640460200d8690b07001030b441403aa0141500c036903012000038400c2c0302c04600174000410b030403100000402c1d045010f01119000080051050210104c00030341454000d802c10000d01ca400c00c03c80f84070f07011302016040240b02c021000d0303005102e20303420090150300138401c44229001e18403a540d410350b51552100d0f0a41c001c0c42051040c20942c290008040403585400041c54505032004100c007074425207240101c6244180051450070824032111036543c0010071506c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 523415044 1250 523413794 523413811
    0x103110429191d0c0903060703050106091205210f0c0c040506030c0d0f0602131e090209010c1e0816050d0903020619020f061602060f0615030901061e06020c0103050906 74
    0x5a135612201c101655001305090303640c140c021078040054a9034180c0c440c034183c80d0241c9400080e04c2e01c030722860024008400004060b039105150944042c4c02e4000440340708443c0c1d00c002ca10f45686496107407003641044008409941c02140b440300710f840c082c00707896400340c0c1c00e900424050048100046030b070030004102901c40c45051046070240000350701281d41402c40c0103131041000f80e60320406001c61300301503003a140c4d404240c000481c023418140211841d015059441110940749502ea0340e04402401c80c603010030700103070011100000c40f540080c00d4072110840d921200440d06003050360404071009510010085c0d0b03983e06000695600080c0d642a00d044805101c0701d11a080090385015011040c1d6007171031080300d04210540c41090310441480c04075909076811604c2d482141c0e21820010348200f54001118005140d10829000140d5800680c500000c5461581c44244602030003070388003400082e6403c482d062110a4041040b01101d54013880e0030032842c94504111b0b074503440c0180c110749 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 523416294 1250 523415044 523415099
    0x150f06090e2d040c051c060b030604020f13023a060b072409080a02150108030f0708041205030d1b140c0c030f1015030b010311042919 59
    0x10140410410030301301074100031b88a5510720b000400c1021584061200458529042440001e10307420086001409581e01030a0168589040c1d000c20002d00c10021600c2c191560030b00c8801e80a680c14403214024981c408006005040d00030540e0303105000c140380c2c2900060820904202400604040300c450741c2c2c015a441c00d46002540001c0c10441c5504061000305040c0407140d030034016988010404405240c00700c9403001c00107031010423050405d04c180f000c550028880421201a42c0004214a600c5250b006e4505038907a1745078502c060341031606941c16400450155240080c0f4442c5207135100a15040d044413800410f0020491800001c6911401c070b004a440091802c0c200a01c075100d17400102583c44142500c0342e07481c2c0d181800b4014120300d509102c18010310080301c0100a0969801041030340c01682161241c4a0b9a40c02640030342c0c1281d60b542e400030041a010000c14240703511603000307080031024042040380301402d9014040314500650030801c460100c1040c20fa80341c2e090381d000030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 523417544 1250 523416294 523416301
    0x1140f16060912170a2d02040302030a0f030807171506040f090b090f07140a0e060f070507150e0d1704030804030501060e130303150f06090e2d 63
    0x18002d03207942c010003428048500900b0901542041c55001e0b168408490100303181d5401c4105002c0c0d51088940d10119450010301c00400030f0040000130384610300c00e4000d860a580c0342d0100303140940c0d17070109942d4603620210440825034060340321030b0440c2d81c82c641040d040580000141c601340300a026a65280e1140b0211009521003805841c02410007804020f1202c1e0754001180180c201e0b601018442c1002d5400995203251209025008200302e42c1c1d90810454640000c8000b54000c1c3c0c03c080502200d07000c4820b03141c1d00d40300285045000a00d1498440c12075180591410b92581c00c5111080282c8aa0141e000d07480866821040c1d0b08991a0380310081c9410035030003861205211208170500020003109204c903000c020805ca80c07245000b089484c0da079541c03080200384203464105400e201050315502017031003a0801c255000e1103030001e58055a80cac00c078900c40c0c25815030191002c900c0c18401007184209800415902952072801c14811403070520b00e942030f0764104d01d078004a00e0b1000f0f010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 523418794 1250 523417544 523417553
    0x91f030e06040308281a01120c02070302091003020607030302250201050307030c05091f08090c0906060304050f2d0307020a06050c071e0f09090210111f0b01140f16 72
    0x1080362200b00780d100b000006c040006d080502c40c043c02425000c19202d50200c8000c40a42c0300b0001e100106501501010f03007143d0811180e4000584051110304174114003001507901c640c020309842c0e100307490059407030040c801e54581c5401c0a26007030030f8050f0089004000340c0d811404482d80702c030140ca00010740c01c160000c1a40d00b03010f2000f100c1e40000c0049207403000b1940d00e00111200381d44076141c0010940e203024209681d0700100b51041e420420080204dc480d0030030002031504207205070250740380480440a0340d032800302956200c80080c01050785407000407944085110b0f407030b40c2c414080c500e0300c19950042889901c01d84904410007034000703042d203c2c010f8240711740340140a194144150040d10002d0480068406009107828140c28203030014201415100f4050341075070150949101c24941784007035580c2060781180c1c0e0111b018511004840d40840315414044408044001450382c086000040082541d6010042605800c2216522100c1150183c0f54511090001c64250303103114a007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 523420044 1250 523418794 523418851
    0x170a0204170604050f030c0c010c020a180516090308120901060f0b0a080c04050d14070b070c0f12031704080d020f03060f19030303020906091f030e06040308 69
    0x110781c1c1000300809070760040c000480c10034000d0340610700f12a144a1940c001030789070f205507900d440495104034110240365000300f040f003045030300003485c201c10559102c05405038007a000000650041da11420800c00503c542004019846c0510f440600d413810b60390340c16054890303a400611401c080350001801503030250030003400b40540b2302e05881c9844c0d46940d14801a046105d81401040c00480020841d5000e90107550072a46c0003004103090300c2d10f0b1b44581030103070b21030402a41c4900400c0300c041005c640b1203004106c1c151150303407100051132900700c00041000c92900195524011341c103046000c0f0340d00001810201881101403000d40e1605c3c40c2848041c442e00032590034550010813032001c002d1146002d54401c0d0402d8840055a6402104000d4480500a21058601c5282c035060001c41e01c44d502900e1094070117880c061030b20308140300141c10040e0320019058400602010042c509034540107142080b00c880004112504007a9405000305100800080d03030210101c0030a00c14015910 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 523421294 1250 523420044 523420049
    0xe01060906081003021f03140606070204090c0819031107051503150d0308060f100f0f030603050a061524080601050d05040c06020c01080415021b03040e2401170a0204 73
    0x404590030906003101c100c1b0800404401d01c0003183c40c000452030341007000c1c15031710321035440288030501c1c240f129130030071004100b00ca0040d41c40c074004000c0840d481031304216486480e804010b0750b00f0780e400c1501e4028000c141c25a08080c16070070800081086860f00b08044000c854500b4860b40c89680b04420200e621581100103030f842507032060184240354200c46007034090170341521404444001070b418070181c502804002000212098505041644100080c4225100c02d290104981c0d07602e48a0a1610003110821ba400594611440d410154010300c40c01c010302c404444078251225a42c0b2a0b0041d400c00e10000080c0283c2c140003171040d1b841501100c54640313140f43c0810a80c14182401d00005006008403005403284600308015580600703c0c1ea13202d00c2d032148841103461214038101c0c0103500800c0c0c1121000a010041072403501041c0098009414800c2d61000a0314040c0210000508038880134030038000c2d4241d0001d0f4990340b1200c241d110f201c199a40682548444000d41c0003482142e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 523422544 1250 523421294 523421299
    0x7030c0501060303080f13050d0f030b0310020a02060112030914010314090d030b010201111e1303050615010903030e04150807080309040e030306030712050a12030c090e0106090608100302 82
    0xc08000c15401411541c0102a102c03035218447d0f507000f100e082000c0e6424800303001c1d54001200c001c401849200e284066142030b24000c12021200000300e4a000001d40d000092581c0214090791607580c10001e1a00400c81c0011010030561079807405401e41402d070043ca2010140f40320b8048490b40242c10544401c1655071307031000b251500110143d10b0b2181550b02c4800a810220311680d0380d8414083d0280d8040e03001c0c015460200721202020780811809125501c0c0d400038810b9200c0c6880c4608054011402000500080e15005041c2000c080000540e09c0c14081d04000c1400481d5101594216120707050b03070b0014072800e0095050b02208441c1c0e10417551842000b002040c140c03070110251a0109040d02c0521110340c040c121f0b07513201d010890300c264040c0c1c003e6208001d20003d03000404075241c02442070f64480701e030ba911060b03605403000301031002198486003000c40071544644105c00500482c2c50327883d01d550510100130009511071094104102014021070b901540c413803c08001141d00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 523423794 1250 523422544 523422551
    0xb010810030b041a16080a050c04091503080a0f03060518150a0f09020d1d0d08040f0f030e0f0a0b03011e09020406080105010801090c020604060e010212360a0807030c0501 75
    0x4661421003240c1d41200000250703081000c100700071141d0003209e0007004400c82e40790905040c143d400000389903001d11806040310741038001000c10000c0c001018042501d036941d2003210b081c0c90b40a4103544c2c81da030210b4000ca550350040d421801c1103103512504250807400c4c40e803a0121840001f004050f2076003007440c1c1c1c008508800148450994000e2040c0041207c007400b2015500104100c01e200981c0030402c0303500040d824030300940c0f0841c3c0040c0d00078410f00d491081e4108548a600e02c601c900102100400c1700c180c2c0414403450464445481950b0407550040d2090034588400e03094041803041225480d103032894480e119030500f1841c4041d00c40a0310441d102d91313a8410041c5401003c0c07003181d0214926400210f260b101130700a0081d0124241c0040109840381d5407550014980d401c403d115a550034002c5455180350695014000c0c14421944103102c0c82d8007801d8001c8032402c46440c061400c15006890f803003038003c18555003294000305165260310850500f59400f03401d10030002c081d54038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 523425044 1250 523423794 523423801
    0x301050d02040f2004261c120905010212010905090c011d03060c091f090b1612030c08060409020a0b07080c0d0306060906050f1605010f0204060c0203010b010810030b041a 75
    0x100300c8050021101c80c840200c0c1407004001d1000c00b04160403640c3e02d01504081c0c0740c000061040580142107002c10f02c1c09005410108c101001100c0b072502080714240d40004045039143c025510b043e0141003500d00410081c209a4291565666002000ea06101c1d24800120a0300e01070a240c104042000d402e44540e4502090184003d5000f40c02c1c0501ca6122450520011001d4000b5001ea0428075161030513090701b00942c200c100c0d0000030104881069205a001c0020119600410035029a44010402d803c0640000c2d24030707840205041e01440c03400210358096500c5910030000c44028414481d990030080c1001015441502c0300c850b868491500583c41050303155001d181241c090f40c0d910380050317031990802c50700c0b4403034404003a214000030f00c40b0320b0a18116210107800da600c11800003419202c400191400e9811680c03200001c200d0001c800340660800b801900c0042ca000d10700350500785440c4642e5441061035005c050003294083c00003070200512018064440080740c00070500078034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 523426294 1250 523425044 523425101
    0x1021f05090d0509090a0e0115080d0f0516030804050a140f0c061804150e090a02011106010501020316050c0a0e06040f050f0c2b1508030301050d02040f 67
    0xe030aa54030521441032868084007144120103803498524011300441c501d8540d180b00d1006030903611500c0c042035503141145096106840542030060002030003a0403814200030010702050b56881940b0203100081110a00c5240d400c100b0482142d89800c103804582c035070741415071408100c42001041040700901e00414554006504619403c030801200c0f40c481f040410b11045009210910104c55050001d0444610341500301c1d20111003d0400c1040440d03a800d200000c59100340c4008815401050b82c020655a01c4001e0111002040008003940e506d0040002c1d0340c0d104101d800c03040440620382000c1001010b0050400b500320013894061401d49850b075000c01c0920517903002d4451454440d0b681c43d0f0f01158012244100861070118620b503441e608a11100c0d88001c0040d240c00103c1102101e689185690300340403664140d100041400700d00210b40e00903003190f002094298418801040282d0711803c090340d0351941907501040006441c10000040c0401030750444030010010000007655 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 523427544 1250 523426294 523426301
    0x3110a2618060702030a020703020919091b23040b010c0606090f0507030c020601060806010c0507080d14030108030708090a0504020a111c0206010e1f0803040305150c071101021f 78
    0x88071000607100389441e5980b00f60703624407800a0000143c0c011032030420252521250040d400b110427030394141d412f80a151084202c510b0100100c80040e80821655061100c0c0110400030b00fa1660b0700d0242c1c101034140454112607120f070046d21898940c240d602150f4858045005032940c49a03003841038640310459007019013100c00625460601c1c00000840d514864000d4162800d40368015202603400c1000c1154108001440b8505001007100e050303000508c100500d81c001c04111001d04483c0c009644000c140d08281046201c481d0301c00e0006204000002c002c41d88a50750042c00c20307070b8600494000c5600c0e007140361720841d8803501c00700c0c00710380c119001300d070b030800d0f183c030403800c2e990500b29910f6010a8000d0014407031005920000040c030160a12001c0079801a03d0701010700d02c10010403011401560342a0400c84c01074101150420800800700000e00305003160300303041c044600c0c00f06c840c0c140c580109080540803417200703ea0801c4076402401160011030500031049154a070026003c00074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 523428794 1250 523427544 523427581
    0xf120b010203070c030803070f090e1302041509140708090d08090703020d0b0708091c14160309030b0c041206021602030d0306050312090f010f171603050703110a26 72
    0x4141e040748027858091280060700309403807034590580491348450300b8110050708001c0040b600907035551540d42c074810104003003500501000b000820994402e00310409000e070b0103080807092003c510706000d42003201103822a41c2e1025071500310510b90701d0000c1c1c0d40c648040b0340d001075017001c5c4a016010070f009214121038451001c0f9150300c60185c0f500085142e271207200142c0804070b840c1e0b210b000e2400500c29510101131000040340b182c10300c03804410703d418020b1128000c81c049008120204100b1144d500040e900888070004941880c4c41c21103405001e064941009210070782c0002c040990311007104025402a40180494001d412075140c0034005000b03501070340d88284a07500b51042d1440300035045609189002d400b4035890401100195542e400500680050004034914106026850b088107481604413400008003c503500364017504850000d00318204050812001d008140320751003c5581b00c4056241c18031650113070008903038900d000034400e41c0c0461900c0c02030180320000b000e40c6182 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 523430044 1250 523428794 523428797
    0x10052802061509010605090a09050705071704030f0212030d1d21090d151a0a05310605060d0c17040c05060f0f12090d0f120b010203070c03080307 64
    0x1865220034003100e902c05441c0c000c1e1a808800c8078014130056114070040c0c11080006000c0d801c0f11501d176001c400a0740c0088076140009400840d00703800780100c103a030392000205618500307841c02e8215150305024039403009019020340241d800d50005000100115140b82165550030085c00008296586441805212400d402d21a0000c01480c44141955a6500c01a4205221b103840c15540c240481c0e0025030382c054411110340300c00f008407014140104010303540b90302800c603100707100c10702049040d010540205014000d0040d194540482e4100c1c0f01d840000b0a1402c99940080040c005000c0d140507009250040700c0418601d011040c203402c818506001c2d03031282113802100c0114412103030006c03035004d8104144000d040005081c50320080c01001e01005c49903140004200b4000c141d81d0021041c10340e190542070400107200d0040c026503c0031980b501e414404000700100c01010351203a07040404040d0f0352010104102da0080088840c6241d014501e020134580d00d0030150095001200d8010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 523431294 1250 523430044 523430053
    0x40209060d0c0f0905060c070e04020411070f0b1006020604030c021c0503030103050f060712020a120216020a09110d230106020f1002030705070f05070905180f0c090610052802 77
    0x16585415400c4d55080d003031f16401810420310b4000703001241c1d00043d20a0742c005699101c5800301800000040c00707000c0c05001100c050301141e148c01c81d0103000c01007804110180c402d40900c100d0380d0100d6003c0d003245c1c1510300018080321500000d007426601c0714000c05050062200902040b40c0440503504803070090042d1100d20000c0e40b2031548074442101c01100140b00d800241a90310680d40c050b01d1010ba041c50300080302144001c6810490b8003001c80c440d00401040130410443c504100c4510142c5000c132800c0c46500c40a41151040c0e0142440fa01c2105031111503210b60042442032641400d86c40030700003019960344034000ba48440e055140c41a45004040d0364480841040c000c036030040c0300640e6032a1821140d903da000d02c080c00079100320350314050310100013420307101c80c000d150040d411621020b03c0184a500050310b070800c0914201382c2030300a40c4507085c40c1d40c0d800041c143e00071419140645205a9480100c5080c81a600b40001507001380100d000401c000d241d121000740c180740c003100e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 523432544 1250 523431294 523431299
    0x7030212060103031e050f130512070303081810240e0105010e0d06020d0c0509101b06050910090f0201080c090a090b03010608070e0402040612080702040209060d0c0f09 74
    0x9407549000d02001c0c003c1a0720385000d048440140c40e1034440c0d5181c0349022800d0203c11514014154407640101e4030400825100f800f2030701d0034042d505c4200d0714082c02061468550f560203003910344014030340e01020131040840500940f0911108110150070792040000d6a424a000498580ca10003a0480308019604c00316003100720803c0340d03050b14416154403001380100c40800584460a40c021203002da028402c00d41c0c54600fa0254801412485c3c80701616884c14209100724100d010411000304141c003e070440231840412580360b040c0f5005440458955603007013101703181988203040791072803d1520500f00b0030f11600e482401c4006100f6a44da643c2a01ca4541e0b000181c02070000103a03201904100c10001a451a4401e846442002e000443c003580d545200509000d001d82c803d01200c8280c60410003145464403980018040788480c2c0c40004400343c4544c081409242802806194001001d1030305940d100140c4140c4045c0c3c020030b002e1880c5800004001604100c00c0501081469601 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 523433794 1250 523432544 523432579
    0xe030d0f09141207080f190905010f0e210a0206120f06010c150509010b030709021b060112150b09010909060507080c120c07060e0f0d0306030308060907170702070302 73
    0x681000419010f254100320050303c40b081d41d40d2107201000f66280040210218042110b00100e59540307450f140c1c0450a80383c50b00250481805803408030401c1803d035203510700d603a10802440b42e011050304c225032645071300f511001c1c83c1c121611b401030742c480c0740840e40710003030850808800e114800300c64081c000c0e0344895005583d903109008004141804c0304000680d0f40a042d401a0307400301c0e43e01d0003c9044030100020a0420641303800601419400003160000031800ca0304640c040c0186038010112985821500000101d491300010050400442c11042880d81c907045407002d81c40040c948110b0f940d4402100005100f101c02c222031a50501000828982c054070750705108800124500b49031050703003030141d84c0c003160003400340b0201c040510a240218040c1d1150410010440d0010322040540350461854032919054403010941002d0003400000c0c0d1008000780c01c03540903a074400090320340520946403e0b000100e14004c900415040000c0c065000509004407402a030f01d003445140798014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 523435044 1250 523433794 523433803
    0x1a011a070305070b040c0b0301180b09070e010f0203040f120203061f0909030311030403090512120703110a0f050106182304050a05060106031e0911040e030d0f0914 72
    0x14040c1c007190051000201054080341d010713038814855414209001e480700440c190540080c0c0100340d814415540314084007ca6100d0030700d14100c00c4501c800700d8501803100808443c512580c943c1000a4501e0071442d4a008009440103802c041c01059040c984420b041c648078500758000307178030a00c91040403440c01c000090300c7c00d40303030b059000102845a0601072810040c000d040411401c050340c1e1090040740c003e010014600544c400c0c0d5440680610b07000c00c10554200440940c0c0c10742d04048101d401d80d41c03440044414096160600750751a1500106a0f8284007808801a101140c1c90595004201041d0b2140c415600c0341c1040c140043c01c220424403c07503a0304602d812103602250040201c02e580c00d015103078400d200310110f980c490503640d100b5041107000c2e48480c01190b01c503140b45441c0f170184c03010070031203500c407500030001c0652688580d00100804001c060040e956401d03005000202401190700a100445040c0400240100840000c00309080180e4800f5942071045581c07040204 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 523436294 1250 523435044 523435057
    0x6160f0f020601210602030f09120301080d0807140304240e03160609170706051308090904170f0903010e07030213111614100c0207031b031a011a 64
    0x1e0050106a090a156484520000b0402c1c03604c5803044801e00c0c0010b041e8001544204020f100144140c142100c1d00c0d481d015a10340c03d5a8034032010720042c0420384001407409041d80140c42e01007100d40302c1c0d44003560900000c1c0740c0560712a4002040006001520750450f4001c2c0104900d0700120700902c0f6803008807154505808095081002100049120610009107003802140c0c00121060680d07560072402060010009000c1d201040794800c1c46054482c260f801000300d0500d00074001e140d503c0c4d00d41442003800c100d01c0741c15628089014018002107011243c64400c0c0003558a041303143d00104960030a5284510a41c2400444c2c0041da201040d101d007107c2c2e028083c0445402c00c4003003c0c014004101046c2d007084000d01811751007084030751081032103a004041c011400b1108100341401e1955002520076140e042c88240011103171b0000e292000c80781c001400590b1608410f94500809030309070700c080c11610641010700f20001c01d500c1c0603412184541e050040500031042c0c001910f00484 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 523437544 1250 523436294 523436297
    0x90f0c15040320062206020304030c05040507110f01020405091b1c0f0606030902030c090c090f15131e08060c0a12050a0f1d030904020f0c06160f0f 65
    0x240300c01c00005954a415920300f01c00b01e1041c0c10b0031004440401e505411034074498400b0401c50001c00511281085000003400311440954641307811a211700220040902c40c4130b000e6070360b480006513503030b2048045520317121000080e036149000c540d149034042d401c540241441007004c000031075071400c0036948003a003913401601458204804408510040f0624102111042d916159161620100c5210b1100030300741540f4002040c50302030044c0361404074001c25150160000c102882018134610041d80c8124104890164a103014030011501440860780190481c440205900c1814691510300100b81c40b90200114809643d00040c8089050a440786403542c0c1c11081c007081240324960010030f6041b4003410840c1c061141d0f0840001205c0086680c149210703600c009050000b01039000b04911a805048840f04c0c000c4140e11007a00d074410203039180d203d603500042c1e29030140701c0c103000d80c2e015442c0401039070403070315000400c6044041c0320121070001404105042c03607518090b031080807001015 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 523438794 1250 523437544 523437547
    0x30303150d060504260435030301030501150816030803060a0306020712020d080c09010c020a05030a050c040b030c0f0f010e210c0901060e1002121602030c011e0507021305090f0c15 79
    0xc7c0c0d44103110002003c602c6c6040541c0304007078800e0000d0b00304002e60023184034a00010b4182600507000150704119001b6022503004107103210341c0c019041c680315046d42d410001080d9603899150018403121041d600c000e04860001c0f43c00b07001c0c45002d802750b2030303060005e80950740106150303801282c05510490316400c06075400d001d2015294070407a01c0443d980e2001e0140c03030b520f68440300020b1801e41100805c603403e5000c450381003070074105409000000c0c14160b0080025018000010300c101c000400c1d110b01440e0b1041100035680c1c8540d10603c9a150094041401c50b0325888000c2c074401c2080d8070f6008948160216018207083c03800280f4101c41d55513403851040c000d41020017030011820820340b800c41c4a0701480300ca456078404001c005000846040020000e4035105041c00c00c1e072000345031410700a442e894001d412401c0d83c0510f0101c4070600c0d08031307901c249a100203031204051300501100e951a040c10001c82100002d4400621800d40c0200c030414481e01e800c0101e420500348240c560f2110 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 523440044 1250 523438794 523438829
    0x1080307031409060717180603270106050d030903110a0509040618060614090a02040e18240f10080714030304081207020915030303150d0605042604 65
    0x40c4040a08071480340280074030b15040d10754031491b0f0003c4c2c401040741c2072054001803503802080c0300701e8500c480b03c03002e81c0c030f0605500d0a076660030b16048044050303440d10700310742d4401e0715146001c0d800710002c0c00d0002c0c83c21803540020f043c010003021140c00111a60703890000f0400e814070b0305042c01c1c1c044940050a110f000d0303590345d0f10304028101c080c40c298070407050f50740c00c0b0001920f140201c1020701415a080020008113208000607543d025091583c200d104100a104038071300d1910055010594101c0309034170401000840f890402101c5034003640c0d03010881c0041d0a0300034120301d43d00811040d03081f122551601c06a4000d60320203485000000c2d4070004040105500754a030070407410f00003c0a40381448e070703a122000d0a120704030401c440318503800143c96045250001015402a05a43c001030000c050382011964a01c00038011000f600303401c0d124a0300070350f0340290344105250320503410b03ca6414240f600001c0d11001c0c0201c1080105d200b40b00340780005500c0c0c10745040b1420224240c1c201d05 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 523441294 1250 523440044 523440077
    0xc0e120a1205032a07021503071223040c15030203070e03010b090a0c030f0911011806090e0406110c16060c03020a110f03030c0d031503050a031d0a0b070b0108030703 73
    0x1903041d080401811300a02025025030344407030160080c2c00801103503d64038030307280000410540c102101c4642541c58800e0003004200b110304110480c0c981e000142e221600c2d641444e00d480c03034072640001c89611120403a000c81580c5a00554000d03e811380b9801003140c0785408141c2a10000700289030841c08540000e071000d2520f4103c00001d203094103002400035070708410041500c6029909580003001240059202c0d640078030424400e115401d62003042d00d0409900070905100381c441e1030b0004a9000108050066541c86074101c400e00b07506c200c0d6115848100c2075110903ca8100692142c180c1c00001106e0740541c0d04480306541c158068100381e0382d42e55420f200321a50403a00c07904000021014115910708000816050050381c0c02002c1d91804024004c0981d03d040a200c803282210702d0040000480014104200301d900d0304050017807113170350011148041d01036507059502a5030101c0000b8070403c9003000b003031854061441d0090980e210010310fa524851084003e00080c03041c0390307035407816 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 523442544 1250 523441294 523441351
    0xc050708030a1508010e1f0e0601230a0314301629091c26070e0306150a050d0f0f061a180a0c0e120a120503 48
    0x43d030070400a40744240d11054214210b401d5035129070702580c42800710043c03144000c5c0c2840c442a40340031082c480c111407200700c644c40e100184100e43d001d0340030404000700d00d403801455004500000c0e04555940d5a41d0910707060100302c5c1034040c01c0500441e1100704000d035000c0b4a01111549c035107209600d9100345002c0002c154444000c648422100f1800d101c002100405188412640030700040b506a01031060000701c2c0401801f040b60a0b40200c2e0500c003007680d0616003801d0041241086142c2104503e4028008011001c0c00000d0f0001c04041008064210904900e5410250102e403525641c0c4020070321850b80032218994000c214002c10042c1b854054020000540b040443c410004a10354075403051220b02001140c12075240d001482200c1b900c10b5046000780011140b654082100e03242c51400c20401030700044041d80ca441d0820802409600111418031001e00384920310400900c280e40c80f822074143c02c03a08030780d4040501c0c84040c859020b40780100d00900b8580b0a031801000c0e500900d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 523443794 1250 523442544 523442561
    0x260a0b1f09120c0b070b0f0c130909140601150e040b09060d0f06020c0d0e060313020111070320040b030607270504020a11071a03010312140a02030d0c050708030a 71
    0xb10302ca005004c030302e40215802030498580700742c02c2a0711134140082c1400500c10000c2600504a00502c060a90203088030803590840c3e603c000c0000300300f229030514039042100c24140d0031040c411a40001a4685100d68123082581151382d0050021030500401007039500740c10041d984919200041040c0c5c0c98080c0c601c0582d03e2050407601c41d0010075a40e410280d0b080010203400313039080804001d510300c0c0c00002400c0040c000300d8034103146103000040380441c098501c601a0400000d00d104a071098400c101c8800556001804160400345200b003284510418000c0b09000780d040c5001007916040004403903000e02c4286c2c4803008a030303082c01c40ea012484202c10400304182c070700303d600280545031032005182c0c800059456110070004010014a4000190321102206840700f900b40c00c205041c1c0c0c01d40781503a50182c80e07460320200740c0004640c0184020501c20484c58001489078401d07400100505504024010502214555102c00d076040e020302e9402030200401040094512640c3e6802000c0303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 523445044 1250 523443794 523443803
    0x8071101030b0a2705012102060d06080601031a010e0705030c070215031b16150f151410080a151e1a0403050c01260a0b1f0912 56
    0x3582c0b0181c0d4000344503407035142c0c052000010400034032180c10b0401201c1000e1045480300c140030951400002503185500308560001c01d40c030500780348085549040850308081000780c0c06002450722004c03065141c1a0a101c2190030042d840b842c0300e80b200501c039526049403141c14000034184d0302e49078190391a6000070030b460369400d0100500c400507500c40c5e0141c180e003255510030584a2078104220f00c481084441262144c1106000e41140f16924036003040c0a1a4441350a10b1241800c11040020b0500d02d04004101410007203901500d0500300602411a1075028005207017010030b6081c04030b0540b144280703d0000707070308000040340c2c0e010345d0b0480c031055581c4141c46411990703545610403200b0100c2d500030400c081060020805148154000214481e4a1900c030346414695550751f0b43c0c0f150700d11036241c14801c41c00080e441003403296042458412000c40191400e19200d111007005000451250b84102180407a051080d000b01001d50b000b500c1c243c03920a1080e0a00300c410b80c0406941c00d0444 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 523446294 1250 523445044 523445051
    0xe060601081e0a0603020925050904090606080109020109060302090a1202060702090a05070e030606030a06150801060f15050a090e0c090d05070e010605072607050f0f0105010f030807110103 83
    0x140b003032030540c01441607611200004205046104000b8403c0d0081d1100c2c401c210100390700c01a404403a1b100840707100184c2446942c403051900498003030804507001601c520700d46100044c50172410f4000c03099a038400d030ba400740030340d403124000e41c22805070040307842c3c0042c12004240302c0032140940390249180000e001ca42800110f500156491008a6010446a031039809210b03086400030f000c4020b140003100034056030b10344800801c0d9120052400a0315540c1c4541050408829030f102d0b04025012090082c8003940e01c8403822a2007a800344100d503a03680108444401651240b816542070104940d6400286843c103a00044607e1000c1c10036005072000308400345d502e80d910100000780394803400180c901d043c50041001c0320070805a214900b8050104502c20000b8002c849043c030060050001c0c1003640009020108a4014080010614441c1905103100d00074000362007201c00d01c114000384507503038898982c0070f24001144401400342d80706000b1440000c54001c03105000642c10715001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 523447544 1250 523446294 523446331
    0x12090d0f02070b0304331b140307111203070801090204140d02150d0f0e06010501080c16021c0501050c04150c0213052d06010e011d121f0e06060108 65
    0x70448141c100c00c0d0b002d601c0713056490001b010307200c6010f8040e145c00010501110032000c0b40d00a0841d1091038084030072200c0002c001900980113851044c3c800c04801c04880c094100307244003441b10303441619245d003c540b2400000814100c02d008950660703c0864124880b60b041c0c4c0b0030320200100700f240407070740000660b10700382c2000e110f40c0240000345500715001c030301e5006ca00861021a0741c040c86010b0a50045001444240d8100c0740d00c07030b00b1031080d01c2c3c1c0c25941d0160800b01c59224500042c001c9d88640c0480515010324000441d8180e200d0080008100945500d140483c0c240304910a1209000803100c80c0c40845005407904d2010034000340c2903c22894211418030229807040301c1d004807500390182ca964000016265242204507408480e004034200440007808400c01e440b10503040040c0325030030301c81155911031400c15402d0054140c2c800110403000054640102c003100b4240d0250821100313220701c00f0380c0a850a082e0440c0c1c0a4001d0b520784100456511000a15801c3c03440b4a24640 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 523448794 1250 523447544 523447583
    0x130f030314150f040603080702061b0a030c0213061a1305030a06060e0a060e06060c03070605070305071103040b0a031d0706020601030c05040b09010b0307020a0812090d0f02070b0304 80
    0x1e19210365000c0d4a202d000011075020042840c2d12030104a000361728000c0c042c00010100b0003210b0301140c040b2071064032119600104650001c0c06a44d88000b030080305098010103403c5404450103074400c490049842d003882c0540d1048809074801d001411744001c207203801d40b801d41c1c0000e0000308074107064241a40d0303c4001003860304500784e808451183d5a2401000004581c144071504880d80d15000e0041503d00220601c403050b000d004035215141c0005c0007079218004000f1102d055500180500c0540f6018802400600302180c1c004049101000c64a220b90804001c0300c0c2901d50500c24103081422030b800c01c600900c000481c2002c84104c40b511222507860400c407220080800b54001d05056066240c201421651540024001c50a1070106041030741e4034020310f8151602102076607140d40d6203200817403810401140246c04e01c03a001031420348150b000e01050307125824034000c80e1680840804111190b1289440380c00040c3c200410500a900d02207004681041c0517003404814100200507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 523450044 1250 523448794 523448831
    0x280c08060916140114040302030a1a06060f03040f0f02060c010c1205190c14070f020918030409090f0c06050d060603110405040209060c0303010b030f0f130f0303 71
    0x1190045600000070045880c100304090203952000480c641d1680340b501101448a41c0c0e004080c50600c0401000d011010483d0b0042d030f001948c00034102e135000b14040c01c03d240c003211480600c11611009200141030307420980111060b00207041800c51450365140c84000748007100d14000c5510071141c1c00c2c0718015a880340b001d858140384d2040009525400c1c40c030040d21041828014661f00f80c1014100040c140c4600545800ea10322401c0115151002c40022a00c0040c4070300c0e582840e160204840c0d00b0300c4200e5980200c114400d40e120390360344e10791407030426040f00401d11108141d841000144883d80c090b400c00075500344500180304075044660b80f03c045150190f0403000c0043d40100d8030711313500c80d16070146800070a5541010800900010a00115803003a40182400780382c00040c201c455468200417291040071000a0b81d8072961550036810441e40300f038420921641c107000c04101043e541004960040c030041e840c0100708001c0d681c41d00745450080005800341940c41c03141e20f03070204d4240d5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 523451294 1250 523450044 523450049
    0xb0d030203120a05250e03010f0608010501080102070825020d0b040209060f060415090f080a03020706110c130e0a030f0f020303090309012102040f06090504020c280c 73
    0x10041e64890800b03850b10101004002d088540142c240070074000401c048210320300004030b0902c040c07440540d82d03000c240c1d071200c000c0140300d416620703140e03891344014540c0d805802a58008802882240d0765040c04038240d0007401c6005e441c4810400c001050a0068101c480b41c002d0141c11500f01d030b440300d4000420a20020100b95402445001040704619011045542c00740040720409001101100401c03114011809109100c0d160000d120034110300800341d503c020724540320b84d04101a10b030700000e034461000000860151141d20808074101c0c1c0142e004180780101d42c001403050320100010010108494417280c20615564066080080001d016100c034242c06602c0354238011600c540d00a06144003a03200c0400c54005100344800c500020088a401031400d1030461414298400c030882009146000d82215070f02c0014005250041d62080300101c48032512100c03a21b0b5624030501c03080c0c0c490342c046601c0c142c1003c10710408240000c07003804415100e59100d440c030130304550b80f0008030f005543c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 523452544 1250 523451294 523451297
    0xf0801150e031504030c0b010e1e06030a0221160311012f1612150b06040509010303030c0e100f2a0f120e010c080309030f03070c110406050f090a0b0d03 67
    0x101d01d05007070004c01403107d40141090b94840e401841c2a0210f020114074250401111015080c0440c03440d6908010000700b16400504d070103011a2582c080b402030200707000f0038400b107004020800b60841c00d031526000440e41c0141901800c031a00030011120100b41e40f0004a4051501c071041c050b0300455807046100942c1c0000400d01d0155000c0d03103052031040340d840010204601050700d000100c409010f20f950079503e80d400b02d10308060000144541c091500540d4000200c80000024140e15400404904983c3d88804070102c5014044c090354140c41549900880d43d04904504d00320710501030070b0402e0305111203660261100320041c181e4107000c1c1e98140c0e40d8560760742c0760300280410074085c0103c2c0b038000e08081d0080044040080d00301403179800c0140047c1404130000d2400d50303080c41110400d0391070305209a52860b120f500500f0008143e60f040d583e12142d8240140c55040c81c0c4614825a00010800e4000c2c012a104000200d400180b03004d0000b03803034031a6610790f922820004030559101e07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 523453794 1250 523452544 523452557
    0x50c12011509080106050a090b0a050306071806080106090e07020a080a0f080121020d0f05100603050c040e190201020a15050415230606190e010f0801150e03150403 72
    0x100140107010b00d29075001541c3d241d1422904010a0f03441c2844c800803141c942c900800c080407241c00040d8500303a81e600040d00350040c1000c004003564803140341e0b80545403043c0d1118040f074442608a0381c201c1c0034082e05001c00c3c2d840300b00b800341200396181c1c2640244248103c0e03608081542c2e56441c40c0c0c00484840d004200140491020a42c010109a016203a0450f840c207200380503a440c5454207030201ca000e802070351002e108909210301c101b01240d4080d0440e0444480311000c0d5000001010180300550310390052425504492405016420301d049001d00100043d80c1c660310450580d010f03628040307041d40308015111000440d400350301c81600802c0600020145000d090507032401080d01d030030449140ca01221340011503201d0b401100d20b0015500082c04a540340310200d40144106c1108101c10071a003142c503444d0b10b90154022041407000ea032003041340100e00b00142c80d90381c428000e42101084c1c129041c00c485102d00c1485040c2c0000608446129109041100b00034500b50307802e40001e01c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 523455044 1250 523453794 523453829
    0x2032805091506031b012003031902120412090801151a0c0d0c06090501050405010f27020d02041d030306031209090703051009060b130501020706050d050c1201 70
    0x401e2181010400c8003003040341080c50248006502c40e0b03010304200041251081005d800741e40308118002e64400905140313021000c0003490560349400c111200c00c0e03914082da8440d50314107042d00076070348181c174070301550800d603103448d9201d90100115000351410000c07510030025030810240a581a40c4021000b11401a0f04084401d540800300f0300c80307003001c010100702076483d01c1030000c0d40c03002502c983e140141e0341d000305240100141425540140081d8204028041807040c1940262000741c0b00600c10000d0748a100d00012a40020b0f8100da500f00300a801a0009824100c050020f491b1004100080135024481041484400f07002603001c154800b0081007040d003010441001b0700e40c1510146c2d41002101c600085c1e400c2e40007001c0070708040c2c403400442d20802c08100000301501101e00240140f0761544035885564024000c2c0882c183c10101c0700141d25400402c01c01c05952940d501e0307074502b14588000c800607280140044007461000c0169165400f411111680640207450b0819884032 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 523456294 1250 523455044 523455061
    0x2030c031c0c0203070305070303020a180803131e050111010e07122f010f0921020405160c020105071506031a0a11090f060409092409051002032805 65
    0x140b20207415000d66004102000209421109aa00007540340c9005681d6405400007118950f0742010640b200741d0040c2400305150b6000b002030400c000300001d10120140d0741d0b041200d848034580a445660021120003072011b035120302011000d108111002044807809000f001d8130f4000d00ba0700201e1300c2041c101c95a82000801c402c02241c80102c00c020105110000c4030905450a10700643e605000b090290490241c1c082c1131928010803075102c2d007000c008014080308941c000c4002c01284601e00e0300002414003400c0724444a6034000c0c958905101c01416401034030143e22402050754420002400038010300001e00540300607500c19030320401c00e42c0c00d080c0900e58649000c2c15100c07107113060a5441c1e0b40043d04000f6201d510108544151942440c44c0109600307100c0d542003503042c82d09102c1d114052100c0703c40344c0c0c403a904100c0340b032100340541002010101c9140709001441d6400003402240d20301e1441d0061074120007124441c2800c0e43d50301d8840b41140385a00020408142c0301e03401c000b281d8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 523457544 1250 523456294 523456301
    0x120a051b0603070e1c1209050303070f02190e1303030c0203090d03180e0a0501080712080f0306040f05090d0f02070e0c030901060f060201060f060e0612060102030c031c 74
    0x20204504500900800c000900034000104020100281d40000705825038840c80382200c00c61010314044a8015181445000b184160410401040c407022000805003000000c542c2c00c640c0103404403850600540c204407a8403e211294010f6181200000c1845008581c5d00b500400c40c1c54641c12000881740743c080c064404103c44e50096420600101b002925040822a00e140d450710f45030444a10b90b15140304062035540155040000c004104200303000c1e183d2125060310680411555440c0d5148640e40c1d0240701c5d08030051210400380400c1081c4403c810207160420f0000300f01158202c03a0a006108447c41204c414605a04c46d04c0c2c21101e140e08242e0103400181c0c0c500c0540b543d1418074412641144015001c1e0305407440000c0050130f41a002e5100700d000d02a00c040d03100c086592090700901030000360217410700c1e501365203000143e80c9000f007041c59802076014103001c3c24a0319031900903000030380051a040c15800100074007072440800740000c0640c0c0307918034140442074502080301c07000c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 523458794 1250 523457544 523457563
    0xf03100512100b0102011d010b1f05120a0207060c020303060405010b03010609051210090b01090c030c0e0d05102c0a02013204060504060215072309120a05 68
    0x90388222100e40c880c410100e08801410b061240104114208800407070050040c40c007001402080c42030084204c1c00107402030316031030104461940b494191861403815501c507050313000020400401200980e2464020300320b50025021800604100003900e0309020790701d13818201001a000081001a18a0309211343d41c05040c00502c020700b19810700c0d00242186039140202481942c00280384070074100c0030001c08070301016201003408078100601d03169171008801c0c042c0503202414051010b041078885c2c8076005c103031407099440488145868040c8048241c9070b40b0182c03403500410075800700992590003240100040346540d4140883c0099030305c2130140300324160038803d0b0400f1442c540540c1e0300074201038622000700204501c0301c0d12030800c40089540020b650000d50000318002590a4220020703004554140e02a0365407081a40d800280005048410f40c000caa0246001e60640c1760701d5000300190905400f0075031500e00140f0000c0d0600340b5640b41e061082d8001d6104c0002c00c1010300607041c9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 523460044 1250 523458794 523458799
    0x31203050711060606090a0503010c030914010e120c1c020304140d050c01030b06070b0c120f040b01031401060b0409020d0608070f0506070c05130c080c0903030f09030a080f031005 79
    0xb9801e8207207400e10748609000d452984903070008181840320b680c4614880d0000c0c074008008021070b8071800d4016014000a6030181d800d00d035400c020000b0540180190044400c90368050207051291105c0b1001c190081d1049001c1d0340726441a00100c114a14900108011150000d54440d0302e4980302c010319071968140f0500561032421124006400052088807290090034042107203005080442d806001d6010042c04081001d01400024071401e0000c05a140c0380e18880c0f690760391100c09000c60518180d80007820003611354010404519030764100c0040303001450020548940d510240301140d0801d0f088030f03000307903030026080100303d1480c0b0814004041c42005080e8080c60002c0b85c4180280612440c1e010740070000700c903010494009841c00c0548401028040d140c111020010010400112420081100000403a0a01032014160f500c50840180110301d4010a4030340a4141e4000841864251044020300000160301902404a000094000070340780d180202a16642d501c55522850 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 523461294 1250 523460044 523460057
    0xf030c170c060a0914030307170105040219030f023a0e032715030412030513030c060615020f12071110180906141f11070806010312030507 61
    0x49040704081100b9030b00c41100c1c0400182070780a81003821810003100f20804160000104010750070750004000c1065040c07607907011002d6a2076206000c2244500c419045440020949002c0740d45d10035048000c81d130b801c50601600b05036540441488020709141d0319140c50714402c000074807141856041c2102c41e040e0070014440744000c001c0c00e541f03074031408640d07003d0b02500c5025040d003103642c1d0082010200016004880681545040c0121a0000d41c0c04441d8907a15191380c0307510303d200c0e028542c001c007000c0401220b0f495a680d0155401040a131701151030700d498020001c0c1140e204541702e4171540e0190094008441c491100d1800c0178084984040294001c0c04840b003c1410200311128062013030b1292103444003480b10a8034031081d04100d28140814065001c1000d204903007100c03048941150841c50b50309122000c01268560303000c035100c0180311591442244a00c5180a094802c540c5c000796103180f41c8820180703003000030980040d00c0c2c0c5082e40088801180e41031246a038004c1d410f107000c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 523462544 1250 523461294 523461307
    0x30b0a0510030201180b18040c11030a030f0e01050c07141204050603150301060303050d0f0203131712070f0906020307120e03010b031b09060a18050703090f030c17 72
    0x407044080320780400fa0411060714680c1704108051020f00003e00580800242c54226808000003034040c00084280070b681815190021503003d00b140003091107040380a18100f03008004210000d1042e10f00801810b40ca6066642c0041001e00c116400b41c1e4240c810b40b50b988110741480c0040c000c0306400e002b542d80c400c8a882d02c1104100c2c095406641c01214101d03503c2c1c45800b07680c0c03e116a035402d801c1d0305510f4a40c0000400d60007400820140c0071113101444510f20012a02040b4041100ca0110307400350032034a880080ca008502c034070740e20014200e00b070801c101c0f0400c0c54141c0d94221210f601152441c41410755480d0400012b1005203c58401035103841d240740e440020028982891501384956500b080e0801e54083d08080c403e540050100d03150b0407856000f0600408010004078003e41034440458950306100c0521801d03500300c109140c0243ca000c2c62200c0c01000003d2044041581e50b602d4600024031080d0410301103802a41c03081c080794040d00f480c2916110030849a0644502040300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 523463794 1250 523462544 523462561
    0xf030309150206010303030f0e1c03050a0e1b010203040308181311122203020601090501080307050d080c091e0901090209010c0f020f030106031a09010903050405040c110115030b0a05 80
    0x28281526498030b07010a19482c4003061034094484503007036240a000e4034504954101c65a00c42c0280b40c406c562f01400a901c0da00b0b10700d81200c8400400000c1078000440042482e50f2201071044521410b10450303141c00c0d036035102d0700800c0e000100714404496040d141c0707200d02c2c03030600080c030450090a1410031510b03400c101442180e100d94005010b01080d6000020000c02070314070564450f5110000c556400c10b0325190080d100c980034042c0d140c0542ca030000100b05940300005031021030764018001c010715504480300b40c90f0303004000c0003150550020082c41c4615116078102180100e030000301296505100c608214040324140c000080151041c40440c10b0b980c0e00c000384401031504229424240b0029002040303880614072030403a015801c02c1000401c00c000c5180c2d95655142038000e4030300e543c0f1010240d50032794804620190001d403061100340034034642580054852402420041803110055000c10b0a403440010344481c1801484000c01c1404000c1d1642c90b407255042500700010f1900144 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 523465044 1250 523463794 523463803
    0x120a0c021f0504020a0f1403070e0f0708250f0e1008061201020d02031f060905100e01020a0c0801060614091e030a0b130c0b030405100519060f0303091502 68
    0x1220350050340c0302da021405644950398050301500e030640020074066110350300a030509580c2c031403c1e8003a1041920000d6950505400039010382032405014000341c0ba2880b0494526a025111285c07044417440d0000c02200c00031a42000c0134201c1d11035280701c4104500240040c00a075000e14002e0b0301c403030a40f0300030a40c000b040f15441401142c1c3d211004802c000d4440c028020710401b00c6a0500c000305116810701c040a17107020315010b00c15202a2143c45000c101c0c1d050344a842000d0300101e01001281a0502802c1b41128001041c4100c80c3c40e40c40079140c4030000e40c005d5000b030885035074074541440410345c4246d00c01c0150b0145940c2c60318200009020880d042c401e03280a070615212410030094070780d010301420030b04c40d4101609076014104040d950b01142c0041d01d04507032400e04501d001401c0740415040d00d201d5a001006055282c1c120f8005501410b00180f03156100c035805210a42e203840f041c030901c00030340745589031142003d0031854040c0403c041d86d00102c0100001443c513020300d550014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 523466294 1250 523465044 523465093
    0x9090e0a0311071a03040b130b1306142e0506180109180204080d0f0e0f0a05131e0905100b0103020f120a0f050114011b08120a0c02 58
    0x1c0c25030400b1410b1002a42021225002484070704004011888007a8004020b540668060054520183c03202803000400031081040100740c1c072405030000b17410410340f0038420a0980940804a270f901a1a40341c0c403100c620072036015519203400e820084a10702d80e40d094200c0700015820551401c7c0c100f2002816a009504010a1160105c5086502c1d640301c0c0c094500103000740e2a100241c0c81205030303100065042070003080d5251284c0790303580e01402c1c4079525180070010542c41e07c260031600d0409010b41003a071003c007150050008180094a070710b81c01c405e160244a1020006060a19030183c018000b480000b0b0395944da042011580c08680301086420034002160b400090040c03580340140c01900500c81410308110020031030400030b01e6121a868811701c00a4420014190040d0103081158000e0081c1c80f906090551452000d5000321034107000d800c124030301c0010002d40e9640d544510360000500c9940402d00100380140b00e886801984951a058000392200004c0d140d1154800007046 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 523467544 1250 523466294 523466297
    0xf05130b01140a050d05011413030e04060e0f040c080f0d0e0d0c1502011107060203010e07030509030a050c0f030c0115081f0209120f0d09050904023a110109090e0a03 73
    0x3c018006c0003030952024080e04c0d22245a0705161038284510b1240191240303050300820803a544510040c0703006e20400c404d44580790300100407501d81c00107050192900810484810950040110b134034203041040181c8680d0004c000d0019a00700000101803902d2040b11034058299080e01d2030014500144050581d0b40340103100c02c1864030020101d014000c0b41c140c0c5017000c03000185120502405400071410f0b41c0400e51034000d0f41d156400100c044460880d004080b0f0b40081c4188400300c0e119000412034042e0304001c64251400c44100d4600355488030702081c1181e955025031160022220b10014014004400a08082c54512490202c0c0c902404940c8000c07070382c00a00803600b65940140c080d05184614126040101c0d00d0b4a0260390b00104404100441c48603000042c0500d045814988150341c0906009042c04030381100b41c8030790f0340b40e08451142c4001c00e103c64400c0c0d402840c030307900128051210021090310707241c0003400e156080d801c02c115180c204003240c164550002440c5046aa06 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 523468794 1250 523467544 523467559
    0x70b040314040801090606061b120306050616060b060319050709030b040b070206090a030e0f04090807060204090b1806100909021623100f0f05130b01140a05 69
    0x264502160180c4814003803041a9201250100b0701c50415031100380240c1c4148800c101c0303545c807400252001d6005032135403a08104619800742c0007951010034400420700e10708000c1b80c510b44a000003820307500150072650f00c010340481a03006025040c0030342c400001c0b00b40d0301c15203181801002850007a803112110700e4603984800c0030802151042140f48011900400f0a190b1340c10103140150800c0400d0792050010f10860307006c64903000012482101e00c0e5856150604450001018002c03c1c03480c1d1281c4582c0650b0b0780d80d4090100f000c810080502e184241c90042e40d88e82400210300441d036010480301c3c040d00340c001c441c103150f054245103d41c2003881105c820886040c1d1034030848180c141a000b64400701d00100c0d0300454040c0101440d01c0d01c600c103803500c1c141c5142c82455101c20000c0c0da034801c00c0660001340385a5914100f41d000002500c20070102041420b140c0d4416820b490055900c4800c103411050700b00e043c000c2d00d0203050301401095135447c4944001e000002d0400b096070181750312a520 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 523470044 1250 523468794 523468801
    0x90b1302010c0618020405160f0e060405030a0305040312051204140a0c120201020709090302031e12010e1e060603010501030c0c0b0403090e1e070c080c06010b04090e0f03070b 77
    0x40b035000901c0c940c000303024446210303a0507012411903102c40c8224040c60500001c140e0112024070f840105440720359401d83d4010701d5000444100142c0090745400903010007000c074290b201403101c010f81e43d000b40c032900d5070f5a00e035150030041c00e15051407090410405010006040114084050300142c022002c41843c111000b1030343e040041c02d400041a40203010b40006420060782e0b81c400c1024001d1b000d48040380e84c4d42d5000000da8040050040043e0410000c800025682c90011047c08250b0319502e401c00c86650218481d800d07080e0800d0f80504c0894042100090030074001c0360801400c2c1d8083c0410342040c03404600a03000601805062640320290600d8041c0306007032501c00742d0381202d802d074483d040904000c2c142c040f09008601d4400090400601d06811101000e20104841d24003000c00ba5912034007210281c0c041c0400b00d503644010005260304800400c2018003906600d14080e6440740703050b003170b401240c1214040c901d10b5084030140c0041c03d5000b205880b0815000004080103a4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 523471294 1250 523470044 523470047
    0x6060d050c09120106050315101502030f030705090a06020118080306011421090f120702130f0605030106140a140604051201050402031504050616020f12120604090b130201 75
    0x2c0e03840324580050b80030451040154054210400720741040d070507a5030f05540c00c4403c2401c0801180c1640010014803410407440c081240d401c442c0c242144103690900d00c84201880710741e8800e4800900090000c24000d82d18548014183c0003424140000c0040c0c00c404003512601914a00001c0c00e0400d0204c00500a6400340c90000f00000011008583d5910403907800c05103248c600c102e09156140c03200c002200d000c0d0004180f010580041c006003c1603160030303171841d0341d0341c08050120782213140e0461161200c6124014813008481c10080410400c0c14074080c5821103115500a0706580d91500b501240750701c1c2c0610b4201510390304a101c40520010a021812034803d9502264002d0706225003041d2741c18040d84158040c4d4400c0741607030038040b01030040b007020031003d880260094020101085c20407460382e05c1014000042c3c01039031160220f01505506101e014409042c001000160280e9201c50360405250301c07410840b010007402080340c0f20140c8880d0003d00d14051504010014001e40e03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 523472544 1250 523471294 523471297
    0xc0408210904060305060907060302090a03141002030f0f090714061b070305030307140f0f03040c0302150c07080105130f031205101d07140d14130b010b0306060d050c 73
    0x79400036005105181c0e9a2410b242c0e00c10003200c0c105030314026071070302003480f91280c021030b000c41d500100920016030442d180d045214400c600c3d0b0703003004c0c45000040c0ea42c54bc0c05001a42c8601000a414400341c506040c0c1030600c0640180707082c503107420005c03062104044109030b0500c145001d1316010b131994484102240c08a060000c00b40301441b9115000007000030000007584112101e584031101d45c42902c9091150740180d22844103400001d01030b0070710300c400f603d02441d8054001c01004c40c1c210360f290085005220105044a260407000a190f91a43c0c42045248010a001d070300801c0f151500390b110700440070b041040108000c500c113581c0020300d4450022845801c802a10401c400d04040b80070b014030a14511910f84404510352041021a0b0492403807486501c2c01c4c0c0300c2e03000202c4080520400c035403223281414035080d034504141c8958024080700724440e030260201020302002c0c0381807600000b038059100040502007041040a0fa0320340000b600d01c0c0303868690740460710341c4070f08a013240b03175 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 523473794 1250 523472544 523472557
    0x1030b0d020901060c051f240303050304030305130204092001020a1e0807060e01090201110c030a03051e07050607030b030a121809020c1b030a031e02070e0901050406050c040821 78
    0x4004c03142d0400c3d90000129485003da00341c0d440c40205900b4a100d0a00748d0000031440003902285047c00082c000c64040e80100368081d02406150600304203640c0002c003212100e0b0411f64001801001c25054204410906002d00c1c000b40000d0400081c8d030b0703441c00e10610000e18a001281c86800d900820031000400b550301c01d991012040c400b4085200e80e4a0080100f4003099000410a03007039950116800300d000d44640f00003a024041403506510141e40650042090021640300811842c03443c0c000c400241404511030005014a8104800002e040d0f44100c440144240c008922a1000450001d070386480070701d43d8140081001058103040b0748000c0e07140c0c01124540e0000a40002c01080030900d9403508040a9100c0000c8920a040c50f0b521074601c0c4004020901c0381c01a07a480a1070903560981c104038502c1103070390185d190403500f82c2d034907410f036082100c5030b44075000d10003080190300800d80d210030303e10078150810703140071001c1d80d407102d010900b0f00307540310042280d038101003d05044900 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 523475044 1250 523473794 523473823
    0x30b01141206160807110d140f120a11041211010e1005190f020703230a14060f1510030b06031e06040207080910210b01030b0d020901060c05 62
    0x1079140c000d840350b0b0740000c0700030301900007282c113000900182d0245580b0007030411081d0080505445404041c0d030164009140d00c03010940500070b107510000020300403e01c600844c06c01c08040e0412011300e0f425070b8072485201250100c01e01c0188200142ca40c801e03110560000311781140700080b00c0041c0c907124a40d01019400c124824000903440e50810000c0c114101145594401400400b804590401c180c451400050b044207900700041041103680846903505c4480500280b00310320341407441e004400c40221000c43c09800300c400c01c48000c2c0003085d0721580031070a04903240742060301038981442070003510b442000208190362103280700758020aa9408050011f0343e89041c0600c500c0e28061180416000004100b0001600c07410f050083e100c00c03d6200c8502e40c02c0200304010030640110a03c2c0000400c802081045c0e12441c50b00304200d00d00c2c1201c4400a00c0c0c80f44c00c400141a15600f4203035030700900480d03005000503207400b10940d0458a00303207060a001106464014242030303060131010b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 523476294 1250 523475044 523475053
    0xa0e0f0a0f26043b0705090a090507080106022104050607060912051803150c0a120c180e0411040e010e0102030c0a09050d0510152c10030b011412 64
    0x51070300300b0300001d60ba5803201407820320400d1503400b070111303488107203a81210721455402d800f00321164014405082d040900810b035264040d1110900b0040f5001120010006050390300100203868050003060401c400e02d541c90343e00c90110300000e5040c0e00c158800d00d03009520000741078060107243d510031486c6503030110f002c3c1c101c4400c0100080c02500702c01c20f1009001c44034040301c02e2510f00002d1580010405002280d01541c421aa0340c405030031035203c01003130100c0700c01c4c002d000e01070504c13569a4050007500c4045151000c141c0001c80a2100d8000120b29070310300061201041c2000f504015003070040790041401280c442041e409454100c84101841d8008021b102000b440d074405801c10391070320b07514504410394540401c522411042c0c4003030034542000043c01e000003040d800c01c1000350740c03985040c1149580d907555a1520100e10705070100c0d080380c450784800320341d1042d00c0d85501712201080d140c000720705540311580400c0040c131540d021005208002c01450f00d408115010348801c0c00242c4c0d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 523477544 1250 523476294 523476299
    0x180e060403020705040b030d1b031701060503011a0a0e0d05240a151503020903152d070509040b03070b190305011e141203030a0e0f0a0f2604 62
    0x41c0d6198002d014451045d03080614000d07035030500185602034020300381d440440030041d0400319040351009400c203170200480b001c05281320710320f0020311900a126079070710075a69625010090a2003d00c0d0030749903e00f40d2040003001c6d0400e50004600361048022620405404540d152443c5072a44d942c902403011400c9440311100d003008c400445114848081d42449900165406103444104a008210140b0400500b402c44a88254050b194100d0301800715a084814215510400c11045609201541001210b9003049108620400749012814400003440c246680090300e01d000e1079600700d0103607643d58003c402e1940e041200000804e055650190740d100822602e1103052042003503440031a00701000010403003604502040801c059a01520000c1e00300b09644c140c0814880c01694004511a0510b80e00e032011700c0103500802c514400061103405200e105801c2c240c50503100120f41e003040c00341c40007081c6044c402c074655030b80c0848481c181e2819002010803890340080003208640d00481e01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 523478794 1250 523477544 523477547
    0xb09161809060303030e070b1e090a0e090f060c0307030f0615020c01020607020303061f0c02150a0216080318060403050d080f0c090a061407060f0c0f02070609180e060403 75
    0x18100f81d034007940c0c0a0142c0c00c115145151782d0401881030140c021010005207060241d4011041c204042a8181a00d841107484c000340000c0322a40004004403100710601c41800c20401c000840000584060079061800c03c482d00c84900009112000b410b880305110313480c0711030a03400400640007102d051031039425542c0d0003d5590000c803111078050300c50440440c42c05030000059a10469004050b42011006003000c0c40003110140d00f10010320550460b03120040e0344507104882d00710440071380680c0382c510241c00245000002c05000003880700ca158140441c8202004455101a180903000000b1070101e000c5075991085a001410310300480280213025607000c035110303025a0741c46002c21801d4503400c4100300e843c4226008558804268182000002d004018000004100351221410030110340c482c48199a103d030180980d0f26610214010103e03008145950010701a10080c06054102807019290300a18000e40b90041004402d840c40036440b0f4002c0d0f041c3c0d207034403005c1e60745d00d040a140 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 523480044 1250 523478794 523478801
    0x4080a03060306050906101a09040c0e040f0b04060f060503130311120a0906030506010e010e15040b070c091e0515120d0905040b030c06070807020d080301080c01030b09161809 77
    0x91030001a214110001040d0007101040d0010080c0c8c03c000d00d1410000e0001c0000801c0b06038080d00134400500b41001940e81e071480f5001d18590100000f0400040c1c2208110440d240394018025210142d601804003c0d40031007607907403118585c02408031079206420103907840a0a180709114034840c0a1420b241042a00082c224204841d1200c1d1805030701c032034041c3c00751602101d04900044d0348130a080200d602c24506440b041030301801c5d07980d0002180d8120b00c030f6940981c0052045201c001100c000700240c0e2034055004000c502c1741048146002054a01079100c50130502e00341075212404501c0803200c0c0c00d071724061108014140010b8042d04060300e07842e403c44100c0d40d804a0741c0150300007114241801403409030803005001e441b5000c003540421560b500118070950350104203100710700040c0c0700c85804a02440c05400420f40320f615000c1840e20707009400442134101410100519029228100300d00c0d040070703074035642c0d80070300c40754400c03c4580014061102184070321030000003c46a00603030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 523481294 1250 523480044 523480051
    0xe06040b0a060c0c060f0e090703110309030a141303240f050124050f0a0509060a030b1908030a0804020f0307030b01151107060305060a150801180e0604080a03060306050906 76
    0xd0041c0c129070340c0d280e0541c6c21800359103907000441e0b40319100c0883e51a16205040d440001d50500040c2c00c0c02c012440980b5400850300c184c0c5a91000440d6070925410a42000c0b01c800212441d51034510b00030040c3c19010a2844000c1c01c0042007031541c5805814115003148203581003004012010041e0444030187c8820301c02c101000608104c02205200381046100810845454242c64450807800072051940001020020410103000640c0c8581e00c40c0e00034126010300c1e550200398000320f8070801c880c41000980e00307415010780c0300d001c02c040c3e0404000d54201c910142450800d954940c000f04400485400480b0782c54083d9920200070040c3d003640d510305913034940c1402044c21298030016101a9884450102c56610200e020040b9910a400032588100060007a0341c00030703a45d0211a0994450392040d0006c102e100380148101c400f4409028082c6540c4030040c84101e0301d1844070350300e0304805400030300200c60000742602040d0181e00080700440d40160b08000c2483d000121079190704065 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 523482544 1250 523481294 523481303
    0x1505040b040c090209031b120601090c030e0f07120204020d020c070806060d050303011205071d160e09040201031d030708120f010510050d1d0d11160e06040b0a060c 72
    0x32040821181e42610179241c110b080600101410302c2c052403036000320304c4500d600961180484a29030140141809524000d212890780894000c103500740140688442c000361103503550007a0164000f0007000910201101c00382e43c04035415425900226000e0b200c1c1c104841c0d034603400050b0710700401000054035400c80382104162040c0740c44100420070b81c0c00b070124000d85103620500040c0050107084c03140c004024440c0d011a103c180e0783e10010917a01028040d8001580c1c1c0650400038000001d41003407070524143c2c0740c8020010704481c0020b418a4018001a04069903103901c003980c504901c240828481d4450201c9407031f403440e450300c902154000482d0302682c00403100403900014100b08a90305940c0000c041100c41401801d04640a0300075419010b03200c0d8961030441c1040740000d0b01141542102000b42c0318021030303030102400103880c10040c101c0b10b03408484201a280100042e5506840c00c0203236544050f11240c00080160840594450344a50000c400061a0f600f214403146001c3c8039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 523483794 1250 523482544 523482563
    0x705090f010e01120b0301060e0903040f050a1a03070311181305010f0b07060b0a06031b020f07050f041103070c2102060a09080c06150411040807121505040b04 70
    0x154030044802c400098151400305003011071507602c0c40f046401c080034070b81011300001000c82c0e807203c4052000c40c0a9401060503040050b0910603058080ba140e800751900baa01d51600c1440c0c40c48a05600c45c051000c1d04901d4004004910b110748242c01c004c200c0d0036990080c64032200181000e01403400c6420000f80f090020f5000f0300708981a43c0039541c101d441500f0744c0d689051030401e40501e0b582c010001107803084c2e82c4100c1d020565650203010340103070003580d4000810007190810b50545569914041095602009031452106000034488080d03a10981310524000060300101d03000d8140141f00c0000d10b680841000b0350158003060140e5070781e000d112030080465002c00f0750802510b508200800503005140021050801c03a0003400e0307030902c100045c07840c0c144ca0141850804000352040d12660120040d403e40528107030040000742d0319141616843d203850142125680c0c510780c4100055400040340300030a00500304803114020900e50014002842c0a1401a04040044030111020840c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 523485044 1250 523483794 523483819
    0x50a12021504020a05010e0307030b0109090605090f0c0f0114030a0f11040317160501020a0305041416030b0702030c0316151a0904110414180c1005031e070509 70
    0x144804442e0141e60003900c040c00103420038004594032001d50f5020741c2c0600c83d500d0700000103059001043d00a10400000241c2080e4502c0d00c0030541e440074100d00403581c8000c290f40b500c90008241810008030444d13600c414945040c00594980364040d481442107074010082250b0384113190004035000d0502401082105290500f07040180146e01010740b8541d07032900a810740e91003c074001c14402b25000b881e03451320b460603500c86013a0382c05240120000b035243c1040c0401c002030828040c80c011940006416414180441c4c0c0343e20140e00d100140451411101140c02c003802071044484881d40e4405403a0746901168180c945030325002000c8400c02c452506009007425180710344410000d403040d8071980e404600e0200400800050000e440e6904039803071204150795035101b07409580400050fa602d4625142610008243c14080000c0d587d402607004100300b951080ca502238408018104140c480c0c44614445944d400c0004509091442c080c6c00d2100c0103402074041e0074035100894100b401c000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 523486294 1250 523485044 523485073
    0x309040e030a051c090816060606030b130b04020c07080d0801060306180b030709060626010b120411090c0705100b0604060c0203030f031005210a060507020a050a1202 73
    0xc2202c0a0400148050058826511000c0d03c070004440c1c4038140403859918603161041e035940081d0b0182139030f41d040d0004401300601c40c0a80c1d4000c114a043c100068200040841d06800e4051780740b202040d5580304502d01c1d07941c0c91b81501d8103102000100c401c41e64544c03000650340c42e02003c0c56404034040a000158003440b81c007400d015103445807076050203030031010b086002414001804c0d503407500542d13101084109a91203094024129541c8100c8405298813100c1211480614111120000040180020b020000417135a9001c10103829040d5030b501c1d0b0615440d200c0d0720301100f0740d03c401a4018000e00c0d148003c05009824019019902c00c1c08d244034113a0100c401c2d031101d254110b8014082040840e0007039410080590002d03013902e10304000140c8043c516481112241c1403026500424052414100000c4018820b961458880c090303255030015515002c41c2d200805250305d40000070081d42c42448109555a070041c122000702a6600c0d01c4164407040c039240c10014421050b0700c04001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 523487544 1250 523486294 523486297
    0x17090607021b0105070b1e0c0307231e0408151e100e100e011205070e0c040e06060403150506010323010302060d0e031908011202130507110307050309040e03 69
    0x2c120507100c0c54030308501d40d40c810060040c0200740c00031608070350200c60402510f404415101d0008c490415a8914280e14045c0c040720f040d0304401c0d1180303403231801e4543e0641c80e0812101003106e5010021501910101414500d10881c1c10421050240b41c1f0844a5100580c125900860742a40b00140e045030482200c01840d0f4200d402d0043d00c2100c4070100100644010025000f100c800ba4011050362500c01134640b84000380d01892000101d0340f007440c10302c24180404009414150b04084160522203041013550041d03002c0d07000840306c0e0301e021400c03664071401150015139001000c0040e03100700d2a0b00d0300041c5000c540f06c60209007000314a8000140040e6115001d00c03001d03541e40456400c64080c400d00750000782010781c4131a650745030500041400c10140040b500302c1c0043e4496641d40340c000616501060380f0440b10706180c80045401170f07481e0488820300c080d002e80b000403265140e940849000c0094602400e040c00001142d2040c02800300003025144415a07003030003403007402074002e0765a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 523488794 1250 523487544 523487593
    0x7050f0108061e010327020312030702030307050a0306050a0b090901080115090209120106080604050d0503070f0309060f020417010e06040f02090702070807090515040608100c1709060702 82
    0x211050103868609a50340030f0941124100c180740c005103001c5000b030304034121103050100d001e05c104000010411854108007180803692178413a047e040d82040c01000c0d582c0c0c08050001c3c1e0601c04040b860704074051003036000f0303402444000c0c058030505076150000a40ba41c0021074460282403800d0001c601880d050043c209400040300d01c4564862400104400a41240851a61110402242484400090040402500f2020040d200908180c500716240981440c00301081c81418400c0100c1c458020340c41503290100c50034003040c1160700d8070302000204544055131b651288042008142448588958400d011908008000540700c446007260740d540125801880c0680400c206801801d1800c1b205401030040e004541c15952a0308415082c009140c1100140d03d075283c00300840d04c40d0030310010300240d000352402c1244a040c21001a00c88a41e0549101e000b501c84100d07102c414031684882e0800d40c0c82000d00c41301c074200a00141d40780e020903100c030b000500c9201242d114826201c00300112 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 523490044 1250 523488794 523488799
    0x140609070f09110415030c1d01212003160302030c0306150c0609010209040c03090f02042c0319090b16170c010506010906090e011404060b0c07050f010806 68
    0x10902e4601e5040c0684458145405804818000040e83d40d80c0b95014030004000b58902040d09290008020600101903140c200d426000304500c21880c2d030010207080c05101900180e003405220b01d00c2080150a58211940120a03c414141c9200b18071801560081981c207100c0c000703446580004a090340000c0c0c1d8030030390106003003000c19458600940d520b10381c0c0703121050440c2006081c69000d400c0200c120340c10851a500010101c0301d518051040030840011f50608004c01c8503581c96110f41802d010200034007440c2e4499041e41000c0300d0800c00c18036601e4040c854961141e003200300399100c1d0007040c110700511107041c2100c074045006041c00350680d03c6c407800e9981425400c007842d480382540ca0106030780071307072414a2486008640c5401810701d241110008201d40c03d100d0001014017035158813010400020800038416092011030301811203401c014540c4007541c00c5c10014000b810729500c40d200c410000280c2c2141c414004c14148101c403030803204400040c10b80310041d60000001c448159 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 523491294 1250 523490044 523490069
    0x10801020705070e04020d141f020304031209060b0a180e0d0c03142a060f09120705070e010320010e010c02060a21020d0e0c0901030b0912030414060907 67
    0x13201c0101c0b6900aa440b500052030b82d80c9400c0365441d041074402c6085d141040300e4100c1c650b00942001403140040200200040440c40e500d420b44006010814030501e1003501500c030390105d07040c400c543d0450000d5a0004080d0000e4680d904403040541d6804151901d40609007802d0804000010999400e071034105c0c0c961408494080e0340846015030074000c00300c1208000e00c500001e0056144076420b42e041c4403070f07005019543c1200e0f20342c40e12400a06048020356020f04006450a0110300350042c07450542280c1d03210451481d0044c2400c00c0c41e0410020540c1150002060081070700c410500d113442009903c09100084004484454141c4c0800b4040f4000d803030500c005043c40b200508035080c040c83e21150b00103c00000704d43c08904015400f811b42e40118000e00400c0c040e1046104440b82c040080044d507151001192055105102c0941030a54a0340020082241170150888100030400542d41d00c0c90507142456407101d400354420060b2140d0b4001039001000000c07101c0541d5090300028 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 523492544 1250 523491294 523491299
    0x1d090703020913050d1d0a1503020f0c060a05070818030406050307030b130c0212070c030b040305041d0403030e1504060f0e0a050102120615030a090201030e03120f01080102070507 79
    0x102914024100603900c070074203014040803072411311116201c0c0f20141d498614542c000c6e0800040c14004441c402d100322000740d020007025030090a4840f001c21f2038107000d0b0f1034044000c220459802940959107182c0181010011240c003d603001d1841003a80c0e4031a400c9580310035040e56021003000e0050769465104000138840c1c1c0f0301a9001c1d5034000a075103004a5040280b9011480c8203540e11003010700c0c03c2c0c84142409030103405210a0042c0c201ca001d400e8203215898079040c46490307881c440506007554610202c1c0a0511880444016142005c46080e40c2500c0d5428407008000441e000e9000034035040e0305446150001c101501d0090300c40c0401d403602d13210303511070708010b0402450b0030349007659814505010074418030181072000d000f0300005844001960381c205091400802a80c8582c00440004803100802c406690b0484e1840c0000944a40c0c03510050b001008a01480c14a40c840400c01948550710b03002564800d528040d40104241d0f030b1a00304038247d000705032000b0059040300809 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 523493794 1250 523492544 523492549
    0xa0b01030503121b03060d0c0302041b090b0a1b08090604061e09060503061023070b0c03090a081305121606031505011b08040b030106030606090e040605041a101d09070302 75
    0x4507001e00c1e02030303000c8c0d0201e181c0d079a0014088400c40d003c512060010040d2114266800070303601c0c0000e1042c071030700c140340101c0c6c52002401c6c548441601c4040903c20382407402403021160a0754900c00c401b600c40740d541c40d150301022b030500e64502d80380910b404810351100070782e600ca0030503201114942d44031107046403140c00c10402d500c40020111410054200c121904041d101c14801b40300c50020840c60b40e4906960038025548400185030085c418070801c2800302c01c00000a03050811600100d203a034541c203419408000d01c00782a071100b90301800e4041440d034201c80200711500040c0340750004107c800c0c0e8841c0305070709030f0740f807142c3c00c0c2d0714652141e0040105500440d05498241e040301a0f0021446041c0d0312040c07280c00540082c085046c001c001031001d01c2d0507100f0706025040906240102500e01803001900b4040108010700403900c1d600801c1c20402445c1508031814003041501c0d40501d0002d0801103207600350701c991480c0c2010b088001800c19403070113845000b094400003030880d0504540a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 523495044 1250 523493794 523493809
    0x260a0201120e21090934121505130b0609040911040203040b0103050609031201260d02060712060b04060309080d1401030c090c17090a0b01030503121b0306 68
    0x5501c2140c012210003145041c0c00da85103601d103181c0102c045880380b8041043c0001444020010207060800346e43d00402252030444100101501003e4245140440708007103824003500c1d2594491281810010740c29241034440820540d58162030010040e091410403009070307080c0c071940d90b4020208009040c80390030b0a400420219003d04000f80c4050a40000702d412070303008440580d85946540014802c1100501006410481c01d1005500740310884481154940707045c42408141c2004403c10003c00c0404005c8a1104000c00305a84118181d28006521404110b914400185089240300c031132566602c0740e4001d540e01c00c46020300745403c1400540042402d0b04003920042001d000c0d100f00c820290040042e2400f4601c140103a551562030604580b42158000c14080c2d400e007807810b90f015501240da19030305900e04180040d242ca50302c0c4624141020f44002400e0303414590b0000c000e100c0e0000040080c1c030f43c503002e10100d9a440110390782c3c042090040180015008001050383d6241062 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 523496294 1250 523495044 523495061
    0xc020f010e060723030c0c0f0d0506070306060e030d050f0a0302040b040f0311101d0a05060a03050609060a380403150e07050334260a020112 62
    0x62488980101100080d0283c20500e000c0354041503601103040c1c0c411582c84e0801e44400c07600c00440c105400e06c81401c0c0c440400d854042c1c010301c0c482000103074a5554071907501105420406407440c038140745400034098205400b429001c00c0c44490a03034003078180001c400e640c0307030b405941d40303402c204185442c007000764010040d240c201a02030201048441d040c10081008010400100384420f141d0300d0030403645c00a0f01e20862148440427054011550030440c0c11a003000f2017210780005c1400c072400a04550702035040301e07400000109080d8001501540598007483d800c42d40c103485135684100b0031403070b2405405800001c198821021a003034260004c19501d034220050540c2d00300f1068144d0782c7c80e0b130b00254800c0e190303000403d0140d0350369411413080507030000d030440182a24500b030502103903503540b41c1400102804c000e00e090f10103521760a01c0741c8020609040490312603070303a1078007020602c00c1004a4110b10105010000040d00300009000240ca0b40c180c6510580d03410000d4810000c10340f07203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 523497544 1250 523496294 523496297
    0xf03020706060e1806010b120f070c061109040605030a08070b0a0e1f14010806160e0405010e010806090f190327090b030f0c190f0e190c0c020f01 64
    0xc540101d030340c08240b11482d204d400101c01c4504480440c025082c80c241c010fa10590204030f00b0011841d4181c440c200c1c5075401180c030702001c8815103542904903a89209100d02601d11450b103c480703252002c40f0703001000e201c4c400300c4050105540710010141c40321420403008011420800024001840c41c0318526405400904006a4500041e81d01030410000d40d85507074148810310b9202c110401c90380718500b0890401c0f0601c2660307604018a140e503454003d00106110307101d008000c1650703031180400b0601042d0207002404596501d03c625403640900f8018081c10f4061400040d42c0c08100280c5003c0407483d002c020030b102084454400141031500800340e08001e0740c000b000088a04100344510507900100c80c1164861400240c241281e4441c0804d61194202e00d1300b20360f03003010008100301c1c07400d001c490790307010030600c8401410304201580c070800c0d62809002c000154103c0c0d200703070300f4407440d020f0800d008001c11030f44a000c102d500f6008683c000c1000451248050309004250360101c0307006 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 523498794 1250 523497544 523497551
    0xf01090602040f05012d1b06060314030a12020f04050d0b0a0b190302040b060415080601020d090305070506031e0c07020f060703020d0f03020408071707050102060402090c1c02030718150f03020706 86
    0x7d9602e6128403040d04030162545602c0c1c1004208001c0c040e190400f180d41401c000c1c0d403c08540b614001c15025070b01e05003820403a00815107000d00c3c00b5a20480c1e0040c0002440500540103601e0003449440b0110750704090b040c60004a0505420403180700000e0441010503181800c0c00e650800c0010710105002e940c10840c00d01021611000d001a110492400d50701c60301414504400024035200c102c185c0700c0d003003240521040000500c00207000055410403503015440ea500c0030400010002500d4a909110080605000340341d281c1b000148015802980c1d099108590002031012600c80c1145c001c0069000d85040940dc40c85112007509055840ca0050b1410740d40c1c1c4c426600d0701c02d16070800e620301280501c00030b014017410400c54000706000c0c0080c0c200c40c542600040c200745001000703d00c00500004501125228450601248040303c46085441e41025800100664140030080e80d01d80d4401e103011442202601c0c0e82251036080b55551091050000b070110040d4001038030403106c443c0c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 523500044 1250 523498794 523498817
    0x70503041502390c100815031614060f0a030507020a0b0702151024090f030b041401090203030f131d0906100f170f01090602040f05012d 60
    0x1030b800d8540e80c098480c0e111201e030038a01609a0190001c0f4600c4002507a0180396500c460351038200582200c0d0009040082085c0e0741c420442441d20342c01110742da41030207040c180d00ba2094208008109650580001c40d601c442400107111280c030442440340b0b0801003c0c443c92a2080c800c0e00400d03031098035813065402c581c2c140d81d039a000403c0c0a4600d44050780180d1390b5000b210082519007548154102e2903640401d1416030080002c2c2140d250340d40d242c9014198003415640a00c2403d8018545428403180c0b0799642d08241185e100103880440d0800c0c14150141e00c640c1c0c0501aa000c81c50b0010003a506e80b8080901c1a1301c16800890700d4290301d40c1c1e601c130000e584440255000246a25a0059440343c80c1c081c50007420504000d280c5050b004101d1030900150042e0500e90081c0c891b485c030003600241c0900c2d0814940f80d40305100751404c2d808c18141604208450300074104840c0e00f6048049071640301c6006696a4101c100307817075a0010004005c001c541401281c1f03016840a50520850900 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 523501294 1250 523500044 523500067
    0x906120f0f1b090f140703110714030a09090b09150f040509010b0906010804031b17030711010b060717180d051c030606020a0204110412061a0108070503041502 70
    0x2403000819407040da442d080410103e03950340542c00a004500300d04000700c0914013104108035038050503407030400d43d03905064055203400d1030880b0050740d0000f069542e02c1c241d0340c0a495a90348003100940006001a030005208000e43c060080c1c815001400644190344a0307541c0d4200c440e820a40a83c0f02104800d00c51040e200c52144a0080e000d00c400420040800c00901000c2000031300454108103510b0200404240c0c04079545009072403640004603004020706140741210303204014480c154200105001002d60000b4404219568420083c4810490001001194040c00001808086c402000520160380c0d50009225a03000010319001c5112402d020441201d030090003100c040d4090f00760943c8a81100080d200740d40b10f107180034030030b0504100c002900c541031040000c4c000d41c1c0724514420b1805420f000d82d005001451000c0c10842410b06228014081905035840d002c510700c02d4038075142d40b10780d07a40b0b40300f00307815190b0f1031642d140c03580e603c1500e8039004801d80c0465801e100e522102c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 523502544 1250 523501294 523501313
    0x315090905010e070501170c07020105270307080106060f03180606030f1e08160201021005090a02010305090606091f0506030403030e0c0d2003120a050a02070906120f0f 74
    0x4034041c4000141143c61003071080c0ca0488603400c52418010350200d0050701c1c140d99050503520210081d081038541880f4801a14240100307040030b00d2031200420706094524a24106001c1181c040381294111a40d81141600306d41260140a002421007034070313100038501070340100150180f9002c5207030038000700d92a500b0844040ba001116416a000c00c1541070080403148014411070380e0440041a0080d41c7d210b0300780e4814400101c100034845440034056a00900038441a00c40700e5074188203503e0000e00c0c00d5140c031022041203000c43d1070280458100040069198440c50703019002486907107605886440b074003030522544200040d60a000b14640d203e55014bd4040d510a0710085045040200d2460402c00c0011519026041c8210444003107440c60013004410302d1110398070040c4800801c0841d0810b080034000380c1810500040601324141e01000400700746000340c0c02d0703503081b5448840302d40c1662601d01c112100c00c541c1b40b4001004c65501002c0800302407090403644609001035131100150b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 523503794 1250 523502544 523502561
    0xa03054204061e1a042606070306080d0302030610110a140703110616080313060207110109082e061212090b0f0d0e070e0a0608011d030a031509 63
    0x40c41ca010401c003405000e159400f000d041d0708080c094400040110601c818043c91041d8090035000300d1040c0100c0144944100c421340450060f14560715010300082c0c0684214814144140305103144900003a00c00c1c82502c2c0034060050240b182d500c060001204c42060b100411600c5000300c000d01d0300003c21502c21031501201080103050070384d2079810310865406042004a024640820205004010b5000e92408043c0e008100039201d441c0c110998204030781284004081520002d010f03403e00c1484803d0b0070a0100981e1000c60141d240d40420f512681940304018a40218000d440404002c4511416002d80c40340c0d00010110342e500000301c0d581d80410010360300e003a2542c041508890748040c4040c0a48100610149003c110554201c050b00c0b542808500d06956251034080ea2001409081c0040100b44010900760030006202d90051100c1e200300f9406600e0080d007494910300c03041c0011402c8264a02450510b00408010b0300905032449040480809055010400b000f05100701c942d03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 523505044 1250 523503794 523503809
    0xc050c07090507120e0d080403030605040f05151f260403050c060702010507020705060c07050a0b0d0c0206040201120506040b100c031d1c030e09010b0a0305420406 72
    0x112070903c10b802825501d05041900c00140c1091981408034100040c00c907420302d000c0c07618621039607075402c049004141503040143e0003820128540c680c001a50030240c0502c005480640c10320002004000100d013840641c4001c030141e111240c14400c0c0600c0404540a0310100d40e03003c04208018445602c810444040740030580100e4040c10480d81000070b40c1d072000550008100d2420a200c1c040d40d526258400c1c0c0c0d00c641c20000300d2550003c81840458020a005401041c1c0151510740540142d0050018101340394509076400c500244002215402240c06071200f40c00e108a2290500c06400020040743d0029140e0010401a07111400c0c00d42e1450066501c401c445c02d12850004c082c8034001103072541e040b6a0b0810590b480ea10200c03803466075a600203503440e0310300461a0170356291032011200c6a122500308000500210740d10b00910f640c404642d1b08124030390750100b09606840c1020324240d00f403092603010480070056131102c03519643d4150340c00200d0b03403d082c001500303590302a000b810 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 523506294 1250 523505044 523505051
    0x1515030f0f0106021b0411030a020901020f07060824031b01021908310605040314060f010905090c03060406090201020d090b07061e090b1006090e01090c050c0709 71
    0x211400301011580c0140440350622919450400300969503e0b660541c83c9036500a10948507150386e61f644040c842d01d40a00c46161130389425a0010025004043c40c41e02500030001490000500415a40181c07250790b00e403c0507a8840005148006100801c10712001500e00c0600402e9501080b98002c1200e4608424015100c020002824180d5100410400364202c141c5c1d08005907607001503560510b07092604192a145d10102488880f0902c0168800014180004141c940d030100041040e61b0207100f0108a02c0d0396a542140d45000032182c1040300400c51006010019940d00102e800c00580421141c10948850000341005c509940c00c84c0c505507130b000914110b5805100c0107200307100302e003441050545004e010240e544282d100003420302d552031200705510b016445282c2030a00c18024100000344003403900045402041d5414034070f04881c1d40e00000c0852161840380141c400c01c07601000540d10300401c070006407a42002d41d4041c001c1c02c0c44190100740c010400003005103401c50010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 523507544 1250 523506294 523506301
    0x60b03160306051e1306030c0807030606141e03030d14090f0d120f1404031101110c12070507030b1e0a051012020a0b0a0e1e0a0608151503 61
    0x2908498a590190f401404c52880540040c2c1141c0040745404100303540003119100c88100340802050150802400c508644101207004a400600f000030760b8850710080204036210446601e52100380000c05034410f10064015115180d0702c041602405405000c490419600c00a0342003584da050340380c4008202140100090078504008a848402d15a4003400c1e980b11222130003080c9424020341450202d4581d002d40071036250075031007582000014052036889050502d0000c025640032000d0083d15800c1840e46005440c0050496654245400050608241b020010340d07554100c01d1080e9414040e10000001288410049901c52000c0018003185401c025049270300111018100c9158103150070f08205104411161030030603141141c2d00100d1003c2e0902c0014441c1c4101c0c0c203e02059100451401001500107440100c281800c980d075580d81728016038480c001411030b410321640521036442c02c0003000c1c081c0011580012841e071400c1c00d10380103080825030300280c9038101400d494001041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 523508794 1250 523507544 523507547
    0x50109090501180b071407150911100e0d06020c030403060e070e060117090a23011805031206030f03040e0a0c0e0904110d150614060c070e0a060b0316 66
    0x110381102d440600b483e10340c840c294952240c03984004112900348903a00d403a150f203203050f01040c0d46140b60301400311400d4001c5651143e02030051202c00710b40e00108411580050324240000b01d160000540d25900b9012044c000c02c200c903030030b150061310758940c00c2000d0311032040c0c203000600145000d100045080701030035002c242340c200180c0c48210301c8050700d0280940c51703901c540c1114804192403d00d01d0140c480044031030600999090062140c0c0701d07050410709542400210090400c4450b0080007000440340090310001c002c584000c01d150000c0206440c611f1401c04d50940200020341120341e81c070752200b0290b00d1075006402c44184060200108800d1500900035a5103100042c91b0041c841c2e40a000810210f0380e025000800c60307548202000754a407a9001c540082d1500000840310b000300f030070502401060351b07004d04107014603801810b44e10340c02e000b0700706c94000390030500a055084c40e01c01c00301c07071205028045298a44d2544000100e0f140d4900256000749810707044d612101040e400e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 523510044 1250 523508794 523508801
    0xf0305160605190e1c060f05100b0d0e011103040b0f01050d02180606160c05032b0e0102100f05060a091104230d0f05010f06030c0621050109090501 65
    0x4071104100d400c20484055203054890505080f095007002c280d21551000001e004450704941120000110319910042c00b0f0140c002111520704444100708545600701550302d007a60038029600380d164104500e82003500c1c1c2d41e020741a015010b0700009107814020400070718590080d1010350320790745a0340511100c499203081490041c902200c003101c2c0a41c1c1603001c1100400002c104090b8642d000000814503180d41040703690004020400300b0301a00c04d0b1401d54081c849500500d03009200701c42c20100100904000750f07004018903403a01644034003007003040b10201c984c00c0b4034504501603000350344c41c0e00700345026840d40145607440110702072420f0824400b00508035030100302042e05010440b441c04014004440a80d982c4003030a1100340000c04402400d0029151560b820540380251102801040c0f541648014850b1700240101a01d416448041d0f45082c04061701c11002c1000400109000706110887c010196251100960b01c4900107022107400364000880a9124020a01045800c0c403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 523511294 1250 523510044 523510049
    0x4080315010801050a0b1b12220509061e04091211300f130f0b190e041b0207140d080306010f180303021e0f0d05030c040f030516 57
    0x41d1541041d0700d004001103030400c3d144210780042800242000ca022501540248440360420803205c007100814230000c0c0951181d03220410440c01040f000d03034010214620340701205d6000b80110034607202d40b410004140301c8014108001f40250030000c0139922a030190400803801150105540144680c1c0034000100c48038034984903070032070040a107010800c40c00100f0001034050080c0540f0002c130402e20703548e10a540c50b20764003840109452803281004c480e04000c0c4e0300b01140e130a0319256540e905902d540a05c020800c07505006003060158580b20780030140c4007100040000c00c0501e002c100410410304000b17416070040e08180010300286802d100250084030341a41c40c0e1000820a4403403290601028000b141000400c040c16102c80d40306034000c01c21103d6101c01c426100359607103400707596190307241c47c2c030480e403080024640903034440070800509030000f80018207015054550102d6980c2d0000b803820403607100a001c085a910f00065000c1d0295100e00000c252002c400401c122406001340e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 523512544 1250 523511294 523511297
    0x30a290a09050d1107050d050a111c0204051003201f020c0f0102030405450403030b040f06030507380904060324060b1305091b030408031501 62
    0x912440002100003d0b008a12846481d102c694010600caa2904022842d0301c6180d0250b14155848140500802c003281c551344110404100d01c0d00742024401e50071050078401c0010034a039400480075042c240c11003a44203007171158940b0040d440e950750100c45000d205003520405541000c110342d505002031a100c2da0880c0481d10180354075030f070100a556081d22040240251403c85180383c1903402003007607401414000700824501c8400c21034010080986030720340942c1421801d14a0b403240313900b404400c031000c0d0400074601150f07900c3d03c0603405440c00412464001e9982c8c800c20400044034814080518414805807020500d404405920301c125988c1c0051420100130321781d90300592104000d180f48000544444c0c40342004000100140702c0c503400504001010320843d180c2c0c01021410f914840d00d40030003000050b0310381c0650880c501070078041c0040800485420303c482c0c60030703407402d9034442a0050782824035060a10040341d640c00c1610304603035850000c42030106807270700b0240751150080203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 523513794 1250 523512544 523512551
    0x40608030c0c09100b1b0316121b0b1008070f0524040e09010b04140718080c0112020f220e0402060d09050102090a08031b010515040b030a290a 63
    0x41d40b050000c3c54840d11800d016030000156000040c002c070303112546c4890340002075076201c14148500c0700202065403001c480c040703903131110414a24003412402050518151190145541965551a8118002e49800102c4403c403000080c10b95081001e81d0141c003030100190304451400003441001094070070b0340c29550b00001440d040940c1018103a804441406000900946415000c14014404c0c9089140c0103410204005180301d40b2911880c05104d0b0756680040380e624410044504580d503000b9001d6603004480280708640c400c0d0845802c13070790480d01c010301e002c0f0b03400c0704001d56034000c107010f0780415036010f41c0040d24850760083ca8000e00d402500080036151581c002901c82c4622842e103561aa60b40b0b0010080c42002d5046e940c0042c4041c1804440303540312400b40d517607a00880f100410807480f0219907058003d0600441707024030186114176642001764010480a0142200038a4041c402d440200d408100c050b402038080040c0d818103000c540c8210030b1000b8200b8001492540030905 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 523515044 1250 523513794 523513801
    0xd0c06021c08011d0c040918020f10021c110105270a110607031101140628031101050712091e0e040b06060f07140f070807060c050c040608030c0c09 65
    0x420360480b010705020a548040c4c0380d8822800c207400d030260790001c000c0c0c01d29040ca06001c0c5010300c8400900a40200c58a03010804141708001401c803040000c640180c0003d80d50800d80003400b030542484000c41e041c40c81c000b0080ca0075150841d0011035005d4421085294107192040344007800d03111403035251010b800b405d00943c5810f10003d07208156240180b0000601e1401c0c54415081c80c0300141c100c00003401900325003444121114029100c4a11a100d030403c4000c001d030100c2c4010460303162a0510b4401b0b1442c544442c1c40b4211030350b03000d6040c010304010391b400040e40b008a441880c0c2c001c0c0c0f00d407040c4a007811201606200c14024400d0100c150750f00501203003100410b007642c007507840440043e503641d5000100c0d2190264000b040032030140803c0d038808201d46540ca401c950a042401c840444100f1520603680710401e105800c4180c000d58003d008040c032030721609000ca0b000d8811146100001c00110f02120425841403060f504080340004808106110313684098004941d11600c81c00d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 523516294 1250 523515044 523515059
    0x3180111071a07140109020f120a0b06040b0a0806010e010b13090b1f020129010c03050a091509240801140102250e10030b04020607020d0c06021c0801 66
    0x482405481d030810346414902c4015a0000102d40f4160380c41080b20700031000720107501d0b02a2a802004030310030500c8210748c03c05803e28502080342111604002d2918421907141c1e1114040042e080c0764116885401ca44425296140398100a00c40c5800a00c0c07a585003881071030100c441a0810305103650200501000046511108001da440d4a00c2c00150441202c00003015140c48d81c655071030320000034581444554040d4055000b44000e03036000e41c400c2c01c4412440703540a40341d200c000d02084102e54031801082c403940251425003190300380201d03155201c0f14042100c150080050300080d80c0030134207012034494552000940c0c6240006036052406038000580f00400501400041d0514424a400310740e01c00c0080c04a1018905c1444094600142d26001c2941a0b4012507202c0c8103c000801ca5014002a05500300c0b03406ca03c0f00351075a00c03241c0c20008198450802680c0c0001605820000300f00c0d982e03e48002800190000c20140085a4980700042c00c461102c00500400030010010384 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 523517544 1250 523516294 523516303
    0x4020609120f0105070e010207090b0604030327090501140d02102303010e0601020115030804030602071502030f0405010e070602060c221701060504091e02040f0e03180111 75
    0x12104489498405070450095840c0820b4900001c4066083c44103001080303410080c0554003840a0342659000d9454030690b800361044082e1254022008002c1040421701c2030521441c0c8940341100160640c1414984100c030b44042d40004600300d54480040050500038a0180c0c7e0045c025a83d0142180150300001d44124140c00c4142c144010324510200c4030614070580103124255042c07540d01c95031500c0c072980c0310480132102c07a400756107043d0000781e103c1300d040401412641d0208602d0f00d0a1706596694010b0b42004e81c0484144291130000c00187e4180d00140d441880407200244042c60705003480c0d800d403620b0001d070803041d4000c00740600c200c65004c80c50719130116240c02419501c00d0100d202c03240c0d01031a02140d40311b00c2c0350484007042403070750000000540c40c041c9000740050b5490720200011600380b158014008210340e004040c180401c04c103160059400200000b580c0d41c8500801d00507aa901c0000303400380e800000b5000c4592042081d980d401d100300b071800050142c000c022642d40d9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 523518794 1250 523517544 523517557
    0x22170d050f01080a1101180602061518130809060c0a21050a0302031e0f040501140606031501020708060c040e09010605030309011b0c0e250504060f1b111305040206 72
    0x100405110f042045c0c0c0d000b440d442c000c00c1407101104841903543c10340207480b1041a245232603985080c101072070362890001c800905446000403410826203441040915040f10302c18215004c690600044202ea590320700035000e004000320140c891941a03203803060042101140d0210940440040300c03c21079406016104181000d041c01681c0e03460f03040740e01541922650700c403004d61080740100700346c403000d5401c1c943c040d034868002880002c500010b0500d070070b40200c41481c3c1100c401d00025100c240c068000034041c49040c01581d4940fa01ca212090070088102d42c561000d08001400b00801040000c41c140d21042200080200d5402e00300007039268800d500b0170364100300380d981944040f400c00b0202010b1886d40220700c562866950b001c0700c02c4248044800356500e40582c02881c4a01c00c003011090322000007030303440c0c502d40f90030308006540110a03100d000e81001460094030700c0e07101c124900c00d80008e00a0440b000700300340840c05c0146521480c2c1d0380111070342c204401d220058a0b804140c3c1d11 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 523520044 1250 523518794 523518803
    0x100806100e1b1306020d020f071a03061f0503010513110d090c0e07020c010801050409020d1401020f0721170a020901030207020d0312050601110622170d050f01080a 72
    0x7501e402444114560183c4941e403080355080180c001012500042e1802008000307809603071914842c0d1640c070b034640c40300d41304085444c210120132880380d50700ca4000b990300140040c90f0328400c1c1c100d5210700c010060f4010740900801c0c00040140603524011401c040500f001d500148406040b04210048a01130348076544070303c3d603c0d61181000c1007801e4014038050b01800c0c1b011b811038544468002c0d0b0300e030102e0504c180402c02c00e4001080ca414140a2850019005842c1c603040180545c0c07030141381440800403111075503007030010b044514100030003800040e00440d0414110303c0070410700709600c41203e11000922100320003d9400841031031129074080e440c41e0006841c3d07824038005030046e100e0300c40025400291810b04504140e04a0f02c1801e03030300007030f80782040340380d455500646180c0784c1820740580d5a44034030b00044c0304207000407500550104900300d40003413420640d2407050811103004810800310022401240d45d440510035140e101e0a40300700c4420a501d80184180c940590780c2c000b40 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 523521294 1250 523520044 523520071
    0xf0c020708070909212304060305130f0b04080415050702100201020306100e01180e0405010b10050913091703010303021002041d04030e060d0204080f063705100806100e 74
    0x80760041140c0011820052006e1171108210710109445034010b000f12400702c4d280501159400703c0f40500d0341c299981c0100044c0c42c268043c1c4510038014030050003262481d03030402c408110501d46405525508a140c0c46160700c40340c5c030748100082d82d10000309941c1160f01c1402007091985c0c84244014001c512400d012029104880c0102c074050107440c0d40c00780b510001100019107040101c0028402c2d40114020040924031070704112580b514a040b07200001c60500c0a0612072070310b5030409100071100348000030540300568400d1401c2e1005d0405201480000c401082899010300c040d480b014102c903800c40c9420b050604800710400c0025824460140c1c0e50000f03010140a10306031041044000d155a0b11400d2900441010b5441400f03005010702411708004a024400035245000d540055200c1441003240c44800b009062000c3c800300214408a0703c01450628502c150380c0204403080100604504000641e441c00d070018014440c00d45c9082d10420050342c1c0310001c150400010140003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 523522544 1250 523521294 523521353
    0x1110a080105060c1c0f020d03090803010519090e0102030402010810030b13111e01030b190e041a070806040507020a17030c090415031b030b04020d060f0c020708070909 74
    0x40c2c98003d490f22030701c07540b20174054140940307074000c0080300180b03966078201c66820003441c004401f560b4405000402c0410144010b0010345010700440345042c4207081d00300741159445060b001503c1000341c14900c542d60001c18001956031150500798802811452410314500c0c42c0e90301e00d41c0610041508604003e4038405400704049081c80610070b4500400113410b1000001d8040d04960030340c6540e90200380307000520443c8e07003011441c00740d50407108480106001c0c07802000314100400100116942c11418650040703010410100c01d0241e0510b079a4084035103880d90030f201c11140d0142c103030300666010400441c00254003c1c5015040c80030030450701e4403030310350841000c1d41c1d000300000039a100b820031424a000c0000410b0302c41c1168020b0243c01000f60106801c40c0303158096020140200e421100014054203008402800d8144190700c0090300d9001d1160040803950980700110050300001c0c01000403c004000c0c2d90b014241c020420496064296a2800426140340c000700c1c01100c0503492 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 523523794 1250 523522544 523522567
    0x613030305060409200a0f05010c081e0a0305010f0501050f091018030b160c0215090a050a090b010f210e03070b01032316030f0f050d0302090301110a08010506 70
    0x41c103403142e402140c0c0c20708071070f05940c42404105c0d03d80341d83c1e006520301c010000e0840580c40108088406c10f8640d4a1482415110000280c0c803204100da0800c200d44800d00d201c41184000f0407a15009a80014107541060b00c80c000034401607000d4cc0c1089428008680b4110b03100d030449012080c00c6a20600c4144800e00560705284500749082011070404400000c0c003801e0001584a505000c007032280c44581c048082d546540c503002c0207500700d00004c0d903200300003492000030f020001c3c00425181c000b40d07488001030036084580d003109148544400702c140d00c1c1c0d600032403100c10088203414800038850011640004000392007030800c1c220707a2141d1440e142c02034103000701c440360b940151504806e5038407814041900782c00c00070114180a218030508651020119001d05041010845100781030302d5038030b07150111440300e90150b41c0300040300c81c0b4200180d410000e5414031140b68401680740c00011081500b100c90700c0071a40614002005403604035684441c00d907040d180c1c125012504c401d4010b02 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 523525044 1250 523523794 523523801
    0xe10170705061b0c0d05070303140c0d0c0312141303200a17130e060103021c0f0605011b02010f02100504060642050d0204090c1106130303050604 64
    0x7100382c000c0c00000f030301600f2075981407442c0d20004581c030807100301c140c40c40b041c00a140c001c030300f01415680240b417003800080d05c1422882c0324120191b01a84c14201e40c0042d071070502d401700180300c001c035a003140d0b04010945c2100c024524031040020420001c0c6641042100024000742101c0f101da1041c8100001c15008240c860340c0101d800c0620030035107500c080c2d010707604c0542c082d040c0d0344d943d98080d0300e0703144400a06c04c40c1d140c11106424113a44624050004c6100c20010b814541815020b0044050106140d00350406000201c4408100d2111144400b8120348807500414108982d100c05501880d440380609540140e0a18250a140d010444101e00f8400320b5041c2e190010709080500c0306104c030b141c0165040d0350011891004d00e0666284546c4031401101c9129419071412015107002e103003d0b214911210b196007889413400503008884000c1303a010350010314019584c2c04210b20410750214400c245a0074070350007040300f030401800603040c43c00d01c0b60004082503215800115075454941 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 523526294 1250 523525044 523525049
    0x1091401090b1e030a02121605090d02010309050a060501170f120d09020a0902071a06130506060903030a030213050105070305030a0f09060513060c1d010c050f070e0a060e101707 78
    0x2d0284c6900302000d51001a5112640e14441d5522039004a40d0025100440b24801c400640b540c070702c0d0030554028006002c0801200b07a040c980d642e100e1802285042c81510b003020b01c1000b00003801d6040c0405401c14040f0340101c80e0440e440020300b030749000c1000035005540d80c01c0340c0c00a0385440f405101c0d50041c1a8011000390402600c510004440e2043c0d0060008207100b11028849400b404015103103054049804503404842e0560851010031668040383d00090040c0ca00e0b81b40c00400e2010a14550054081e040000d50004150144084854a000c00b8000034a0042c0c03410400b520010540e0102400d10603459070340d40d41d401c84030001c65010341e10705079000d0002e01462400c200e80440c45840050301356440e500300060783c2e821520402d02800314007e20308500c1100461500111550b5003000700c00c803000d00c1070142c18404c0130401c018007401028140003035480c0c0d15100d051201524296444a200c0d50b4032a000d20070801480b0f0304900c00e48460f0842e02d081d140e030007001a8030303011031507 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 523527544 1250 523526294 523526347
    0x206100b030a06090213090b1813020112050c040305060603060105061e2214041b14070204050414160f061d090103050706030b030f0318030708010c09030201091401090b 74
    0x141c001d5210750031b6a09408031142e82108001032170482091001d54608508006094010000001c0310040500c100d5011280189400310b00d100c9540016811640160740f1a48840004282001044410840701d0303400711040d000b07402194908004680c6500030908107030a852800450001c10451a20586030795100010880481a0a42450100c0c2d20a24041d04801d620346150030710550406004043ca0401503500101c20021066401c44903105195042070f242c420801c40d1602580e5903000d0705004500880109000e00e5000c420207141881d40c10041c060301c1c140301401c0040010b051024001c039001810509000c00094801c1c5402c1000719015a43c8040514000301c14001d000880006076031150310101700d8000d558040640c0e0300e2203c2c811845551003000142e2085e1150f440b03a840441c009000c5074810380d280c01e207071400d5640c0120b504000030030f182d000300259a0700036039a4005000c01e1040c4164a900100002c202d48040e0280168111000550004203003900c1126811076090 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 523528794 1250 523527544 523527547
    0x1a0a02121c0b01412208060403090302010f20150a060311040b040902030d0e030c0901060c030c0507080d08090c010807020a0611070b1305010c0206100b030a060902 72
    0x94064410708540000362040c803189019618010780d40181455000070385541c2d43d661003401c02c0d004c0100001d0031100720303000b41c0404000144003032000b00050302e000000c200d04a041c0fa55007100e82403000100307074440e620741e9000b2018800802c2d0001c15940a4030703021b180455807490b800c0001d82c1c030710311210501d240950049004026802001c25001c1180704890032880e0700d0344401001d041500c0d400e0101418079200c0200c2055149801c0e80821040b03100600085103030350580d000641000c042600c0b0101182849081020500d01448060030044040f21404501d50400700002c000b00e032000002400d1040000f00d02d01407080400068009040c4d04045428400c14400005c0c400c2c0c0c41070ba05500345118000c81c00c181980034400943c8250030382d42c020a1810b800d51107010140ad91154040c03050302c0100309080120f103264819500c01e0740d083c0c2c03142c000000c103441d289086400700030102d000c54100d00203000c1e03003044c0d02203401c040b40c0307000f03504940320344800829030000e02c0388e9401200038910 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 523530044 1250 523528794 523528807
    0x20618041e020c0606150f094011030114040e010e0c120303010b0313140109230c0306011419030521090105030a0e031314191a0a0212 59
    0x1001d800408803402050f0568072907440c2c0100703021003030030032001c403d000d000c091200880340d14504029040d507540051001200c144080b140301c0f0385241503099811202680660081824481e90207910700e540d0030141049040040070051a1781c0c00117000c0e4818030342114480d0952a5900d4015201c003c8145c8000c0007a40d00c8109030070b69809002214a0250321340c0c0d1a808150003001c4280d034121395003014160301e165240168410144030b00002291810306121241000060920414042c5881001c3d01c000e050400c04d0b0f0380391262103c0102003100d03800b0f002503500c1610041481d5045502c02841241c1c0c0030548000115251032600c1503a400f6109060000700340000022421036813403911801d00e2900d007a100c21407600f807088000d0180411000c20101e1240005503100d60810032044040d0ba04001216400100c820959400034100034152418a505031420981080e80c403044030b0308400106240100880403010342100b07006000c1c00c040f80610f00305000740142d02c04490820007156543c0c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 523531294 1250 523530044 523530101
    0x1050a0e040221070207230d0203100204031a0c0c0703060209040902030307111c0c150507060c0309030e10020c2e0206040b070309081c060f08070312030902061804 72
    0x40f0483d02c2c48010302c503000e800201c00001da0301d090020f12652a441e10900740b00018071150400b16402240c161046c0c05120602410510140c4003444c442c5c280102100001d20a07841031001c080c100102451003000406603900e4005107000840c0d074807240250715120103800003001080c01d03960181d01030100055510402002982c1e0701304c2207804980784009020701030b1075465040c600a1000744100b1184505100740400160205451350303aa240580c035204907075803054240c807140e81100303020a403200110380805400c141d40000c4100c0c2510440c84000103004000e40c0c1e00b201e20f00c040d004482c1d0900c0c004e29000076240d02c00851894256001d4040310000000b56124030446d03058901400d0280031900d160b10a01582494580161440e03081c01c50b1a8003c45103100c5e45203050500550790680025038441001500c00105680c0d00a800003501d1400c1c00016091400380d024101841d1601610059440c4820b841c40c1d02c4003511021140c21550b00490001d2008058140382e4400b405015403544 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 523532544 1250 523531294 523531357
    0x100506040f090c1b0f061503200103020f1e040503030a0f030e030301060507030f030609111314030a0f06090506040c0311010e1521071106130201050a0e0402 69
    0x100d159210400050f810b0010455481c030021a1910300510800c900b1808181c0306407801410034041c440002d0310401400190038100003507441190354850f52480d4052460310041030f12400282800d0035450880108000400b500c0f80c0b01204621502d07603180c05c1e92056019054402a150141c01c0301c1d640d544588001d800103541c0041c0000280c107006032500c0052000c015a41280c026403215030401c43d0341d503825114803401114180405589140010320f408050140d22181100b2140043d52000c0141004110b9612a0004030084811006002c459203000941d180100e80018a03030054803086d240c80c0780901850390001e0f0151003000140010b1140c0a0b001c20122807140c89254018803a000064480d01407132950703a0745c41b0362074a807086402c02031000105010070718800281080c03d001802d4910702e5000344c4040000401c103034140600c0e1801082026004445d14800000c4018150700003011407054594050400240562600180d151a01078030405503950b50202140b41d91020040d402 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 523533794 1250 523532544 523532549
    0x30e030714030c1605010801030201080703020d36021c051203010f0f14210a02090109020a1704050322080f1005150a09020703052107030c09051305100506040f 70
    0x2400707801801300812844420003011544117031a011041da196400546040c10000c00c00e5007816001c02c28070402c0c48007803007100340c001c046804c0b640300b40810340604082c440100200c1820014941c0030314000d85d1791980054212840340c07200315501d198515045080c45031414559034201c40c04030020800744d200c0564001071391000410b0b152003a1360341c940010040d081c1c020941c5c105c840789085000c054800c1ea010010054039004680c0207204135804105020000d03880001040c0c0d02040c20036040e0b6100e034051542034242043c220a0742820b13101c031902d074410004941c1c040e00002e00c04c0ca46444c05003411100420000082d506203c118901c85900d074030303280302d02c5081140303400c0002d50105c1418a18001c04400646070310041408c0c00c00d040000d601c030200640c14020148031544040d144071105822840210f0460f003800d00301070307001a084c0d4141c18141d0003807000501c0c0501054aa03000d10740703d410031310788021a03035455003400f96911139529040160801c50008c0d011a0400e2000b011404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 523535044 1250 523533794 523533817
    0xa092d0b0702040222051c201f03060f0b03010807090203190504080a0201050f0709062132040b0601050703032004081203040512030705120a0c0f0c0203030901030e03071403 76
    0x3001e41c0004284030b05104200e00a24140e60002a80d2310a850b0160752149800301803c003090b000351301c0e00180a504000301c14040000d444801c140075030032803900d1b200010300281e40418115414503600396195080b40c028030030344175804000587d8500c50b146803c3c92030100f1080c2044141031a0510303a00580c80000c00341d0142d0309001c04102c1d40030b11040346a04c0340502d030703070307908001130400c0d0044864a568040c0d644007006081002c1502d03201500c129103a80310741648801c600408080741e110604004040ca45085240200300300c0465540848194040801d1038200c1d6120014035055005000d950700d02915802e02c02098608000b00000920544180e030080390703605042c0b882c0264851200310340061007604007413401c80d40e10345800003568001000d803d00600b45060001c1d5807194801c111903151485840703a00e07860190303070054141070041600745408043d44015802007a03032481920201c1e41095903038600034030f040d002407080d10a400d030b10843c03840d01900000580e9542e504000300500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 523536294 1250 523535044 523535059
    0x160f030923030c090402031e031213030f020601030f020f190902031f080309010302130e07030c09090b0f09090109080c010b01080709030c0e0a0905030a092d0b070204022205 76
    0x1d41e030311304200020301c160742c003c00900f1502c8075100c04040d0200806c1d5840b041d4803040c441c0d01540d01283c517071584541141065680d0000d0503040003000510b00346100c1c2c065410079401880030424518451140a40568070010750808060200c1c10040180c5a426030030082c200740400c440080b43c0055004045c40729076150030b840b210b00700c0c00c5041081e108aa115501c2006805501d50003a006014158000707520902600c2d9902c1c03107440c10316411142000002e035103c6405140942103100e20014014501c002c1041070703012008680b030750600001640c030441c402e20015818003025080081d040e64444407594454000740d00d11400b8140801440340490240c1c0e00091f41e044c80303640d4000031242c0004e031020702c07207150510922040c0c1c405000c40107403c0d103070b403181740100d0010070082810b40300380c1c0d4031060000d143c194021500040c01d49030034040180849800600b9480140c0316041c0d903000310303030142d40c0c980d0f51001400078070540c0002e020603452140c0001007464803514510031610240c8071403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 523537544 1250 523536294 523536313
    0x5040501081302130c141201090504050102070c030c030302071a070221070e0f0108150c031005090702150709080a06022208030309010525180911090312160f03092303 73
    0x4280380035887e058448651500700400461009801c507582150203100018070b0314403151030b921203c0c075981d0410703249030107062130400070990704114030780082c03031440781b007000c2e644402e0980106803080b07071800ba1084680d120045a1081d02000301002c011000301180c20840e600c0d0f110a031540b10440c1c1c414003540805000144520780481e20718540d490010540c0007036135400d00c070089240c00144c02031300d108071084004105504c0c2ca040c2c0c076000d4800c1e038005100040c24105052039050300101440100503001c803003048041d40000760044140e901040250b00d5a00c40141010103203220384036072021849400b800540c10390040002e40c020000da90080c41107644425080092514040d41444031984000e42540c1c424441d11212100e803000ba1074070f1112036560051003041e680c014a074050540000101d0101d07038a410003402c030038000c20713400840c2401c0b04040380003000002c0035030140000c60034040201c10588103000745800b0b000101450402d100a1800204605401101e100d009105040340c030b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 523538794 1250 523537544 523537577
    0x20a03061a03070207030308130209072a020604090c02010e030706020705120f18180403030605030d0915030b030a1709010323150d02120d1e05040501081302130c 71
    0x2c81c1d20400701c0b03800415a03546940e40c11100c0890003805e491461189184000050b9900300c886801511255149501207842c0450484600140d61a0503468841d920a1900607101c9400303480c12904140800030b810030803544142d000d01980608208180000140c5800308121503014008080c01803048074908900b0b060030013010304c585110b00b030f4102c00500400c8140402001c90001c594405410342702c1c4444034901d00e561480090701d00b100440c1e1a26000d001c58201004041c845482030728007006d22900d03045011115445001e0240e00705912068140e400351000c100c403803000303a440080664440800c0c685510550064540a40017908200d0141459004042e00c2c2407500b0307100c55030010907125802c0c01d8290800a91045801070192108500940d0307034280306d80c268488080141812a4103400010031240106c0000740c0740744c42614101c608141d00909072015541e0038209280c058803040e41c44101c80c42441d9000754803e4414014000e401050f410104d80303c45152500c2c0200218040c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 523540044 1250 523538794 523538797
    0x1050126030f030105041a0d03081812090405070c020303120103110a06021b0a09090b040605010902070804090e07090507054314030a0f0206130209070c05010f020a03061a 75
    0x10b1030000008184014001032400d0340c0301e408401e8003580c8610780b0000d04008144950704000054000ca4034001c100030a820410820881c2c99601001800c1c01401c40015005280114000c85000320340da5400540b40d80c0c0104c109425281d001411030f41c940f60642410383c20110709000c100c45501c501214125141810624034041da00716401801c03070480d101e40c01c210310f43d0503920f035030f58080b5100314000b0f50b9040912901d030202e0b010782100803039843c0c14107003031090f02c4040e4040d004151041000f2000301d1003d0003030740c0170780b40981408108485554009032401c0100d0700040c0e841490042400711054111b8028500040381040d41700c08034003002102d090074546419075002c0a50081204190847c2d450b002c0000300b44036884050503040c003441c0701461500104494804a801c04450a0410350108561903111403002540c0c41407a03903550110b42c039144040d041105108480d411202004820340050304034640d800d00840d100c90410303a0003405080c49120720f40815243c0128842c2c40c0d08140c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 523541294 1250 523540044 523540057
    0x40314010e070b07032f01092d0206030903091302030601080601021c0f0c080a020c01080f160518090406060f0e22031107080304050901120c031506080105012603 71
    0x103c80303030409960791070644a500008040340202140c10491080e442c484180c41480711080c2000051480300506e414a107400c81c0c602d80c0d6071000c001f4511621100d008894503030708540d05840715905c039103801c602280766000312400c4c0d03a48685582a6146104044c0e800396100790026607030110541c40300d0005a85642c0d44051001410640c6031480c1c9001d401094a0201c4044c00d00c2c0402000c0050744400c291900950000ca00607040805105819030380856200d4108080008210003804c0c42004074408850410503907062023408603000400d1040320781902e44900b00500103042d10301c0c0900e4424000c1402d4001c0b001035040c0410b001c901c15100785c40a40c85110300100308a8a41c0c4140010010100e07401801c03010025151030b805020103003400b88400503e1050000d5403114203040070040c00f010160010000c0a038190240004101e282d460307001141d41240c80f40305060000e812079000b03410a9004800c1540c00e0100004a0321416138003405401d8502030700c0502e002d0449000f507124842c20 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 523542544 1250 523541294 523541309
    0x3111005070e040f0e12090307050303030a090506010e070c060b04111201061119060905030702060d0e12090619120c02030d05090a021f031b03050603071413051506040314010e07 78
    0x101b417258034400c1d076401402c0c4004000d003114001951a00020702c0c50303008480a24055446d00b07078480400a0400a013030152416140710b030001d19011400801c0740c4000b800103001e00c1d440e10f00c050b0f100d4490707a200d050894269001030781c1c0c0d00c5480f428012852402e00c2103800243e00c1400c1b90050750f1000c43d11003004444085540708070061a00da000c0a00301812040d14580410880348006a0355407008040c007081d10200800c0c01e010122180b410003003014030060540000b009a048d050381c0700c40441e00444903001001c83c400080400444401d6200c40048c1c090728078000f01030410580000c0540400a2251020722042c0c1d900110b60b03440d002c618000a41240d080c0320a01c07100110f4484002c0040361a01c1e00003001c10000c1d0041403180c3c04003900402099a070024800d0b81e09080c02042c0240c00d800d2110641e21105070701088030005106840d107110703981c41000c201740f040c030f4001c50800d0141c01030000c1d40329600c9040207801c1081b807101040c20342d07180040600720810085070032800c64088 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 523543794 1250 523542544 523542553
    0x10b13031103070e0708100e0c0d0c090801110c070b0c0705010c0318060905030c01210c0905150a1d090402010e06091503270a03111005070e040f0e 65
    0x216a2911169000540201d6141c0901100030840080d00d1510b1440f8030350346d545200d01c0b802d00000c1d442009401d0380040310241d862108000b03e0f044134108035500105500300000b9080c040a404807640440c0790800207195080c41442c5089990311000b4080c00e0100b841034800c801c0e43c0d035158140c1445071401c001455081490f0800166004a0701c81c00541d001c2d09009a0304110340c025016080d0281c2c0004011035100380003440642010070090040e61000e007041c800407049400301c018600c02e00b08580e5105520b81c4072104078030384a99440001002d018082c4924003002445039402c0350011500c0200082c104621151440950a0f903c10110700141402c02079848640044440c10580e122085d0402c2042050a14075161380d40001d846c641101282616400c04a990f02101028603100641221080c031061440c1c80c0c0103e04440c0d101d9050904418918031400040c3c241440080450007940c82c08080002950300f220354038004040c2250b04000c4203c40c580349208840d00d1500b050810b500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 523545044 1250 523543794 523543799
    0x213080313030f1e0812070513050907020708100b010e0307030321090b090607030c2d03090b0a021c0c0f03112b0506040501080604080703050909040614010b13 70
    0x4030582d0001104d000d481e0f01e03424182540d498091039041040110740e00c1c180050040b00756426400410380240940ca0070300e240c040006c85181c0d0104050150134402c406e584041030406008000f4640144402010b8413140e41109800c0c0005100d1280e0183c0455426499001a454081110000e40380e1503140c40d8120380c01d856840a1040000c00000f110070382c0c40e025100440e25022110b84900072000061442d850041c0c001403d0f1944d4000d0802480801e00d200200b1204003004080d040c1c0f494116001611420001100644208040901040a40401e1040d0201150001c0c00e070002c1500342c02051515508012040700c00c60500b0300c0001d00070348000c00c0394510079003146182540c80518581400008842c3d8850444c2c5031040302c000801c0c080300341c00f0008180c0109a48404110303800c201d60342c9418201516140010402441110001852420503002d18180c07541c20a001d4034260503032409103010700041580d410046800e505203400040c50300c00002c103c81c104054070300340b900c0051 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 523546294 1250 523545044 523545053
    0x90c031b010c0f050d14040518060d020909160b12010e13150914030f03070c0309030c03030e0102100b0a05040e07090c050909090a0f0b09010e070801021308031303 72
    0x11180040c2604016074000200c010680d40c0510500b05401840a40001104050041e00e4000b07400b02e240d07082c55007404100301c503503180101c00040c1c0003180f03a0000a96100000200d4113040140020343c048800d1003400644c2800184c5240c000300203425402c03141e91a40a2400709010720b0740782c022015618030052100b01e1560034410342050201035501d90310306140c0e50f68840e05040b8080c8150f08c9940317030481028400e200701d2210003910300341c0155151a2040c184000e0340c0c44014a010180807120800b0000c25110f01c02c0900159040f100940165450f454010009a07850105a00600c50000034030760b040003d2040800d1081c00a140b41113081c80c000911029215a0303d54050300e0141100c00541c4a61501801c04c8113501503646c55598210310040011740030018150b101294401315801001980e4a011488950f1300008a002c055440660300d034058040100421468000c0340300005080c141500600917580200e42401405621000d0b200d680b4018032541c000511140c503000c04c04503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 523547544 1250 523546294 523546333
    0x6030c100c060f0509010c0507020a121704080c0907020d091e0807090b0a06050309060105090414030a0c06181515050910061407020603040213020c0d02010f05090c03 73
    0x80c061800d2240010303180b5200c102c00c03548442d01d07003005103490700e0800001850a2142480b59101c500700a400d28480c2d4020498820a44c015541c40710b2181c081e41041c0800c052007800041c1541d01125034132a1503c5881d905c541c0c600b01034a01072000c00300441c0655002160031140082565101c40f55030b441d001e60040c5103008d1220000780d90b610030f41d010441440c10b0000d200a0701792500c021079800e001e5418400c4440302d039408102000001e1050010003440031a406044440884100e50603480d1800c020002d03100703500000020384400a5844030145e08480a02c04950080200f002800034100f10100d140200000003000140d4003403403140401c2059202200d42404a900c0e0300d1412b0b01c0c0d1000c900b0b01d00d0207a44445080b5050a010001d583d80217005148100c2d401c002e80b810003203c0d502040b102d00003d00000d215071043c0725101c0580da900c1e415100321200b18800c0340c1164031381440c082d009203000301c0c3d00320f0034604140020343c124a00180d0300704420741c09002091031007005030340751410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 523548794 1250 523547544 523547569
    0x7030f0824040b060c0718050106050d090201030f020c0c0114040b04030f15140f0907060504090f09060f0f050a0c140a030e0313080607080c04050402160c0e06100806030c 75
    0x2e5580c0c003501440b80c89020203054a20a03200083c20704a04068180213001e0109049006686c01c0c0801130040703607031100030b540c0c4010302408080740040c100c0c07006030042c1c4010041400d84910109150511040015510419840c00c2e241c00c08858014499107100303200d6030040103c558010801040090030407920001c1c414052000040d900e02d0b819144003c1d2144040d004031010010400e0049900305103070300540040d403020041c40e00c0c900d003402c00392290280e8403950883c0750f5123491401000029070085c4580f0b030f5110900f0042c44540c0c22909008000110078040311920300030014003851041d00c107a4a20b094140c682103030380b26690f10510000e61001640100305500c481e078001c41c6c11020006030580005606911070428100003038640383c068000d188a040000680502c44401403410468080d40c000341c40c056940d160b215024807245440000042030b042440a00103206041c2c40d98050040380120b50f2030340d8801490a0403510304805942681d0701d508140c10110491501d19410481e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 523550044 1250 523548794 523548799
    0x613060204050a09051609030b0601080414251202090a0e0f010207030302210f01091a06040311040c080403080a05061203031003020f0109030515090c100507030f0824 73
    0x78041e2540085800c20440e0751014850320348400611000c19620008801c9803482d514058840b43e145442c1c0a901c210080c3c6154184049a80880d00348180b601442425400700c034201d6101055040380802400741f40c105100c400c10201502160114012081081480c2c00910500c240c0c1c956030124401428005101401031140041d480d4040e03c080c0003801000340207440c0140c42d090350b004459040c5560300c4118181c030480c40304003c0040e030480f180c81d0544a0a51001503140010107100058210000c9a00e6201401080c00010400c02d40c81a01103502c0660382440f030060888030540b1200c03800d0303070010041090100003850031022503006584c40310005003600c00c0b201522000300d0450f44150390044450172146402c0c415807c0c030f10740901c10b00070280707450180d0070703d50340781c10340c44e65017001d20300380040704000200d030a40c0400c111220b130401c0700414005140c228524003401035885503c048011412202d00410400d00505c8010303c5440f90482d084900d0201401890820310a1482c456 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 523551294 1250 523550044 523550047
    0x7050d080d0b01180e10120201080406051f03050705130b030601060507020d02060d1a090601050f130e090f070e0c0a03240f031a0903090919090606050907030e06130602 74
    0x2d5209075013080030000d001c1180c00d24003c4c100b24112030034041e195000381c1e540c26030140030b0b00d0060340d004000301e601c0350b00118001501c0d02e44484811481c0c208459101241003003407004802c1c040003050714012180112000204042d0011030942610400c11a942d4142c00c5900100b03c12401000280002403001781000301c111a1640050b03d181c000c095101842540c500d95240399071030403015401243c90480304450b107494041e000a0441c4594480303a18818130105d060841c6c005440c0a900103010380b0030029425291214107180d0700d21540c003224006112e002e00018081e00040180c3e030284080d03065180c50094050020313000b5003401c1d40306000150301c0e0806424100d08181c0c50350040c141010212000600c0d60034000703680009100c800845d14000340900a00c59000000c46020480a035900b80c0e0a54031200d16900e031510b92200c81e10381e9401c014001d0704204940c1e029106036041121008241e45403050200c08680d1090300c411440d0380700748040786203804800e550481c80352141c0303000f5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 523552544 1250 523551294 523551317
    0x70f111b060f0d05070302450301020705030a2105010b040501080702030c010c0f03140c250f0f060e0d0f1d0604031401200301030b1306050906010807050d080d0b01 72
    0x204d0398200d81c200002940481e10030410b0811440500d40002603041403504e0f0701c0c01d03100e003c0e680000c040071554030096901120143ea01c0c20b4040c3c1c3e850a42142c140ca80720000307080e02601711103c540f0248041d6429400c810480505071140078103075034220807000d04250401006490708400900660154070042c410403140000902540040041a644403c1072000c148001340a464100e142a181c010100701000400800b58041d02ca50004a000715002c0d410800300f2003a41c90440703d00034125542c1d003422a0203103d80c0074140403100c0c2c410070081150b80e00b0600080d48032203580310b06600080030f10364400c0f8054071510755000c1c090000251620394192010004034a030f80103900440f4008244401510170107000c0c030072000354001d1140900c03079881c40300d01c08034114441400018a1144118040761049041e242440c1416a1201040000741004c12070560740f01024810805c0c3c5110f0910042950300301101010601030744141c816080c070600000e50000b13094000030460400c0b2958020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 523553794 1250 523552544 523552567
    0xa14010308071704291b0c040f02090915010c080301060306030c0b03040807020f0301110a0c05010c050313030807121e05011e0e150306011e06022a0d0b070f111b060f 73
    0x3d10206ca6042c000a211005c0f00d0750601040c1c50038620301e0304d40355206102e0400035031101200158094020301c40e41010040e14030042c0c3d4116203100024221500c017000220364150554400c106403405401c02e01d40300380c0c0d21085800d540c031040790002c003180d0f03040c40228010704240e880800c0c00700000300007148200040481079000d402421200c80002c0020070310f4000d001c428880c0341a01c26032880d1040ca1850300600c0700114076a640d80003810480600001010320340300d142c241c40c80c0501a6018018441488081517401188011888001d0f00d854000610301c50110107924014181003544000a8980000340505010007495101c0e81c44c031404880d11503035403e002c0580038140c41110340155020300c0c0d51070b650240702c1c0c1e0051010f42d80042480380c1c5d6071200728040008264281409110031100402007104031a4401000300089944001d20407113540100c444c03c0c1400c81c075603c400c140c200389490309039038a40c40c101650088030300602e8100903040000051080601e00d00b6014a0038081495 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 523555044 1250 523553794 523553827
    0xf0213030b190f0c0818060105190e0a0603061b12020c070e0c0307020f0c030a2013022508032d150a060507110105030a1401030807170429 61
    0x8500d18404e80da040d480f0251904007044070340100c48000c080541661503103d50381d8401c0180180303071284d01482c004030311003c0800c0c48000034040e545100c18103810002a03c402030555800210341003070800f03c0c41c040300500358032921000b030003a07500d82c00d01101000c02c1030000d520400c02c512150041403804a4404822510706000300e42001d641c5a1740d280803a4001d0401c402d01c40f85060b20740080080d0040c84d40c0024a03501080d42200001e929000b103a003403030708450109110541c000b001d10701101c200c00c038594050070020384044403240c03105040c0703c804403a81d0401c1a000b40034803018004181ca00300e00c1c20b652045040c462088054481d0041000c04442d8400c0300d1442012010300c00a80b0b00d4105040494000c1686043c540c0c20088540da4038222000c5200300103040180100000700368594540040aa8480c2d91a921045584908006100358489441681c100c01010017603480b00c0740c1c29040300e08803500000580e052107003c14002c0410004207032070080004080c01590030610b06100d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 523556294 1250 523555044 523555061
    0x3050f1b180a0f05030d0c050d0518030a050105041704050a030b090a02060310090b0f010e010e0102031308100e150406021303060e060402030105070305061005070501060b040602030d0f0213030b19 86
    0x164800d42e0304c0c0c50201490401142e0680e030400c119000c4600000c2c100107071141d000340070f505109483c1d0300103401744010b40464a0f200780c0d051141004610511406601c114022402000c1090488981c3c1010598034461407080b2a000b10301c400040020a03100c0801540000b21003040d139102050070703000580143c2040d0707000e202c5070310000c004001128083c13081003a6110181c0700818803100c40400a08061100d815440c144000b980740890f10383c2c0f082c000c841034203004110556035144c5400c00c0c40da82304600802200b400749070900c403070341c606c200040d015103103d0030116116003951140e85140180d00121400880390b403c0c0d400200c006403260042014800619004040364900340c0105401d66a001e0306038414141790000344a9961688060028902400d042c119550150751070640c1c0100083d034088214200d002c2004106141d0210080141c81c0041344180b08842c0b00e0681c0c0022889102041c5411010b021010400540c40707031b01003640498006420115210100110070a552014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 523557544 1250 523556294 523556309
    0xc060219051305041406040203060411030a0f182f0604091a0411030105040c0e1903030807210509030d0501090606030e0718091e0b040303050f1b180a 66
    0x2140001c8102c1c2201000d000a0034100d60a200d1002120784075945a81c0182c80d20740160340010002c0d1760780c1c840f03400c0f4807100010101034990340d2400780760b1031000700403030b03444400c10301d0506203240c0948907225252400c007a004107255800d1016154079080b240c150f0400c251134400f00650018480e6580005800109514034001c1000307554040e84801003029255903d1217186442d00c40d00b490034410098034190f8000f950001004038418a081e0b9500400c80c000d41c0d8406035240005608074000100d00c0200d0303100303441d004016121900d09179100e03542e58240303442d1501c150214100c4103904d40c01036508900141e055900d007150850b801340c11703680241c01218210740c456800b005031135898441d0300304000404029200c17483c10814900348000c206d814045419498402040600060504500031812404045600503a103442c01c20f04100081b10240c1c0420b18000c0081d005a480c2c030032141c8900c030701400040d200811401c0c000c1c1e2a410658078240005480740001000d81c891071685006003414 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 523558794 1250 523557544 523557547
    0x609060d0c12061119030203071823120d030903120207060624050306190815060118052808010204140a05040e071404140703050a1514010c06021905 65
    0x10f0401d4400d0710f5440b41e60b621007543c01c102846507030380d0611501140314254640544d40b5107a1103c111061101008502c0500020030300c0020904881a00c1c03072261458005082900c0c24032008110f501490304402d18041d41000ba42e101881c1e11960000400a01c241800c41c40c04c01e4071000c0308204e0b0040c8904070b4080c3d54480041c0130000c08070700070907140f20384c40c001c11400c1c5000c1c40006140e400040e206034010100f000000c0042082d2094550140004404a56011440c45410030140750142e401e240418028012028421003500c100401e80f907001d00720580c03076a0203010380c04640792440c0c0840c04000001901181e420402e00080c0020240142034210011070361042040d01a11548094482c030f16000c146001c1303c0380490030104850082c1c165840c001018404500605550002504e062140604125100d82c045d030081d0301880041800700501441c24414260000302c074040d044904011401c1c0f600c0d2580300e480d00b95185c5102d81c40140c2800c004001c000000b486200c00c02d00424030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 523560044 1250 523558794 523558829
    0x1207080601110607020703030302030a0f180b010f050d0809040b04050925080601050904050109051002222105010f1103011706191a10031b03020309060609060d0c 71
    0x1d1100c40048001e1941002d0031841c105441302a59549203440001c4c00d1640100010321810080ea001c07414040680d0418800d90885c3d5040d02007103035001c0c8c000c5030100d51000c000301d2103040d002d54803001e60328068a003401c13212803500c42c0c54954211a40d031030b51040c4c44007100500c3d80c80780d01a8901800a080003010008484112100c0d0050040c80b80ca02c022030162003007109400001c1d0290440340c0594840c162a100d81c1005800b420003088081c01c03034401ea0000c00c0c0c000301c295000300543ea0180b011280b91002c240705034001d5000d030348201050081c0040399054120203c0415603000ca21070800024010464040f41040d01c020b103403c00d0500c03401000400a40c10104039020360004800003600c0c07a4a41081307000d400403000880c0200c2c0c5962130902c600c0500c620207904a0201c0c00401c070100e032045240c2d00030090040300070600541160300244146150080c02170b2405040e504c00600b5550750740c40c0600061400052203917a100b8458004031b8042078a060900c8040c010340c1158191800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 523561151 1107 523560044 523560047
    0x70f0618052403040302060a06060e0310020d0605130504060e07080a03050918090d02010f06080303041b03080a02062d0402190f0f0306051f1a1207080601 68
    0x200d00001380030a0580000c0c201d44540c040c408103010907a100c8c40d08a0b15080c0c50300d58903805078001c900c84000201d05402412101010660005680d95542d00141800b540043c496507042d030f80f807061009008940c0580200105140000c4c0f95a915151085554808144014040200100b43c21000b0703518a2195550700f40815801c10560920074040c1d40c82d00501080c0301c002d0b40c070380080c031000d00c1028022441200ca1000145065070346649698500c030861029442071a140300501100241224014001e8040c25038010b210500e03105a400003941e1554a2039500f80c0744820a90300e0340412182da40380d200c1d0341611401f49100301d0303c0f408803d19625800034181c004c0c079008082030003c000c180c4541101d01402c030911880e1030742c3e000c0d00c2d4003580c0c1305a4030340452102d010900c1a6140c216001c02d12100e4001718615110b01d844020401903800d58810f00050390aa05010296 = true := by decide +kernel

theorem cover : BRFrame.Cov 523381294 523561151 := by
  have h0 := BRFrame.cov_init 523381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 523381294 ≤ n) (h2 : n < 523561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
