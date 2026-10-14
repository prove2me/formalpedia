-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2888
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:02:39.244492+00:00
-- url     : https://prove2.me/submissions/40b26218-e889-4557-8bbb-c200504ccb5f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 519244604 ≤ n < 519424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 519245854 1250 519244604 519244613
    0x13051b0f09031b18150409030318060b090108011812020703020a0602010c140c03090409030e04020d050114010507020a120c241806020a1b050a230a0f050f030a 70
    0x101400703602030080e50081408899401d060040d900c100316048001044e605243c0c40c00700078812140b8003103000c0d0b561441d40d0010300d0302c00e421055400d480c04426140c001c16a04101c5c0141058104950041040138000500128140300d247c2000c855105900c150030156920442c80c0d80400341c09004500c02c0b17030707070200160340d4418124006013100d0300001449400800c01034080001854680c48100040c81460030120000c800c4802c101c03400c0f1000200d11010346010b0b644d035081100c4098100f0310200b2501550542c1d43c2c040c40c1030b00c0b010fa403410400172005004482034864110001d4205040303090030090b8030021041c8800790351050003100e904645400058015007212030550113404011442c264041e900680c07a80c403501144466400d40a08080000e0b40d102e6000100038861062408000e405c030b035505001c00081c20300240b50024440c5d80d103d9047d590344807500380c1c048580d4032002c0240d80c1e00c2c3c9001034804450003813048030f282e54070304000c100188142003040c541502035220044c0014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 519247104 1250 519245854 519245863
    0x3040b07030c060209030106170c010206060f06030a1e0c08060a1d04060e0d0512061f051c0e06160306050f0d240507090909050309090601050f0304050c13051b0f0903 73
    0x104601c1c08500c940c1c640c80c100309c500d0704981c02000f034155006a01032100d144c4034980f4102da1440c09685890381c91b1a00091000141940303500102901d010341140241c6206542008003141104d9854007074030707290380d01040032010142c498040e84030f045d002d10081c40b88091991540c0240a0721000403800010820903092000e0001c0d01c0001030400034008511507000542d140d08600c064450072011840340380c1ca04003203a0061186000d11102142c10035028551104900040340c1da54014445000071404045d80d801c0705540f03140d440141000c075020403d1003441902e08840d0001c00704007442e00c1d1441484030b0b18400c07000c16229441c14446912048441808170030031040c20b81000601841d10080050008400c0d81005007010308104440010400008c15100011401c507085096a01c0b030000580d028407540114202030b1901004000a1140c0440c025502403007e440d014103503510f40381c0d440102c941c00c4680c007800611814032518054103180141c9440c00069010b54545030070600000d150 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 519248354 1250 519247104 519247109
    0xd2303041409010603050403080402060d09080c1b010809070e0402151c1107050715020a0f030e040b120607080a0605061b0c030c1c06020f0414011103040b07030c060209030106 77
    0x422501c03903403a600d1410240295401080359190800c9103040a0340e00600c87c0c200608084c1c41400c003c203e6050664440e03201c0045541c2c040d1440d0b80e134580200c0025181c0640d01142c90b0401c3c01c0b84160b1803954011114940306880200c050451141405d0100c0404a40640f0503030304100f524249541c4021f03d1402401d040f06070340282d01e000701c00c403580082a0307454100c0c80e84401005100340741c001500003e44c201a100591100a40d40c0742c00c6c1c3e800c0703181c401202d82c0a8002c180c038616203000c3c07540083d115800c16005031806e112400c1c50809100303200720700c800b503d80c01e07511031400100200c0c03161910641100c482074000c01d40590f83c03000143c0c1500091001210b4911034024100d038010104440019100150080d001c011000740000c0c00491a0900c400d44000500c1c603000700300003070307a03049408090f00400c402d5211382d00c50900c9490700424083c1107010411422550701e02c030b8400006d036400c4078041d141e2a40f5003003450394110303502c0d08401c000f100c1450702404040e01d642d6080c090b4002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 519249604 1250 519248354 519248369
    0x3080c030d020f1c1104090e0a0614010f0e0f0c0a0908030f0901030501090908120a0e030304060923070515040f030807200108010504090807020d050d0f02010b0d230304 74
    0x3c0b13814449403011044101d40810090861503c00325607441542c41066400701d400ca820f0000300b140c1e46074015400d080040394018121482c03c061080c8101d07036958040c4c10b80c2d0800382480c040f641c45101c0300a10300800d40301102e00030841000516021030b400c00074411a500791502306100ca6550603098610f81182c0004109004041071220481d60700d441a07500410300180e0a010030400c64a401f0b0b0765221310011000d078a4440300000d1510212500b240070070b56001811265689090f0820b04010100d11000701c0e04280c00d0915640c000e41000c500c01402c01c045409016000d28080401824001e60402e1094001c414000040c01140030810032000b50300851016540740d0341c4e494000c2c00c103144141c440cad04182c1e0310404e0800a90348000e8003810346205440004003030300c681c00d000000c4d015000e0020351218a1090090402001003090500c00c00c0c01e480d2440c0f001c040f1030041c0d0030f9401c1d414200b904010610311941c08a00c01ca000410808841d16561113402200ca10b00e5040d80d1258020300c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 519250854 1250 519249604 519249607
    0xd03050702150a140123030303040215030c04180207120827190b1f0608040318090c0c050c120c0f2b050c01170406150b041706061903080c030d020f 65
    0x140106c500160a034009442103018500e10728041c0c0c0004c0b001207143c07481c1c116890012000441d101d030140200e42c0948110000d0303400c080d01101000029600401084810282660700b02d040180904120740c014030305624a805000605c00c40249a100504908100b52041c4079544000700040d0540112807030145000c0415454040c0d40a401e0342201c0a520096000021040200030790242055402c1507051501610345a0516254045c409aa4010800032454120904205500241c410001074803034800d5802a01c080810000d450420010700d0401c0d4004c071201d604149082d29200c0c0c2203400080007000d2088040c6030341d1014280d00e243d00d0103849040320342803007440410000001c04580c24a04100c54041c0700310b01d83d000170340140004000c07948554800c501d50001044c810081c000004400d42c6035a0394540c4182506022042d9803028000c00020410600745154080703103110420800b141031a01d555504600d582c0120541e1104c0e0006102c603404201c0d880c001003981c0300c0d8080f10b05 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 519252104 1250 519250854 519250889
    0x151905070b130b0a050703020d060815010512031b3409021c0c170901090308061c030c030207091109040509070602120f0c031b0d03050702150a1401 65
    0x1804100750150042c2c00345003401a108001880300d8110551080c460b003004205504c4400c000d41c0030340200c807044855541003c00c00310b111000003414007003204400040340c1c03160b6030b10014805076400315412600b00b6017007080041903450714019203105058201003200c040701c00325064008031280c94039107001d60904045052a150700e00c840010007030120088118a001404051800f144072420701019080c3c2c3c841c078040d801c0c1c070700800441c03280410994201000c0d162801d4120700909203a0303003c0f40440c0744180420700e42d080c559080b0480d07110100190f411000c041d1001c0c0d0f0183d4140c00c0c114110f108403d00030848014a000340e00d210100e0320310581d1204185001c01064032001041c0c08250f40c890034041143d40d81c0001d00ca103118140740d8250781d460812405410144c400c030300d01c41c03c0a1000082041200540d00a44403000200e44160342d1001008141141503400036620400107074000c01d01c1c2c00b522002c4103101c0390803000511002a030080c5402003e10030004c00da010307441041051181 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 519253354 1250 519252104 519252113
    0xe0102070203060a0e1b01051306090609080a05060a050408070507030c0504180317063d0903121b150509070501020d0c080d06050a03050c011409060915190507 70
    0x40c560404e140700000d101c118a401e4446940f1400758611440440403142c0d80400d40c1d01442c11240c134120400d04030000c1c640c860001500030341d0300e4410700b070024003080300c0014041004108190482e41c46005010703640c1311444400e000d0203010303006944124040024500041741000b41400862081c0b6a2100070341c501000c100407a54801d0490003540030900c90400080d0748405890700140c4080c400500c20380320038020809016075522200320303003c0d401d0301d40c94030402c0c030307003081c004007c2c072159003000ca103404400844450310148030040441d0481150011031500a1002c032950802e6200800440c0985484005025070080f140205141c7d4a500340140510203226140c0584000c0c001018483c8a0080090025142490141413000007060703d5540206940100008100c0144500d85c06078482c103180c1c0e140c41d00c0b20744d0a0701007860340b11070240030101401a100160001040541040840001d00451030b210886141100004204c0d140c0501c011000610030300c5042e43c0c8490300c403407041c40c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 519254604 1250 519253354 519253363
    0x15030501060f0b071a0a0e010204090504050705030f0d030c03110a0f0806090105010f0c020d06060b0301080f15010308070c0504020409140108030304112106160f0e01050d090807060e0102070203 85
    0x61010104205400210f101000c2c60062580d00c4160400340307a46d4011110004c0c030101c80031074882e500003e0005110515500054000c3d0300503000d0300c0c075140c2d55004142e44c82a001105000942105801c0e580440c000d0f400400c541c81113003004100200301c40e00010751079010b51000004600b407198010315203030340418ac1d55400441038442c6012035042c5000641040403000d030b00010000c11840120441d122140c5e50030b00303594051424040951100d1940a09800902400d5018880e0802620700620005150326450f00c1c19400951580d085440e690119405050305840024640e50009215122071006000400702070b40009481a480c06440c0d19001060703001d00f500354000e00500010404280d032260051000719103441881e030151215035120301800034000703654010b02e000c001403100c1c42e000708003880016070748007100196103160503500603030800b59031340c0080c3c0b050006520080365544054282401044083c0c200600d554a8405a0f10141c040c040c044c3d401040d4041103007010030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 519255854 1250 519254604 519254609
    0xc03070b071814040906020c0303040b1e0f15060705071e060305090309040b030a08160618030c030f03020f03090312010506040308121314070e06010f08011815030501060f 75
    0x500042d0b8481c41d200c46420003c0005024070300c941e503038045442c200840395040721000c0d1804000c1d640c40b071501d4100b001c5080001c4907022100351482d991400c080c0c0d404014188100c00350742c0c502500340c403105d00c000360501d01d5150f002d4100c0da0030020070001c80c1003000401c00501d0031819000d01030528040520415800343e205505050900043c00604030000c4182c0d1090079054500046c241c074910000b0349444a000b00107040c0340d00019400070092081403e80f543e16024000502c030440001c1c0c40c038140e5400304003001d00010998640240042c0c810701c0c262051401506d409414030698407400525640709840d1280598400540300000303070070106420703004103801c42e82d60f4107080ca1919003071010b10031310102c4c1055450302c3e40092440e02035a4546094290402800d007103900c8c04d9040c0310740c0d885560048007803c10065001540543c4203448a07181008a50348850840c5d280600c503040c542c00f00480d100a9a4541e410000b14462490f5264020350007440085420740c5040800003c03200380e80c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 519257104 1250 519255854 519255887
    0x4120e12070e04020616060506040516021506131503120207061b0218040b0a11040b12040203070509090303010f06090308090607050a02060d02090307050d260c03070b07 74
    0x3844400c154500400c0340340860301c2000b14015035a6440c0300090561044110b4411a10b013906502c50500030740d5806a413180c04140d600f00b00540301c0080c103004142c440d05000c001a88544d000480e503942c0640000d401038000b8040c81d00b18022036a0f07007010790301036504180503c28140720403c14000a0b4035401c06900c02400035000300b604101004120400200c81e1301002d8405d0416a411519401442041c1e01c4e440a55020141040d161071756a50605a440840c007506001140c175a640c014821941100c80422600d841c1140b040514400860020400e07681405070000004464903028160f03441350010002640e503070f60500f5400c1403450321581000301081500031040c00051310407030484110324003c9032240e417115040e1406912340701000c28025002400802c404144514907005445007140450544038141e44490500c02000c082003005028180c2d4006038084242c454001d200704a02d020b0445443c0802480b241851070748045c10407240701210f5410002807540c8003ca240b00d4a400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 519258354 1250 519257104 519257119
    0x10e0c0402090315280903030c11060a151508040b010608060a0b03041e031206052407020303070503070f0c050d0c0b03090a0507150215010e042904120e 67
    0xa41002c81d40e1205903c0713000003240105000f00e030100458519926480e070355401c0c1103028607034070350826001d403590900440200e801d00320108890344c060010341c81145815001400c8550f10801810060420904840d42c2d0855000000c14000d00320349154007102d0080d100c00740281428a0104011a0705a0080302048204c00520105940d00c214080888130003145143d1aa1101d09120201c0005041c1110a045020340e01200700f5400c84190303030600854880820981e5901c1007403207480b40400384070041040321400c010644095000103001d056002034205c07410079a090792a5480d43d07120348000ea6030034200945c1d9a080049203e0a0780140c10b0943d650b0161b41d2180d900c10012103102d01810070400808400228540000c202d840d000980100071141426607520003a030f01007695103140e600500900c86c14441483d800d20f03690b0704032180510b000c4107650740d40d221180c001501c00c1c00c0c42e000c10161500b086071094100310450107903015901e840d0031001c5542000c6c203800350320b0f02c11170b019044 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 519259604 1250 519258354 519258367
    0x3060f0603100306022110050102010f0c2c0a030c1806030b0f0403030e19060b030a030c110f0406080d030b01021603030305130f0803090721020105130f08010e0c0402 73
    0x301c14601c4040703c3e030041001d0780342c00c1460500d0036405408005404100441010409080304850300307d8100c8500380c00030860000c15403403960a8410b500300210201b00d00c02e002d000c51000d40b07480c00541104680400c0f4039003500200080308040300d54020340310b007401483c06102c0380c0510072488041c00e087d25002c100c17062640d40d85003a440c0c001401894880345410000d401e040c0a9009030705100034020544510a4034025010503100802c0c4080c0c407058a081c541445c1170400003800366a85800d03883e09a440d03e410350310304030030028070040641c00c1800e00c280a1059121030262a01503c0d0a41c083c080c40044084002d0403242c84400d002d045501810300780180f042d0032402641500e4040c036001c03d071685c4800c145103c142103444d00400c10340803186102e080c0030300c080186001d66960029a180599680f82000340380c2442d120b20031248100c0005000198000c030000c15111003803d045440725aa15111003054044aa200148a94407001c42918242e02409440e6a101084404505002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 519260854 1250 519259604 519259621
    0x801091208060d05120a020f07051507060213030f030809010911040e070305030a0503070f02070605040b030a0902040603060f060e040b010e180304060215090318060a03091703060f0603 81
    0x316000c441800d2010501c0816031549900d00d8050780c1a03000f03c2114840090240c40c0c00c004e0340031000030f40040c002c00801c14840301d00840d0040c111240107196041000c142110040d03258401c0c07108030b035120303800c1000110042400d411000194092020386202c00d001d42006401014028680c54591b4540518000020840d0a80d4001a0800d9400051900300d90714018540324990708068124403001c2035944401da400340055100720021b658014003608240e5080c1c1c3e64521a0084201145040c0014005000154080c540c00721507004003146455694000c54100d8006e5082541da01c1d031102910741204116000f032000820740c00301c140300c09103040d4480400050045c055028050092400300c0d900d4151081e0f034405d21144078043e00e540303566407403001c1d6594246550318035000c0c2c1d401c00011440e41d0048281e8100f034021b1840d144007500103004012440d1b204028079418580e0300e560070804150a592480d0803105c040245607500d003000c9017088100e000b01c1c80a1407281008008108022 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 519262104 1250 519260854 519260873
    0x1120b0904080f13030c03050f07060c1b15020706080606070f0807020f180109050711300d0506030f0d0f0f031404030e01030f2d0603050d090609080109 67
    0x42d80084080d0b8031002210500100303481018902c041c0c0181d030072000300c20b1000801c08242140e110f030045820090810307000300e07125019441139201041480700750f80007090b452070700b2a0120304140010360800d034840220221000b040c070100b400680c07001000f841000d4100741943d401c030800300c2e00350703040c02c00940c0d8031010b041c00e05000401d40c21022035010110740301c411260070240030060910b00100440065585500c03000d1281c42c070580d0a10003c1071110f4016060300c480341c1d202e603024207824142c1100e60303070f1003094402082c4800c000340c0304401101540c0c20b01501160004110105a0341030a6040500d0040341118001140e006682c41000c6c054214801348510549400c0c150f04001d03280300300b80c006189804850158802002c200300070958040e1151080c4002600c040000c881d28440310300c00c0394928160035030032240158850400f0b40da04c0700a08c941040e0104c0110300c558490341c403a400c01c18408501030120301c02d42814010b040c1c104032098003900305513008000c146401c0d02e804a01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 519263354 1250 519262104 519262111
    0x601080c03120c1518060615091c06020a020307060b0901080d0f0e0301181e05280c1214030705030a050c0a1202070603110f0d0b010909050c030601120b09 68
    0x1200000b0101c3e203120080c00110901c0d005002044864608450143c10b11400d500140005000d1a0f0020348540f82011083c000d101c1d103006031a082c00c03008030170322011100d501e0703162000303d034189484400664203000420608903241c2c0a50b0f1208070301d242040544501034029841403410400500c80150000356643c0750042d14900088031640c01001520225a0010015019400e00714000b40128442030040000c2e84254401e03c5080c0070b5044880c0c400c1005d0b00c00a0aa400051050400386500450210030785082d212240c10401c49a0342c40d03d5194030f5030702c03580203a105001c0360418454103240030000490765101461900089e40d603456183e200300b0f28904140722010854100d1b01c8002c0105c2c444090380003d0700c214002e0f800c4406952000340b071154a0019041c0241d4030401c1d2b100d1800c4d580c40841c4105960b04006080300c041010703100c2c14025074104400d0781e600242c6040705000e40c50240307034000ca60795900e060032000101000c05d6a02c1030300c000c40c20182c0031915a101c2003a0706a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 519264604 1250 519263354 519263383
    0x14091305280204050f04020721020d11011a15090a0305010501031a0c0405150f0309010b0301180305070b060607080f12070c051f110417010b09090703110a09020307030b01020601080c03 81
    0xd036024035281c0884c0c111002214276070785041c814100341d489030300041c8800c840c0c0035641301e0013071010824102038280d400781e501698485000810141032818401502560003540d1700065040a1120003c64000c41c4198801e581907034407000104107014925400c40089428058801a00e1402131314004044c411449418020304c1021440160160680161580388201480d09a502d007024400c041c0641000f01016100354640408000d084900071100c9500341c1d03054490505200094480e4804008010506d43d0041d504000d80ca0004c0e0b0580024043c1c5903120303442580310190680583c0311079000402500902c89007246100210704000b9060380c0300c040c070201114058440c0b8000d00c000d045004003446a191000c1008140482c55980c24a01c10325918000c00400030318408122051400352000301c183c1d0440e02052011400000103960b4260001e8252100141d4480c0401c08030b0380211084400a0f90360640e81089684c1030100c91f005254040c010010941041c0000e0f4580200b0026581c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 519265854 1250 519264604 519264607
    0xa0f030f050304090f020306031501081b040905010c050711012c0d02030601091a040c080c0708040f0306140a09051c1214010f0f0614091305280204050f0402 69
    0x3020032108100301d6001c3d01d00040309001d0780c0c42450f030070806500107036020f9109002e480c00a00c80c0c071700d03002d04682c100c8a1910040422088020b0302c1c1ea5040f1001508540180d11410306001103002401341650702c0020f6910305940b990320f81850000c1c4071051500c141000b450781509411a02d4204c030003c0401c003850800700b24041c056000600e81003603140300a406010301c800000c0c821669510419080644610402c2e003c1c031100108000c07911300e90381c90700224915030301250b03210410030080c000492140c403040d440e017911382010100d20001c44e8011144140ca881c6441d40c21100c2c2500c03240c00907004a01400072114179a01e040c1c440012a0440306034041e0030280d44800c1c0d1144038945001c04410b5010041d6000e00d04020084d0602400752070f02c61030b21080700103105c030103454030071007100c1040c1d4454211005100058405521203201a03603c40300070300d4030303e5003076000b481400c1c001e52510580c0720307450313140c0c064113205070b14a43c0d507014501388180800c00942d11003412450f0307181e40803100103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 519267104 1250 519265854 519265883
    0x1240809100525020307081207090f0e16020d0206060f060904110a030c0203190c0303090501180203070b0406080c0c070b0c01050a060f05010f0c03140a021b0a0f03 72
    0x2189815a000400801c45003881c09008000f01c80c0862510003424408049a408802a1090341d5034030803060001e11100080062942c11007040300c0094010b101850075074551039a462007490741010942104103001132040c20300000c0c810082000f40c0ca02c0700390002d44400d14002c0300c00381d02c030503001700024000d68151b0645092903490004503002800014000c120004052040031a140c104041550100e454100030f040b149000005840c001402c450028484c0600030702c080302c1840c41c5900440506407941e8180000070300a0045040184d21a0308420340b04007103004041c0b8060b1554010030800204000500a0380e60000786181d1011104042ca55209841c5803641d141c41c510341d2006000c020049030f0380500c45c0c8103410083c054040040c3c103108061b00c9007402c0b8031003040c1c1e1244501003030381d00c0c0c0d000032034600070000d510440380a401c249044851903112120303240e0013034190310010b801c400c41c65020042d051303c0031128950256010216241880240c2568032242d0001034440135080140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 519268354 1250 519267104 519267121
    0x180403020c010215190c0509060a1115060d06020d020d0207060b010e0103051e180601030f03080f01050d0b090a0b0c0715140106051606060f051c0201020319140703080906012408 78
    0x4030342042354041e000d00e0703542c05c0800e0300500c500b00d040038000141c0100741000f000380c144000b0103405044001d0080c181210b4a84d0b91100075804075640c0110140c00f8006540c00006a101402503940100c101107410000c0c2c0000600040e045508030f818913150074107000c11024a204441084c44050441c132503151240b400c060070410002003c98400d1041c00c0c0044104901051300f4a580d138071903102e40300319880c0c1010713810540c3e400f4080c13550030040b003044440110341d140c01d0031604a800c00007a100030011a46401b00d0f00c0b0801c60700b0700540c40000401a04200003100c450380c403003058520401040750a800d60220405041c03007800200103003c20300c84011281c016030318054681c0401b04205850f601d5004094010342441a248600c00c51144103501001d0038008505042d4164051441c1000c100340c440c06100710101c0c11000c020b009402c03c1c0a0a03440070040007a03034003e403034196403031410a030f04074a03001050b0000310300d94001108100c0030f20341404045541d03140030306100d51959900042c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 519269604 1250 519268354 519268357
    0x106030c141b0f010b061603170702030a02120301050d14120a090501120c090e0a06050d050604060501170c04020304171804051b0f09180403020c010215190c05 70
    0xe600e0704000300021012541e12290440c440000c9940c0103848820001c40c0249080729a20780a8507000407040108804070000c0c0d00a401585c1d11900306499040305003140e0340b01c9048204da4102c0941d00000724203529640410184130300c50b40c0506000e2441d0304217000710f480000140d02c010300000080c614641c0000003408034100c950210034441d511340012050003040318085104550200d1207650796401105000d024000c0c2e210165181d4070007143c50082c0c0100e0b1171500400c1d484000c1d07510380d0007050350364626000f64a5180580c00800303030f9040c5810040203e44041e448103100d454800e0101c000d00f1004141c4511740c0c3d6044900503103d035242c0c1016000d94018080355907080400081e100305802d146e210166406900361010010395454464140c8050b5079802000c888802c1030001e50301d03200c0180000c11030070314003900002180c1c45495409004403c1601c04070302680009845840d2564100103243c1c40c406003411008160408454401c40b00b8010185c040880b070703c603459414140d01800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 519270854 1250 519269604 519269627
    0xa02060306120307240c0813060b06040e0a11120708040507051c0309080705031915020f18010302091008100305060112050c040c0e060307030603061109090604090b0106030c 76
    0x6065941e1829145003030001900c2e2207001c000717000707030303140e40006040d9444c443c0101d442c40c0d40d00c034074000d601e41c1138040004800081003222012384071130307582034940c071800040c000804180c00110741c2d80c20400320324010381b81d035068100d11022090042201030f85280741c80c1074001d90b4a0a01d041e040e100c41c1001800e00340545c104942250000c0900d11410045100c0001e50300c1c020340e188051652113110f030b203490710f41500c54180d05a00061688445c05004100c0c604600e201e0b01b100c804032a04843d80c5401d80c1c01c1148144d400b1200402c09070012404801000303a0010b09280851502c51028009540c003500c1101807010844c00340002802e126000c42d03404084d580003000c0340c11540c0d4038a00d440c0c00480c5258212007a00603146100c18038109030007288542286e0b07440c0e228078140c841c018480f442c0c0005041c0b038101502c4000002c08180c40c0c0c030944c0d4681000008e116940d6031820180720541002a107182c0c0100e01c2c000d448800314141e0100b0a054401c035150100e81c075201c6a0040fa030f00500030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 519272104 1250 519270854 519270889
    0xe15030303071101150608060f120d0206040c150903030302070618050c0a0509040f02060715050907140306070e1e09090106060e03030c1b010903120206060a14030a02060306 76
    0x305014495800503c20029044460001d00400f030188800c000740800500c201300104c0c3e650004118103107881590b8411110b4094420680850071800c06c52034030300300744504000342e0003210a010600c6118110308001c1c00f00b01059620006004100034100c0e9980e1201030101603012501d5010002d15401400101500044030804541e2500700b0644501100c041940301c0c2c1c1d07821100042604150f1100c52041e074001c100ca01c0b00081c540c0074001c0c140d0018404482403d844000d0600c1401240314040c01400f8220080c208941801c500b88031071902440114820b61003002041052980415480005882510846541c10706030144005045840c4002c961005030f9004002c1810b00541c0024111090355446036408074031b0034185501c1c5d00c1000e0140200f60010300e44800d140301850b0340c2c0f01031342d101898210f94241e52510381142e07640c4048030380d40c0140c00070820300403a407524619000c045d2240b02089276054503c100003039555040c00000074000c040100018030b0a07648c9065440e03a14044 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 519273354 1250 519272104 519272107
    0x140f0a050903060f07030e0a0309031104270507140f04090201050d0914070603052514040b07050705030d02030a081f0e0a050a020a0e0d020f190501020616090e150303 73
    0x213442c045003803050031101740c800245007840704a02510001240c078002038158480d40070a41c10b50711142c8280768051100c6800c15140c07240d0090000d8403c40d580006850091200300e00d00d114981242800d9030f07a88103115080c54600840c4060b59180399020510508440000c4d05641d988016105d9000381d11a00f00000e18089080f03041c00320b06c10901078030017640380a56116036100c001c15001c441c001d59221900d0b1045403001d49440d02213040c1d0400102460030880143c0d6100b100000c01030344075800c0030380c074a280440c82100b004400c200c00d10281c28101c000e4022855080c200a540b401891010300800103c1008101c0406034a20785064044025880c141001d484894200c0e4600d402e0b100006054a0040010007981041c401e540318419a0b5540c032010000703007401c0048045040606981c404c0100c841e552140d0b07190303a0301c1d08120300141005003c0500e0480003a0a00d0001803103540c80c1d02032444000401c40c5e00070a41c9041c1e484c0303640e08421079242d89078001c1c0c40000d5800c841c0e405210 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 519274604 1250 519273354 519273361
    0x801060e130c030c090f0e0718051e2706010f210209090a02040501090b0703021e0c04150b0f0f070f03030f0c05070506010b030a0207020301150e07140f0a05090306 72
    0xf4160890300b4070380c0700e03502c5290295076a040c0d2100c92034000d1280c003d440e151070020500051192005404180d45580070f083d11540300c40020f10044ea100703541c41c074031500c01020071665042010f2580701c0c1c1198011410242112a0f08002200d02d0041c2072604208904400c0d00700180610b6440c404c1d2941007404d407003009403451020b0000d610507080d140c071400b03007280003030405040f84c021034064600607910f02d6900c41c03803c3c0141119400c080811400d5004040b01c024000c030401000007402008038006019210400080c002181c817191980f12a510300b1038024408007507203030b0844070a551400750250fa6000c098082010301c0c050f91000a092031aa030201405250f4150408100d103410b02c2c10801408420200036580b6203e0150001d05542041c801040f08421942c040c41d4845c60185002d80342000d694002421900b80030544448029000001d1000112032180554860301a0514404042020741d510880f8080d2914100204a000440825240c851030a8402452000d0100d544908 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 519275854 1250 519274604 519274607
    0x109170409060f14150f0703081803090315070c080a020d0909062102130e0703060f0903020a11010509040504050606030d0f09030308060a050a0810051005010801060e130c 75
    0x18858070420400d141042800b00e0800300c50000c00c01118903c4d00441c0e1140300312000e120340c140c9010b043c0104000c1c14045406c4041c2c0300401040254030954400d030a6207400e441080e29006500f02d0310901c2da04c14031901c10342ea140014100c0d144013145108070010703030340e04a00321106010904000c11701d040c045148610560001028506220141c495141403a01d40c08180c04803801d40c0701e0a0f07104000318070105103070071000340049940d070f0000d031030040500200030507001611103c840a15556024000400c180300c10340c0700f1890359241c1d0700e10070700c10a889510000e503982041100504a5a076402003111f1740da00907421a8803211024005010924103801d2054030340d641141c845000740900413442d119036202d1071118541c2c480640300c000d01241151812240d5803c0100001d40220440c172000c01d807580c6c1d80e8903070001415500d00900d03183c071072244e0364029a900038107051821540704809220580c0c0040c80e150654001d4640b2840800c1808000341d610700302d0191988029103440c603184003d5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 519277104 1250 519275854 519275857
    0x605030a1a010f20010e0a031103040b070816061b081803031918060213090204030209040803041509050c03120f030a0510030b091513030c02040509010917 68
    0x29495510100426400761030211280c000192080e070014010019400c4164051003060354108075204c108000802004819800c503a0b2005a2500c2136000c20440b42c205580070070040c109a140b08040c604051904004059500a840c1d00400d240b0020600b400d204d4060308203c00304540110707051200d2101d001d96844200d8000b640f150002d014070001030316071100c840c0608242c1d03112400440c69980c0742589104d0400742404156182034a5101055081c410a0522100d4078099140143d880003520205402510141c0c0801c1c04180140410400340c0e8510301010f6000340c00c43c40550b40d940c0e8070f10342061407014070000420b03118075110111060080014420011103010340c219001e50000c2518400740d4002d0302010b185c205e5042002031400b5a917504001e0304080741c64124070250b9160f5460081f02803044410405580c481c0d110070805c4003590021941000480070ac0c80e9200c206514000d0440380703080400790050781c440d00440d080a0095001094540d000004080007000e4640945080d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 519278354 1250 519277104 519277111
    0xa0b010902030105040e210c0f030706060e10080705090615120f0105040b060405041802030304080f0d03060e070c020f210c060301051e13020a0203031801051902070c0807060503 78
    0x340e86000343d8604810000192080d0040e87c041c1c9000b810a558200d1a025030300c450b002207118040e0307142c02c00c41c00c44104003074140381d4441c00300490b459007004444190480c009111420300251046d0800148501186000c281c2d141074400008540c0c81c3d102182d40c15034441880454800d0000302c07111001541241c25000340d41c000000801ca0740d980302000250399400d080154040c40811040020b49080c1c0d010a4410038100a056a0000c9030740001341140c205600c2102d150f0081c10450f4101d410a100d40c2c1c01010087c1403c2000d00c1c10600800284000182510184000200382d1070640d03031510000d00403450018060811808880700d0b50307c488482c3e40010f9114851a0071015031864064152410307202d0180019981c04040701842c0005855851078640181c00c444d1040c01c1001207000920b0b02213100e4000316070364103185080c42828000c2e845241c038030f130f45000207220341c410043d899050b140d04081301c05600c552482c100016024400e5102c40c02501c6240c0740020181d4004029511 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 519279604 1250 519278354 519278359
    0x70527030106091a040203150907120c021207030807030b130603030228080f0d091a0f250207050d05060f0a06150804032715090b070807050a0b010902030105 69
    0x41551011808144e9205141d4914181d50355400308249003425030217164000410503c0030500c10300e071800316007108019139041c00003030340d0038070b044102490034011201039290920040444c0c98403010b80034820f00410780010200003a01000c80c0c000c0d4400d03084040b50140081030361005001c40b41104004211398401107026000f1860025509204403900060b82c02164100c440c04103900d81c0e600e49181d200c51540c501c0c4240c140084500d034031151040075016880f440245003844003540c4461040c02c4000c10460740c0c18180800c1190410f482e112000c00003c030741000030070000410b0401c0e414604184c1081c1c1d0880b100e80340785002c0c4503000a92900a6200b80007180050311404403a100b0386060780506c035606209603039a801030720711a00c0d203583c0c002e01914000440080d80003100c002001183c121200d07107002c83d20207001c00030355201d402075144c0d180d0800300c000d2841c01180428a0040342000f401064021901c2c90900005000100c00181c1c00b21059120b0342c2c4402c00310000350000c0c042d0302d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 519280854 1250 519279604 519279611
    0x414070b0a030606020a05030409020f0708031509010503030c210d050c1b0a03080c0901050d0c0807020f0705011b08040819291b161a060a0b120705270301 68
    0x40c0341d90006c10000c443ca40c00030007951030141014a47c0c80658001030b41030f95682010030001001c42c40c0341c00a9801110800315183c0c0074940c81003048a00e101c10381100348250400c0240c8180035000040f251100040125011034806d0355803001c100302d000d4aa1890103440c1490104565129001e000b003820802584142c040c081c0310405442c2d6410882000401088400010421460b600e00150001003014900f10b8605110b5452140c260340d45c2442c54004a203800052052058042c030622010400c248024550a0325140009200107405041d1400c4030084c074821105100c213200480d0041d11002c8101d031040f1001c18550300811307000b54010b48449110035098842c24100007810741030020140104c1403161a404804440088851490039503010200916414480f201c0211001c0c5401030202408500c240ca100f01c0485000414280c800d4440003414011040200309a4201140c00108408130b0340d14100d040ea0036100c0c280780040076044810f41d40c019421119030482c4404400c5d1300a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 519282104 1250 519280854 519280859
    0x12090f0d08061c0203030d0f0612110103050a1e241d011d01050603130506100509010e16050a0504030501110301081005070e060a0201151410020f03120414070b0a0306 73
    0xf140010220301000398180c10800c01040c11009680000c0e513940348207100064043d5503415580004241e10b8800c03603403505108104640e0390380601c946980312040d402c0901828080c00e440061100d007401c3c400c080346a45101c40740c20400c1b01d20310310a143c0c0002c10b20004261712038114a0747c031a0b401c7e80e00203003e0908000802c1c06d100071022100d40c1c8400c502120250703400d000030403a032908000d2080c411802501030541c041001003048500807424246865101800d0400307200c140c0c0c00580141003501d0060f000c2c8a51380030903200b0903115000901c0e05984843e0104421509407245602c054800d45c01d119190158080c3c80004604030b03040b03031048a04c06404507000c50156070080b5440300204408511209503420400c00600b4a12968400061020034000609e40380c0403880c1c0082600c1c6080c0c2103440f045040507400040d211516000508580a50710400b5a980c4540c580c007803e04011717580400e0410984150300b802e5042c420003944d26042c3c03950b0112005030048078582c0006400c19000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 519283354 1250 519282104 519282139
    0xf020f070b01090b01023a0905040f090f030e010c1709210705010f170a09021915050d09080304120306122f0307081606080c12090f0d0806 61
    0x26440d400806030080c1c070080341203c428038006940c40d03254080007604114803540c425a0742c00c448041021f5904c40d07001841c102400e00003111555101c09605030300e024103107004189582000841d0f6540b41ca4101c0c407500d10794004030340b071444071080107100c0340c40480c009842c03440303440261090980681d00003184026a91440000c522155040105a0440d000501155100c1c01c6404866552410012035075070580c800814111300407180420080d0b81c0703541034421450300c003000c2c000d1a024480200440c42c181302a4003110b5900c14002c0c1c0134000c0000c2c0e200e028000b00d40004640c2078000c0c080546030f2809041c908844842e079800040002c0c40e2040126003c00c0d1010a00030564001a0701c000010050500b04c0e40200e80c0a4001c5942c8806c0c030003147c0c140e40400080c0b0251111602410351145c002c06109803c0c02c0303a410000c1407144210400840e241080146d850401c0300c40d04060b000c1e00d0b4002c01c1c50400b042c000b417117101802041000b541c01500005440c0c0aa40d081d596460b43d030001600 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 519284604 1250 519283354 519283361
    0xc01090f1124090409021c030305090f120409090c03020402030c130503072d03051f0c02070e040f0201170c12090a05031b070e04150b04050402100f030f020f070b0109 73
    0x242034195180901c103d10f4581400c5c1e206641461014200d0900030303800500a01484a280d6000c80000e074440c0108110188240305540e0714070083d40c000c003450f564a0040c541070740224090345889940e980c4101c8207020107500303a0f000440d005041107549040c0340d5a2000c159001c0850280e001d1008140020a4140010300070100c0c1c0c2d04c2c100c00340c2240c03220f001c9400912140e1081c5a840341c0080c4000c004107106005030a64195410445003150790a2540c82c01643e018008001c00d5406c80d1400f008001d16a42c51103a00035845500c0c01c812114a1005840b0007051035500814480c85404121652102000a040d48443e55911000d5079071164550b03503a4a4006100406a0308144418100c1160501030407104880a00940394001c0c2c48840f262401641220143d0b0030705049000a074000003a441001416641600c003803080b0b15040d00800c03c00000c0200100800100d48500e1484911903031290081d044403042c1075540740010451400b00c0c1d0403e14094401880304800010034892620 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 519285854 1250 519284604 519284659
    0x8040303110d0f090b090a0906090507080a0504020121151716050a0e06060706090302060402010806090402010c0311010b030708070333020306061903050f100605040b0c01090f11 78
    0x9984e1803145040038078801c076580200c240290400c4126038082540b078403038050007020f48207400001481d8500204001c3c20200c015000b8134030325140905010150368401c00508000001d4555a50f40091a0780c00d0f070010318405001c291911240580803d070624003e00c8000e260780d98000700c401005076556442c1101c411481034030342c00300403018108600524003503007a0780003d0091110742010015150300068070803c1008500682140f02004110360f00503c1141d04814240c901d01c4680c076065001070024500950081c050044034002c0030080c5001b500081030805014040d1081ea0f070392103508695038829404201c825950b000400c6280b042c2e00c1c90000417054403443c00c88022204000741d00000d500280003150000c0080069038039130004501d983c0b035101c141c0e99000810b40f4140303044101040c00981140c00300c521104003040000e074088251019030f54240d44c1c543d640d03c0c4804549006003141d0f03070020700038000d203071040080c00040350601407100429501140410220400c00030412040f0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 519287104 1250 519285854 519285857
    0x305042109030c1d0f0402030c0d050c1329060903071412060912070602070b010e0f0c03090c01111c050d060b0a1b06090605130203010f090804120c0308040303110d0f 73
    0x7008a00003030051601b140c000790541c0e04454241000c40e1007203005079400d48a0ba40408082c41c0139042c54070640080b030400c00010000e0381e0301c400d560b450000b80903203c610428400c6082a980c0c2e9184402ca9081d07101c000c04403124281d99032024104130004484451155030305007000100c07040c001c11018400c603220f2010f0a1030748441488080103030085a000d0340c50641c01d018010004410130100ca0290100c0d00800c13003c0c2ca4200200c0880e854018104e9025050510901409000000300e02c1400202420540110000342014500c2d105031700c2d41e1181400c202d00707000810300740c101e170081808000d004410b10010303403940114503c503c0b521001c03200051121101d2990441402c01500e1824441d0303001281c5407003117803202400e0b2030301954900f0301e0fa045c3c030303070100b0840c502403041c0c62211500b0702c801d02c5a184e840c0c8541c886400b943c07203980c0c0d508049502d14400c0044a18054002c0c60b8080590383d1269102e060003460b19a12210011a91251149000c800da000c3c411048420056 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 519288354 1250 519287104 519287159
    0x9050106030b0112180b0912280201090206040504110c012d0e0304090c120614190302091602120c07050f0603162304090203270c010305042109030c 65
    0x155558180440c400501500c006e008d50f80b05000500b900340c005000c1854002d4001c00b241d00c003001c418413002011a1094250780c034004851005031100800c0c3c0302165000c803000100c0e1005021040628824020280c55035441c1c072003954903c44500c00c0030910140c40c29440030301909581c1381e1a04841c0c0510320321985500c00e10041004a0f4a50080003521541e45403204000c000d05407090140d80d0650003480c209040601e450146040c000c104d14030802000c0c114a01c203030314580110341025000340c07080c0101c000c940c0324005958000c00030944002e4110215030ba3301da07103001480b038480c1c0c41802554414032000d1500d400314981502900d000b107004a07005183d05007000d00540302c0004001110317010b500000500f101140c840009003009100d0158090381c0c9141000d085001c2011460f48102c030300510055083c0043c1000584203d50704080c00c000540341c4840c141070a4050714190005c500512040c0c40f600d4256100710075030704036442203e510807500c0d00c2d9122400c1c00200d190084000c00c95 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 519289604 1250 519288354 519288401
    0x150b070f02130902040c0801030203061f09090507031a0109050a14150a12030216080d020a240912091a12041b0e2a0a120609050106030b0112 62
    0x41902082a403041080c2c8000740c561015404a0203417a0030389600f102107540b8800400543c18144066035101c101c6c1c420003841141c00307140700344281d100c600072050a19640c500110401c08100710078006503401202850f40d0030b0340d0820383c06199400b4083c40d540c160400c004181107404500a01c0071030540745080d14015521464982c4110701d071b07190450340c0241010300000e00c1030400408405c1c121f01a6000c0e1174919104600d13000755441740d03480149594004404510081da011030038100407170f8448548080e8295010766085071007600f00328004517905e441c0c2004200140340c01c1d030021070b041076121040295564040304c21180861f01060b212080104803d2180ca810500700c240d00a200702c000c88500302c0d1039030348141c20380340c00d80040404d00400010301a07050819642007032030150003010940780007000c0340e4107c0540101d034505018810300010000010b0441d803c45d4000e00744483e010403c960b13507004010b0107440072203d22804a8504054041401054000d034083d0103501110380c070300d000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 519290854 1250 519289604 519289609
    0x10905090604110d0b09091216141219020d09120c080609010603050708030331150f0c08010b0f0714030a0c03080903032a0903010906150b070f02 64
    0xd18050b401940d54103e040d0b04160364015221040b0703403030300c00180c0401c400300340301803020082c1c03202241d035200014031200c06883c4d0b02120003a051002c9409140005458410f0ba0700e1155100c0c0480c034080c407442c16405003851317000342c000c036990500c60040c400108030003aa152501e0110310340c0080c5c401c06c070501001c0c030041645901c0701c1c0f00b031408102003a6181e41c0d05041110941d103804550f5161281001481400c1000c0c901138034564000e14a18100302c500054030030303001e808450040ca00507003070110210204030585692034002c0400408140448136040c014110101100302480c509403010700c06074030441d50b03141a15510380c0f810b8980150402120801d81040d0800c5071300e03007920665440340410a2000d00081031113601c07000302591251230060440000208442c859a000740304100c206800c186800a81c804d41a940070004100e000d080c1c50107100c0c040c50250150301b401c0c00f000812099601010780344105900301c00f0700a440d104444103500c1241c00c0a41114030700c048240251 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 519292104 1250 519290854 519290869
    0x170109020f0c030f130e070c02012a051f06051c110618030d03020306031509070b040f050a06140f0901030207020405010803030601120e1e070f0803041502070302010905 74
    0xd0820724503190406040c400200d00d554001c0c2444c00d00198080391a200044003400032102801c002c80011400b07280030070b0010300e020441d01d80641040584083c40800b241c400e03001e040d140c1107901440645015030304004e03a4407504814580c185801481c502c1c0c40c40d004a11910040e100c0003410911040420460000c9008030503c06807404102488280b08130703030f0303900000e10b9000f20303991900c0c0f2110301050400d4200f040a19031007052500400070000c0c190ba0101c0d450044e080041110f00c4c00351244000d407441c14206030001c8010220005e00812003000058000c0c1c01c455084490744040340d00c44a0440786036904e80b1030128400d4003441480912030100001c0e040401c0d0605d0010300302000d580005040d00c1c002c0e4090516500004180103940d68054006510115180c20034072601c2800f40c540c0e81d64810500704d41840002e464019410322009000c1c182c000c05003440011820303500d804505480342c1c030501c25200100b01e60007020324150f0004c42d440301100d405843c3c904070131f40f81c0340c01c1c40040c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 519293354 1250 519292104 519292117
    0x71b08031503010603121d0105030a090c0b1c0b03120717070213050103030216050f120c09090d020f120901110a0605010e071206050901030305090d05010e0604021017010902 76
    0x107441d0784400e0685038809100e6400103501a41d80c140321007401d108050200341d2494204100681400c20092081e6080720480b03421003601c0c2c01c00100e50080d400e01640b8800144c12510000c40000352a040c203d001080a0881d8640200100549070002081554500751004600b001000c00d00c440ca01003410a007006485c0400704001502e44080c03a070001c1c600000089a1006160b5a07a0061041c5541040605141c40304034010a51881c14400041e00803012030071843e01c1884200315900218005100b0003880140103890a80c860400400598032801f0f08103803a030040c03266540c0880f6100303001401c818502020030a9600c2c10302004011900c0c0e125600000020384250240b580020f4424801e080c020641408481d90b5420300444c001c00215540d0115420641802014822983c80225090441c1c1d130508000360780749820804551b0200c0d091802424552800e0a14a620b600115031684564422a05150300c03045180e4255003914441d143e403020a1040c0700144400000c5034014401c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 519294604 1250 519293354 519293371
    0x1806060721120b0d020109051003060b0c0618030f0d0b010e030a0507050102070b0c0709090c0806042414060d030908030a050c07090507120207060f05010905060306071b0803 76
    0x14a0690312614212003034003800c07044000303101d4010305100000648588000b04804907090302c1a4402500000e0484c080d502815101c0c80802c141482940d000c0da010074000c1c4556840345407110703500c1c0307801c41d22014200d07108041e41110782001c204041380882120744480c881c460090030907041c500840002c005100782c040c18050089040f4201d030307504216100c5018801e0740100b001905110009081820a034480070080b0800d1041034010800800c808040e01e928a07400940c581841c1442c04031200d10f6400301c25a401401d041c0010310804142c1c40b40180c2d280101700c50401c5c0c8001c0c0c0401100c2c03441070315041c0e641d000e4020911500d0300e4045a01550f0091500101e90b81d11041d40c0d0703085611141059000c1880025515011003041c00b07260010181e03000c0801c01481c1800c0c2c040d0151410500783c0035540d60010340c1c00200040c0c2d503c603034040c066400e02040b881d80c440250000a110540d05c181c480c0c410080090141c1d4400c540b008010030b00c1c1140041100b0b490f42e00c9003400e42010b0b28000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 519295854 1250 519294604 519294623
    0x9090f0f050406020306150406023a020d03050f04120f0e03010515010215041109190f0603030e040606050417030904090f0c091109060f09180a0b18060607 68
    0x459065032400350601590065074010303564140340c0308100500581102190382e1001c14001040043d4001c5082c2d441880d41c000608142da003030140c0060030710b4040358401c01d003030700210302a291154005410f016105440c1c60030090364481c0803124500c814100d60081580001000700c10792103102d0356544040a10604100001e05500360000c0c1c29610100da0164802410038405134a40d039041101d00e03002030350311802c41c1c414103154a905400c00c5100b00d115000b07003500c002090381c044600b0511003981000c1d10082007801c0345c540700c0e200074151130311080d8001808001d526407146050b00c210b004440c01900d03030500d01403511114810300d060405c0d2003125400300b8000001d00340c50754020802050701c01c00682903103103000e292400b00e40f4650b40243c40341510302600041058042411140030350400c40d2a5911002120005c00462081c40c580503041040610701c1506079424403880384c01107404450900046110f10300781b00d01d0b6105442204480c0c02500c0c04580c032410680010000c580c00340042c103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 519297104 1250 519295854 519295871
    0x302070201032a09051806010f05160302010606141201091a030a0b0109110a0207051c240f0c081302191d01050d0f03080a0e0a0501060e010608040309090f 68
    0x14038456840760540c0480050f124107002d02a60701c000008040c004c210b41060910300c130120354600503c0d000342028103109040b50050480ba0045082d120340e0790009048010b140d0342c624000b1301911051080601080d015080604400c40311016540b2000032010141940e0303180103402d402824503030f00300d50380708030103a02c00c1525900d0500011040c140034800c5280d03154586000441260079204400f100d0000c140201c180940d40030481c4402c4074804c440043c450000700c040e0380c2500040354801086001e04c120300d656400d0f4a45e041654004441201300310307880050036508180c401402c2103070300003102080041c078004d1040203100d660301d00161140e5240000700c2181001c0a800f5000401c103a0480302d02c004407605010120f0303000d4603094a40540c0110259194082e1b0f002e0904020280310391070300021680320142d44061521042c600454003070b1502404c4c401c0c000e01050103029098003550001284217405504c5480c00f507640366030b80580c80e5141102807401009602d07051018a5140c1610 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 519298354 1250 519297104 519297131
    0x2010f14040f0e0105240a050c10020d05070e041b080c0705030a0503010e0603030405090c030a09020a060e03100606020604030c0f0b0109050f1b0a050a090308030c130905040203070501030207020103 87
    0x107001030901203480b02001d50508040200f4184074001c0c030107001b40054a0000d0388806c1c03c00343d0f030000c102810700c15150624901010306001c00d503d0140310b550310125a01c0100328032a00214010302d203949519100300d40c030030240401c0e071300624580c44140c55154007030070416100e0300309103074081449081c00342441d0040c0d4403d070455025243d00000100040010b009000164070b60710740110045008518081c5404081410070400810241501d10b0102c000707680f00005400101c10907034000c013240004c80d01d880d0054483c02c0200c00b05402417065989003641c070f1000344a20300584203550014201582c0f542c1c5c00301c90b0310f0f860f0002110103254000f494400a098929194041c0040c05008030700e51504c4083c0040b2180020803044e0b0b0541a204032800c030300700c410100c600d0740c074080c9841e50f903400f01503e0a8440000e55440100184400000c220101c1d030000c2c094403003a00d1a0314020506640c51010005480007510701940c144c0089604000642c0242d00400145106060108524014801 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 519299604 1250 519298354 519298379
    0xf0d1803080c01062d0306050a1b080a15050904080a0c12050417060411210a0b090105160e190b0d0603030e0312030c2109030403110d02010f1404 64
    0x759500b40c0c1c0d11203000740148041194034103881a403030034041c107208040000c1e0240b4400c10f440090f15403652030340031400c5501039030410300342c03010840d00200300c1d20700300c8030020031510f0102c80c810845460885c0c50400000b59407094800c643d802001904a40c59a0300c2e01c2c102540303d407040d0f00a020030300003e0000200d0003248041c0240c0180c849a40b1245070490129000100040d81c0020790400c00070000000e003c0794154000102c1a260102910b28138041494401401c981c03032100e40c840d4640303201c200060720064520a40907330f03009100645861303074010000050b00c5005800301d10340852104c4181080900008940130042040c610b81d42d6544030350034541e1180f42000e01c1152609818002c0c9500200320310703600c0c03505500811185901c42ca482106010140030102c01c084001a84800b0701a8810140e23501401e2401c40c01140c10503150260760707a0310a00c400c5845142201b5070900c03626140212008003170b010303191254140340c941c00844000c45040c1000c201e1190600c40862038440709407 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 519300854 1250 519299604 519299617
    0x3020910030603170c0d0f2c0f031c03020a0e120d03050114130b03070807121202011a06031305060a0906050907050a03020d060908030f0610020f0d180308 68
    0x481c0020718030705500f80400300c024038082034440c42508004c50450800c0025011420b20440e1405440004403280d08a4400303000d0403241550034050300503e03126081e0404411040542295501d24045082d0281616111088511082403032410490300205000c5c0e00101106407042c500000d1500708900061141140ca14400440758004080c03c0341094151042c24054440c0c96441c003000c982e03402c0010740c04050802201c000035107034048440d06480c200001c0c1e015080410590346200e448405000050780c124000780e4691f0500541506003900620400c0103502c4200c034448181076480c0103001c151341c40540348403005420300b0030722800f00d2014007080d40244c41070103020800c0d100605000c000d6900141a483c142d400c87c05040100f540c40180510031654103542c0300480314400d0808000504074003002410b521030000400c0a03100d9048641c9101c0c11007141c2e0020219100c0b4030490703580400000344280c1d03600038000c921243d07011303410000c0a00180c2c401c0c0404a6200e030341d058180e030840c5c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 519302104 1250 519300854 519300857
    0xf03070c0b04140d09050f0d02060d18120507080d0902061b1605090610030c121e0c0c020901090b0a0909050102130503160605090f03030c1c030905070b030703020910 73
    0x720ba40010107500780210804600c4515010174010306003000100302e180c10440441c03164418029100864503100181da005004812040090300c1d2502c001e02100d08240300d00b1140410f00c509010700c203900500c29900016009400350341009260003542e001000f8178a0705071f0348030b9414001400001006080040600d040c0300c050540344007040112100c0d00b5164002e144140c0c0400b00f00a425201c42d11011400d4006103008155160409815243d0014941001d10707210f04048840344500c1400c240c90008000c2000704100c1d003034021008450b00801d4100080d400700201004201644c02c2d90881048048003e0802c64a41d59072156841207032114001200c4594000c200d8604400d20405020001c101c03ea000d041801d00c0c800c660402100c0f80d002d80f0007405004500d0002d5600c44a200500040e000340844e0395500140050a0383c0e10001464107007840c140150a0340b404c1d1003400344200b40c5034000c000317003c154102124486543c00040040003055420301c0144141c0d80d0752154a0000d030700301d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 519303354 1250 519302104 519302123
    0x5180915120d080c130e0408030f01150804020d050c0406030606030b0601030b01050d0e193002031204050a0209010308030a06050105130920030108030405040e0705060f03070c0b04 79
    0x4490500c0300520400c85228880c1d0416040707001d680f904414540e0f401850000415030f60861650111422080303500424003071000700c810041000801001180581e0482da5000716036aa15583e400c148a61300c1e070305c03400051403030003c2401410031000c0919050311600582d0210158440490121080d03980b051340d00c542c403680d0400501a080303040039001542860f040c0824001c25001900b0b40c41100010f4030b036695146a40d1012820600c2400020700b0340d07041d042d50584150510440d00da8004c0000c800401a2031040d9460740180c0d400d200c9020f0302a0055424a07810f00d00c50412070303000400544441c0101080705006907100c01c0101d000c2c61080c002152203040c2101c180d021608281c0009050103010071141c0360700300304109181e0844000000228268211034881404140b141568007c980400310000c54a07140120142050f61016030b401c0140003480c2007440d17a104110f11400c3e8020204101703201c00341003841e0055912103c1c1c1d040219a03100e003a503403080d0210f401c65082c0e80750b800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 519304604 1250 519303354 519303391
    0x17060a05311e02040f0e1906020408010603030c1a012607150302070c0e040f06020f0d0c0201020406110303010e07111603050102070b0a0e0606041d150601170f07051809 74
    0x4144c400d100c01300804072400c0100c11030b002840c6a480460360f1007c070700b055000300500204807007038040b140075044610091104a60f40d00c0d000e8182c81c0c6c204800c90b621981d80c282c4441204010380076074101d8044a0843c100c0c5400c400700d815004561001140c46802401d03000310710f0890786001c4003820401940e00681d00c44040c2401d4000141a40128a08a094500b4040400c3c0310341041041c1c540c0201c00180d95400d000074003200361049e100d00c0c07140f03542004214001d194040d0b01030310407151203894080f2203400d0408480e451344002d014940700001c840020415841c815140540311141000444903420500480481c400810f03a0003120075079000100c100c208600003100c1500400d0901d070a01c80c0b480d01c01501d0391140d5008059034000d50ba280d0a4071800120386110408084034841038a214800b440081d50300c4460403074420b400700d1140d100009000400010162040340d903603c1d00796060321030038011216544005003072002000034000081c6c90303684001e0614003940000c0a100140003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 519305854 1250 519304604 519304609
    0xa03090506010e06180906061005041512050c1e0a0309080403150b01030c051801090b0f07060614011d06091201140106020c1c020607060617060a05311e02 68
    0x208002048402e40c0c0303208041c4001d81c0800071f0141c4e04250304032941802952416021141802a64404550f0f40c80c0c5025869400e43c206071880740220705010144a190388005004c0454840c2c10301030814034503a40075000e40e1014030360181000c9400ca182c003151004203a21409025042904180c2e01451402000d850003100c1d0711a01210700e9003070138244400c51072408054110700a82001074203500320350070a540140c0c8218003410240041414084c2c8074042d009488100e900203441c1210041c0c603010000c20100002042443d05c0c00c0705a5076607401c0c21f6059500103880804484690704071005104c00704282d075884c0401c500c4240140b00006010300244501650614180c2c0200203641006039001080e460344e0030b1411640306905c03800d8140c10300f83d1002c1000752043c100d003d403a45282400200e1688912000001300f0300381401101c40035141c4503040d20072518180d8070154042e0445220081020b0502039041c0c510b19800c0c03800b841c84040d038880c802e00e11b00c0740302c0006214801124200451 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 519307104 1250 519305854 519305869
    0x5060906130b0106080910060f0f21080a050c15090606010f020d03020f0d0c020102070c0f1508060d0c030b01050a0e01080d050702030a08070b0411180a020a03090506010e06 76
    0x141c240303850a450725281d0380390380710798003418018941042842000074030149403c100b40d004034840501c0403c8007079a25100100306070014000d00c40d18022031940021400054542e4600c056030b0441e0030013400c2050f40e1612115031015580500b0705c0000e0015606801090100d8203241e2120740c51000c4a180c004035181c1400401071040303061010074040044403950005007a191040c4c5814010317038500c007458503824640518911559068142000c0c0748050398103402a0080622516410040342d8075013415000d21269030080d000b00032201c0c030217205c00c503100d900c01070740041e00508440103131062600d4020340c0c0c280720340007654510020380040040d0b0a0090076600203200c10b07600300d880b03541048441502c40b01020381030310420001044000555409202107050503502c100314a981c1c282c10700c3c04050b2410101c030b040c1c07108454030429061a00b071014401a15020110501170696183d514020003504002c6079801019036405290000075410010075010386803860f001181c1e4540b0404101e10b1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 519308354 1250 519307104 519307111
    0x21070b160f05092b170a12020d021c0c09090b01020307060902011e08070e100f2703110405060307030b0f0601020a060c0e030c04050c09062505060906 66
    0x9140654040d000080d4090341c291049001860999528420070f000038440c600300c0c284c8100303c540b2100504c03400390030042ea4074004034890741c0d0a20010340a0400f510480c000c00300404c0110b0303c4002401d18209813a1300824103141c00c08d200608203140c111880c4680a0b841e00c2082e0320307030341d02d00011035920b820030410340040594000a01c40c0164440000f9164000c0041c0200090323103070708e41103085a002c0d00380c0d00c2c19902d612032070031048a6803080007000340d4016030b40f1401186014519409604010000440243c426221080d0751504200e0403154102210904800c01c1c41102c0080c4040702d02c1c0540c0d000448c050380c028490501400108000c607007000c0c00e00e5100ba4001c150410000e0090b40d6003da000300d0008400c2c80c00d9484200603400d088071210003c200c240b0700154810071542141401c0300092064080b11120280402400101c48007a40c4000c0c0304401400b0404151400310001c010008115000b40c548401d107007410030786a8815542112503800440070013050310001c1110950 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 519309604 1250 519308354 519308371
    0x80609010f1e050402070c0f0b0f1b0c040204060c06140919051002040e010e06030a050309060a030e030307030617061311240306131a100221070b 64
    0xa55140c8400300100c01c000b40316041e2200e190030030011003a84000d28160007007002400c00c0d03544240905d4041e01e02100c03400f075040803200e654008502810820b0950701490b481c1c900251600c420500712140c0c900a002500320948115003280404d900c0d42d0003d400180015224002d00070001d16100f0295441400501e032423424a00401c503c2100006540504900c130112381e42800d0348078100716041480340181020220700004001034440c2c0c50342080b50486078448024402503c030f6408150f00d44400d140061700a600030301c00c0301d00c9881c0020007010703810300d5420000b440e0303009031040504641003103889102003035440a0821000d09001540b000e8001e4a4000d816149400382002e05403180565002e000250744410f140c1d10303911031002c800e0500261b400508080d800c10003003080f85900c11981c8500542841d1768450b480c107a00d01585030b880381100300c40480d5404e0101801200c0784460544030440c4034441102030000780c400380344141842010400e60340c078950707410000b1140348080c010070f8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 519310854 1250 519309604 519309619
    0x1051006052701020a14060a05090a0b0117100e15100608010315061707080c030c0d110406170303040c140105030604050c040b0a021c020d05040e040c180c0806 70
    0x103500c0c0c034282408601104400640709426400c0340101d00d441700e0f0700c00040180e2410508240315400028069120342da845006100a07a92a100d640c2c840415031401000600c61400600007421602600204441c1d81401c031020500040381ca0000d44551400c0c031035250300048101d007444001c031030364207030302814070880c4001070303454004000d040031414070003d000700440341c125040d4840240c014400400c1d2500880c0b900310142001583c41b0480c40c42440c072540b00713040314101103080100c0c0042c2c21100040c0b5003a4921495103509010141c010050340d4026550366010406185a1350b442000e20b5480c00116228642850032207001b994036000a408207090b20403100b1f65a0f03024040302c0d400503050301d0201d103a803110320366409140680d81044020300c2e00465188c070386944c0014a055800007600e861900146d18401c1a80c44944803d032200006000b00803d0100c00e41014000d500305118101d13000c9296500c80a03d07000500e24000c605105440d01145140140e002f031200707802604c103d400d00b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 519312104 1250 519310854 519310867
    0x91b0503070b03180703061a010f0305060604170a0506070c030e0409121b050303010b0d051f06080403260f100e1317040b1c1a09060d0c080105100605 66
    0x2c20305800010f2180c4111140c14a1064107002d081c04158000e60340a02c0500100035140c2803065180d02c4019654001049a01d4a4010500c00c1c0105402a18050412460103080203040d038a17038203452040700b082c1e200f056559000039900700300540c440d011a5460201d43c4101d45401802441c0d040c0501d0321031410000ca0748003142c5c500a60b42144003550074950184c00d10b008c4c0044240d00708840150041c000400001040c1a61a000340a444a000300801155807100a00d0038501ca000300c114400143c5c190044c00654081c9a1454010340a401c03c482c441c0c0302120740d504a14003105140c0242c41000e000d005128202822a41e04a403100030360602003801c142680049000043c825205001440b51080501048601e060140441090200c1d070b00d90319a0b1402d0600d5104180401010090030706000c030070a0b1a2207100d030006940c0c0c940b034400115000c100080d00c000030380001e03440111b0624080c00222070014070341c010715a0800114691030901c404038184085e80e8000e209000c81040351 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 519313354 1250 519312104 519312119
    0x606010207210b0103030206060423161806030c0e01030b0306190e1603021f1706040608030c0d0806040b060910020102040503060a020c1902010507060915091b050307 73
    0xc4030140c1d06010544042c40071001407a031180c900040e0042e003018001c0002109240d40414164405c030001d0320300740002c501e42e10403030100208240050300d004e144e0001007068213181c42c1c1080c8110155241402d81080f80403201c4031800610780c840c8004c80c0d5211a9020001d80100781c4950082d0242007c0003c485806d000c82d480343da0003845120010501010200c40e48060b47c40703c8440003003001203c035400d0141900c07001c3d1a0f89800240e03c61002d1954482c201141c0003d07402100d04946e41d4460b07010180340b0075002030040a00750b2030f07009407100d4020401007420005000881e10035001403e190402c400080c1c0100b00141859000d00d0070b000e02d1340c0302900c03050116629503400b60740b6440c0700700c81c1210490080c05a070300569810702595003030006d07682c0e440e0003034000702c10480c0c280c998810807542e0342100340c0000500240421400e102c194007007a004e600c188400703402541000c1460324500d0b9154200c0d100c1110803254042c030640411041810254400d01070002600100156403c2126 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 519314604 1250 519313354 519313363
    0x40602010501030b1311040509100212100b07030504090b03030702100309030e0a06050702010809010f0509060a0c0914040b0a3f0b160e0d06020c06161e030b06130807060206060102 79
    0x3c0447c0150b840d100441d01d0054100060210015002d0085450b0381203900d00e0140c6030310642d101c142c00f20001001280003c401030803161402e506031146460f1a00c1c0098250140185082c82a0305020520610026031541017141403000215500001e60a00074030340038000004190000380503808105050281580240494040b150242015100b66442c0769010380586140c041a002ca01d08150600960b80000038a00d400b0f125100c40030b07c1608241e040448800c0300d50f1140c051176209001d1000c0490a0a501000c0c1a201c0507001e1134031992190744900803a80d5000d2012050b00411210460940300169280e42004030b41c640410710344903588444101c07400240400d43c04252107109050a5030091070300f1884079101030b00c40d8003100200c0c1018002900f10140c0040d0900480e40020050041c1025a01014485032101640c01c0ba58402405c82014068601d03c181692040580310a994900280c0310303840c03420808a48850404482c141042802e51082046d5403210050024503a00841d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 519315854 1250 519314604 519314633
    0x302030301091d010c03140901150303050a0201200a020d03051e0c1908040b01080105040b0408180616050f030708090d02010905060304030315122f0303040602010501030b13 76
    0x40010800b403a0340e40960307903203010903c0c0c804819882e01c5005031085426800c00c444100c41002504220ba80760280d40703081e240d08500355404829955030500019000340050408420341e0310000888880c01003820352001141c400032841c2d04004a0150b040030390401c010000c041c074610b0103100d00d00301640b5141442580c800d08912407104400080e8a0441e0017041c1c9000c203540500e412140b0341c0c0928040c0400310b091f10207a031510307007200020440c0c40701401441c1c0580d903c040070480a80d142d44503081190011940c10f5a415280e09103028250f541c0c40103040c0c42665850400b1403111903280003443c0030654a0070500c6604244440004030b018182a03d108010a442a1420b249c80703100480d407000590b004507600080200074002810751692007880524003042e0340805491712081e00d00000c12080100403c07030a2034030303407103a50500481e0110200d2900400a00e40340800e010009003160001d030040d1006070b642c1c0e0010001d001000342440e0300280b0310031040702c10b40d40b1a02c1e418968407204 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 519317104 1250 519315854 519315869
    0x604030804051e0d0b0f01230d06150e06041508120703030b0d080306130605220b150d0516050703030b030705120307021e0d0222050c04150201090302030301 69
    0x41480003a500d4080e1015143c00010705065110b11203250202d20a401510300107050700c000c10010481244036036040b5100e40c40b0f0404004130320000c07400c01c070710391017420001c0720900d0b1181080440700303200c0c894180103040382f840c515003079240050038001110704030b900451258000007030030050410049035524401035910311265581c0401d0070700380c001e4502102e6490700000303501d072800d0501070200080c0d070050358122041d1034007045044c100010b40348180290707176010300c1d80702001c17604102420043c0d990024112010513264100e10008130309038a4405000015040007610724247d03800391080c5a4400060700c074040a000707046070001c06034003844000905159854074902c100b69000c116441c028a00140030344010428030f009a9100e402410049008840f640c5103110b0070104c6902009501744003801512003002d81e50200040030f48a0300c20452800607000d00241d10000500469100e1003c1e00c15951380c2d985040c412007030300c6528041700c4045900d01150310000030360100842e811903040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 519318354 1250 519317104 519317119
    0x4050d02281205011b091707150206060102070e1902210403120b0901140f060f07050303070905030c01020d0e12030711101106040305070807051006030b0105060403080405 75
    0x800040c01c204250070540558101c881203000070750080c0c000035012005208400078032403045908030300031140070315516100c08140f140005200c0745603821082c84c0d094440301d0864590700d69691181c8801007940b042c03080140c02001c100030140d6010003900b0018040410b00811502c0c2082803203214015001c2088a13041d000608001c08a0315200c40120120121040001608183c64040c0502215400711150035003003012800840c1340c250b820504031503284805046161030031042100e13118141080d0b540c411000d0001c26900e0203418041c011041c4038200455a03403c00302005401c20302960300041c440d6200601d4182184d0b030110740d00d84522520704141100c41405000200041c0d1005112078451001041410601429103011150b90034242c404507041080b154003140c44c080100c0d00401d8980c8010042400a0f20840040c00001d020300d801509000f004e684e214240301c1e80c0300c00c1900c4252550320500502001c138003024014034007120300314035103855a50380002a01171845614801c80c0d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 519319604 1250 519318354 519318379
    0x606090a091a180c1602120a140f030301090c030905100f2a230c070e07111e030906030103060509010b060c1e0a0209010611060a1104050409060b030102030705070b0c04050d02 77
    0x43c0c0c9140096221b80c02003071241a980c0d9129819074030702540c1000c2c3d44040d410310a00ca4851004542d824043c00c1503405540746a0904960401821510703010404155555401402164090010310301c02100c601003c030f1091a11b0304c2c84400c3c0e50b0f0000d47d902002c0303c14803c04880307100000120312016014184511469045d50b0501426070605c665018a8031300080c4c8040c00365030210b1040151651119807228946951400303c400c0c1c1010004119a6409501e88804060b0581c0c00ca00c0302003118000c80b0300e030150220120b44160002ea004032043c07a00c4100b0322403c4a020701070000720913016507100e42084240e01078aa95a030f50700c3c4807005503280c03002e102030030000d06211180c51070380c01500c2c0301c02650392510010002c0080c090128114002c103808a03503540010b0107482c0e040740014100340e00f030034240300030000201030f0800125105030f5a1640c16146031002e0001d0b41c8521300e543c42e02c4e9180c80701c0c2d0520b2900800010b040f9501d80b20200070510559071081100e9002c990155000d403007854 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 519320854 1250 519319604 519319627
    0xe0f21090d020a0e090c130504030207060507060605030304260c0604180e0d020d1407031d01030e0706020616030204030b360a11031c03050606090a091a180c 69
    0x8030703040501009035031410801e0b44000041d030801060000d8847c1d04004162244060441d04c0075500100140c2004c18204491407103039001d0321010340900d030006506907840c00040e145500a5019511310112400a00d0442038155400100c580500c0094601d000c3d00500081d0b1a00c600e020701c1d458400d415141c2c04a0051079805036244007038000c1221115154003101070368400034035442100250040c0080d488040550065460442d4182c40c1c051140242d01d0110300210b80040316581050b41d00c50800e81016005c022080050a89801525050500851102802c0c1e40d104100050500401007000000c244a840f103a0100000e50300c046103c2c110303511010303c596000d03100c0160102c0a4140c015a4001181a81c0664800c4103205005250201415141d201d0041d1b0400d41e41000d40f030a16a071360003034101c15031002004111501d0106800b0004026510303540200c0c040303e42c0e42c681030598440300e01e002540e0741006c80360802100c0401e60341d10048500101403001c00440801e0705030028 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 519322104 1250 519320854 519320869
    0x1b030c090902030a0603050606010f0f0e15070b04110406140603060409170301150c05100506132c1204092406021515010c02010e0a08010e0f21090d02 66
    0x420101c103096542e401d04031142000b8001a000681d014040c0d903020805e80d600a0340410490718181c1c4541031041100f0f001031b1a03841c4492011500302488420000400c3e0011004114091040c64500c00506140c140b00e0701c1e140400c8240c0d80650b01d41a01800302c0f0281d10b1000b032141d90700304c0c2e9040d960ba5403100071070f011b80500240289000001100440350030540c2010314180c82401c1c60020101c010308004884141002030080c1040d081401400c1510f1000c0c0c01072a032201015001c455262101c0c009002100c1318420380794010712003460301e0034107400140402d911b03452031300005210a00424010031085d04c036903c00c900009607a014041300b04043d03100d0350010075151744011001d003a0788600103500e51140c100101110805400002e96010003d65090402c0318181e44122401649900640b400c552a41d680f0754040c501c5600041c015209000c0c1d0004c50400f040a42010368500c0e41c400d01e4514078480e883d030000641490801c80f00b0107001a034a403c1c80403600007403001160f0000c940b01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 519323354 1250 519322104 519322109
    0x31a090c06070b152d030c01052502090a020d0b06281202070c1805040507050f0301020c010510060f0302030903031915080d0e0d02030d03020309030c011506030606031b030c09 77
    0x3e01c1d682d2600c1c2c0181000c81401103401c19040860302030960105c20561545800d0140034046001440303021101162220f1318441041c43e0403500c1c003011003580000d07001c028212101507100d900080d50072902c20150103207014015054407840d00f014400303240f2248540b5400e09103102c141ca001c0c400031030a031207019840400410315904541c0d807000c07030900880750542401207042d00c100c0711000c8a5003400c00e100307283c803850708200070b0803036681030004000300401e410040e550702d59001e01400310851405c3c4699401030fa00f140304040024580031001c0c11000148541234241071040c002c01801c85404000c4952200740c00d5410480400100b41d5640100f40e803214030004c503a6031104c08900180300090f80f00545ca015111181c50a01d54410092071b1400b40400075015080100300020450080e0082e607006500441504c0c20a4440e401103400c60395080250000e900c110384040241301d0301440b4000c05000340d0f00d01808851040a07880100d0381e041c06811041582d520310710088188030307070b003400f01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 519324604 1250 519323354 519323359
    0x7030b0102160f06080114130b06040905010b09030705091509070c0602030414100204050618040e0d230405031b01110f06150f090a020d0b0901031a090c06070b15 71
    0xb203454101843c0380450901903540440c1e4100300104041c1c040c440380b02c102c0c0c00000c1c02d16902d04000528007010b0300e84024119003000d010b01c400310b0482e81134050305000c0d10a5000b56074664100e0002c0520301610760340003a000320850000c0c000c8016121000100b44c60b019140c0700350a8440600446210040c3c0d2005000c1c5032010041c84104061144060007000c108402c84400c01c2e0441000000c0340301c0d512426521840c104180d814044a2295210890b00002e00004889004240712030400786d009172500c0c001103420203000026001410b24590308118008140e052a0400c40401d64441d880c82c0d200200c20010325032007030745070720500c11010340030b1060060b038100d0054100700d01e58500e02666041a00500c003540d60005041401607030801382c07001044100951074a0980c034000b540440140f90310551168001d24603034440b4100c2a000350f00c00d201c110500504001d81d600c40c0d04c801341038101160003107502c13841e10b9911181a01c400380e402a65070b58058035100342080c18260070082894 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 519325854 1250 519324604 519324643
    0x120c2b081608030c12092410051012060e010312050315060a030605180f0708070c1b03020103050a0509030d0e07080111030714090114160c090e10020f0307030b0102 72
    0x41c4d0700c019030054210700780030280b80c8207aa00c0c0d000c04241c403803250740880c034004044000d24003110081c4401c2282c02c04883d20f02c1c01039060f1a0760104000e1495192150f0100f0300b246c03001710300c21003244a03520040c0044d00d0700354110750559803003905441815488000304a0b011001c2041e02800030f09150041d60020b0505554401540028010300202c0c4211845010840000300c00a1803000c1c41c40d00c260062500d00071a41d96801042d200540040e00800802c2194800c00f80020080c9807205808101c404800c603101e850361000405444000380b403001240c0c1448140114a0400000e862200410030008a8030080081f407580c07030040140d1082c10301d9030030021400c140d465048015405041550b807401c202110107240400b032841382020081c0066800644030b1802002800a403016005801b0001c0382c20880351225144062a600980392503942e94a075035008200c2000700c0e0300ea41000784404e5040c2000d111078000c60340030082528040c140c03500c204c0401e982c0b080c84081d00080f6100d21a1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 519327104 1250 519325854 519325861
    0x2031b0609030f030a0b1801090c020f061f09140f130c051e0301020d050121030905011b0501050a0e011503020901030b090c03120a030605120a061a120c2b08160803 72
    0x8113a055402e108a80345246084612b0024900c00700740c03c2800014400107010645a040d8401c602c074507281c4800d50b42e80ca40b204c3c0452a80e00b6800392004c082c40342c0b01c10030403504240141004401c000b81c8007421070400840020300141c41e0002600495008545e0000701c1035079940c500d50340e521015921641944001500520702c80c19902040c10f842c1c1c4543c4d003800203c3c0701030141d074007404480d4019000c2400c4060402c000c2d8070943c0444a4852808544030417041c9a079203003400d4a80c151941050715482c1e29094042030000d2103006509a201c070300d132001c01480d540108075480300602018200701c01d50740008020400400803140403020140c1103a10441c42100600410b41010b001d1700300190612031300058502d4100c0c1008003031680c52024100403c1d0b2940c03a08024040d9444880c03075114101d003070101230790340c0c2d501007044515501c02901d0590514810014680311007c052001c20f40380350707403001451003031810f010780b61179024260355902c0000b00f680d5641f81030030000003000400c000041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 519328354 1250 519327104 519327139
    0x61810060605070b060a05130216080414010f0315061407020a0605120604020310090b01031d1e0303010b03011e050904080c0d0201051b090a051002031b0609030f030a0b 74
    0xf401883c0c02900c00c0342103916210100f00c4040340f40d100f4190f0007a145c0301e140e0b40036601c60340200031070782c11091904204d10341c46c2d80307510762600b155010462490300808104283d58004031b400030412002d1070204500100d4006060103800b19000300020401c0f4a0100420010580200c4100756002000710786031aa540c00c004049500402102c0381380c0725424086621401c00d0300a0b24010701e1028074181d1814100350541d0010300401d0310fa2410035880b00300118503043e039510041d20140030b20014103200c1503810140000e044a299940c60154010001080070300c100c1c0040c1c1c0e040d81c00b140c64443c140207010103441c450b18819001141d2086491080c481080303913480003080c04009200581c1c885904454050742240c20844020140841b1075600c01d010344180c0c0000c211005008202d80032446d1110b011614401040809001681c0000b950700054290003c00042445180d401000b403450714000890322030140c9180c10001c4980400814010300d2f403504840010000540b049001c011000c44 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 519329604 1250 519328354 519328357
    0x90a0902120a120f051606020304060b041a03010c020303010815091f0207060b0f0f01200114060901051c030309060f0e0a03120207031416150903020d050705061810060605 75
    0x240200410800104135010f1030260007555007104503409025001e5145840c0e20006e540020811110300e65920034001180e65184209030608041040707031640803d00380e051608440f00c9240040542d40280010004038500045001000000c1c2036600100d444441a051a181d40500c03c102e100c030f10621034014185140e03001c0d041c207030300031001802050200418800340d010010300712500841c94600c0c078201c5501554103003280c1e0080c00102806850b090500600b191048110083c145404506000c500d01d0f001500d103000d00012604000f854003044242c40011000100082c24140c0340c00700c0d9018003401d07920070b002000f031130034050041101d40e50303140340c035901c5541085002c1442c0000400502400d8130980301800c2e85070302c4400d60319080e44008841c64212903040101c0d442c44249810003c0c01004c5904090481c03410045036101040c90080d0424046880d40d1042040034014440490b00001d12141c01c90034096011a207554000080d40c10014091130f0540c14508003000050801e50000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 519330854 1250 519329604 519329633
    0xf1403040305160504110d0e030c0d020a0215160f02010210050c07120e01050403020f0a0b1614010b010503070f0c02100224060303040312020709050c040305010f0506090a0902120a 79
    0x260584d03110420070048441c0c40420400120041c0441c0c8442e003125408030a452010200326814404010010340c40c00c44c0d00507038440180c105c8003459045081a034514440103508038581c5007010003031085100c41e802562400b414941001c0002000e590007480b1804440011040c20f2210b0714046580154981c4400c10442d4903015800785d841080344a91803480200005950781850107141da02007012154207400ca0544c00b82141c5800640c150007c0e00602441801d141d030301554142d642001c60944200e02c031803800c66414000c005c0ca8582c1c0c03050480354880450708107002d0b0620a203004a03411480b03404001c0d0402d0801c00c030b050401e40c0004410000f80c007600948c0741c0a080200d03040b6812001070703c281d6010760042c84140300003009031880b013a00230403c1c41112111a55070202006440781030b02e82401a080c00942402408428007825000d840803040074032050a014002c0b88040c0402400840602d03a1003002608640e12601189400021103007160180845414025250b81502c0b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 519332104 1250 519330854 519330883
    0xb0615160b01031505040c27150510020a0201050703120e010f24050a0501080405030f180a09090c0e07050714010606170c030705031012060e010609060b070f1403040305 74
    0x8013200c0212044500030588540c0d4828041c1d2034182c5003803c0d000000400070213901e060507180c015071400c907200e4403030307449400c90491000c80c0c0585450240301f11070300034200c0c074021500710000d1140035076004021104480c0c1c0c50710b000c10216409001c0c250007001c0c5650b4410055081900b282d200b604a5000030700b8004040c1c0741c4071503030f40600a60201c94959403041079001030440b101082250301032020303142c1c082c2c00740c029203161640729003480c050303948418030070200403050501c20245c03410015251f03006010584800c0202101d07039100e0424001c498440c00442c035030018001061030b440766055580722640103291004084103135900034041c009501070900020b020324070b8060030720a410101805000c8003050503185465695089400e51b1000b41030140c400c075186400110742001c440f0040c005400341c04000b40f2442d0645026007520300c01c0c0d220400c0b490500e1010b02001c130800045032890765001c4001380941545207401911800550303001c07005400701280000510402159075010346000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 519333354 1250 519332104 519332123
    0x2061c1d010b09040b0709050d05070e01140306040204151a040311030307030f03153b09070909050a02150a11150105010309020a0312050a02070b070b0615160b0103 72
    0x54086030303800c035025411201ea01444160220b00400d1720705c25051340086c01481e001c182d45440e800454108101804101d59a91110700104400d410600c0d0203400341c04200da02c00d0703941d00500c0003e6035400e0050f1029104654079030b0309101758000c6c0d480c000000e204103840300b20540c0d42c2980b00b5030346402c00c0c802503c0c0c84400008403c800c0c0780100440e100c481c2d0503280c4040c1035007196403c50040103522100710712103030302220102d4a030000c007034201c0100e108191061031049611130409060440303041c0d000e030200015818001c25110204020003519a144000184540e180c185a8a0321b14542d40194210765a14060f2360321000711002010191059240d03080300c4500500503980e0780c541c0c81d04021000c00e0800051001e58807a030043c00710313240010300c0c1e5404035440751510301011911940110100e04002210030707441d0b40510404004080118980741440210b45500403160f02c0108528820300c4521140d09050300700b5010b6480440c0e08010030000341c5a40d00e0500b5510718203004c1580c0003100e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 519334604 1250 519333354 519333401
    0xc0301020f1e04050603010b0c160620010f020301031b0e010e060906030a150204050118050d08090307091b0305130c090b0111030d0c0801080604050705090402061c 72
    0x40500840d04100103410140e4942062400c91094010074503119070841c00040200007072a40c1e44402840c060b1096600d00c0f640e0721020300c1d0540c42e058a041c0302e0b0314001d4698500b04810f82d000343c5070306201c5041c5a8181000c00a000e1414010400050107a070100c0c4080300200c18804420603505124a0200c0c48682480c1c8842c00301c9107a180902c120980d03c402440055401c0c2080181290061405400c07030b20b5905032075852049500b00364083c1c9030042e5001c2030812056a014421504039851109110b1001341080003140f081100181c018081c41d000042c164500e031410803096005085010007001a88122100d02d140c8503150b10192001908100210340340c5e001c03425030180380c140d002504031201e43c5070201080c040d21113442d006060043c581c0707500441e10310a10090151145100380020b1141400801800d8843c042e0031980882c0e12140c100700018034001465002d03103404840f4601645c2d030f07a20000e0f40078071541150010115000324000310b900c3c11034100d103180c4101d50210540005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 519335854 1250 519334604 519334609
    0x11040507020601081009020d02100806040c05071106070507051503091b103605100f080417040f06020c0a09021303080702181e0c03100b091f0c050c 65
    0x81c03082c000c40040381c1004414041e0142c171980140003840c400340c920f55001c03e00b07400061180c1d2040c180304012030341c0481002900d01d00381c4503650a102c2d66050280c108040c5840e440d180c9040c0040d1940241c0000030181c00b4018100003000081c8801090350050303210240f00703403080390070075684215207210f0001d903441001722148a01225400142503003146042c0b041e0101c0e510840c10341d00d075440f000d800c04640e80501c0c021641300180ea03414002c1270070712403604003030180207040c044003001086600700c100c250050b0300503402d41d007050b0406a00d086078040201581d00d18442d07030780802801d4094040010f509500031402a000500446600c0f540380e985144d03103000d9110388420854078072028507080c0002000d42c0c010740141c9001820540003100c1640f01b0100408003034941c2c031528a0300b0f060181000a43c021402c3e80200744400f0b45086042c0b40d000c11034003102d507015000010002003074201c1c0680b40e0803219003040c0d0003814104424444a0780c003a001480c1e11b03c4c00c0e03801c0c1c002c0768242c01060 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 519337104 1250 519335854 519335863
    0x7082703070b0a120f050106020a020f030312010e040314030a050901140f0109020a0c060908072609091807030605070e0118062604030305240f0f04060801091104050702 74
    0x403109808440c0c42c24450981c02c0760520541035048105607900c40010012842c00e00c00d41f4060302858004010b0514a070042084480004034600c0c400c0c1c0c4208529090a6221040f05e411540128840d6007580c4803890240c0310000141c030301c0c802c207400120400039108604d812290051050100800140c0c03443d02805001d08000c07502040d0400042c00100845000c1d603001302000501864211180da9080e0b85d0b18050b920030507416220030b40c0200380801402040703004207440e6000d07043d2045294000ca820110280158012a40f141c00d20302c2c0004d042400c070320b0384901290000c0040c0d41c01140c80e85002c07802440165506800940c00d1441c03940c05500883c1ca01c40030b100700700c103105000c903c2c002013151004c05007921a00030700007440c01d12009035032514403607005030b100fa10042001c0c07401151a841103251440c916403114907403150f01415864640046002d10b0301504c0c44801e41c04000c0106015146941c0701c1000f035031a01d0651001c1c0310366200d20b23100c00d1400312000e10a9031a40c11013203958 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 519338354 1250 519337104 519337109
    0x403120612030228020d0f03110f0a080307030b090405060907051e150c0d0801080c0402040501080a050402150c10050a141602162414040e09030708270307 68
    0xd40d018140c01c1c50407541800040410000521580301041c2130345c0c0c0800c411145c1c40c44111541d00300401084100740d0000d080e1102034200d800207150a244c0c01c49990741c0c0f41c42c0d1031300103000c5400000c00302d41110304c01e0700a03043d00503018000036030301d0a040c40c2c0705640c0c8038101e8905a050140361780c08a01c9142421604108820005070030101745d50b0181006203c5d03150200b82052400100042a4405000c1c0f00050908560740c4074580250b2400344024280003442c40410320030340c81044140980ea820180d06a00901c200a00113910742d264400301d400ca0103038103180000d099011401d004800000144088090900c0400380f00b03d44500354043c0c20b45001020140c9044c803071400160110461405c10700d40803c0c41c0c4101d9100c050301d60140e509030032068000c12800c01080c4d50b400c9000c8021003c2e02458400c614042c071504c0c002c0700000c1018004c42c01156250a107842c04594030410800079503000580010903550b0b901c3e92801e1038a0030b60003500c80c6040940069444120134600881d88008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 519339604 1250 519338354 519338357
    0xd0501260106052107030215030a0509031207030506031f0621050a140c090f16020d02030f0a030213060801050a080a0210050d020c010507091a031b0c030d05040312061203 75
    0xb540600c2651900080070381c113001942d03c504040000540c0e212482c0c8020b01d446403090070f0b56401d0400c1c070f01c010b941e802402c1c411507600401a01c2d045401740c0d01c450358070084a00c2d0000e2107484401c002801d05508240c004120342a00e0a49038002c803a542c4024100c40c0d5a502909002c40c907039107048030032041a01c02030a641c102040d01c20202d6501071400460400380000e031a5201203c80004108a00641d560003002d02020200028400c5c40e145456840d135140c0001c02c140112000025542e10600d0200502e018001c501421124000c0c0c050303690248421021070705164507010010484e10302446101d1107066003020001e00c0c5580491000c0c07500f074015043c40000c05034204156100e0b40100725000c9100c0e070030045088152001e1003401e0241c4541d944a003455031030030381c4000c1518003547c0d0303265408030100f00380b01e04001c603044154540c060900940d0b88a090401040e400d5000d2000100034042c108003c1004155120504001c6400c0f00c403410000940c07600003401c605212210004c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 519340854 1250 519339604 519339619
    0x1032a1b05070e27010204030c060e0f0f0d02030102031e010b0c15040812090c040e032505011401090605030d031814012c0d110d03110d050126010605 66
    0x109603d107008420b944800d885109140240034410000c3e8020318154440141d650302290501c1001100c1608100800c0503142002510071480005100d000c00459114820b1030100c0c01001c481e121140740420050f002402151245403036003800c603e100c40204440000524403001290300785210381031b0b440e4940e00e04000d1a005a901c2c0c0c403014000b801400c00e5450740c0051020000c009084c04485105050420282a18a440405000958003001d44148141c2c2081c07040c2244086455042541c1c0007600d206420030061a045c0140141380100d25038018010000c00442c0f98401e80d000201110001c0e8100e0341ea0170507958003102203600b0000c3e88403a8003191b50300c160104040840040600b03099900001d028140c00203aa050441140b6461100104001c0b00c4004014180004141c4400c1d5041007038400b01206400e03501c03460800c0000003450341e00c1c54907036101d103030200c20f86803403900d00c810800440d40c41e140800d811181480d41d00400030030b0203030b045409400c103015a00460b5400341100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 519342104 1250 519340854 519340859
    0x2030403080a0903020d2a080d08180601260d141b0d0201060609050402041a0304060f0c080f070f080a020a1103040b040e0f0702100b01032a1b0507 65
    0x864650b40140c0b0600c0800566401c040007580c0ca0303092118099100740d00c00440708000b49000c030510504070701c0e4620501c1c03603d542085500400305030000c00201c01d181144040d51440c01001c02d050300b4480d640d0003441000004200182403280114464030b4802c00e40350741011040d030240e5103d00d00890803000940c2d072180d0510710710b602d501a1460145112200e000d008190504c9464484c030003505100607074540604104442e000b1020380e020f00710540e000d40c03030705003030411409800c00804118141030313500100081c00e10100b6800140c002c00b01c0700040c040c12000038401024003a00751040990360b5004c00c040b4400c80d025075812409035090361a000c900341e42d4100148001d40203580303c0c82c248681e01c0007102c0001024002400500240d905040d140d5040c6032152024050041040c1031010481e020310040c3c6800040880007802071078004540010404012809003075181828040310703510682450740416a070171a0079298034203503540c0c0d0038006a040c9220f00c0d40842c001c09089600810410b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 519343354 1250 519342104 519342113
    0xb0a02060930091002010209041a060304020f010507080a050a0f030903171e0a0e010b12210f1603030c0311030408031b03040602040305060f0c181215090c0a0602030403 74
    0x1e00d00d202c0e1007109824188400c01c0c0c04200c100d4880c001090061354001400065880c10f0b104020304190500d0500d00a48224400b0030000d20000d00040c1c42403410b0701000207aa0f12a208072074919500c85043c83d141c584495015000383c0045920801182e00b0040200e15a031091245912058066682400d001117190b140d1a03020405400c903600714008040b04408000150340c500c1c01412850000500c60303182c91101421106d9081045120706040e03080070f10107140006c0c0321b0314900d45280c14411458407041003030140b031140e403110b2007002501240c0d290340441e040c185581d0490191f2002d000700c00380c01c0d07401c604503588070000e001c21043c2800414040f51000c4091039001d0440c0a202e041c0720030019061901d50422681205e10640000703003801040414440b071500000350036804401070400388202c0f1800c0c0210340e156800001021001103181d900c0781d01144191088900750740000841c83c1c8100014001241c19584600c0b80c08050440750500c2e0542804a9070580d000e5410706042d5030b00d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 519344604 1250 519343354 519343423
    0x7050f071202010e1504110303071a071e051b01050112031805090405030a02070801060b0304060216080310031a04030c120215070f0e040c020c011202130b0a020609 72
    0x403004542d41d40700d0407510000200700ba48200340541700124043e10b072514002c1900c00c00c2c001054040d4100340050030014504420300c0c104051030000d608225a2015000c44002d40c031000c030415880c0c2041103c001361038105000f071108900308800c0b1203a014600c00c00a007610030038800c4100007401d941409020a2141007034040e11013904c8054000b240d0341e00001007d201041ea419219500700041e01c91040303030104003150003010b0200081c4030843c50001c00e10810b000c0108090030079a00010020608860400b8a411407a4851801900ca003031602c12148420750300d000403509440712a0068018201440300244101d606507564880e2181c00d50700d54010800840030b10040d8466950b851500c84104201c203407081ca419520640120304400e00140412125031107103009030301d4085034a0030581d0109804c80c010b002170a1414910f0111100f1000034418422003850062007c040800c111410400a140340402642112030b03548076441ca5540300c825114140321030440714510301c11001070400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 519345854 1250 519344604 519344633
    0x90602100902040219091d010302030c060306040219050a031503020d1b03050304060302070b130c0e27010207051501180c03020c030a120e0a0803040b0a0e07080d0807050f07 76
    0x14005800d00c0f038142c3c0305c0041d081440c0101c10214514000034400070080700d084503600b66100c0c00b4504607524680100707440c0c044050880303019040000000e000c9480303d070100c0b44500c4026501901740424110010440d8001c21301d0200003a0603d40103941c1e500c0c2c043c90001c00e42e50000c080c54504011a5543d1401034066444020fa161031080d0002c08103509001500040c04680c501503030781c0716a490003407a003c000a0070700040d641c00e00301c4440803982e0543d11100b81e8114500c4d2007150389421366440642c00c2004202c88941c1c0b58654801c180e60341c10b4024000051050044861004030075540d020880000d010710090a83c6044280c158034050380c00140400c00142401440d0215921140d815503100c4481000820404250805841254411008492103c40180c4240c001999622200d88000703000900485020000b20310245071035408520f026104500311400d00d5920a02e450b00c500c443c91058002c1200003001074007490041044805a103e0140014036207000f42d030321088040b074101e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 519347104 1250 519345854 519345859
    0x901020c09070c021518090718080a1a06100e0411070b060906010908030a0305151c030f050301052206090e030c07080c090f1803070c06020607090602100902 69
    0x2a4030040d0703455002419000e600c1541d14080141d542d80103000111401c40741d0b50f82c00080c00c0000c0c80d41035000d810130911446046031a0400c941f54a041221f018000c11030181c200c001c3c44000094514000540c10a80307845038520030321907a0425084a442c2508641290300440641c034404d00307561003030705801501c140040c0002100e00e4898000050f9400242040340c030b9118182c10b0040500e03220780f54941c0440309203450310b451418030034100cae01d90240c00c20000a242c0c481c40880e12444088036001101c180103440c15014080ca4100c2c01281541760380294085286001a40c000611490880341612800f4107030484680441d0302954907801d075007051a0b81180d8a24010a0f00d001034020064100c40c5c0c0c500450f12149202c0c146414924140e010401c1c0b030384060180b070f4582d00d40802c501d601c5503428680b90300a0740c504c10800d05000c0c0f8100b105405000c000f0702c6004024010303240a060311031550031281a030792585410754510803640982c40160348076038514011400c098000214581c0301 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 519348354 1250 519347104 519347113
    0x306071214270606010509040e03070b0903031f06020c01080405011b021c050412060519022106010807091e030c0909020f01080c0f070809131401080109110402090102 73
    0x7050240c0d51418015940d200c04a82c1e5141e1030640c071159591454900c2d07401c0e80c050310103803c0840c0081c0c46c520502c4186030290744c4401914071011b406100340d502c804c1c0c10010054042c50180c1d1445e449610481d003004c0f042012400c0d0b42c8580fa142c0b071552050b584160010074401c10280015118400010800c442c25904c4a400034180e687c20309024210740c205800601c1500b0075958000d00120441d00000c0030810309020801c21500801c040040301a08144c001401f510b40020b030345030300752503e00242659800001c00a85e9410480b210b102140c1c0f162421406580350704004450109042d140480000c8a800003840344098140311103a03404104420b002405550340e945d502c9404440e0300c2204203130303a07613a0344c1c00c15030400304032104c8480001d10b0100c0d400e00d40402500ca403402110b41c084001540030400e0001c10003c0303411113140300002407201440c0814100f069010700b035080c048944601c0c1d0b51000054003601402046542da03442100050f0303a001c2441440020f401c9110028118484d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 519349604 1250 519348354 519348371
    0x301030b0c04031b15030b091906080304060806040507030501030807060b0a05030d12060f03020a03030518040912020c061809040f020607030f0f05040f0e070903330b03060712 77
    0x5801c421841072501e8044584d481c0c3c0e190080c5130480d0150b0038840b005140c280240c030901661400c41c8241e001c000c031220300c2040f29195601e8401403e054204a04038840058042211034020100d00d05c5544c04844c00d00c026903a81030110180ca80030701c0300034500170091161100060040c0c00020340c0c10300c080c05440c00b1594440c0003074548580ba982900210327030041307010080c0c88614024103010349585d0548508451869011488010301884050708105010803c5a00c407017035080c0c01070000c40e00030428400d120b410305107210f41021510f02100544030305080f003901030078890113460764400160300b0b000008903540148043c11000400490360882d0400000006948000c090b04500b402a40c1d4544104860724020b0700120740d0801200078400284000c1000e103a00d0484030090303030302c03140100300c0540382c0640a0391240c03603075007000300a1a180d01c202681d044041210480c11502c807240f500c2040f0420342e5039004c85101c000b007250542c1108000417180307070040c42c00301380e00403030400000741c00071 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 519350854 1250 519349604 519349613
    0x309030803130b011404060e040203030714030405130c1805090c090105071e03091a1b1e0309010314011a03071b0b1b130e09100e150c0c030301030b0c0403 68
    0xaa090b000515200c04017800c403000c6042910803a0060a00303192495405c0c202900041e641e4014600001c0c0280d00e98550b95549000038015503006080240011450b88203400c80340340589007101c4070400083c08441c8003d003440d400b86040007180e401404802c0e4070f485840a410082e03000b40811030502504020400000700e030a01b5000324981c540d0075140902d85e542c42c00a084510700d9000c1d1030307130421110504102100550888800c1882c1014074041403201008581c14044445001e84403d00709003a4440c07071315004401441410026a401c000b500301f4007400710000030080c011040181001401450007404205c0150b4101c192070034650903a0300c05169615080c000200100c0b900c01e030110502802d00c0d01d088080445a0300300c1400303030418079811011400c1e030045c0d02c110903440302c3d402c1c0441e500d41020310034000e56144145040c0160107000141c150303180d100000401c6010840e4000a040081400c150303008665000b0245182d07034a5a2180022203c01912482e80480d04000010014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 519352104 1250 519350854 519350873
    0x10e01110304030203371e02040b0306090a0605010902040f051002011121010b03060d02013e0c030703050303010905040303021b0109060506034908040c080a030903080313 75
    0x202d0300c1c440490222400e00d0b0701e41800200780c5045c0d49103005c0d07003801d000003003443c007241c1e85501d400b0000c00400c00050002801402181c2503064060183c0010300c10031300803b107442035125005620511607170342e03500c10000c124440d600c01d8404004d2000c0041c0a186042c0c4c100c42c101c8800c52001042840e4002c0c440c2406500c18044112001401c039011a00e01c052002080c1c018902103008a0652410202264140e41d580c0e0000b4104a05400c501e00b01203600402080303480c4503081510b1028608240b6040080b001d40c024944511843c3d818803c00e10f8005215010b03070764444c0140d8150b07407800d50400040c00c4090801c50034141c0900c1818541d094021114807000a03200c0017003405d240a0800070222140a81114000d41103500030160745000081c038100d442c5480c43c4a0a9a0041c04121080401c6180c020955401c011820f800c400b81e88500000c0c01580160b406007106035580841c03540e50906d40b040240414841c0e031080010440203000756900c0007140b0b03094000000144c0c0d4500b0711 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 519353354 1250 519352104 519352123
    0x239060412060f2936161e03110a0c120804020609011b020901060f120603120c0f020a180f02040503060a1d071203110c010e01110304030203 62
    0x90064100400003031020724043c259110441103410441c0c000380b9002c9069031203a21501c410300c021052030f400442e86441c0f8884048140070500b14070030f5540070700c4003107001e820044004180314148001c01c014162140d40c81e02060002d0f10f62840e0903031244021003449402e000c282c03044c0750341c0d020601000d6056000030311100e40700341e0720008045030030719003450780c3c0e402520403800f0030104030304000068503240c00702c4400c4042401e04940e040c0504030fa00c05010a203c8000b50422440400041d51a4100e03a01540210072625601000f000144d01d00d0101c80c1c0e00c0c800940001e100c600304400f010300606070070b170209000e024440d00114094006c51700303542c07107a03220003507030107125000000038038040c481c10740d03480b003112415842c00e81b0700000641c0e9003031b010381035481c1c075641d4913007030401c3c03010f80e00710507441c0b4a002c0c2c19640e500369611510082a07110002c16008640908400819903d0106181d445164141c690b071610000c1d04004603007081e6101403c0229100c10800400980d6041000544 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 519354604 1250 519353354 519353369
    0xa1b080d0c0611030601020d03050a09060609061a0a09030611040b03150a080c010206062b03020a060f05040f0b0603030f04080303010302030712030504090203270309090702390604 79
    0x2200715207080c2c022921642d1100700000414018020540c0c0c1c08224a49402002e15011980751220400000105501c178001020076180c54000208650680c00000445071028520f0314100042e9541803418842ca486180c00559054003d02c0000c1140d40452102403584030054207040e2035144040c1c05510030b803201c031a043d46001886a6a00d0500c1e008805444040c02524140b1a40000070f55100f0700600207500c503c440007404450f00c00100906a070300031410100341c0c2c0312842c2d401e0280d180c2c0e007030500c01d45800303050080f400351811341c0c0c1c0100c0e405185e0013802c8804000c1641c076880303010040645261b90600003004017100e04800c1d040031780f000d415540c0c00b0350754030b500d144101071600d401c5900003480130148d041c0f084082a0004103a40803220400703405a80c035902c0d428107116840703290310021554000d0328104c02407120004082c01c6c2d460070030343d880d4020340c032121420303680d90310122455001e00e51206520540b101000580c0d240b00c02c0c1ca01c0815510303003240c10004086400c01d802c00d00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 519355854 1250 519354604 519354617
    0xf041104090501200a02030a1b0623011a07030302030411030f07051804080405011101110418051b03070c03020712080901081b091203070c030c05210a1b080d 69
    0xc4aa0b4642100c1554080c08138411034604448030a02a41302d00441c0c1442062181c0c0145901c0d18204002c8030072440b5510500410100a101120581d03c201c0003601401c5900038100215450384202d0401c0c0c06090345084850030101c0302c0e0b40031030195100400450f000c0e080030f8202101503c040080e02100310862024040150420040c05041d500088205201c0030850003880041034010701220309494080ca801c1015041154000780580140308060a52103c00140003c0f140c1e161010040b848034030034070510464a441034504041c2107500c2c40d424200d04208085010113010340358440566109005944809960f45008640300031591401d4404580000783c400365507034000840740c3d03c0418041c03c94011408440302d08441d0103001201d0b40501c1500b031520000000410540703401e942e1040140e19201d4417403600824400042c41902d001312400c0d400c62102e0070f4001c0075042008041d200400310400706484240f034030b9081105401441400141c0030554110a011900c1c3c906400e40781e40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 519357104 1250 519355854 519355871
    0xd06050a05150402030c04030212120408030a030b030a050709050601110f010b1206010e04080708041e0515120c030a02040e0c0c10060506070f060f09060b100504030305030f041104090501 82
    0x1000c030b645815038152285204004001418031010700740d0f4144c3c0c0d01a00c010345480c1c8007a070268030301034600c04203030759603500818000f03400f1034000010010300ca0199020b00040c0b160b20241a948e60103124011301e01d4004440500804130355030310195025105251102d0000702c205051801e0a0313000920001c41d9449250400d01401d210701009072080fa03002c01048150701d0045210303ea00f0300504002c04010000405070b0030721803041c0c29a0080c0c034441d2041007001c0d58005a03040f240200e4850079006541c421103510710507124005840d00c02036140b10504003030340c1d102003c41d02a84000c180304001035082c00081510307850201540c1c4a0101c0d5810203903a90a84251246840f08210308115a2070800905100e107440740019240d1b410360000746070a000d01d1910f80b070302c0902000190300340c020b0300e056242c409001171034000c00f070101002d8480008484681c4070803100f5106501000e0b000c10001c0010a00199000d464154047d000e002010030000c03254000070156004140300356000c7c0c0d107030b0306035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 519358354 1250 519357104 519357121
    0x153f060801020c0d170c070201030b060301090c02070602010e19020a080307080409110702010912150c020309041506090510030905030a080a0515010806010324060305042a0902090d06050a05 83
    0x1540e0300002a070070909170004a03000d030b943d1000001010b04181501c0450a05e04590007500910010403009103400d80380c5da19081c1100c0140788204c000070040c41244000501540180304510100c80600060003018100006200e440020000100d0f0440c010036400111f030f10007440981200751091b070000b582e5525051690342030740c002c200380d000c00e0365081020b240180e070040c140b8802c03103142402c0c06401c0e141c5410001d44508511080105076402c02100d11101036002c80203103076012080f2801c102c4100180c6905d0500100f80c01a000424100c02050125260032104443c3e011a0340c5030200e403401060751040d00350340000700041d010a041d44203002c680c2010303008669008299070810f00008031a440002d0a55801400303070b82c141603031a1460a04040341c00e081e4403292034003444e4500b2507652498020014102290152801e800181800188011248080324403c141d15081e00d40e081c100710f00d8038000d500c00d460b51070340180c0c0010941c00052540c00303403a10442291400241c1743c58400c05 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 519359604 1250 519358354 519358363
    0xa121a07020c0109090b0a05130920100203070c05091008030a050405010e040504110405090102090909030703030507020a0503030c0d0e06101a04051315120c153f060801020c 76
    0x48640320074108800786ca026211000c05800b00c6804940c3c0b042e41d50007007400980100700a0710098480039840c0c020220715031048528060b540c03810b4564034008500e2300301c00ca0701c1c0c1c0149c0070000d09a0710076060400c5075150459009810075864022912840eaa0302d100740e18640c02440c40202080c0c012504001c1503070024110700d4030310030035981442185820783c2c03100310300421128100d01c07440e96203000c6884543e095059031000311000e49000c0450402501f0540c0c2c1f9042100100c00103030404002418043c400303c2c52a0300990300c0300042d4156142c0008401242d0008451031072a5079480b181164012000c102c441d00070700050105598441c00c00701c01400810b60110302c3d022101c01004208206d8554503c096006903494100151621001004445032182a40080400140200c2c0d4038113204840d0f0612040358080d107410007503403807080000c1c0d4684c110030120303404800200709031462400004180100744103d41c2c0700d41d0802d40300c541e01401101d44a0300300c80a1a036021801d015104010070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 519360854 1250 519359604 519359609
    0xc03040e090606060a36081005090f03040317090d1203050c1c0f0e0114150102010908070201081003020604060306031704032307050915011704020a121a07020c0109 72
    0x384c2181c5091100c000c0074002800b90100301a03c1d8a40020200c420100840703845622900021100358403075440351100d95442401d49506055440d00000c110481c500044416403801c080d00074504251440c0c860b003002403221014250342d00d0b001c100e095195a907030341203014094482c00b105200c683c410b03c0000c048490007000090401c80c03c11024140868102403d01450030b02e40000c41c201d421400b6050242646503c1c0c89150342c2004000d40402e041a85403e03c6403072503000d081d01410040004a09a0f00b80b4500a010140d040000700059480b49144039404a25510207406141c1d0305d502144060340f10394010340010307503944c1080c801c12081c0400b040d81c02800560182c1011b0454a40c5000803c540011080c44848d0307202540d040b20b07042c8541c0f002404000c00443d09407409104510740d2840000e2010b000903000741c40c3c940c40d40c83c082c0c03515000d11740180440b440b1504188401c10860b4000c18280c9040040c41e00f044481e085c2102110f00c205243e074054001c16040000240441c070300e98 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 519362104 1250 519360854 519360859
    0x6070b1e0f060d0201030608030d060612140f0a02120106020c01021b091303110307080a03050a0203041a0603030d021605010612050604060209010c1e1106120a020703050c03040e090606 81
    0x34400e20984511100032076811803002c94102ca5108110b20060700240f840c0e90007000b40380004280d5500c40702866025004903940764840c07145515201c4081012901c1c01c200340c0d4000741001c404a4030f42c245005615500615030080140380090308103403c020301e002640324100589c01040f101069503410302a4611040200c0720010060400c00002040840024407100504507100c0030401890f110740400a4050185d10030b0741d58481c6030b0700f005123455008e0394520b030100e0b040201041c41501c5920880384610f4100c1c04800c0c0503002c0c4c84003402010740241184c0d41c1488140010010a41c443c4000d2000050350444081e0212080c030340b8a0a64445500090980d24104034401c04034030b000c01c2c07440d03000760b00090059940008c200181c40c08080743c00c0c05001401d0304a00c031140b10395074203103e02c4031724090310100c2031210381c0e4010000107104203440d07404400d9030000802c3c101c00254010b8503200c3e00c2824400c0c02c3c816100b8181c0d195801503030018180e10794850502400790010300c00160429070a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 519363354 1250 519362104 519362161
    0xc100e0f0703020d0501090b07020d1d011d010509060f0903010b010504080303180a0f0b090705030c06090103050c0708070c0e09010209010c031d0303030106021e1504020d030e06070b 80
    0x5890a46445284902c806801581d0a0310072204200b000e42c094014076610240ca00c441d4242003000a6881c6440013500b000705450f407080c10284002801d020310030b01c10584d40d0284011000d103051080c1104007071a54180181805828051742d11500504400d40c0c4620310b080d00d8100e6070041500355045020503505124003000207101c0c041000c000c49038083e010414810b00400400c107824030384188000050800442d01044008200d18515040d0003400500102d0b910280c40d201055181c045a03208076074000020003614116502035000954007001e0882094188880c0d41c82d4030040e50701ca500304845088180c6000d204541092490680042205008608241150002800e05008410040c0030320000d61041c08102403c8008858030034009000c0e00d480e03595030750b00a0755901d500c8070f12103400d400c0c3d541d1210740b61800041d1030540381d00d2080300c204261640e400f80641c60f06407074000c0d0100024040c4024641e04e42c0002400c200d48100c41c11000b525081510035001210029503842c06940f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 519364604 1250 519363354 519363373
    0x611010f091a0c04120b0601180b031602070e01081f02070b01030b28020a301e0204080706090504050906240925090303050d0c0908030c100e 62
    0x9502d00d80c100601281d441c00c1c003a03118a00310f804540550381c80800301514401031802040403034500140203070400c0e02c2d4800c80e0b41c000c03204c0003508015030040380348908040c80004e200c0700755a03230380f085000c50074019281030326107a4404000d040301c02d0b0403111040d4090b107000a800900c01054454843c01420110f0030303e0300c180c0d00c0004030f60041c400900001c008002160104141c600200040301d0743d50408005c14417100b003208081e41002200c00d022800480040d44008840b079020b000803980a01001c86011000750070000800000c986808c0038498000c411124015610042c000341681c10005c0c86040d02d4440700a10340707000c82e00304500860622090042e0014001003250b00303d580c071200d10541d64174000c031015407807854001c0b00340e00031107900510524140700000900001c00030ba04c00c40b807107058480e054070075a0540c0f100a00044080000401500c61a40040502042441c0c8111415a1001d0040c40c41e0070040405c00796811032040300c0358510f010f2203260700b5030250358007908022a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 519365854 1250 519364604 519364613
    0x312061a0a1e051606060e180c032d01061206020c0c01050c0a0b04050111071401050a0506010219240e070510090315020d0e0601031415160c0c0611010f09 68
    0x7031010b0102c4002481c4c040c4020480d940e04000e0280c0b140017102041d0b46002000480420a5403007201c8a40c0101480c40002e410041000001c100d504032800c41400da2842c42c0070848a075148031191155660603004c114007104c05c011407402e6008000c00358941849180950520328401d643c00d062100800140c0f003034000102c0c174521404d4100c90a034041e551355007800c2d030141c48241d126590905000890030700b0810450300761002550248001c100c0c5039590010032084500c16144240541c0c480644004008442000101c1c0c0b2445007482ca4540c203c480f10000e5a4100b648200040300c1d00e0b004003100c40e84080180100514085600c011882004140070f002d000d036502001c0c00704803a203078090808881580480c0c9240300d00107000c21004109248854460001b80022140032003080240210044009804840c401c900d114800c1181c803030b0160200e600c1850000b220a00110703900d140082041030055000800894489070f0851a02210705421181a81c0900304c0c0e49180001100115 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 519367104 1250 519365854 519365857
    0x5010509040209041502130f0f0b04180e010518010b220f06032019031e030e0406260f030a03020c1501180e0303090a0312061a0a1e05 59
    0x50b405072800d1059488030706151065011901c0c2041c2a640009005210054604400011194200703100c096958484014120003420b0b8031500c81c61141c140414040c5e44800081c900421101e10340002e01c1c4070ba007104050a446e411240300700b41d00090000f00c2595842801540c0c0001e10031030306906026202e100c0201c4000d24040c4144561b40e541d0b92481500b00d4607803240e0051500406c1d24090300b0014142e1a9480502d241281d00030110350030120b43d07508000e0f0718170041c0e81d8802c210740850074800c80c00d54103110a600068040050110710200940c2340e0f48284400303810a030400030100380c4200890460044404a080c1c02130f48090b200040760304000c02901d620a4061502581e134400301d11005103880d04540305180c0d0500400b000041440030051400c01c540c40040301442880200c0000c99184d00040f259815181c0080c40340000291040d00c0c1c1c2d55003a91605c00005049407641505040c0f0803401c081c60000c0720000410003846130b000302042c4104001c084170707500e4080e80140002d09070b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 519368354 1250 519367104 519367111
    0x40506061c02160b0a0906270b06010309060f06080606030d09050f030c1f0e040b0319231e0706090b131a091306050a030807080409060618050405010509 67
    0x5055021806503480c3c420300003865031840e003103140001d56007044603d010060045000882c2c4c440d10781440c14461501c1c1400400c040102e078400591803806640342d1080c07010005015604060380c6150400c0010a02d1140d506004200200016503a00b0100803600c4c1490180004d4426404030780d01d1140d496000e80c000c01071700c605583c01200c0100c0400443c0c60011038282e503580c4405200c84000060150782e02c03020301c110103580c0f4841da40e1a1841440708541ca8156070f6505600128050300490300e82c1504c5681d460311400300c18040d0490215018500110391184e44000c1e00182c1d1082c51410f2460185104d05030550082c02e00b442c54072070041d26032007007449480300c0181e0100c1c002c62450301004e2800d0040807c0e05000b0800d40420107050405d9009240c0c01c3c0c814901102003024510103446010140c48001c0c1107131268506580352850503412008084554a0341000f0110740c010303050040400031301c201d0300c903880c1d43c4549002003290b0031141d0300100d010380e2803c0010400c2d552501c055941 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 519369604 1250 519368354 519368407
    0xd0204020702040b03150a060b21100b0f07051006051c210c0201020f010e2a030a03080402120307020102070501050a0c05011d07080303010b07170c0a1104050606 71
    0x1d55014a201040c0070b4260450126454020009030080d40e070348504480b4820549010308001c400c0d22003c00c80724600880781405042103052001da01c85605141201d508124806a0807452550b19042c0c550558000e110744142e07041d010851604000e07040015600001c1d01d010107000f82814407002c903180c0d03106400102c05010f04921100300b4040b030846001d10398010001c5001e4000d1440a0180100d109030004034010701c138201c07500381d803c0340c180b08082c44001400050f01e03d000c641079100105003800c880d0100e555001e0130125403540d4040001c1d6403510303c2511042da480c60180100102d1211442c25900d00e07030030801028006030790100304801903480900f042034682d00e81d00c104945042021344003c200d5031810039255121010341500001500c1c0410480f8025a12004442c0d1a0300003072190b540c418205200040004865100c0040440c0c04041000d0625001171012841c054a040c07050700e0360f00a20b0389001460405000305c0d41d02c4401076500760720b4208584c00340300e800c808200b2180c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 519370854 1250 519369604 519369607
    0x161409060d0606030804030b060603040c1419080f0f070b090108071223100602121e031503210307210e06150a050306072f0307031403060d020402 64
    0x140140d6030101d030126200d400c442c2c01c100440d141e00e840e80c02a88640401d4810a1050002610f245825000c4902c41c60307120380c0d6540c805203040d1441d9002103006103e190b022000840181981c030340c01d66411700801442d00103242e48604107039068280b0780308000c005102d8010728010f000340043c2104444e0b0f080020b10349411181c1e40d90000302d0310000c04d03140c4200300609000d41d131605042141703802107150b00740506600c9161100007560107503202074400c0740f0150f048281c90000300a0003502808000311090b01010b00032580120104140d03101300c640009244083d014551203040810452603080704080c01800c0c100340006405101d404000c0004041051841d00303010388006184081082d8004800305000d078520059001e6254102100ea820f1a55019103440035540b0708140c46804880c805000b81100e501d0f444000c6610301041c0d0301d070b10700a42c40b44a000740d02e90007003503001c4807946ca5071020315201d1945280040012b00c03146148060784005005000d01c2d5a240e0418804056045078010b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 519372104 1250 519370854 519370861
    0x6070c080d060b070803092b03020318160314030a0806041d0f070512010c090509181b010201200301060507290f13050604033c02161409 60
    0x4058a4140c0043d1036442d40443c2801c20401c00340059401005000242c610b2010a998005007000c118444558118490140c04036140d0299005540004461500350442010940ca0f10715100340d60048801c08940310000b0014010751190000030032002501440c41c20710103407401064003501070046c902c200d07982c0100110b503010203001e50142001040c19110005820410b29868580c14480c05024150007003002e5490b800c103100e500960612526102d10203030a00c0e080c00aa041c00400d030141d0212103c5c14011140ea08008868520205524180c4c01c8041d060009081d51069428022403d800c500c1c0c101d92540c03a0b10030381e41911504d1800980710750840c10219a5280080351281a90b807151001410655113485407601c1840c10104d81599a03ca0900c3d4184030568000040c0c495000701c0c1c007250009108100c00c0000324070071031444040c03403040044104c84e11003103c482c000c5da0103450280301c0b0207a0140000c0510f0784040a00c410010720740200105d40c1c481c40d2500f1880340c0f0045000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 519373354 1250 519372104 519372127
    0x5060d0204110d110708030714040806010b1c0902090115052203020f12030405091003020303190206090d050706020c03040b130509131104090633060206070c08 70
    0x105400160000d000707210011440b0382c5641a81c0c000540201800d0400c1c551020b010381040c1103941d010740c400070079495a03507151021260103251342c64030a0071000800000500c2c40c810007813103019002c100c0f000c0340d86d50b224084803145600c0c00c143c3c0b01e0740705052842d40c4000d070343c450010030304440704805002901c0203c10412110f40c07040c42d040d008013400c49841240c45030b00900d480401d50b0b00c2902c1400c0868044002c01200009500a400341944104402c0c009401e000c400305802241100c5195038464a1741d0019080d40c1002c1111108450204031404009504109807038001708280c001d00940c0300700040080c0103110700c941c0a46006e80001e40712268900c20001c0b580140300e40142e4a88440c84182c0451100c4258403990307100d51001c401003001d5a031070f1b5144441541d48040c0c6466059020030a000c007030442404251000d903600d07010414074024512000303a41c4152181204c0402d244010031540d0840d41b40c01070b1007154441010820f58641081c80e028400b40c00c421401e460b41e030f540a1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 519374604 1250 519373354 519373369
    0x2101215030c05031908040611120d200903070501030504080c0a03080717070507030e0d15021e04080c130e0d05190216090c0207050d0506070807030b03100506 70
    0x31040d08491800c0c030010a0002c2c1c038120506a41086050307841d00704949003410410286540050000c9808000401c4210300614185c89007403903c10030707a21030f0342000c101e5191540102d24a80c441645401c0384641d5000c4015101400c00740b0700341c140c1e00f44065003000c6503880d0303d01c0c000c180c103042c1d070740021070140000e6206030344100d23404c403017102d401d501603140003418035109444040202e03101440002c0004000040d05105100d070340c1d207650510000703850403581d40d1001c140b080d4000405041440c081240c001c14111050111480565100540b041020002c039550720710182c01c0a051000384880c10010581e8034600e9003c40d003062000c1e05070101040200540000003007a13100d003140c0c24808036040300203000d000c0741c20094250b000803040c0d03040e070300d91461115007100d40c106190709004480c1e09030700024841c0c40740d02c102c0e0003164503100401d8460f02c3d59201515070390b10060820102551000b04941d0002c0c0b0383c0b82c24000001c010700400c0d924285244001e142c29254000101991905003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 519375854 1250 519374604 519374621
    0x100e12090a05030303040c05010206090303040f0b0403031b0207050f011b0201050c0f19030801050409152d09050106080706080c032508010503010b01051204260d05010e0112021012 79
    0x4044c3ca40d241050303e442c0c00741c82418400c0a0143c01094005101818040b060b44c0c07169400608182c203203156651030741400f96000308114185680d804084846644003c541d821341c500c55002000030320309080170810060300703450b070290401120400002005100c50010301d02c0f59130a003851900c036121041c01e2800e01c0344a280390401e5100b844451403408100c0c41d03203c01980d000e501d03003c6803079032204244411380b800c03010042d0071034401c000781005045060b4051070b0105c0601003406402c1070700c141a00a15440000001c07c101d80344c1d602c2109011f801e01c00c40008005150007011210700e07003038004c2c10f41e180090809540203c04400506030300e408003024000c254011440310800101d00201805d00791080c02018080d40c41d25100070415405a0101c9650000c6030420203040d40c0c07255600a031524413098900310020809880300c3c1c1c5001c140c406802600e8400602155070360500103030740d11480c016400a40000c42201320200540c0b610b0f40e11040300356961900600306404041b10070050803100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 519377104 1250 519375854 519375859
    0x70e100b03041b0b04030f12020309030f0304050a0806091f0b04110309070e070c020d0f050a08070308090106030c0603020a1701090b01020106050f18040c0b04090b0102100e12090a05 80
    0x41000b0000302c0321840381e0b00b20f42005100400d6071500c501d08074500450100500079071420300c07041d02103050340300204003403e880d01c101c0307160096100101b418400380000782a0140d201140c144100d140c0f82420b140035009500c000d1803a49007002120750707034500284080607120513078518004080b8054200b205051001f030010b1020902410660700207a1046505480d01d005502000c01c070091b40303001c142d000c0c40c00c0b90756181110b1426000c2001c28a40520100c401c43c0e2003900110009906104806c803941c020f00025803501142e040242140500408105803649010020301c0020106030705042611258038005071500290317081656444002e850311328ac00400c603800096a112650419a1244004e034001e0010603034800602480d11001103903240e00c40300201c642c0300419014000a0744c898000c6022505079a690801c00c43c0a5101c0c2d0002154a615040ca486003035804020700010541b41040070401c20408501d02390710340f0b0340a04a08061180003d103149681d441c032070300300c01800f0300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 519378354 1250 519377104 519377107
    0x123041b0608072c0f04060306090f050d030b090a0f180c091a0a0b0c0a06090503190c050615040e030418050106050423061207030603170a02070e100b 66
    0x310140501010030481d03d820004550012080c0c1003c0d610300c1300c3c8a41d85202401c00342d29070803041000640c0905003210794015903500c10000201e81c090058040c614000c0304107048910207410141d04106015480c00700381400c00d064026262a014185c0e5030045500d0400144010140c0b1f0f010301501c03c0d40c01e14146620409581d038103018914690204682c058241000501c0821055081e00f8111045042c5d010700b40b41e004000d100940f90045c000100100d05842040820ba039130345003181d10280b810b071801d910200e1805044048030b1209500d5000c0350401c0c14101c10560303212980da00300209594142100d28414038107540355600b14204550141c000c0d89d444a0b10341090380e41c4580c020f601d102c420350030407000242d00ea000b40200da00707440700401c3c000040440001034030140f0740c2205546410a00410a4220f6030050a41c1c007400341100d0703078001c00e42c545541044104c0c1040c44c45141c0d411401000400407546e000035a140c2200d2070504111000d9507000a038021190040e4402c2d0f140d01c20 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 519379604 1250 519378354 519378359
    0x10f061d01110d0807080702011806110408070b030103020907030504051903090503030d09050d08071e021e031209010203072a0507030803091603030c0201051c180302010e0123041b 79
    0x4210244c18480d921680d01e44502d5034820901300d0a071502c0c2403554040900760f8441e1000b08072070b508480e521728031040313100b4a45079a1340341117441c100481e48151080071000c13006004601c0d00034040342d000703845807609000324280360b141c494460400d00c04442107454040c0d01e413000c05000c0d401450041c9001015291030b0044015040701030214001c04680038001d1a4044403200c1c06860983e01400309962240880d446110719100f01500c0348401d44d040d4414507541d400d08480740030000c02c900e22440d002c0d41e11000b03800401c82460f5005041000564010300401202039403040c04004007c040c5464001404034410810101d901017100291003801022004000d10481100941c001c41190080b1200c4a0b980450350408000901005001810980c448400f561060380645640741116460344141c1d01c10b0782800044a001c40381310048034407456074082c2456028803403c618080240000e201e032220785a00942d18400c5505880301c650f0b000f0700401c003030043d00600400106205caa45004498 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 519380854 1250 519379604 519379607
    0x1020c0109063608130f05040f09030e060d0609020f07020a0602030a08011a09041e1113050d15050f041106131703090a0f030308010f061d01110d 64
    0x41290191081d600303081451181603510011001200d042900344074100a4041c0c08003140c118440c0d044e0303a408020f0200c0440b006401140c04001d0036401143c94003d441d01c01400241d541a001c0d000c81c0a00c0c05111101103a002071b250201c035882114025901c84000359844000c03c45908500f4080703201296003500e5504507001010010f000f141d401c8803003540e0f000304994904c81d072005000051119001040444203102703c04002107441c0a0460402255001060445410103c0415800c03540082c05501c2107191048008840001c2401ca1500d02d4200030714083c0c2d040c5110b0076004034140c021150600000d0540340380070070b00039601071195080c064014501901c09450030b40340d400911280040303500e4a5001c4404104004592803c01d2389007000309008081071700d080d06141d0200f0401350382d280d0788401130040641f080c203210000b52411414010844c0c80140c0024205203899041480b40a400030384003420044030081d8000031136001c03001211084614025015140b2406030b400f40f0b9507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 519382104 1250 519380854 519380861
    0x1707031709030f06070e0607060902061204060614031c0320072904020405060f0a0b0c0c06161709090403120c05031b090d0b19110307141b01020c01 65
    0x61600302c04030340c150500001990707100c880c283d0304280442c040000d07801c40d504009024115581c000c100001b4107020540104903540c0c06814a0b00050580200300320030080e4900c6000f0281160000310418400e840011a0b900d4244210007079a221441c1034040c802c0d03110303400130b1a000b05501c409076080d0105808289041d0028001143d600900442019160344070402203d01144c03105a2031980742c6507030b000d01c00107103006400940c009030303609805a069166103000000420001c1c642e56a60a41036003a00c0c18824400740c1d03903100d240208941c2541200354200c42c8100b98020720340180c04c20300446500d50314800c08041d940c00c041d02100b04014550000748261030550804000c2c49074502c5914105c0300e078801103500a0200071103108104030203801c40050000250301520044014000e0748034500201d000725601c0d9609201c41c1082c1c000e10000d4021800e9044210349100d046040c400c0001d080c14020054200c4600303404503101c1c0c9405410f03540d24035006a0343c0000c42d0b0741c025401c00716003c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 519383354 1250 519382104 519382117
    0xc030c010c1b0b06030114100905160f050a050403060603030305070305060a0b1c020c07260a1a22060506121207030309020a1a04060809030a0917070317 67
    0x951805007000d01d07840c0509060504900c420002c0e401e0340d2001d90701c039810000d0141c0340941545d0b035448120007000c00c0c4462036000c2c002070b4a05607251031410070f011056640041c01d041d1039190700300306a844660020032500c0220343c2c034105644c9400c2c13034050444da14051135001038040703401d28000100f13168250340100d000c2c480703d07036050040d80c0c2c803442032059541452040c19000d61040144039007030060f4200100c00105111400340ca0075000605081c640501504208188401b0202042d00d007030384000782010114203800503184404041c1c440c0110203e0b4880c0b5881d401e4095400500c1c0d03010707240d107026503104c0f2170680f01d65240010b0501c5401400700b10350003802845068400800300388005a03000850078041000e920b0813079207075000c40c06480907240490b000140071030007060a885071504156420503034001c540d00c1e42d1a000c6d00a08a0001400040c0e09400402141a040b0740c4000f82d0002d45442c10803000e001c4001c83c42041c42d0010f944c0c405800110b0709017031121680301202c010090b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 519384604 1250 519383354 519383377
    0x30a0b28090c120302070b0a1404030804050a1205071208210901060602120d0c0c020a0e1510020d0c0507080d020f010c020105060d1e02060705060a0c110c040509030903030c03 77
    0x41c454554150301c076003007100c0c3c001030003686c440e000410449141c0030040c506540c0c1d500d48148000300145501c0b1094015800480c1e4080700480c080c049801d1003019800109003021038032025118503211562103500b6402413512030000750075420103008846c0101d5406403d84442d000f4280c403200d0210b82c01d000203860102c00c95003420b40009400e440002d48246450b0350340c007580c3c5000d60354003100000b01001d22280045c803070342480500240c0c0d1071345000380080940601c010308614002260345d403846010040d517031040132400c00d26030b1a103a0005040c0e031211024100a4200380d060701b06141740240030f40c0202107500c01c01030340c1500c4c20f07030100b48a40c2c0d2644110082c030203116a0f50003642a01c0044032929046140b600600c4081640902c94a480b204a8056181c99580316004200702d42c2c80744002342c4040e40b125043c40902c004c10300c17940751140780918003440d07440e01440e40240c0391301c1050289441180c0700e40102c4d03003080f0140112031510b2001002c0303a942d103d0b004011a1aa04450030344003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 519385854 1250 519384604 519384623
    0x3050702010906050301060522090e0607080a060e010b030402031e010b2707050a180b042619080d05010e1b130b0c0f070611010e0c030a0b2809 63
    0xb07915002d030701071741d050b544143c84d510b0602c0306d1410160185105c0d1400c80160340c03120701e80083d0a00b035901c5030620000c039010180042d480c00850140580d00b0280250303081c07a18210040003048100701200d8195403010306102c0d42c039240c1e40000303498a500c0b1601c50294200d180c00e070b6203124105605c2420302001c10366a81c89541e012103102100e0791103030070203070462518007000146541d102c0d000601090803103003040840005040041c6d099481c5a81000410501c00942448000420403500052001c1c2c0d000c807a4402140b00a540d0720740483c0c0900c8003440e407080d07401e1820001030005a40000c01c40341401c20166030b50f0034402c6000704040e01d00b80f51801e41a80354803080803130b0310100c50780014044014048145001c0071800e565120118000b81c0e80680d035000e42681c0303c1404070200038080750380c40d002c2d1106115001c50842d40d075000201d60681c40319005c000b203514007103003400b0929000707500c50385940d8496108005902401e0401400031010381b80c05c0c803215142d0f0f4003c4035810700581514 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 519387104 1250 519385854 519385859
    0x13c02010c0809100c0c0c060320130e1302030604110405060105070f0b18031902250306020702030c0909010f0c0804050a0b091603051f05280b0d030507020109 70
    0x649110000f51003100090700208403140010300c1581006500b80e91394034101220b000c3e19100d0303112084807904214000781e2100301d10180d0903194440120000c40b070550300c83c585500489602c001d1151417142c04c04c519101c10001d00c44688840070300442c190082c0980701203140a2070490024002189800c1c4500c0c640004514154458400e0b1402641d0240f1030061300090344c2c0340c3c0603012000900c4089888a001e140b10004202030010306010280b6000c48100f241c0c0c00e0101a007029140281c0c60b45200c4480040b40d00e14094103030001c1240e800c00d0700140d0710511800428240b020015880342c1050150050114a000550218007525401d4100300912501050110f900c1d030070946000d4500e0340b00c1d04031074000c02c03d40084160080362a4086800800080f6850300c0082c06950054801e80c111600084104c070903209628a0783c1c000b81c40402840c646440005a5052811101500e00c0c1309100500220b442c03507805008007013001410194102c01900d80100181e03c4024101e0002d030248400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 519388354 1250 519387104 519387107
    0x10050f070e06180f041406030601080d12090c0b121b070c06110708160503070905010e07120b061303021c0809313602013c02010c 57
    0xd210340070070091169191600070580000a0403200360903a901c101c04240314911940d507481000c1c051829020b4194031446d08004040c1410816409000550407130030801004541c000954100a80307000c9001031003564030300704105050350300d0300402a45200000e40303408603605290864410000030000c0c0900c84950160414180100c020003803030320340100801c2c02400e00402840304803524880803581090358440102e407820111400801a00143e000c0a01c12400e050003458068840c0e140706114652600300700503041940144004e0400070300300c03081814500c090304002c03454600245510748030381c10fa500c0b00d080003e072840100d20620303c000d46410a10000c40ca139035400340c0c000d0401c07418500b03007400303002010f50440e401a60050010405140d485c2900c00d29403000703c8000c04c0001d001c04100d4000b41106004100f581000b03800b00c00c041000401c0c0d01503171503416428a0a0314003c24218000318100200681c3d6685a4070b0710101040c0303150380300d82d01045400311503000f4003900c142c4540 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 519389604 1250 519388354 519388367
    0xc0806160804020d031206060f0e03010515010f02100c030c0e0301050601020d1d09090d09082b031b0201150515090d082106091e04060c02070810050f07 67
    0x400c10218522100150240c5401d08515046034040d050400215140c0c0c0041c00c1120041d4022102190041740986011740d0b2100d40b520000c8070681c000c000c40d00340003480303442150304d15001a040081020108000c40d02c00d101c04141000c841406100d69920400090081c00421101c40001a00704139200c1691805004403401001c06801901890005010454200705a5104100d40c4031305890302840030b442e848200ea00c20744400003d46205941584000c048904cac943c0081c1e8954483c82d2f55805030020004844030f41ca0707000c02c0505c01c01904400507000f4220780300c012102c003da455207407101d0540640000240d8400009845405521102002200d03040700c2e07080d0142c0e15040c8103660761420141940c0d82506e004001107800d06602036140014440120b2008101101030000d01c4224202111550781006481d18101d441d40d090000580300000001c0000d000c2c191103849110655000740543c00143c80144203555031a644906031002400c4150b40380582005902d0019070b54510441 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 519390854 1250 519389604 519389641
    0x91815090604053d0b030a1a0127181212050c030106140d0608060112060509030702010f050a0e100c050c09070504030201230d0f050601080f011205030f04030c0806 72
    0x2c45000046203142165510030318010460300c1c010768400104a090b50100000d0b02014882c0b55000002801c208040300c2c002300680c09501c80102000c0f040c42107212050003202d540d00000d42c0045e890114000c441183c240d007180150801c1c0c01c0c1c10b0010400ba41c415906090700b40c81c80801d202944440c0ea10b60981c1c0300034800d4400140b20004010b4850407054014225880c083e080441e410343c44502d000e00f801001e9106007094603911400d0000c120f49400340710b50100d02c00010f03600340017194002804d908560020a0200040084c4003c1464028400102c83d5400a44814075100c05068040d01c3c108840c2e50039180e41c85500c892502c540b0300b0f060903501c10b49e8640d44d428249841c660054412410040f020781c00210801211007128000c0f402400302c0507080b01000c81c880c0c0c0020520b800300ca10140c401410071400c8170070031401442a81b072071811980c1ca918800145607982c02c0c15030031400380c40c060640a45e00000c0000c24045e912004001b45c03540d5605072512610350a050440d10b131083e9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 519392104 1250 519390854 519390913
    0x6070c020a050607050a0c08010c110109031b05100c051b0109110405191a040c030903090e0c041a0409060b0319050a020c100504060b01090509181509060405 69
    0x684090110781403e90144c200544920110f903113000032950f400b40081c010b504586481e83d502c04495070b485510504c48161480d20800810614199480c010031080c2d0489040e1100c48804445504010040003a03000d17905d03a0f0b5200b04000c0490f82c0b8014a107030b100c48100070344200c002c044051b91003010311544030b803d607010000c22405a8240e0501000e450010314011200760b0203010b00d0410700c80f90003060782210244000160b4510400100811a410707190201c04162074006900002a0003202060546c1c0003a40050b080740e481503503210780c603c80c0c0d070400e40c40312044c2c40c01c0b01c4c210040031010b001500c0e100c1009001c00c6856020440f01070104542074903000c0980c500c000d01140e080c0e41f185412030600b8401620301300d5120510342c605203105a00440d01c07541c460400c01445111301c60703900b4940007480c0840c901031400000501013103010707050209588506540903510401000060002d44a1038038200952030050781c00d680b00c060450301a90749008107240a10b454210520110200841d03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 519393354 1250 519392104 519392119
    0x1e1e1a0903040509040b040807050a080301030303051b0d0b0a080106060509040f050412030209180103050d030b060913050c071403130902270a03080c0c0f0a030302030418021303031106070c02 84
    0x3282c540150f25070b4087c2050710722460400880c00071600c10320503881c0700f038003680c6405d5880d40f440c0f60007011203c1c000e19030b030203184e01300320042c800158680c00c8517400b8402c0040803c420995900140ca00042a4044452507181250004102e40c100c4060241a081120b04102c038040100a90084e0752040b80d00910800d203038004860302c18001c1d40a000b01c1074002e0504291403500c00d820680c0c1c014281c2040c1d8540d4065903086950303075854000c00a040b80d00391400ca08101030140468003440f480d90503445000c6c1ca4000081c0d030340c2d4140099070364054100b141c2030030a140c03000340b40d0b849602041c842d5110000d84400070072040c07054002c841d03803030500200700240350207652110180548019610340d4085401e04000010800460141071a004450041d0081d501e6241c00c114100b980642020f0048043c64401c00103e90084180c0b01140e040a0019241c5500415100001d225140b10121040c515103004000d0642c00540941944202d8048a2441d00c0e444000d594600b12044002d500015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 519394604 1250 519393354 519393361
    0x160b0301080309130e060a1d0f0d0c050c030111120c090603040809220605040c0e030d030b0a03050a05070e011211040e010f361e1e1a0903040509 64
    0x20440290300030340700c60500025802d0181c00009083c41019291456143c1c0c8469030000c3c0e400e65a403036108481401c9009210442708a040355884020b00307180c1100b0710618800755410301130b0900401c0c85052000700200f041e0890050303180c15a403c2040305c081481d880b1000181d1156040c07045a6044100901f00e906642e40c40c2d030740903e19070108d0007094002c2480307501c45003043c44c0d1480d0340b10144d9040c0e4021030481d04090030300003220a006091010072400321659011620081801c400f00485c910300445c0c08400d610100300c01c1c5215900060181c45400324210605c080441d106044d225502c03007665603a40e1f80c9403011006400024050843c14180300c3c01080303850300b0f51107042241100b500200f50360152002d060210f4006005141c042d1214144c050081c14041c2c3c11801c500049401c90703074142c0d2080e01c5001c084c9801d00c4050001184c1e00c0b4400c418002e00bc3c0c801c81244180700090484c0204900e00460b0058140c407120150302c20440105500791404030588040d0b80c1d018003000380558 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 519395854 1250 519394604 519394609
    0x90303071707332703092120040b03070801020406090f05030d0807090b070515010506070b041205071202010b0f0406062109020d0f140303160c170c160b0301080309 72
    0x451501c1120308004e4510400030680c0c44021801240c5000c0d40f11000003a00c1c07e071003240c82000030b031100c0321803c10038100c100024a6004008031480c03040780410707004460b908003040042c0700e040788481c0e042c400d061000400c0c401c1500180103990060361000100c9a9940c606125818580207280d0b040e0403a01024a000d0710401215a2049041c640310b1000795549007103641950244034142e03401d810000d000804038240608850040406481d050b00d84035454aa4010000020744014005000c20210b5100584580c09031101103800116404060241780c0000e03000b031040700c4000303000c0c88050240013850316141c0300f058111011900c4041c01901025082d018082142480300b03a12a554400179002da100c503680213031128031400311020f503104c090803c01a980c802e0038501000364020410068000700c0e21400f170300002400d08041244c5000340c41c104842228102100329001e8000c500e02c09081e40001c0c0d25003c1c207030140c0c00b00600980319041001c16200900a198641c6c0c070801c07101c2d28a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 519397104 1250 519395854 519395861
    0x30f0318120f1a0a020403031d010e060708120f0411031c0f050f07030c0b0a06150e0607150516030e03040b13030606060507030e0d0c090209030307170733 68
    0x1034801c40e041c840c580b022002c42254118151359a80480d03a02007018820550404c4a024544005081100b04070580000081881c500810114028000030401c04100400d010545944070800c00c070071203280c80c0c4101c00e21110141200c3c00d4403034410140c0a01150b04010500891822501410032081c8070484401d5440811f540c00c10341c1085000c00202c0d07010b0b040400034100e414481d40e1800440100e90038a10504c180c040d041d4031082e45080420072100c50350707072405005100681041000c07014078070b0000d22079024025012300440c91000c403000308000035501c12480b0790600800050008440300c030440407103091031440b03420740e4010407041c23000c904458080c00d400000d0541201e5403585070350f6120700351011540b100300403850124103041090342040180302a40d01c03e840c941070412250315a074011060714865690083e500090111154500740101d074603250b04200c0070300003a514013001c008640e0101c4403d80b01c14a4201700d014040e04900340c411a5000300020151081d0b0031941020000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 519398354 1250 519397104 519397133
    0xb0a051305060708100e0f011a0f090d0c17060108011113031e0f1506050d050a0308180a030e03010506060c060c030606040f0608070e03010b0a090510080601030f031812 74
    0x5541c2c0d0170300000300204800c01c0e441c4110a5810410110f52400e55040c0124035150030540b0010428000c120807000d025040e100d58280c11101c010b41c031000c1c3d06140005a442d6000031905a00306401158600d0001800504235070a110080124510194035034002d4021802d41a00314025501c080002c90410941e030041845000b0305403101d4038807540c40317908542082c141180d2001d1400d41001501070984528402000d0079200d144810b88207540d0320380c0b2040c48803001801d00c5198800319403048002e81c0010199030000003210a03541d12814090003030141840114840d40c240b000081c51341c149202a12402c4042c070009101540700d100b11002142c000500d20740d00980c0c14400054840c0c1001c0200300100071340c0c1c94a100c0ba00b00000010704c268940c51480b40241c1c18400c1d050056141d00c241c5004580303842d08009110744400701c4014080b041548040050b11980b0000710900100390b0203200500e01c280c0300c40c1c425584c07251000c1358000b03c0380b040000310341c2c06054000210340c40c1d0140100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 519399604 1250 519398354 519398371
    0x536100513170f0a050a031b0f080307020a05070f0f090e0303070f0509060a09170109030206160e1512011a070803130501051005040c080603030f13030507030b0a051305060708 77
    0x180c900356002880c603041350740c182039400ea4410004901071580081082d0401c02c0003849910054040c0c1c0c0380d92119561007103008016210010005603000e20a109800c4503540c0001a15031150303903600011804d01d0a406116105c0056420000c2c460700d6600c2001070b065600000f450179aa5400c5082c0c0d06141084003500c207110081160849560341c0030010030702e031043c03a00c9041d0160b081c6415241d56005815090315940c0c03514101c0c0000c2500055980c0d07204a0146480402c04a01c01080342c002900704801c5800040340c0c1c000800044006002d052110a00400200c5c942e9940303c0d000c00001d45d140030444072020400100002c100d2440055038808402076140614103d16520a401c40c0c1d0111405125107800c0842030002d45440c3c01120b56048441c5406071860400c400021744074407443d414810384420010348100000e120760b104400031600603041c0d8940d1030740d03800c0602d11560b04481200c59a0328000008072105112a104500150443c00030001661222002c4e40c0e0303540c02500003c4d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 519400854 1250 519399604 519399613
    0x7120c0611071d010f060c02030a1205040503030705062d01090c0302070f060903120c0e0d0606081009030e01170f060a15030e0d02010c02030a053610051317 69
    0x2620a110104145500c0400d400400e9190305d01310045015410340d400080c200304a8824a0000d43c1d80051000b8803d90040a00a2001c60000f029561403007640d0000c0c0c0c040c00f0106d50002403000100c1c010b40708070010381840703090740b04a003290f10032480441014895125000010700102e500e0342e1010480d0165420010b03d000f00c0c1da00c0f503040d401c0c52080110313038907612520001f0406900420840501e0307440c400c00e100d400320102e030107020b10781031500c00d902504240041c1410300042d600537400400c05c0c075080ea100c0e41c3c0c2c001264805801c0006056020a1700003100310b016500c5000c040e201104442e5200c901500c58241c00e19101002401180e80113260803404502c240f100c0000010003a02601c2c00a40c1c81a4041814104000080028250391405404c40c400b544c0200c211103203401c1524156548a106800d4002c0d85150801c6000b00800c00c0300a154800641d050300030b101c20740440784041e089050342001c80d01d5200d41d100a04072660070310b408105d140c440d0040c0b004042a1101902c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 519402104 1250 519400854 519400859
    0x15060907030c0e0406080c10110a0204021c0203041a13080313020a1e060e0409020607021309050d0f020f0c15070303060302270106020705030a0f1a040308010807120c061107 76
    0x1d030503076415810049039500300513447c0311245002020090b00d0492820441d1a110b0004203241c2c6416011a002c0d00031600000d822500183d10349410341c1c030340ba401d44c0031500c034201820251520104500306c5403403442c0c807901242d007004a030030540001d5503000c481e607440d568034041d8610703070311004000032030f006980e00f0404107031404421440c814101d0501804650b007464030000801c4100201817843c0070702e02d0003e903100903031550000c58412070b80545801010307180900440d0003c00000c4000780040c002c2c441c4d02034081c0e50082000c03408920765030131900c01c0b00041c500c00b0b4072400c154a00c59841480e81d23402e16540c0f51810050409507000f8240000c200d42d07070340c0100e00000b0f202c1619450754011900001c04a40c126820a80540898802450381c5801c00020035560034150070050414039400e40c0704002c004d40003808100f802c0901e0500d042c60300706031034003400010080c010740c00e95010701000420022001415101a140c0003000c82d03c0141c54400c041c0c03651b4103903010005640c040d01801 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 519403354 1250 519402104 519402109
    0x8181e031606020915040806060120100506010806040c0e010e030307140309191208160f150507031a060c070e070e100306050f09181e15060907030c0e 66
    0x40581c40e801a4409a0380307045101c200301c43c400c10295440004003081c4424003d54500040740d40e8012030a0a180030401c0001c500008008202c0841c40003505c44c00b45042c0704840ca41d04024041c6500ba2219036094440300100003c0d00c9996124000103540041444060741c45011406000d042c064152450f08009403901c0740d000041e420750704140e03800003a0701405400c102e0300d4202090b0a203402011028140400402145502e1a01070103418000c42c10f48d002c17035400022100c045900a11104144280f440c0178040c603821102421030061070400014905400307802144c12042d620140c410720004083c00300200c40d040503005801c903108940d404514942e10130180c1d4015900d41d294003402e0350a8178204800a00c3c1c0405030010141031110411440c2c4495142d4807000404444003040ca9460384c0f1b541d5443c00c144490315456225440e101509290710000444240c1c9054040d20911040d414940820322402c4d2586508541c020000910141c0719a108000c02c055030315043c1c05100d0346900 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 519404604 1250 519403354 519403387
    0x51030f02031909030e0d0b0103120f0801060503060328030305060427150e0f0607210209040b03010203070c0c0807060e0d0f02060406091e150c0f1704030308181e03 72
    0x3401c686c107000b500014414002d001c0d69600062140d4030b003024851003041c00040290310180b040ed01401000300c04109556018848059010642c90001c1e087d203402030010019220b0100b402d030003003032401002c04c00030b09150040b00e8202941503010410b070510285d241120650070f00d000d5810701240309802d110b2803545c3c068198410301000081c907208100b184201e0614801909020620030070814a8200030031410004040036040000103844c2d00200c4003181c040e203580000c040d4507500c00020040219004240051958040ca0940078100e880d104901c0d074642c1e0900902c008180b0482c00c000b250316020200d00c0d01d00e417058400c41c010100585c04211103030040c0e0440d1000c592515401d000e0820340031500c2c108290080e0b2044003452800302640c103d0341c0c82840030003c00c0304410130301040c800c040e42140300040e03100c0714150030030f91342001508058120b400101d00044106002c9040303010315103c0e200f03070094200c1c041c00388024241c0c00c0c0b0130748441c9112440311070b020a0008040e001c1e0182c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 519405854 1250 519404604 519404629
    0x11b031e051b012009280617010806010b0a030e1608070902040302062a0106082a01140a090e24101209020a050d110f0a51030f02031909030e 62
    0x286804020341840c0001d428502049020341c255408c5500401c8410000074a103411070f010141d45580d1800703618030483c00380042185c07080d074501c50004840340c20305160343e40c00119040c002c141c80c540c1d91600719000c160300c21440040d50101c802d12800500007404404802c2d00b102d046268003840c03100351178060075580e980c0d0007068039822440c101002c402e1200044800424184003140c0403614260028045040805c254a002c0300c0c0030030301c2100705018250f140081c0a2440100d403a0b46402c61081c4c20102c030303021404401411302d01c041021820320603003442c1c5d048850b8031500c43c0400c400d003802004080c2d80394182d910a04241002409865030b03140e81d103081d40180210030314001d2410510040e08085406a40240c549880c2004071150004020b007024500d444c5400303d0010010748a410f51003041c80008908690790041c5034038080085031120b400c81d80d0349042c00528042911030381240070469400000b401d1400b54040c500d1503681c00912520711906050120800301801700b0410441c0301c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 519407104 1250 519405854 519405919
    0x3070c0b070318030201050d090c0512031308010c021c14040e15010e0d0605090a0804081b01081003110d0b16020106080c011b031e051b012009 63
    0xc1d45001d2552044034150003054040d03000026628640c002801d5114000401c8000c1c6c1e40c46ca000410482001000802420005c001d41d044a01c080042c81c0c4035070010082942d80d081d83c10000800c2c050602070341042e00350340c0d000760542e04a032402c620141c0582c04800b0f000c200c0201e00c2a00302c9101071b0060300140c80c0410101c00645444082c84007400000d101c0d807030510200c1ca860744516662001015149903002d500401d03141c542000444c54400354050040100ca0042800b0071499030008449150480360f5407041c4218a0000c01555911016502541d403142e403100f050020a00c5202a448d02e0f4502801c449501d03c09604d8043c000036080d611800d540340d0071800031805a509009843c0a00030003005001048001c0d0700180c07400d0040c80c40d1484100702c00c10a402450b000b41c0c00c510440c078450404804005807404010020b070300210900c806c1105040144811000522074551b6440e590011041c29941c04050b070201070304550302d0b4682c0300c9005000c0d00c4018100b010b19060f42944c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 519408354 1250 519407104 519407107
    0x2030a0c02010e010b06030a0213031208040506250302030415110a0215060a091104090c0f1d011d0609130605010905090408090103050a0b0d030e15070804050f010203070c0b 76
    0x2100300c0282074841c0745010031116030400304014040d0762a00700b1260000004d10340182d90384496030440a100c20329901c042c0000750030301d8140d010103070002c2d00030340315038401e6040d5066590b500c4159419180d90044c45024540019180720783c00740a503004540190045800c07245404444032090305544c900303c10714500040206500038842c5d010401d5403800c0c281c80303c54541500e80f00780440c8c0e41017070a00c21500015100e00d0002880c0c103a09080b20041c1c42d25000a020036031600300c02405001507030100c0000a284150f40c0540341521141140d00c0c030b0f01c140c1d41c480030030480301d807200c4e00d030480d0680007940000100306d01038056907002d034940280700581d40f02107890703450000050030319611644a50700800e1700f0b404002c0014403400440c0c10680003420001880c1d10b0b210b0720180241840500e00340c011002d2014403040c10b811441c100401d003002c0303d00842d002d0304c0e4001c61565001d142001020a00280300034046490040e0740c091201d03806204403800c00e12661911450780d0301540c80144150070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 519409604 1250 519408354 519408371
    0xb0a050927180607050a08040204020706060305030f04051509011209060b030d08090c010905150f07020405040f02040f0c090909050c030303010f1802190305150415091a10050309070902030a 83
    0x40a003d6030f42c1c880c3c85410810309000d051113014201900080000340304a034006111810005a40e024a01a503008011691641d80010070314040340c1c0603000d803512518980302c581c1c0c4100404030440301d45c1007040c1d5444d85020140034241c80078010412084450940f80c1004212640781040400340342880ca50f0707125154244403103618200340b0ba01c40f07403504010200c581841280c6030071b043c41d0f040502d81518243d45200c0403440039218014408029440307400c1500780420310150401d03120440d0f000b25030070408405030381070031800c43e995060303000c0c0400d05009041050591551084550074018001e4500300c0d80c00c0310000b400c5520076040710704000d84004080c407085140310040020046089403c61400325000101ea008009942480042580300c0c400a8203400d000790841d010f2080280c402d0203080b5200600032070074601da002e40d81120b0710304101000c50a00869502d184004e003d031101c0c410b6540076408403181e030300081c4207151a20440c9800251030405100861051800c80c0300090b0048 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 519410854 1250 519409604 519409651
    0x15050f1c20040b09010f0e040507080109030314060d230304030b04140f030c060a050901020d0f0c1715010516080d2027010c02030609010606090b0a050927 68
    0x1a40c0c07026441c0145003420050000c490b80481c4001a60007c000168050759240342861400503030344c10064441d403c201c105401c0581542226038442c041c0790700c0c85a00c0d80d07002d00740590781d9241c40c03000d000c10a10f001700d840981c907151030040643e2124805d90b45030a0b202e0315103190643c1c05490845030200020036070003070311005210086400141c1c0d40034518000d4041502961010050050f840907551240441d031041025411252030b0f602d500024000c25912004540042078041c04080c0400e0002030f0760002080c07500041841982d91070040342d210001c0c10011186908400d4452800c1450041ca40340451106405012060714044002c11542140c03202c0c40100603000039504c0f081c4006000140301300404049040b180b01c0403480c490001407403400121000281c03a080a5050f0090780140311007404190400c40603a080d03521403507219651849554864031601104200088042c0400c00d03140c50142d036424021405d0040511240d52120a0208505015546203240c0c0d4508038580c9980d2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 519412104 1250 519410854 519410861
    0x3603052506080112150902100215070f020316170c0c0103110f030f150a03030302040e100f030308041110020318030c0d0305070510050f010915050f1c2004 68
    0x41005241046207540340103100c0b000c4e071024140040802140d00003013a17403800e0950104903da074004142c8244043c0c40000039440b40c9809000c050303070458402c0040c40540c0900110600e1a600b03070300441c50a01485032200200038903103001c036412800d20f06041c915400d0348018081d012040c6001e0703d41110780a0014044410700704010306051020b202a0a46605510a81c0d60000d8411008849903a076110a0914109654045640310307902d02000700505615070b01600035100103020412464440c8041d0441c044064420345440222400013440003d02c155403a44e000b0b403240c80c0d03a4100440d2440015030300c10000001c4001a480410031f5003008882400d03020325400c059014001d41c40c0040080381d1071a06013880901446400034078035040040800041e20652075241040010b1305111200c1c0b12403c1c000c9c81000b0400b17080c00042203542d200d500c042c2040715001408141e0b02e4840301d003801200d03070f42c841241c001000700c4492400400c482d030501030818082074244035140c0c07050744e0411048 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 519413354 1250 519412104 519412109
    0x50c042c0f04031e0306030203030327070302060304081c0612061a0310090314070f0201080a0e060a0f0e0f160b030610031d0118060c36030525 63
    0x1c0925010900000c20340102d48a03112078010b582d40d0710711299614068014141c1580000c1d0540b00010401086451010404000d80d040050360032001090a181641d20801404080e512450800c0880d0028014000503c2e813440615004c061010300c0700740c900121085a4041c0403d03100d010149020010350340b050b406c411910700c8180304c0c0a02e840300130995541201c0c0424000a030b44032641e50605006120300906882048203a9507184140c1c604414030848100049000c240c1110105415110038091803c83c050300c1c40003060107a80e00b011400c081e03e001180040c0365a6192080807846c201404585001c128110091035030202c0c99a000e1040d11496011480e050014002e020466903a0107022075140d13110305c3d000c5645c1510701c03010100396000c4401800690700c1c0214070302075510ba0455004813103008030000c0003c0c002412040d52618015410008100c041800060f0100ca400901101c2c064041203001c441e2912a62a5864410001640100b0b064203240e80380d0303000c0191804001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 519414604 1250 519413354 519413371
    0x1b040603091e0c1403071e030204050601020303090a060b0609030f06011703070f06090c0b1603030f021218010e0d050423030304141507110306010e06010210050c042c 73
    0x8088041d9150811000000e0007251400c9461850314169550104000409070103241c42001954044560380300044c0c7c5a0301c003c0340140c1c20000025119800403094900c20003540d8090409a1616900e800041c0142020103a00806c2070060514540303040100081400c01c400c01010994141050540c0d81d001c82c010140965201304560800161417882c011406a072000006c11101721170300d0416061281d0360171403014804017141c0074820b803446102842c01c050194500304000705003003d41405038420040c201040f4030fa02c07008681b00c4842c2c03030a0754500c0c0c40714178000200303402030050031400c0c40c20b040035520014401080070300601040000817140000000400c806a0b031801000c65240d001d83e1013040e100d8081072a040700d06807910303100340c111140c50b00c0c003d59480d102460004050341c0d00c9030003140203104040001c288928000030b890b004010513001000203419025005018000092141c04080c0043c00001b4141100c0d200003904000700310030020301c0c01424420182c20b2113008000c0d29 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 519415854 1250 519414604 519414653
    0x30d111e03010807140f060a0c0b011a03060f030a0803070e0f04061508100e042022020d020c0105070e120d05090409020301201809041a1b04060309 65
    0x7114034000a084d07411176003507640d100701a0b2901c0e80000c06540ca84c541c11a00100c00160382d22802c5d51110900401c14807a0603240d0590341c8507408402e00c07a86c0020440d06400d41000820b86078603002c1c00d1400c0155005040b6841080242d507003460b642c00561300c100218030010048045d030f140a400c580b04040301610308000c0c280c640a00d01c0d030510600c20b051001c1c0800c100100c0c1c150002410ba48000d084880302c045400e0900d03103000c2c44e4101c011042e600341101004c942070003a25000a003125034186241d480211059802149402980f00e02c4d0408440d581c2045040b2000c4020301443d4440c0d800c0c0e40b101c00020707240c0028411001400f250114590b0494000041004e0f084000e07140f400f1000c0d240010b5800f180c2c4040b070300401c101e0700312060144140710179103001200e80300103007000d0031044c000d401c6440c491001c2c008800d03016180106515080059000001c3c01023038403662100d4541c4084202c400c1202c80380c002a841a0854070000e038440100e0810f10001c1c8030300c6071024040c0314031003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 519417104 1250 519415854 519415859
    0x203060a0b0f0a1b060504080d06090e0d18050d051c020f0a0b0a061809060c2a1b03080307090611030306010c032c040608030a080109020a02030d111e0301 68
    0x8900b284030307801d5100203100b0f4003041c04040ca064002e4030506181d018000304801c1c1020f00303041c40103800014414070524100480420324a050780207210f205040c0e64002e04c5810388010040c0e81c0c03400c500018044a41034044001202d5440c50400010f1900807000b9011a4440c61078440001d1042200e14042d540300ca424152200c1c400a04e802502e0707001201607540307441c0d404005000e4038043c0d06c600c036184101401c0784412111503001284c114403d00003040fa203071500d101a40c10303120042810205c800c02c6441c0f904100c4909600000403881840c0c0d00d01c8014069124021600a5400541c1c01201c01702c00c208101b034000340820090b2503c0e00f00840104680e5120075605e11000b010707941040804141102014007880106001c001d131040c10000303042c0b0804c68480c154561815040c030640c24208001500362010088446c48651035445074a903a0810740d0f610003035400000014114071003048021401000e91154007108040c4150860381d40b034681d1006a4481c0110100380c40480d001c0004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 519418354 1250 519417104 519417127
    0x1e0f18020a0b0a030207060501030b0915010612020f0904140106170c03040f1103240c09010903171210050f040b010e040f180b01170c0d080d0b0409060203060a0b 71
    0x9440403628550007459643e4281d88040340139014160008105a040200100c1048910045d0f5480340f51900c048940d1b201c0c2c020b000c0724001900384180004103052078680c3c100045182c000300071520035000701070302c2c06051074003080445505007103070114124804014088954000d10341d0004196402c4502c046041105036281d9034440500014030402040c40c5010400000310262040c004004003a28044103080d010180380312807108110407840246400256150200c40035208100700603074038034001d070b03041d44d89001c0c1c840c071800070a0710080403d0102d5910100c0f0b100140e889100a8440440940e150030240091784010301c4446100300d007000541d08040c4d90004290204980403034000c502210151848801041a1107410800c092004040e6080c010780c6a90305040f14403c1865120704c048034101035440f000c910f206036922600fa0f02c6c0750303404180c034a000b519000d02100b0000400e00340b9100054125a0101000c4525a40100c03c000c01441d20301d0312540141002c0d540700b40b03000b90f602c89 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 519419604 1250 519418354 519418369
    0x9150a241b021c0201110106060203031902070b04022e020304030c0e1303031508060a0c09240f0512040c030201030b01020a0317090c2101200d050a1e0f1802 69
    0x302d000d000c3c0201035407003568401d59040314007018050003000842d45501009440c1d0f03000b1070354069205800001c00e41403500503c02c5581c0c06411411508640e25280e0801c492005101c400c500c040b000c1280c102000700341c00c61203001000d5650000c540d610300d1850a8881307083d10303900400044400c0704c200000104040004004154146030010b00ca580c000f0183c915134920360403587c128440c0b8810080b14100076400603030701d94060340b180c8c07811540e070f00041c081d80c00e402d4140c46004860007000a40450003085a0079008005040c45402c00712000030049594004a070240c40106240d1810025541c252003107240010f070a10240c00c18041c2a180070f49803407010030b00a51911103030701c00110000024442551203a800900016440c0c0c560007012482d0b480948008807194681400d81510000c1c0f003150303589451545035501e044c038602030001d50080000821b90b42c06c0649461b0840b210b1b04030541000c4040b1803540c000503418052a0542048030b24151500c0d001c8800100112b0160380c0d0b041 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 519420854 1250 519419604 519419629
    0x806040b0610020c012a1a0604021908061324080303090304060c050106031707050c0604060e0904020109080d02100b0904171309021303031b0209150a241b02 69
    0x920702c80c243c07080f5446ea48030004842030403424810340030201d410044a002e03c440304002c88500319010352100402c2004a21071b40320048818203501c65100102d50040c110305070b00020041c404d10900328107100000039168251554082c880351602184c11942c01c40c4504409071120380c00135400e51078100d44c02603480c441c078001d40e01400f407560b40700c2013001403d4024502456100082c041e000080d850745540d0358100039400c03550b60049180c0c9200b50305110f4141e504a544640e21402c0001b47c40301844082c600190041c0d0400a143c0c502248012042144a428a82c1d03540140f2801c041d00d045102180c504051051240003c40c040c80040b03003880c1001d6071501c804100d10f550382c001000c2e076007901c4a015840040f040d070022501103110100c0c5d8103503c0850b4082e131035240341d01404895100868800071002580040201c0118090f90303150307003400d01082c1024140708419030700c486030810900c00c0300ca08050304003000c90b0001c1200e80d0041c5041c0104074014050f1880841580c001078401601c6c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 519422104 1250 519420854 519420857
    0x60c05030a1b3213080706021b0d141c0e041107170d090f0b0903031308090112090c0501020111131809020409110a1202210a08040806040b0610020c01 66
    0xc00c4010750343d0803021030881c2c51038411180c1e02c024131a40700030ba030842481060128094100c0005071180082844070442c2c2e25042032100d034605038030400c1002c20719880c056410502e69000015264070800070340d8000b10185a10494040524000404d8048030031b2a0f40c0c0034030700b04600140a58900e4007a5007a540d0b0000e11040707a1000c1c440e80000c54081c0e004112446403c0c494510f050009500c0502c56550044281e42c20540d100940c5c0303550b91106441c103809a005c510109004190f07003c0180038034040500d02001c40604031081142039555400043e01d03080c071842010032070740d070f024031036290554840a401400c00c0040c2d0981e0b201c810161160b0600d03415042402e2580c028607900080443d41d0041080110100c10f052403865840d17901c01060141703042e0078000c41c01c2d1918010031071030160b0040040b840a00c00540140407290f800000c001a40b0980107120005618035010304060f000c1c0200400c440d24003030070f0195550703102401d098007407003151000c2490301c0da01044410105200f03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 519423354 1250 519422104 519422147
    0x1c0b0f070507020a0321030501080a02190b0d060f050d08030a1a1215010b0c0c12010b0604180c050f070303330e060609180a0603060c05030a1b 63
    0x3518025030312072042140095212108900200401400c0710500100c080010042e04142c05820404d8044030428005c1c218643c2c03015440307500518101042c0d440100e2100344d00142c0c1942c4400da13441e1500850b211040042e1030340c03428041d003c80009124003c09080702c295901c2013041d12917117024800035104100d4a500d51106074031990480c581520384901c05402d034441d0140411205450b1701070074001001c40303070f48140006a641c04020030ba0707101c9141007001d405410710070030400041c0c03103401403149041c1d5250381400a403036407420090002001092242000500301501540c04c541e015000c0d002444824800d5000000301c81d01520303041d03a4542000a13424102c0d80d0f25014140c0803d4914126042e11003801c95003194541c0760b441101c0ad001c0c00c0c1d1049407210010800f8500417101495001604c90680c1848229510751484d00a01800c00005d0160b0700d9032540005c0e070f04070085240c0400c200205110503030b40701e446040281036001c043c4100c406400c40c401844407001c03250003240c0c00c02 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 519424460 1106 519423354 519423361
    0xe0a031e0207080c1212071a0a090803010e04081b0c01030e030f03040b0601110a030f0923090c0c190507170c010c030c060207030c021c0b0f 62
    0x6804041d05100760100103104805541c0c03c0e103004a441b50810f41c440980c2007100070506640610b4100ca83c086100840c80ca50210203800f0707540c41440c04244902080c0900706803410b403803441c803010000761202e04001c47d2a000c3c4e80004000d91b480c41c400d2081c0b4980019038120b0029003130b201031010401007482e40382c0341d00401822401b03800f010400140043c115840295000205050658031048440101460404c561000320f0200e44c038070011f2400c442e0401d12141c018209030341ca80749003030b2181c87c10484400307003030104500800d04003002c6001c0c14031110030345a1020a1100701d9280101d91101c0d01c000c0007a61409075014015105c2c041040518049012400320b14480242100c002d44001184c401c080c8490540411105003285000685180028400c25000b82c1d0351480c2182a4010800a111410b0403508146a8250708200182c180300010350b014400c0303011170703400d51b4 = true := by decide +kernel

theorem cover : BRFrame.Cov 519244604 519424460 := by
  have h0 := BRFrame.cov_init 519244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 519244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 519244604 ≤ n) (h2 : n < 519424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
