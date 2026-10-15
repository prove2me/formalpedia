-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3916
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:03:10.859124+00:00
-- url     : https://prove2.me/submissions/28251e81-2eec-49a1-98ce-75ba6f7effae

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 704136690 ≤ n < 704316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 704137940 1250 704136690 704136731
    0xc080c010f0f020f03270d0909060b03060105072a06082413020d0618050403020c0303090f0402030928061b0f03092f0f0316120807020307030312 64
    0x1d13203011250450315113000c4c0c3c2d0590a40c0e000e070440c090b00040c14030310000105014450f01c084003034607465061442c00d03196000b42c1b64654040700c1003003424410000a0303600a030489007072584c0680c020302d80400c0a4082001c100c0b803407030180000d8200220100d11680c2001d0114000c003602049541d48454501d00b0321030b0111140091504440c00e00340d008841103207034020342114150044089600f646520b004c0c030449242992200c101c03034507a401e1005060301071109180b490410b402071440c045201020510854641c2032042c0100ea00100084507044144a54601070114190000d800098282c1102c4188412881036070007034a404d903103094810110755000c5040100e52541312040c10b03c110182c00810f6564020742c0d10380c1000d01118082003c2085003400c2600c841404d90301c2103640820b114011220550650003170303002000140401c40ca00704000211303038401c203110052140d0b51030010b409010381500250180f1a81c4c60100070035030003190401c588001030308100805990724031003544022 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 704139190 1250 704137940 704137957
    0x31911060408040b2b1e0606020706180b0f04060f0903030c0b0405030c06040c150203070f170d0c030f0f14190e030325090b040909030c080c010f0f02 66
    0x1420002080b030504d00c64040c00c100d6420001640c5c110764031103800b9041e1000c0c4440c4160315581c0e00d18a100380e0070701000082c2291000081040794a040034070296495015000305000d126668000c48080321440503c40050541481030781d0304d540800c10b4414068000b80200b0000c1a0090804464548240b001d10100c940658a00d04444055141d030514150060002d60340380c00101300802004c0f10405c1124010742c81540007000441c44d1411940c964000100701200319002042204040790a5018096003e50030442406c0d070b000070a00b0b0540e051051404005001d0301340b0320030b500c010750558081000901290b40512411000c1420803040380c1440b0380c0c21071092078840c0030401080d000d14075806071a000344000241e03502e601e9096840c503041103c800c114802c0007072900c0c200140c0e104448081107000c0c00e010505d681420440c00c07190045029400c51140d0324000d49081c58400c580c040140368220922656481480d02101d000e020401d01c601000c07810301510300c802030342030300c01c444511 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 704140440 1250 704139190 704139203
    0x10213033801060f051321021e04050c040521340501030c120e011d061006030920010c0b0702011b0e030a2010020709050c03070e0607140319110604 65
    0x190802138070681c2141d50341d0400c14847e03d403182000040e01c403920a85035070041c0303d40c00e10050f0316502c1000b09488004288400302c2405005c1044503480d40f2010b0070000001007444944000751544a61070100640400c444d01022502c11400c805441c444284e200960790041102c00341d19000103400b40c402c145542c0f800a6070541c0c460800d00d01070351003104402900c0c800800c2110500c2540390580d411200356030f030240c105d40705014503da8800031080c0101041c0c03c041c4100040f81c1c0b10642207803013448031400206865079106481d680728042400302c0c69132005081e86607007402400240200f10f440250304040c0101c3c0d10768146540241050304032000000c004092070303207030b664400c1070050100c0a4808e2040c0514900708117545c1e04d443d08203110206a00400d0414509081141a41d60107801c59540c540100140f1640ca03500c1840700024003c1a150f065036a2078914100d903411545103203c8800e40004144c20310b0781c0d41040c21511050305680d950b180190880800306403600c0007928020b220 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 704141690 1250 704140440 704140477
    0x901050411011d040609020c060f010b030f0c0702131a1807030e010e01060603090c091104050609190e0106020d0503010f050f060f030702070512010213033801060f05 73
    0x350f00c590b00c0382c524002804802d50f00c0b54100e9020400345c400a07002500543c2d0040b4052100180400540354080740105100a00354904100c0e014140300250060000c141e03401c0014862008040865900c261b02400d0307048816044044540102444031141c1c9041c0105014101d50380b0785034400040d640100c1a880c0a5615440780030b44c01000101841c0c0499504d850b0b10030401d94082c41400010241610081400303003136450001482c540d2034100c0d0081c580380c03c250b104194400400c4c1c50a0b50419501e0743d9075080c107100020340b24203440c1004402c100035040c011a130100350011a60407a840c40d000c4483c8054040d005507510b020074001d080340841245010060b600d4a00c07040d8000d4100605240c1c9081e07481070704140f0b1503008075020b00241c0d00119040009040c006c04991000b00c10b04000c6051141c61000404180c1e698840503050800c0a03a01101064002e0020142e540042d808150340345820744240041c82002d10808010611071402e01d0001409901100c01505152201001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 704142940 1250 704141690 704141723
    0x9080318211b03010e0a0501020d14091b1503040c08011b05030f10050d051605010c02030d031e150905090607090611101107050c0f0d030c140d051209010504 69
    0x11071030080c8042e5403541d00e41450142d4980d0a018400c03185010710009a0359800307210b4031100340c81c0c0a03030980d1210035040040003414000800d404410381848082074007411000400500c0b9001c803403001d01ca4140c0d002007030100b04041c0807908002c9840c02002402000410a1441000e500701d41c00980440e00800020320011881c5100560011560030300016075503c0d1800301c0c03980340c40798004a0f0140d11114080c040e141c48408024020030b02442c00300c02404055011a4403089031640c604241a240c98802400c0a81080003806104580408120300002140711042c40b80c000d00c00c2000084c80c0201090307074800c000ca4001d01c5080d83c0e4513010350351071a00904070b800309540040402107000300404912001628026070709204218860261100c82a040560a280524510b1880384410310303072114041d180c111421000c181c040c2029a49004603007090b8426409805038403419000d201842c0c2841a000301c00303051441c1c0c0c000c090008607920806102d080b104107450180ca055001b004051 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 704144190 1250 704142940 704142973
    0x2190f080912120a1b020a21050f031003021c0204050a0615080c09130e061f1401090b03040c03260702280e093a0908031821 55
    0x1134001e41308501c00203442d090500402c2140c4007054080006801002010080c855040c20440300da0800050b44c6c41804c03040c0c2000f034080d200c1c41a01d0012604040000b81c08042c402c00090029900a40280100f484c010001040c0c40241b01c0f04070f105500d0702011440c0300120788101000d9500000006501c417805c644103503290720b801000e00700301010400c0882e0031922500c81000c110040008049480400000c056003800e034020080e082281512542c4100c4004d030744140d104842250402450069590300101d8142801d50810080c200d4000180020408440381c8142160302800300305e40c40528030b030b503e41a041403110440c40800400d2151030702505d001d540b901c0600244403100001903410a580607102d5072107034040790300a005c10080081c803080c140950884242030300301030314007010440e5280880d014040d008041c0c1007007201c2406403aa01034420300015000602c2281c1d102d80c1142040580c00504052003402003000280002c02103039201c8000d500c00a14202410300801101b600c41c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 704145440 1250 704144190 704144227
    0x14040306051314070609050d0b070e0607021f0f0203130303050307030b0d05062415210112020f040209011d060d020d14070804051c020102190f080912 66
    0x100d038080500a070b80d00028a42c504010300007100d0000351448a1400202401c4024250700c454011030b001c00c071200000c1c007855900c5600c0421810301403c0e440340c0b1804a092806982d0009420000d1100c541031031804461030040b60300c042d0340da03807204903241c420100e13140d000c0c0303003464101604903010070b1000900501c0615805441860300041022494002407901305518005540719040b000a100012400001c461003d2489080c051000c0e0400404075044203404006201c0b1544003003103000c0806c2155401c9154101d00c1c0361081181c0d612490512200f0301024400c1344124214050001c190805000380d500c0420305840c3c91090759402d0030006d0901404203451070340480104800c0103039584502c00380007413001c08180060303101d0aa0b001c0c02042000a4600d00a01420004010000c1d01c0010301d6084002008814008003c1411069000e409400340d42d41c540b00c0038814000380c40354422109044e000003a0303540c603196141d04920945940c418040c1107550b490401001c0784290b904001b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 704146690 1250 704145440 704145451
    0x1120b01050d020a11010c05160b06040e070617070c0b060d0f050607031a0303030408040b0a09081504030201051803030c090121021b0102190309020d15060f061404030605 75
    0x5918110b401c0c1d0340d140480c0c0c4214030304000710b40c50409607404001c0912400380002058240645010b03003100380d10840142e40312004081b010007070002104c07901e40b40c1280140100c0c03001200c1e0b00036101e100140c02803042404c0d001d10818640c0004180620561202002c02d80150920240e92260024802070b0020494143e452080c0360303d0290001724100304041c4140c90513580000e0003000c5004512071a528030710414440d920034000c0c0303c00b0640d428104c0c1c04807484040400c0d590f400800058030340d1030041e4005111030040c03040d0740903180c2440000318401c038402d074000c103c569070301d040381681c0b002c1e180c061109960040c80003070300c0c0c040079400500203010141051500c1064240b08049640310b030440701c61400c2e4001c1180400c0da5240b405070400750418000940c00c02c4203280d228280b02108107034890806844135103810641d11341d200d00c13101080d0032480c001d0b60303030030aa42d00c100545484e10860050a40c140300000c0c140e0720900d20078003d482060301c00b525180c5075448203006400c0c06440b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 704147940 1250 704146690 704146697
    0x41b1d0108070e031905070602160e010509190c0512090a0302150702030715063330051005010906050906030c0f03040c240c0f14010905010207120c0201120b01 70
    0x1000b4010500c000901c0c440c051069005187e0142401002030800c40d00d0368a440507182d5481e0280b004030301100100341520000d8030036190ba0f960b842e18000c682100d5045a80c0340d00d25001c0840c00281d80f04004011180c00700354148800d403038070501e06d40d540d01025006001a085100c400ba03500340720070452a0098180d20459003041c8050300e440300e2003101910ba45000c81c3d0b44000400150203030805d100e000c10580d500d207a81c680c0420094403001c0048000c08820030400c00e2010b0b440b07100221000412182d610191061224000702100c014403050340c1c4003180301d000702c030f000420f50704c90014203003500c506513201400c00211a050240d00d8101610081c101001480003144500222000d540b299000342440201c1501e81080d494080380b03160944d0411000070843d500b40d06070082d1a01c42d441d548002c0e1562030010301c0c200701c2d10340b806d114a805015400c0c2080881071060540160003001d00644503503c543c0840081034038020181500240400c60740500609845d5203a40030313003590382d010304 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 704149190 1250 704147940 704147953
    0x130905030d0e01050415050f01120303180f020f04110a110a050a050a0b0c09010f120e0d12050609060d140f120a020c092404020405041b1d0108070e03 66
    0x8141206640300402d0204403030303544004010a02040410b12450f100c0406d02c00c000364140044910300820050085e0804040030048520070540f0a500002c61902c00c1c0400c00006d44042c40c02507203200c1c0c455020781c400c440300082000e2600c6c02e0303c00c031901303081d41e862001d1800c040503100fa6045103070302c4200c00e058024014400042441444090070103032080014014204036460014141c500103400c1103007590b0140302c41d48803a40c104d21111a00c01050404050803451a00440d0143c41440c100c41e500b401659248042980c00c9040d89040c1170345107400b8066642c2d4001070220396102107402c2e03a80803507029040808540e41003909421504c018060720749543d01b40c1d01c498035010207500d030900020340006a103c00140d051005c500208821100b00b581c42c00d06002c480c802601d8402c3c0c5001e89034044204000907500ca50403280105030240003808031228a14079181d0064400100d0380220314003520810511810010109010f001611901134a859a003011a1840700f0340500582501c01c42 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 704150440 1250 704149190 704149207
    0x110c060a060e0a09110604030305030f150d1103010e120a1b0206070809030a0c0305060a051302010c02100e0901031209060807080a05070908030304140f0c01080c0c07120f020f0a0513090503 83
    0x86d009001444c02921001d0b40e905200000303020f029001401100d21111100c0601034940e901342c142149242c1283d00b485070f00c51910700007030040440000e01d03d5a44940021900300f034071183c0140c00c4810326a100c1d0240c03a040f039003034024a07100300b1000940c0b003503081002600150030f5030050318002901030308885000700d00f41d0326410340d1440380d00183c0701940304104020800e030b41805a254003060340d0550041e507210030313400078000e0052000024400c06c0d0005424800030b10485c0794003d102801048c520495a49052820000100102d01000211695000b00c7d0301800f03502c03504c1c056105503441141c00e580f8181050010107002c1c200c0d00412458050003d41c0d56000c20107903018a004031100b04040d403140c07500300d103410003040416016400c01524a00c1903a04082e601ea400108440c0550380e07004080841400c0171031a801c01c00c80c0241000e0302070b0501c40300d504c01c000380610a41d48000100c1d40b803020001d01000f81e00c075460340108440c0e0380343c2c446090f9410214035148610304a81c10042030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 704151690 1250 704150440 704150449
    0x70302150403020303040c052d01120c0c02040f0b0d06021e0703050d0c1e0309050a0210050301031104060b0a0302070c090f0905011a0102070e0910110c060a060e0a0911 74
    0x950701900164000320601050001070408203004020881e203803001f4007004034002c4640041058103001d0f0582154503c1001d902600d100041c01d00303022001c01100990300e0340502820100170302640100e10b884034012112401d88904003520900820501c0d0050096a0b44806540290f00c0d03170f548a00c071400411065880c40303001d0641c0610035120561602e0074110b07902d0843e41c440003074408100c48040c030100304001415103032032018807a00c0e011400c61018204285404549480290002138400254480300d500c000a941a28800c2100d06654035811003044259138507401480d40c40c14041094082c0f46020394018a4480d00c10002a0121940d40b40740000711181084080d000607200e05645e42000000e00c15020f2101e40022282036800700e020000f560755125000c0d02102c00c1444001c600e008108000300d400c1e803c8000018401040b00050b140003d030050501c4031818420341c0d0100f4550200c1e0300481d4180c1c2c0e100c841c5a40c0696410b9840d1001c0d20300080c094412501c901c2c01000540c68 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 704152940 1250 704151690 704151733
    0xa051309050610030b06030a18080a171b0301151b0c090c02031602060a02030403050d030603061103090a120917151e04080a0e0618090610090506070302 67
    0x8008100081d14508007040c844848018601d01e000c051501500550b0760340c038002034a8004540d00b000240c4443c1004400a44001810002d8803a52010071003485140d4002c400c140c0c1c2894805044e409a00d0f0f07808942c4403060102e42015031000244014031180000980c0b075010501d4a2400403c040030220010322040408070b01a030310038082c2c079000e00c10010140104004a0103e20046141000c40b42e40d141842e04403010003071080d00300094040e1500c1c800c10503600550b41050036500c964102c8680a001811180b004440c10b90900d8010252411102c040d030384100e11500260901d08003a6940306902c81401c070810041c0805050042500035140c20b070100708003200401052003c1c1c0d103d400c9840808003c0035510110021108590141468241a80c0041e84400e8032500e4040f000c40544e40c9400e0a40d40b5500b1401c081070302e030310003484500c458030361103c150303007140482d112841444149900c0502000c00700384030410401450404000501c1c0140c041d1042d10f0325501b090542a9a040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 704154190 1250 704152940 704152949
    0x6070c06082e032a21020a0b0315090601051c111308010f050c1603030b09090610090c020304030b060a17030c0705030304050a0501030903110105090d030e07030b0c0a0513 75
    0xc0750b818041c010441024101290780070710303290000802605441c400c03000d010324098407010040020251501c42030711995040000c1d8003c0540c81c0072600c56054500d990401c9611524150200b40d4000a600f030965406010340c0d41a90385d0b40ca4440c50f04801f10001c010000285191170f69040c805004248980180580c4e5003a00030501e04a072070031a04a00395004116000f45043c030742410b00c80000d00301c00494034000c40b0341c1010090703d40c0381c1c241034000380b200e104403a403c001f22100700100c100000c1000b0b407041c001c07195203091064490f242042214003407000344000d640204000d001048061031003c0e804132004015842e0961154000705004144407605500b0768404550b002c1d18400510058001e00415401182805d192200096000e01248143c5040c1a0384600d14010b04d44140030ba0510181900d000f0300450414125860340c910740c04020200207407400c4013110076040089207107000c40350030400803031a90319090f1000d25543e003d017920209201c3d080141402030402800000000c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 704155440 1250 704154190 704154271
    0x20010c021e1c03110712141002070303020c0d0c0b0a02180d030306030c0e0c1206030f010905031e040e0c030c12091f2c0a0c080c040b06070c0608 64
    0x2e801d030325000c3c0c40782d492407011a1058000100074030011810901420617642c0240d1043c03c60141280c07a13138140700701c04c0c81c250f90450000480343e091540503001440406034610440700e03081c0d800c03041219251002580200301c02c640340046200c00c4d2050f000380181c0c0080510f41141505000300003541841e0210080340440e849007410800c2c0140034640074000e00c10a1403600540c501801d0b100c0c43e51007003d80700a0a10055800700f5400c1d01c080019050409a21000b080220344a0408035030f03030340014400b030024200c1d41c1204024105d1520a6408849103544001ca051315603407403407030103038000601900f0043d100340604118056203890070360003070001901070003040b08088007480e042c003400030314a501d150615000b0214044082c4800714500f056605d090030050000c1c8820b4181b082190018061103040302c000304100401180b103030300001086408000071200748040c4000b50060750070180208a00701d0b820001c180c010b9408a500440e000506001d1442815441e0744941040c415480312 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 704156690 1250 704155440 704155489
    0x8190510051522030b0c0f120a090b090a060e0118020607050a020603130309091107170405120124051008060d020a060302180103200c0708030301080a20010c021e 71
    0xb40500b44181740d4220105a413528a00350703504180c8400385c42200c40300c00204403d000042d6091260390300403401c05502c160703400c080e410503000c041c0d902c0b05106800d0b1010b80c40c0981e18035042c00305100d403030040c0001040b50820907240d5000c1103541d412482c0203949600908400e84c0042e541d202c011407243c4203e5000c00c400344107504000304070f02c0c8240c112804240c5884043c1071510130705c0c000d0b81e15190b400010901280c0707000840208a01890340050b406c0040d00010034541d0606400c0381c1c0581100024065080350b102a2004120a191049680004e5030304078480301580310324a40c1ea1b1004010f00810b440c01d41581c007040781a41030ba44060b0000ba0701048002034880310400040d40e030b031402d1030706112608840446202050222100c12032052000401303161001007800105c00610254094940703d6030f5a421850316504000400c136901d4040015100d040aa6080412800c14040c0c0d620703e41d6022540c280180134968900c220404000b8800c1c140c0c0c0c9540310030a651740c8550f0b402c0c6d80c149 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 704157940 1250 704156690 704156693
    0x90c04020f04090501080712240e010212090c0603160507020303070807060f06080607050d1418070803040f060806041b020d0e04050f060415030c060819051005152203 73
    0x1115010380000540740c11107501004000c0c00c3c0c0d480d00740d24a402c051001031204c410089c4c0132450001e030b10201450380c10049141045041036001e054441403074101c6188540c1c0b100403103915440c0b8043c4199100906001145648205070100c07a025000c50400919005854001a1845d00141d00c101c51441c40090a50304204e1203000b40b00e0b01794440c803000d02c6514100500c0540340c0c140241010100400810444000401d2303821501c03004141185201c064140b000c0c94035940030741e4130b030703042041e200c0d00707030006110140001280c00f1a041c0e080b035400b1306424842d007103940240181c46641d2040e1244004146091a21401090300106800402402581143c044c0817404600c070001d200d18078207400c00002c9c03000d6180165220508660010f1000400600c0010b4269a070700301804800b0650004600507401000950007990103401d0031440105803185101a10000c039900e41042410a00c02c02c564100480b103a060f50040944480c2401301c1030030450030300c46d480d04c254040340c48810310800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 704159190 1250 704157940 704157959
    0x203130813030b09012a120c0504051903020109170705010825080a180b0406051e09030405010e0604060c12050c030d0510060f021b0a030b010b030a0c08011805090c04020f04 76
    0xa0300c60488000c018218034013020702509842c01c1c1789400c8401929000e544123010706c9001220b002e01402032044514502602501c0c2520380140012400702d840c41e000811500c03007140740d02c2504410000201005030401004407400700c8040c24406d050244044042d2203000400d03507140000040d81d450383c0851030865a00c03001d81c0d04e29418000035440c0440d00d0b001050070b500d00a50700940103d07000c280d0303031a407040d002080c2c201415039041c064030800900074480e0001c0010822644242d8420030352000c44010402d03280304034402c0c3d9011070f03034024a590008080c0101003c81c22400d0906a06050b10300c030350a03083d9030004c2c45128400d69200c2c02c00800091040ca454003502c3c00f071074a4440010003c00c01380d543d1403800506003100310054418a550755554241101a40c0d100b002c1e0456561b6441000c4c0300d80d003082e100c0510a40c2041e076000450f621a111603070407201c00c000341100d215012340300a001494060315942d040e00800f054031500d51039a000502003030310005106561140f5001100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 704160440 1250 704159190 704159231
    0xe0d1101171b030c1603050408061e2202060408070e0a050103051e070317040e0f07200109330501080304090c020307120905130203130813030b0901 65
    0x105984584092041007040e4490200c2e80900700340040e65240c0341c132003015910b40548440d45540440002030384040652100107081102d0b0b0756030407105503031510114440d9041148200c08070706001c810000710003030415104800b10110349849102c0b0186182c001c200207501a03080403005500c4000e0030400031014048041c0e0005414504118035410750355216200c041c50342c0c2020070641404e002c0c00e071070740d002d11400c0c00440e4802c0209803078183e140300c0b608460b0030078851803180012000001e000102e111f00558403401c0c490759040881d00c040b448141a16845c883c00110030741d6140501c0002800c1f10641841c001d00c0a024a215002001050041c103070b0180d000380e00160a00300104140040002540d0994030383c1d0f000460b40308405003049141d8040d4041c041c0c07941410304901102540c2060703103070098034000d4606000b60000306814805038401038580150030040e0011007004591928060070396000041488044943d40c0e8691406080041c1c0300c950850755a01000c42c51684c0c4103084 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 704161690 1250 704160440 704160467
    0x5070609020112060929090402041e050f180a05070605030711070e06030d09080c0f1215190207170705010204030f0303140a0504111912030e03060609060a090c0e0d1101 74
    0x940c1e409441c1b440465440c03140030700005d0042c0d4641d4100103204030034401084c84803208600c100058a440ca80b8901d54001c20389154512503200d201030038204a01058601c4496044402084550310703200049034941d1000380468104174417188014805982404040010980d40c084c07203403207080440405d030a00421243c1d10041c0f01c00454100203080020803001401d1600b19002201c0180c1c4401140b130401c0301401d200c1c800d0199401b14035071244118045805070600c0000e003404482011401000c0b40304682020f840c41c10215250a44200c80d0b4005005451080d4009402c050b07403984c0c0c02031840c0710380e40210b01194a42848035030074021040001c3e40440c136407000b4400c0741040d17102e01c0f0392100c54009890042e06011445001c520b080e0a45100030218084111041c1135a03080c02070008110b5400544280a04004200e003071500e20681401040c00170082d03c59189025a1b18000f062481c8030102071203800c00d50030010751380b071101007203e05005410103804503240741d000602400c05c0d10307034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 704162940 1250 704161690 704161751
    0x13030f1109011505090d0209071806080903090d050a08040b04030317010b07151b120509030901090b0d090b0a06030203011b0f030902220618050106050706090201120609 74
    0x10480f5036840303d200a034650303050800907900c090201c0400c1c01108407000294211a40b0810312092940c40380c100c12240310120706104115459000440d40c031242500c09065a504c18044074039035203042e20711418020712420480d01c041c403a960368410190003030385c000c4c1d09100d40484c0800c01d042e0081c001d9200d190118042d480c4c558100787e800186401000009408520741034a1a030210b0000c0d4030107034540d840300828032000c40c841500140700d11146e9144c001814200740104989410000c02e84940c1c240503116802002c6c28100903088035001043c084410f252180304000105560b41301c00c9020704443d82000c02c280f800c600606003554545c040c1030f001e001da02c1c01da40120300d07441a0403102241584c600825032015a000280b841400003203440d000e4207012060262500e03859000500322050b004641c02081d804450610444200744203840c0407650402800c0005501070b400b101031300d441410300c142c05140c0f110600003210020f030032030380d0429524480ba000c2d81c10a624002e120600515 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 704164190 1250 704162940 704162959
    0x70801090e030f0306010c020405010807080d02062e0f06050304120203190e0f030601090207140a053a110c030106060c170403150c030606050c0307030e030313030f11 73
    0x1c40c90399a44940c0300f00000010b0007001040c0640e10074452081003640007003091029586030418181c841c0ea01344100c1c42580320310f07a81c1504981c008182d40c1c3c40740034000000780090356100c0000600e020f07600e81e6010103885800b4041880c810904040307015001c0c0c3c1c0d0f203050b1a45450b20340205004800394207101554824004030006a034400c2520075040c003030b46005000c8211500103c3c0140d03500c09840d5034180941c0c40081401d503141d50145c90048e000b0f00c0b40314134104c1c0d0920f0b02d940344c0c501520f0180c42500032528001030049610056040c2580c000000000c0441c62907003d80d000c4400e4126600080e02c20790240d02007001000602e090031001c50003040941d141001c0581280340505004040b1409182c2a661500c55241510011a04149160a81114035495000401682d140840030901c0e00d48040f4800d0301c84e900341c58a82c07030640000c0d0b240c486d05480540d03655051440f801c0e0305120400c45160690441c6410500851003185011074030402440c2910080808c560701900800c03022 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 704165440 1250 704164190 704164211
    0x60c070b070c0507050d05010203040215250510050f07080a02040609030320070308040f06020d0807080a09021009030b160903021c06020f030609090a0507170a02030f0607080109 78
    0x24940d64005405061992544800b0300c2c090b41081c056910842e804449001510144241900214855407089035140c4241e622446007005500880300c01c6021200c0d00180880710080500c2d100e0707221405102105c030401d6880640300207403403003150b014100403064400c1c00321040d0485401602705044140660901c2e0814000800c00e00445c0f00182c1004294081d86650380040c1807070b4a1200c5801064441c0980c5904003031510382d0262290810340d0720a4000007035000c0c804101000c154600350355401c41c03901c8081d41282c402e100501200181680e0307200702001a61180031801c400c940c40d403280d000880c51030911003154040240240f40c45030000c801c00c46103a0f44005240207036a41140e080c400c100d0b07038004003506078070842401050709100040300e0212400d031002440c414070b4203c40c0c1180691b100d170502c43c0c0310b82d2507450081c0150700c188001c0c0600f403410a004801944040300b10782c420440d40e000a0320703007444107202103155003208042c8036000f94821800ba0251905807014440c06081 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 704166690 1250 704165440 704165453
    0x80403021e091f150f09080d17090f0a15060501110d050715020d020418090f1205160f020102010615300c090509060f0607020d0204091e05060c07 64
    0x40c034000c511109590114040d090409102c005040094890610b542d0b4511001d0560000022141d003c03072006d180024520400051030030a050460b51a0b2041521540c20014020005028282c01c0d0040c0302064400006c10000b90300c05030f01034400c4440b281d412540307480c00c64619804c5030381005081041241c0a40e40020030b401e200110b49821a501c035824240702168040c0e0102030451b44e0b000040303d0180c488035030081c00035114107400200d0400c0c14106e100003100e51122000b40101ca43c1a040c40100303401003083e01d01407034a414440e140c008007031142c95000c92558800c46048038600798500039964248102c2c009401125540108035207000c20280120000e4076204824a1620f0303500e4208240807400c0040d112440a8244440200108068407690075805054041c00304000000e04510f0a1010ba2050003000303030002c0d1800110b03400b803042d80d001e09101070340c005868600c42000140c10f01c1d240001c0d0951100c6003644500c0301d1800c80d00740500a09840402001401024042101d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 704167940 1250 704166690 704166709
    0x13091803080402190e130b0717062b0b01081207170c0c0d21030605060901080c090916030c0e0105090f0f0301020a030e160f121a04080403021e 63
    0xc04680003480300001d02400d13600283c142d0441c100c009a01c00510080c4040c2d0003d001c1802d1140c04802e4256580301e80c100c03410840040d4548940d1003640205030f0500308401e60a203d05c01c4500a191a81c110f589111400404080119503190000004111a410620803990107515800300c080c60009584ca4032421440c0200a404610f200000ea4450003402040201d02018020703100381d500c26440c1c00c00107440344090a104803c1900c0c0e40994800718801d00c98182500d1000b060b140c02c140b0400011511600001c26642d0118801c02401d41a5900c03c80040c1c841c051a00100c148407801c001c00405030b4603090040e4040c07050700a00080d00b0381c1c004003510400c0d0302c240c0d80c03529042c03240b500103a113140da07128440d5015440014400100755158019a02016800040322015103c0282c10944014a446101c81d10380c9210001d0021000c100b1a450001d80104080c0b64401103501c2c008411050a450444400800040800071030800180108ae1038402c0114038400c4c500a401040e0320a4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 704169190 1250 704167940 704167943
    0x20c030d05090118080114090c01020105010b030c0a05040f0803190201020f040306020f1b0706032007110607150c0e1801060f03090b10030203061b090f06070503130918030804 77
    0x801c40c21111220400900c0785002841c10100030703c11000a922540187e14059800e0401401544800c45055005000d42412076200300c900524540d00c540c0350b604035400c20490003080040c20000003800048501c2a03001600007513000d507a84040c102c030b103481e080c02c00b1340410056900501070641d034110020140ea003244d41282c0301694406e1503440c00c903a5031240000c40d19440188072032240343d99100040041c00d441158804010610320382074419000a4090b80d091003c00c0100510000100c22582c0c0d420b000d400035020034244041652104c83c590031039000e00500a90b180344035441c4607070088080458840642e10090403c8500d20f00c5801c0d003c050248506214007466888ac01900c83c3d4066103050b60410311040290400001d125458902e0380f2003a4404e2007a103003c941401000d031000040c034109200c000740340c840141c0c148a41110315101c503941c000e10174015000450024402801c60850f9031004000b41810500341c2000c864000800d0b8000d030a80c5c801042c002030300128800c0c0c200703 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 704170440 1250 704169190 704169197
    0x8010c08010b22090f050610050412080a031803031a121e070f031103060a0b010503070f1e0e03011d03070b101a03070807050a17060111010219020c030d050901 70
    0x60740f14004891820079941c00301d892145844410000a049944400d01540d401c407651201030072019002c540350300803401042d00600c41340c04050b0010740098020803220051341004100c00340e9040b000c00780c0c0042d844003940441e440344410110001ca003c00440014001c0f80d1950840c1500c01d0030b9552052090b03c100707146902c1e1021022090310070007115006188058094a049460785803e6260441001800303000740b0403c808149c8501c01d034010702606941c103035034903400c44d926080200e0f40c0c1d0010000c44018052000c1e65110030400078040034a182e0380d9902d624034034400c0d01b4145800c64104004080c0c803600c0304034246003264808011154030079000381c3c40b01b10603100c05410141c1c0094036440080807040700514655100b020b100654412045a21000c1580d99074900a641c9482210480c0c000101d0b110000c80504000d44511508114185418080803c8241520742240d0201c100610160704142501540c240e0410404c600d0300790a80141c4000c00510790064407a006218119050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 704171690 1250 704170440 704170477
    0x61d04060609170c060318060115270302030a060506090907030302031e0f0c01150b2d0702040c0908070b0c031b0a050a060501060306360609110408010c08010b 70
    0x203d0420450042c0240200000d54a041440c46002175811904141909000355800040c20319007a00d02d8401640898950312b4000c94440c031020015481c00d00c40c003521210558007c8007689040000c456014070a01b4005000c0c02c145041103d0340c50300800290807903008a1003032000030350100960340c1c1317600d010840e10f071032510300021896a400740c901c410b0384500c3c2c0405c081d0740c2c900341501300c45070303002a031885820041c0e15040240228800ea00180360030003d148180d01c621488442081d00326094454842e0134110242e0008007a283c42125200c001808494140035240c404d105200081c00356901091a240520f02011744038003844068019070702134048a200c0ca02ea0a029070340c2565030000907944c0c0c1039454600000140402c1c051440007a140150101e520351074803004841540001100003009444400301c1070004401644000241e621098009220b450718004c40801d121210b404a807140e0030006c1007400c440b03040b1410010880e0241c0101726400340d101c01c0340c0d45090451420101c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 704172940 1250 704171690 704171729
    0x70f030e0a02060c06011706042607080711031c08150621011503061d0a110706021e070f03080c0f040e07020d030b0310050a1104061d04060609 63
    0x41010300769029400810004d0098900c00000c1400d5060340c42c8503201303040179100d04c03804542c0c6150031140241203080102031304090b1042c40c404d64040e101448101480c1c85103e9450580d85e400504040340e1020710007503455234a1038140b206e10440065200524846920014020000500540b090310140200c810722841e60300c4507801c4900c3c61507000d145501c2000021180310113003e0900c1100e900d040f0f0b00184c5407009200340a0181103031040400c1d414103420305d43e102c40682e0b402a11049296a0715515004982c10007405044c4141c06003c0040e02c035140244145500c140c00d4050100c1c592041040400140540500d0401c264240c608800d26903a000c0141a2921424120381c262603400b107000952022a560154881c8445500f80d070807000001005505540100d82d0fa01c0d495005140c8005118803150720656010116001c08100e40100000d09070b03480e031041d0020300020700c92080100000b9001c48084003000400e49040100b10707d002d40040c800c0a16000f00f603070002c401e000c44d62 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 704174190 1250 704172940 704172943
    0x2030a090b0913020a0809070e100e07120c020f1b03070308071407030606150201110f0d0615020703031b0c090e03270406060908030a181a1809070f030e 67
    0x44281c2d811804640ea5107a61401511591040710045550300c5400f0b004502740305d036440700d2130194140000001055091402d54610018020b2141c0100000c078000c1c0c012600f554011016625a203401030070201003918441c604001e85142188910710090a28002e030703480c001440f504072600290318a0300c60665140c1104400401100d20365035100f401d00220502032280d01080c01c54017903285d25440030301c2e00402a803c1e605070001e800c1c1541c005100c1d40d41540c910600800300320305031030400104e5544645141070184401599100140d004450502c00c141e0009a8403989003001c070f119110a901540c0c4426030502c40b070194a00c1c80f5202c001c02540c1150410903a0000341c4a48001109900180f000301b00d580304400d20a84514109040007442a02825031402036402580140d840c00300ea050080d40d90f25100c1c00e0611100c86901800a0410740440b0018130060081c00029660181610b118404000049040b4030898010040c05801a0031035800421010642004115021401c80c500e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 704175440 1250 704174190 704174209
    0x6180507090e04060515010e0f10050c0a120305090a08030601180b280306050901050910031e0213020909190f0e030c071d040605150a1d060102030a090b09 68
    0x20042d00103007061104124103038001620170000c1c44d1911043c485800011180c2d25030325124150400040b0721070320780d13a080c02800000d1034027450030b14528080149030318602d05012008152062204a080060b00581c103014940d0400400c1000788640b88040d110f08007103210190242e41403094200c0c000390008142000310000340021180d1079128400301503106500f020755604c1c030380901d5014840c8c1d1007403402841036030b064400180c50003445030300744400c4c05032003180501000c00d40c508100c40040040c1310031071503c2c0303030214a0b1400c041d00b400b1351041c8a03a03400c0e508072881083e40103000748122604c840448a500640d0340c2000d070001d02c00c808171200149550305000f9038003824000603903d01440007006162401d13141e8202d40d040c0390f03551000d516125880490031800700c4504085000310761590000c580158484c1100d9841424102c00a80c100000e51310041c820b184854040c003244890095141e4001801e0015518241704440010020b015501031141000008903440f00c603034940c2580b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 704176690 1250 704175440 704175449
    0x10602031c1d010209040b0a290d02160b1003080904020304030c02032508010504081e0c0105130302010e060f07051c15080f120712021c1d040618050709 67
    0x11558142102c0d40e264042d50210034554040c40c1804e2003043c8034141101070b10111240c000c917560b1a14552202d40302556401010294034010900c591001d40415200800f082290500701c42c0d0b50784886c0c50502d061200050020902c102c0c140d00800101d0b04a40807036892490807200140c3e01c1e5207629007a1103000c2100d1020b03402d481764140c0405040041284560305c1e40382c011802200c16500c0c0240e9081c0c490460380108a00ca00388030b0807242c1d040040b10403e40408007281982012181c040290031510200d4040d41c907040d01d10818400c1c9602071140d082070f90f408c0d6000d00b02506e000f084d070070481d01c40078059004002d00003405c1c19548850348410345440401c190b0922005105004202e0000094082d4100900640701c1c1d56045000010313080c0000c815641e845410183c3c41d4541c075a00d074810303000c80c1e02580190031030366060210074031403441021800e40311240ca00304d44201c890402201c0502c0240298503144081c080380b59848102d120140b440400071402d95200c800032152401203602 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 704177940 1250 704176690 704176721
    0x1207020f01111c060b040504150b2a19031b051b0a0f0807030b040809040e0d030e010b010206130615081f0203130f02120a03050c07060206010602031c 66
    0x4400610000000040c60030003c0034042c03010140c0841c846208482e2a0305c11040060800c02c002c01150030141c00201c000d4151440581c6081c3e1380d03006aa0300c40c2d228880d00d1032002d45154518812000380141d11705180000b0006029074040c084c07000381406024140642400441d0000d150b118030303500850451343d07622500307445440d040900343c0e4107011140508a44a28052200410009146a0143c04507071010b4010417019196466a0350003a002138411b803070b19801004088801e0703c95000c0c2c05109842c4900030705142503071f0300004044446d002501c336003907410014040d101d40c0c0e0014002d60410365103500343e0740d510058540305000303200b007082e82d02d240b62300114001890400403d00c8003030b5181070140f6040c07500d022080b40049100448000400c0c108102c140c0c40401c1c20421080e02c0740340301800c1145050001ea520510f0318101c92801c0340004c60000e40c10015201c14055000280b07003c0c0010b21255040600c00f94990007100b203c034071410030030b024035810502641c0144001251180 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 704179190 1250 704177940 704177951
    0x5060402130602070f0501021218041d0a06060b0a090b160609080406090b030115050d151211040b030309060307031e0f0c111c090302191a09061207020f01 68
    0x210182d102c0d4000c5c4110b0054400145d00020079500100b0b01694142000c1c0c580b034500705c1911060540d05103034004c8181c01c1655509004034180740b0500801006c05c46038014184c00c14945403140544005401001d000720f810701c49940c10310340040400d802d8800b200d8409484000660458040e0400c1e0038003c0c0940f07007014802010301c071824005009862540d5205c1021a07115240301006100070b224500c0780718440b410710314195119401804d14004540b001107815401e46a440710024407a821070f50110060385181002c202c040381000d040904141d4090022114501c0000d882c1e0090f10205402004000002911148a503101c207141c0c040c00c2000c06031036807801c040311005040114400142e03a10f0080194020f902039002207150409203002483d20011a4003880d5110300055030300c009002d900c6002000680c4e44003044042030052514501501d4a070420390b83c0d00480c040c190600b0038408208103041c0c1d0f02e400e0122050306150080d01c02e4151600c1608925144401814460652a00703 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 704180440 1250 704179190 704179199
    0x40f0c08011505040f030f051c0905121f0b061e0909090615010f02010213080307060b0913080a050d60050a15140f09040506040213 58
    0x1541981a5400e42e0895040d44101201c150f84520550244807080c608088007000010220145561510301c82c0080e2a000090407020101016044640d0170200d0a007074400c1c4841d042043e0000c40c80014000149035038603900600c0300c61f019092000410480d16000c506040e615007404440c00280080e025040d000110301c071030201500070400440c030420751440480c000b5080010300d9405810307442d0301c020700082c0203401500e102c940c00d01418155502030008019640c11314800500922410014603038bd4075003481c0a008032035100d04004d100368103a0061000f074850403030341e01c2006544520840e139034804140307003034031540501c82030740005034108540e096064012a00c000002d414008080402d2018030800410304c80c3e0210a00c82c0041800342c555071280c50510100040e8000c100320140c2040e200c402003a064001500312a40c41c030f00d03541050300442e81c040e4030b450201d010011079038188038100c2011a443d2190005d202d1080ea1103a011a00f00e0792541e045800c0b200125030002c6606996 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 704181690 1250 704180440 704180447
    0x70632130510090e0c0705030a0c021c0b040218010e150a05130f110a1b060914032101120b0405100f0e100c020601060c050f0703140d0c03021b040f0c 66
    0xa03000c4d45480c2100708020903c4030340003401b0380703010381e0b401005181000e415020071542084603103020f990200c02c0000e1140c1010705d04c0020304850740035012220b650f01d05070040c8000d11220a8040d0b90000080c40100503904c42000c143d80c0100c4c040f020458504884000140740300312a801141e4811105481c5040544045d440460300350078180090080e41c08582520100380209020305003c101112815808004595861004240314501c0051417030303420340301c0d0280000c11040034001c0d5400022a0803490500403c2c0300c0d02c0304249101c0360413641c1410111400b543c880800100b0450021780840d04001051290707030b41c01040003208020a202e101019805003e111300600d500340540c40307550a6505540c0200321fa0905513800a0250340d203441700454003150618010765250103070480341c110761642405400c0056004215078002500610922400e00d40c0c014411010300040341c4200340003076008218407401030803c414000301c903a503000204010341b030500d2901e1000742ca00340c507510750181c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 704182940 1250 704181690 704181707
    0x10908181002070f170f0114040507091503030c140607020c040b06120c030601021e1501060e030d1215030803150a0b1602010509030102030702070632130510 69
    0x11110307254a0310186200741e03110542030054000e0919205003d1000b00c4505140c2417540e440542150700440c080c103192401c55042c0f05070403c1c90f5030058140030500030100550000340c550004100002c0c09024400221100d0070311000f410b01c52245030342c40500429410099065041d4019100b503860721040007901c0385000d80600d48142c0c90814002000e003441029100460041040c404160300e815030709112503000289900e0443c49141d01910f241e180403000e0056a2070b8100c024202010010800c4a9406c2c0c160406001c00440080f1404140d6000603800d4942245060111010020045001c081d24a48001041040b409000002000520030056103d03084184000b20304d940a02d0402416074504e1040002040051140100642110303c0000c5450b00c141080381c17419090501083c2603230801c0310010096042600100100c6802502c0303102e4440f1100c0311800590034070040680c034040c0c0c5a151039450000031410915840481034410301030b0500a082105170120f44078003c100c1d80 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 704184190 1250 704182940 704182987
    0xa0c0303020d03020c19080403051204030b0112050a02041a0607050307050610061706030c04050c0d240e1024141806030411040606020a05010b091302060c010908 71
    0x1150b6450480c04034880c2c404d45003c11450406042c1c4184220b00191201c0c45200050702d100008200010000390200403103850325070b0581c0819201c0c0c0c13071070518401500c4145c0c0a00310003002107410200080c00070410307559059044400080d460305480d0070a2507050100091a0442c00014040042c0b02001000d030540611420446010f5030314240d04602844091245901003950146806111040f905d86964054400390480d1042040036001905030b80c010755150642c0c0400182d805140d00c41e0380124214118403a0b21506883d600320328803c10440c0030310501041020140101c3c080b8180464560000e2041c1801c40216920344110328401010481d00702c0d0110300c503000d02c0400c980105056550046100602a12011012041c055550b03c010811210381480c80000f414560b524410742c4040c0110764001c0015543e9403030201d0031035280d4140917104c0c500a10820281d0109400b00c0c80e280c81e810b423811703a01c59240c600c00c01d000d0030716048000e05812010a02c16481c9601c60030412104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 704185440 1250 704184190 704184193
    0x20d0c080d0b130b0a090b0a0e0a0b04060b090f0301090320010e0609010b120c06041401031b0206011e081020031501080105012607050c03040306060311090106050d18050a0c030302 79
    0x5544001b0030046420304d10005821100028080005a4101080fa40c0c4501c258802040348445000010102d620706d80003003a424002003a120b10906003481c0c5448aa1010340080004951940b806459015204c2c005481103c00c1c0568508800c404e4110407100c2c081c4000301c4c1e000f400c00b41c2009006c0d01c8091480c6014544120401c0c10080e00012015071410000d4105840d2a082003040381804e420141b0803414141c407444c00f43d00502a28052035540c003141c1d40904101e5040c460402c02280c00c030242c1c000c144400d45d405122085010400000d400b815100000d07410306e44420714a00200714440c40d20200d00040104040c624510b450317540b6071038090340c680c4502c0e13072550700549403840c120894071040081c0d6042e030418100d6402d501d0f9000203050401038100082081c10307600e5544242c1088034110740300c030300c00c104100d00d0012018041408484030f40321f641c14000c0082c003e001c1d05401c00b1034151140a0303000c0d51240d41544c0b400454104c8103440c44001a81000704101080d848100c005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 704186690 1250 704185440 704185459
    0xf080910050703050304021c08130f090603080409020a090f0e01260c04150906060905040b0103021204030305060105040e070201020a11010515060d0e2506020d0c080d0b130b 76
    0x380c07250080318996070781921002e0031521580c00748000030143c18004074000344101d0888010881420140c002da100e01d904081c8401e081c14004800307210240d010380703c0ca81c20151300340002044141903909803a2440f00040e02c41890b582e00700c4920f1035507401100981c0110b800403840112a52405051703460025680207070300701424111020402000b107045a80e0030400611090b443c06401040c03040c41c680e503012614603100c00d104030071200c240e0f200d44046402c0c0d240401890030103005000b140780003400c00f10306181c40c0c2c001c440304d0020000c3c4000d040507a0b03000041e03e640e018505580c094032801082c0c0c1d81c02d2800c140041c2c006e600c544002e1003c07400d4080350300701000050244520a440f0900c61410300d00c1c80c0000d01c03c1541250b410301c180180c84601080013924100084d00c140181148489030440c5e03c40c103d803202048a4001c0310464200c080d07000091034000450401141d485100725696050200000c4010010300c4903c0707600440b80050000f01d00f4264005010260088905002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 704187940 1250 704186690 704186719
    0x92a080615061206151801020c10140a03060315050405010b0d020f060903030c0f0106060f1724040c02030301091a090103031b141006080f060c0a09030f0809 69
    0x8121030300110303141e20890400c400f8032858001200c5541100d030142507080090780342d0000841e00d07040001c104503091110002200c00f03607410000441b084000351150084040750030f40007085400d04000c004160704000600300780c900d209501000003150424650440c14a901c15014003411042e03070290352540c00c110a200042c03900c0c0d040c2281240d801440068841091024040c2c550040040c2d581c1c113020038040c10035008428030074000018400000002c250b4180040030740300303407440d6010340c0802204c86421202c0c18030025095800c200400d852500c940c0a01c2c40007000f0307445401042e40c0050800700c80c6184990008080d60586280560a2001c2020030070f00700030030075080d40180d5219283c1c0c001080400c4c0a261441d6840300303020b4001a000c540c030307250010020302c00c644545590f84055050361914109208603c080c00045c5c0c041c04005145d031940310303580c40010744a00100349002414961207801350f05820011507014900b0522030340313582000b040c0da8000044c0c0c00d020310140c40c8602c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 704189190 1250 704187940 704187961
    0xd080c0a03030b0105270a0512010504020418030801050d081b06010e01090e060606070f1407030201031103070e121606030f0f0c080106120b1e0316051003092a0806 72
    0xe01c440b90380207545840c030641c06d01d400b074502d0810030f03030319007268440a0104154580c00032215407034425000108140c10320780b050008441119034100100d05041000900082d0310207403d904480080710411400307451818180043d11a100d41301100210700c000807000004089001030486148845201c21681d82d482e103881a5604101d00d40703020f400c080d0000307030703d49001d001070805580518141011109183d80c1c030320070120b01450401040d84116010400c540e0b140c090300318000404440da42c00d50410b19005400c804503c003d19221301404158035900301c2c4200148038000c0c030404400c60034941c1d1450081d00524030003040300301c1107050014a600b20340369400346101400c016541c40c1c1181c1e1030304104490342c0003005100d0312501d031120211781c0315548109400f04001c5102072924400008901018603000100751108040b00340c0320070030031080c0d50b0190710041a86041c1004205080b443c504a00c802c80255071a009040c0c0710701c1c40350700d416491040203060791054007c41d070290b02e9200401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 704190440 1250 704189190 704189197
    0x1b06150a0b0403080f040306060803041401050711120c04060f06140c0d08091f061d0c0901030e01020c06040c030213020c0607030c1b03110115050319020d080c0a03030b0105 76
    0x91000780010030003080000c40e844010300305c08110304130352403c264496881e0b50a40325140c0c0650b11907480410b003801222805488000e03411001d0a016142c10151394070544000080c91446116046a03100722135518801c0c03086425005000b48100078007038480b043d5640d0b2070400d0040d540001c1c000300c2840708255496007280e080c0c1c500030f80240002e414801e81240c656400802038007050048074640010219030600c10018072440307031130115019013060300d404640700e03821019001b940d86d020f046c0040c0d8039003202182d041442c01c0c81d0104200c429400c000340603209020581020b84980e008103c140000f2246400a80e03200302c0d0481c2c8001fa02e12100c000740e004160b4051001e0700404d0200381e2540c003a500c0361244039038900303201d01028564515010b159407240c406030049058141200301d0a0001c1c0b24038000c2c01100059a0000f134101004651b640106028840380350103442d580340c0035556900310309003109a000507100d5481084403201a03c500310010110701003030070840184029801041035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 704191690 1250 704190440 704190449
    0x41415041404110604030c091d0c0d03030f0b06040e04060b010203070b061003090501051006090b0c07050d110604030501022107120c2007030b01090204180207081b06150a 75
    0x3440681c440f51900c610080740c1546169000c0c004100c00800103c407d40c2802c018038840c0c000280070b1010001d019402c600032480200706800206e43c1703480543c2d80c0c5c0101c2c00550380514001807903451401451000380104c2c3c440d43ea01040214000130300b0355491404074450380c4603400910144004000591b541e000701c400051a91107580300103141c50070079165041c0344580920307020800813030507251a409c4503401d60b11001760f200303244014040b441d08000c88c80000c040c00c24210b0b10b0910300f0b081243d12a855401407500c940914801441404410900000280c07402000190703a96a130345041e034001d5000000d20200000c641404040e4445084102c0d4442d03a0592195801c5601c92004a030051001d42451014080e20b04800e004601c80044140110383c003240040c68403900710304146002d2801644031207080e0b80100020320014035000030a60514080e0780025880b85203034605401035010b00080c0d80c900000702d00c1500c040e0440010046c5c002e20005c01401800c3d07002c0014000400f895015 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 704192940 1250 704191690 704191721
    0x19050603040b040501090606140306060a0f0509060f090c07030311030c04120f060c0e01140301050319240603060c0201050c0306060904060f0e1e04150506010e04141504 74
    0xa4085039800100d681d00c20302c44c0000042064880e61510100e48184c1c00105110800c0c11400f400f60404000306d40c0c00140c00c6036103807010340c41c0c0f100f505d510f03496600550f03010b6411400031401c05e44440503041c1034a40020040c1030185082d070305d480b101d178001c68415000a41811011105a04480112030280240d0f0315001e02d4141012001c00e40c04c800d010003240c0d2802000418400300c0c605108032340745074045036181140d0030b1350580018902d21001000103c802020001004241d80000d8555545030315000e404d01c0d41d81c0c0a04000010a02c118500c04648114244030010059154810b000740c92060703208100c810002503080b400c855040303400c408070150400c046007062a085019005d5240300400c0441c145860b00000f0b1070b40c07402c075030041002c403000000780121190340300c021039181500c0305442000c40c5020b0b100c09015915444442d10550350f0b07100070440e107904c00c0240d02d0003048090024802407180043d595542841100d0b080c0070781554098054542c80d0501829943d00d40120 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 704194190 1250 704192940 704192947
    0x31e0b090a020703120c081905160e011e081e090601050118091b03061e0605031b0304030903030801080106140f0102031e070c1a0a11010e1209190506 66
    0x22200c00030f5101800a0701403112060809480040d5030140c030003d0503143d5200382c041e0600b00b0140625611003440300c0310301070a002c2000b0644200c1400b40c200d1b101c19140c940b00f42007009005803105883c0b543c521002c0c84a080300c0d5100b20350000c40c5e10340904400b041040e01c2c5801c000c680710703001c0d5055903a041c894008100412240d8410103020049064107074040341119582c44402c01100e0202d803038645480d4003440c1d200d903c180c16100c0c10b401054140d500b1091848092011100c0350641d00604041c0003011001c5580c241030014081c2d008503144410960f603092905010700200000e11003140003405680000ca040c0d035040c0125400c031000c0380f40300320b0b015105034104005409d02d001c50f60b04500c800d00a281110900844030303640f0f00941e5650503641c08245c1800258203816412a002c54903042107207001080504044a06072036492038228071039a503c6055071f025013105c280d407860300d118400e100400440c00380000e0820328800c17180642411200c420748034040344107100302a40502c007030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 704195440 1250 704194190 704194201
    0xf010b07080d15050d03030b0909060c030703020c0705040c020f1204050d060b0d050303010e0901060801020a0509120c06031e06100507170f19020c030f07050f030c030706031e0b09 79
    0x9410403030f19000b40000b903c4500342c03508041032104846040c103400103038850425004904103a03040d59005148a0040c0001e8507009100c15100d100140030082010b500140901842d84240114005410000c20501214400c214000d5a40d10700d040c6000180c0201800e51142082c040100c4048600c0035015480000e955101c2c4801002400000e82d00f002000320080000b0f2001e00046002e0452417804403d541050307010a4210740d00e035009014507a10401c0f001c80e03529002000d80d0300c0340e941150b08005151003d02c50300d0411008000b500c4d0800004001d1008121440d800076900c1e1518004001d419074503841040204c0c80f15802e000045142000440041502c40040c031140038100e405240ca0940c0c1e40f80001400d600824400000d0204601507003400d07641405680300c1c0c807004030001c2c1400011942079588501d00e62041d50301c601348100f1035110b1070700c0502144000200007801c1d00c0d000c1d0340c1c519018000e80500700300c013180d400f4102100c0818803020310500940400c090020125581c41 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 704196690 1250 704195440 704195467
    0x30c040b090705090406090e0f0f030723010e0106032d150903200309040c030b131a031b03061e0406110706150302100c0b0c09060c0d080f010b0708 65
    0xe0302e036885e041921410301007000f401c540141008001894020003001c010180c0c01030038a904e240078050103070401c00641e004100c88504080362036101160515003900420b00b0030740100140241d100c070700c0d42803040000c02d202191000440030658550a101440c106240003a203028030404000c00702c500303100040e02d2514241c1d22100000307110307040c4060300c0b8a0a040180000082c4441d0008a6000240c05445030500c2e000b64000c0800c20b090502c50020200300042542d0f22506070445113135500c204403241d084039400d1004680501034250fa072800404402421280d1654901600a01c190b0001c95102e15202c00c10020124200308000815140c50f0b4805c00a0400e0600e280b1107000c082c44009d0220f0118030461442c0c80300b25018040e91803540c414401405050031000090000d520320400200746a10710b510342c050801480c403656041c0d4400080e6807030041301e070100d40c1d500c00e0110203120700341c01c0f80d43e4038010000180300c450940e0380c074512030320513114140b0020300307101c000d005205c01c0c101c0c1e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 704197940 1250 704196690 704196697
    0x1302130e03130308032406031b0f04180501050d030206130c17030c061f050d080f04031203060503030a0f20060c1215090f0a02070b0f0402030c040b090705 68
    0x2a000241c0c0c1c0b07040403144444005018580003520405000010700c402c004160540c28900e00d0091030201c0708200c4980092078500000301003600744c4c03401c885c40161a038680700440305001030301d10340141c480c0e444216803404a10a058150843d6280400109070780c905620782d03a28460741540117107015503400c00501402200c4102c101e822800d03900011880d1184001020b110401040045846803505110b0030300d8203501400c2c1e000301c0da0040b00340c10402084540000c040d5a0241c903500a200c07118070380380b81c0f50b120b240c1d034250700c0800103c5c010080141c40c040042d40e1a1050340c050100c50345030020103031284104064080414030351030031080070350f001d090b1043c0b800691a100b00d08480180180300e0a280040380d992545400010301e070035000905490f40740e00181c2017440300015032101800304046a5014003e192203002040024408100036011070740d119a2003019500c00e13007400c401104030b000e002d8030104e1003409a8101210307181030034440e03124031180c001c0c141a10f070380321180f0544082c0d2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 704199190 1250 704197940 704197961
    0x3030f071a071706010c020108180c0d050c0102070b040506072904030f02070b040503060708221104060603091a0c0c03040f0501181a0307030f0f0501050405130213 72
    0x206000018100c9802840e100c0d031280b14151503840e4260b4009841d4208031900a051505000c00002d5020140c1d901059a60b4850701410844400f80302c1c0307a10035440d22a946507017582c040390a0025000b040404901f40e40407603800c2c1c00b00c039082516035098450600542c041c0b241c104100f400080003090428100d0344201c0129000340c032200d060042890609201201c003034011900080c1c0c20340c03405030b040180d1030081c4000e61013141860306010000f034542034080c24a03c20007400c500494a1270f04601e140c1d107402c01070440c0c1c0701c01d100d0030791400790400c074200810b591195180c0140018110f001e8010840901e0780610400da030040122500480350381d0107816108510024403a11502c0c1d04200001c0015100c4109240d581e1761401d400181000344078a20742401000d5184108220340c0c3c1c400b8a4082083d62031312a0f9101e5940010482c010440f68100001c0d040c1458080b081c104103541c003050503914203480c1804595150043c10000f502640b10083d000000781c0d60001d030b98100d90707208840c2403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 704200440 1250 704199190 704199203
    0xc210d0c1a070e0a0f141e030a12021603051c03060b1c06120209221709010f02010e03040e1003020306010305060f0a0b1e011404120218010503030f07 66
    0x74000e41d00307a00705541003103580c0b5010443c03e07080394001d0f28010110302c00034001c20714040340ca80e0905500b00c642d9125400258000c0755030f58443d020b098118a904081082c0140c120390402185081c80b1b0f00120803c440840503004040745030700f00c0c0311005100002c0ea500200100407050112042d00f824640040401c8101651558007060710b0f8000802420b0301d01308115202d05920034410040304441143d40601c00c103644600c000030045c0c607504000d60380070034022102e410640d0182e02d0010800502c0d2802445101c41c2c00c43c003079500000c90080c004a030800c1e42c2e46240f81e400000c06908807170010711030500660041c0401c004075018400398aa00c24040c1c0f58030014192340b030703010a1802d4001c1e00100c40c0798001104209a003165031083c10341c003040e0b5001c14801c1c15182d8021406050741100d5850810003001286082640126580d0141490b103103100303952181c0e50315212407001d8a03150103d01c101010780d03c1000100c4c04080131816100024051442c2c42c0740e40c030b0303a503215510850b41100e04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 704201690 1250 704200440 704200463
    0xa020c030105090307110f0108061c0204110301060816120c030b0a08010504032c0616020a29040b0a0c02031609060612020a08010515070b090c210d0c 66
    0x5549080c010540070700f03040c20046440e0446490000c801c03600440d011801760380d5545e001c0d451070703a100548540203602a91006841d00822031050010406440d0194102d0704100003020151100d00040d812114160b0740d40e0a1a00d954005c000340189055140d07002803808030070144581403c2d803103003800c840075040c001200219003010480c540d4590f030024070f25965072000c000605400c030b4200303104400714494002d10680b030403001848510f08841d80e80d0040c00701044003000021500382031800710780c00030030344954a41c0d01c2489005a00d1040d503d01c11003503490000510042007030055a00b582c6070850f015040c040c0c40c0b102150b070380044003003d030b9043c0308000307241c40409820049007010f400694000f1440750309060300034100c0d92801c22040b4005104119000000b6405079489065540c119150070410409200164082c0680080500049904414031400080000c0c11000d407240c10740e000620381201001c28010441e03091b01d8107003550407088a55542e02c0c411800000d1642c820001d0306003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 704202940 1250 704201690 704201713
    0x1120f0227160e010f020a031b06050f0108010605040903050301050f060403080a0206150d020303090f040b030f0f0f010e15040302010204180519050c0a030209030c090c0307081501140a02 82
    0x20300d40c002e903038600210301103900c01150705070f004440d0302c024082801c04a01810200d00e00030350ba015014800b40804c50072030700c0310300204055420304469035040b120921550130041c0c0c043d5800f80080c03140700529840c1c103000149908080c01002d01c01a096140d09045a10b003200f400210380c4031351151a0300440800002c0300280b00c2c80042c151985159004192624008104044c1c0300d0264280a101d04244c0380c81c000180d50000480c2c1900320f050310301d0401c045c1414041009486840382c8281e050044034400741600b413000a408141d18440c008a031000c0204070304041c2210071203040c5041c3e54000e108810010b0000841e0550018130070b00c0010701c0d065890f160b0304410301a40c030b0401d03901a1113409005c480001c940c403c3c211800e055804201d941010441f1504501c2810ba180040c140c01140d5040c0658080c05a11403036000035080c4030240c170303101a2aa1165008840c180042400207011419801150118103614403041e113460130a90b10403841449580c001c0c0e5048000c500c0781e0b440242 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 704204190 1250 704202940 704203009
    0x71d0c07080a0801170c13022a030c0115050d080a181d0901050709180b040603050109021507051b040906140106031103090304170a06060308040e01120f02 68
    0xb800741d40c1941e860010394107103000301a041010140c41005030340300580030081c50341e0740d4060707003030760700308202d0040c4c0d034010310421607080f2028000d0a1400410380002189807a00c040000d00880750f08100800800313510314141a11144680101c80d008410b0000d86800030311034000500400d00541010890b002062090481d020f406401c8028140795042182449082c0e40c05041d40050742c12000b0703c294034007540d00070040180e9100390281070302000d42c96010ba03940e0343e000f24411070015209200c020f8a90401501074202440c0c22805444042075956510f41c6000559a0060780540034055030354489049850800c400280715603c2036407001e961001a841d4030991035003482c2c05003003c40387e42c50001c0c0902140e8100030210241081002003002011001c8100c4003680d0f00041c16000e550a002d4030782c0e00d4600203a10040c8006e252403c04820f116480c40038000711203142c0c102403416070300c1d8156420040030050b001820f4035040c02d07014006151504008120a90802c40c00116020450422 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 704205440 1250 704204190 704204197
    0x3605042f120c0a0305090f2a19060806030a0b1b09120a0203010e030a080609040804081501031101030207120c021c03030b0306090106050918100207060209040e071d0c0708 75
    0x100002c0000b5011009a070940102980700010401411a051404441ca034540240a802d52481e1340c00c8904240e82c98284042c118900307e008c0c1010411307807101c4400000c0c0100c80e0140354007081550000486d04c0c5400600100e810380d2180f03008025440b4491010350342d50ba1118003001c2e00e902800303200c1c900d441d4081d00c1004020540000c4c007005103240181801c40f0403a004020f80c5400421140050940000b01107400c50003d44104620366240e0418003a00c0c09140c018014900070441800305400c0000e1015050f04d0081f07017034141210304000107404a2244010042c40071410681416201e0700902c56038802038000307080b031a5260903a60004003111240e00701240807a80ea03034181001d80c28204455035100c05000000c000320350620001a03074403e0020710b91131076100140303900120050284503024085031918815901c1d04030324644000a5000282e16502031403402c01c200900e01400613030a012070b00c410a2110341c100401c298021000401490700400c0318040149000007003411004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 704206690 1250 704205440 704205451
    0x12250602071110090803070803060d0b1312020102030121060e0709060f0504020702031c03091205030a0c03050121031704030c0203160b16033605042f12 67
    0x1030038902c2c01078008010840400310002d400f0008440320621400c040003007160004c1d40c2210035513440360780380400103a500103c031100801d03041b4403a050040a500f81c595002000f4815211400a00030300c6004900302c0c002442030446080303a070700a04089e030000e2810300500313500646000c41d14424580d2100c2c6804c03520351203203040b0750b0744240401419003450030329006807904880c00c0d881e2022a80010b682c40302016418044820800381d0050b80c58020350240d0461503006183c160b01800341d24016050b504222015100c080c03c01d5682000c0902c40d1240c641614140860101300013144520307a0900e24400390100c040c084150b103048031007000450070501c264440da03141040340d20180f05040c14583d80c000c0f28010f16030007913014042501c1e402c05840c8021110780c2a0564000d04d800c0440384207400400b140c05515000c4010310202d2825102404181142c0e0402c0381c54981e55018401182c80242c00280c0e1b2503230000e681610405140300500342d070101000c0550a00c04410003204940105591 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 704207940 1250 704206690 704206703
    0x50d0f020c06030601080c130e0a0c2c061605032110031124030105030706091a0306040b0414070813050703081308101b21050414010c090302030705031225060207 71
    0x20001048001c1c0504848106680307404001c184010b244101054462143e1000e4880e0310002d690540c0c9a000c2640c43b5440742d140e140012a0303540c241142c40f58009984454100702044040e407903111540c02150040c80d143c0e00c0c0031a41440d64407102030010368030b0401035010a80b400510030031884480c1c180212296107400c0b968a524140c00c040c9461070582c40101030289140d020800d400c1d9808004160540c0c046c217903941d0b9542e1000003130042c05030062099000303280c0a01e00fc0d81403440e4045038440d1047d6200e640464484520030040588400d07001440e80c2c0c4555000d200241010024003807111b01e01403001910b540b0b0b180701c141000f00c0310344061101036907404620f103000f100c021542121700840c00c2841c4040c0c103a0240260782480031b01200c108580712800700d0108140c013050781842400003c000c104900c0c5c0000c005107169418402030340701e4130500340701181c01d182c041031983c580c1101541841c0341c904050520711072010541c031b00402d41c070082011003001c9283c6000a160075440b414 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 704209190 1250 704207940 704207969
    0x270a06050609070c030807141201030f03080c03012909030105010608070206010b13171c09050307090506060901110a32010504033603050d0f020c06030601080c13 71
    0x2801e120b012407006240c00e0412041c642c901000c260000001600219039107402ea50314600c6107015403140c0300b69800c080700d88201000010500540309a00704540d4820f580780156900c030786c542c0c40304170f01081c028007103500408000f1400301060f0800c1855a00c2000b000d19007041100000203084030030036805070b0f000c2640c1d4030400c4000b90b418400366002d007604425503410000e07040f00752450001c0e1800f074010072040944d412110700104100d00e20030b541d80c2003480440b100321500002c143c3d021600c00ea50081c802c68001041850782401941d10400001d00914204890240110380b40106d000407414a402429100c4c0082070b20310700b6400c94001c840154600f9040320549001d046a44040d24240c2d0341d14240520000962104004414411f840304404041440c044a9400040481c244080080c1e800d04c1c00010000013241c000314004098480c60001d400d141d4050f40c45d200101c0c2241da1080c3c0820014040d98020802035802000880b0240d0400a0550315100e101c00c603074100100105419 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 704210440 1250 704209190 704209201
    0x306090504051f022a03270f060c10050402060c011821020604081b0609070603060803041809080412030201060305061503100c14040b0c0706080f270a0605 68
    0x10a062803c0312008030b421460054410304032a8101441501103081c4940d290200120101c00c0090b1150b06d94071100034040b8001192030014004811060746000c2d4810100480c403d1030315105880300d11042c10f000d008121207014250b4000c100081c001c0f03130b0289080c050503c65807408d11235003804007142d004d040c081c15000e003814440c94a148030304841c90b030807290f00f00e031200703501250081d0025809001141c41707c104a101c00b00100703c201c8144450b108250030001c62800c001741d108116400341d1002c0005d1a2100d2020340c50b48101e006500c0d128019041180345d1200e1b0b0780c80448440e020701040f5041c02e4540c00351283c484240c0c041940142c2d1180418000c1c044140902a0001d41c0408422204e080003000b103a01c91000e40300d80000d0564030300e00595500e0180c020800c10b00b5044e048503603140d881e92010b0800d50084030039501d06118140021550364014031075907000e5913160348001500d50700c2481d6890b01010203039280c0d140c00344180d00390032030042c10090544200c0c840c4170b01160b01d2411 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 704211690 1250 704210440 704210473
    0x120207060e060304080a0e041b051902030f040b0a091206140a05070212030901060506040e0f0105100512150a0801020a030e011422020907030b040f0e030d0c030609050405 75
    0x1400d00705102e02410070038080001c0c024000c0301c101081504283c0c40280c1a4400134004002e450711100b80101e9000c032030301032103a000d802844510565100030710041640502203949000c2e16148540a40080205101c4845000094185040e880c50404a81510b8103440d1003580e5a444085510640720b808417062100c0398211542e001800940801603444c00210080d552000c1d66000b0810300c50010204071100400c0d0000005818040c021660300d1f540d450241c521314104540c15003c0700000c0001190510340305074890203101a13035480e1070900300001a160b01c040ca002e130050008910741902c2c000701c1d031a1540d2100c0140714030400142c40f9060800c0c0507090720328007030004a0b6a4075010854400308034040d412504003101d020700c5120070000f89a8200c1030a510307030b40a540000d145003040700450f40740c1c00596082c64207450602402040484a0701940c0d11b400508903035400c02c1c00410300c00c080d954410200300080b46000305016940e50421421130358252010f031100d0b0404200d40040500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 704212940 1250 704211690 704211707
    0x909050c03390901060e0109060311030414030c1002040807060201090812181204030c05030303040222110403110a0b030c0319090204020c0c0f03241312020706 70
    0x6501910030380c0d0481e0410b1042240800515101d603180803094500c03400e90082d0740c0b08070302c0042c0c071100165031206005000c80803c80f402c28005098201c010860500ca40200c2900300075000869066882d2550b43d032040840504403420709102c18841c0031210030080140d04103410405000590381c0f41007600160900000360001d0043da13050038000400180386c802100c88034085590140100c0d221130805c1c1c46c44000c0d11180c00782c3e07440b170380d403200041148a000030001c80b031103000c2041c0c0803640d80c0c00341602c0f40400c580181d817107802e00020b007294403201d4100391031404000310009001107018040045e00e42068200350340340741400e101610789041c035100c070101a0043c404800e007186480905c40c020707031200030820326041190401c914041c0c0455005000d032141c0c000d100317540300c5481484440c1d4420610070043d2040c0307035401d80c6154600b40400d00303e10441c1e041d05080740c003031054070194100540c050081d110701c60381e031441c9501207a0203500b80c81c2a81e800703034041c180713a51070100c00816040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 704214190 1250 704212940 704212963
    0x103021e0d030809160f1404020f03010e100e010302100c0309050307080a05010608010e1b0303041d19050c0703210203271207020f12030328060f0e04080c07090905 72
    0x10005c02091040d01c0d02d0000306401c68041807660500300c164030740030401a00840440c8401c00780084000304100c040444217600c540c03229500d03003076043d40d00c2408903041c480a100207508540c07000060000c50f88651183d01b41c06000b801c0c49c01001e581d0f007001c03900d807202c80d51080010350403130101801000f41c280904c1c4001c3c0a448000d0001c00344014400c0d8681039141155101c400700c1c181d078000c3d10346041c4281c4001304020401c071080300564040310064070004450288080308540c04031019002107110b828045d40c0f1060b101800d104080e40c0c10b03642904020500c130164200b00e81e00e0612207010340000c5103e007610400c0c0d00c101c00b41104c00140c4e141076500c1c4004854101c01d41c4c10080c0c0114009507144650100c641d80c03507030900d007004100d0115591a1a240b680000810404140740c14141509000c28496480448190111060080b128240034a4026070004c49042095004800c40c25402500030700105250610f40c1e15031515240c0c495010005035601c55420310280074040c000a036480 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 704215440 1250 704214190 704214223
    0x1021305120d21050a0605090610120905010f090c03030f090612020f1c151a030f06130f38100903050105011e0f08060103021e0d030809 60
    0x621000c24592101903a4044008100d0341c0c0080d40d802c22042c07803d41e000301002a5080145041c442d1111020385400c0c01041e011700003030030200e4001d0802618031840c4513104c2d034403000e07007580e29140c01016007a19581501e08c0d44d01d4501c0e4038510142d9210f0b4501a600c01e0802d11019469403070b020784503408000303800b4203110b001c8070b04010090300544900d1f8940c2141c04010381d12898400c1c814410300a5a822502c6017108503d0340c0c110081540c40800042ca07120418500b06990798445c00c507280400340e00d00520403007400030459a204003100d003604900300a2010b006024900d180804580c3d01041c0074600e16221380c03071301c803107010043c01428042c0c02485808504640a0307003061071018900038514020b000380522480203d10549003000590340c018003d001e15659001031010f40c00a040d81c14400000d14880090f02140861007d030460b44110050700490b03280d9005c000321a0400c611460058090700c981a00303030368600c1c9042c100540300e915401c90301e003000240b69213040e00c81c1c0d4480200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 704216690 1250 704215440 704215459
    0xb0702030711061e0a020a0b0a0209010507110303250204050609041e030e03150a0501080109020310020304020105040b03010b0315090601170619170c1008060108090a1401021305 78
    0x42a000000860703102e009841c43e0f6507504445103a4030034140303516050010305a010507900c810a601050764000030740218058189a02c80808080407485000c0340070340822001c001e4680000d19980e031120074044000c2c10789081011111441800c0701264800c45602141c12082804528091041e190000300035140244285066515000d018005844080041d01804804810503104220b00c231050030014045d070340c1e1000028455001074600340c92003407100f402c00c1c2c00402c404ca014414004416001002440102e40c0401e076130b002588041c0c800d030f040100810011500c40d2107100218002e20700110101c1c1d0340d00d0075141c4401207941007441c0603c121a43e030300380900c40ea80800780540b031100010415105031140e00c00690440342640102901e104410000510007101444a880340c00c404000d48a541c5608000c008050031002d4600000c110800302103429948188030b820340c84980c900448040c426a07031100c44050056912011090790002040c03e10b4111201d10100100070076204c2020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 704217940 1250 704216690 704216693
    0x1030305160f06180201320a03180b0403030c0806031c0e1e03060f04051e15191503020906100507320c010c02150705120301030b07020307 61
    0x401e10a22400202041c040c02a000c107100350210308000350303a0700000801100440c04c0c041c0080b4048030000340e02007903401103010030072184d00340040703e0010358020f0408818a10100b1164542110a010003016034842548041e00380c0074510301000c0c0d0158501345443d103803615005050303e0940c211300042001040030301c516a14006124409a480c3d000c5260090881c408129200c500c020071315540308890640608040864003c05944207106038140c03659981e8072443da00b19120280d0b0010110740c0240e48506a07a05140b8201003e83c0c10725056404080303143e800900000340503070701c0340d240c0411903115198070700342c5216403621501032070704d019040e0780f0303580004d104850010440b42c00303448804880e00740644a00d04079405641c1c4401000b003092000e02d0250b0011445401803908021040d400030000400000c40b0325900c20160344100701307030010380c1c28001c0d24110007100c1c0c7c03c041d00510160f00094400e105101d1616200300c489a16980f440c03c2107000c21801412940130764000700090780 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 704219190 1250 704217940 704217947
    0xb010609180c0c02040f0b0a0b030117150a05060d0609050106180605011b110d0305040e07030e0d180801020406111501180b030a060e0309030105070915030e0c0d03051c05010303 78
    0x502aa80450b07000940340c0011002d00090707e1713501d1410768000d440a00c0403030458000d030041c5058814280312207043c0d0340072800469580c1600328000165000d001c0028502c10780c2500b0043d480680988820302e00300c043d0765440150b078440701048030141d4503500c0074010b040800050082861720200700340410340c50400040e08091141da20464030f5006000203e0602c11301403501681d00d05c0242100d28504042d0500600c81d80107030081c442d8000b08080030442c1e02c1c0c400d0190301ca0461150001e4840c0110b41c1000340e0700c501000741c02c0c1700e01c56040c050005014100b84042c3c4001c2c4525104d002503a8070204c1618100001b0b5030001c5a0080c0c400c0041c0841096509010020303d0400400205410b034200000e251841c0303514001c0520f4100f001d44011b10034040040c0c404010250000c0c071454544250954040c00705010b1150341500d24845003030140c0c07103a0440c080c500381210680742c50a0414010030741c06021000190049600018004805000d00e619440e040102890400c46941540c0e03000307 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 704220440 1250 704219190 704219207
    0x240106090611120a0c11090411120f030c0706170f0705070c050a260a0302031e16030f1e02340f050f031b1c0b010609180c 54
    0x41c08102001d020a880103900b0070402d500800c0800d1981c3d03c07240d1991000f880c9016000040361000104180c071794460800c0100c060085a12210815035006000e0130b020704a161a0340548451044180d80c0d060f40e50f0034030040002d5894040a4802e25003890301c00391640103006aa4444100030301c0c200807190350070301002e6401155602e0150ba0350501c6050812100381c080d0416075110a42c0d0b280002d81c400310103041140d01801c00882c08401684144041d100c020380c0401a015030420440a046070204208100702071110695140c14a002911040d08010340140c045001c02e442202c02149281c0122000c02d0b182008804002c031486c550100940b14440c80c3e15030b0741045140982c00303603107100800d03554100018038840c144000b59181665082900a841168002c407442e8849103030b10300303010840d04c1d841ca4409405042811010017405000180854442e00340003041c7d000d0800202e54004c1c6c00d008080d1a610292602d08048114080001c00c01c04403803510703d02031a1000f20b43c1c010009 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 704221690 1250 704220440 704220449
    0x9070e040b070c0203100c0201020a0306083706020412061404052e140601090501170c030901090203070303050c070509160f020708012c06070c1103011d24010609 71
    0x280c4000f5040d44082854050003079480e6500908160341203510590540c0506032824503580c06200045da1040c49503283c0030091403a0206000c0c00210024489042e00c2480b06d07030380701000807400032400707440e440200d0700700d5040781c2456001440c00c00c0602149000c0c00005c00503c00c0c10035241d003842e582d09d80c0e9600345030076000303031100e030004a54010302c10006641d045a1f9503080240000c0b10700020f42803010008440c981c1c0850030022000c500e5502c100000c403986a1a10810b03806600d901c0340480c0903801c0204040d04564913000c0d82e000503141484000000c40c07180c1c588a0b1941041202c07141052041c0e00034070701400e58202002901040e0301c54600c1c0b910521f09040b0501c1c8800941242828801c2d04224420741c00c004000010082000c84404c0c1e044203030020744000a4103a01c0c4a0312a41d01761000c2000030a5510300c10017107901031502d03c0f45050010b0000408040380888504523031115940860b042e0010b01c0d0f0068261080494a44c0c1030781c0c12084140340350304000010300100042d004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 704222940 1250 704221690 704221697
    0x109150503190f06141b0f040b0d180803040c05061309050630010e060606040b0f0d0903110c010905130b0312040b21090a030516060f0509070e040b07 66
    0x2c80c401c0c0102d8065440225400180c280100000c3c500c0354500c2d038030240e0f201c6080366200701c4021941014802a036840907522170a45182c94902107980c00039811588210010030b0b65454098007070b002078003600a0740f6100c1c2e0400da44a10b0705003000d10f00c03180e82c0d52040b40124020090070b00404492220f4000359400104009102c0e158200860001000f001b200f2219510609000c50000050150800c0075441d0030b000740144481c1104407611460700b5200240c00001c284000c0c49059818000341450022014255050801c3c0d003001000780e40d10018181c0100c1c0800018000481052041c802c071182c00f82032003601c42e49071001007101000e5001c410158299260285e43e403595040c025440c40b07451188075103854070f45503440c1c80c0f80c5030700030005040d510943e05075000e265601c10840e107109445820140825812646081d01c40782c1c4144070061000800c4420200040d00794880d8075104140418001042d1030506001c1c0d180060300d40010403099481410040002c4c13510541c1356010801e807a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 704224190 1250 704222940 704222983
    0xc0f03030e060f011707030c03141c0f030b040b0906130b0402180a0608011215060513091203090f02041119030509010b0a0302010c0b0c0c03040e0109150503 69
    0x2011001808640385088441c0504030500c040307080f24000c06416180301c0b601c1400a800c000712225960781c082d20008028448690013003001c2247d10068098480c0e64205070b41e60241c000c070002c4210000d0036030040101c0c42020b020007000707615100c3c1442c810345c06c0c0c4040000c2020140001c860f40401801a8440e1081101c0d0786418510b54001aa27840340240096440380d10301d00c07174004c0e620702c0c0300101402850048000140c540c8500505812a06011200e03640141c068031a00040300401020202554a4520004003511002c801103508900d01000080710b4012b4902400f2454280c075400040505040070b050128401c404403415075941240d00040036000300d003c8001500402d40c6449020414040e0707a011150582c10542c403402c441d00003040101083c000300f01c0511464000607001941d50380700000000d9007910000c2d000301907200b50a0910544440151440d4460341080c2c02e80c1c0c150f03000400661059024024102c11111800c0a00341e080c400443d47d940e0b15881c03c90120070006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 704225440 1250 704224190 704224193
    0x21504030315080123010e0a050403170108060f070e061b0c030a0f1104180809010c05060a150e01060f12110304121b081803160305010b09010609060c0f 67
    0x281c0c001c1e02d02c59118218030405507a2001c041d8000e0800008945054040150800407503880e8803071281680c006441510071034031303441005401003034014411000d2120095002e5081610083c7c03642c02080b60700014000da24045c2c00c400c0ca040800740608090108005100d00075035101c0050b03030340c0440a5038011000d00c0c3c07a0750b01a071500d180c038808960540192245881880010b407102d103c45030003074a0000d03080080d1804c1c0001c5552580c0c0260040100706c1010002504203002417092180500d4010341100042e110300d42003034000e581400b0002e035581d504607483c1c085090404c00400f82d0741510140d96140c5800988150300d40d9040000b0040c3c005200c07006480707903902011180c058440103d8481c60180f404413800c0003042d00c0080810f070000088020a40444481d00c009507014526604000844444060f00091a03020a625000380c2d82240400040748100c500294045c50020420302d058070240255020181c0086007080100c8609001c001d8210f0020310500360300c00c040c20300c044002d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 704226690 1250 704225440 704225447
    0x1180e011b050715180302150103240e06011e09140604020f0408100f050c16080307020f013605060103030e0604050d050709272306070906020c090702150403 69
    0x104944500039262910354a004e0288120517451640700f80c00711400030359200300070030380c1d050244030041040c072265141d00c5903c0000d084819a1242d450404508401c41c0341340c6c0360400070240c100b1700d035283e24105101c1281d14841d6440c402440f504400304014865400d440001003001001e00f801240c0004510041c8129442210000d1014405940303403104400014030103005034200300800c035400c1401060603400b6080031141d02d800e904070400c0c0c44044139624003810b0b070030040094041d0701808844001c508400e000b46560111202013109a00e04200075480088084d410f0300c01d4400f1049285000084000825034150307905801e0211094006100284191051750400d5400c200c40780008001c110380002c42c0000c0e983c0f650003e100c82e030005000c0042d01003c100000904002c071808510215981e024451950b8051042c41c4041c10b040004d020b1038008143d40e5000059017200c400c0107150350601c4400e400c0001110580c0060a0140c8025a642d8481c00342826015111001c5400c1500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 704227940 1250 704226690 704226713
    0x1202130b0a031a0601120c0518010203091309060c03052e05061605010b0405060d11030a0b0132060403031d120f0601080f1c09030b01180e011b0507 65
    0x40c800c035109403601d038180b00c480703c010042d205140403c0c0d08040b01210700e4410f0140b90f00c040003d41c0c03064102180701405010303512001c804141540802c00c444012600c48160000c03143c3e2007003102196601d03162510314204c0f4400310010040501d8001444060701e0304542c81108440c44017100e0046d403082c0b204442c0d0700e0000da031100e540424000340c07036914161103455240c00303140500001c000b619000003e01c01500c1e030440c2c042c0c0d4440704861142d00028000803800700b900402504640110740556507101c54044281c0080440145910759485002c01d0908002e2412403000d0f80b50a40c1001c44000c90b020f0301650000405001c07104080403d06960303c20a1401c3c0d40d40201015140203159041c140c03112583c8200e035025001b01000410b0141d00064030a443c43d24080090000d0450440100380500e11035a49200b0000c0110340000420b2046288602a000e408145410000e101036800c0444245030324208507641001c0d41c2180204042e1441c8241005608110b69500d4031132030420042203 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 704229190 1250 704227940 704227943
    0x302010f080c040e0435030703020f0c0601090b031b010e1309151506050f031f0906060f1706030705130e10060f0e0903040614091206101202130b0a03 66
    0x601201003109015003a148100070200f0341d05e070600d90001100a24811070210001b000f40c01c0d1042010602d100e110382e00902d0f12110224000c0d0810002d0361181c0d0400c4070a074441c240f400e0300c0741618000307454148038580140189501c00f100c0d00d1b1a000020781100d814400030340c80b0f02050300d40761000c04403603008000b41c1603006074036040a90064628030000d0025519003c0a44c2c40c0702800f043c0035005070103d4110000c00742202d402c596420b100c0500b00b80391200ca0800d29080b6142c0000d40d0902070142c00042c220329110701201c01d4111034020f02400c0c076803182d01c041c0f000300e00501005071000300d4030340c0640f101a01d03600e0704000c01602e080003604e15004491800d2082c80605242c11a15901200c140c8000380e941645569559124044081c0e0540d59044190800c000800409010f032080d07084840c1200c40da10b00708040702c00040c5041c90000c1140e00260030100411100500402041c40584550050342030b011044d03802080c180080c0c80c52402c40c0e00c0e91a207030012184d9454280c1030045 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 704230440 1250 704229190 704229209
    0x50c01020715080109021b0d091721030405010e0a080301090c0806010f0305070509190311030123040309120b07030518120f040f0611060703091a13080408010c02070b040302010f080c04 81
    0x2110350703d0000d0402c050b40c80b2b0400c0c4000040c10281c040040407030390484009041ca13994841c00382ca10201021740c1d2010304200d40340d40d0ba0b202e80a08281041c000440290b0292603030b582c61350700d0302007440c083e00e104080503010810b0310f904114017aa000022905a6121490005156079640b44d0594144c4a20080b0030351050b540e06003440224a60303481981603a00c64200d40c5441800e9a00307140c280c0f01224124450f60344414045240100c19043c03083d070003406460040000b940d207980c600702242d017203d42a214000c81c0020080c0d800d4060040c0b40e00402b10200c03e040900c8034099440e1541240e003942408420300192003a40c01400b103003a1005080a44140c01003c0c0c0e880070068044101c618880106014041c00250400c2c003c2c070a0b105095005000d150f081d807160560400717400d0008100743c100c1c0c15440081c030041076480000c8d00117806070100000302c1c800440300192800c00c182c0d100f1505441c0410060006036400200201010340f1410b0000003510b401400762030f503002e141c00042c0380 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 704231690 1250 704230440 704230453
    0xc0f0804060b22150308091005070605040803010504050601090b0d0b1f020a1a040c0501030506031507032705031204080c060a02090a080c090f0a0b0d050c01020715080109021b 77
    0xc490f503401c44002000401c9010010014075203030b0100301e80028440609011014030110141e820704074001201c5550502d803051505d003e5541d1a401c540d0240c3d000d440c0c0b05004001440207003803500c075498100c0320900f403501d6050302c0c10030811072600c40c03441800b10082d00e80c2d07001c1c8103a03200c10b0401c501c20301034a00d1940607080c80300002555030500d00f030142d6500a2884040d07408180741c5101c94091500b181014000506060065020f440054210340c0c0511910f4520356800e441105c60b41c5c000c144030341d008140204550380d0f12241d40410342c0303000c286d5400741c502200050300000032681ca0551305520071040303a0700ea090124079030150164000030ba014840c100902410103a00801c3c3c500c00c00c4400304d00e0705469204c6941c0d550018010950054003a101042c008050705800e80c1d40301240b8080428041242d001141f2101030a43c400c44007a40189030303020300d075038050003c2c0c4007401c0041010030030200000d4000f84901c1c018031408649070341c001844120018152101c40340c0304206400c403003a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 704232940 1250 704231690 704231719
    0xe0c090a0b040605091303031b050a080c210f0114010203090d0203120f2d09090414030c07090c0c050a08031e010b0306040608070f090f06090c08090705040c0f0804060b 74
    0x1d80c540050022070020346003403078286c2214041745280b150301c2702c1a0740e4542082c9407902d05443c440000344ca070840c007003000e006080000c000b104251401c40c41041945445040900c4413002c07010068000340c4001b00b6000480d04c0c2644d00005580e4940001c498800d000091400031038181060005c4408183d64001003034a030020615008200018030000c2c00e05640c01c60030300010b03080c94a400160780401080185512a14229400540050140c0509000140c480300d00f145140d210703580020b016000610304100386035a45c8942090780c0c54508165000c08800d43d901500ca40304051300802d039042c08408a004440c10404001e00c9030584010341c0f44550f1269101002c0340c03c11181148190b08018000c0f920030004204101250b50700034090001c2400c018801010380b881e0031082c110543c0d16440065400c0301c90140c08e260885945806900c0d0408960460400340150010b501aa0401c0e451200c0310703034007000c04d11941d040e600d0800c0301903d451426a001c5d0041288a41e41305440080340c60 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 704234190 1250 704232940 704232961
    0x510030f0b15031908090f0301022704020309070b1b0304260d080705070201020c090f07080f070c020108060f0a0305031c1802040b010c051f0e0c090a0b04060509 71
    0x9004036007100c07602ca1003640d62400c169480211200358100c00400d0550000012094800740480840c01008821690507000200342207802406845002d0010f50703d40c0c6001001c1240301c1501d03090292070940c594541000840d96580c654810080d01c0e11000030710942014604200b0408000b8207800da0f0358840d0b035441303503801e425002074882d004104407210303103407040c1d4000401114104c010740742d400041d0384101c0b0954068102290981c15070051141700d264a07500c200091380b04080100c40701442c4c0c20034075002021000014250304c0310104d444248a58150854268006194246040c051300d65485003c1804032080c0512107400c044411408410080044068a040142c8080300002042d0042c440d00c251415240309014140d80c81510344094206508204030b00034045c100715189001a54800e40340c50f0082050031a010000e84481610030141d0140d1a000c0981074000c10b8902d85c03c80000d078a6007005003009005d1035984a841c00d0984883c0c0294008000c000c0200b2098500f404084 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 704235440 1250 704234190 704234213
    0x51c060203010b07110f0a06030507020a05012a0f0e040207020a03050105240604050f0f0103090c0806071409100806030c0d05010e012703030c0203041a0c0714130510030f 75
    0x11a61010401741105060510300018050300100510240f0941d181a90560003458058200d500b1030040d0000c3c1f1000c0344003401158109403402c404520002040b5000d20002088a0050420046621002c903460f03640440007140c2420f0407603005a8403c45440000d685280d01e074801012342d42000c0c20090314110b40d185074120080001ca81d6186800c0035070030440f40f4070450080b0b990066504015a24a0419090b00d48008030107040000e40002d03207403240c503808035003503008501c9a4000d90400201c903510803090f031800c00c1c29565140c02e08046a000400f480da502000d502041102030006010b0750b010050311800303d402501c2c806681540d810f290b0702908660413840d20540c20305410b0903840240c0d030714a03158081d100c2810071103084142d40c12400741c443c2c00b080e0340451005000c0800c0c404001c09070300d00d51a6074403008981d105c40800040781031000301d03480032480382a0101d28001c50707180c06031003442007025410300103090f565a072600c103a844c500383c00140810002044003020806504110b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 704236690 1250 704235440 704235443
    0xf0b0102100605030d05070f080417070603290301140a1508061506030a140709090f060503030313050a0b0a021c0e030f210403030f1410051c060203010b07 68
    0x281d0700601001005a001d48540d40300340e540581c45410b81059451042d03024000c1c05200d00d40d20b00f000d050300c2d11003407090703007064000d40c401c111240c0d0711320380902040200c94000d0076141010b000e0001c0340944483c07841700c0600e259070458898807181840359800c0d80144910b01c0200005140c604040c0107003001009071079800d08040b080710b2802300c1c07001c90000d9914422042c01c1d070003103a072200c03d40034485a030b080070309900701c03003a150700c42a40d000032078001480c0301d641c0b290354441d009480c12500710150382c0707a00340013506030703281000c10711598801104895204003d0004081c07010454500b852808001500180c0900d90b03030810301c1031080342500284021104480c44502148950307611001300e482c2140f080921741e104100d82982d062411028000102d0020700c1c803009030000c06108203082008070380403800aa500c0780044030301d5000303200f00344c00540b44111484807486c0174001c400ca20101c0380076461058614584299100d030103e500180d0480e840702c0255101e594503000d1b40700e5078010040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 704237940 1250 704236690 704236693
    0xc100605010906020c060403030309021507030c021804050601031211030409232a0f031312210930021207030e09060301020c010c0e0906010521060607060f0b0102 71
    0x1000070f00520008100d65203e20007030010745010325580d800c0e802000401c00403a0860342d500e142010310340409014000c81ca000b40c50324103203201c04d4030400c0f00c2004034820700041300720100107101c089100050030a041d43d90150038503890002c031807401e551302410b00b41d00700c901b88400100425440c0d1150050301102c41745044a4030304110204941c0c54020040352014100b0003402041090406220289015029155511840d00442680388030365035001320b075802e40082910100703404014501080346d000c0784261904200a20b11001e5407440e03c40c51050741c502c400c0e107440d1802c040c40041d0101e071030403242140030102c910203140745802384409403000d1400503001c1c04500c8802908100c04a4000503495590b610503e000d01c010440741c01d2010b44450f0b01503600b4403240035100000d10a5105101c582e03140c12000340b400c2400c014901100130209410081c0c18044000d25010850700b003800b501a185040c07240c0c2c2c1c2c0e0070012841e01e00607010702414403810400c0903105001c40d6401005021000e030b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 704239190 1250 704237940 704237957
    0x6040c3011070f050c010f081513020409050414032b021207020f0f0615042d06030b132102010917120f010305100b011b12021b03100b060c10060501 65
    0x170041d80c041e860120706070f000c15401000610982c00e00402640e100b51700801d0009102e468091050490b00b168001140c0c5540d030340188818005015801c90085001c0c100561a00420084e5909100a01e485206541c02071001c020f071410f5907901900e0051804807090001442c2c0f541000f50f0320b200701104480d190140712401040140041032141c4120104130343c64608560403010f21005000b02620080c0c82071458207503140e10110b80e407500f15448021030020840c18154100030302d1910b00602041040c40c0c8541282c8009451601c9004985d0315141803e000c1c01d031503400581c094501c030314005040d10b90066101c0c20706038403100074205000d01040c5004a40d96800310049004030280409401707035100702012050042c4c03507081004c1251b4185800c00010f18141100450007418101c111420b0300041300f6003000d254100141c2000d91012922050140303011808a40c4483d011006498510b4071740380302007100d41312501203402898211088443c80d4880054030301c0281124000ca60000754180c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 704240440 1250 704239190 704239213
    0x4090809190f030b04080c060c03011e0e010308070819051207020a020f060c1e1b030d0c060f1e0504020306060105070c1412030a050306040c3011070f05 67
    0x7200341d01a9201e00215060302d5086484507a41d0080081044400c18010021841500c4003400858010160b041603241c403035042076100d80d104c0c240c4c0401c2500c0d0154400003080700e1102c600700c0c81c1c110fa40140c60070b944c3d00f049040441070741c4114410701c0d48004510544880142e4004010210302c440301d022001c2a403a4002c04a859110550001c1c0d400380c5502c2d00e500d41ca10740f4000a01140b02100c0c04c640d141441c0e0100103180c0210101700f1481600818100c4032411880f1050300124441240584104600c108014182c01c040a001408040e1b40e441e0340c0790111401d1b489501c1001d0032030440c0d004206050055000341ca803c0720b04074080d015440200f0340310350081c41031354851944980c03501c6000703041c10007840740c071107081c0000c82d440b1080e41d18041044400780020800302e0740c1980c0c2c0c0c5590389000000c0c03006603411075442000300301e144000c02e820f0111070441d40382c0110354200850381e80741d05040c9903c060414280c038450560000100c91080100c0302c3e200802c1a41314006171002198036 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 704241690 1250 704240440 704240479
    0xa051c200c010e0a0521010615020309041a0607080f070b0a050402130e120726030a06060207060509060901180b0c060108060f041e060507030203010602100b13020f0904090809 77
    0x2803040c40e801000802160154102e00910952928602400080d08c140e46001199803c42c00d40407d10240c0c10008481f801405c0501070780b1806003140c1d038440100b1032040b012030080e02c00d415018061090205454101d650b005003100c242c1a0481a01280e50910101d0320b40100000d0302c0c203c2c4200c49420304c40202044900600c4240d16592014005100030301c1c13028a429804014116031003d842e11016807611950454921000c4103800c1150716031030803080d06000c03034015070400404d41d442004200f02c1c0d150f00001710340202105445403030706c40702048016100808400c8010301c456914000210b018020940a0400d250070324007124510b07644c1c2c0d070440b82c44000503540c0700d100403881c5d0001f8011800d400000380242e140c03030800120003801d13500d4130000c94209032030020000e034002004000851307042000d5600c0c90400c1c0f100300084444800007814490b401c04640c240030b41c01048105031100000e0a8407940358000e8000d004c0140c3d1460098010f0342702c40e4525104103401c124000c0302208 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 704242940 1250 704241690 704241709
    0x30c150318050304060e150a0e211218040e0309030d030218060304030203040b031501030b030c21030403080d050a051e010605090d06020a0f0206090a051c200c010e 72
    0x200b0101551800381441411a05200e105446035005854003103590f910307840c0f140c01004840016564505400d0502c000c00821106080250f014807a02845c1d41c0c01c1d103000821030140140390003200307030b55580420301104064040612442c2d4424680064803110400c0031000f00140340084050b1440d41942803400e070100e008800213814070f2042c0120628490410900954200d4000c0c01140d08151303480e0a03110050344101c0340c21100c1c401c9440201420350300342c042c9040f007010817030140c00d540d0300501c0400c2803c20b0480e07004d02015101c81c05072401c0003091080342d01454001c0c442e941c2c2d801e003030800017010348400d54042c1411464000010311882101c019200200003901d4425400d910b00b00d8206d07110f8100c0c100056100c03c0540c8600009005840202070b08031305a26560101d8203a050083d090030001080906960020000080000c3c00410070140c0081803d40310880c950142d0700481e5925420301c492280e8401000500c45050030024001c0b08030300c000d90300c4407500c1d4100b100744410600e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 704244190 1250 704242940 704242943
    0x3080903040b030a18020613050307090e10050709050307080601170a1a100509040506090c040c05070311030c0d02030c06060103060609030818030313081504030903030f09030c150318 80
    0x150b003840816070030b00094004060560101a404840041c0368000407510351001d420300100c503c081008000c603007010301c4101e0003050419820007404140c2111036494103181040c21081c02e80d80c000240c0d0341c5000f0a20b40010b001d0190455a0203516040c5041d42c8010030701409007824920708591041800009042184070350101c00080c469070148078002e0501400760804101c00100303240030070f450722210f84175881140103800030300e00d6050000c120350a200107004061301803402c2c10a0729100c41d801c43c041794105541482c06041600c4031000250a5008112000c0c06034050b200c0011103160340000503100c42c82030703031040d1202600c03001d0040d0226842403107240d0204030500c0382007022900f458054001442d071880b901c8a6024190006401c650007603203460603440450f002403010050400c451842d440890556601500309628050b04000203484000c040084502442c00c0c0c03144690102d400841d8040360101525440300345503a40d240d203d4401e800000e15000c070740044400060440b040d4603 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 704245440 1250 704244190 704244209
    0x41d0117150a020d0c030204090c02160506130803030a0912050c10020306013c0c0f0b130803070f080610091703040506040305010605041b020c040b0f040e0a0308090304 74
    0x708040c04100c01109802001c4401042e82800784521003c40350007800114600741ea40180d40310b0801d1410022204d00242c04c45c110741c49070b12640b03045001c44850206036541191519141d102d035018427400300c5000c1d00550b105010110902640b131010780c018001c0188107000001c0300c181650800c40720b40c011080c0350036a41e4001e080350440402c0070390086030040ca062402c0000b1503040c80a50f0b6003125445455080c10303158904807105504e20040d0208031450b146005d084081c05a01c6500c0c0078000858054400d850710008126518076200041c40d050398401c5820b901d9261849019110250204a59012418031320001301103246c40c001021000486407509078419083c103811015411461910342e61a100401001c24240e66a001810040d0304c5000086082c6082c10144000d903030032aa040d400543c5070740000319102e038000c140e40e000040706441c0003813085400d0340020000007401810a4100740b401c05d0481c00382c040440c0c02541c590107a12400709032380f14010b00da5903074031444c420012034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 704246690 1250 704245440 704245453
    0x142a21070f020409020909151008070b0d090c0e0f0106030507021b2716050408120d020d110909070221070c09140106030605040507270b041d0117 64
    0xc4001c200c00c44202d00150000580ca003c41d804200028000d4031044801da00125010b10f1110412004c6584007a410031221016480d000100e95104c1e001d005212918030302080d840c50b079510b0399100d21310381070300000341c00c07c42582c42c8102da1a4200c144da030b010043c0403079800460081d0007801064014070307050713000340040d500e10700034a4120170009405552203108180b000071140702400120110034400741100c0d0150403e0412800110400c2c01801c0501c8000c1c0820401058082010722400143c1400c50f940d50301d404076403000a202ea408003820300d5241130b031080b14645481000d4052401e090368200742e41e8955150581c3d403454004c40d1001569100300c0440c081c003664001a00030140f2a18020180c19280d40800003504d80b0200910321103a052001000199458091140102001d072003c00040c00d0100d03008001c244e581130390100f461201207030f00c0042c0c1046440c4c000104864600241c650303807500102c5004241c000302e002601401c100000c1101c0300d4042c2071500040540004109 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 704247940 1250 704246690 704246693
    0x507120c1a04031103190e0904030c0b0901020415030203060f040624020a0210020a0b0708040309053d0e0f0d020415030b01030819020f06010501142a2107 68
    0x9041d0041048042000e4030241018581c000c10103800e8003030070f10b102080d41d07200d010001000100d00404540c0309040660a010120790030550584c0b025410416039990b41d9582210a03029120ba07030300a0800003440020324881c982d069000d0b42c05031000703c6141c0c1c03100c00304d40f04102c00e0f1000c2d401026601c44102da403040c041c550b50042c2003181c0c00d01c1c1c0155a00e041c40c50300003845800c9400c4480c400343e0403a083e000e04204e042c0c00d403a6031003980d909110104d801d01d52001080e80101c1d0182900410322100d0503e44d50000c0b5020b054604e070862410400c101102003402c010201c881d92400101d0a1421182658a040121854501030241442d098a8140d400704400740003040d00a98840b1701c80c0f000031010580c0c1c1d80126010f10700411b007a0f55640030414010f10100701d5104140215040b00a40004620000c42c190b41107500910b0590070716a800140c0588610802c031000c200d2100c40040081d005078407156011540c610030080c0c0b0034541e0381c01940b0f80300764004039030f1100c00f0400b0840e940 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 704249190 1250 704247940 704247983
    0xd020403120c2a03020a1211100f08040f0203011a01030b0d020619030207080406030c2a0f020a15031a0d080318010209090f0a05070912031103090a03030507120c 71
    0x1401d088402c1c03e22a5079070752a00404c0300d031060b94000c0713070f0603030070510a040501c160010002000403041e14401d0310701c0b0a40d2001444000c080414004010101000c2400c1c0180700100725401d0381c00070000c1102c241c034030f114a640c8407022446540030a007840b0220310503140001a10800d80d4016200070324000104009413050640e0281032803d05a0a0100e4008543d01d140030f4400b03813009031000541c0050807a8081e015290101000018444180d40c0c02d08210b513010b048803045600200400001c503081c4001001e00307405d604035000a000a030032485240764590003a00050036000280d14002541c807040c00240d0800d01c2002c2c0c1810000c0001c510175613a65880300c0d04c420940d40005042c004801c00203688070f041034402d9898090b100d418001050103074070a06402207603900340f1444061519040c6594a0040070000d03040c850768425201d90316406100315800e2440082290003027903101e1801409035000a04107441c00705000003031506d0f8500460000321407a4012101c0c25030f0000100404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 704250440 1250 704249190 704249243
    0x80601020703080f040801060f0e010e04021c0624180621060603051f050f071409011107060818030c060a02071b0f14040b06070b06150d020403120c 65
    0x541050313004020020308034400b0b102d440702826564a100c9061442d1003207081401c1d1040e001079410021070307400d10005a03200124520800780b191004000300c0c14501f082d00060518842e03460000200d148420000e41250421a040e51006440c0003000d940b410751400444009000c0c034030b8413a400c1160058000c00004c40c0c04401d520426010a0a507181c0e554031741003241c00c00104404080249162104800c00d000d41540031740b080140746128a84800e00404565502000c00d550b804000b4011300144d10512038804150072048c2211951a071740d0b08024000d20b01100c40d000c0100d540c0100a0383c5a0020044a4004a401d00280002c0d1206140341000307512a44c401c0b1040c184200c0500e06800f00f040b035081c010018507045441540c0352109010014800040103440740d854a142300002d07556a809840c00a500b18045102c0d42d641c0c0c0d40400e41b2840800e0000f68440c5022604c0e042030811500204152031003501c6001c02100c00300e07810346148000400003000010081e50100c200301000814 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 704251690 1250 704250440 704250457
    0x6050a0c02010c030b030a032a0b06010e1207030224030c040e091b0f0109090c0c060f020406080a09050307170d140603030703230a0914030c01120c031d0105070206010608060102070308 81
    0x9040c05c4109c039112404e00741c1000c2c00840d60446a182044095a041f00b94103444030002c1d03a4200c1d003085290710160b19a007460000a2040c09800c1c0100350400003140341c100841030b205201956824143c200008a030401e05ca100b90180e564800244d06220200d4400c0c1c180803521505003142c1540d504101c03c00d6403690007203040000ca03560020742528a8000e03074201c41d4103034440b01c02c2056a401c0a00940e102038594400882c01000104102c0c0d90085240c0c1e4484da015030009000b035154039100c0d0841c4030b1200080d000040c200c000580d6401c6110051001382e0441340c0420005580c4941c1c03d5205004075109903150300f044c80004040307070280c11b08503a03a100d40307042c5504803494011000900c0d003100b01038200085c0009410710190000e010041c0f000c090480080c90300941c0d1900080c40104040724060b105a00c2d00c1880012500a40140000014040003c1c1c1e5008001c04450b000b40002c0b03c40c200184600000021018043d80110303018a01c1039018020050031030b00c45001c0c44d03100c0c005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 704252940 1250 704251690 704251727
    0x609230a1e09110d121206060905040e030403051203010611070308090f03210d050a02040b070213020c24070e010f0c1b151101020309100b03030706050a0c02010c030b030a03 76
    0xc01807580e44d1a00390700060303105d462800391110210790000c1030b400c5204413076500289080410320030710760804c0c9140211032045038081081d002501069085005d1680001c05520900750007420000d00303507000e54144c4e080c6568502d0382c1c0000c01c404583e589c1e194403010f41103100070007220f001030602e60500b40c1c0041c005400c50309082c0461100c0c040c842c4000c0700078401010041518181030015004181e04a103000409609042c14854620945c0c8a4000b0080c0b1400b00407242c02e1901000340c0540d10015026020741d04030751040c0e099214007208498107102962010700005807198000d684a00300000f0680d204403109503014030036141868060410b0704d501c00b40d60025105241c84062507000f801c0f0368540d203408030107182c038060b00740310011580c1c5907181d0040c0200864144006110405010f172000081010784071000441e05500c15200302030a00c9051800708180c5c646550007d80c1ca95109a008201d8104114030441c00c8525891015900d0340043c500d40e00428410b840815011001ca107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 704254190 1250 704252940 704252963
    0xa0e07051605010c0e010201060f0620010606050403021018060e06040e0103152a05490b011407140313210b0f07030609230a1e09 57
    0x75102085505a94044650f41c1d110090144030341c1d403010318020844030070300003408402d00b000303002500d402690240d001000f200040100010031092011050221032000070401162a030074024001ea005000a0380140c1400300c1e0282d84034843c2c00121004510751845003060b0382014422503c1c141c49a136001c0e4040420301003c603815100f01080e030300840c80382c1d0b4401090040c40342c43c9001d64405e1038980980a0810031110198905042920305103005440e285549400e050754000240700b5000118500380031340c1944800c2c80b04283c64004c0000e565002c0705a41c0c08190b020302003681d41823044030340081e000c2405140d00c050158060810244100f81d50340f541d031011401c4a14503000131004850342501500e003002500342d503240304200aa04445900d0000c1e035141c854031003c0c031010f0045444100c6100010703503840c1c881c0d40900d01510402c5004c5c000d1201417a01100380c1498182640c03031017151100400d0007415940b2a001d83c544241690a6110320074075040c5c07009214900e819a140310341c10 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 704255440 1250 704254190 704254207
    0x70e0301060609090b03060702030a0e060d050711010e0309030c010309060917070c08071a0304050705121e0d0f05031905040609110d0804210c0617090c0a0e0705 71
    0x207006020203807080d0340d50300000c2c0f440c107502c1c3c1c001e94504d150018080d80089040c050066404022901c0c84005410216102c001d0720b4085504e0384034a0301c142148034544018403036410750020146a0406009000303110050703100b440c081e100d205190443c0e515a1001c46c05c0c07549940a41c02c03c05107640aa040091112002e0701d400b43c850320700c032180c0b4401040000703400c1d0402524540c09000340492500401c00b060a03c0307505000215000a4152000746c080005002c015080040c840a404080d0450b80010350017510140e64046400034180b5411410915620111000400020f0702d01156280c0844141d004015211544082c00b05a440200b1690002c0e079101c1e00d00500d4000c03480749200103400c088078107000919900d85803040384140c500030030034008102200f0070f48040e207018400b00f034407582c0782e003d40c049204894403005040d030621f0748000844941012011340c7d10400c0084100c804e1f074034400c04586076040313139110a602002021051201d82c810000250784280c10342822807425621 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 704256690 1250 704255440 704255443
    0x70e1906081506010f020c0108040602031f0305010b1309020603040221030c1513030c1e050604050d0206180601030b060111030d06050a060314040b0717010806010609150e09070e03 79
    0x10501202c400b1802241400b02d41d50340f0150709080041548050401e11800c3d1000920314038020b840689001d8000c4081018071400c00ca2a10343c0300c11004070342c10081e0303407494110f001c0c01c13070300302020710038442185070440201c0300d0f005148090b80e0050885195942d981e081002000d50407501002e0170340100e501c1520749d10100001c00910207141d00902040e050300c0383c40e42d5400383c01000b4989880c00b0b0500a40045d410001c0c1003038a6030320003070b440520610500ba031000143d01c000042c01e9403103807000f4081070040c085006007180f845a82903c160b541c9401c8811554081c00641096983c0600300400100e45062805500210145465038072041c0e90100c842c80c6030004200c510050b0303628001040646092182e54008061b07600b024408055013403529100004000e102a00000619001506061080004c1c2d883c1200c14103101c038041d40c42d034541e40e5a405007401600c01051140401040e03150890212900301211941c4501814041405102e00400c0c0505164180981c4502000755982c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 704257940 1250 704256690 704256703
    0x2105061318024005070905090a2f0306180105100309110901080105100510020309060d0902040603050d0215160e031203010902090108130503040e13050a110f0102070e190608 76
    0x400d0250040d11803c03140c0c801080391400f50002060292001c4104403541340c0500d01c585c17111065000041a80d6804440d210f02090718016119828080c161452040150740c040c5008120035129503844201c09015008410028080c6590003100ca98030750724a503119030402c0d9101445143d142070702035401c20201f0780c0d4100070b8100f050103035158420412550700c40c080b03000007050100c802148845c040703800603460388240080b65028000c00648603000e142039070007841711564090800c100c102d0340c0c2e00307000d80c0314140403603000014040c00c803244c02201c104104c2d141c02030f280410032596401c03584500743c40707405e25602c5882e054000d51422040d520596005940200210392001d680ea810b004001400b5401c0248920032940c0c0f190000004114000b0035070b01580c8544403c02020740303507814a10301403103400c40b0041c03031803086d000c1d460f0821083e1704100080d00400d44002044191440040e41c0b0746038a401441d0164202c00001100072004c0e0441e080b841605403c006401a207800d101800d0a4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 704259190 1250 704257940 704258029
    0x319080f0418050f0f06280506030a0903111204090902030c0904060203070905120d0f020f030c070303090b03130b060d06091a0f2203210506131802 65
    0x955a07420041002c0d03c2c889090f911011058121007207143c1000015a00c16512140c481c80302035600d0841d0040c7c403024a54409854001c08082c0c5a1030100002400707082d2108080380040c10004825034600310014800c04000750702d46072a410241841075030700052490101c183c3e81071094a039145070b541c4441d50110300403802180d0150392441c0c0701001801c015403e90119000e0120110080611280030910803041e400f1842c2c9580c038401c030b409049140c0601410300c0321240c000040d00d080d040b03000003034074806c5a00c642c039008050313a0340d0001c42425000c2101c54191542d1030511a00010300404283c5c2d511010040c44d041404026403102000c80b20f80c20002c1340e58009000c4081c2455100c4400c0c0c070b0780708401403150460303440c01504e241681e402498007110320f0501e03940d8403c1054081d0034020084452604410740d09584507403040302030300d01525070740c0c0500c451003041d002e0b0f503040d8062404101003240b95034084c5103141c0c0c28404201c081c2ca14100118034012040e03190300d0109201c0c1d04184 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 704260440 1250 704259190 704259239
    0x2061023040c0e030c0a050319060b09010e041a04050a0204090302030f0c010f110903071202030319032a0203160204090f0317100e06010c02031c0315050319080f04 72
    0x9007041c0f400c0c0b500c0e1480e00342d056442401900780c1003216941c0021100b080d60301110607407841004501c2e218000d030058102a40e80a0103040000c070320480c0d04100284100d00a425003200000c1076101f44070901001d85000e84181c015811150140c1415000000440d01c00e20441b450544141036207045a0170110b24084665120718080c0009001802161407070081c400e5410b103840d030001c001a580d41401c0c03140d610300345411000c9106550f41402510208441c02d0741500b00103042c41e2008005007012980144110141e020030803000c40e070131040010445a03a0000e40ca0040c40311402c01031200d9514040340e0007902c07a05803030005003641142c964604e12a0b1121200c600c0c10810b4054440c2c401071802039502c0c040304041140da402070031143e0f0072400a0808424144041c00420f090038204486698545004ea02e22032055605034801c10b28070003401d9491500c181c5032410192035882910040e00c44065024990001c54400340013031038450b142c044514a82641c400f14094503080000319103440 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 704261690 1250 704260440 704260457
    0xa0c02010b060405060714011b03020a030507020a03020601180e0a0c030b07030902100302180d05161a0d050601020f1020091806040f110a020d02061023040c 69
    0x51540900441000e540c00310380300ba06090818000c01c1c2c684c00b5134940644a5030000300508101002940034030000641c908074011602e0301d2120140c01395105c0c103013150010780342a0025031560b00c085072100e44103506501600316079203001048441891000d10a041c083d5549000c00d80d200f004202458402d0300c941c1c0c01c480c04603d1410136400034000101280b09043c2054078400041c2c0d1000442c403494280f9050040e1118103581031a4840000b030801103030440c10b03c030845410710000181c00340060b58030011107000300740ca8000700c6082078141295503c1c1e000050110400404ca15045598003900600c11100510203481d98145426102d261801e10b43c3e694589212450020220305048081e40882441c5002ca003840854030030701c124811040c00c2034400c3c01140c50384e03455400201140c0401007003030000c001504502d40055205640d560094403030f50380304080c264001326240303104031029444003090514091804003551054030854007000c6d907845a404045e50760784600b20000036544d454901 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 704262940 1250 704261690 704261711
    0x50303042303120d050c070818040f0b030304030b041e0b010509010b04060f030f11040602060612070f030f021f020c0307140a0b0904020d021b0607090620070801050a 73
    0x79810030084086001ea00030310b02c040c07140c540420842c0c0041d49501c800103840c1d0b407103016003200b60081c02e40007000924005015102c02640c06c02d1621520001c88d010000410b40003015411140c02c1c0d803195400d500184030130000b14884401d1168490301803181d806030204510640d20310420141401c41e1280300c000014416810800d110f20f014140c4102c000e8589410690090b0100c0740a45082c02015150f04031189200b441e0380100100c0301c042904103444545414019440c0c0004a031428050005c0d440613000309000001c100c3e08a4240b500c41141842c29502c44007002c0005c00d80503600200341c1e078030045020a503030015035a218044d6000c0c04080c1944c104060803c60140d2025031039104101a48005541e201c8003d0100e44400003055520013050300810040d004034100344100c9403003c6000f4581300c001051080307036441c2c90020340e80290f85c2c001c4155181c040a002c1d413000203070040c40c40384d61301510300803e00c070103007904d8101c49281fa900d01c0d80324250f0780212000341c011078540000d801c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 704264190 1250 704262940 704262989
    0x9060c051b0a030801090c0c0219030516050f0907110715020d0305010e06040b03070506191202040f03021519021e19030f120203270a20010905030304 66
    0x42030200020050048122252002400c6131018000d401e04265202c14007a1194019604546425400f40c58007200207a003501700c04180541c2e11080d6242c1c01410a281084100b2407080c0050703031402840030060341d045400b07004010100401e1300060015824030344540701d504005650061483c00000c0e22030410000000303080051682280c0e0030316042000501600d4610034943c3da101038187c03800205848030000180c60000b140d848031340c0280300000e01108207501e2107600100c0c1a1341d510f030020210642d420320000c911840c400c11202c80450203081c801450b0001e0130001c85184d894000f81002c610303826645da140c41384141c890250b032062600482c0307a80081140528110140050520340e840f200b07156030030203408400101004480078640c4e10407405034008004c0e5580001c0115102e203040c800e484070441546001c211100301c80380841d0f03010f900000702c806407a5401001d00909507010f4106905900d8a00a0706052222560003c02d658404002904c01400c81e940085ca040b01080c0005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 704265440 1250 704264190 704264227
    0x2041401090803071a0627070f050a020a0206030402042703030c0905031c020304030b0a36030e0a1a030f010f0501020a152c1c170a09060c05 62
    0x401e01600f081c0704100224101480070450340840d030300010401c0e56440c0000e000004c401c10380c44000303003103281d07021908110b2a07403c610030445d54481d000f950500f04030646d0341d03000f00a01c00700180e000c10351640041c1000009140c2042c0301400104003c000d012011010010034544c0c082c8600c03103010301e2014075905010b50f48102c0d005003060080c2d1410038001ca5199803a40180f823000d0303c0344020640d402c500c00c000711401150002c8400c015820155100304c080c10b68440320900351602506220701812221440c0a02c1040c90401c9181c841032a940c16581000d50a00056001c0d80480c40019810841051070358003495601c4025030b2440e05c0d15011840780c006811002015441c41418001d80c3d80029074809541d422820004803e1014044007016102490038900c2c44010004040206150140706851145048042d0b0359600415000710b0415080e00f441c00c80090a9180c1c4880c40c21384080500b500030584086c0411b0500403515402c05544580248100240000a6100540340800701c1c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 704266690 1250 704265440 704265449
    0x3180803041518081b0609150a1419060b0315041109030a080c0a0606030804081c2f03030720030424021e010f0b09010f060e130204140109 61
    0x10804a40e0408256121402d0a0310051410340009070036903011000050341c4240c2c5c120310003101c11034030380900a162149072514500c1c10f12494100403458130701d003500520000c608000480099541d0301c0c0102801c94040b44044100c050783c2e0200860300b4501390380114468001c02070200c4c003e0901105010441c0d01700c2403602035021052042c1c040e15500401c000d07204d540c00032501601c034150003205600745042800005d2a0600d0810004100228040503104603007220003074a942031250140080084076903a000700008103195054603200d6645481c00c04039003644040d01d5103d410010701c962441e842583c074000400e2050802c02142c01d20a40b146400404000145040510744920100c075108482c0c0903020090400e0100c5890078401c0103e2004201c4d03400a5108080007044000d00078411107881d01111401c0c044c20440714240b044289040307030484c81102c10b503145820800ca5010280318043d5038040e500c811030702009800c5001a1010700380e4202d58602034041c04001600d0301120703502 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 704267940 1250 704266690 704266733
    0xd050903071208040528060f0e0103090515130c140f0607080405060304060b180402030c01030b01171027050604050105090a0c0e0612090712080403120318080304 71
    0x54580000d114200b0b44040314016211520040946d009201400d4060246040e41d254900d100103842039108444100c840706030307100d591050203050011010b441400304050043e03444910403580314801c4140c42503000700707981034600b102c0216903250b0040700055800750381488202d12400341c0310728180210320f070860821640649001c1450f80e0b034034200c1c0260302c41c05102d0354003c0b00240901146400588204a0041441d0590074004462001036041a18181c0c0640304034070705000d035540240700da45e284080507103c070764580b000080304602600c801010b00d6808004503400041e1010b001162203214211080c00b0350b4030000c00b81354401101c0004200c01d2080381042c3c01000f213a141c81842075001100000d01044030344007440c0039500803030042c13034031a0007100004d01c007841840c0908509001d030309104192040035550313407031010b9031880402c00907086400401003040090701d96801550f8645860401103018600020310021000d41d51506444401d400000c01c002c021f000503410029080700307203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 704269190 1250 704267940 704267969
    0x604030b06151c0e031e0310230d110d050d08070207050913050c210c04060308032703132402030d0c02010906020d021911030306010c140d05090307 65
    0x8450240c29901c503000400044e40e40e8120440e81d030000c0c0211200d00c4841034000c1124039a21001e11140d90044855640414400310302080d004004d130901494030342c40500500002a59504120b00c91685440448d90151051030305c040649510181031540d902590241901c1054844040c0c22248020301a101319000240b00703001c580d0f6007201c1c9541041c2d003200020034014051600c2071074070346c0307100e078840c0d000d038a5800641c00141e00c080204900e0400a0030b0303940880c409400d100603100c442c0801000480c003030000071400c5160801c400d4070682248074102101c50048007150a59010b450b0044091008910501410040140410200791054503a6024409551009459003d00d1410f12101c0c1d0b00e0304403c581e524400d401484d0f01c0b58121008554554004540b0310080d880404804540400c0e007100541d03950041c6944102900d1040146155603112001103e1400d503460f8102ca001c40031a42e403500ea030341c0070040c195881c1070b5a151550303904003074070170186070841a5101c0d4003080e119a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 704270440 1250 704269190 704269207
    0x209010912060914060a0c0509030604021c060c020c122103090c03060118050609040b04111203032a040b0409110415030204030611071e030e0604030b0615 68
    0x6090001218804080c9101c0d2000a00d0410050481d407403010f00400010070f0818501e0401050182c010300e0ba20f8001c00100d0308460040e03910340a440207041e0305810460018025050142064581500e85446100355108582e91303002140d02200f642c90059121215880c0181406074106820050b1030000304410440c02865500003000000b50055500c000300c04160000b1003080084a0200c00506a6a5641c1c4680307401c0c4800722003074400900182002c01255981c10b118000e11b001c4da40020701807095640d9504e807880142c180d20040d9070010b2094035140e20310302060003e9401162a1004c4a81020301c05242c0080482c401c50320b6241035404100c1004031070031400c00c58003152403000f408240407503180702e09034590145910441402900c003401504d120b50550044c015244120320070000c910a03203c2d083e0b0a8001c1c02802080300074180110007a80e5210410803070924801d14100041301188400324040b071700a41c1c0210754021148050000c1444e1501c8500b980200c500c00040c01c02c04d80c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 704271690 1250 704270440 704270447
    0x9070e0c120f09032704060321030509031b0709061403010f0203060d11040902030f0d020d030b150d09080c0a0b090a02181803040b0423010f0e040914010e060a020901 73
    0x6600c486010038903102541001d4a030100c8002c0d2017000c004004000182d940d091100020a17150414002d00d4481c1031181c85413406885464020428000214105008004201c0c0340075503202e0710ac071842c030800c0c900180c9114580524005402625000c21110811505141c21340d4617102040c5c180500500410246031074212140c1c84042e0402180180e282c90035001c24010018094040c0d014010384c500e00c0e80041e000100100005456805c48100869408c411402c50740042d0089510155401c00182184924405424011001e030340025010001e9500c1c0340b40d070341c08a410f030101600710f00e000d902400301c1d55042c0d075480b41406000e8214900ea9500055800208002c03100c1123822683c003040144031070b60070500300c500710182140d039299182d102c81c14135504984540c520080812001e02c01a500c195511751b5405010f03102d240d00e070208403a09a030180e00d4112a65041580c58900300003050380c280d482c040c0030110100000c0c030745040103505030410301c0051080202600411010f07402d641d2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 704272940 1250 704271690 704271697
    0xe211b012c0d2319020607120c0903080f090a09150807030c17100e01020403020f01020f0a060f090206190e010528050c060f06030628020309070e0c120f0903 69
    0x100461481c0b0003081c0300b9034038400e0300500f140e1110909090105840c1300b900040d940e401003100342c9550010340183c49542050f520103001850018030101c00070000100c2c204003500260030051041e42c20080c40102007082c42000740d00020b0b8a584035050010351440c01c61121010f07141c140050f00600b0f0071901c607202c030f80c0058442e420201850a01e007403111101400044681a40c0d4003050242030b1014441134043d40050105902c6440040190603c139030000610a2090043c0e20160070780c1c0b02c0bc0e03116880200b2150503110780b800d46404d8480016642c51000b446069034070300c400008015007450051444c800440204e052100400903103000880300460700c01c0d0341d0807080242c051500481001ca03958003641c8090b40c1e29106807000d01400c1e00c00c2511003032103828140c1c202d4085907500d02c0701300f003103282100c00c00d030100d2282180489209050b07001158015144803c80d000e0f80c0c2e450b4410b030350030700d01100d0020ba1078202058440e81202c1800d102508031040842c915014100340d0041e0351a0710 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 704274190 1250 704272940 704272967
    0x3172e1a0c0708031b060a05090606130b0310020301080c030a020604090902010c0b04050c030f0c0109060e0303041d0f070e10050901091806090e211b012c0d 69
    0x50216650100620400c10030780502883d4042c0e98603400c0700804c100040720350941c0d0381d69034020340c40024604892803040c03074498020b01000f0304031074842e08140316240040d040c0c101c43c0e00b51688039210303103610108040e98500303161034401039896141950707050800c64588035591081d00607808620141ea03039441503030249c4900490001d810a104c0c070050360303840c0d1140401030101c0410010842844000310341c4a00b124010b80039240402101003400b515025080101d6000c12003030101405100e11030500704c15840e0026044a1402c0e0b160b0481110380d404c100c1e12a5480c00f10707481000040c800c1801010707002910b5090825241c00700c0d10015119200a805080c10001d0101e291283c0f44c5c450300410005041c0607400c215030081d442a0f18018000902030552164107001c24281c6280700040c06086003119803005110005a510311750361140d101b40004105100c0200601c80441c00070b204007010a8505220000703a03107000c00341081c0c82c51001c004000e1b03d8000c00b80d403284880c0c104141c8030080d07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 704275440 1250 704274190 704274239
    0x22080a080304080f09030601061125140609040f061e0f030b071803050f070b070503030a3303110306272104030c050a03030c0f03172e 59
    0x2c081d03851307124005000c1c441e115940b52140e03000008200b0380046100c15208031020640f008944204090b0002c418014103100040f802441e040081c1c05400400103207400c8000c0a841c074184442d00058251034043c100e5900141d6a000c0c00c00010550032804035138440082d55903050245800c41000703400001c0e21015103c07280c60b10000720784910852518000364188ad80c4441e00c217490707040c080c2e0380d44814025480d15214020002c0750007400a000e0703983d9190f01c00300540c6969105031068020b00001d0014210b20000c03040045605030700164035000040461400c2c056280c51800e000840c4902914524029000081407060102d1280e540144d803012002c0103901c0c0d610054001464905101c104468010140e29500c1884090340004d008903402000344403906516802000001e4510788401004a44040149800100d24003414516180681008044484111661070f4004000c55440304c50780d40c4103052914070100c000420001400b03071030710240031500301a03042c40c07d40c80114a0f079500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 704276690 1250 704275440 704275447
    0xd0b1e04021b0303070306030c0807030c120501090803010305030a09091a0d02010509060c0c190612050709050a061205070305010807030807020301091a01090b0d030507060e01060b22080a08030408 86
    0x241e107042c0788030030751090040441e95249450040180102003a000072110b090b1100e0f40020400b0f00041d90324192608001844046481d00b455040c00e80c08038002100c2070b5480e0000c5c1c20105180303074044c2d8001c0d806039000d9552111300e80760041006010f80c001003c82c5160060000e0061250b503ca4030a2140907108a00c0800e91400140d815001d80c148040e03001800080eaa48440d0b000300d50004003507004d0724511031f14507514040500030000c50080d000018000c424042540c3d03241d410081d005841800d02d8000c82d0380340e101080c0304028680200001c03800b80650b080d0004072a101e0545c3c40364480c40c08000c00e50420b01e005489403001d03c4042c204040208454056540c01e40c400d000e016440851949280c0c1080c1d00a00307580c03800d01c00c0040c1c0711301d4000b01000c103003414402400801d900da0b03159441c0002c203a484d1001480d549490701e4056603110720108a1551940c01403400d410038051400d640b2140103c00c01805040c3c0c0c000180c2030700203440d14800100e00b43c05503030304281d00c40d50f820307207 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 704277940 1250 704276690 704276707
    0xa0305010b042111130b040501080c0127050301060608150f03070909031e080f25080c07052d0c0303040e18070e010501030e0d1e0203070b0c0d0b1e0402 67
    0x10200000442c11760700540c00c04001c041c500141d8400782016000780c6003888180e0361142c0054480c0c0c081852180850b441846c2d214074044454285075650b12140c241c0e0400300d4a81000c41c1c210346060b08013902083d003400c02c2c808411201414106008021a08054070940d003c010a454803000c1c03043d40d081c00d88070401501018056803040307004503000342c8400002c01c40403c00030241501550b802c0e14002268000c0342004421221003201004003640c47d110484810300c00302d40c5890010005600180f06200d100002042404103d01d0402040a00004020a90020545c9400c1c4042203802070303010180d07450300d40c4c8000c820349049074000f6900201d1035541d03141d01500742410340c1400019009000c0d02207802450f07980c0e868180c400030380c2e041001c00f100481f4107039203003112151107011606c5030000f84114503003102c120714054914810b5904204440e91084600e02055035000c4a07540082854103a03455544298440e11004440c0120200d880008101464810014180c0241c1d00040e02c0311 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 704279190 1250 704277940 704277953
    0x6040c0503012a02100f0501140907091203110f0f070b090a140409050d0906180e1f09020a02011e0513062a08150f01051611060f0a0305010b0421 64
    0x19050016190f040c001c0f11b59441e181742c02807200b40204541e80b90b41c500b0702d0103281000752a280c4100304c95240c1121040c189501041122160740c0308030100200d1016000c0049001d1105400620440300248560007251100c0b40c2408a5600407003404038080c0b24140302513a0724007141c03049658900c00f0948801c03800e00070402070421a5805071407480390070440c80380b050748244664225511907441c0031608600c44804000304c0701c41c1c8030f0309030300030505400b041303203030004000e840f099000400380e818940b591000403405036002a94841e0250359140758104000351901035400368204034200c10031a500d07046030300045149100101422880d03a9001440c4052011b00c0c08803025509000080725550107160020182d00040312408611241c207604084241058803160100f800140c442c6800d002000c00f240e405101010b03c143ca12000d84401041da9440c3d980013004c151019080d010740e030340111a000342c03c5e82d1060f484a000413204020401102400b501442c0c40d01021101e200c2c0000b819040c0103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 704280440 1250 704279190 704279203
    0xe010e0a211b090c140403030f03140108071406040e0705180a0e0403031a06030109110d06060c02010f110a02010507030c0c0e1e010b181801060206040c0503012a02 72
    0x1c14040b903104100e81500d1100500c0e200f11102e02d032080c4440c0d1850304040350f48021540946403001c205000600c0060b02541e820185030100e46800109210146101c05d0030f007000b030b481b6440e01d4000500c140300c8117400e0384541600920940782c2c50b00d0301d480c000c0d8515420030f00501000030850007054040c1c268144800c5420075040003070100c1c0301709031070f102c0c45004584140c030228080791034081609000303806510900e10a200040c2410700710707840c000320380c1c0203001503020744285e60500f085183c201c3c1d01c841c402c0d0b40c080c10383c680d100d24100c0a00c0c400034004030441e5840e1410b1120310341e031410305c060300007038201180c030350a181c0b240c1c5900052a059461035044800100301c092004004a00ba16928823241e00c0703440c06401103c0d07190720740c07181543d841c2400e000e188500c0b84c041002984000c8819040c510280b005054500070840720341228140300000c0e0886001600301505202c11303c1084104000a024110006c1000c03e000c1650b0050303828030076062080c0824800d2084141a00130f100a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 704281690 1250 704280440 704280443
    0x306240305100306051e1302010c03030b1201060938010e1807030e0d05130e040c12060b032e0c020106150c0521031302030316120e010e0a21 62
    0x1784144d0405441c41c500b2200070103501c1600d10900c070005126070046060200b9819010703100c5501030b803a10f880c101c0c0500a851035064000c00424880b502146091251200030301c0640000200e410040c980362140215280801c4094414800904051058400113101d403940c00d0922410910300c0304042500c00700d0259a4406910b04681008031a54054110f40c2c80b021401054916460b084001940e243c05000e81104429410800030b00562500c6981ea6812a000f1a44000f1140c0c3e2404c62644182c0c1901080360382a071a5a80720a16050400500c0440e2407880c1110710003080394400006070304d542c0e011040d0f60315110914103a4180c000c1d48800083c1a8242d14810003030901000682010165042120316101e40c081d446007081891111190716900d111a0030302e1502c594810003044200008141d915020810554480515810981204d28410b54025074079108003240904940b202d0480c0c81d05102041c0307603040d91552140640000d5400008460305144007061900d214003403400300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 704282940 1250 704281690 704281703
    0xa050402030c120618030c1f1404030906170c0d05060a15020705240f07051203040c05040c080601140705070506040e190b0a0306050a090f06060603062403051003 71
    0xa00f0000202092240c4241c0300310b8005286000901c00d21940d92241c5100581e59802c1040e18100d21040da60000d08000c0c0002e50124848140482d040d03600403041c1d03011400300c0d0340040108251604460300b0301600c90907241c81c0c2040c0c500070340d21040a2003010340c0444400c1e901c0b400203a40e966201004409025001c2c0c04611052a4040180d0f98124600a862107403504a0f401c4101211501e40d80c14001c0e00411403904003030300c2e422214240d42042400f16503500800c01440c065040010207984114020006203240c00d2410060208540c000d0405a04000792002007116590b08011034110003101070140702d41e1404642042c81c01c000058124603804000050001030245c02c0c1d085450040c814401c100d05103a120b11410360484010f040501d40069101c0000c101045003580310540c001c0c112030b07010811107403544e151542c80c00c115100300c40040d030722203052144561511a5002400344030021200001d17080d00c1c01c0803201c0d05446520101501c9800180311241c455100c00b0003140d0045 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 704284190 1250 704282940 704282959
    0x1b05090603070806180f07030b030c030a0b25090306060603020304050c062d031f061b1509060f05012108030711030a020609010b0a060c200a030c030b0a0905060a050402030c 76
    0x42840c1600642983c00c7e1001070b0800b4400e1f060740ca0041000fa800d0702c80240100400503050ba1015020a0300400c051183d018128514070803252660346000e544410f03540d022079144c00c611303203070301150802c1d004a82003510500402001540002d014442c0b413908491094548003d51825403107900d2080c410300004041e0080e103240c0c85a94000745000300e45407640d203030341d280c860b0600c00c40441c800d11030600020f0006032410300710315041d071143c003e145c02000504480b42000d020301d0213032142414221042d030359a0b907410105003801d00c51280540342003104050b04850044035981001803001c000f403d15840000410301c4140079644a0100704582c5043e641c507110303d4140070307481e0802154400c1c495402c2801d04036151500c3e107c40b0041c1d03403080d2108040da00301c94858125000740d41d041c0d446410582c08810f601c1c0d54900d20000c00640c8540010364005056240600b02018050580c44080b8103120b01c0900185001c01c040b42c0c0003013848000107495840707000181c074102012170305079003041016 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 704285440 1250 704284190 704284201
    0x308190e010c050301090e0a12051312050d0206010f08030a120e0109080301090b06071e0f150f11030105100f230a0807020a050309040e120d1b0509060307080618 71
    0x10007445c1216004142001040c8207103803802d4640c10300580041688680600500d5014001c0000d48030008840000800054442880c0380c03160710303024426100d5510020350003480d56410845280544800c000e807441da40d01c1d044500c1c0d62401038078418000d1055034140040f035403059a200e0724403e42c506009000e000054100340115510a001e000e03510303401c1203140c0106007009011600743c0703940034004041b2812031031240b00c611712031500c048545043c1c1030a40b6001c5404000d2080b00705041d03400000d00842c0d052951000c980c0103140c2082012418070040142e03035103220003141c07000b5080c01d040e050100e2068044680300481c405844100803c01002d0b04e8407406030b4003400c1c490a042d110410585c035205030a80c1d440c01d40c00303801803040c2e10401c600d0300c05003003980080201410f0103044031940104503400b04c40c250448480c3d03920644d07662912076404400441441105041404d219203440149000304240f44001002e40050007410008106540c0300c20300040300c070042d2502d280320a41000d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 704286690 1250 704285440 704285447
    0x20a12050406120b060d1e050703020901020d0c020306010902030709090e0319030924060b180405060616031b052e02040b03040b04020d0b07020a0209010906030308190e010c 76
    0x2d000d260002219000000c840f900c0c02d22450020320001459207007011344504191000c5c041e050301d145020441c20940d0b0806c89403e000d500e0246d0125200542c0b0f07a11041f000a107015a44a040b108100311183c40001580340030800b9815619410b00160340d80d0ba0301c4800351000007650384910b55140c0340404600611002101514411b241c0c407052003c0c020f80540d049081c0c0740d400801410629110011500804516415541d404004078001c42e400e0b50f1030036005c83c40d40004041412014002510b6000c901e420b10505a0041f81200d5944c101a00b007803221007840c03040140241032040d428400500c000705d00704d164100d01e40c01411540012800440ca400300b0700142c8041015910b40c840c0c1c11040d100138000d42c1e0566020500d000e003140d03941c1d107440703044000191050b0380000c01c000c248070100b040700307614601c1824150000e1100404a10501108a130f05a000307071881031901c2024000264040c18158002c1c0010341e15082036048402600018800c242800010390b280508040134141c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 704287940 1250 704286690 704286697
    0x50a0e0a03050a08010905061f02010605060d1a0108040b0a0905010b09130b01080d051c020409091b120c050423090c0319330c0903060506012c01020a1205 68
    0x600d5603138041c2d16660350400c0401c2c1c850503030f41103a100c1440380602101c1e51550078040d841c44100c1c400030823000da0701ca004c034100da44403480c2051201d4131001110b851b0010741980d040800e2003860b100e110b5160030307103480c0d000d004040c2000c0281500e07000640188002508240da1815000380911180d0400c00c2c822112881c1d110000c82d5501d094000020b4104004110843c640c695511071502e000b041320742e1240d008031242c52078103402d5420300001c96801a51320401014521507001c040c40780d92411656090030085a2214184441e484840e10004000c010343c6d0080303035401d07280070461040780c0e5865491020554032080d004181c2c0780802043c1d00c00041c04031020001541540c940b1001040500d205403882c03500900319400740c902c0c1040560701c4a0320103034000b4100814030303410010a50000140c9042c0145880060301c0000d040c000e100c1c2903c101a0800c40034201004440c005480902c07a054184480e1040021010140c0c45646d000381f00f2007412990240f03910100f4520f10402911a42 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 704289190 1250 704287940 704287957
    0x2011815080402100906020601051302160c03021e060405061815220b0a050c071a091503040209061302090a081605030304080c1005190806040f020913050a0e0a0305 72
    0x4c0440c44000d03001401441040162242503024219980c2000180081500d645e00c1c000c42150342080303c922803000700c20440030854131444003440c8091550042084445a54100c0ca080780b150740c1e0400c0255480100b260704442d011369107207403140d9003070701c0014104c40762110322500080d8018030600c80d411004001c20040d192202c0102c560480e4141d500c19024440c010310005401c00c00c890450713180102c003d070081c0b81e80740048500c5c1170b172104241e100d042c0400e201448244c50204501e1303003e241c03c0c02500055684202d4003421441c240c1c0008161842c0644900c0c00b0b050b061000d6800154241c04030361901c140070303040e030303c8041d52096034903950001d0014413212500004008160b40c80c1c00700c1250100c50100000740355803440c120411000702c0d14920b01ca0103014081041c003622807446122000d401d03600b500c5c0c0090925000d01804103840414851910b0617204004ac50703480e41d01c3c03025001c07644080c900700260780e40d02c0916040041034283c00300000c502c5145240d0301010b920070f00402420 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 704290440 1250 704289190 704289199
    0x240c0305041e0f06151a190309081204060b041401050301180c0303140d06090e070603060b040e0c0c0a0c18020301050f060a090e0106020c12031602011815080402 71
    0x1008101c08001c100300600c10010504011041c142c4086100783d086982c01c2480c0358500d81d58240c0c4c6e000c010060b4078820121040800c0045081c035034600300c43e103550501c0e1324607080c240101d041550711904640314603080381030034051000110342441019030180e089400c01400400141031203100c2141e2030b031800d125440c42982001103180c1401c0040084c0103580d0751254280c8003c43c1035607070607101402588201000da14050008802000160003004014000d207000098000b1414420070b0030204190440014542003220800c0159403101c1140c0c03c81c1c1ca90310301001d0645520317420b112030303100710240e0007200e1040200400031b215540d03100f60b04807259441014080c40304c01724444c050380003d12425620078968608111182001700040001c3c80301d6160030340c0c10399182d0400d250159000e81103400160b20803d581a000d0525541548000d80b03928011800d02c06030f290290700040c59198020304100e01031416442510701c10300810094403040f074032408086a81d2100034403665040380d0980c4038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 704291690 1250 704290440 704290463
    0x201060e06150f030c1e04050315100b0f0405030304170d030504051f0b040903030b100c080d0902030709020c011512170a02160b030928240c030504 65
    0x241c0c900b00c080440000a031103100c1d4100a801200400d0756000180380d086240c0c41000310a0300050340c10800712608401e00036094445050200b4145001d501ca40308241c148004000d0091000800d100d060482d0b080c04030b12aa02c00410050013a6409503600054140c0710104000c41e1403035000c40107190344501c0108503a014030074000200c0030344506a40c00380580c1c0020010b4504620044401c0c580c11001c804081100744004000c50125800d081090b00081c1e52000171f480d80d85408000c0e41c114560501c0c0c03000c82c202d403d45840314107100c0e440d4080e000b00c0c1e40708902000c64030140443c2000700f450540840d111451442564040e0807104d0159002c0a55a0700201d1403081c11504040c0c0181c21449040a0610700c850f00b0419038072114059040d48a500740140145401d15648400740402d0104607499041c0750350f4140c17400040d4a44802c824a141012408440d600304003814130b103800c4085210055400300a0f21000c2141e07048884030136050903d0840000c0e0140c000b940641c0c8035070a04c0e9507 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 704292940 1250 704291690 704291701
    0x110f0304210c05012a0b04020f2205070c02030d03020408211606020408071202090c070519080f030109150608060307030f050f1e0c09010b09040c02010b030105070201060e 75
    0x1007904081004220300308400781440a94407030343c1081c84c006010707030145003462030070401c1243c511508441119042507101c100011420301c409242080d000507524803075a40b042e40e000e985c9120b03080f2414070071640d40300c001801c410310803900c440c0025006801d503824076101c2003005020750b0150140c00c0b03851141d40068013039103040c10030343c186000e408412581400d900401d001d5141d00c0f0039006480241e001e0002046031a4280003070401880441940685d002e1988103008509400070801c0303e9008050040318042381021440780e01b04141c1d00202010444603280c200d210340101c860290600700e0100021407580156403001c80c0401202d99500c0e800f83c3c0d1900d003101c070001d0880c0c01c25015088260200005404001c0c5d0400c40c80c03041040c0c4401008000f062854030140003000c1c504810071385110350b03802a05100c200c5141c4d00a4919200d00d60510718102103521428034614000c6039548551624140700303511006208400400a002c0750805200c024013904c51409410030702903d440100b007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 704294190 1250 704292940 704292989
    0x12a0306140d06050709090c26010f0509090f100506030c0301091707020d0609050607180b04051012110a271202010c0b010e04060606050304030c0b07110f0304 70
    0x3010801c0104032100c5000e095507180d0182c50007508110602443c000042134980c154050b403020000c990b41d41130f18103d404110004a1603500440380385001c0340788014000050780809100c19502d0541e0641e0035601c41c881c00a00d048040b061484450164030482050b03611141c00860050404404980170906000201803c80340141c800618207007070812955046032644000e4000907000030026622030340c90f5150030042d51500701084a954000c10100610180c011881102111101c1100940142031480c20704503880303103004451007075544000a112041c03003107941d98134244440314140046a0103080110103500140d10210200e01c0064018046041c14002d00668500380d489079545280b4000c07040d0001000c0b0710082e230400a040c0151004600c01b40c804500034144a2000310161806040420484c3d1a035001102008410018003000c81d6000700b03240c40c010f03041400d00b44d89880c0e030b01080d20401d400c14101e1a0074080d54030740c04240c0d0f10200c050b204031486003518680e0201040c0c1000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 704295440 1250 704294190 704294219
    0xc0203100f06031103010203090a1101050705030d02040f121101120624110c03150a02040e011503110c0c01110f0a06021306140f1804050c0c07290705012a0306 70
    0xc20b607500c034802b141c0100f20222001003015006052140c604441c98983d18290740c00400806421600090b04114103140d05407614014020010000c0e003c0030103503901e094113030002c808036040022562141c80080c2d41da5200400500c043d090408107003100399003100015003842041c0c2d010500d9582a400800c0c3c000ca00c11313900c0310004000d01079a1540c00781078030514901400d1030a4540d400d01000c00c0d403940e241c0440f4040c200000000d03080c0c00044d00001c007a1048200300039100b05040c00407402c01c039000112804100824200003070020b134211007042c6811070000300c4101c9441001c0802080c00b03075503401020801c001d07046640d08562608419a00400703044c248130f02c036143c208600030201d0601800744c140c400e170113514101400b01520001d010390b1400c4d640070000900c0003591221070f0b40c0401c0500b00401850f40810040e0074052100748011043c00e004081035040060501c007000001e610a0f006500c140c20104030000014164000825020a080d408646440c4000c031b0303011203801c1071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 704296690 1250 704295440 704295451
    0x29130203010b120a0e2d030708040b16060c0f1803050601032a1511010e1c0c051915090b06064509060d030c0203100f06031103010203 59
    0x591400c86a801100b1003180028090140d0951701c0d044200c14600c28000040c41b030005000111079102c9150311000214001d13400307100154000c000b03442c000b40c2510b090314100c0343c50144c2a40c840040d4040520811204030009092600d0b1024103542d2540050f660032100100f60758068a14040250b000031501040c007002d001c0e43d10010041000440c1e0351401284043c0304110002400380001c440d6850105540244902c080441380f03100c02e107580820540c2d03107490404024046070f400c11582585804000d0300090356040c10040340285240110030b99050598410101c620170300528854181c3e11810070740407545080c09404920204e0349a025140d0300980140340e1a501e03480307034801c2068543c408180c2da4849132844041d80b556400c3c5000f404088100382c0b030078411000444069503191311400f14800c0c4a4440e280c1800059127031520074008665041c108001c05408600010740f400e0120030700040d0885c01c1c102c05d0220308840750000e6040b02c0c07155401d03031502c1c0302080405d401c3c0d01040740c2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 704297940 1250 704296690 704296709
    0x1b0d020f2109120a060207030e0627010c150b0f1f18091e0e0a052a10030605030d0c021e04020408030c0105090c0f1e01032913020301 59
    0x200705140032251004200545005000700107041c1040e90709410448818002d80b036003603001c1502c00c03c0c540c010148104418003119801d1410202d803038401e00c4081c0310800813099070141ca445a4460740074040c481c1c46280c004003580070001414202c50040c0c03407900d80081c0070380d6180303003000901d0070b100c5a004a40540f070241d0302102e00928000300c3e141d00c2482c031481078001040c800018000c43d1842491082c0d90440d04000a40500d440e0080680380c45030340034902503204050500101c2c00104144001c440c2c0d0070800c0742030090700f82c94007415146080e034040e0b00100e00c0300ca007072404d601680700030201c1d0401c3c2c00782c401d4003269044c10390390300381d0f0440060b42084030441c180140d40da81074074144800c90700400040c1040d0710781040d5032668000442c81c031450381d5103406100e100c1808006030804400700311640c1041c1c016036004146009088054944001e50201841070580e010340c100c9030440c296205060a20071180411800500c44401014003c1c000e1801c40c0c3c400e44c1081c021681658019071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 704299190 1250 704297940 704297983
    0xb070c0318030506040c090219120209061207081006020c011202040317040927020103022101171c050f0309010b030d032c07050f04240503100b0d02151b0d020f 70
    0x20030998040ac940d03068416030701d500b00f180031200d594080c041d01010400d0b10ba80076203842c1140001d0078201c00502011020b501030142002190342c0001d21000080003860070000400b00001c0b1903000c0c0c09a50002010804869240501c0c2c0c0e43d1b800141044409c800d005025005035406c0070481030114141144400d041a4440d00155019400400700080d0040302100c0304006451150503004003a004503451f000710b03960001c85a0b80c00c00c014000c038030046020329015243c8880c050044d101d42603440e000480040000b41c0382d040203500c419990400903007034414181d041c41c2c000300180700790440c40c0d10240031421600c402c80003d07800e012450300800700030700c1c0f03403030074481041516103c04000c9580b02e51541c20171180020b03a142d410450303020740c101884200b07040804050802c0140044840e8140c54604100d0b92903940c15088001d20790140c3d100f0025100c10a028403e6205042c10782d02d0311303120a202c02100c214005070a26045c50703e03038213440f6081d200000160b00c911840341203091031034020f07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 704300440 1250 704299190 704299237
    0x60f09021905090103080f0c070605090f0108060a050d021503010315050109140708090111180f010503040f060b06040503012c0c180c090a030c050a0509040b070c0318030506040c0902 80
    0x11b0000c104800440403140d0900c0030b1384920f14941034494222100081000c42d01c03500c00c0c2080c80742d8a42410003403c14503118540300001c0341501d01c141c41107600c41c0e08849220015502c1705c0580040109458849966135030b1a0708225000c2150b98414509051a1000005001c1910311407100c1221102c1000101034407074030400c895a15000e001c5069a56a0303c07080a041c0100c90700401c3c0d1440c56000b0803103030443d2207041000208189030080c0c1840f0b004c100304130010389120b01410a19138000b40c000b405c05d020300042443c3c4c0c0140e81000e43c0661034100c00316074503900e03203150220800c000c4043c45c0c0050312400407075446070180719010b5003018105412020441c00c0305285a0b00c01705030307001d450030300c40d03480001030824900c3c1c1e1058601440c005002d100905200d005600501416514121642056901d00241c000d0040c018010890042e04500816104401c0c0180e158091a41d503241c480e02e81c24001c0d144d01e0305550450b412400210002512006402600c0ba40400e1485021213150300d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 704301690 1250 704300440 704300453
    0xb010501081015030c050c0118060e0706020a26031801050a0b010c0b1f030f030305010801020a0f26151309030503070c0f0b0103083601030f0603060f09021905090103 73
    0x210080c1070280f120600a07e14204001d00c00c5102480c204c8620140035540e07414035504a8100d0380c20744406030001d034004e0250036000616201e0942d0301c840300380440c2c2440c004c0b100c1a04d4010600141241d800014000e080407091000001031034000001c1003d1744804079203c08540d0040005404909000c044002050810b82030344e6012412154040c00c8a06183c20080d441c01103800444000c0007455241045c9949886410f001d00036800c021454a001d007603019040200a0140e002080743d0003945445a5004010740060000000c0e40c01e002402c0060243c01e00203020301402d0700a40310030349400d411010b140250403665405845d06851620780302412541d00c21010410740345c0f5510446000001602e100155000f0740c020440991030300681d03203c1e6241d49510300740b10315005407000e01e00390412900c468814401c0409080c00a940700b401000c8030041d02c03859001a140528251034102018a01e4010040440c4200e95a089608140003012034841c002d019064000b0311407001171001401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 704302940 1250 704301690 704301701
    0x10603020f060f1c02130e1003061a09091c1716020f0d03020d06060e0a06050a0c05070f09110c0a06091e1101140c06160c0507030b01050108101503 65
    0x28400c03c0c9840e007245403810740c4840d0702c0500e0008065500041d680e0280c01042c070390b00064800d40303855030300f0b41c2003803000001e80a501e808090b0056076110040c030009501c50030744900111019010310a545044055591a0344000480c0000031050040c1c03e9413151207041040c141881d80e000820490301c44810a0040007420034081c0294418105102141181041040c160900c50366000d40c2d5010600c422400351035a03580410140403c41c041081d1035941e41050b181590513918025131075070556081190003c8150a000d407440c060804007240c660400f0141c00180d13a1140014000031420100840c0ca03403207600322a1042c0d402c070426000004920f03401810402303019040500046008031a02158111181c00803502070000c03d80d04012541c012001d001c4032a942d0514a042c03144005660352194001040100c01f01900c0c0c29116507280248018001203070094103c48142da00c2e880c051040341d4085c0036840c0813811040002e035000c080104480c09072240750354000d0264204c800305034090403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 704304190 1250 704302940 704302957
    0x11b1d0d0516030c0f0803030403113f030603071a07020a0b031008060702190203120c030310080a030c0f0201090509070504051306081c02030d05180d02010603020f06 73
    0x11480110324001c900c0c01c00807a140505074200d140b80b0a880e62030980f000d000e2581c0100c10303c6580751810400c400000c030680358003c0e014100241100c941c0c020a07070501c03c1124014185101906582d040c08009001c00020170f80c2c14462040300c0c030400811000d182c0001c4865a515504c0302100b0302c804901c1c10004924450805240b40c101242a80001c2c442040c0d50040449a000401044118101c104d00d10b00180041e01c003415250500e800000d45071002100c502c00c8182000c01c43c207045413801c1200070300c2c1010091403151241101c209a54495005035554000c0c2d83c40007001140381e481c0031031904540b0758181c455440703200d0070342c1d2291440310f0342e04d006906200306688001000d80b11040800c1c4141420380c5d803076580d24184001c120b5503891006600c0d0103280b8100d0306001e01c120004000745ca81d4841640c8200d130f10000314040380307544285000000c8160620040c40b103003048500d41c004d000c11040e800d50390501d8a13240200d00325462880040d50044030094800e0007400e00e0402041503a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 704305440 1250 704304190 704304199
    0x60e070c06200c010c0809062a040b030a0905100903120908160302060123010918090606080304180912210903020105040b390909012303120403110a090c02070305011b1d 74
    0x30343d0700d12f64094190000c4900703104a03926a5006020040d0034007801002c3c0307406039410007045009880c020118803900c41550355031031317541038901c0034007540b1010f94005511500b44030400765418030b8025207540c0207114030220306500711000c0c103000c00100000c0e01d041e10103950380b0f405d0f00d00e00310111940f1140314140c4404c1da0b0f602c04c040004921240540070181c600310006503900ca1400304214400303608211075100c00e03032074102c0c540006002580c081094a0841c07800c5410603014000307010b807040200c0352400d40c0790320300124901007503010f40002c0e00c202d0243c00e00103104d554110030300c00094521411901c0a0481c01c401c50180d605032404e44640f01030003d0007509016400380400c124080030b8104000c1c0201a86000800710714103058840c241406401501540401c005014901d00450100608841c1030300300c0031016403603006120000780561181401209400400030752122520b0000b03481035428104440c0054a6407503e142c0c0c01015661000d1500089429681c1039118a07003119921 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 704306690 1250 704305440 704305447
    0x120827030328111005101e0906060305040f060905070f0b0c0c040b1e01120221061e0105070503040b0f0409060e070c06200c010c0809062a 61
    0x1151000c1001c0d04030794284000c41045405210b0310714030102c01d9003480c42e08002c0c1000c51803402d00750105002c80340102150300810342d92958a01607118000c00e40040181680c0c41008240b0380180c0000a13084030280c060401c02d5586441c001c9041c0c8000701d40190111008107010000a503035a03004411207800b507002c0d1003100d6120710740c0d0303054003070140d02c01d41c0c12101c0819983c05006040c81100c0303039003004403410000d4500303500200f011400c0200a2a4042900755103e01241e40036010348002d044000608650307602118020200c1e50800c00c2c460900100e541d4001103e0341000700107070000c000380340714030400400e5000044603103602003201220315010520000071076803a07030f0018180070340842c800e550f2070700c4c00c201c0b0b10001c84095a00030144a4200d00c180481c01d90004420910319805c10804281c2d114906400006034a85001c4000035010014061300c41c48410740c06200c1c6003225540300341590711281015541d54406171200c1803441c5110070742c000342201e41031b000c482000d00b82d510f2604 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 704307940 1250 704306690 704306767
    0x6080c0f092e050702211507030e01020f0a0e1e0f010e120a1b03110f0103091b090e030414060310080105130b1e0c0a0c0f0f06061208 59
    0xc1c110b01085520000c5007021841d6021842c10032101c81004c800d200e802404000007069103a603404a256441c01c40c80c2d900408990407500c00d0b04400f1607000140c009554403540034140c0f84151744403551a40011344813203c040030038602240c20301e050078080c0303c4801190306044104001481e040804905110700e0041c2d0101a89604030100d89881102d0054002642c0d5402c0c244010720501e8003000c2c440300c8190007031001074400f85102403031103401c2d00c5113241c1d114100c6c01640102035804c0b001e02040c0a1618689802d0884d044600684250136070a0200e07000490501c1e540340618018820322000f0010694141d013881d00180d43e1251010310303d5200c050750307504124215070b0141d50013201c04005802d00414400040040c64004820075100d07030111140298141407141d02800d0548202000180200c6503449044904891030f009016a82001000d01d0b203070b82c1c000207044044900c1410250000381010710112407070040740d00a400c8524194800901059040b5100709035556103401285014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 704309190 1250 704307940 704308009
    0xa0504031415010602060403050304120504090f05100807050a050607060605120a110f0916050d06080c030f070501050f0f19110f010507050901030509030d1506080c0f09 74
    0x1402030300780e80908404041403000d00020369058000c0000d55209200b8803000a40c04000c980d4800d400c09003080c0c51a01d0342008a0741440b4039840613040c5810711142d400c1c90451a441940680004101022425a5441030a40b00c001c0c0d880340c1d960010000c9005c01103410036100030302d11203118241c000350300c030344a80001e90486800d030f10080003680044890020010764403a000520001101d0302e441090000307000030000c0100030448802008200701400225003d58203031440e12580110601809032140038996440c0349440040740b0911070161502c0d204000481ea0100b55241030f0742e460b00d000c01c0b0349401016580b0100070985021170820143d00d203a40516000c15582200766aa0106100703180a05850100c060703d55000302d92400040c0040960070004482c0102c03003c0c2004140c075230300ea10050b41140600b901d805100c80c10300c000400d0844520090200340d92458030f802003245c0700c03828100783c1801281c1d01d5200a9200b00401c400903e05242c955400090581c40e040ba01e419408a10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 704310440 1250 704309190 704309213
    0xa0b060c0313050d02061617031617040b060d030c06090b01090b030c010f0309030e0301050f01170705090106030b122a0f0f0f011e021e010b10050a050403 68
    0x10510703400c00700340c40c54100700200030200104001c40c2d55966019454000a46501c03c00e82075500120100300c60384200900e41c030490710100304120802d91280340c07104540341e80d01c2000c01e244001441c0a04c44035851084442110300071a046081c020306036a54000b4048085076620b402d40a0040903036200001031010300070340d40300c644600700c80340c41075262001c4101510071119000e07209800001c030146060740d1020f4199070701b6a03240390204001c900d0741000c1d10400c83d1100800e80550034582000380d15181c110350a0b040b550301d52605035040d0070110f0116140c990034021150311244000042142a210740c2010b005140d0051070700d100121415056460490381501e0481c05000440c6426460f0b15400240d48070346100303480c0b641008804030000781d51426010900c034419502201c841c0c4860f441109201240311001c2d165101c904065807000e50b0700c000d190140d41c90114904250100070b9018050400b25100150640025000c580c005403034a411603030252082041c148800004241d0340101e8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 704311690 1250 704310440 704310457
    0xc020105130f141c0224070f05060c0a0e0121020c0a021014090918030a0c061d0a140f03041805100b04030b040f121d09010b040306050a0b06 62
    0x5036001460440c503940460300e40f0507034a204080c025642204c901c1581941120558112510f10003d00104003000302600d00d403a20111a4802048035010030008003070740300001c1d02079422034901d80c2d100328272040c0354801c40c100e24000031100c80b4003031600d50082c401c1169802c0904800d00c1b4802e08580d64804982051221505a5014181d984150b08003924400450032040c03910101d411a001c1c04481c3d107119000d1303958051070340d1200103052142d0a9109d181501200000e4035503484215070b0007011303883c0d41007058480520703015003184840200700c4030014040b0b500d005030503c04a01e0301d0310520602206515080e60041c620240c694010a0000780003609503501030f4030000c0403c82102c03041700c40040085840d4888c0784010300000340b510f001c0d1001c4170790180149907a540e0314549070851340341c2c0082c001c04001a91041413001c070303006511601c150952940c12000c0d880701e48100a2459000c1c81086040c01c0100003e00100f132080d0003032640040d003481c000c600c0c40c051401091559100450 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 704312940 1250 704311690 704311709
    0x1140a1a251112030a05090a0e01180605031f0506121c1808190501020f0703110f06041518020a060918020306060d180c08030901030b18070c02010513 66
    0x1101c10804126440300c081c880a40b841c400c0c0c40701c4416900e03034034403800c01d00106100c0c000c28460010341d9442c56420280c4070000c4a0b0445594818811100c55a80403078804090b00304400460141000540c100d03441c030303c041240340000030002808004150103061181c000355140703500d0321420b40411203250030010950300304034007030607206000f01003517040300f3b101c100b1039480030040000d2040064030f401c070310001100758080d0811702d280050080c403602090320003081c07003c1044014140c1141060038001034030070a46100040a4444a03101c420446004069400c044981d4401140756440200d00500d041103a2004501d10340019820f80103941c490000900004802c2c80303284401080c404c009a0580d10642c19810010b0000e81940150126010034541d500c8040d10044850460206210780002e4000002511804a59240c0c1e0050005a022a050602e61131440c1450114051034034001c3c40303000040e8603644021212000b000303070181e0400005000006880010350b4071800149030148 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 704314190 1250 704312940 704313007
    0x170d3203090c03070e15010c320309010807050d060b030c21040f0615051e04051f1205030903061003060c050a050d0b22021201140a1a 59
    0x164000d02c0c001c070207a8014001e40118504000304414200f0168000240f40c420021340c14110f00100d410136903d21014040060528201075502107220300c4a0320000111080e001d2164039264081d6284034020b04140003c84010003d04040d01ca40003900401046000100b0070341c0d650980b81809070000c0c0c07128070154100141c110207a6480c0344914032642c6e00f004c2c01076101c1c54642c45800340204e4441e006840240c90f4203444000d0b90b600c019140c054030009149100340c0001c00c030071509121790300d000a40134601d4500450f490115801147c3d40f000b0502d450b0507242810b001e00c10103000c4038881c0441701031100b40801317000c95038244030f20b0740f199081070b0400308040d1440c02c089041e41e11078210f8406101c000c1100e036810300d61080c00c40f0030705414101f003c601e4060100c04546054182d42d0207d02c0d03000031203164640f14203581c005110030450b03c14401c0322030740ca404d660741580c0c4c088100243d22040313801c0100040006400c949117841d58010101d03003800c0100055428100686100190649009 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 704315440 1250 704314190 704314201
    0x708040513060f0b18041d060708090703111c03080a05060607020603070f09080303010906080715050405100311070602070210030b100c0c15090807170d3203 69
    0x5510403011007010300051100d01c0ca03011040f42105064094a20122800510703540307810a0b110030100d000c80040c200f008070300300c1201c07000621220f0043c82c01e1503024500c082070340703144900f108a014490001c06048850301e10354842c60340d8119000c3e400d81040c003400490409a5445042e0340c10a4003d465070740003450840700c0741c2d046450003000244610410311580300943c85074815640d000c80c4508000401407055482aa45406c503540311425601c0000004100e0254a405c83c000311100d0030210350703200b911211200481d01d103082800d00000d006000401ca80d28002c4484034031040142400a003040304a00266010f500000b41501e10980008201c01103007001c82508488500c545400c10a41920700009941b02c000000704100300700040301c0b440d09218600b0911001000e41d440c1c040340d0000342c0100a42103d5180c0b00785c502130b01034150001400d021070400701501c0d07690100500903103d20381100b51004401300e158004030340d90144182c565a8421010400e120082d45407403616480c21 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 704316546 1106 704315440 704315449
    0x4050d0305192a0509030f01060506030a1d0f070f050105030402010e100512040b040201181d0c09030a03020109020418020d0b0a0209030616090e19050709090207080405 74
    0x34003d4210016801c0001844a9501507082d1200c0b0200c8011003422103215100c1c0300e8008a0400024400304140d0740001e41441d000750f2800b06418199100d03030310b407a60704840342c1556400700d0030911001040034a948000e040c01d00e441c0c0d00d50300d0303c0c0e40000d100b1a149800b0a000340c000750740080b2000d0080c3c040d202840c01c1090741025624080c01c213660001001d41c1c1c05d9010800e9200d2126050040c14a040103a41d12408a00640c450242d500c2d60307a901c0003005440112400d00c120b0445076018411742c0181c1d17000c2da00104400d0f0340d0f801080200c640350300e030202480321a010528010f880314110b400034160002406000c0750380d01080200030344503800c010303039141c042d401c02c01041c400c0070582d1000c02042c0707550b00c10360b55450743c0e0352180c1030800740d562031860b6429105101424038190041548040b651a241104507510b0f4003c10690304242d00c12984100d000c501405142070 = true := by decide +kernel

theorem cover : BRFrame.Cov 704136690 704316546 := by
  have h0 := BRFrame.cov_init 704136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 704136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 704136690 ≤ n) (h2 : n < 704316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
