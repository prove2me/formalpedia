-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4879
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:02:14.384981+00:00
-- url     : https://prove2.me/submissions/ade19fe3-4adb-422a-9aa7-eaff1820104a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 877338129 ≤ n < 877517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 877339379 1250 877338129 877338139
    0x302070b070314160c140f091503010606082208030f2a0705150105011409060d021309061a0a111c02010914060f0606070c08030406030605180114 64
    0x450042c03500c500f84500c2c607140b071107025030f9070342c0140c0048071541001e111049410600c0d01101060040703c0100700d051810010302132410031b2440500308840e81000034420800340b80b90301c209080341d81d024042c0000500075034070751040c41e00748540c0d1300b051680c40202082c241c0762414981d1300050144800c40341d1107051250345a250b600e8482240c02d0110100b039030380c1e9070322400400c5480040c0c0c40400800307605205900b1148011910301351001e107120244105808110300806000c1d001140d14020034003080024940703842d0060000c041d5040703800400408000c02070201051040c0015445542c000d01390303500c00154030700c0c1d10707041d600d020784142807414040003003c6800c1040e501c0104501d4640420706840d0381c04d242c9505800900034078056109a4040c44000245040400c0100b0054028440c0102d0410b07aa6074640500c50300358808442126507070603000001901c20703030a1010340701410310381c0e40c0454464505401c1190100c881d60540c50360842c00d070010070444040b0b588283c0c003c002520b07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 877340629 1250 877339379 877339387
    0x913080403080c0f120a02060a06030203030d09020102031603080f0c18040207140a11151911160303020601050103050f0601020d030b040f060b0c070605310503030d0c090b070302070b 80
    0x41c0080c10401402c68110b500d10800c015010a4064840684000c0b410b513400c2300c4659031000c9030360b41911b205200203505504208260790100c0000c0d08071940003030040c0116494101551210503540c41503510a134002440703c42482012400094405d41100c002100107040a2801044131880b851014080d07100d65400910a810850300d09400c0c921007041600b624000d61032820900e50191280300740300c1c4222000880d0303082c0401043e003561780058000100c80801c600400c01a00c0343c00517001c0d06c1c407080c8145800b15103a0000504c561016521030b41c00340401c1d5150100160541e200074102800d8009080c0030072201d0f03640040c142486000ea0315000c034490501802050081c01c1c0ba55200f4412424618042012002c400007400100348140484120715030310301d8215458000d1044080d5a04204000c0c0c01d5102c0c00c1034070340d4110b85901c3d113a50a400ea9a074001a1865100f403465040d42030300e8483c50310000b40c2104002c402018000000e500d8088181e5009403141e200780219442c400001c5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 877341879 1250 877340629 877340647
    0x1030b01090306050f190606020703080306041d0f0d030b0f012f1e0f1b0a09020309060907171002071502040305070f08030f07140f100902091308040308 67
    0x14403000700441e000300081240f810440e04000c81d00e94200c840184c03600e9100002807a042040c401c00013201d006501614080781035a5410040341c0c40a40110707445038554a401c00046480354070310603980341910080c585070229032003480c2040c1f40b2208800a05142c40c01410240c1c0350310402c0c1600c54824606001800c0c4010400d08400b0302d03c0350204c2109a080050032104071000070181e81400f500e20f01c0300c40013607030540081ea81303807081003a41d4580d400500c180203900c081d9506410109000420082c81e640d210b1000e01c080740c2048030007105036800740c0e0900c10102018480c2e4000750440946000b044c8040c0c0a20360385c0c59610000d8541d6a0303600040c2c51003881002c20918020414035003003599141e6807818107507540c422900800d80007461110001507a003000208880d02c103440e181c500360800140d5242c500e000e00801212102c00d0080b00c2a01c2121b074030500000b0b801c1001032000042c0e02100d0f00611096440050252040050160040700440c82e01c6056070100da80c03000105640da1000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 877343129 1250 877341879 877341887
    0x7230727020c1507020a031701150c050c04050703051509060a140a0302040606170a05070c111f210203010806181204090911041506081e09030c06061005030601030b01 73
    0x40c8038107410f0035502013409070817540414040c6440d4000d6a80b250706180701900c2c0094100284648001c1490310030507a40d8460158065000e0726000350180c2d030000100c0030119090300c0342100c0420029640317004111001120100402c10044240c821a40c5440c00002203424018079000b881c2040d030301041e04035015500d01c0585d401444c1e029000744401c580d25100500760701124200d0849a580d031100082d40c0100902c0356922404017a40c6480080c0d00c00e0300c031040c0c014030185e43e4a402090a450309918400100b511360103c03002c90303a640015001c00000605640c8411007032054885c01000100240341001030119004402c1111001185503000201071424003d2a10001c641d40042000118200150f004590300f602440c80c0ca070a00001c64200011038503042018200801c400c2d20501410384200003456000c500f622031010851031803246d0783c9080d20116181e41b601e9100198407620143e0a01000e0b400040982c2c440ea201861220003070194000100240d0415582d010b905a5076845 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 877344379 1250 877343129 877343143
    0xc0c050604150204090204090609180c060f05281b0f06230c03070305010e04080a0f091716080118060c2d020706020319110307230727020c 61
    0x2a0006c65a80707903160a00d201030115489003400451401005100342c20550109800013a884000f001c181c6003418400c0d40d10510700184182084400d0046d80000301446a0031041214140304258034143c902c58001d01d551300d0315410109050304071212100007992000c600b100241c1c48cd1011403010380501e0420403003641c040603014020510300c14070040302d24040c0254040d00d20f0340e6080c081350380c0700d0b0881900c00c5400d0394014140b035402c001890400c1c1c07003180c10310015105450b280d11200d80c0c030454404104400f900c0d98000760085210035482d00040f20701c00c00205180030082c4a00e032010310a4076018865080003074a05600c8403101e1401d1480b6281c21403008205004454841010850500041c0d41015000002d841505004034a040c0000242c41c1c00c00b00c00c0b065803203103981e0078008030b41c07440310b00703450030f407541700a0001000046c1c0036004c3d6840c440404402d054003200d11419545417080c540d20609007400a0754111401c100c0580c0400c82c00d06091001681c2d90200c0800305141501d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 877345629 1250 877344379 877344389
    0xa0e0106120b010e040206040e07120e071e06090303050a02010212100801141605210403032306010512070c170301050f060f04090c0203040801021c0c0c050604150204 73
    0x118155020401014200c40d60140e28010b0900c10a542c0c0c8540c041580910b00b681c001c1d50141061100f0032494060070110703588218140b802500082100010340143c8584c8803c10480ea04420000d0181840d65034803c80c0080c000c2c1d20800c407585c90002c01401042c0306000180421400065000d14a8000d404446c5402500238000610303142070000d03203001c0440c1d40900240341d402c09840c83c1d05500380301d0389030703024466050031105c800703640300c0040d035207940079030031064925940c6494070801c205007107003540c8503078040e84010a811203140201c8076420021020501d036078911605102e0282d9107d0103844142d210703d051300c0009c1cec48006041d103c008c1c500300020011b180014448120081140c0603604070741003980d012212101080800c00356000d0480403480d200f906100800980301143c000c04041001401a2480c3c2034030b0340c1d01c850030f9030300c2001c040c01008072421452498003000e208241c1000c005103000107042e4072613915135495003006400078001c1c5181c841500240401c541c102c4000340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 877346879 1250 877345629 877345631
    0x20904170f0414132009040f06031b0608070c020108041e050d0e030a0f0f23010902010207270c110d090503010c09030503070f050307060203150f060c070e0a0e01 71
    0xea0340d1044940c50281d50150b41d0f0080c080030400d113890b103c442c001d910780f0101e44289041072184101c2c07500e85a402030520564029110030005251405911800019500400940694012070402c00441051607842001041003400400980c0c41d800080ba03070701184c3c246040a01510307035052045105141049052b80c08407400176135030400900280e295000d0fa44c540765041e64a000768105a1504440c41020340b0750204003940c00b0009660039009040680b15648031140c100c9440101011555501400e042982d59000000d05541e0100a00d00091000038010f141e1044688511b804a1071850003202410361506c0d801d9035540d000b1050340502c3c500329002c58200a0314100000c0100d070132481118065413038441c03102c1c0100d1099012100303480d00b0030025480c2294a43c0c80d460f41b403802000a8a0b0b90106000311400603115000a60083c10f070000c0c009e05030030116080001d1425846030003442404204515130042c080403c080003240c584c02d80b1101ca584d0f415540074003800c104074030101a5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 877348129 1250 877346879 877346887
    0x11e120c0806030d020c010f050c0a0501061806050307151d030f0a0b22150204240f0c0506012c0109020a02070906060206151c20030a020904170f 64
    0x1940c4550744038072a0200710300300c81840741080010381e100c8684a003414005050030040b80100c5000d08010701240000310119545070780940c90b96802c4400320380149035000441c80713142a0454842c00340101401d4100c001d00003903890a00c81c5803900f240654004280484d400c0c0240108a214021006104d8068151800541062011074031000c0480c0102d0310321200101052182c40d18913900c3c4c458440300d03179440d16045190b865207031a481d26000494003580e020070010980344049410072456090540300c4001d01d0100c01e070060196141001c6140c20402d42c4c1081002091000a2940c115880890642d00c00803101c01442c900024101c01c40c5603c5030b03003c0000416100e140c0c002d24036100c1d40d038203039030206450f41e6840045e03481d21f03c0b82c080140e200d0300c080f0b1621b400e00101101303001c0c00200f2035000f0312900f40303c405018450ee90103843d0900d1089400c0c40c1540c0100c00144903143c210058442d00f0100c0d03001507888a030141010307041c0b005004d8041800c0340d0540c1250a40e4409400c0c80d0740b1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 877349379 1250 877348129 877348151
    0x307020103050606190e04150509060415151701141f02010204030f0b04050d0906050d0b0111010c0806031b0a030b09390406062c060a0315050906011e12 67
    0x800900c03540e46c0c50180d0f00d403801d10183d020100c03940324103450004103100c110392207030000c00003d0f0000600c0c5403103000c2e14400002e10101d296101440404580e00e030740c03402020340c0c0c0700403085010590010300c1080f4102c10f9511a03a5405c168810403c040c0110b09545080d0075104a00a00460f00002c200451030349400c0240103407410440d200e22321600481c1c80c20005650121440e044500c90f600100b00d0900401250401e80e402800191f14107150410010308180519401d5959620800001c43d00c1c07001401041d04040c000b2868001403481009078818030407002c00e5031000507110140c0081c1340340d0f0102d840d04101b4024000400c2c144400500003295140c205070b000400456a09a24014011220b50609050069408803030042d1125894520850f40d03d0582d1030311103002c9c0c8160324070500002a51368590380604a601c010b41c0d000600240d28510b0828284a41e401291242050004118103a80c3c4807902c1501801011414008001c89440540700059500042c211060410505c002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 877350629 1250 877349379 877349387
    0x91110030f0e0a02030604030f030b09130b0106091202061e0c030406300c020c03030c0106092702060a030b040906090506060d03080c090a03050118050f060603030702010305060619 79
    0x440070300c20004004030005400c41c10765501000030000c1d010740203100000d020902441c00f094019045050201e041e5100c00d0008503045012198441448040c06414050022100d4080c4c00740080d81031503104941010a03404024407501c0000744521000181c91031100d186002c00079000c1c43c8408101d44805045c00c40719200e42150103a640068899000000c16400355400e000d50000c2c40e203080503800c0c0150b00390101408100741d40505620501803e41c1ca2510100010b007001d000e000000549681080304080945180521b0003540d444600710340b0000c41c1030481d11416a0750304507541ca40c0c1d1014900103901900304541400c4e4080c0c0307010003910511801c1d810030f120013441441556401e54860301080b15080c07800c407003e4005410480000e01c1d5050307106c024625640e00a02507114aa580d03600d55094413401d0030307440081c1007420042c1e810450b08002250304142070300c001d0301c3c8910300500800e64a0103a41c00c00381c1016104e00100e00075459180031120b40e482850410000108100000780c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 877351879 1250 877350629 877350641
    0x60309032203170711031b030f0606090a020a0c081603030606110601030210171006090f030503090d080903011b0e0f0603010b0c010e0714090a0b060a0309111003 71
    0x100200c81c80310700510009400404002901e90201c01074071651602c02140f032550f003014604480304841a81d07540c900707a8080102c01e980c100042c0b2a034142c2203d50b400d150500140314081116030780b00c13400380310055844441c03407503200041040042c0c4844003403208803040c20f02000041d2184070001540b0f1800000b1182e0041d00d14029182403000c81d9451a040354a081e00e01000c4890350032280c012700041c9050203003103d0f10f6070185401e580e001c2402c078003000c1802d0103480d880070300801203c040060a402c2040d0f400203010111030800d100d495030319001d85074403528030107510864a038a02e035010410340c0e07802d6521101c0090000c202c1c20740c00342020740c050007010941c8004113a10000d50700013483c140c11441c00c83c800c0501418110392030320004040350f8200c00500e0f481f0f03540f82e002e5240171200422034140100400043c02c0e8030020001c003806a20075010744080c1c50282400c14000760f42d10f0b2182101d010182d18138002910040720f04100322441c02c1020941d6108038107611140030b10b80d141d0000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 877353129 1250 877351879 877351897
    0x41a10030207121412060f0a0b04082103070810090207060212150102030405150f03040c0924050d0609060204060909110901020601031b091107051608100c0e06030903 73
    0x4807000c0f94144010350b111410100d82c048403020410030100b080311800201174110001a12020400c0d4001c40000c00000294000c0000750700041002c001c0380504202d0104c2c0d00c03040c6100803c08454040c4001007602c802411242800a230201142c2007000510f6200001c0603d120115100c0009160110180d0b0003140380105028444d00801c04e40d5100c2049175004a4058004615091521050003034808061101100030304046c4110341099070480c1c0258480c0c1d11600041c000303503042580040440b281c040c00740602c0c107000c09005001c42c489a40d080c040e43d1080702e032040440c11610b4040c01034546d030710009014074004640026626040f51210066038000341040c01300700311f5030760448040e00403501d03510f00690000740100003090031001140c41c4040501410701c050768603a00b000c0d05580b4502d0429180380000180300060000602c01d4440340300103610703241041464241034950b52082001070001d110350f2408680207607130246030b0328061090040c15050f201d10b803140b940c0d5183d401056107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 877354379 1250 877353129 877353143
    0x1406090913020603041a1005030618071d100b03061516060623011112070203100212040605060d0c2711072d241517030c0606041a10030207 61
    0x1f05642d481404280810368401074000e081036642c8803540c00800301215404401409034003c0424140301c858020900c0880e10449420103081c15520200b422410368008003045d81c1c18801d0040541c0c030300c54401c01c503592640480380c4548224059040d000150480140b000307241c8540018140f0340020002d490480c2e8503042c941c0e86070341e00300542d1240c0c1c4030703032031b507030540d00800008500252604003601301c6900140450300725401100c580c1c02241d06c04600f0b04003101e140303000c020400c4505c1c040d9a900034000d9500a4402c242d5584005c941961401071300c0410702c8100c0507248039904030140303450078040d843e0140042c041403c54940198042c020a440002c054070112200e02c001c0109171040c034240061050020070251619543c484440314085c1ca92940a42c0300e8001d09203034041d84000704603855030107100b186018400d2600f10003580d02210603400c207110ba449840404a100303648007000741d9011928580948840c180c0088202869a214401400d80503440e40d0540c0076004083c403682c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 877355629 1250 877354379 877354381
    0xe090f06090a09020a09091109010306020c0d030e1f0e01020f0c010f0b011b03031e020901030c022a0612160206060102060c07031808030a12061406090913020603041a 73
    0x1c2c200c800d030382c0c003c00040c2d00030035000030400c45015960f1045003100e0181d080004a02d049000040c1e41100c203030700549000d43c02140320b00041006108010780f10881c1c1c03c08100d052052500142c507880d4100010344038846d8404554a4a9001c0d08407003141a9440c00840d914050500d80704a00c1d0014200d5aa00398a080074601c60103c1c2440750710418581610707042d50203100080005481c00c0d0100c802c500b01901e907401c200c0c1e110241c1c1c00012580c1c0b40e10300701584402c070200006048038075107508030007154403155104840038540100144142c1c039103115895205001c034085915032042031100d800c0c42c28008204003a9074140c0c1410030902520f9400d0b1825a1540d400480c0e071030009813034030455170700204001400240a588011100880191300381c5c0c3e01303546c0b4207902d41103401c1001c0d21000b00d141944121404c0142d8421000609400c42d0207001d40b0411502044490148104080c000d810103000b050301c81c45600c00400606a000302469078a203854506840800400324a400790707121448 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 877356879 1250 877355629 877355641
    0x30605131a04020c0a0f05190303050103030e0d110d05070b040305060103031202040b0301051309060e030903160e0115050d021c060e3303060a020325050f0a0e090f0609 74
    0x2000b00c44d030769045507000b44400010354840e040040e0000d0b03401caa451241d9400410040011030041c08a03c4c00307900d00040700d6241d4200030b08004610409148664801c982c5500002d85200c1880c04204043e10040c88140301031501a00e44030242c0c005485148011800000300040000c01c0d60681e0f12035580d83c604074a04d0a0010180d0059015510b16228180014441400c1040c8403142581d82c0c4000424801015143d0034101d1f1300c0d2240010b1150030001b00e1002a0408100310400240e0603900fa400e401d00d0501040b20642c018007441c0503a0a054440a804612441c1911880486140110354030301c070031280708030400c0b10990907000e481d0500e54005000b0074401d0300c0c68071507405003541d94030090300020000e45040001215405800c8104501d82c016202000180d01c500c109031001681d900301a03d01d540c6a030b409958a1280d240d10703480c041c40103640541a1150640b025a44980b6601103041c00c0c1e44018441c1ca00c9134020035800200000c6004014245018800568007070b150742e100e00c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 877358129 1250 877356879 877356881
    0x601050a05060f0d020d0603060507120e0f1c020304150305040611030c0a0c06020c0a030e0f04090c0306020310090e0c09150f090a0b180709150816030605131a04 71
    0x440d03000030446014840b144c0b6011072070b00205a001074100e40094040e850756902d400321f4800b07887c554005910018085d048042d01d2051030100740e213040052000f41203040485903982c2c1001084403030080c0c0e11441c41d038118020425103000d0300c27014100c5030f503008101c0d0b001002000d04a609480d40c4c1c0c00e0650400d00080800101ca00402100d0310f841d1401640c010150f62904000c40120f450650070088500c0c3c0c0841440b120781e03414401c1d5641a01e845085041188814180907181d2240d0701d010559400901810041e4044980c01000940c42c0e51b9014403040780e11f4410752168461300d003054020003c1440118410382c0408040305d5045040c1c0f940086100d80c40411baa4035600403105048000040c9400510b090b803000d0344220100d03a0342885400f00e00e858210000782c0342d01d072411806004456410040031009040c2180310341407000c07002c0c1d0000b0039100d806044031076450714002e0800c204510a400a4002c0c19018001c0c03416501c0309107584000700f01a101c010380400c00e003070406d9114541 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 877359379 1250 877358129 877358137
    0x40506030706211d15010e0c2b0f0617071e05041b11010c0801050103150816050a0e0f2e150e040207020a05100210141501050331020d050601050a0506 66
    0x12107c409211031751113200c400da95622108048080f0700704c9580d0815501d403429803405488400c0c040200e02180200d00700420b031602a00000c442c4c0828a08441d01240d0005409040380d000e1046c800d60702140000119100d6a644c12a58000742090031612000c00c0c0c030300b020403101d00d0955411241c0c4600310740d01c9007215184905100040c80510040003558800d400c2894210140144155019510704404e4500300503a01c080e00c1d803c4030803004000b58034000c00004001c1802003400700c45850042c1d03d1002011005011000c410f881c45942d4a01b0001284082241012502403075040350702c0e610451000d10740d24880000194031142d0800e000c0c14580240c54603180c2c09050404004c1c00d02c8100500705c0c0c2c070100c1650442c4070308201e2a85c000c3c3c03d4018100000c80c0c480c1c6060141c1000c000710800010300071517103810700a0070030612043c414086815144800322440750407004d00a0b01c00c1014a100900e8042e5001816002e07820a02030040342039030403039608440e4080201c0d81c4034103000e01805 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 877360629 1250 877359379 877359389
    0x618051006080901020f16120906141305101d0d030206010b0d0b09070c1205070218100b0a11070e0c0715060f0b18040506030706211d1501 61
    0x18030290100025801100308940000110340050b061865200c605a51078201006100320445d02110074814003103114460302907441e0b28540403a040e82450030182807544110788030360f803600c000074100d04d883d410581c5081c0504030060108000300c0003c140200841c40710350020006c2c1500b01020211443d02d0b08003031248561607005403500744c1c07a22007009200d030081411b840302603449100302986aaa46404280b0071200c607182c0200542140c1041d00740e40c189440000c003441170130400d140c056075803803007002c94100d0b02c2e030000741c0301356034200d1005514080d44d8001c0032460f5010070216040350700302c501d80b245450810121428542d0342c03010011780741e4054813000341e548001c100d0040403458010403c903a191042c980801c840c2d42d0381b4141e100c0202c0c42d9008c20b802240200b201c0406e00145410654007400448007804503003040e9002a0b210000c034400c030003e010581c4004802d8580300e058604031801c3d031102c00c100088400700701c03056022410740202021301480503412455008446090305032a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 877361879 1250 877360629 877360651
    0x6060c0201030e03121305010f020f030c0c0c0a06030b030f030405010c0803220b040302010c030b03030a11010b130c0f05031e04140f010c0f09051e0114070303061805 73
    0x601500190010b01d103142c003105250204005c0c0c03c65820070b90040e207020b024140c02c920329114090400c103003120641c068449001e8010000c45000020b9442501e800c86240c0854039034038071581c4c101600d0700c10300d6500d80f900041010f2000070025059480400499010f406a800c0310701b89605090f142c0c0700720300841e800306502410361004581404091a401180304080719848500002448241d50030904120b50540080c02004201036082c01484050030346814240118040000065244d002d8444c403002000254000900c12031404d4201910f039210162a0060b0005604000f8000c1e1900c00c000802081c0a042905079581c07180c42168443c405e000d013050a500e003200080302c40e12101510681343c41c04412040134018400780080b00c032a00c02180000b68007482c0d58800f4100421001088081c40103a1130100400d07201d0103410f28038030802480e40c000485113200107894140030358811a800881c0412490100b68040d440b00003070360312481d0069802d0b2403801c020320a9a00c00c440c40341101c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 877363129 1250 877361879 877361897
    0x10b0d05100905071224090b06011101060504020c01090203070b030408090607060905011b1d0303190311160201080105060313030309080c0a05060402130203370606021506040606 78
    0xe6810740c04246a82d2043c019991220b170f485840071410701c6001010344240700c4501c0308400403507503942d200390300d002110004d112160b4961a80d0741c4281004100707605229020307541c000c0b080c030203600440241c08014411500c48000c049583d000313001841c022800303841844008690b00801c04142d07441254840c21300c600c0c0040b41c200384030300b80c1c10031441102d0f011f44800321800002c0082c05050520840500352011102032104001c02444040f40c5c04a081c10114881030201c2d01c4c0402200c00080303510001c0c03508200c032500110f00a100e001000104001c01280000b0403200c3c05840d1034956000341d0b5041d1003641c8540400000e848255802400c0c0c201c80010700002a00a4100b00441401010201c0c10070030380301c81803410801c50794001c03a000c1e041001044210714103d8580c444030a801c1e90b04508616141c214008111070400c1c030b101500702007500020480c0340304105080150304001c3d06000b160741e0b44c0c001070360f03c5034240b002420f00420003000951504052180300c040351401d42d80c150f04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 877364379 1250 877363129 877363153
    0x80a062a02030d0c0e0306130201030b0604090b04050f130609020d020a0e010801050702071211010903021e0102060906090a0215090a030c0504050a090c060f05160b010305060f010815071709030309010b0d05 90
    0x15548c1201022414103890b0050344510380d03151400f0300021b224404000c22079641d05030800003210780c004c0001c02e403131101105000700050b8500e00c4624042d808000001c014106000051801000d020001c0d0700c04d000c0c0c0400f09200e03100301380d035030f049420340c1c1c000744580c3d241c08006981350f074443e001c2c0541c0c402c25600c2200100d00c2d0340500840c031074410304014100c641c50350041088800004a0741501001c010440d078100e5a0400c040c9a002c441c10001d00302e5420508000d50321040c400300084e210740000b4400d40266070565003100c10300c040042130243c0665881c90f042c0303e04003883c03050520451a05000401e868424051000019402400e042006007085810380b009a80b20409004210052101450b04043d41d090032601034040d12401441d90300d94544030703117403003401031012140040000041140c2c810007d0a01072074140550401020780c1c4a02003291000141508240d2400d14101030040f848800310003075000b60881e5009020000e91036080c0080c00180c010000c059512000c04030907 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 877365629 1250 877364379 877364401
    0xb04061d0d0f0f05130807170712061e140f07020c090a050712020c0708160b0304030e061c0c090b0a1205070e03030307050a030501050a080a062a02030d0c0e0306 71
    0x34030040b544c01d1040c140b080200322070031240310740d40000105500c6054103008500c0c00c15004140c0300503000050200b1030410004003e2051810401042c0301d03100c640000c000064070681003042d0302900c81c2000a042040c00d080b400520a4461710080350410000c40c000c01e2000c075840d5045640503054050507100d00850307100420000b0005410410103480b4410469190b00041103a1308d50040202196800c110700ea41c2031500001e241c07541c2d18040131381040514000400c4da0b07800fa0705410803150b08500c4501103105403144c91410415110020640280464035901910070740e0303030700d642e4400c1c425101e2040440c148100d00d0302002003003007000461300072032580d0840c42e400291407502c030a80c0201c0c6808607146400031340c0c0c000e010400104e01c0f0490f466041c0b140d10b005140480d80e60561034a440f100c25100c0f1440500034015903150b40400e005580c03413803500c13000450a4075192009825820000f9101c3d0014080c0c0030b005810318607500003017403041c00000c0341040001c0c050b00c90307078443c010090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 877366879 1250 877365629 877365647
    0x7030b042a1d06150a0512100302010c03050c03070b09011b0509030729030c030f0c070f06090f0b1008010b06070c17010e061003051501150c02030106030b04061d0d0f 73
    0x40e0f07204c074610702ca1441c810040e4004c1d10f8412060388916896090341140302d14100300c0140ba007801c4107150301d42000540c0c0d225035840c1246400d41821035403039a030900304074110300c54800d0117418010b5410510480c09415800805103040c803c0043c0003c01010004507080d21074002e505506078843e500903c280249902000071180c580d14045040044003242d85a950b0001c640346880d602002c803c20039581740c846c080643c003803086c003403251814415640d581d22844e03c030741c0003500280da02d440c000100482c2d19011300b101034102030b013001145000c0841e03c6101c4e010b4000d44419500345003000500e8207100c410342d0240b560040321100340608014441040741e5210003412103a40d202c01d40d41880100c24030299006650b8200b4030340c1c41a085040040c070741603029116210310b00790300004001d8002007441c2007508080600c1d0a0f0600811400000d000d00740d070b43c0001e02100428014841007000561048944d031801d1844940340b5142081c00b19100c01c081a140030200340500c644039586407260b1400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 877368129 1250 877366879 877366891
    0x408152503020c0109030e0901120c06030c0c050a050705010e0f1e060f04030f0201090503060405060c3006040e0607080a0902131506030509030f1b07030b042a1d 71
    0x50900400f060014292040881c050f000300b0050728500c4500c0c107003c80014054030801b0122109001183d4910a211403d0301c503860070199545450b8110f644103210780e001d001e41003411203004110f5030410039101c0c0c910b441250f01280344006034408606040841d55150301000300030307039401401c9075081c0e080a0001c13821164040070411101c05100d9113100a00080d41c00f416034404a50b1681c4005010802513401079846503000b0010000021710000b100c5910022035440207443d02803101000140001c92080c41c04029035449003140e0001400220794401c10702146c061088090b4049034540740d1406030b40701400074600d04009035076042580c001e6a40288098075a00030468400203040458074114130090b40803c0402040004030787c1409116082040840550700d07201564030545850f1160810103084451001c5000c200c00100303001800046800000f079440c0391403e443c006030182d800f07000d610051045d4190441d40c0c5416600070700140d6050031080303c0e50070410110700c0d004060003400b07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 877369379 1250 877368129 877368131
    0x909070905130911060c1c0905040f050907120c0e1506030408090f1c0f0c2d0b040617041b1206061703120a200408152503 54
    0x40007800d41c80364001224000c0544800058044807860000490b02600d0707605407040209000803240e664010505c41c50891480c80f000c1c1807500d40240603650100c0380da1155a00038504001d540146e403254100d41e10918504095a4265455502000c1c261161141c080c044190a060a1000400410300140c000d845610002810b81c2003000007081544210b5040310bc0ca1800700c0d031901d0500f045002211031030360484905580050f09035041e41c4c509a6004007410b06920842150244802d180801001d040030280d2894688c5000f04039070b40b082c0031701104d054060340c45400002c0c84002982510f054031030b503a075281030600341100c0d0304840a201034401c0e6000c2074004810440940140c0608000300310a28030410b14203141c1c01d00f01c04640d82580241c400400381c420190607a100482140da401003422170416041d254081d49000404166040c511030790b00340141c00826401d58809007085030050030480c3c00400e07441c88003401c500c009641d0200315110f0b03914105450082403032101200841840c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 877370629 1250 877369379 877369397
    0x706020726030406030c180e07030902040b03010204030b01150504030b01050103050a140403081b130302060a0221030610020d020a111c060608070602071a0703030905060906090708070605090907 85
    0x1080342c11544558401d2010076610200000b031107820100c00fa0400700e5040700061010700e07040710701c0383c01c0740300030501743c105540d80e030a4404542d9664445107240d000640210b44458803031030500d071049001c1c010300002510b51309503400c00c00d209600303c41c152a40000e0882c0164a03010065000d00006018103207150348a00440b51090b9010796168829030190b91030008034100907002080040100210b040702c0d40080160501c000041101c1c401143d906840d450b1740c0300d903030030003c82c10800d605004105203802c1d010003204100a0b04003550080e4801c503030f241c1032109070400030303070741c1c3d0800c0c0e007013840943c110249600c023084c205050484042406000960300364000f4441d080c900841d40021038980c0e598070070074080d11404001c101d000d002d550008010250070710609402034114248100b9002100045200030580b007504070b04d03c030652160450b4290f0500c3e09050b6201c1808845280720f40c070074000009011400010406e04660840d02c401d881d05c20840144036000384014984014080012 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 877371879 1250 877370629 877370699
    0x9080a03080f01080a021f18121707030206161812140c0109030b0405030f0c010902120729090a03080c010e070e0109050a0f050a09020f0307060207 65
    0x101884000512941d542001d91900b81da01049030304041c0c10652003548608450030040c0c80e04c80d00e07600c0c03150900201c4201407202e81e200319a485510400c84007404021800002c40300316100100c6c40942c0b0a08902040224103a000c1c10540103084000c0d00691216010525040000b540f0042da4003852412a03503020742016402d00c48070702e5510007402d0101c400042000c1c4103945025104220001000d80a003c000e50b0000b4030f8601240409000d04201c0c0d008102000780400c01c9406541c07818880584508001d11030714020720024106a00414401c0b01441e001100414580f05861080144040c06020015041520258500f24803d40801001482e041d540d60500580085106c2e0014655030307200f00c2800b41c29108881040c0c01c42c0d500280c0284640030701c0360300c604e040d505080d0002a680c1c1e1020f4400c03001e4145001815519440c10f01400603a4002d40c0155020b28000c2d182d90411203403071000c0c5566210644200c00c0140c11024007844840180c03101428550b41e0070700d546469404070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 877373129 1250 877371879 877371883
    0x120723010b120a14060103111207050d0606061112041e0504050903040303090b030601020304050d210e0f011b081e0408010f0b0303090d06020a0530010e0709090506010908 75
    0x341c40480301a51243d11400100010b008003501681901c1000d00b8855166070b80c0d000070034000c0c00781988a0740c20b060400400c0602006800010312009110f00f90340380607424000014400c6000341000101d14041407000c05030000380183c4200180b02c487c500e00342c9011550781600c0c207480d0b14864018030003200003981e96506d01030b0a000c0c560345809156268030794030b009004030b005a81320031440c24050042255613a0044281c03012101c0a1341c0c1024540020f1814100000007a0350391846400806641041c0035442403144083d44000e494091082150f0310056803003a441d544002000c2445240c030000040100d8007030481e10160380d240290003130f03100c008081540c000c2e0b00504944d80d51084079441c1440140100720207000300b42d01452038500c182000c500c5040d6080c030090101c980010f08581594410701c121000d10500f50010032510754013011000030980c0f04011030043c00344450000c9200c0e0107a0301d03540d0040000380c48207000785141c102d200c4080c0034000c0c096418440350100010b070070881 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 877374379 1250 877373129 877373149
    0x429010305061501090e0402010f03020f180a0f0b1605010e07141f05030a0903021906061e0609140102071a030405061005030304031e140609120723010b 67
    0x441d0018064502e001c1c14210306144428882a0400030060f00800402c2000c0d0b098641280e020329040f90000010803043c3c010f84105d650290b4807002c0000d04925907040d208401c450981d04441c021542561059910030161030703805110f107008004c0203201c9005030046206074080b0310410000c2100548880002c2c1014800c0e84159040814200a80070610380362400c11504103060b0040405c40440348001001804014481115159201d40e40400d140c020840842c20355214015032428135002e1a092020708418403d000070760850040e10850310030400d500d10180c4102d55503000d00146800300c0c00003443c1207803015030b041d4010408003090b0392103541e00204010b0442e20485a982c101407a03c1403070250010030712400e800c45090306000658011040b101280d0308190b100195414110f040c035141b014500008250b03480c1c0201c0031900c0c580100d035072480f030081c8405503800c41d81d11000714925031081440041025043c1d20310940c2c10351601c0082c200c0ca100403000058844c00030004650b80c0e641d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 877375629 1250 877374379 877374383
    0x5090403020709060914070513030227090607050a050f120103081206030a0b0601050714100c170601050702060f07150b1003090812041e0309091a0904290103 69
    0x54a824410200f03980220340003440000c0040140400d2442c1403565040c01034031000030004c00081030b032440c04084286001544e0000c02e00f030b110baa441921600307107203901480800b50030303600b80004480450110f40b00d44581c1180e100e292030210503000444031070340180070b21a0308a0052220f0601502400704030360107140314003580d580c6c8100c0109400850741005003014802d0348929135000020f812007400c80c0d0404001c0c2090340d00c800307885c82c0003a042c6c00721901e0102c1900c81c036440740f40400da840d0080640703e59991140c00401148500350451340c04115103180c04940c007044580c0040c10700d50020420f543c020b03135941e8201012555a030108a030002140b0039001d40b625504860351406201e03c4a03008030034242044035580079074400302036008061070f13904410301010002e0305205c8901c2c0303101420354400c80800d02d800c41525015200075401c0c0200c00c066031034008409181c0c0300c00e80c6001c8203003600a1045010f0365450f61002c00c24003c004103001440266605079200070a40721205010b58 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 877376879 1250 877375629 877375633
    0x501350c061c1406010e0405060102070b030a0e011a010305010608010e06190e10090506101b0c03050d080124080a0c0e061204020301150f03080a02120d0905100e120d060509040302 79
    0x4101040018002040086d1480c441d40c5407006005442e81c0006055044503042c040e69a20b0742e881c21480e4000384240c1d0360403c0503500b40380c19000c1e40c0d0001c4040c000c00d40f00980b0100040e980341c2d401103d13604000d0052411402c00c0c00e01141c2c40d442c1481e0300c01d00c030120b070b26101a845a00c88004d2020000255104e103685540404103204681c514010180c0c001c0c401e903246c401504d005c0c0e10081c0829103000c9841110b0400c00b420105109114456001443e00300f0111400121910001001c006007403255141c0c0585080360520f07407270030160040c007440210380c6e108100340c0c03182a121001410a540c10005000f21070300b134110030382c070b801025008040e151406219030303107400d00500d0b0a50b450b1050071500c58000c450180541c14004030701a098035040701040d500c906140c4810380c504201c030300c1528002c070710104908403a00d00d00d4100c006228400c1060b1181700c040e80c03680c0b40c2500c0103046c84c138200760044207880104e10b00007000340601180027100450002d82e11804203842540c140c50a0b4010307 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 877378129 1250 877376879 877376881
    0x1e060103062301122306190b060d09020a0906120c080a02010e01260c0c0c0301092406091820031b0d0b04230a030e01050904090203010501350c061c14 66
    0x47d032080c0300f2099141361aa002800814403000001751070384290091540d407180d41e003442200b5512042d844002401c4407090401c903168441110803448854a20102c9480780002030208071140c010850407041c6038180c59030345800e0849001901c1d01b04022000140c1d06c191000415407000111510754000c00c140d040c031030b80d560081851103003070140c00c0c5807007030003607040c182900d0010b410b04804490000740c0e40120461096030754074980140009a001c1e8001070b09010725001e000700ca02d010404102d10442244031101072854403a50a1034401c102154150004425403802c6800c140d10b050b1500350041140410180540e500394403800103840540e90307465928000714041c03014460284001c1029002402031240d1a41c00401c2101d404900c0390400a000c644c07803a29481c5d9410005540b580103000b030005684a01011900c01e40b11201c4118440e40034411407036801e140c10345240f4852151010300801ea84602c1445055031085071803004009100034043c404064602c0792000307240116000b080b007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 877379379 1250 877378129 877378141
    0x11061201150f080108030a080405031c1a04090b0c0903012d0501080a0c0b131503090201020618070e13150b09010506030f07030e1e060103062301122306 67
    0x40710450003018051000c04001441745c00350010554100c036069182c803901695562a0030717400d41c0a071300443c00c0b0038440d1450711082008550003003001e81e4804c0501c1460300c170030300c410002a0fa9000d0405042001a480810b51404162004111440010b800451440c1001102221504001001d0300001081da07a2600401485024250040018400802000e0708a494000203610346108982070100e0004404640102c80c2e1165402002448000007600030b1005002d405080c42080890043c02448002101081c9031140c40b1005602d020040504e03505210340f40190080144c48541030300c1d20480601c1c00101c40042d00400900b008a002c541c8852050921405201c1030300524030903007040c810009421484a25640d020069180109155912829550030419000107100c07582241c070001c0491070000040580c120ba2280204100800310f00d058480390280b0072448801d080c0c1d0000c01084000358a2184001d4980688064003421a00070141480c0e2007075030650a00c04d402640400c05 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 877380629 1250 877379379 877379387
    0x31107150b24030a11070b070f03020a05040b0c011119030e0307030c020108040201270611010903140717030f24010e12010f050a022d03041106120115 66
    0x901c110706403601c02004481c10b14074000800c10744042d0300704074404000184020131580124a04d2940d480f035080d13688565041c10450150220f40d0036004c00c00322001244001c0c4688201c03905c480c5242c1c1d070b090800f82410301c94680b070b0780421400c881c1592603a40840d185c2120074028002c0e00600255004050761030070740a02613484113040b070180c50b0024070600380843e40100071207032001c2e4246409201035807680f00690360f92120101c0301d0b5100080d0b00c805020b103011f4640760402c0d65096210300e00c00501408502c0d0036201d505c1c40041c0025400200c0001410000380506041c40c40703030b6001340320741c41041110041c40c5c00c100e40c07441c2c640f240c581c180203101340080c403841140b03107152800100e546428030000c1c0420602d42003c03809180c0b41114000348603400c0d8130a0064000000040c0402d04006102070043d400000540d0704071070100d82002c00241c1440603040d243c00c840b0b03081ca429aa01c0d611400352921003840d0440d0031000400040054403c100c000d540030f05031843c05100d00c0880088024 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 877381879 1250 877380629 877380641
    0x2090102060106021504110d14032517090d06020a1d0d0c032a080c1804050d08220c140a0b030103020607050a020d121e0c02010e0103110715 62
    0xa40d08039060708011000446a2542d01c95000301000742122047c1307010400000d0321920142c10f00c00880035002c41c820300440100418800e800c41c1c1031004c40e246905880802180c5030041c842c480c107414030403059400740041c08841d080100391034007101d240d45942041e41d0155181c02c0004e40310b106c0c621003080d8101154003080348241d40b400240c040641c1c5800e0052a03d000244c51350807030600030841900ea10580812010b42c400080140c0ca942c1c1a00560344c40c074003108c440c8154038030f02441c3d10100d645585244202d810000621071601010802c2e601d040c0064600140054135042400f880d0607070a8040c00034a00c1036240340000c5191101c00002c0480b154080c0380300e809521001c020402c20481940d0540340c04490960380c4c0c4559103446450403040746002500300307a0902c80001407001a65182e081000300e6101e0040b40040b000c1c80407114102c807120100401c0290200ba40503521422403004080b506050000b03c188020b80c4108098000860486078450900103006114907180a40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 877383129 1250 877381879 877381889
    0x1403040911180d15090510060b0901080f0411100e0307090b0307030204021b0706090311031c0c02030f161d0f06062b090303140c09060a0e060a03020901020601 70
    0x1480c00c080e8444800c03920b070030307400d40c00c10b2050322107071004014048007082c070034030200c41080c040040038605e141c441d1319036600c01e003800f20790f6180c040001255080070b0101d40312502c050390341d01c0d50703a0307294172a007200c0703100203081030710034000581c40d01c0200d44074808a0280c06a41d9160140c00007000300070140b411410f0780008070b002d800c09a2540e46500d0008640040c0d1b981114050b880b1000140c4d5069404a0140c20681910403280c00007a4150083c16900c10789024030b040018040001050650b0350622010710403508200d00d0414034800e10800140444500c02030949005c0120f9150042c5000b40390082c901c1d15140a8030200022140e440100d09032010001d10307550640742c09403500c0a1039000a040710300440c00005c000301d095415900c10005081c1c0c1d103403d2503003640c520484000800401004602003450040c00c1000c9401d1900c0151050140b031081c5882d18003240280582a00012140004d1000000703801c2c0705540c9110207000d411040d550010707200c0001300300082c5480d40681c04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 877384379 1250 877383129 877383161
    0x3040c05030d230a0318030809062a0d020c01060609151106010b1c05090601050406050d110613050d12170f040609030c050312040b0702010204050607110d14030409 72
    0x18511010400c1c203002000c401050480f00e4880c06001070a42c041e046101e420082060902403410801d03400485041c0294035010032a40c6680e034a07035141f54503418031003102c03c0000400c50402145095503004001c40581c515000d07003031969603498542034480d0b940000c0d010034501c11061002241c007040c000d020380d03014a04012203140d4801c141e600c500e018040c1001e1f0803000189001c280c0d622542480700740c0c6d0440020000f61501c2c01100d5100c035000e0160600c40d909000d8002450301e00400608201500014503111884400041042940c4001e904540c00c103c40c2d4000200d5036149040e0f6056140180d160720000c81c08803600410310060001ca0a420b0391219091005000e039160320140e09c5640f052000034180080e06042c0c4006040c00390040c0503200000f101003501c1680d5507864000d522420000003941c490080c1039081c1c0c09075006403500058244140d201040320080601030030403000d0182c05109c4c000e41c0760118401589080510b6a03400020104105085803150300610701c21400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 877385629 1250 877384379 877384397
    0xd0e0a11061206100e0d0309180603051b0a1206140603010e21040f061e05040b09090a0f05012606070905040903171315090b060d140303040c05030d 65
    0x400d40708010b1010704100d000c1c210140d40c9909a0780030740d4010016110040011180840300c3c0350003403030b000741802100307240440e040d29000b02d418540940300a03070764007401410044611b461440f0030400c1c207440341c980c0655510b10000c2d00b4800b9801c424061401207102248075040c0e608004241c0d13801405503070003680b504910401f2100040f41e84a03010000c44250000a03810380480d042d180115041a1100700d040754001032036940001c01d403a401e040640101c500c2c0c4c01c0071001642c181c080c2c0e2041481021041140340c106262424250358000260180019543c041c0c540c0a022180c3c01d0b00143e240704081644400d816040f02e0760f04034050010002010f4515082100400d00b540f68860325014507200c40030300301050301642c0e10348200071220603409401c0c900900d0786992a02c842d84203070707014030740e0641c0c014801c00c181c06468005600080c4190003921001c2c280086040c00f504142c0328401c50380303c00c00d804481400214003450081402e1481c45007050704040c284008011881c2c2407107143c413 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 877386879 1250 877385629 877385647
    0x6061217030f010e07020a1e030806030a170c1504060c182103260a0e0c032107081611120a080a0e150333150d0e0a1106 53
    0x2102c0d80c0c1512404a600348564540e442c090b490510300c0c0d000184040d0180c52000e030880b00d10142007001501954034001d2584405007416294668204060007000c000210710300380050040060900d0110401101d0004801c3d030408900280182c1c0c040b965107032078121400c0740503441610811780c86e0504110800040c0f80501c003081040740c2034034803072048800c45000d6003414040d00060307290745122604200c0900c040b4000400201c0100c407010740440c81d141e5602480403000410071140040900141507a22503a42411880c5c403098500c911100001c0001c2400074030114043d00d07010720466258122056203141c4090304c1c102d0301c0c0005010320b40f8042c00407094040022109501d682000130b1540c0d40c09150001c440f82c0b007101d014150007801c0780d201e07013850000090045108000c0041258000a40b090b01e494129410070400040d441422503000050f184c14522144100c540d80041841c000300c180482c0c0607a420011114000e030800e0403c1018042e0f040705a01910340121011850303d0499 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 877388129 1250 877386879 877386901
    0x1801050a020c21031815070203060f10170c15091e0f03030408030309070e060109060503190c020c01030c020c01050d0e01020f190f0e010f0f0c0606121703 68
    0x1c03900d0500c0f41c000070740708440c8030b50241c00441c2c00420703150950b07907940f40b03100e48040070724028500c0c98000e03039101090201c20304609007a21016503004000d845140c580004401400723802801402c02c06208010010f0205e6201707210844900020010f4420b41955404015034034043c00c0c20054942010404c078203146d030300c00e4414014034082c2c009040880c00e021010500c0c0815a10115406200000e00400d88220001c041c5200c0c65144003100c180036251082280001d8083d0345080c040345000900b4006680904051684007180300c201c1200444410f2003001900c148400e00c2015800140681d801940d16002e200066143c90008200000b04000002c209104503003502004560b0b404001081180070340461301c1142c00000110b803620140250010b510340304000366804684070030786401d5014000c800c080119034050311210180100b4143c140c80c950907108818041000c4035002a001404500c0b4070707000b4185030710103120140381d2490800b1121403c4007500584010510401c20341c0030b00e13 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 877389379 1250 877388129 877388143
    0x2070f09020c150a1d010c080f09030d1e05100602070603150f030c0810270f0f03050a021e0a031107093b0c220f021801050a02 56
    0xd5a90041e40c8200300c40ca402c1c00c03e184000100048900d030800c0c8078030941541c1110580d000060600c801c0d00445c00a15801c0702e5640103010049250300c40024405442c00c0c0040350310050400a50349030036150b0b07007904105c80340c0303400b1440c00c0e10340c07203001a898810034440c1c0c2d60302801c0d28040103199810440302955415081c4114420180c865181c0c0001344100417419004201c5140c051403100d03141d10300305683d04102c2c09054403920405c0c0888215010500405030f0080080310700d021250740300d200080342e02c040c80c441038501c200e0034600d84000424580d191401030703000f680c0f100d89800402c40001e0a201d44059900070348040313034000442984020039469840741e41420682c00078510f03100d045003007a18542c0504c110520b0301040c8060046528610f1542942c15a0f01d1100d441201002d10341230254481031250541c015100c2044a080590303501c07000d9021448e42c0c81c2d002c0c180e5003918090314000420f40a400d42c020802c0c10f8801884090401c6200090901034104810000002d5031031003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 877390629 1250 877389379 877389389
    0x110105030f010b0f0c0601170d0903030e091e070807081305060a02130b0307090e06010311180a08100603060b030a0f031409150a350a0f06030506010e010602070f 71
    0xc0c00069613001203181c4000c540303401c01d10106071030701983c4d9034282a03049034036148161100e0040400c5805994804c28507001a40e078962500914100460305118102a0042c0701d2002281c220542021051402165602c102c903195115109491b26100c01041400007808140c02c0070145480c03140011000310355154009165400140c664034252910b4825518981c0002c10360b22000043c0642c080c1d021204c0790079148031850a080301d4403004011004c95418101c1d0000158080c00440b90180110f03d51a40c0f407040204000503454589540c1d030300b080340b0f001c000c101e220741d5104104100045809440b2035440200c0240110442d40c0e21100818082102c004041040a400108405c8901c6040d640501800742c5400300d01071754001142001d1b402842ca4102090b0b810211001c0b0b00528403130b18000c003100940400d00c101c0d5402e40c41040b01001382c580d040303107500e441c245d140c07081c818070680d00207501441c010300c61549003003e211400c0606030040008c5410594040c82800312842e15081150307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 877391879 1250 877390629 877390649
    0xc11010c1b050304030b07020703200604050103090510110903011a01020d260106050c010f090309090f0617030702100e060301050d0f0506010e090708030712030b0d0602070b04110105030f01 83
    0x28200b85031031800c622035600000c1c50700c001c100c10310816540c002100802e0fa486140035007401a240d0341e01b5107110071581c5500354000320800c801e20141d4404c0d080071218a100d042154400381200b01c0c1c000588450340d620880007000812000e6240c40c1c01d001c0e402c0740ca00d02e03c440c81303d10340003200000c2d10b404040c5a910103001c4607841c040e5461088000d07100c2030901910700f070326441d44c4071280245542c0c42010030b20221343c2480e000074a01e00c514030400e55019415120828214641500362014040c00aa1074004c5070340d400001490f00c240303503807541c04800100c02840d0b6444d4148104420300c08081ca51030300f008000e6004204540390002103074117403030048402d8040000c2c00c0c078015880c0744214600500600803c000002c0e035107002e8040c00d01407001c1030b00359082291101107a540c0c0e07001d2500e002d42118030702c904050209019030321108242c6d4002d8460b090001d669100c01c400c0c1d034817162040390102e94400400c41844000b903550b81c083c41c1d00b440c1003403a50500b0000000301036010300480c4007130 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 877393129 1250 877391879 877391927
    0x1a34030203100e090616020606090708310501060b0315040f1b031406013204150806040506040e0a0b221a01170d0e0d0b0a0c11010c 58
    0x90890444a00c004140640c00f02d8035516165004070b4407090207856005014041c2c118490580e070003c21110f200362000380402c4910f641c1d00310100c4400b203018200c65928071507110741c140240001c58004604c10ba42e00c040072648622460007508465980d400441e03c000c06006111a101039082b268410000840300890680720600d81c0c00700034024118003624418410840d80c6d4034a80603000100d1600001c040d00c206a0b43c0d02c0300640d42c80c00c80d00030142540d041e04c42c000340c511000e6956100d0503044060580d041c00d440324241d801e05540150380740c0206075070b20b003004007074a014050070b0380c440c0040d2001d1080340c000b6481c07980d0321051158000c002c03404400c0080c10004658104a01c0343c0400140c0c0c1c00c01122a040100b07954400b201061003458031300c070010a13401c840b5613144900d140700e24020035519008000803550203407003111856111110140901c04588180c4150b80541000030f8001841560018040c04e8403100e00040541c5904021030b44100541002c1030b10046400708025020f1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 877394379 1250 877393129 877393141
    0xa0c02040f0f05150a080a140c10170c041d07020a0209100302040605040504020d031d0406030c4104090206390a02060c03071a34030203 60
    0x40c007441940510100d160003941c000d490b040381c12032801054142d0100c0304180c0742c1c00034812112128000d40303010740e11410900001907520030401c1c401c1c0140006881420000400050488266101540029280c0da03001c480c2031040001d41c907003003000c0001152616180000040c5c0e81c2d580c120050000080c2080001c64450007071058180c1d4907402401c0b03101c18640020300b070f5449295400283d004610b0300f6000725180c1010b101d840d00070b68009050422410181e5002c80e104102d03182d00310703480d10040c800d440440c2c0f920700515000c0d40c8581c09441429043c02103080d00c3d0700f05e000010a8040d000c1d00c038495855614880320307801000348482c10713189910000c0850f0107014002c03002500320000040074801c50714903010216440300545100340c04d8400580000b90400354185145030260400038040d80140b07000c2c001030070201d5031542603a003048541d489042c00d00380c0c00c40c01903014220b203804102c2100c2620712800c20303c10b500a5240030096100e01240b41500217031a206050590010100c1c0c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 877395629 1250 877394379 877394381
    0xa0308071115040507171209060319150317030610050a020c061207032f0a0e0324070215010509100e040c0f051f082a071502040b0a0c0204 61
    0x1208092450b0785581c0340c180b80c0b908950b11140c9201c1c082889035440148400c1c9803002c20820911945000c0a6042ca0300520401c0942c1c0c0c40903109684101200e82d035643c0528840c040e801044140c507440c03091035481c5080911511940541d010b00c0c1800410400c00c050f40c841d08141c0f071a400718503005440714040034040c4d1034035002c603404e554413100200c1ca0300c58460780000080e1103400240c2e028082c4404010040b8001c0d140011501c0c4c2c10080d0349c22140017500c5010180001044514009425a09540c080790034102008019018080f44e9880c0c80a030040301030405801c0001d42c401044410740150100e20649011301031700d0310a082c40340c0402e03440150380b01408060150030000741002c1c01d00b403800b0000860a8401d07104201c0c05058001840d00e84a440e00400d03d043e10041d00000c202d0031001c440b416030041c502d14500009103580d44420a13640c41e0722070164480a40c2d596154882d040c2551010b0154014407412401004144504241c440a071090140c8038204000160010700c0010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 877396879 1250 877395629 877395643
    0x5030a0e15100807140112051f230f01050a0f1407050d0e06090102070504051305072d03020901050d0f060e0f010b0415060f02070305190614040b0c0c030f04080a03110a03080711 78
    0x1803900c04c40160b0110301d40b046441c4058842c1c4603070ac1c8c200b15000a80c000d2000c81114038000300d020032801d00110b500e0070300644580407420304600e0301c030050030750a00701d81160b42c1001c0b83c2590310b5800246c0b085d800c140c0200c01b44d2068217003124450b0500002c03d0000303640d030086005403401280c070785000c01d0079a160709101c0f613841036000c0c05650146803102d45000740c828103da541c0c02c0d01c49100025080500401c800f003410b80390080d0030203100d6824042844014400f800049031f01c84203c88900f0086421446170b00d20301c500d0640503040181c03e01400b0750035038043c0130007144600e182a000480d52000c51400c601202c0003030420300480c2c0c10b02401603090001560020b070160080d500441c000c02145018207080502c950002c00c80640c80b80319140400c00101c2c0c00030074421940740803c107200b02020213000c1d0000c03a0b00c102c1c1d00d860104c10b1000316503000369000540c0d40d4080280d11003059005510f440320f00f0040e100510030050a91002403003110007500801c24045020200795150f1307400d03ca00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 877398129 1250 877396879 877396921
    0x180f02010318210e1e0a06110a11010507051002090f09190b010c0803090d080705030702071a0f0f03041109103c150f05030a0e1510080714011205 64
    0x20181c10078160785d120003a00101c1c5c1c00394814a0280c0001c1b449500070b030590183d20903003000411046005658030401c0004200403e4103006041c8803010010300308011644108510a10140e29203107518281302d07a4a80c1021654841c140300010000750107100e14001c0410b4000700c001082099044005aa440041800c040d000c50030000400071680310005103070721490029a51003035207680b800c600302d8207404180c4851006801100040043e40140c40d80301320744000c0040594a0320901108641c40d0fa444183c124448008c04002c220074007103a02c3d0840d030000c905031030310105450720a0b6000c0c16480c03240100103510380f41d030790101d9061103803415800c03922021807280111a640130310785102075113403440740c0f50703031b400d0030718001c4c03d40301e10803045600d1410b02500c03803d0a50301c0345031561010340300c07005100010b03102d4ae0395507003544184640603134020704499440c1921a0308040b03481c0c0c01e065080d0840410601c0b40c0418241990348541103040403401008001070940301c0c441c4004010000c1180 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 877399379 1250 877398129 877398139
    0xf040f0b130203010f060c0503070330050f06040b0102070e0718060c0210031505120f071512090b0627011508090c011b06180f02010318210e 62
    0x100858420781e680218140d600c05100101010780c1c440003140c258190a0000304250001d010741d0300081e0040e107480081d50031480415580088060140705c00320b510040701d112550f10390b81403194240300020341540102082d9400e00190780f600300041e6444d003c602c580324207042028001079080d4401d804e05080c1c1c803d4105d010740c2b02d0b075988000401c0b100d00324070240d20403405030021403c1d450181c891011072130240541c1e00d6800f0328003810481242c1e4640b07500c00042c0140703801e00007a07207030500c01c000180020225a5805401455004061200d440c9404c054549400508001b01e11102c44556109008590015000184c240300d04e1034019075011003544034107808004611183c02164025141156580b009015907a21a4046d501c001203c1c101e408104030b1900541282182181c481d040d0340548808160b15044107076582100b00c00031020f442c81080c0413064011076a040c001c020b1000020180700260144540750700040074140841d072480308200d1000400c0f5940074600003210750b800185 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 877400629 1250 877399379 877399399
    0x807090315050118090b0106050703021606080919030203090904050c031617031c09080c0601060512090c130c09050301090c0e0606030103030c03050a0e12010614030109020f040f0b 79
    0xc89007000e01402e00400310200c0f42d0301198200d4080c2440b4041040e03805c071041080507403a214040e200d45c1c0c450207041d000c40c0030f50650510740d030281849481c010311140d600c01e00c0702d2801c0f081c041d082409900c505500004407411000110340e001040d55440755045820303408035200d6181081c0361440c0302e0000c64050256a0044280c04001035148d0100d910103160398000fa6580030115480744689150301951840000d4100120082c40e40940d92640c4522030f440e24000300c1548007858140260300440008100003140483c920052841e18ac11400000043c918210300304002180c000c100155041000d581b00700007d5401c1c400c181300c86c01007001178020442ca10103401c00c3c00da03030600c2e402018668926030380401c0a50500710b0480341202c0e0142d0f5001040440c95404994580c05030040340b04100040e580c41031140d80b01095450a8103c6d03400002d0103a01d80714801100d40401041c0c10f10903403400d0004030247e00c4030b0b410340c07031403a00840d00000c0306400211504001e0480302d40041d00503071000e03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 877401879 1250 877400629 877400663
    0x3031b09040515030705101e0509090f0103120318030e0301060b041806060203190e0f0423180a061d0d120b030705060706051003081306170c04030308070903 69
    0x1e4911a0302c50096003178481d015190014400d2000d0321074003800001d901d00c10b140306600b04140e0020350078902c5142c4079240407814400651440d10a59032081c0e0341001c20010810851402d08200e24200b1501303041c440e02c1d11003501580c018410752401340c24001d4440207030400c0d0344c080d400000a040f07001c1c0c41589654841c06e2550580445007064002c1c580ba240020440d2800001621525074a02034041d0b65000c00031400c8603100c5000801c02c0d001034403102122001d80c1c031401f90032020300d00700c14020311201004e401d65000660292510700e9015480301e080c0d90220000c102c0340308280c1c01840128240078086a1500040c0281410a6903405992800340200381d01507101c1e8101c0b08504800d100c41c1c04102d04140e00e806030b5103c2c0f80c0e804041045200e000540b10b03001258400788041541138520f560f500c030389400307600184440c000803046117005e00c449170f0403d140390a842c104644031401840c1c82102050103104500010301481101e07070005020030300c40c100e0000511b50243d0401c00c0300c01c0d84 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 877403129 1250 877401879 877401901
    0x5010e010605130e0d050d0f0906050a180201120c0216060f0207170703022206240804021305040519060203010611010c0f1b0804080604032003031b090405 68
    0x150003094890928200344040202c803902030544d00e8031558001d043e00c40d09000056030307203600c90810645002d80351010f4104c4200c1920403007400500a20011500c0e240c5000508111070b0512004503104044d241c0000140c1d80c407195040350f00e0300e501400200440059030a900d046840210082401004800072401c142e0041040802c00c0541d0200c4680030b03251620a906007521848550140e48110070800261421803020f0801000380c0200c6100c1d1890b0300c000c1c40942e4600e8016040001140c10390725503074142d80b00c05256500c01417600c60841d0509500048502d940a070740c1c41609a03d401c04a0203200c2e041c840e02c0401110740c2d06080d0303882041d203400720180d0024451340011030400c0d080206005410b003d601e81c6c003170301a660950004d51240007568800c80c0c60341c03c00c0e51a90400044400118000014000340071004020b003100c0c5042e2500401c240640320b80c0c0c06c1d059601c00440b0800c020000141d0760460703d55115040909020f0314074045d80d0203035040145d4843c3c240010b0098400d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 877404379 1250 877403129 877403141
    0xf04170f06060603071b08040b1201060f05070c1404111207020115051c05031b1b030a150b06090411031e24040e070303020d0f08040b040b04050a05010e01 68
    0x10003801c1d11040d58903001040300c680011241c071804181350300301002c40340d00c044070300e103d03900d02c1101c0240c2000c0d00c40481e012660030001804403031040c0c0c0d000520503076410951503035210100b8030b032480c03504009a443c001070422501c1f480304194014096005240c0d16604141250300695100075119400d140d0200c1c00e401007a100500035500c0d0540010404095400b881d09070341014024045200f04601c0c40744081045140c01e544034001401010411741d4031780c03400c450040c2c01c1e074014000b07a00c1c2410800031000b550140d0703e103c4e07400040b00300300007201f00007544a030b50341e040030000702c502200c8003280b80d504c1610945640705150590640c003511900c0069801f4090184511140d0511115541c4200c00c0503a0004540d40250042c90603103004040505d611b080e02400204503225041700d141e1411801e0340045000da0420180c10600581c80380c400050b1203500c1c503007074806007072a4503035484403031001c0c01c0500b1800745071001809010040001c5000103911100030040c50034080603003402005 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 877405629 1250 877404379 877404403
    0xd1b0b040302061905070e0d0c09051005040e2d190308041101082202010309080408061b090a060c1a011710020309030301050405060d06110a1b0b0402060f0417 70
    0x1004c0c001c02007800b5642c0b15a51180e0303043d0f140c03aa80b8014040c00c001c0c0702080c0f1442101c3d06603c011000c1a100c2c19800f805001d00300000440516034108410841550304100c119400e942c0b2a0400c481241c1005429900d980d001c00c00300e0040d024051003050a0108050b088000210360345803070800c042d403219650340305d9401041c010842c80885401152030b40019202035400c840510604054446006032010600d4814100080c1c401d07013030b07078a03030758075400030b40c400310994100c5410010300c0c0391468030f5812245d0099104074074003018480004c402c44d0440c0102010800b10000d01c2080004044150702486c840c411810540d69640052480500c1390002c9182580145101400d4040e100d00a80e80078442c284003450450303013003401703000050200419841d800508070303420303c0c08110380b0b10034604015810070307203595075200004015111443c80080d004030b50503d80e071810045403c142c48150043d078125030305036480755100c5040025020720f405c005260300415480000384036001445400102e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 877406879 1250 877405629 877405651
    0xc010e06090a12231b010f0905040b12070305031b1507080a0b130b0a05011409040b032b0e0d020d0b0a0b120106030b0a0b09010311150d05070207090501080d1b0b04030206 75
    0x1700030f18004503444154180c1d1040403030301c6e0800034001480e00d0f40140612100141480c2c40700d40d800529285029410341c4281c0303403030304000f4000107a14002c610450304812840d00815107070a42c100050418840102003108020480e0040b9103d441c2d581c00110385000002c00e04003404000c10310400090022a101500c542e80440d40054194040c00c4c5c070300e041c0b00c03100d90054200001081400082c0407152142c0f503260083d80309000f0703005202c0b100303c040c44859030f80c90000e2883e0041d01900b8801a440e03294400d007045075081c401680d402801641065021750030241d0341d11000c0b40b25015000310800716a110289540c0820003102c150320490840380203644007102c5031211000a0211504d0000954203d26600014030100c0c40421403411840005414035041c0c0c00221300a240d150840d5000e414064ac07128240035005604000c86000350032078078002c0001d9403501c50070941c0c403100305500409200c1c017448018241c0e88030b055151076054016207000341c5403505240c000c0d1140c1044400380c0c608 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 877408129 1250 877406879 877406923
    0x40e030c011406030a030c060e03070804090605010e060304110a0302121501050d0f0f030e1c12020105090705040b0f031005060a080a0b0112020415080c010e06090a1223 74
    0x2000c4540c146038058140070b801703852030005a44040380c0d00b00408000f0360f440d0340c8030750201c01c2410f81040104a59405020015103d500700221901a50340c1580f020381007000061506185958440480b904254001e1100c44404880d0300868161851948040d40c0300000c40140b0426506c081070800c280314200488145603a210801c025881a103030f03501418141d10b0380811400a940c07004008210f0b8000d04149003000078010000f050720311402400301c01001e80310001300401c80701c02c94004030f8030040c0c0003d1000d480d003070003000d03594a40781c45680e2140d9110801d50308141c1711140d04480994004e01601c108071807c90460011780310965600303000d2000c614002402102c0400c54020f140d034170500340d010700c1e4a01144a8480050303180f00340d83c425039698080415005140e901e900030f0a00c0720241620100e508009030082c40910a000d000d004c08000c80605541c41e6088641903c6504440c59002041418007002e000c3e008410200717034250382040f08010100004100480380b0040c00b1108078 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 877409379 1250 877408129 877408151
    0x61015095d080f1b031804050a020307080a1104080a060912020a08031f12050610052b050111030f01050a231018060804110604050603010e070905040e030c01 69
    0x1501c03440000a0700d014000d000c2c400030742c0c0f0f010008080d0f5458260801800603841e03089241142c3c8140106008580c884520100a081c41e005043e400081402c0031400d40c9000c00c80900317101d5008000b54503055a54961502041060003500c01902c040c004491032803400e03180920007440b044006036040324415803d001c0c0a80300251074111940c3c005101c0382103894941020074034011081440d5101801100f020030040c2d0150b04000e40d007406280141001d081030220000b1203e03050300003500400840802c28000c030b002048800410701d0002184403490803504181c1d00404042031a941c0e070720000020b0114008544051505070f41c0c0c11505030481d90743e9042c1504008908d0503200c1e1145103801c88100d40d6151110000f18008000d0a0064800c034020800e070001e181c1c150840f0011501e04001d0000b4080d0100611504d03400c15140310346007505000005a40d4001403241e1213400e25140300141d0700c0b921a52001c002007902400601041085500c1c16469070840200118250703e89074200c40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 877410629 1250 877409379 877409549
    0x30902060f2101050a2601060b0715050a05160c020607061103010303030b060304020d141c020d030e071a031308210a0501152f06101509 60
    0x1282d000700120003800e2140d1040101c6d2000e401c2c0302c0b883c0c5550342c000c0041c451301c48500805034a442955449800203107622030b8011150003502c019481440c1100b0001058803801e810345019080d8140300b54520180d100040c054410000d00a0195090110390020050000060341c143c2c1c1c0710391010701c6400503c006101690004650195214400d00706002c0030420300350000392100480c0c81030303800f500000000840c0e10800b8008a00060b44880003201c40241d00d80b01382400c03c040c2102070102580ba00915010080c8490610540350300c0020114000d9941010313043d4085900120b40e039151801420280e1a04c20402c0200d8011801d45000a401201e984220341c10394100d6510030480d20780241088900e240700d039440e01d00b8118200620703c070708402e0415460031603507004d00a0805d464040203008500425512450800002c0c4c40d8015030103400c1005101a1810021441624110f480000b0780e4401c80508411440804440445d40b9114400b0200c810141c00340390030b1303e00711001d0f100003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 877411879 1250 877410629 877410649
    0x80a0804030b06031504030f180f140a1211040f05090604080f0c0f0d090602060f0c030601140d06030c0b041d04031e0825080403030902060f210105 65
    0x41120204020a1001450000300b0b1504400d0140c112400200a2400c1c40c031181d400791002e501150180c160510180d07445440001402200c00d84101c18900d0b11076400328080035030080514580000702e40b02201d031900003152004000c0c1035800070010b40303541049000144040203440c020390070302d041030301000114010607004542c00710042c810740d0b0391078480741c21640050410400c03100041003044120070040140040c0916890003a102e04288054040c184031040d510120547d007001c410003000b000580c094030f5008a1500c491503482d40c40c040100c400881c05900324690b402d003c40c2400400c84183d0210080c0e900c02d505600e06240c88200b0801d5a0149119000d02c16107091034403038a050000301103e4001e4400e00f404541c1e000ba940b14514000e01489107140020382c0f100400204100c21a500c488540b025108012819441d03607009003001c0c00204080e041c541c94010540441d02c801c4202c0e1100b90200301926114002c1307251440f0401c816280740c00b60410b003440085607a00c1c21500038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 877413129 1250 877411879 877411883
    0xb2101092d15030b0a200702010804032114090d0801031b031a18070f030609060b0405070c1514181204080a02011106060d0f0f060923010e0c0103021b16030c080a 71
    0x2c541080c20070f900441c0c00c4d0270010030031003c010001040d11041034000408001140590101284940310760003b081c81140080000d40c0359031200d1400c8599a40220445040d80d82000c204600a1070100c03c12000c0c0b8103d90000302078a055075404917810344d40808190080c10070166402038035624000f0395503544e0071401a181c0f11340440c10200b0010b402c039813008548910420000c40c01c1c10800d4009022640c0884821003c01c008501803410010002049500c2000c112820003da084280041d024010700501020240707821079403900c42c0c0d00f000c00c0300d00c11280140c00f0055031039440700c002540318100002c0803804109500d0644a1307125020a58501c00c1c800a040100309159984502ca200071004c0c1c015508140303206040d00c045000f45c02050320a034020020340c814181000c450049070349050300325625503498101c0504c0480302c0442e00d0507103404246030160700e50141708403c1c1282c04a041c0e176040742c0c2c45142d0080340c143c0003281090003124014512070910554a10b002034842000c4440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 877414379 1250 877413129 877413191
    0xc0f0e0306270f010209330a020102070c091d030408101e0609020a1b0b04150204050901080d02010c0f09030206130b2101092d15030b0a 60
    0x42c2c080b80454548a0107001d102c0c114000000e5a020080c01c103c1c41e8a05100e050f5000940030056003002c2110b4111400c0c3d55116405030074a44a490320020841c080c00983e203c0e001400b41d42840c800d405982150350450860314146583e240a0402000e8103442201000c40b00713032210b00450780200540c0e04480d000409003004060104440c0d00130a81064060014111070214a802440d644901e0014004904006a45000b080000740060800044154945050210390b40c0020b61059025402c25401101902c124445014910103800b40340c10194001808500000e003038600021006812044c0f50000c2100905041e021030f1810032481c00b800118082030410001404d00d0f10082010100c800740140c0d5941d1a0000601c1035400404074242070f12800000c420300410391a2075a0040c00d080c01e0401a100391400d010084c1103512141040035a5141164484030841c2c0c0c200f44024168800d07448003441d100c0ca01002019410303031b10041482d290402c151410324014003183e0002e1070300c3c0700d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 877415629 1250 877414379 877414381
    0x14031e0a092102150a1a0d0f0b04020f0d0f060e01140f0702010f0f09060f0b220603020907080709050d03090e07090801020f120c0301050f090a0b060a030c0f0e0306 72
    0xe900401c00844000882c114800c001d07408030040503a114241c00b40d51301110109603201d180e410840d9160802c0d05a0344103c0461300c2c1000050460025a00c0881e0b21400640d01d940d9070f800020054124800055089104c0c0e94a60f0204a00c0e44619100b503482043d042103603400f4081910b08a03030003520054100041200491300060b818194941e00206510010640640400802081d6101c90030b03200092074590301c2c20020400c0c41d0040071000c2c044044100b0011080400094981582040c402402c00d202000103041016030741006016540260600005003015900200326040454000300060100c2902040a05d41485030a001c682c042e0307908008141004d0740c18041002c0500721406010743d00c3c0c0c001400300030a00241501381c0c001003e0903250684810b00d000190401051921507140400042c001691440d0010a100c06c00340c030090780c140c0c2e4143c09400244116a80960b0041011421142c42130740b581040b28018003554036810758407030120050300d81c0b46210410340e070305400c000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 877416879 1250 877415629 877415663
    0x340906091410051608041212032009240306091b190c1208060a0b04050904240629030702100e010603081b0610120305070314031e0a09 59
    0x807001c0c001c03200c00c00c3d004804c400700c19543d000e903503071055000308034200c1c406145200b0700541403680c4080b100130341001d0040060304800012411031600198080b04800700d000b50440c0c45c5c1c0704c05410824401502c0c2c5803600f8210000021030303001210213034070400c002000290020700c581c1070f02d4005121482000c0c1002080307451a101450000c0c021000c00024400c0c0001043c0c80c0040080076000e1519006e890341401c3d418464007601c590080100c0c1d4008000402ca030361035840c11079611940000c114034044e0716085504200040700e840c0e590917a4242103000c90044401c0d0000d15490340c41100040c00e426060784070030701e9400f00701ca034030000d600540501c081ca902240c21441081144a00020315241c0f00c0d580c01c00e00e41c008044070398095600c0c07a42101d0130341e001c210b40f5405c60312040b03143c2851894404081c00100300c224000b020020003098007030030140103941610703070070350541580303612481e00701644020b26103a602500da104004001282c0c04000c1481031440154020121550090b01c0b0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 877418129 1250 877416879 877416887
    0x60913030c0f030e061201030318260a1209090609050c180f04020a080604140103050a0f03021612110609010c021e060a08091b09340906091410 63
    0x361400f41c06009011408803656550b85e40107000840404420317041d81d504500380100030070303801c1d1400c03068590049000e1118030400c2003c8040300451001041d105064803195034244801c5010050020b21800300940d0041d400c030361280140c64180364100041552061007600b9103d081d140c01e002c0b404200052400f03a0031010510450150181c14001e41c2c91054000c2422a44074181410000f140c0b4000d10101c0d2a0a024060304001c040e68240802d5046403110354a441401c00002e1a0b507070380300c0342c8900300b41c0203010288080c0c9015940c400d01700c1c2c0c1c030324242c0b00c009918841200c011480c03010610880c034000094860b07991060390b401c1508006582031160040f444080c65189284e480c25040156859200410180070b032340d038440d5023506100752028038108401450041e43d01000c5480700312501d460040f194061580042c00c19001c45c240c01c0d006424124080440446810002d043c90701500411007501311111a41d541c60340507a035401540305900e01882c02c66100c21000560701741e03030348a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 877419379 1250 877418129 877418153
    0x70608090d1e08060d14030a03060803070b0115230304141c0c0201020a0f080705151302301f0509071a3009060403080106031e060b03060913030c 64
    0x1001d07080f22800000c5480d1b01e030070300d814103008280b15800002c460516980c140980e60041c19164000d50030120255210340c50158140501c0b031100d14a03983d0a00041c0c42555040406c41d0340000007041c80d5120300140420b64001c035810354501c00345d004644207900d0001001d00b40303d0503803060f6000309411520b08551103007820200f40d04510440711568007089064400d00e29080c40307280c1886e500c0780d44dc41d10506101d40e150109500d04000400c00c800301d0407006100503440d904a4021580c03105e681d0101150540c201512544016681c001002c2c030900022808201c0c40b1290b03e000290304030000d00c106880040f100c450807500000300c01c0041a0001c070a07103c0f81c001d100350880c00c10403040701689030b10095540d2401d10500d64940c2004403039844042c581c1080307a841c0139080c1c0c0d1600307031805000300300c043c4250020540d486154244252141c060601c0e17204244905001c1545c0c1c420502090b0f1700b0907074141c2d2050002c0c0c804a0694800c03103d02691461f4180c0b54030f03026562589805d81500d00e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 877420629 1250 877419379 877419391
    0xc02010f03060306020c010510050d0803010303210c0e0307090915022a07090c0516021905030a110f0316090c05042105010f050c0f07080903070608090d1e08 69
    0x502c0d00340100010380c8a001030014a003000000144506d0700d505c0342c64800c41503034086802128854800000b162800c02101d0560760541001a001604d40032004586003d440200d18074511b00400c2c1402680d01105800a0300000c40c100c031004c5843d01d64550481d407a540009016100303a01c003820454140f074024012000303507480003c0228400880390220007014466a420300d0300020b20030700c40740000780700300076120000345803090070545001404607484500100c0a44545000c42c0d40e144002240041f0b45c001d40409408c0d00d2103214546001d006459800600d20722a0610414010709400c000400d450054212030f1010152481c040304980205410725201003000010880498208090486150020000050081f800a8505081d800c42d0880c04046030031500f040d05200740300710404c06444100804650081d9a22130b54030f0580c0141c411341841c1909801280000186103800c14281441812104150b4070350345103004003150703a4201051040399511000324990840d51041c0300c900d41c454 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 877421879 1250 877420629 877420631
    0x40203070302090c1902191b050a120605180a08071109070804140d050405040b040207060e06070807020609030414061e0408010b06071e0816050a0201030b010e010c02010f03 76
    0x1d440340c0100707020f81c6086844034002c41c0000f810b00c1205510000c42c500280c19407000c0c00d01b215124807403150303100441034081c241c00c181c0304224526000c0540541d00400c0010030b00e0311400e540d402c2c1661200b03541101602e40524000000380310b440000040c0325486810f038003400c4455101c0d1b44200e400e030400c100a80c1c1c3c040e1103014900c0c0e95210f0810041c000d0072544c555000b603141500c1d0a01c0420007022544550b50094500c18520580010a0700c065071001c407800300d841540c0c0c01c0410003d0007522405410710f070401203d01d40480012070164020070041d62105491740c2d034428142d03900d95003581c40044582c003c100c200049040450560b03c3d50400900c4240b920304800481d000d03000b4102082203160f84001340800c44030009210700d00c1140c0c002c0d2076050034100541c03103141d01000480520b13080c8030260603a050401c005c10080b03801c0400480000c5a0f1072006040c89a540e1030195001ca0101c1d2405001904943c0550310341850028169580c007c8642d0f81d42c01191810056050b04045c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 877423129 1250 877421879 877421893
    0x1505091306020c031201060c0201080a0e01021c020a0f0239030d18050a06090311151308060709181d0318090105100203121b12040209060324040203 65
    0x1207060005000764000e10300159142c081c04a008068407a041e482101800504120900180d0300403028a521001000b400200c003040f06841c240a4814486503810403c03082d183d0f1100c608950b0702905404d810380c1d44255800d1191201079982c1e41400445420800703180302e8901c06007000842c0d5000d5552840000f044580060022a02c2c1c64516981c01000c00c0054406080e03d941e151f040c0e00050204076901c504032860030002070442840b5000240c1250101c0311030484070b413501c00e080c1e0b401c1038200e40344541e2801301200155200145004820060040e00c001c5043d07203100c2c401c0801501e14100350740341180b014003903420003052456001a00034030075560030351000c041070015003681c8040744c2a0b000b290700d05004002408405802c6548500041d40c510700c586c43e800016100c0500710380120b00f42c1600c5000b00340c00300421180b50001001b0000900444690a9249031030080c1c4c825291450381d40c45850800d511004801e15489184214040c203050560301c1c0ca02c060f4110b400034003a2585 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 877424379 1250 877423129 877423133
    0x15110705100b1302160b15151602090a061a0a0e191707030b0c041a0c03220b0703054302040b04020315210703080306131506110115050913 61
    0x81b0b4411201512402d599401c11092818900410000ca03c0c01c04a090301d441041c003103280d090600e40c20081d00038000440003401025144d406000949494002c0340e2000d81c103206204400d6104040b660b0014550320a504100e040c2180005441d00c45c030441400b5160030154003000140d12043d01e04041d1040c4040003020030100007205004120060070f2a030340e20b0a01c0041640485003892942e281c0004200015008001006440c2001c9201509500003980c0f0028a00240e13102d4114000014001400754100b5030000b0003441074071007010340f045800c0131000c0d03041108804401100001003160740300743c0c1c1100601d07080c6104a413001348002262070541d0301040c201d80049510481400d03074043c465202c0c1c03030000e80c0d1281d002020030160050389901d0801a0301d5020600c0020804480400400c0d0346584010180b001303100b120340d040042411420400c0c1c3e40703140354414080490031100d81c010b4650307010700a54246803030780035070740d80c170302c3e00d0074052003001600204085414401c036128000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 877425629 1250 877424379 877424393
    0x60605032e0801060f05010c32100f140601091403191109060625031124010b04030309050d08041e0f090e0a02010c15110705100b130216 60
    0x2d8200d8200008640703080503121003029005800c52418040c01281d0080000c1c0078500b500102c2101c3c45c034030340c2e0580c10707441641c1d2407030042c00c50264a409500c525100d15006688038900030505000c0070700072100c103000d608681c0314007958100c1c000381000c0400e020b41d040d50300c0340c030103820381c05011140c138600d101022030121030360340c1d804540c107078002c1048924038a003010009401c4902191b002d0f14202030300080c40c8440d10120b40c0b51f51114030151924041c5400344507409a5450000700b80e4070008410039400350000e6080c2240c0303000000117000803507540300c05008d480649504d070300c03142d0a42c0d00342810082402071200301214102010800071480102e5802c01c80200d240c0200d01203001801e24550503141c142d55000395546a02c3d10802d0540218001460520240c0a00703040203c6440750030b00003a524441c11403204070506045001079410b1144c0300078800b590103402641c1507014415200c0c030a4448034040303541d1111441d008914030b124564000c201048405590407080485076031450 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 877426879 1250 877425629 877425721
    0x504020a15020619110a08150901030506070207091a041a0a08151302010509010c060e01060b0d0f090f140a051204050f090606031503030403020301050109150906060503 74
    0x107005802603010700c0741d21075600c1c401c078006502e401c0092110850b2030f02c0e6000c0e18001c05141008012011001c56440c80030b140c83c10b128002e025107020b680c0d607128201580d03103a00c00c0d0307801401441414000100320415205183d000695402c500c0d2410b1070090400c00684500d80c00c1513403052400c0380c11100d03a52a4a0910000c05000340506114000c410716200c555000074004115155414410340040c1e90010490f4410502420701c588621881d040030801402c00d4240d9402540c41c103200070070301c402031a003d0108440354440502c01c5031341c000d0900c010768518401c0104840b40c060b822070005a91001c81820719000e8400300c990094841e102c036403400381c003c211180682000141409582441c6103000d04100058400c05540c1c00c0c0000800c4003032000604c05803030843d00101c0002599008c0c001c80c1d00440d0028021b02a6507180e81101c0020b01d1101001c003039a0500030070004000c011070082004031040c81e120b00e415951a0520002c26041c485022401c903000d10122055000d4540161 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 877428129 1250 877426879 877426919
    0x2d0709090c170309030a1e020d0b0a150e0f1308210612070902090a05191409040b01090b13140a06090209090610141623100504020a 58
    0x101d44940c50903209a0030805541070000c401e0300100324214254400003154548981d01204c40038103020021206188080e1500c00203510800300c112100500c6001d02d4054003030a0b250904020b00d07034820a040705140032520071420707801c082500085411030510300050f40200512004010604541c0c1e500340f0941c021201c00400ea81108903a40c22091400344840d1310100503129002425a044841d56403071005214201c0240d40000b242c07191030301c491200300001c002c0600749441003048101d51100e0f1034402c1c002c0d001c902c6141d04041030f6034544854806c1c041d54100506802c03c0e420000d0b0003010f8954800c0d1503410910b40c201800b074480441c82002d0200c5e480e18015905030601411100c251202940841039041c010301c203003502a85e9840c2165042603084800307880942c481700d001d803104007a003464101d1090011408428030942c04518030b0b4828400d4140002c50b29211187c0d42440c0c10441100501307911666414814181ca580a00c0e00140000d05100070030747e480c94502c80e40c070403d03028 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 877429379 1250 877428129 877428143
    0x20f15040204020417011a062a0c2e0c0f080304060204211b0609180609020c030d0b1c0f05100f0b0307050a0b070210231b2d070909 58
    0xca1090045080580449400221416480c000e001009c550203074002031800c2c4030700d07d1a2040070101c0c0c0810000440c008074003606100001107855005030742420808402e1052584108098200314400c5130010b60450b4052040200090191035264076900000c10888803aa070030840424507000591840c1e2031100c100311694405c140d02d00d40300e501d051610702142528030303210f078041c02201c0d0804900f0707060320346107207840d02d04012104003480034010750761000404610000e030308420403030048010220504044414000c005a0006001c02e04180c500800f0f8500031a02d242c50010326404001c00b407450081080300c20488003000882c04540541800c2e01034290b481d4402c40c0c1e20b04003403000310000d1030708440307080341ea078507151007803615104d4605d000340b081850504602d034160003840a45a00e41c0700c44104000015804680300080c5d00c69240040c24209103805501064000100c62494000c00d555a030704803600c0203681550f00039101c0d1307102e5517405004000700300c40a0901c12240d0305401044 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 877430629 1250 877429379 877429391
    0x3130f06020712090b160204020d0e0705120f061902070b070210061d2d19110c1e0f03030a0501090c2c180403030504060c020f1504020402041701 64
    0x42d100d40640042103c560a00c0341e420303010064034021a080da00400300c01d50440107100c0b010303c0014020f103e888441c2c03592900d040350211080c50002600f50130355900781e40030899a0070700c489890303807200c8214440c280c43d4807034000240c22803850710084a900361800030260031314040b6920302003500022201200140e000d0741c80000803600718054000207000340702080c450507080f14108505910b0052205108080c25446041f44100c10843c01c00300c0030f01024218600d040c440070889420984245a00d1641d041442a0ba688040041101c9004820000074010800040c1000708c041110940009440c0600240c0c5c1c014100144025841905103d030700190075810b1661050480e1140d140c51003c210741801c0001514080140c18066610b004441c16400314201000400b8007510440c4142d8002410003440304068040e04543e00441c0729144c240186400c041c0204c0e40e900705403141504650000b803c056411481200c0c854010b40042c10240c981034550703035512652000302c2411412699141 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 877431879 1250 877430629 877430633
    0xf120906141e0a0b06162609032e0f1b050c0730060c0f0f090315020c07180f0213140a0302042c150c03130f060207 51
    0x181c0d2160721800c561000b01d800b42c2d1950303442c051490000d000034220350f83d0302c041c04040e07510b0b01c064030303005105102814651a210701d02002003603c41981840140744100d400d0031022581d100f640c50008020b4000e204140e10401c85c3c010070780d51140101100200001f00c020904101d0141481103031048101040c4143c40070001190f6401c0550304008005044c4401024a00d01145450845441c4940c0725000d80e081e21803401500048083c50304136401a5046104000b119003040790707a40700360b440b2203c0d41c0e0b0001401743d074000000340e484d40c0081c00c001c005000080022060880e22041c50000505008110450700d1810a0a40083c1d888400b611613141001035680254032002030703008410350070001186041c2160412030b00030070701c4409038103500000303940700e03e04040000d5400506c2403080c11b100307030406001c0745400204c3c3e405c40940c0c0040c0600c802d0000402c0b181c400d80c04401240b541e55401406000342d000a4000701c0240030500000010800c59812400b1942c0030340303401179a4406074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 877433129 1250 877431879 877431911
    0x120e0d02060f0103120f1404030c0e100501021f09051518030c0a02010f0c0203060403050315040203090d08100e0c18030604020a170a06090602040e06091005010f120906 74
    0x5100842202c0a5001031000800e203042240c09100181400702c5008003d100a403641007028000000c0c01001180c000280009250100100e84400720850304944030340f80407001c02030302030240740d0243c3c3c0040c803484010b1415101e0443d40889501d800070b203003007840da540b500301192001690980580b5506104c42c00d00340351020151075481c04004c520704920f11281c40d442c1c01ca00f64000e81488810001c2807007007070040000c6198250f000301581ca11346418580601543c005484051504031141501d4000e41481d1003100c0c05042c07000c00405000c007007880300b181c00c030000404001100b9045503000808140c407011041c00b44007071b00440c0740c13100c6a41e060810004841d03811942700e41c1c4064240005a128942d4213401c1d1a000346010129500d040307501440c04ca04003200070044d0b03140000d44001d1200c0780e07000d4415204945c000309011384520080080e8250b06465004e041c00c20310754100310941c010311103d2802031207403e28200740161110010200c0f600d0003c150b400c01d0321540300300115070007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 877434379 1250 877433129 877433131
    0x506180f150408250e130201031b0c03031503021c240911010c24150f03021807080a05090703060f14070503071d0301150b070506010b0f0d0b01120e0d0206 68
    0x40c02015a00c2c00e20f417210518140d50b001d407001d207040540300310b29801e59200c0d400604898110800702c405051038408010b00c1494a81c1301500020300c4c10255100c3c1c1d03806021600101c0381c0040500c4071000c3c2c1c1c40683c082c3d51710a00c1003201c0c0340940c1070850640c461081c03001c00c5141e0410384005110360310b500b0581012060f00502d91b0400181422079400104802070401c000c410f800c1d600b41200c0041818900241020f190303031204050320010005140c0d00095100e02901d03c25a030390140780c5141c2e010300c41c001c041900c22402160713141c4005012510264025039000111304101c440e5030382d40e625807c08841c00d00040105d042d4540c043d1000b4031500142482c0c220400307107829841c40c54484802000000404584186ca2040c900c200c0c0f002e9074250050304008400d12400d031100c40e601d2001811940c000300c41111076000c2c00000294041c0d000041d605401c04949480d4900a00c04190a004000c00c08415050003440b00f0300c1804d9440d24468111b003184114000d00e8000500710b0301038501a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 877435629 1250 877434379 877434433
    0x13020d1211070302010c082208070302031e0309010c030e09010609080105100509060d050106031a0702070b1809090a0f050309121b12030d02030a02040e010506180f150408 75
    0x44003200c10001030342c0c4607024280351500318000c0c83d2201000000d814405500450a232a9155444c602141215001c2030500490b8804c0301120302d0031010b150354400240f6240c0c20907205030018003030140a54041e00e042c0003414864503020040721002c00001e1700c0040203030003110000390014024049040244142078102000710010038400c2d18010008075000d600900349401203842c030302c0820410000350028800f6551150380c101c1150712a4079074000224040b02c4080c018404d40d06c0c00614029058100e031141e14036980c00508010040090003211003002d0124181403141e49286000b0403803503800408541d106502965a48483c0010011100001410030f9840e401c01c1700c0603030003428400314006943e0001c0e83c100b01c9815000078114150702400b03142e2a8114000010401c00c1582075000708140d031240c0e00c005120fa600e5009100d02070240303d104250000c814148072840c0c0c9444009100b40c0040141003803481c00309009441c1c540d4015921441c05179102c0c1080c542012700c07580d08103140320 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 877436879 1250 877435629 877435633
    0x609070f050906030606011d03030c030702041508060412090816090c031e050a090807030224361e0106060320030604180f02010917070b0313020d1211 66
    0x403c18000290725040050080c0d8140709880300c8101e20845000f1030b803c030040008003500e07140e82404a02c01c0d00c1e5402020100c2c0f04601e0824590360000710780b0030350303030640741410000d116964960b69440d1407502c1c0e5684800a00030010750024249404000841302952140a002178031841c11602d5016290746101c18002c0c5400c14080040c40e911080e115040c00400300700106868584039041802085903102c0901502070000710340e01856000200703601d100288800b1503054106405000486a074169010145841002d030318140b038188409c0251650800c481e110480401d0146419141140a8090000080004a032000002820312030301009008608041c000b03403191001c8a0481241e08104441200001c00820307020740b683c0d4085110243e0f4960210382c01c00140c200b8494102d40d1b03960490004e82c82391070210b540001c1c020700c000074501c1340740145202402c00c00e4904040c0c100410202024103080c0800c3d01503507a4107064080d0a0040d119a000648510002801900078082c0042c80d6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 877438129 1250 877436879 877436881
    0x90f190b040c0e1e0d020d0804050d1a01060302040308070b06030f1c1805010522050a0902041401020a05032d0307170114031f0e0105042306010e04110109080609070f0509 75
    0x3600c0e219a0700d1885d41e81104d203005910107602c0e1441840c0a10b401081e008400c0341f00c043c0030840c4400401444c000d011042c40802ea90303400b0308405034819400000e14200050004ca400156a20032050308008001c003070314005041e5044451801d000d4240d44496600100c0d226071900e60082c000601030006110711484440c10400040e04c0341c41003140b0040e0030f40f14035460004400010b144400030b03003c01054840400c0e583d0b011400a50014080c65035144000180c1c05032540c000a40c440c580b0398020091030402c610041c00051506140c00c3d0b040941201e08103d540c1300d0302c080002e510030112a141d05100401620703c1d80c04000b016007140011405440e16082c03560340024480001204210509207480c2150401001410f00c0d15480c400d00e609100901c410003030300300d81c009840307921288250b800c0600b2141c016550082803140d51000f81b001000318002c20102ea04139912000c040c108090728590380e006081c03510000300c800d061190042101800342c407102c407803c170009103021184440c035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 877439379 1250 877438129 877438189
    0x40302061e210601200703081c05070c140a0b040b07050d020f0304111519090302220b040b0a05240a0305040c09111c06120f0b0105090f190b040c0e 65
    0x1b80e0412808090a907a42c04504504100310747c4036040d481e95450041801541461500075100c07041021049034448806410440020800078174180c00b11707040b82042c242070300d0b00c2d02c0d18440c488000e03103c83c0c20002c2c100602c04900105000900314500f41800b60703903491415052010541c42485c0d87e05101d07142e044401c03605000c00740151078198140d004c1d001c0110138055000c5c0c85110751544002d400009042307800341980400c9001171072200703000d4030520250045034104400c0710b00460704658410a03004090106040888004c1e407510005400303a03c20140309600380c4041e030840c152100020340ca950402c01040308070385004000f443c042100380000030084000300300c4c070b00500004039034094100c500103040d80d07450b410ac07100600c2c10305160600700e01c0900f000082c0d90a82902529002130480c00050300781403858010748641a1103021016549039200140c00e8828058031b4814000c1d1181c0e1407a540e41d58501c9148998807070b940720100619291018003440f9040418403880d0400740d10340d0418 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 877440629 1250 877439379 877439383
    0x6050301180b0315070305040605010f06050a03091a0f221505060a030c2d06020703030503070c02032e05043801060905011103040302061e21060120 65
    0xd0031007160398010403502c804601280c43d05060713898450882c10790794144441250075a00c458040ea000d0b000a100c240e0300d0301038110003828544100c80014801301b00300e45a8038420b40c020b90b101e0340714040d20f401d209052410040b20240641c0d02c0c6024000791400d021b088981001c826000301c071a03119100715034100da142c0c0307045500001102407101703403a2000504207a540c070f0203180140d907000c0c210580b0642c450041c5144240300c1c42c4021034040700d0070090110382c0007d560714030484203654000c08025040d641c0850341c40d0009088241480400c01000300141d50500c03080e40d03010361424a10089207030703030400c00f805102c00d89005003c1c41d127444c0c21300000c0b58010f900c0c548800c0102d08140300781a5140c082501ca03140841166503143c81c20030010904030380c0700d5800007c0b1a826600c14081c142c10011240d00c0e481940300c0254050410444d000702008556003400d040064140c0580c10003580010810080c10340000f50601081c045040109644c3c020840c400024107500007404a60040040c2503 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 877441879 1250 877440629 877440659
    0x15030e0d020109170703031b0306081b24040b0c03030604060603180210020c03070815010509070e090c0d0f1e02040501170a09051912080702030a0e240301090606050301 74
    0x2542c1c4c3d10700180301000d043c002d8102d5000002c4000c40c1c54280009924001c005000c0d42c0150403041c0101c040d0006028411010021155401004200d0794800d94600c02c9040e4410103107a0070022041c40001980900c400c003402e640c1140c8405160340749005804c0100b1200c00342c0280060510b0001210010888501499241603056031411900c00000006902d004580c0205a0b8507110790a00404d001e01c01241140c0b4401042c8400c646c0750b40ca620420114860407146040001c862055244040c90702d90030854001049414041c9030804030002e080c1524000c202644026444c0c03844248800a03c0300c4802c980c22070004110300742410702c0002490b000010031009110122200032445120495100059180d13020007241e03001c140b40c00740020003003114001a2903000c60300c84840c0301c55016a102034451b00302e981c081d43c604030340494140d89880e1200e02084d0007800c0401c49045e030400e403600901c2034024416020344c8079817400140d04140c6005422010810400b44010030041c03002040703403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 877443129 1250 877441879 877441913
    0x70b040c09020f09040c0306090e1005090c01170402010e0d03030c090902040b0f0919030506010612140609130b09010f15050d0308090a0f11040b0a03050c040c0915030e0d020109 78
    0x1058011b0076000c01ca01600250700040c29003840d101c010480c2001c001405040c0c0b60a0340f606005030b076030b020105500e40303081003115030200340403c46c8031303803c01243c020b29948244141404050345046c140481c00c0c080803240210003107540d88106c42c0c080f507080888000145410f00055281c00d080104204403030050070100c8400200c0828030510503a1030010442043c2c3e913000c1d40450b0740381d50f03090060751003200388541000f0071440c80200c0b00a020758050302e003c2915407000400d458441d1020311007030034030007021801c100d1031107144000010f01004800d4043c1100c580045101d4141c10b0602c02101c8a14290b143c20310b409280800c103a45882c14100041a00350421004655a0b4143da50604040d488010071000b00a040d05003042482210a0201d240555040000c0750652080c45040d000fa4040900340d98004400028149400d401412440005180c500d00321030f92014400740300012424410042500c1c1c0811200c10b10080009086c1079625100074459104141c544500c286660307980 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 877444379 1250 877443129 877443131
    0x11b03051e07140303010623030402060c011e060f0e100e180d09090f0e1c05130f0302032b2d0801030b07050f030a05070311070b040c09020f0904 64
    0x20a5520280d0307080e1011660000c0039200f6068001c841140c40798401d02a0401103280c01d11060242e24036071241400283c006148285541c45079000c00203075070894032004215640b41c80702c041916250310b68081e14213050f0344e03011403410300f00a5105c882c0304880e000301981f01d081c0c000304030340800c22404203011641030100c3c00c0000e07200c1c2050b01d03a4042c8181901040f604c00da022102686500c03840e20310445900220400002a8803c070800c152501c0195498140d84000ca03d11000b00c0c031403003044e1082c0003500f01646400600c00606000c080d01342d10490300600038210410039400c091201a04190158606106800120f40c10a12011040076183d04000410308181d0320401510000541c0040e5a0034519400701e15a0380101007a600740422035100b040c0704d010401c02e502690544140c83c40da1801c06003181c2d02c843c0b032100213150080120b030030180c51341c0100d020204c100c0018100503000320744810007031503d07062118403144150b0000300400d104004848042c0040826100103800440c0c1c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 877445629 1250 877444379 877444417
    0x3140a0b010203040f0b0a090501031404110f040e010209040b0d030f1101020d050f070f0306081e07050405070f080f04030c080a11030c0a050c0612310809011b0305 72
    0x10040f40380d4007554100c50b003000c400c3c00000c508000001e0150030201040c1d920161140d4840c0011410b44042200390051403144101190005d2840c21034603a4907034001d001c06554002000001c0c0a07510403420314942030b54009281d01203030500f0b02484c0042c903401e039081043c3c210749580052080401415400c00c01c000ba6408460600b020740480b4a6414040010f00c05400c00e100d039407a40308c1c030503521500414000700c2c80303907070050081c080c1c43c048502d413001405c07071000c95031001054410090328550050090ba1801300d0141e07598400c250240100d682e4081c2c03440303618100544620400703864142c000c20100200070009074041d03a410f052640c0000190384840c04006c0554024010000080701404086a203c1000c80002410030b0300f41c0c0900101d80410855805000051041c00014103034038408100144541c4902c0c07050a20080340412030116140c02c00074402c41085100d80c0403a0350400004d2100240d69000c690b04650b940d03030007802c4039514003d6070054468443d401e00710407a600654 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 877446879 1250 877445629 877445651
    0x5060705061617040b06030c03060c040b090402042c0f09060c0f130b0c1011040306090f24050a0531050609030304140f03070803040f021c060c03140a 66
    0x308410b11101960790f0582c181c1024a05015034110445619000380700d6030040101034130f80003442c0ca000300c0031041401e1625052101140c003a922010a1a8226400308000a40c06021070303844550036040714400c1d03c5940e000707046018101d402400e5800e41080030810302156001c0800e01c1d40c2c0011418003c65642d02e20b058204000b40160100b101840503400c4c0001551710700380d0000c041c00610740c41503c52502e140c00c40742c8100d0300e120003013007010003091005100050036070303000701e11490054600e400300f40380c0c41d610344100841d44107003a0440ca140e0000030704c00c10710600665800101c1c181c81071280f4913001c90300da2003c0503000900300d12102d20300104002c4000d10058543d549402500303451852030983c42d52580d0b075000b59070482e203c880203060313000800e0001c105a03030503030f0b80800035525004054031420000d8001800c03d443c0ca00841020074010799441c1c40340358a50001d106010103046c11818200111090058048203042c1080c100491031408104440e0740020001000520b8070600 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 877448129 1250 877446879 877446887
    0x10e0703110919021b120a020c09100f12020f010905030a030c0c0f06050304050c0d0203030706110d09030201090b060105030c0909130605040f1b0f060503370501050607050616 77
    0x11110300d4203c1440000c150300042c2511040781c00c88804071007211792175001e1511505036403040b800f000005030000c84140700c9070b1500f5035109400c207158840941b09a6210768100d1210049503001c01085840686003900318101021a02c604031001d080c5000100c0c41c00d0040b1382c9900d0030b01001400c014002041104103c0f80c9400c0c08064a2311454203805992190700242255000b91000ea489110f411200c1146c0d180545511100b0380d17014000c0c50406403076030740d41070180003030042c10740e2080d00510508252071014403a040c4068001e60000c161011603082c0b4051692014200314100102001000030129140c0115a1450429200702645644400c3e050002c041c61440003021242060700740300c24003420001050440b03000b8801d603459a800300c0d0034180c014a00f0721030280d02e548411030402145020300c1c055035010b00e054521550b00507032000481c0c2c0ca01c60310b4400d01d40700c0203950441d4405811500c07a650151405a0b201460002d19468807991108020400380b50b21102003403040440e441 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 877449379 1250 877448129 877448161
    0x603160b090301090602040617060303071a0c0c0d090509090d0912020d02090c070c0e060f0d02010c1a1b0f04120f1a1b12010e0601051e04050102010e07031109 70
    0x40854070340b511100000c0c4840c0b00c02140c28270410031400400e005107000310441d95000d900880080000c20340601c2d014090302e00800d9042c40850a00c00000380310000d111104c0a29082e5680345035450900c410410324120107003000b44540d0228101e403451135002031002c000e0b01c1031010b0b01784402c1e200c0d100160904242c00c0d0002d4114203100b00f407080c41451070026003000b80c81200403603c038036260b160001c840d0a08850080e030007901040100042d00748000e50b03120307140c010b1403c00030408554840082c900502e0612001e100703800e00c200311240824481d816912203003010a02d203050301014451000d0b0145001c0c107500d891a04c000a004c00c041b107264504403582c05210101c1400041c505082800000c603200302240d50300414031015204c060040710050348204004452a9003030221805403901c006016506218041103807000b400d4030456402030101d2484241079541d824500020f00b50b035a40b0301e40d5542c80c1d20410040c000215006803c0303040c104182c4d5500c500b5900d2080300c2d100b60f02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 877450629 1250 877449379 877449383
    0x3090703051c0f11030901030b0a0803070f050f0c060d0e03090904060b04050c121303032903010e12070602030c1908062b02091510170603160b09030109 67
    0x8298058040201e50041c1d0301060411a0b440d40ca22203991080700342c4d0881c2400c0100919900104808082580254070072160b501015010052098594908501d19031101ea000d030780c0410074551007420044100070b552480541d04c0043c1942c0700101000c24550300030101520300c465101e10004091704e0042090340c40503a001840c0d9189820729040c51401003003003800841c040d908140006025411031030441e10242c640114101166484025460b015610170204034101a201d1150f000780c01500c00070800da0060920070901b0807010f2038109400c483c5444881c158907008081341d058032440b11030a1714131254005802503aa0742d078078841d540c001e200303407010348c070b004000d88902c03544140d1300008152081c4815542200c0e9a640d00645001030114075186101d4020054040310050514250140c1c0100b00c440104800b6850b0400040303003000c076040c2d9800000c0342c1e0080f110f050580c1201c11900070400754040c0044c1c000c1c0c043ea15502c0c203918092141e11003030020b04031a240e1025408807003a55 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 877451879 1250 877450629 877450633
    0x16061806050c04030302070e060114130308040f0e0109050c1605010b09040f200a0b0f071e0308180a0b09190b07180e1f0305070303050a08070318080309070305 70
    0x45001c08100b829500640019070061188610104941c1c840c500d203540140d905031580c10b0384610343c00c1900d10b203a02c0551102000303407640c02c0c00400200d600c0050300141600c480ca111045003010700d402c08407a0305901c1080f03030505140074400c1e00407848003260088081d1144000c80c1c20442d003002405000c050b0001c58000003804100801c4c040000d15210019200d840e0514505219021192880012000c01603015988200c204080f100c20001410b035499807900c858140b0f10719807113286180c1ca204a05500742c106000c1090201940319403000c1d4000d581080c1c00c40303400781181c003259503410b01450080c101006030300801c0000307000308000c02c89001d0f403400c1c803a02000c0d240f85c4120300da41b0954100c00030401145141e1810000a000203055030a6076440c0b0666582d2404050151302c1e00d20064501c01d61400c2010012800c141301e0100514026210555142103040340244081030040a40007014030780690451041312404c440e40c409600442410b4980d00c89a038100e08081481d40300030454 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 877453129 1250 877451879 877451881
    0x506040b031617160905180d08011e091b0e01050a080c0d020c030d0e0d140d330302030d030b030c0f06390d081305120418050a021606180605 62
    0x2803000c6c0c2140b0310694185941102044030181107a80d54221010140f0200e00548018007560f89070a403608540e80c402e50710f1400060359040e540c01101c00d5500804507400960000000700d035002050309000c07040a01c0c0c118606010703180000c1c06c52501401140410a0008200050440540580b40113455500a4903551503030580c446000f800c05c104d9241060140c801080c40030350003011603060780700c502d50055281101c601c103900700505c0645024141d05600e83c080b5603004110501031004003200d00030065986086004040c0b522204e001000200340c00d003000d001c100c0d00d010654442842044c0e81c3c012070710048c0c20000c0d50138001c1c00807803480d1401d00c2200c1e000340f0301c04082503074214880e000c482601d100c980c01c0075521341604404000c0422884e001085014014181c06030b070700c03030280054403410300089902c1c015a90080c0d0100341075107105024811405001c1c86010740021b55200110300c0e1070015041c1c656020004039001e455265150300142501c000c00175010a290b0344101e08101c1c3d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 877454379 1250 877453129 877453139
    0xc060204050a091524360609050402070c03060f0b090a14010e160807140307120c110c3a05060c03070915030f0c02010506040b03161716 60
    0x4100102610721903420324140024401c1e0a0703e509645d40100e00000c4104402d04d400c15151090a010740084041002c03c161810030900301c204000082d64141d0031075000d1903c44010300503519a0065441140b041018200240c80c0360300106c204d0b54801800700700b1010700c0c40400000c10300440c02d19000f00d0b03510b0400c04455026070045680b0310f400d840501e01a600d501c3c00c080032040456082601c03114640611291a0144807807a40c0716102d8030303100c4c88080c1140348452064109645c03400100c0e82d105042144481d4901807218841401e2511142c625044101507030341e905034a180300d02800009003000004c031801c107240070000c031240e0000740004c642e141100920507070906041d00e007801503401140400242c641124041d01d1540e60340440641440f901000d800780885804040c159a000c42c0b25480c01a40108031001c200d6400004861803d841800203503441441000d01c2034122111030131400b00080b0950003680c944513a07806581c9150101d0610b01120703040d20603040340301c26000140b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 877455629 1250 877454379 877454381
    0x206160e130c020727090c09020a0206060a05030a0b011509031e02030105010e04080f030703020d0905070e06040e120906070b0f070e0f09040f080405180928030c060204050a09 77
    0x120300314160b08032296517a407524020310075144080a01e40145421004040981241e0409200380d4081e98115100c207596416000881c2c1c0141110405600950308021131450302012050042c0015000b505000e042907503100d1342d20005000314080012400308c0b0104880c400d4010f8030146a105060cc0460b60984030511ba0000f0080e100301d10a40c04c0c1000414a015148006400f40b540050b00d40d003040d5140e9484980c6420040031081059400d01070694400c5e07450081030582401800680b0096080c81480558501c0091159016034105103524144e8100003c058034800400e6a22540300e00076180060361a00ca6001d002d444004c408061005540c55400d4090283c2a251a0316071038144504c1172000e40480c44812a50040400c000200411190b00100758090b1281d0701c21403034a600c840000783c182803a440482d041804020030030814800403c1810b518100008500c0c000d000e0100400700071b41d400110080404ca118090700c0d00300510364044d20080c0c480100002c299540303860480c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 877456879 1250 877455629 877455641
    0x40303030911150f090f041406030d0518091b07080c0601060c020a0306020307110613021e1c05120a08090c010305010f09020f1314030706030c0206160e13 68
    0x103204496200300100c20b40c5028594040050078140082d410500c400d0340800c2c19801031200c040c1c110882c0403404d00513940c1c80c454a1405c54881000203c141454000c1c0752520b00c10b504450b040c01010440c411415125043d0300104030022603540910b90307654803151808094400420004100201e0444100114913000c6c0c18032844420459009a90301c200441e0701031010301029410188403001030002c18000c1d001194031150320300f00f0b412034000340c4002d2480c2000031202d1003024504084260210310701294100c80c0e01e1071000c910000700354203100190b4218034104050091164103640c0d042000001c2c860119401c6104403015200c0700c0507400500301500458410070720707001c0c040e2288150f6000e03202c0e03503068035080d00300000850b0030705007070f10300940c04442c152801940901010a103803000320200310242004810300c842e0074501c0700902d890407d450304104141030a044511504660008240307074007580103a94403500c00c0090806450441c001c61040323400191031b109200004140d50004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 877458129 1250 877456879 877456883
    0x1b030c0201082206022505070f14060a0f020a0b1303120e2a130c110303090a0201050310081525090b0f090604060305090c04020708070b0711030403030309 68
    0x1001996450f45080000340003410603000004440140300100c0e41907400352103811031440d030254200c500c2c0b40c0b0407a80551409002c4840e50b1062405000d60701c3c2a103a00340040c001c070712080c61449a070303000007642801144207840401c5150b1505241992080081c110181e811000d02001400d180104d00c801081021080c0c0c08110080070901e4480d4486c4649205034003080b01034030300b008a8040a4454080820815001d80c0405000c1e00582c0e81d40318007d6081030503070f03000103501520b484014000925503000e1001a030414405c1200595020078a0340c00f5903424641250b031380d0740d01c00141691042c02d82140840d485401318510044442d0f442c4940146070160807208101e0b2095100402c604404040c01d0000340c094401704442280032001d094025004d405240c00c001c816008a60190895400300000944800070f0100490050007181500c80c0143c81c00d515100c0d454503900e8443c0310707a0700000c08408690300044e003520320583e6058002081d00003a265a00d07130f01e0030010041c000c02c0f802 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 877459379 1250 877458129 877458137
    0x8070c18050a1b08040b04020a08030a030203090f030717070305040905190e070522021e0706150b030c130b0f1b060108120d0204090219030e010b010503060f011b030c0201 75
    0x8150003d01d554000e801c0454102d965014056440c0c0d80d072842c40d040c01a204a800c030200040200d020360003400580000758159800607124034020900301d00c0d1001075480d2403005e4008204060114440c894a480480d200000e500e50310545403608407250301c40c0e42e0064003000e00d02800c1c40408020520610350f004407400b010b100c07643d8034403c0a5101c10151103169400940300140710321815034501c10b0801004030b07200060805840751840007824168500c2924a0344000841901b0080c10b0f100310005408010a07421a080c10b0040b285a5440042e100f482001c9010544101c040f6821045001400100d52907985941c2c100605840580005030500d04003600d08081501d9840000749081c120340d415002046102a03c01100240358824000600704c0e54003040081041c2101d800100101501e10301c8109001401410003022151001e24009559040042c511860703a80031083e2600100b0440b050b65141c4118001620b200c032a0722041000300d00303401c01450926420226045419000782c0f5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 877460629 1250 877459379 877459391
    0x70c060911132c0c04020c0d081f05010c02060c0a0302030a14070209040f0c090c0818150115050418090c0e090a030305040f020d0b04050c040b0d08070c18050a 70
    0x800c0140d684040401940c5603c5803907a40c10300d1100c520760080d00d8525026600c100300b8000c0410242e03070040c000d10010354000342041106a5110900550201420b032001003140364020f11503004010921406040181c503400100555071940200c0d0604200b00341180e0390250b080c5800780d100d030012455500828048210303606190f101d10104c03000346600800034030709030380c581d9520342d0f00c20000107050b074040d0400b0b4000300d042c6a26201d100e903c0419500c03617000d540781c9000103c02c040d4403a80c2c90a07090300440182004590786070309d254152040e0785640401100c0c0d451040740d50380116070164400c01044500d043c85003800d50f100d0b607142c600520302c8500d07868452099240c0c010040d2030009a076800401200c01082c40303907100f180c026210303c00c0c0241e1804640c002074070040d00707100183c9184110b50306010401c10100301c9225040400da6080c07143d03002c29000651022013074500500ba6180010f10301c0200104820301001070901042510303002e0100300c10050081004680c0c40940030301c2c0c81 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 877461879 1250 877460629 877460659
    0x41e0e010b1602091b0a080a0513050c090603011b030f0b010314180102040b030702062a04050405220c03060c030605060405041a1002030c120a090b03070c060911 71
    0x1000c40300b00440c045a007407032180700343e4244021910300a156646040e16a600060a10840001424101080da9507002541032210071682105c1c0003802a500940c00c400304000051800303d40c0c02e00101044440c4a400d90390300010a001d80304011203481004603a01c070144075650141e21a05e030b200581c1c90100186200c6000550071500030245640d20740804900003014a00c141200b000002d105000150401d81da505801d1a1074005583d20310140e04050200900042c030720301241e0700f0460a03503c0550803a04004070000d28850383c06074030300070307911940041c0b0030303441420b55004624018021503211202a0900b804541101e00045402d03500307000d0941740c1c00d03200c1c3c003810003600c030010502403401d894a000c010081943c01210030414900103c40c0926680700e034104003411000e600655900c01c9032005450500f030540508100415050290000b410f5100c0b0003078003598000701038140c1e00d840d5540252400c1c581420f00800450034102c1100400100d519501a90242030f20301301496132041e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 877463129 1250 877461879 877461899
    0xe04050703090b0a050c1c02040e0109050f10060509190302030a05031b011413060e0a060e0f1c030e0a0c0308040f060309051011130306020a090b0315040c05041e0e01 73
    0x41e41d001006c0d44080c40a0307140700c840b0b90101044400034000c0145820754640302c0c40c001c640b00342d0100c541c4903654800c010a080e032240781e495024440c800604074035824030001030078038040d83c0c1105000720240041e09660f4221030340c0a0b400b4640040441d904003119103055990313540616454004480d030b68000798031400b03050040c45601030740c0d00003000c0c035543c600c4902e0303113282e5242d142500d4842e01c80c904848180d00c24442c0501503405400c010030b001e0b054107036561400c0c03420b0300750103c2a40b0269500c03031300120703201d00850340c4806841c011900b6000711900d5440c00b1202c05010b0b0510004003000020010b0383d030024001ca5000d00d0024000310380c0d07250180c04564440602900681014808a09030212076008810350082e100b88030342080c8003040a03104007810342d08219074050380020405049908164007500a0903400300303491844c50640804007a115414078410700541c4c4404244002d50b0081054502401d650742c2000c01424511482c244511214491f12108181e0031001103800307825 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 877464379 1250 877463129 877463131
    0x30c0307021515011224051f050327030a0305070201060609080c0409052508120a1b080f0a0503070806030d09030809040e010204171b100c02010e04050703090b0a05 72
    0x1540290b9a105800301c1c01501c900c0051000c0c2052544c1c6c0e8601a10070304411101143d501c4082160704c039209040505102e0f0701078030070003800000d81008400c13003481070340b001c02c50b9488041c510008652240d8480d107200c2505162181c15824040451803080441e0f15622441c41440642e009015070303a9510010f40703c00c9690300406410b5003040c0b43c0d01c00e8a003415009041414072403411516981400c641c601d83c003c003140c5542030b040c044003c00704000881080b42034402009802d116181c2003c0c1e010150200074488010b2642510b004594000c3c46800c03070940701c1e5009032450881d540c2140b54401000c035801200d440010448620114840703041c000741c0603a01342d0305c4d5280c00342c100307044d0b40700c40d5155004014550b512035220140040341080038000b400042080ca40c0303a0503162200c4403030504000c030214400c200391038940c030860b0659840302407211b40064141405000305c200c60004a038070150342d04129030084c0c03c09050084080c1d00d90300c181440b5000b0341140a0030748414040360152a4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 877465629 1250 877464379 877464391
    0x4230d0807060209010c0b280c02190302010f020d05010305010e010605030d0509030f070303030e0f061312180f0603110c031902100603030e1519030c1202030c03070215 74
    0x240c10300005002880d164028484404141481014455107036541000c1d1001191181c600e18404200040100c0281c041d2007034400c0700310014003003020040b41c025519881d181010b0080400c0e020494180350003075100ba505100d484500350742d00c40c05801d07014054507003031100712055860501c5036030010344103100d03000685000a0240904140c032200844050b008800c2081d414041d82d10030780c00f031030010004100110300c0b80d01c010480307884c2d42400505000000b498101550006400c006c12410101c0349141125403001e08540b40000024048070040c0c0510341c822103807604031002081841c00700c100c2070100d600703075070707051182c2110985107000324010700c90b6111040d0b10500c189941c0c5c004e03032010060225841c0c41201c0300001c50701c0644e0241c1d10a42d005502040d40500441c241e0308154543c041c402a901e43c0704ca01d08850000d80d80c110f99600e400c5841059600c4c0c0c10100241e124440c01101915420340035500c1c3d0400b4224400254000d07500007000d41b0400c015074541d0994000014450760b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 877466879 1250 877465629 877465643
    0x705070b0406200c0906131e0b0901030b0106031508100e06162a051207061a0123090a0305011a0108091507020a0c060e090603010608030f0d060b04230d 67
    0x2131346100500110034006820240e201110302c9030082034903400d20542a410740c800e10b4039241c41c0040f1101c40211000802c0312405602c0020051010813415031700181160901d1500040002c0080c1c1c0814110781aa0442c2c180da0140840d60000d583c101d401041400380043c081c2c0d40d941d1100d00703010f0002076048803228042411030100000e11802e0003803107584c0300c40b041001158900d0540d580750420f040b4170031032400a078000c80d281c82440301c02e10800c42e55060000620106a00e640c002034081003a62050902008080f0300f4074200514907070a45135146009030030f020000ea00d902c3e040c0e001e018446604490880b800c02200515803003140124013808866014010103a0205003480031500e0050641d0103503c43c1090700000a81c03004400c00051400d942d031510b0710a14042004510040a051795200c2d80c10900d050001e140044229000c3c1e401801600341c2da0080380c030160b00a07204a510006058001050004421207602c52114a4181c62440c0e80f04100410702041030341084c003c2c000c0c2c004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 877468129 1250 877466879 877466893
    0x10513031406330319031707020303012301030e1204060215010308040b070507031502070b0a0921020708070905010527060603190501170d03140601140705070b040620 73
    0xf580b101c00b268075010010b000d64036520040980340750072a0701d10300c04500040180d1030910181c20f0304254a40c0082d040d202031403955250400700030300d45840380307802002002280b0826040d41e00030743c840c0003403140640a03100001c9503005a4907280d0007a118110140c060807252616010450403040c7c160707940048241c1c1000d0034040c0311201c90300700d01c05c1141c203071154420100201c2c11040320780079100e41080026954840d503150410603400d000e4102100300d41131040120000b40520144401802e00d1041c00000000500b07040f032420440ea8002101805940d10201e0000302ca40c21a606850042d100d00c8a1100003081e002030034840e1090313000504007048045103461800c0740095800415140c1f1000e000090b0b25404411100d0a0380404400c0386070700c0c0c2a00311210b003805003840540a50404006411280a420b54a801c00808007030400507001c0300c09035028002020303105440d070040c085404158440314415281e41c01801000e0216507110400e10030441006000304289498070701030514 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 877469379 1250 877468129 877468201
    0x20d090803090c04060e1308040b0304080417030306280e160e0105031303120209120d0e06040506043f03180b12090f0a0506011a0901080103030509010513031406 71
    0x481f180718003141c0c1c0d12410440092580100005180180d004003a03040d4cd0700d280a4141e26904010130303180c00a600140704100c03a035900e0b00c0d40c100e206914010400d000308940702d111009000a508107600350701c07642e01489030205443c50080040d0110741c075071121802010005581c80d010881d034501d40402140301c1c107800a803180103c80940980740002600b0500703c42d0026031181d103e400c3c001c440b0f5000d801103007450f030760109503035009400a0b1000b0b403a00d801c007404240144034501032552205000e80c980c0e9403400485c0250701080501c86160015a03000b1074291084100840c016400030b50040c58407024600604074170400c07a001e2540040c0f0740a41035114441a0b14001c0c2018002d001c0d15405032410f203001d000c1e1001c0c0c2c2e407140016040b1581003103226815500e414486200b1024280104180790360409155415690541040ca89070340402004031291710898810180204925030008100042c010040c0b828050290949603680c0e21145c098240040c3c802854582c5104241c0d1290 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 877470629 1250 877469379 877469401
    0x10061824030503070b06010809030d09020f0d0503042c070c05120a0314091203010513090203070605070203010c02010b1c08070b100602150403020c040f020d090803090c04060e 77
    0x1160445080e00480034003044102052454280ea205641c0b503040000c6030402c02c4015660341d42d010f842420100c0701818000d5586a803070007a4645a1a040c0d40e4050b0101596900003580010100c0101200e008400a240082d1a074000d0710404400c44c3d6000311141810429206500c071001626084e0641556143c4084584140080017a00c240c003400300074040c140b000c0c0c0d004101300701c0707a03132408203020110765030703032120303031a00401c01c0f4030b250851426210300440307940807207044550464641c40c682501031001001840d80250003076140c8213400c0c0000344290068050a0102d0086000300f045200d05001a404d940c82e2240540d4445a1041144402c00390b040032001c0907800f0310207140c02c2c1105903640c0155420141d4840c03041c2c0d070091004108840c6e040040c03a00c0f540070f4004154550819a0380a556000c03032101c00c40c030943d1074412101c64142242d0640e003804029060510a2000c10f00346010a5441512543e0b02401011680d04040c05e043c06440f0454600c1c0700c010304256036200180c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 877471879 1250 877470629 877470641
    0x30c0f171b070605040b0601090e040f11121c031d07030303020a0e061b1c05030105061e220801060602030301030f0f0506010806160f0e040f1b03020309100618 70
    0x40c001c4042481080b0101c0d95500c92980310707510950440f115810510b00160408060703501020a420280f8104800034038186050280c041d8011403d0140340c03941000120810001c1d00e070303880b0511803011041d211800d18000c92030380400d5a20104007540c4011015020340c00d4801320010150f114107402c1000034800d0340144070744103203845e1820864030217100150780b9501560070010a040e01d880660101e03031061090302c054003050b01043e42d0302c03c10844054810701051090303520680c800720300000301984c1240300e02e80c00952094441d0355130013200c60074034072170f240e90074040e1883c00b154002203000c0b001442002e00769191a001141141c0ca9650303520396202d0803200842d0f240e8214514040003a0040005034060030100000e8030040c0b800c1088a240e240300d640080302008404805d9441072904521066a045002e80c2c010483c0131403090044090146480c43c009407004181095918550550203103015508200548110000303040104013a90550300499810441c0c507103c0282c1450168000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 877473129 1250 877471879 877471921
    0x11090901060f1202040e0a0209040b0c07060e061005240904020903032a0303010e070e1809030a0210060e0c07060f090f110a2405040510030c0f17 64
    0x10510948400300340c0c80345000c80c3d0201907070405403062a03007149842d000b0094a02c0d1000002e1110040a400058140742c1c0500050182e016840104001010742d5003182c40d5036400c8601841801c1200142907504d8034110b500c540408100300010605180144c05401c010b0300e0303012035100100420118580030790101080b00d40c465400c105c1c880725a03d007840984810b40340302c142000d0b40035072a6600c040000314203035180420b402c1040144801c1c460056202c0e000010780c580000340980d2030700411240d00281014030b40c280384003030400c18202e030008018510346100b542610001000441c454050300d03880c1c00f52a1040c00103d0004c0c8e60300050700301800120340501004120380d40c0c440c64410846140c1001500c8801c284203200080c400c000629003411001564013a00c1a444c188543e4004c400d2004241c07001c4244000502211388101c003506c026140003010002010170400c00580141410100c0c1000700f002d01c07401c46030b4640150070b442c2c500542d15203008102c0d6030315034030750119a5110007a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 877474379 1250 877473129 877473131
    0x7030e0106090903030209130603050d0f0201150306060620030d02031f09090c050f090402060a050702040608161d070507020406090c0305060a051203091e030a03031a090411090901 79
    0x10715240b240c043c240e083c074001c0e140169540c203010305001980442c00030200c1c520f41020020400110002502112a800d61500d10350400003160128090072080d241402d1500343c0001c01310500489620000480788140c480b10464044e41000e51000d00d0200701d0001c2a400620011480701007540056902c08490300014440381000146c81c801500b0541040049540e44c0d41c80104011074000a040030784070032201e20031980703000d00004148000c0144000c2c0100310201e02160703042e003d082911002580107006000aa44502c0b0b0aa50f030347e20701120818120905100290a6032000c0e1102182c880186e00700c022a592a030301510503901541040381c00c01d5950800060a0206210b03c0c1614450b40c0d4001c40d00f41015030800c0350b0036003141c000d58419907114600e21030f0010b000044a031940700039210b010500c000c2460b42e15003419240784090b0140610f0b10541c04160341a40700c0c0001e8240c45618070a000e0a0205101c0710100c2100c0042048108400500740341c5003211505a00641441c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 877475629 1250 877474379 877474391
    0xf0210090f0b190f0e0c040b1309080c1005040515100e270316060f0f061509080c060306041505101805061206120a1e1a04050607030e01 60
    0x42c9150b859a000c5484100d890401c0d1120700b04903919010795004158900b2044c03004480404c0f200d904c43c039000728158440d42d5160506107140c2c440030000020100c280504101641150500191981c0004543c3c1c012780585103c0c132051f0300d25803103003034002da401100a220103a000303062140080c8000e042c80000303400f18040043c4043c481071041d88140049404e422a2201d64412100917011900a06e1400e40040c844100310300b03100313078480b2200c0343c101c0c2010030140c41d120720034001040c071840811405403d05e00042101c12580c0d5a544250403039680340804180d5800a07a62030300010700d10350754440c800300013043c00c0340b5140d000464400840c400b203035551503841000030404540c0d1444100411769070100d10050320039042001008000c240d0f5140c1c81c250700c1e00e0051014131001014584500d40e07401e5002d044000170002c03c40215848404041c0708800805030a20400409004540c016003400c944003011406950a41c0100c2c1c2c40740c010900d94030380c50000d8000e400e44049403440c0e0741d07882c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 877476879 1250 877475629 877475633
    0x40b091e0a230904031b03030906020708031f140621101a0f0405010516050712060509010b13050a18061b111209010c0206071202010b010f0210090f 65
    0x126100204003012101503545480e00d001890502c101814a00c80d80122040002103600403003000b03140046c0c10081c0c0507050051500750000c0c00c403111701500c0780e480810104104012000198014040f020040480000203102d01803800f00c580200c0305011950640f229580c200310014016503d0380b8a041d402d2058007603120018100116101c503a10904124100070f001f00070020860102c5c284440d007850440030190815081c452441401c1c10840c0009480c003104102d4030701e50780f0140c2d218064408603039958982c00220401c001d8103481d042e1038100441c040d440c0c144600c3d0100744002e0440418a03440e5421b100003458001d124480064440e680c921465460500951403648944400503026244892000c40341010720105800d001c0803d04400d0720400000750b000000c10700024a43d42c4e8544007004071261845400300030b41100000c202c050400c29030054560002c141c0f64000c10045000034011290071500032414005604051400281c0c01c101d50025500c060056030360f080120304907 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 877478129 1250 877476879 877476889
    0x1081e070206040209060a0e06090c27041a0d0b0604020f04170f010e06040b070306050603010b07051027020604051809060705030106052a0d030906050c040b091e 71
    0xc4400400580200b41048214505402601c2c0c009401783d4040d0070050808040341015100542510701c1170300c125002401860289007151070544007030701c010021036a000151200740100480c158880c509240100110229100d913902c5280c00c01841d02d1002c03d042e89447c2011840a041690096000c21400c2d115000d40f800901c0201000c240e403078002014031880c0c030700704103d6800c0e038045079060407001c2041d85030004580d90030039000046810152203510b0240d0080a01c1d41c091a0401c0002c400050580e071103030064104c050068007601c600d240c50707640440171200b010f861200003094a04222035064125110b203c00544007802c000e1030140c444d0b0002da8101c0d4400c00103042d01082904012481d0005c0c491503411200b075080a5040d9410164054480e0150807800c00c0c140409041255400742482d11a003c808040401e81c0c650014440c00140900500304081d41c5041c10000880d0f80341c06460221011548561011418000a10104aa181072416040c0203034401104c0795801036440f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 877479379 1250 877478129 877478131
    0x9050c040c1d15040b030a09050d0f0f3608030d021b0f0d0507061d1b09060d020603042406050a0e040c03060e0304121103012901081e 59
    0x959110b1945261401a100d0200d42d00c49030168041d9070240007048120b07554809039001c0d20384010040c0d40300d680d010362641c0140704418000d04070f07201d02c10342600c2940e08242c3c407158511255584020010081506a8102d0714040c20603044180e9032a0300100d600e5404084070980da021261207215640c1e41c404180307141c025000010400e5030010b140640200341411001d08448001c0c045e01190719001c42e025100c8043c000728200740100002e04c5030400090b075100d00c02c007490b44180b8075102c155160200e035071401c04650200c11301c14001c00105452829441082c454000101a9002520a6800d210160b000500201c45c03040f21f005640c4000d9289911044050b84403010010f842498001044000c00f001d51154042d1107060090202254840b21000e054030703008000030403505d403103103c4075246114540c048007071071081c0207408041000b40c06040f11000000c800074040e40305020132009143c80c1500244489020b1561042500d5000d106003a901541501d4005401c0100101000070810 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 877480629 1250 877479379 877479401
    0x30a1103010e1f0803040902030a06080a1212091746050a05090f031207060f0b01020f07140a09020d020d060e0c040905060f100c0506060306160309050c04 68
    0x100a080050ba0f501001c070452007102c9200e405000c56141c452400e031039224a0084c0c815aa4000001a403a00c840e138005000907ca16000c441d4000c0040c2040841100e80e828808000b40445031048007132380c924010b55080030b400c201c4980d045c0c81036881b1189190f10040c040c09811403a4080c411600c1200e41d4490224501d4106000d25240008040100020300c0700b101010b020052003500203083e8004280c800c00e83c419903031950350424101c00240341c44a0090240c2c0f0040b00000d440341044a65009040055030400b024000d13092040010b82c0c5035101000e10303e4850340849001c20444036120901d00174103c01410704802551121254402e991242400816031900000c2c9041101c0c02481104020940600032262509110b10803010364403a5216154031140c4490204542e13a4810144980204d0001c03c41c3c001001c401c0d030040c00c1c00d986010245ca00b406003c002420301e04010400d103126144110401040404000055001b04810f10003075a05114024030303005162928800c0d901201 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 877481879 1250 877480629 877480649
    0x30218150309151003060c090f1202041a030a0f060b0901030b160f02030406050a0909021315030902372d05030312180106031a09030a0f05030a110301 66
    0x3241ca40e02d114a080020f404402e4203100440421842d401800d44c048281c0342e1001003c80c2c00c451541003160744000c01c1c3c00c10104828a0071001030000800c41c200c42076503100380d906000b6000760392100c264584003810002d8058010741c8501c0002941803a04a880790320034800005c044182101103844018260000c994411220382840088001521212817040306c2d0328040c144292214402074071383c000c0317210fa44180480401d8281c41c8038000d640c110003601180300115103030140d10003041c0b1820100d204445038110348020904549109004107a8403d0300600180c410400c005071364020048110005840f0b01c07154440002144d0a1501c860001c04c554201c00c030045140061402c100d01031103140d0526004554420002a28080152000c804041c07541c600155602e5290044a450003492609194603100c008020000d11020018400882104031003640d60781a84483c0d81e440b41e100d008021503010049645006d02c0355004603808a8400c0000c2500401e0380318824003504207820006c101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 877483129 1250 877481879 877481881
    0x509010f0908032a030412300c030b030102130501031b05040b0703110f06060103050105010c1502090121050f010906180b040b0a080a02090c0307080a090503210406200a0302181503 79
    0x455102602c000c02940e4100d123540100380c440d6100010350510b2185054181e00c42e0040e4400f203000f584592848a00500250341d160240c0d0541c039202511402043c1c003103031604030302c07210840c50030888800b44621a00d40d145801c3c10a41c1e07030700244d000006c1c01c0742000092080c074440d1000070f01c13001116038240030003804207040a90025007942c0f0143c010504001c1404000004200c45c20824524440310202c01655207c107a80102c0b001c0d000b009200849070043d81140102c20420741c482d600c1100e4000e2240702e00e90721200460140d03019442001111007022408403042400c41d0b00200f1303117000040c80004d841134140301042040d08075500140180d00581c041c28103609005604680c0700155181c2f941c91490300301e00c09003074824080e05002000c1d0b900c51000081060800c01c03200c1030414011501c501103c0c6440801c000d8000300c90482d105403c0112001289140c480a101d60230b0b80c1c006201c0c00d0019420301140203400c6140d03d44400800508442c0054503100c00e04040c004440e4a0243d803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 877484379 1250 877483129 877483163
    0x1602180f0c16030503060a0b030f040c080109080403060c0c0212010c090e0601082a070803090d02010c0518280e0f070207360509010f0908032a0304 65
    0x160360010107800c51007608200002221218011001c1043c0e032604045450340c9130040410304140e00390308104000100041031161403c0654030343d902c103038820500e018110f42c907101210300781d0b40c0c502c500421125060009000040454009036a5580740d8070b0300001c00d4185400040710840c02120440003a59101045103156030b00c6000700015003c00d030800052070030071030002401a00d000300303001008400e94002041b18005480442c2030b2038100025991540c0c16420410f025074400da4451289224000104090318018000e0160b5800b07140c454a08280e03040c4074094a4164080c801a48640d4500b0311107104803254003490141b03444900f544038030302d05010140d866002c0141604078580c07460420440d54550000d83c0000740c49020032042e40c0710150001d0ba800401d208007024400480824059800001c254885c520880441c0c000b4401404054024003c4600c03058014080250030000568503100600b40801c0c81401e0007419074800d6001c5551100a42058a04568500d000680007407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 877485629 1250 877484379 877484401
    0x1120b010b0304083a050c09040203090307060c0203040e01050d0b01140105040306060b121f140f120c010813080f160f050d0e0901080d3504050106061107030305160218 74
    0x1200e021a445c200607905005945c00c0312401036203400c901c610f80000000e5058101402540c001c1a0b0046c0180f2040b6008007002c2d403290420700070000a0104100000b60a141541034500081d03000115500b42d079082c411143c84659080c443da506000081000000040c5e1030f1042d0001030034140d60650306e654900e1802407808801034485100c1e400a242481c08282040100c80c1c02c9840e81c4120148100403a00071030508211480d0440c0d00c408200c0c4104410140171602082c00d0b0000d1342d03000e0703095558480004220844c2600a85540418441080c0040c042c0008029060320050107002d8240c556640c600c45510390b0f8011240d540010fa582e031401900080900c0c030080341110900c08543c100080165128920b500351001c008200713400c0684c10004440c50081003400069103000e605400400141c0d07140c00340d40c06c882070f42c13030081c0c005080c0d441000343c141d0f401e0f40c800c0640042031071038904070f810350002e030013150008010755400742c01a5600450040d00c14111400d441152800310a0341d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 877486879 1250 877485629 877485727
    0x708030403150c0914010e1305060406240c02030c090103050f0c040605012a0c150e0f0927060a0c110f030412060b0d060b0901120b010b030408 63
    0x6101d0b2820514900d0110750008820001c1d55040d644800c13108041c4001212403403500704a40350044015054001c1d0540d2907080075100d0401503d050140a43c0c1d4140c218201c000940900d4080454032501c07149140f00b910918001e078001803c03200ca0030302d030307100040160a00b82c0c0111640e03442205101e084510500c07a840c1160340440d000c22259181000203001c1d00498078480c201643d0228807038241043c81e00d009405142c211000d85801512008185809107207841014042600034006664600d00440040c00500000d400405103031100180303c4c4403800404400241000740100070100d038041042081e12581c10f0080c0854143d4045001070040b00c0c40f4003628105030811940d1406900001003100c2c100c03071100d035405094400030f00300000141507241c0069841000c0d52405020b202881e0001c8209110480c1c040f00c003641d0f54050381100800503040106040780c1c00c00104004001c03540919445030140600514144040080e1400309003010400c522200385501d550b10b1070312100f084a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 877488129 1250 877486879 877486913
    0xf0c0d050a08010308090102030c010603030513090921020f0d0806010e12070b031803070b1b03010305060a020a050415090f061704060f060b030c030615090916020c030708030403 78
    0x62030401c800e04000d18403001400094408400010301c1038084e40708104449064010100030009a40c03030b0300d00100140d0000e403020480b03051b69403002c0b842100d144034941200da40030007131002021043c2916100c2c1800311615906501801e641600c4207130003809040e10080150348c9049542c98003800150032400400034540c05404025aa00e46000c0c0c002080000d03180a0a80d40303490350744041204408070380c031120450550001046000030000000042d501a00852001014407241d010a461060000341700140403544130b14080340c0003010550061a00b00c4251500c1e030301d0141c5880107030720080440004600050300c0c1c0f100402441c0d4021820102502e03031490300d00184004410380400b0f4100107400900215503a1648109580742d540c02003004100394140541c81303103490140c1400c140c000311505400707042c1611201604003510000c86000f40c50041c90403d95894a03042407940592003c040360941c03150a4420040d554200214001007a4007030040da03036142145400c401070030490f504 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 877489379 1250 877488129 877488137
    0x114090705160b0c130f05040b1c060b0406032405161d1201110403050d0206040c0306050603010902090a0f061a0406210c0906021c12021b01020f0c0d 66
    0x2040750001c0d80006016245900483c840d12540c6907070f03c0a5006211300200d94030300481074200044e0100e00d520300030f4216401100c007040b440e07202c20140032442c00d0704d40c0c802c09000001900d0100252013a40140440e0501800006055403680d450400d0f40b030104208800e00000c40a220340e0a61003030007501c0d80071110304203440c0b0400300544064a6440b100c4214103488048401c2e10f101611458030141e6050302c403500a00421a03400c0d904082903000e03000948240c05241c10851000d400050b860b401154015074007443e05155854103002400d01401c0c0039455501d40c0341260260b81c031545544d000b0b44550340002201150000d14208545550388a081c0210340b00200c404990080025038040b50b02e603040c0002130b1191010b0f0003030b44100da0105140242c0c942502d14410641c440c0800060f00c44507000c0360848988858074903803c2c60340c1200c3e80c000400c46004880b01e0b054940191042c1020340e00d00306005c03085a4101170aa070885d49082e600710034003141d000700d801c078100115402e200c16420 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 877490629 1250 877489379 877489387
    0xa1b150b0f1f03200a1e1403061519050414040e0304060804030516121403090604060e01020906160512070b131a1008010507030608100504030905090114090705 70
    0x20b00b0340c03072003894101e0074196141c1c1005400900003d000001101660b9015511604044d0291864080c150300e4004041c2c5136401081c03440c003400403840d0300c4941c0c1100c1c609540d545e10420484c41c1c0e40701d5032040d0111342409000740c602c00403965100c1420003525081d80700c03410500e00c05141c2c0131014460344100e080c0700c20006502c80100459050b034016203026485540c550605458510403820500d201a8075911084184465003e80e090346440030b41c0c950325100d01d106540e0300300b03000644071304141d6000000800e0000300213074032540c0500442c00025080900c54000607402e0740180307a0a42c440446180d0300f904210040c1722500c0e18060034141141030050039151070940744c400600d032004810000103032406108a40310146191014601d04440518003441c1426690240d44210f60080d03003000040b0313038014068010701c0183c4141c0001080315441c10070508020302805041a014458880d50204d12900c42405642c00f820405603e50141440041488800407004080e842000700502c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 877491879 1250 877490629 877490659
    0x105030610060c11061c0204090b0406051c03021002040f0f0905070801060c1e11100e01020a020d06140705131a0f0c0c030303151e0102030a1b150b0f 66
    0x110700c848015005407032004c00d005040c020940d14400c0070140d20f003045055282e81d502c020300303400601c03d0b41c1c0d601c1c10034420660715005110a1f58064040c841d4403200da16007a403c01280100030224150280c811500084c0d845032940049038080e811019032086042010302c640860b400d1200d00074a00d04400304064501680000e000d10f02c107020b098204881c1440c840305120a034031034417089003c0f0780082440701c4045d280409181da0300c610003a01803181c4500300f8071118002e54014021043c1078019000c40001c580c01c0107019556440201c50081c1e442c1c2c04030480ba000140b04600c250041d80310729a80703918400c098800010075a216450700c0d82c43c800b080d06078681d52000d68a18001d9805a203031201081c0c6880b5003881e08090100f9014031000c0700b04110304c0c071410350425401e00241d80c4041407a0711642010105a050303520ba60242e40100040c000c010320810b203440e030880c58004000110105a03480c41c404c10b080324840703030034551203000c0c005032441c2c0014403d0329818103d03131b5441045000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 877493129 1250 877491879 877491887
    0x150f030c0b120601110c10030654060e011d070806010302070609050105010803030f24010f1b0305030114090c180120071d04030c0212101409010605120309150d0f05010503061006 78
    0x76070343e980d015461201e15414503c540320640d42d8540c603881c80620009403110cd0202d9400024031520303070080c26800c22240c50903c0c0880d003600030400c59903021001d40c0e4280c0190065403150404a60150380d4280000100d0801c3c0b0400340a850704002840d603030306040c00c040100d0400a00f500b15003070903420350b0182c0c8013040700a00201728003e0802803540e044904040e00c2c03070807a490040500352511aa404101a840340095040c2e40c0006040b0081c400b22009010014104503045400d12030204044592091014a01285284145040016405007100742d400d040d68210408941e0391000b241408006489042e0914105086042c05440e140a4a00a1160982820103409401c4455004903040403c0c014001d2821000009105c0f618000c1e001840c90002200e0100195117004408220303072516402c00010685901d00039030400c0e60900400000b501d02c500c1609098008100003c2010014000c14401d1025148009440c0d80340c01c4c1494100b00d0300401e1a042c2541c455410310036242c00c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 877494379 1250 877493129 877493219
    0x120c0c060f04022b060f0e03091201021e030708070e031f0e0a0302150a0501030b040b070e280e010b07060b0301150f030c0b120601110c100306 63
    0x200d040c0c07003000c0e0780b240e002091000c154000281504212403030120b00580c062645400d009201d000c040118030300d02052a011070301404181c50480d041000342c41c81503c0d0042c0401d80c10404200010701e49011140c0304c0c44036207510000350642c031202100704040d494000c0704440c1d000a640c181400c0428a0900098039074003180c8466040d080c210000000035002c0e5480140361501d15802c03502d4004850401960740c0400b038440170205194040000c03103042844c0980307030490394007101082d903903191b03a0758801140d030f0028410001c1210951240714150b4480c0621407004e0200d05030f011440c4450102c10b2001c400b180c104145104445004100903e110400c40d84640d8100d50005121540080040c1c0500354100c40c0351f10940001501140c40f61440003c003045078416200c2e00c8646035100c1000301c87c1d0181e5009041854040c01c0042c4d220750150840c001752030340301c0782642c03403c2c03a04c2000640a414170f843c0680c00250303a00c031305004800c105501c490060401e00c1880c109007454100703608a40b24 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 877495629 1250 877494379 877494391
    0x3070302090403050a11070f170706090510030e010204031401050f06131802270a0920030115090c110c2413060807140a2a05030c03120c0c06 62
    0x304c00104038400c00e00c0307001309200c444004000c0d00c440e03541c0c40318454800501801040d40c040000b0000300c504501c00034610b412a009500c0b00700d1914030300750411603042c440e181104140750b00d40d01800c8000100780300800155105004511600103180e840c6400c40c1d000504048162070f091087c0b045550f104484c082c03800b1a40c1d2004181c58071601c0c00e071301004000082c020b4212401c808090300c0c00188070041310182a0500d822907a950b01d01c21668140c4200b0440940818122130240f15119a060742e8044611030143c00811400000521074160144580c40981300c00d40d2044a1002a6809280400031070740e41d40007040040086000100c000303400b07190144a81d0303980c8a55890002c0040261407080004003a10b548055640c100640f621400301c074040000740d44446c001e8445456032094031149207280e9641e02013406071003d9103550380256a4041030b01d026154204001882c1080107080c0410717090041c6880b01c3c90203038081009503020301000c0d01d0480c00d106000050308005040d6501c01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 877496879 1250 877495629 877495637
    0x10302090f04021309110a0f08070e0402360a0506040f12060b09100501091a0a0f020709150e0f040b241f02251406090d1b0503070302090403 62
    0x407000c10500c1c200c5440c00c1d84960000c81c24040201854103050f005050287c05585443c15100300e4100101ca0310002265114080b4142110030840e030f0825601808100d04c503404407207451804da030b132204208440003039400a81c002c0e001280700e40e81030140d107180040c9020381e003542c10300f4180790106880050358000d14090100304036551081c0280b0783c200c80c0011502801c001403604107510740d0340c050a91409440d001c034041d15000500d91303c0900c5140d288a0078404030a06003040d50804032001800f80c003440c030452003521000300310428284640040d04554100c10388040b45060100c2e80341030700041682001400b0201000003007411182d2145e0302c24180482c400010700e500744007503c4101e00054280c0c1024a40010b001c1038000702507082c0b4190101d408907841110b103803448440428003281f0019064442850030031442c6010f074284040590010f04090a0804c4d10012070403c2140000954854400024500d10003580c000c040018082c15006021101c2c151340110344100000341000b8108 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 877498129 1250 877496879 877496887
    0x10504090908070c0605070b10060503040b09070302060412030e0405010302030a0f0303020d021b010e0f1e0c0405090304170a08070308060117040507051206010f0e090703051f0b010302090f0402 85
    0xb00910040b60759241e0f1001c0c003000389548030795004060307402000c001c1707540d4020b0401040c00c04050951510442d08507035522441d550781c03940c41d084416005030510700b1512541c1030103c01aa54000580090400300102c1061b8100b17a04006280480542c1810b00035842e200c01030016031004224000c0f007d4102071440f140400b01e1408400a1040f050401039040c40440c8038640f44011103000514240c0f0715000780b10310203c0340010b0ba1908500c010924460f4408180a0303642000f4110f44800b4040300003e960b942040c0102290543c0c1048a4210071500000740034400c0440c1112000c402e410003900030084445030b9910f540301489040c4002d03040c80f942400240e501d0307214802c82100c0014407501032005017490320707000355a071481e07010306071084e90415046c48801e400055418100d804480400c03983e9071400601103030341480500320600e070b4090040c000c17004ca08100034a1400b0310156207503040070b1040110410488412030070f5141050700402c0310b1039440e900c1e80c0450f42c121600300e400582d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 877499379 1250 877498129 877498133
    0x1504020306070c0c0e0a0906060b121b0c0a0809010207210b22050601090612021e061303050d02100903050919090e1e030301080601090f09020d1101030c09050105040909 74
    0x130b001250b130200d606140440100b060f6003505801140582d07200720001d10032681c560300c507030203180114041c0c0428140b000700004c0400c1d28601c060510440c21540662038005a01c0b4400d0414102d5002614515000907034813005590400c400d0004010100301c1d4400b51030f54040c003403910155260098812030801e0301149802450961107141100c509030020040c9080741b0707100e80c44030000d128076040d0394504040054080b020610b032a0429500170908000c2100000403d00e442a0006216070000c1e0140130340300c010b81d240100e540265000d280144212500c80c40028602400c100c0b01c9218079080c8002280020f4101090310a01034084a41c1c00382514920700c0030541c0c9031690300c041c4900d03040c000c2c83e161034980850500652010807102041c00340c01c0b00561640d03484284150811a4840001008050b1040e8010070a2400c0e1100118210006800003022001e2118007520344050f05952000c0319030301880f84502c103101e00d0600c42440c0340f030580080d102d4000e500c20701e1211629404030b0300c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 877500629 1250 877499379 877499393
    0xc050a06020609011b02250902030c0c12160f031701151b020307050618060a080108300c010f020d1b050c030a031e0c0509031504020306070c 62
    0x1400028059204080c0d039a0002580c07604141d450600ca035203020f00212480001421003e0281800c3d0000c0c0a071203841c11803003400b14924500054002403810b404152801f11303000650144090122154a50f14910009401c0041800070401c01d18410001101103c45524031401041d4000100d912650750794141030710280d10410103024642084000030aa03c0040c0f103004101180540c0c4031717030364038800003d40a084c1d040d01002a41c141e000480030006417400030000d185075a40011070086e62100c42020644603040f104003240800c002034014401d1764810008008080a0759800840707542d00050074980c80c2c0380741a44e51a80c888002460394040030250132036109034610b408115942c6920440210081080c2115407100d0450b4240500500d0301c43c0c01134911442c40d441c090b500d8040d22440641c01016802494030307804a40750601d6490700507511035503c031640c01e44c0fa6941d4452103e000c01d81040080004e0300b0303c01da041f00621015880004680b503005000341043e600c10081814008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 877501879 1250 877500629 877500653
    0x91507030c1212060501020f15070908010c081e1b0a260609060102070e071b120909051303210e0604030e01031a0d0219080a0609110306071b 62
    0x80c1c01210810710301401182d100e01e051000b03800c0740c4000c01a06071100d00498230380100d4800394209038002240014071420004001d5081507842c20302e1801c0643d40e03500f403829107240c1503051010a0700c2d8020001ca58058160b401c19683c0421940c01281c6415003a10003410700d1001310500001000c100b050117140194588021044030708010514074400034011503600f038007102c04500030700406000c03d605500000380c402c00ea80540e1800352507562070882c02c9600441c512200c05a40200e48a61400b1075002480790409410f569107007040c603400c0070514406d50314090301002c40101079040403c08a0b43c415007603031209040c00b012034802c21014541c540070b045007048220a40c00340b88140010150445c1c1000d01c03058003a00d0900c201da149084800071880300d0000302c1d070018080340d8140018900300f9480720144068050010f039103616455914640b41da0700d441110b02c2a6210070500c14800e0003401800101c0f8110001c180d80e207000035004201441112000c0200301c0d58880800c01c01c200003500c8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 877503129 1250 877501879 877501883
    0x706050c1308010501081e07140a09020c101d03090906040603050f1f050411010e0a0911210610142712070302060426010203010b0717091507030c 64
    0x41c0300002e484101d9030703000340800e10418120344216000d40107059051405071008202c03a102030110725242900b4400e01c0300c0708150190340461280c40108a40f41d01c1d1020b49030549a00300101000d07490030802500f15000600301c41c02040300c40d44040c070001000012206050300c01d40d0700301c02a403151808a4042c2959800c01010350180154138505201d0000340f0441c0e042c00106820241c664603450b0004480042d10007500c01c54454810240e0307540901d681e19903503003014044514481e0ba845c554000c56518141c20200d04000058010700c0040030700301e11900b000c494045107140d051400001c1c2034010000d1081d414007004078070307171040601220240c0d182007908210440c0c103035100300a0395181043c82228903114412001c1d420118140000d44003058a078007501d01450507051814414044100c10150344014411040c2c910b180344080c0007a50082c160b1301013060301c4105900e000c0880388615050161100020b0220740340c903076540300d0150906640081d55035078078501800c040b0b036000f90034040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 877504379 1250 877503129 877503157
    0x81c0f201b0106050d141b030a0807081201081f1401090c051c0506010305010e060f09090102131511031306030c11010507090302030f011a0f01030b030f070311090702030706050c 78
    0xb403801808581d150b1b80b440800f05805460521070a0312408122446540c0240e40680c02504610b001034800b03c0140b100708c0c040c0f90307e40d0410b090640d0400012800740c0040d0303000e81010000c61a50303a0901f00d1400304e030082010034040c1400703002c0c16661449051140300000b680f10681d0b1005103026108403031104034610307030704041c0c0b1032820078940161605640c0d03980002d01d080b000151415034113100c94020f41d4000c140342a4614083c0030400705480c080c0207900255401c018202c0101403520307200f001080c5150303540e0444402c0e01e5024215083c808060313442500700f08021250700780205031600c01e0702c00078140003d407001c5540f41141c03000ca02c162000050740c600070030b000f4810f130400341410440e40300f20221041d92060804c51801d03035200402110100e2084410002240362450210401040614000400350030500010f4607108034148121016004507205000744948aa4114400001600d001d2410308001310025507901c52018054260796443e03000c03601c0f841242c012210310340c0000744 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 877505629 1250 877504379 877504399
    0x5150913141e04110f090a02090306150f100504051011120415081b0307050c070b090d0605150402030f0a0e1203040f030e04020a0306090608121204081c0f201b010605 73
    0xc0c1d00294031289c0c000b48a441020b00003803280c08041030784407400001609001070140c026092004585112031701600703005050102103000d0310b83e1492000070100c10303980c1c03006034051102c00b142002c61100380d0182e0440f080009001c007419100c20068032640a02c0c060705950394403103940129604586811b6448980001400407007a80000600000000c00c0709451170740c0c0d503981d224081d61042019142d0444070420740c400100b80103a229942c040070080d1420b561791414800101264021900c4c1d00324022100240003544c04580704105030425860010580c0032004080701c0c00c14080100010141911840c04008151140305031801d000b60281c0159102d0094110140c040d000502544034003528000d40041d10600c0003460643e01403000460503d032889840d451040044010029940845c04011003c1480075000d0f000031714441000000881c00514180c4070207444090880207403c0724822015000046100100c425003200d440100c42901c11503440c950141802d50700c01030703020354040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 877506879 1250 877505629 877505641
    0xc070203150609060109060807110c0904050102030f0a060f090f1503050304150e42043312090b01180c051305150913141e04110f09 58
    0x280c40340e400b4840071200020243d41c2c41c2c0045915031818400c9400240b40d80f4017042d0454001e9803012050384075882540c41061040c000700d452080e00381d800719050b84d80007003000301c0301c00e0501e503aa4101c661480240900e600d072100f01f04000e01c0500031803c00e99510651078200c44a60350151565a0424a08401c0165607041c9107440c0d8009200b81202042d58011040500c0c0c0319950340051030300000c20b20b1038410700742c00a15151100030143c0f9000c61006030f04c000400c1401e41034103103400d01c3c0300c3c9515a07902d09100c8403009072556183c900c451031614150718109003940c0e02860a191005282c180c185a280c0300c00400909071211028103200d81100000c506019184501500800041000d200b080c8415900300d07517030f00c00c10807444000c0000000601441c07518560000600200d0a041810300203c000056001c019035100a0b80156488400a000300003080c001075002d54088554230807004000740c0d03030190a074010001840317103070001500d840b00d64490a110b02588000741c803100701ca141c65 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 877508129 1250 877506879 877506913
    0x180e0105090a12020c0a030809030115090f0c0e3a0605060405090f03030406021e0406030c030f020307091403070803070f0b090309010903031d040e03070312090206030402090c070203 80
    0x2c2c0209541901c1000070341003000740001400310444502400007005140785446100341501b00ba84420303410754035010f0111594010340401c10207015882000030b0079001202d0424203c1c0c6500b4a188103010103c0c1c89903100c0d54801c0f050044c0c00c40074a0090143c502030080d4a440d0440c100d00c840b680450005d230800c01c0c00719039480544100d0080d1401c001c0b6480318000180d6500342c03405206d03200e42c0200300042c0001c41d0b5801800d0f10507414910312030403c3c441600300c015900580c1100c00001d9490645104085d13050144101040401d84110314cd03050040c4002c144840900400c0ac20350300860703441c0103549080004000428084042e6030b1a848149010810084154829240101d00d0b0012491030300000c411900624030584440104a02c0c40e0740540d00d001d0b2007800f098a80c10100a5242640c40f28020690720450410180d581c03818980ba01400d070820075582400d1040c41c1460b400e0058548000f1031390000d070100d038072100303c0d07580e080304072480c0c442c0c40002505400b40d103155806403500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 877509379 1250 877508129 877508143
    0x21003020405040f0905030f070f0c170115080c0f120613120503060310090f0c060f1b021804080d02040306091703060a09231602060106090b04180e010509 68
    0x125004d1205145a6002c2e03000da9a0684003d4425042080703800c1c1d051a0140042c520903105500a50306040261224030315800e141d400301c035140c2494102111010801e205c0e815502e04c04d13004468809003030040b0340e543d07200303413039501d43c0211a094000b0185036240c079510814014600c0c1291028980104050080340c0d8038082203c0d000c2d44d10410410341c500940c1600d05c59a005401040c18104040c10038010300350510095a08000b003854200c0443d03240ca645001601480d04d965000070806203008188100304001d40800103008500d250061391040800410026040d01c0301c000da443d40d0800d001e0f50302c58545500d00347c1e07100160010410083e9045441d0040c02226458100c001e9034010b968103100444203641c0c4048100c00074070001c4a40c1d8030458a03c0384002070b00c199144407000428480d0b80a4440294120070b00080c840600e40c1001400e0140420717107042e01d40d072450001503122501403401030092420669141c1c4034a5121540000b110f040010700034402c9040100d0359946070030f1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 877510629 1250 877509379 877509389
    0xc010915020a030b310605060d3303020d1a07021c0801270f020a0203070606080a26072307050103150501120212010806100e0403050f03060d0210030204 67
    0x410410b15451501d81040340040c0b045c00b10030518207030030407030100740c40c62a20251550006036407544003182c40d17141d03040984a030a1040d0030003d51041c044005100075018a4402540758046288001d141595542074104490341a658202010854a40f000a03c001c4c11041900d091400e001c20010550002c1c092205105090035440090042d06003251035090034091301141603210125003520140007000c142d000d50a8060004824202c0c00041c0305a0380070507001401680003186100920007a44203c000409961000741816050f80c1c2e101c80380903280d901300202480b240c0c0c0145034000c030b8030002c58881c0c662103041110003d20700307016003421010818402c0910703c1601d501181d1540a0300c00c000f001c003181e0a000e00207a2a020046a0701103a04400f445080c1d003d0208025659a10310300c1c078003824440f0040c088034600b00e500305443c0340584d03001e100290303450024000480d4108040350000c080107001a96030799100000320b60951074407a002500144c034140342906065150340030b40705541d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 877511879 1250 877510629 877510631
    0x8010c02101b1e090e31050a0b090718020703030510063e0c030d051c0c05070b1501110a020a0b0318010501030503090f0102210c010915020a03 63
    0xb01d44075480c2c40000800c8040c0700e01080c0715500303809003071400503607116411400d03160002c906921861030501803001665003461505080049034800c070050b880348110000e401c05043e09410003600c5081c0c0e20200d8020250200400704080b511640e0144614809032a0341c600d140d000341d40355584240298420181580020320700350101e26229582440e030070071104281d80d03d03c1e450415208030020141e0824480841c044d01e00c10806044840310804030151803581d0144c141400114140350070000c4881c0600100702b010041d034400d0000d00c10043e000d04038003640014001c00f4030241920140704020317018050400c0d000800c0081ca032441c54144101c4000e0380c03000301e001c41d1106019035075a56110000c0d0b000810030001d04c41056480061036002150b18084a0070b0301a6003c1d0508440007030b042034500fa00300007141c241504050742d200f04002800c0c0b00600028000302c0102440507460492001e2249002485040c801001d402c4618115000804234580c101c0e000d50241c020740c800201c240120f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 877513129 1250 877511879 877511891
    0x3070f0b06100207092408010b041b0c0807020f060706050702071703041809170a091d0a0911040c1d041b0318080f07060b06030c0d0207050708010c0210 67
    0x1d06222035000b195503096001040c445003043c6074040074200a403004500d0b61108008010850324800e8440000c2040400000350b880c481d60911064039590884034484440da0000c0103543ca6001d062a21695081110140c440580d4070001d6450500452010344c0b0603000f140400622010303501c114001e403030030740071207104071b54486a050140407125083c0109410520040084180ca00314143c419a140600002c04040a82e1560b64014051036001100000800e60100540d00082d040001d48440040030049248204050741c4103d40201040900b80c0c480007800e04200c801000d000c0c1c0104003d2040c030103541c40040060815014402407080003030b02415451290515214600181020b102e071006605804441903014201c0c60035845991500c3c900e03100c0228480070094010528203802443c2d9031212810700d001660111505184126401c0090100150300e4008803904005228400346c2c50300b1203400d050b4104101035010724025400c0c25220765160741e001c0740c19450b09089003010000f0f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 877514379 1250 877513129 877513141
    0x60708120105120c0427080a0206010b07020604030210031104080d030605100207152d20062a0a0e130b0d0b1f09020a0e03060c160c030503070f0b 64
    0x242070428071003400f03a005812082410308064000c441c155a0703001450f0000c656480c9816101c1c28040820340d0140303000301780a0a0a581403240b1401441007812541c100304041e00000e00700d02c15440020722880c900d1412b0903181c0d0094101c407445005458000c1d4445650b0249140c8401d44520800c0020349000d07404201890482c1910040c0c0881d68010009ca5040c0041c2031445548103101c40c060240c17541c4030402079040300d03205505c000300142c00d14500d4460a18050101e80440315401d110000481d5030b00e0300c0003800034030b984e880740704410040300302500382542928075554a071418007000c10004140355481e80202d1000c000740d1056400d800c101d2280d40d140ca003110411035005034004150344458003c00c03440d846040e0407207005014561801e180801c01c00c2d9040040c0d100b150b205030085001030044d40c0002007004948400d90150409180410041003180704801030401d0202c08240c1e000c041c23104541c45000a540d1000850703541c3c000500700020f9081c0d12000c100c800350500701c00581 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 877515629 1250 877514379 877514389
    0x605041107150b010c0519140a050a03200f06011d0c0d0906020f0a030905240f040809090f010302040614010e01080402040b18090106091107080a020309060708120105 73
    0x1e801500030210650641c107035070209010305000d00f4002d04100c2c1003d0f80c64085041801254a4014400004800c102851500c14441c1900405100c0e00d0b030011190300300460404107040440c66414504440122200c000c00d20425054690380d015520841d20341420460380010114162161070b1082412030840c01940c0d0000c01c400c40d180382d130650003030100c240d1044150308061003003481004003604000b9000c990000d00e030811802c54001035150b07141030051110520425100400340c50030136000c1c2410050640f01c0580245c4221f40780d640c810001030030702c0b0b6400196507041d18014000030003402d03c00004441c1080c2804264030591800c50001901e003116011031083d1181038542c185510944001550036080c0240182d0b000341e10f41c9a4048140c6d0380c14040150451822075004080c1040c05050b4212500c40d0480d40d0740134a0002d0540420000500342c070381065110b01190b40e07030440100224254000c3c40340391900a0008204c00080106c2003002d40030710150340304203264580e610300400c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 877516879 1250 877515629 877515637
    0xe012f19020a18180b0f010b090607020d0c05030304080d030e0c0a12060b060a05120c0301030b011518060503071b03120906022808070f020c010809010e0105010906050411 75
    0x29403060000a0400012049245000300b090b86000c0000d20000306102c3c50248682c1345808440c0005000c08203d10180020016800b500f5006d0303040e800d000310040458400e11640b440a1b00c01c98851027200c040280f520b0720030024001c00f4054940b6659a05507080da2a0380d59802000420b050005d82c3c0042c0800061100c5000f400070448101d00d450107160841c0c07050000c00958403540c460b81d0b10f128a0701da41c0c005011a04d015030b506a55294000311b00108079401401628900d00c040004001044240d224141034600449601407501014202078541c0b1411004c40303030801e90301990000714075410401551041c0c0b03254491046000800c04a508646500e807001070100c5d40d103080d031000f244050303406600c40601c03030301c40186000035800c0054400150300741d0901c410484016202c0e05640c2c004440340d0050030354204021005007920340a0f4070743d0030041c00f044c100522000080d080c054250040481c01120038001c2065517140c84510f006010f007801002d0059082030364540401408074102c03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 877517985 1106 877516879 877516883
    0xc030f28020a09020a050c07092019080910060f1706010b0a180306090b01030210090e04080d0b13020c07090204060c02010e012f19 58
    0x192030400d04518922030380200d00c008a401611042c005400340c85440e2805070315490b140030f04071520700411010064906c102c450006d03480b449580b110000ca0720800003100105002c0140d45100c1c4121008403007075900000381031000c1ca02c181002d0743c1007018135080d43c0c155030f0f14403000c5098490b80e4000e4110081c070301d0700070440004007030350075045408007002501e8250325000350241a400f404002c0c2d001d00c21381d00c400c40300c1e940d15403680c2c00c0915404841009a6102410102c0500a00b400200d0080704282c602c0d40c0d1040c081c207a000d0072501c0d86612450316540d80c0da24000150440c030003800e00243c071101030130031580d10720f03495203105002583c00680380c5844e00070051500e4050b907c0441d42c18030401007440101d0780840096481a02130800030a000c46c0701c00120750313207102c3d0f040c00c0d61600101540221060000e008480702420b42c20101c41081d101d42030b015101040500c40 = true := by decide +kernel

theorem cover : BRFrame.Cov 877338129 877517985 := by
  have h0 := BRFrame.cov_init 877338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 877338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 877338129 ≤ n) (h2 : n < 877517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
