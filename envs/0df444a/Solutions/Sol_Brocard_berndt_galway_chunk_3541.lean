-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3541
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:57:57.940985+00:00
-- url     : https://prove2.me/submissions/8b951407-566e-43fd-96bc-e14ef1352705

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 636690647 ≤ n < 636870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 636691897 1250 636690647 636690661
    0x903010615020a0201020712080f070c090203181005090606130f0c02030a080109020915250620040806041b030807050c13020702030d050a18030b0105030c01020a0809090c0f03 77
    0xc3d00c0329283c01d0b4003520908000050204640024040c481d400270b04490030841511250f01160380040c4040d81c800120300d9010540d02d0041c030040d8003035680100d403500140c5000380b6660405076034041040c0342e05d29107810000d5141700441c1c4039a00000858880305104180d01c40c0c1d0000781062001c2901051920311056005500000103004420385600c880d00c00e03a989d14001000d0b8450340140a030007524000c2042c000f81101409008400d4040340d000015070807200b0b82090303d4400754026141191101d210319880d100884a2941c2c0d4400c5440e081e24250400441a94a210289c40140082c09003c0d84201c00c02c010048a0081c0da40404030a966422504001b40d03660440c29207076105480c15000e003807403640c3d18400c560010794068064402a01c156106489541085c0c08038428403242d00d014940b0211000d2240010718401c81c802189541007500341071400a49540250542d403006440002094024065624251040341c0200903603544500d0503510303000300104c07108003c0002c0144042 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 636693147 1250 636691897 636691903
    0x905010b2a0c150904050a060f0501050a02060f0a0b030a0302070f09050115080a0b1309060e03030f0f070e150315061602010e0d02120a05160515090301061502 70
    0xa007641c241c89444102030742003400c001114000405042640b015020140a0400d070f101c0054801c1c1c00c40d00c441c10110309002140a03075004440000256036582c900740a021451141d00001d40401e20b0502c0c1802800703171b400ba5803046d015021840300d03002c0e0000140604103d0700f00da100c04070090305444a042c41032602075510002e038001c042c5041d400713480c04104603003280702d154121000b90841404c880031540081d01c5804025080302006034483c880c0020980300c01240b4441e031400c481d000240b161607401c5c844101c0c1c00c0010044d00642080080c000104004030305580c0041c0e0700c0c042284941c85500d0166542c0240401c0c1a030030403540c0b0300440a114265024600c107103100301c1e2140c40f1030701d21300c10000e0034801c002d0b0b40d001408103840c984015505c034950500a006019101c1c8840d2055900022480040400760150561120441104105090043e035100140d00c2c1400e0500508040c0090003a1031107560740b021082c800b007284049590250020001001e0403c0000c08100c14480300a403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 636694397 1250 636693147 636693157
    0x40614031939081b04020a021527030f0418060801050c0403110108040305030106030b0609040e01090c0f0302090703230907140102060c03010611030403240b03060f0412090905010b 79
    0x1030803610080001603c0b80c0c0c04680d000a0480e1400b074403840ea128a000c0200940004800504520401c20400c40d000281c6291501410904154010400c0310705500c0400d04040b00050441c0e8006100541031854240160b806a915514503030110107540131090b4000e1280340d00181180d0b0800052100464411000b0410780b80138141c561034020101c1c0041d2604e00c01a200140011801c0004200703507403003a400040b410360000d124616028a26000038140d4035000c0d0001c0c003d96540003943c01f0854402e8528000b0b020402d1a421001e10b1900054107015005050b0301c18551500c0780d00245c41c881c4241d105038111a00452242170805402142d44d03140140507015001d01445042445980001042c6200781800080c0920396070910b04202c3c0c5541d150003041007180b106000c0400051040648060031901c4035082034000d800768014201a81e6405032018003e802c00824400c90000380c90351281d10a8008400d8800400100c108481400c1d0a80c8424a45803a24001150003000c00e00144 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 636695647 1250 636694397 636694493
    0xf0803040b06010309111309050a0507060206010f06020a080706020d1409120702031b01050705030304240b01020c1e060a11010c11210706020c0a020406140319 70
    0x60078565426005400720b4100b220081d00d0455130500718081850441c8507030700c2c54603140030041049569503032140e10300b403e040401c0b1400d80040d01c0600800c0c1c6d040040e24014807840300d02103005031130600080e46800c002d42c0058440b5500041c504148140390b01100c1c028011190100700d00d9118011480d031252040e030300048180500f8122062001d803000a8030b00c40d58008000c1c2040390203980454080205140a19040c40024000030300420780038400b075440f4a0003146120210200380030310b490300d142880d90300c00b940b030b29011001c0c80599001800c00a1802e041ea8040c0e448820380d0b50f4404032001d031058460340300200003880c21071a0350046400d603807445007070024800103042030000c1d03034103030300c151940d121950080b09481d4034110049212144100d800f121285000b119031510070503070740046c0105103294051900c4008505091050300c1c001e204044001d0301703d03003d040000761038800d42e14200c510740c00b0060944040c042420001600880302d0042c0801c46418038410000c410340300405070b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 636696897 1250 636695647 636695663
    0x30f0e09072006270f030f071109010614030a0b100f020c0a05030c130b0406031a090a080301090c050c0a05060618090c0108191406150c0706030e0a0f080304 69
    0x49080342c00004685000d842c5030214116070030107186181512411142ca050483d100f0911a00c0300d03120140024102c03c06030308550f96886049040942d048040f800e0701e0350040780c25800400c40140d1000b41010700303100440c0c4065880c0c540001107005000b00014083d4080600b07000721110075007052211980e0507140e020740e1400c1d1090401c004a600142c856241c258000d890403080d2494a61000115041c1e418000542c4d520308101240844405030800c42c1c0001d00300c03140004000802e02800d40c41081035000f0486a02c46a481c208980010701c10480b1060b00c40c2d04502415000f04141c0300340d110200c1c2114040a140c0c280241d8941c01501d038180101041c005200309107054a08007403160075104010490085400c00444001c0c0e401059003071113040d18940d8001e4030200303004001d0039036035400400325542004d10420034a40809007903204803031002c00948043c0c0d040441d02c1c03022103905050000f00590f644080c0e5092802400c0c0c024611007203410300302c1c200714400c0041c41c0100c0c096801 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 636698147 1250 636696897 636696947
    0x1f020706050304152003042906010c020f06070f0503040509061921140106210b22140102030709050109080c0f030313080c030105060108060607030f0e0907 68
    0x1d031594481550302400060f4200c01d0810042076582060303070141c00301d200341c0c5c0625030f003d0300410031038109660803107104035888901542112000c0e801e80c2d18200b4004114114203010002030400ca00c2070a000380039640a51702103000e036844000b680d03030041e0800e403620301c04410f600c0d02544980c4103015491207181c886020400c103003003900e0702d0040300090121424201c0d00f810540107070305c02c41c8992106003000c4030f000703c1c0005148480a440d00f550b02c0f000410200d042c80c20388800c440329185211154074010074850040341900f0031041c0c20601c050325100c070340490b00070000b1f0910072555000e01214070940c1454100e131015401944210095501c0b413950300c2e1588011a04040329105e42d010590003018a2045480c12105a28010a00600316490702c420a02882407040155000c0e00080c3c011001042007401c0038060981d1190f000d10784406140340100014039640610080a0200001403a031107210038000c400b045030000d00280304079a1442c02d801c00801d80b0101d690368400300800701103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 636699397 1250 636698147 636698159
    0x90d020d1403060303040b0406051e19030506061b0f150705030a020a170901021809090304121e0c0521030a180b030408130f060e09040201030b1f0207 66
    0x203205101019280d0703075601c1005a5110001954001529181d810b000411001808031440b40041000740304540700c094841c2141d0b01c2c11038558000052417240b0401c10400240c111201c1106252020008d08000500c5e13103981c004034001c0c5c011240144010300b10440300c00100c07040000c001d0b0600178000115012800500c840c0100b01006840810101d9010b00c0415503150b9980c000d442c604080c0c0c0303402070b0001440700c41100c001d80c0c251000780c203e940c0045c00c90500c140306070511071150401d81e640400307420540f80e880d540b0712032031040b1a1801e4000403d482040007400031000c03201c0c6c030010b001a68030858100ba0400c42228491a0b100780d010014040d01c08405140c14840c0070142005507041c054040e4041d99030341c1d9411291522129031100c0800e034031006101850241e030107042801e440c0c0350307482e4800500d068183c000320b10b510350070042000442e030701c105a00c81c201000d48825529455520045e80500a4100115400541d038116000f030804030540061907a1016400c03916811743d148 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 636700647 1250 636699397 636699403
    0x90204170c0105120c09100905030f0a08190c0503030f0a0c020f070b0901050d060906060e060301080d0516020607060509011503020a030206031008030c1c1b021207080d0305090d02 79
    0x461840c0820030074420132902c86140090660320402115485103801c48000c0010188085200b00d10f000c95041c1109218500742009142c0305501188001d00c00c0e05031a803140807041c0034800102c6406900d400c00c8408591280c02905038066106040700d443e81000b0007003000d008401c5940540c880d1500518020041c030000e02220300c4011100034101e014140312600300c159000c4080300d4107100003040031140805407031003090001d0103520030000c2c0403801e0840081a030791100c00414410301c0d0501c014000480049180f40480a06003000c4e565480e10a001c2810000289006544544080340010903c83c16800c03091007849480c1c02000040942d06102c0c03034072040ca001c06500301305014020320050030b0400042d81c00c40798100c84121465030300c489440ca154043e00303490308141c002c261035200d60202d000071144010315034107205e030042c10240c0001c0401c00024a0280c410940f01c540100340c80424880c031005000c402041d2604440760f400d010b03001c1e03c0140da01d046148a0003002000041c404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 636701897 1250 636700647 636700663
    0x70b0906060a05060d0f021c062c130515190501080601060c0201030e03070b090a0b0714030a09020a0b0307031a0d022101140429041e060207080409020417 68
    0x40c030711405c0c00c54040e0540010301c018a5240100d550810154076501d40c04d19002590b02c1a61501040d8141400e0410f0b6003000c0c0309480d21100d1051500f00d80c15030300041c401540c4441800340003c08102103003445c5150004081c103001d440b520160901410038100303880b590340d01c0302c003100030b001c5039a8918585550307100c240708100004002e2100350b001507100390030841d00d1030501c030200c82c00c0022940301d21010500a982c510844d0340124014000c103c02c0c090390f10b0f40514541032911345a900050841c01d148402010000406d07911450300c000c40d9200f0b03203880e028024190f040e0380c0f41c1c03603d1080500100f4200340456007480446d120380c40307286045c2d5451140c40b580500043d01d00c00111500c840948416200c02d03803e552548413090702d1a41d2689a1071089000303e80e8520903055211440415810340d041e07070b2080d05d404000700008a9900b0307a0060728a0101048000c06c5103880c00c3c0000203000c2e401c801441120f0024001600485980240041c4d900e5880b04024088160404640d60307040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 636703147 1250 636701897 636701899
    0x1020703150c0c0210050903060a02043b090d020709020c0703020405060a08060703050402130c0c03080a0b120703060b0a0f050405040204090f12110703080f090301090503070b0906060a05 82
    0x101c480c0c08960500542000c0001e15150500d0412428150300085001e50f1541170301c0c1c0020783c0441c8a071001d1504002d0107030000c114180c2103241504100c0064103038101410300c0d681902c20305c14081c1c410071200d5000c5100707000b50103001c5840d0602d40c0d421600c0b210040304440052090764408034060105100b1100ea001a07000104105480d507428440a400010a10380e4444403000000608001c2800760130b105800d0f56500045034a4540b04114206402840c07400c90280741041400215401400254600c0d030941003000495448500b8440605582003089030000b80350081c000b0205400511401a64456041408028109010300a0280642c4507601c241c3c03030740702e0003040305041960020360800e0014001103100640d54440b07081c441400c083c00c840b00340380001c8008920303901520341d14000c102e40c1c004d003a1503459900d921649000e80b5030300d0071042100250550141c0d074254002d944580e03000702500e07250b20513400e0102c10a8800c4035030944030302818000414519003c1d10650642d04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 636704397 1250 636703147 636703163
    0xd0e0109081e010e0d12150521011506090302100305090a1415150301150b0703080a180507030605010f03030921080c0d0e1905010f1202040b03010602060601020703 72
    0x50456940c0e80b120b03008100c0c00c11035550319026965500810b002010403055035440d0414948010080c010444011600c83c0c0c01c0c101d1004400d0060341e13180d110b481307050541103a8070078518001c1802c0500500351880e606128031040000002c09941140011089a0084404c2d080101514500f54190303a41220140310b2a005104a8400915103594148441c4101001c449401c200012900544c4030143c07900b0481098101128100d07280901a03070380540741c0030000c40d503401e242c07485002060041000080a00c001c01001074501c008661054060402e110083c0014540500300207850b00c00c00e01040c1c03561070a020001c51170000194894084a074941c2d02c07080041d140c141103180403440c50b10039070100306949101c20003182d248005008106440b10243c0005481080f01600c00254040307102c2c00f81d520030b041e1112800010315443c04491081c203100130315024156044400c20309040814240318408035002c618158101c001d10b040c0c48a6408480142c5c0710070300117a958004a100046c4005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 636705647 1250 636704397 636704413
    0x308042103143709200f04090302060604020d0917030712060f06080414070f06020114040807140a062417060c0d0209030708160b04030c06080c1603020d0e010908 71
    0x142c002c2c11499031091034940013034802c41991790030a02074034000c860052908003c110881c5ca15000008040360101140d08000c061a50340d0041e4480000a2409119950200d003d0280360815001040c100e98404090a0380008401a001603600700f07449c210005003005240c8500d00481c1d214040a4403a20500e090380c883c900b510443e003d65009004882800d21240ea0f08054081080410054410100241c1001e41801030090031034401261003c01080e5010511021491200485541a03040081c11041a010009081c90007040f0900100194a0041c42000c01c40007024038080101c103603004403800c40d64030b4842c2e60f240d0040301090040354002d407020442d80c54030720000b806c0700041c044002d070810005000080c1411281c1c0e100e59159004001000020404508544080c0031b244c50014140741c19900c1d0048043d1544c080d103400c2c08905008145003003c2902511241018224080000942464004d48490004403d00041140081c00c0d02c607035030142101e0010396000d0802002ca007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 636706897 1250 636705647 636705721
    0x150720010501141e0409080405120a0204110f0301030f030c0210030b1503190902150705010504120f300e011b141218030f040f0609030b04030804210314 67
    0x201b5648004513902c000c01c110000703560b100c0e2140611900d0380030000d0702001d0250b0042c881500d02c40717003803100384600802101c6580140c08007a2819a84c1001076002244464642550784494448003e03502c8030720540315100300380c2d040d00f004c149410182c41601103d034545102e16141d0001360342030b4004440340480c00c80c0a02d1310380d0080b900f19000070000030f08007012031064040350707004281c00d80f4507035150020801840b44c5070301503900251035480d003c07082280c0e01d14002c02e02203031561b0080c030043e41d0080e0260900d2200d000e000800c200721000300040810022860300915424a480c4007803000d072101462005d005002500002c20741e60a41850000c0c402e01e14155004010802142c20040144a04450710108082c081c00340c549400140c0e03c40c103016401580c03403241d501c11410080c5400301030001403144031010b50042c0d81410700c41c8050f111490a46040700041303c401c0301519010380f606290542c950001280210078018211058880da502010184c80d01a4105113101c1d92250300c60807 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 636708147 1250 636706897 636706901
    0x207060f0c0f0b090313051f0f09092a210b01020a0b040c0501090b0a411c06140d080c060709060917150720010501141e04 54
    0x40610030b00d004498158156500c0148400984401000c0d5002040402c9038110422003030010380000c82e8601340000d404440c114420388a614500200301034042940c4440d40101a00e1010b040804014083c03100303030502080c85d0340f9401c4266541b242d541000750307602e280107900240c4113160012102000541d0b03070700b00102600200c01c8a50444c480c1c0294400486c041c54078942c00381c0d104201014155141070001001c800068101c0c480056041080b81e841507000203107071505543c040241c29038080011000000f8200e240444c0761950880e1440c45d8409d0303104001420090403400d007000303404600a107060101c0d1100d01903113604030b025402c00061761401506d15124940316090706c40c40c2c240c01c0343c0010304101080e5015004210300c42014003416800480281c0a03001d0b80d00740b09000b58800185c0c6950b410f001500805124460700803d00305845080b400529550a1001c508056004001c950007400300f441100c406105c01380500003945016007001c85498501700c2c0741070501c5461410400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 636709397 1250 636708147 636708167
    0xc04020a020705030a0b0a0501080f032d0d090c08190b061912061407080601140d02040305070e09010b0607110a030c03050d031515050f0c030c07060f0207060f 70
    0xe601c5020b50000303030341d901049208240c42c4551554a89414803442010503908180c00c82245600440340e40000d00b1000000c0c1c0f03e6451410181e45503082450b075030400740007041c2d800c451404000281d20810141c160300032121091140f00d0032202195940003954840f9015100b00d6503e0380e12010f0b00000c205840d84c65034100b50001c003010313500e820710900c039103180e88243d00014103109401d6410003800020321071440000301e002051003007071038550707001000010002c081905000303141011301c162180950075100c400c592050219075513516410490340c2ca28031381c400e2001c0c808c01c1c0c000082c0c0410781800396452680c0050541d90828410741c0c1c50a002030542c56006801c100320003000804180bd44100303600a501680140040c41d4035000000e040d078594015100c3c03e0801302108003c44100d011070450300f40c1c500d24080c0d441e014014034918030f6100da800c9401103880085040303110a640405c03448101c4040d520b03000c01140c41d8110503030700c0303c03030300e200303640100c2e20000040084c64001c0740d07611 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 636710647 1250 636709397 636709417
    0x6030f0702151006032004030302160905060d060515030f07140303280c120e1009050604060e040207020a150f02120d11070f08041d01081e030c0109081c0e0c0402 71
    0xc141c2d40900d600c03011b1281c000ea030045d00140d211242c0d14000c0309504540001821705400103008524000300490035400c80d42400420b00c5580303c00040c00101700c40613545100b0340080c1a85c03584022000240d59521860003007006c96020b02032145081e140010844190809480400c18942111502c00321140f8401d0310240034009858809030000354411481800e240c03e40d25031301c0d4030351900c00501c0043c030042040307107081c4a100c040034270003552002c0543e0f085441030f00c0c00c0040c0341c2c25640864040c0c058100001d412038403140c804103855403102c0c0b03032500141c0c00b940ca0003600000014201d03502c2c002150410440d00c020012940c516031642c0102e0890303100880140d1404071160741b0b8107008800280144e07211807001c90103008264016940b4100e40703c0c00700788041a54149049541c6940c0142c1c15040140290200d21030802001d0083c1c4403090380241c001c00c0901c07018101040359900079414445000d06900715586200b2030381c41000a003144510040004c50750000c103000007503024001003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 636711897 1250 636710647 636710681
    0x110d0605060c511503103303060c08040809040b06091f02060c04061b140601290324190f03021e0d080d0b06030f070215100603 56
    0xf44640824454200015080314800280e401402d82c003440400b034024200b6501d5112940900e00345582c0020800414500303070300300081c0e0003040c0140d9505031701415011f051400c1207046460507115050f1000003101d0141d0014440c40312080300032a0203ca046400405d0480248002c0d012030500c0e03030200d031850301c0c00ba282038508413045c000611603801280521082e0440c10401010312581448859001410700c0c030090f08103403c0c158003424404072002d001c204940c200d11038206028002100303060a0b024142501c0c529612500305081c00300208050080701c072200740000049100441c2141c0c8541c0e14244880c40c05c0f8211012460300040c1240881d612040c18031213501002c9407080280300400c42021a032500c54030714414040c20202a090000540078855001b40c2c003a101d0110401415500c902190782d40d81c09200848024001888241d80102021040101070300000c00b05501580140d02100c005a00040504c40c0c0c1242c00c4801580c104c4900700b0800695000b42c0220454048030510 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 636713147 1250 636711897 636711973
    0x80118020d110d150e0127060f06090806070801030b0f04210c05060108013c05131407060e01120f05040b0f100803090d080c01110d0605060c 62
    0x80041604545114144503039213200c0c0502c940b50142c1c20100424408461150541c9040d40b0307184001b82050020030350b0800100b5030b502c0c4018591015020b0032009240c506541e4441c0c0c00103140580500807501184030b58404100040c0c0a560307024120b943c810a4040701c0e0f45c0b41100c807011700c040540b0450f011a03050344d8010540c2540002d0600824003642c42c013450031190309015252110680c44154035914005c02d0340d010b00c01a41c3c0c0104441642030380300400c03c01031a038030010ba50b0303a0020b44200600c3d01092111095808100d424018003d04c43d078028805000e07055a1581c4c0ca512505001c91651101c1a4195000700c04072001c004091400041814100e03071120107640044600322100590502049500a0b40c080110780110b040d91000c50001c0c20003150b1542d034420300b66500d11420400403120100040c880031074100d00c191100a00445407410b52004513500a1450702e287c16017881404035060905030140ea081c504408000d00694201d01d0401444032140c0303405102074841c21038 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 636714397 1250 636713147 636713171
    0x5060703051204080307030b010c020a06110a06060e1506120f15060c01090308070206090a020607020a03230c030c2209020901060e090109060b030601030e01150305011b080118020d 79
    0x2d141c901c80c074055014540c0e02d14000400504562010325000d0520019818550158942190000c02e0755203d00341034000c08003000c201850510348480081403e0b051950200d005103901c03400601604e9014940001c131920030041290368002e401d004c021004800c0c002422a891080c4010f0304910b1030041d2445241c2d202c0d01040c906d0340900900b040c0760391101c14020800d64000c01c81d560000d56403014009a0910744080c0d42c8490300bc0740040c0c403404000c0780728001e6544003c6214000c40c0d1005080c0c0a2031410ba40300b418061201111079024065040b0208490501003101c01c0c0040c0010041d81c5480540328401d48029111603041a800c3d60340d00c0120010385422604a01800b12504c4140440c04050204415400f0581080461134204103041068030f01c0c41041e250003200c02d003004908101782c000503032b0042091100c0f11100f404084000018004194001d500da0325150710108915191160705440e03000013332107181140d41881e110303800c44903c2c80d0301808001400340801314014540c44 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 636715647 1250 636714397 636714427
    0x6041106040902161502040f09020901030209040c020105070206012418030f0b04062d0209010c0c15020f010b15070302010608160509090109020f210d091d010f0506070305 75
    0x210034480a1a6144da070140402d00e02ca10401d54141c51056140c9402c1c0400e0115402482c0304000500ba0040741d00042c1e607010760181d65481201510410812400283c024040c04060740c0b035401501a8000200d0440b054080840380150700500c4030001c80000c1c2422034050114104101e0060707000e4401100007402d8403040d500c0107005117100410390505091100407200c1400f60400e4041c10880040302012003402c1071103c03005015001a1507181040040c4c07259a0100d500500c510200e800201d540d104004188002440325821101681e04284c01d4038201ea44c401011903001d01250b4600a9181020004007009482440081600c0b503032480034619042c07403000c812203170a070000d9040c040c505240003c039520840704c000070f011019440d0049140a040d50324085e00a05600c7c8102e80c007400e02030740a22240d2608030883c5d1540310b101c0e000404c0300015000310841002c614690f64041090400303a9410707a484410f907988464a04810041164000741c0101c06001c1c00b4804490300340b03c51 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 636716897 1250 636715647 636715657
    0xc070b061e2b06020306190e1501050c0601060809010c0507020a0b0906040b18100e09040209060a030206030f07110f030f07060f0e0a060605010212190309050a03090807140306041106040902 83
    0x210343c0980c603401c11b001008440820071000400c0800851002c0004450a00425030880e82680d07024510212610040311030b442140e03d4069039110300030001900542c015041c0b80715501c0c10000f040000780a5908403000e2043d00c0d00030703601880020050015502000044c10050002400d10b40342c1030b82c032200c000c070a8026441411742c01c9403004000d89103041010b000ca20502c001d103456407c3c161068000b510840380900064055402c010005071503444a0a010f406550000c2c00d080d120718041103d000c004a00b1100c02c070005a0384991226168000a010748841d942c800141d82010345450300c5000541228806541c0e468a41015a02c149e2841c4140d080002c4150090f21040c22039080c801d09031407690b4451170455109000048800c00d064069403100340041c44402c650446201c001c401512486d00041e01a0048006900030190031040d8801210720030015554210b0355401783ca408030700090f1420343c00d600a00002400140450300000500e20010083ca041a0b11101c1c200304036001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 636718147 1250 636716897 636716903
    0x908270a12030207050405010308180f030a050c1903050607030504150c1205010b13091a060a0804120507031707020f0d03021b0111041208040e0c070b061e2b 69
    0x108a03107140c180341d41130110701e01420059800340000e5255640b00b92480c0b2400c5808445100c001c0d0a1224503520300038480f084100c000c007110792405542c10b10b5501c501e1a150010b100f84690078280d0a07840b0a824140122500600548084d60f00d41320154041d100c02482141c800c00c052181070403408552103407a5030780c43c007039079505000441c0410030b904071b0740181c10000020304203101d4a541c1d401402c101c20b0640d00107010100d0880d501c1400440144482c621165108001080b40c8170758550004845104a000742d100b100c0010f851502581c40d407107524000790029480d6041500105c0d8038507941c0350400d5071032040300c0b01c2c103070480442ca05100e075000c16400045d800044000004c4100d10100e01380c80085c0d0002c109038000d11035008000d200354031480c05d40c0c03107100c8540005d010358582501e008003074451004101740341c0390f0318050f0141e1003400c0442d0003100000c0856003500b840640703c0b024044212003401200e222808000001d4a50b483c400034a44880603802c41c030b11401d80740080c0080c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 636719397 1250 636718147 636718169
    0x130b0703110d02012009060d020f1c05060312090d060e031b071401111c0203040303350604090f0804030302060915010303080a0204051903020a090908270a 68
    0x71007480c4941800103a10502045a0422a50a154601041e00c1541c06200e050740559502a0b40c00460f0b000d02030035501d00c02c214408034064140341e400704001d1001085e0340e1140c0703001c02d281c2041c4804a41c0c0680d4119096801502090104036148005240f02c40c4010250b10710100c4590b548002c0e1f070b541000c00704090300041070084807101c00c24100c3c1000c0c0d1407040548105410048100c10300b860310303900c07541000b00042c0c9549821105200500104540b500c084200d203807040c501039902d40c00b0748001c400140d0f4000552100c40400908400b69a003110382000c40c074450144004581320700903090f15030080c0d503030345080e0000c0c508400500701c440c403440d5140d40b900d1460a0190401e90001d00e04502c503040404006080d403000000d060540303074541044001c644a0500700ea0003800cc80d040b10741c01402d1009040340c07800e40b00c400c40e8201c0b44202d460345220768a0b185e100042d02c11520006141365814400f0303030b00201d0b0190310350841c80e000f90700c544d4100701210005050f071f41d55640700400c0c0c00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 636720647 1250 636719397 636719417
    0xf09040606140d03051c0212070c03120e0d1d0a030c0806010501050304020312180d03120f18241e060902030601090311120714031006060503010b130b0703 68
    0x1142118803422040b508031005460b0503240d1318041c20f85c2c4180001510514003580d442c0c043c141a99040c0c4841da00d10217041001841c1140d0050500840b01e081640810602c4503c2c03130200c8610701884071100300d4440901400d545ca0001a100f0381403203c1c0e5148030304035070705201d40680c8980b64801d00550080500901651034804824200101a0400782c10010108104805a2030005e206407006440040b802da4407070704048841301c14040342c0401748d88060341182080074140d201401c1c00351481204020010410205031030001c0b100040c200f0700d1440c48151181c8040340c420000b501461040d04489818003040c00c890404a90400310810260b22245501e420000d80e40d1140038085c000c0352501718918102280040c010421a1100820315048058040380d9511144079041050491004a0303002035102e804900d03500d21074011150080c0b013410a45528480180120340c02c4400b151595071450f400c02140002c1a0310641d040703000510003110002d007441505005110341802540c07003140710 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 636721897 1250 636720647 636720659
    0x402090a1e030803091e0a2d0807030e01030b010e1f11030307090608090604030801050402071a04140c03030f0d0c05071401020711121209010219060b28050603060f09040606 76
    0x6c0603215141c00381d9100701c5120340003c410448c100c040d4600601083c031440380d00c405420500c0f030034480c001c00440b0003180c0c000030160040a514050442603d061000c00c031100300468140301300341d00782544840d454056a400003111314600e110310a051600e01e6400d181980f80b50b00d154002d4507064009a25500304218090340700d6051a0014690f4000d802c40d81810349000f40b803410180074052142e54002010310400c0001545207040803004805880986060b00300080c85101d6000348407440c1c00b6612030035206d840d000c400c40f228003544c50706940c20000e9442c07559008003075040009052203030404c817010205003880080559810058005079850400d8603109003600d00e00f80789207000e03800310407420301e1100001c24120071070302c103411a2035240d02d4500d0040349880c4441116110f0605001404014085a03400083d40035206440b13000303a0500104151880012034030701305550185d180d00c180414076008004541002d401494000e592103031130300040900340b0a0b01c0032a0f0070f50b51841d0400c01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 636723147 1250 636721897 636721933
    0xa20040807080d2304120b09010e0109050613030e09010312120507020a03030f0b060d0f1b020607080c0417060601090602240408120c0d0b0402090a1e03080309 70
    0xd044000d000d0f1a0440b00e8003409030180710011106100e51030740741101c0450315504000c0d2801000c28a144040c03640d1141080b2901100a40f282c032019420b2504038620101d05000c0c6500b0654010000d001d640c0d501c0c1074030403050b10b000004804100a4400726100e0382d881d0b00c0854060750082c07140300709104245001a200010440485072104d040c501080365450300441d0030101c10f50103060205175240060300140041950381c9507182e2040000c940c83e1015840b86d070100c6845d0140d5141008452542090b01e1200c002e424002d2006a2020002580c05071040c6540ca401c036222901e22418a13031a032a00e080d101c04c11440504c0b1a0b403040c0f04008042d80c0c4074210400401143c00070306078200c0d54000240a4028000000b023240040300c0100f010040c0e04021203104424000d2211101d08100c00c90780000d80c0241020603d040c2443d40303600180c0340c98421030340054401000e00c15407503c2d010b201000764880040481c1c104c02030020000107d100d94004600c6109428050b04054102c0220101 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 636724397 1250 636723147 636723149
    0x806010309030e01050c071e030303051e273307140c07050301230a0501080705010305060607050115080723210109030e0109050d020307030b0a20040807 67
    0x410581001d0340d640c04a030708100602d0840000380b800d40d6958a60808503440d040c4540e000010300e050341c001101403d81500d80c40700944e480f95500f0302050b2030b061450108611110358000003001c0c40800b190f0325013102c400d426010a628113500c82000c070b01005090030007211003d0750009400c1205074580b4083e400f14104135801041c40c62041e1401c003000028806510500110b9040f0302c0040c20828825042001b4001014014002d02c0309403044500f1565120814070050a0900043d02280305030800d0f000312810f8524000007480d0543ca480b0046001d810041e2645130170800801003900400c40070b014440d444042034140040d0300c2d2500000f18544140d9034400c8800e05001d01403d50030032003016001520002c2102c002016640203103140150801803c107100c410340c80c2402407810103402c15101ca8401c00c003601d0700400c082d5220188868103003580802941174004450510005100c1034040d80c00c10030341500025144203451000f44042580500d200a040b8003180030003869400b040010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 636725647 1250 636724397 636724399
    0x605150f09160f2a14030a050a0503100b0706090b0928020111070602060601030b100e1e04110403051002040f030807050a15091a0106090314030c06160806 68
    0x1600e441c00b0700100b40241d00c50a001c81c100103614a442c41100d1203440040122000d94a4801030402c0c0c4d002c10340c00b8200c0440c2e046800b10702100c080728a4680210030303568401026224280341c81000c440444881d400200300b007000c40307224200842d04c0c180c030703801074207050744a9030000400e405581007a03150014002e01d0034000d5800a640003480310000c06401040d2070b40e43c40843c0a03241a88016944810015401480d03442007400006c0c02c2c65001620354010314080c4c0701040046002002d0003d08800b100c1880003061440c0404d1245042009206d00e010341c4500502e030b07440316401d000405840c1d0310454104070400c0884d040c014460244130080d00c0c1c14010a04510303251a00c050140c0c480313041d100147c011003002c02c120041c0482401000e0040d80d00c80328109001016880e0b240c0100011002501d004000081988910042c0050241611040c5c1c0340e000302d0b036245607520780c0e0460355601c1d01c0b02ca03800700b03020b034038814081040321034000c008e480c1c022079040102da04005c00b1414020011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 636726897 1250 636725647 636725659
    0x1b1905150603071404090213090b01031202061e180f031e09030c060309100501090507120c020714030106030c26150112031e02071805060906010302160605150f 70
    0x4001c80c4030821044c460010b030950b03001c01d05440c140005940d11031400c010f4049103060034003090400c44200c884506980c410810008071110858003243d9601d42143c00182414010310000f18002c0110703030b4540e021f141003404500380c1c2d41c520b004070f0600c007003014641c60b10b52001c0b43c0002c010a1402c400440e88900c542c41d941041c0350071000031f80d40c080c1414040e0240b50000041607010009206500301c00e54002001c3c05556919a003001c02010200c40c4000018818a4000d840101138007a849203400380b98011b000c40d0381484c2080c854850869059076040d03680f0000000020024a00c04d402400a5008000f0280c0d403c0460300d4080410118280d46030030088001c0280c4408448050550700c50074032508503001a4902600d00300041140c0c02340455044003a0465240c0c00070b0500103603500c00c020f4444801030320841c8070550742c003614071a80c0000214001a201d520030380c00781484180e6a1142818010551510800c0b40c105440c9045d41e0340c0150742035040e0341800241000020000e40d41 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 636728147 1250 636726897 636726899
    0x7030b030f0d0f090306060305060105150c0607031e05190b150f0f041d060f0a23010216060504051c03081522020c060a0506061b190515060307 63
    0x809442d2542c1100d4601405038107105110242d03c125190409558000f00030480f43d13031282442036960301d007442420710a06c0c0e03807121109015491010744d8500d00b0030b14010015074403880d0003500507007210125100b03090042d0480c007607040054050a030050304101044230340c400060f0039441c16511f011380201d014180d50440d00e00c1d410344a504035644000c510740030a40790440c000b90500d10303128591104420100f2030180d040300f0b907006c0e6405c50041343c0c01c481c44140c10352240c003440a80d00b900c2c070a0000c82202c0b805040c03600440d0381084c0c0051a01441942e86541900d06482840d080a4101100162003c0340500050618109a02c840b81e040000e001d00e892142c1c1d00148103000c01400001d0501c1174a203d50071030388449140480385500780c0701500300c1c81116203a44009421510a1612510511003c14105422881800e00407007018008501d0300744030f585003006c94400c1d0491803106e845983c05d00f014030780400d811002582d1046015010700c1010703010001d40c480000c0d10041c400e400c0280 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 636729397 1250 636728147 636728173
    0x5070c0b12040308070207180b031e0709050c0c151009110315010e04020a0509041b0903080c0309030a0308040219270b0406030c1a07020d0f0203012307030b03 70
    0x340750750340b19034189400e029681c0d85010481c1001d061303912281c2070804121041c1500b029541019443c02c10650455103410a21880e05581094aa096105903000350100380000b0049401041d800305d01d45203460304d44881038046925201841201245810341c40050206605170000b0742070090280380d40c00d02020344009150f0403144406000080b11740800403100300c0300d90003404030051106c4024401c640b20a40c02e10042c08c2940641499445545000c3c041e65420360561000090542c3c580d039a02c400c035045584c0c460403a4042170540308240b0040c080012260703010001c00803160300c265100345030381c145407044c0150740040c1e402155a09519101c00c0c40609100108020290100140101c0180c81c24450030300800741c01090700d40107401d0080c08414010a0f050400c101d0304141040d2004080a0080e81b42d14061854000d5011a40d545040b0106030300c49a4a08460700003400000d4400c0c01c0c070901d0258400d0014116200d00d03940041040c1d06c1c5d090320494850540c19005440d24000c610 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 636730647 1250 636729397 636729427
    0x507111c2601080c0310060807142404151706060a171510050a080703050a11070605060a0603060b09040f0e060109020403170a05030f04080f0a05070c0b 67
    0x155500c0c108010608500900d01d1603210910030300000000340100ca5031141d50710303621140e0780301200d030103031040e044c2c00c01a000c0103120740000c482d08080a041e0303c5003044014001010f00201c0380780c0c821078290301c803112211814a03054041000d42c0301256a1898201150340041644d00c0240c00d11030300002001e00305001c0101d06500c044101e5400b69200328020090b502403801c02d405981981482c4100006001d805110b4040c042d07013102c200d031a903180e8102c121501c0c440c8100400c00204080007050115000e50000f82d00081c40141c0030031044001e01110400b070300034150a660340384c0c4031010b0005a00b4152268000b5100600d4288029420b000d0365016510603680002c3c003403550383e03413502e80d4450294030172103840e100c03442540c49550b913940384200a50030900042e2220211510300d8882a0821822602800c50300e8441030b0466981d240090300ca4800200251201d0604220511403000f45034000c001074082c079254623803035607800d080c61601c1c0d840035045141900c0341040404c441c12620 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 636731897 1250 636730647 636730693
    0x30213020306090a091e0c03051002311502100509030408031b01023c09090403200607051c060e13050a0b040818040b010e010e06120406050711 63
    0x30030804160421245821b0880118101e41c5e0710f03046110112400c200020754003103100b1640a501101c4906000f0408401244655641d0503a400c02807404480b0041c119046607404c01c43c55403002ca01141d4a034091048194103440103130052f080801c00c0e8240003514403a40da0000070740b800131400e190502c600f0698920810940040703e220515151080c01d03000d4040350303006580b030007003100315002d0360120065103420222880001020030512159404407041505c00e82d11005024506030344030b40d181035404640b40d42012061101041e0098401707407080089900582050380d5990380e40c8013094202c0c8844900f4022818920304288007004200400d1200613002605084054552886460442e141c004001c9004000041020400090002c1c00300030f0000b0240c0302d101032070b0703800d122400c000440703040c000214003050504030712004a51040d0b01e80100000003601c0b861a00300d080100d0441d055084504542550b02c0340200880c45900c0018880515010b20040001003654800a4406c406c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 636733147 1250 636731897 636731911
    0x2032d0a0b0d0213020306031005091e030d0516030605120601030803060d05070e0f070c02180a0b03191202031c15090504030c051b010804080912030406030603021302030609 76
    0x88103007110260765245041c1c42140d90081121130921200e215a40c0a504111a2980700b4010000420083c0117140103541c4110b502c540504095000504110021141144040c80d01d00c020300c4042c0320703220340e84101c9000c0c2c80403d1108140543c10000101510f0450700b2103070007050660050b002880d0300144160560b54403154440c0c80343d03117200100381d2a9240440107003003407007800070010341c0f04070300040c0314040c0442e82c0c0c15130b000d9503640c0019502e18104020003074115240c20415440700703008a8880342c004a242c40080b0303404441e480001d1920040c156402207001180040604101d000c3c180300412102c1030000c0e6040030300b907480c02d8035280541d1100240301c540b0f807a2a6030041514007086000351070400810403840c10107007802040c080440008944c2c070f01c5000715440484824006540750304805a48040156440359101d410070342195078442c0d000b41c1ca03481c030703c0c006c10030600240c8080d01a0341d81c000b0783c0600d035004000c10090a81006811544108203202c140d84402c9400c6a000c02 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 636734397 1250 636733147 636733151
    0x1911060703110f070f0b010e1b040b1605010e0a030513061701030609060915091101410309030711040203010303050901030903022503032604290a02032d0a 68
    0x1494101402d0b0014407840c001e1006c0700c010004282d03a0840d1741c400e401b175894080781005491100b103510300c581c0304a01076440b902c40248a440d9a5002d805d0325000918440c00003c0f03401d24001d0300c00c0b80b525910f2803088021803404160400c030f42c014440c408004020919007400400820200310801503418000500001c1e1a41c80030428040e5503000344a100d640048016844903040c0000743c018411454100c550010306681070410758031600005c1c0d07080b0260108a441d079540c0c18200b84051600d28072441c451000392841400d0201100301852040c502130000d9a900c3c0210315014810a00c090031640c400c503c14401840800d42c2704056401180d400e00b07000450400c1424140d280800302d045031140c0030504000c81e050031400c0002175040328442e482d48110943c048a0840903035500da420400c88103803990024020540c03201d81c5a004c480c0c803958a00015030380401c020340385c3c841181c4401c11590000240f040240e0380c1d4035041c1000e410241604a141410300c1075040484000d020b40044036 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 636735647 1250 636734397 636734407
    0x10112107031410030212212206020c01020706093510060911070b220b0f010f05030a0c030602090112020c010905150f060103050c1911060703110f 64
    0x80e02036403160185a0807442c00c850285001c4070f10320f8030302049020403400380440c0440c21000704c0300043d0001d0410054503030b05150310403a0000701e12a070001d01909203480616032440710f40310b85010725400a040681e015050030b5582c0381c0007a1500b842544100104400c803d010080c3d2100002107082e41102c0c00545030042c50000025140c1140e01c4000804a026409010b49a10b50a6010700b0455200d104207106241c401e07020040e072800780031b074040c0c0f5402207000000d51140e129010030781c0c0c0405010384201009035a0300e07034507100e0000311000900415050010700c040340c440e41e003e00092400b00c00501000c0810342d1444d058001038031000f450b00d5000b1a0703015140e809614404164825401d0464507402e01c040b0a5020b0014400d0070340d2070323004e00d6071020b42c2c1c0125004114450980f24000d09515243c4100450080c100204010b01c1d061043c014000c50220040e1811308810903592590120041440c0c42400d040010341190141450030041e034000c980440184c442c0304144114013504c83e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 636736897 1250 636735647 636735661
    0x1e0e04031b0614100f0801060609120503040e04030e130207051f11160b090c0d1101090b0301090e0c0108091009020604030204050103030915031505130e010509101121 73
    0x10f40440444a035030007007482d0401410304008250700044600b140d0242040c5940ca501c000e080b603400e4042c0d0b07400503205210600280c01c1c450317549030b011442402241c3c5060381d5045003058880080d10200d0004e40003c204140074600a00d8807244880001021860640c4a551f5a5a070b55800c02101e078088100780d00c40d2a90840503486030840e2401c0c400501e40d91a07040c08010041c100403a0111040303442c0101043c054000017a0813002200083c00105890b0103540342d80c03427210f5601d04c40504005134140302140210105021710f0081039004000704024501b0011070303003002900058107042200c060f08220300c0c82e01c00180e403008110f00c104009094039290001c5a40d03403189400c0a9040782c2040d0002042541c0b2a21180c00c40d11410300a04d841169000224140e600c400c04a4000c10b554000a02c403610388403113074000310440c0c0300c00003c0c0d46801c650100d003952001c403854505504220341064905116000f4000494003064000d1320b44100e1a09881070060700e0300360018212007041c00200c071 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 636738147 1250 636736897 636736901
    0xc080105010c020427060609061202010c0507152c091f05090c0c060f070914040f0f020a030609050c030a0e1212071709060622061e0e04031b06 63
    0x1174200031070208181e0500326401a80c050080b000481c0c00a02d441c03000034800131030388224816900c1d000500d80240d03c1e0303070300112196800440d06640900a583c000103007040c0e41000c40030049002d032164803c00d80c0d07029a61213446180c0ca4000700a80d211010400141d070707070011030360b488031000d02208103100f21003050b071070031802c103030481a00a0400d900340700074051010f001d002440411000c03103c01b640d03142602c400504054904c03d0102e0302c013080034010421560000000300c80080c00c0080c1620101c40c0e524199403151032080042c0e9400101c09480c5507040c0207c401800e024801403105042c103a080700c065200091824440c80e0f603d03000c01490303010a1180c0e07101903101e00d01c00f80c0c5821f040080020450410390ba0310300841c20050762092000c1007248581d114100203000303000c4035603901c4203100400c80b04545000c201c01c0c0d0351030b092015081d14843c0070f019000740300803d0810b840130f000b031807030200c5d0700d4107c410000180c004010010741e00c0000004200804943e03a414040c1d10720b48000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 636739397 1250 636738147 636738161
    0x6250216170601080d080a020a030b0603192f030702031309020903010b1509010c2604090e0a080d020f09040207050f2a190308040e01030507050102010c080105010c0204 74
    0x11600c00101a008414000c1a0204100990308181d0703070b40d00101d0350b617004190b5100110303503110300080310ba50481c0d000c3c0103020598100801c580000354001a003036401140d00742404808480801603c1c1041e11500c1c1c1c291a40945c180501d10244050b541002e034014070001040000000041c21144284107441000440d41c442c0c80d0a2521100d904c0d0103904181d9aa80c000d61070510001c8140c609420440d02c400d030103004031071806514800441e41c05981400981d001c0c0c2c2c070f404480c1d400394414107182158410100c107441e192420701c50f0080942d103645201c240d50303900940903100415110b174103c0d15070014003030300141d5500c09807004040a003c2c9140c010f500c1840031829200380080031800809949110080e180480e0504090012080740b100800108940c21500c2d9005410318100e901c050070242c0100585140e925500d070078880d40680c010034130000300c000042003004002c0003502c010b01424002445600c0700118001d11017001480380728104110140c0c14015502c0d683d108030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 636740647 1250 636739397 636739423
    0x60b0f21040c0e0a0504021509010c1202100b030a050319020f1504060b0d1106090f0604060f0906030e030d050a0e0d0905310c020f010504031709062502 67
    0x16094034080c1030880403402c081c418007404168003800500809800d2007440e00c115401000710006400b000c211101a030404425981030002004082002c40c5072080f1255900000750300403c1c0c94101d0300d000da02580c7c202e50201c0d00cc0d074890350110002440100079a040342e40f040d2001b0070700c590813000c200e02d03101520208a1343d41c0070f1070020321071108004006611460003644180905001023080c0085081d41d20006003011001c8000000f4500e400402000f2507030f00105001806904480003030002d41c8107911200200c3c2d0343c0322a02e050150020320320001410181020000600070614940d05c922489843c5266281c0d604000348000d0701d981d11040c0c88607140d200302c0d4482c40701030001610041035070046a2003403484159000822214243c1702d5001c1d80c2c100076100442504692003006400303800049403d501543d410325014400034480c45118a01aa1300c100d00040c0c0d007070701ca485405024002c2140d542085080009480ca511414000628010f010324502420014220700b000d144d05841 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 636741897 1250 636740647 636740707
    0x30b031203010824190b0f150d0b09070f0c030c05010f051803090f09070c050f03091c050a0b190f0f0b04060e0f040f0816060f060b0f 59
    0x45042c90380002c40c003941e001d16140c81035414000300b80c4c0441e10382c01111a52140d14100c401501126a180c0180250400c0a0a100082e50403040021403a503103200540d07016042c04a85800e181580e8040d051001c0c105481e541c1947c20700f1800100203500754026441441f4803128450101489001000c0300740350000000c000340140c42e60210007402c000e0310004020800e98000e0303010440003200b129030901e802003032100f20810001c140100c000b4014201005e01c00c0c0c4140c00301c0492009d0108101100c078031405155181111001c00c6144040c1200007184000f0f942200000104009510f100c4550028108007140d55402d0502980c0c400688100200c1400d02c0d80720005800311341c0280e540a600c540040c0520103d69060100b1507025200e03100c4270b00a05004604481c0c0e00b03280c030030340150003510380c1400d0045940325039045900480c1d080400b54160141d080602c13503140308902e4170f9040d115041c4071492805403030a940d03003c2c5000702c080781600090918400b21212480266050440e0a4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 636743147 1250 636741897 636741899
    0xf120b1c080a0e060901050d0b03070503030c060708011202090712110406020a0507120809061803070e22200a030b0c2d0a0c1a0c090a090615030b03120301 68
    0x82503032070b00800e512801040200602d40528a0403106a41281006039221418a4881403414000c0e20300e4908258240c09002c50108454800380000d106069500340100080d00380031400405c010710580c8041d82d94040e11000e20016520040d07015000301640c901320b00c040c0c1200030260010a51130b50401906031000a00044946e00031a20640f1513014a05940d0400d40c1d8400e2481c0030341d091a0010103220741080303c09c20524140015250041d0700008081c01c0c40303d4840428541403464110003140544901040038515140c452031960340c0ba695584c01020029540d0041200c1c0ca0450708004885259030440d0580c5444440c9801541c2200c1207480c103007011010980d042d4000912001400c450750719502d4020303108418803828140c0e0200d00c51524001d003100312001c9120000444008541100c0f0410208601c0b40030390003041c034144415541c601940401c403c510441c2e0103805100e081002c1000341c01044443d49000800034200800c1c180800c1000038145007032000500504a00440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 636744397 1250 636743147 636743153
    0x120a020c0901171504110d14100f0506030f0703031407081315090e0f042907020d180905090102130303020307020906010e031905161d01060f120b1c 65
    0x303000085220a000707450060101508500d8201340440e00a40b4143c20014a03500c0f50400c2040d00004034007592540495286d50740f0054100140c1d0000200010303242d6000b08074142c4544500d0360083c10840c001c000020505044548802651102406101200303195500152440c021034031807652210000b40d4031118080d141109480a0081000161411007190314541c003422421b0240c42242c0b1003004107a4070011141884000248222182c0b102c020101a50381d0000d840c801241c6400040e40843d0b24040c50000d02e0607146088120422002c85141c010450341c2100c40780c155124442c0100e4140d80d145e1095019204800960800e101c10202c008141a4044003904007a4803c460444080d11010011901004040401c56140d000100c1c41880140b181c0002071780144030380180e449400810408403411300d01980005201456803919070340c5004030502e00c40c054481e81c03d00050500c5c212000810441c5070703c0a01e80f10596130401d08015503203c1c0419203a01d03040c103940114400246c5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 636745647 1250 636744397 636744419
    0x15100903060f02040503150c0d05091b010926031201080a1a060a09020703120e0309011e05070845101d04060806010b0304051002040503120a020c0901 66
    0x440155607852a084880c0210a0030740200d070116a401001031a07403514942170806040c1000c1c2c14030742070070b03c10003031060008100c0c02564850030030b40c406024840020541c04100324415821281000140030040c4140e43c950000700c40e50580740c143c110140d40c0c440d03c0c424030314850402603d0740d49140000010352401d00107081090030744030715001d0212926a40602110703103400e841c010352101790b44400380001070042c0e0140221038020703d094841d20001ca036802080700c0e200d13003d040c41604005040440395030424140d201ca4120810302014030086504002c080e4043d0300801004d480001400710301ca02c40c2000d410a0514040704400000d505031040543c0700b90003503da0000e800714000005030b45241c20340030200190050746401c1c0c20325070b03841404080d140d84102d41c02c0e881951030501041c00f240411902c0d000c3c01400c850980da034102420824900608600d4a40305280100400d0041c0d480210303507089001801c080c05620764440c103905a04040440c0c1d100341c0c001c01090000a44034480c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 636746897 1250 636745647 636745649
    0xa150b03120c0a020631050f010c1a040c0b0a02060403030c020a020d030305180a0602090a0f030804120618150b06180d050c03061e06010512070305151009 68
    0xc4080341d02100e2081c40c0742440c1d005103556030300290010241e08000d400c0031700040004140c07514600091065810340c1002403d90010398405450184900384414180008040600e42c001d0800300d0844000c0c0d40c0e0111111516417915080e2880c580100d810030440310720140c00f512255801507118004086c0c020350340e51084070141d0010b81400c0c100551580007041810070160003600000f0342207020b4905801602002c0e20790070070122407040042c01c1c12410b00c5101c0015201e401c0c0940c2c3c80c0f035030904201c0140030a8000500f040c45210082001078089400c503822240c040161256120103030030041d004007009415500d041000c1090300b410089002940c01c440005031508008881c000420300c41203000721010b400c00c0068050950449240c0407480e10104c034400c0048910194011700820b06184060300c42c45800e082e0040d070303403420174041c901450340040f003882d10360700703104d000d22090300758070360142a60f01450790f10404511309511401c000c903038088000c0c1010149000f21701d4020614241 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 636748147 1250 636746897 636746899
    0x3230d021b01140a0f050f0c070306110a0f032f0702010305160e0d050708011d190b040f03111e060604020c0706050c0a150c02010c0305091e0a150b 65
    0x61070360754085503000d82d004801e1024940e0f02c280c00e0611290040d180070b151803a030001849820700c8001c4013040480010720510003550040c00c0b08030f01e10b2074104e0030742d05e041070308011000080c0282c2c5045070f071040c21400200058030740401c0041d170104034006a40c010000c01481810700c6265007100e40d506000a0400b94401c1e60200b00c16a15480712032103104c20039840e00d000602c5c8144660451400121103444107000d0019984001e42e2070200f142114003108031912184400c9040e9680c08000703000703071390381c05603034004001c00542903640b20340c521480100010320720540c01340b8035014180710310b4807000441c001c507080361039042c041d01244102c41d0050b02d007a80710748035a41c00a591030405009030741861225200134138165041000568154000c0c981c0c04c096807050400b0030000c10381d160320149105d151204001000805104001d0944440507101010315050006000c14440005140103c50840341510444198071042142c1858001c16000d000b05401311000e910a0a0b40d521418174641c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 636749397 1250 636748147 636748183
    0x2040c050415032706020f0412120903020a0b0d020c0f030c100b03060402010807120f0207110915091506070524040302030403081b03070f031b0c03230d02 68
    0x160000c022401d0352003213000624641e450100c0d031002c050310041d2804025210380f001504280300071102c0549500150301802082c805010940306121103d210f640719a002403400c20000e50039600880d100e03800920404014003000200291101d2895040e00c818803100c9040d15204030005114613601d4100c00e29426480c00340b400c031140007803031034801d104c01c6070000307001341c8101d40e6207800550746014010940d40c180046064960036914080c420503070201180711006860b41c06504200c00155120701183e805542c544060042044460704000c100e07a10403030361445291707502d40f0100b110102509806410080126005e01008008100140c50f8103580c0c0300c100c03203001d4400003c1a0018156005400740c0c000300002c1c40460400801840b4216195a00c01d1245482e0b14040707140d0351012500b50344d02403040231580c00701988066168446840d0340c00024041701c40307456001c07000d602c2c1e110040960b81011071462509401380c0c0046a00c00d24882a1030030b0152045029440b101c00c2030b821147c1c85 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 636750647 1250 636749397 636749429
    0x40614010b091e01030608061e1b0717040b07080304062a111504080304030306140f0105090f09090706090915061b0507060f110307030c1e02040c0504 66
    0xc0c07510000d07203105290042500c1c0d01540083c860141c520582600300741016192800461401010014036002d004040c4910456030851800740540c45800b42c08030000c827809140704494140084143d0320103035000811903102d25620404035003c0e00c6642d20041100c1030100d10324040c02000800740d0300c030303e00490080c00011001003101d402540600780300d2001007110164103280074412044110700304034400c100d883e07140154010300c00c024401c850848400000104001c00c059242c01640c00404850b49602e21041d810400101810840020326040005c042a000d44555910782d180002c2c000183c8160300c1803c2c52a901a1036030141d01507500800ca426a0008070041140320305500608000001c002581c148401111310702c0307241038501034018000b454240892010b020000040100e526050350944280d03a01a0803950034598100582e001484041e000c030383c0007803480d1192030340a180c560380e0340500380a045c1000c08001010750018a0640b0610880d90000000d0042e10300c04100c40601c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 636751897 1250 636750647 636750659
    0x1020c070b03010509010b070c09090b06040f06050f040f02040f0f061106190509030705121b07050a0311060705031201032d110607080c0d11070b04290304061401 71
    0x1d48028800ca5401c8a110801003017101c0c04200980400d92152048060ba0796462035680c007139894041c429142c100014007405403501e8980f15051080c0720551041c860300c0d242c0b800190f05030301502e072014010380d103441c4004100c0001e64101e4000d4880d40c032003620101d0311030148090021841c00380b50081480000c0da1744201c0c0c1c00164440c444d060a003060f03880801d00350744400103014041c1030b4405074441444003100155003400701c0b0360341010010704039452701000f040400000004810541545d084028113205036180c0000107070030b694004110f004841101000700b000e0b48900d03c80504603000c08903c0070010302d10030050754101c90180d401d011f0b4018202420341580a0038460141c1c8001100f11004006804018001c0c81c000b401070040c1e007400042d07140d8148503442010701c0d01094205499100860783c003c2258660600c80a00602c1400d003042d080c514903204a0041c41020720110140d041c500300c00c4001388002020100005413070b0f0905161032409003c407031310049070202c2518000304903 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 636753147 1250 636751897 636751919
    0x17040504060e1504020f120a0e0c040e0c040207050712060c020c01050c150a0f15170109050307031809020a080f07110c04020306040f0e0607020f1c0e030703050d0201020c07 76
    0x98000748140c444035070101e4100802503010112146c282e40e8144942c2540c0303041284528400c0301e1518001c14041254580b03d802e000008800e9445503180040e102503847d4005600400c03070800380c40050756001a404c203d032424409a102c00c98a441000244041022903000b42980602c20340072900f400c0b4072030005407098000c624440b0325030f41c04140d10070032030300c0c1c451f0000b604914480b8000410303030002e040c0c0c5030a48002150030019030340518010010b0240c1008010881d12a02000300180e5425644454503449036090141c04c018803012401c03c0200c02a40d00d000030320350f0403811581c807d01d038200a010054125004007043c04d0b030000180c4401d025495039104d0b41c511074080c1c03a031550390404100c02500050718580d0020366624850640c00487d21454400542c502c0040120f841c0c0717000024138102c040a058905034201c40440700e0305d0200a03003002e4200246040251400e240724012a00d8100ca99102425034414807095021054065000340074544038401a11542c1d070b1280b90000c2d0b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 636754397 1250 636753147 636753151
    0x607031713082a0f0106050f03011517030903100b0906090c0406030e030c03041409010b090315060301180c080f0304080607030518030403080a0e03210a090317040504060e 75
    0x22507100f044002d0f1085031028560650041d10310044240744214041c0c18601a005550140141c0d9105002d00c158a000e020304203480d00c0445c004e11030402d00f0100140d481481c0d00c1140340d00704400d03400d2211000b080c01070340c000c51005401c980e0041051200e0101030809404641e0203604080c000c22824100231180320310900d02c010800349400d00d4500b04030018000401042c4481c002444036421902082c070061000b8811283c036901c4590202c070400141e0081a030020b142c0381003c010010f00341d10042400e03419801032208070101a51803602080c091301081c240c002c0000c07201078092040050040664060340d4509046462100b03100350825034912883c02004100d500c50030000f10231900c03c2c0c100e90f9010314402420074111520502003132642c0c005820480741b550300420403c2d0300540c0944d54a51aa074100c0c018603007449520b070f804040410036000c054014400042d0100c1e80c2d80502c800300700450344001c00105200280c0ca483c05682c20502801e44901c0c2080c8001900044545e00c2c24 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 636755647 1250 636754397 636754403
    0x609070c0b04021017180609160306050a0603080c011d01091109070c0506330d06050c0c120301031a01050a1203030f0e03031005040c050403030c0c050607031713 71
    0x1c064a4a8080100d14800300e070049003003000c2603400d0f0700c044400c8801e25000d080205000f049124010450340c1c106000144606040c0e803142c0310f0448078815a07800e5070110381d006100007885443da40c010b034001c3c00c1a50005000b04000062035001500b0562113001384039000c545074001028815511070988400355006061000300c45101200d072315042101ca03401100c0e9003018088849255219410030004403580301b001c0300c045075188101801483c41840342d6043e44500080041a54000b0f2410a6904005003486640e0030014201040c0b90048999981040c07040b11749440c92603400c20000d5000340804c44449055200705600c1120050321541603543c0280001642420440460410141050709500301a1661512600000948510950034040c50061542c2e89440c0382c03255080c08042e40807501461a106200005a078800191070550360315240c54900c100a6003007094840c20560021a4041400102d180415030001210307281d261107032400031041d64440035600d10b07180e03103a4800713 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 636756897 1250 636755647 636755663
    0x5012d1a011d06090d05060a05070807050f2d0705010b0f03030708160b01170606030703031d04090506010617150604090e0a050607121109060a20030706050609070c 72
    0x2d440100e0880207200d600390380107031805080030b00342800907001c45142102510140c21010612080400c1c41c0034059200e1200d0520165030f003044d1030028034500c50389070620144100800d01d5101070080d00440410191547c0001448107582000c0711516400540304490700d42c40d00c000319146003456081c2100b5003100034041c600f40141d03a1107a90141e0310107000160b6800c41d000c0000c00003800c0c3c0c540310303000c3d0940c203800d174800803240b159080c9401000381c02181300c0d6002503400c02c00260f1020190b4030010159504071894002c49002c81c020301465103008102d400b520002081c080e41c42080c03e01000d0070011402c0c1e0903240c0c1c200c800c00346100c400d031060300484104000d000012045e0401020180900d04551a010150715000e00f882415121100000e205010031040d00d0003502402a0540d080202a440d19010318005103941c45140004028001e5007080d90b0f83c000c0100c0000403040d45240252a81c1e0486803411034001c16040390701300c1c49030301044085401d0a2040a005120540c0103400d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 636758147 1250 636756897 636756917
    0xf0a0f0b1f0c0611090a0501020303060f15090402031e4005060420030c011d030a08040902040614040605070f050705280e101205012d1a01 61
    0x70946011040521007040c0702c01075011100084051107081100f82662400b40c2e210202c1c001042040200c5030b104504541c800d00c10301089036588816032946103c00c0701c121000501c03030054a200d50180a0701607611520100400c0f00c4014480070040489040c1408400d0540e02c0c01200c88100c020f42400803511540a116400740031030580801070600348810301e007a40a03286a840903c1c144045804884081032616401c90482008032041a5400c0840c013620200620f080001e1032541c0f203481841e43e4486504401400c2d44081c40312030b000f107400803007640d0340320b46450f4020040c7d13005116510000d101c200404042c0580901590251200740e681c843ca014800e44549070b442c6030303403001680d6602907c2c134002032550342c2c0f03d030803040e4240020201001ca01c803c403400085480f01e500072045405240c0421005d0410140c04000340d0350702e400d400350715580c1d03820304900410a103440607082c0304030a080040d003a143d01c00304000148843c0d03001d10942c41500c41c56054040e00022b00c5010954000da = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 636759397 1250 636758147 636758179
    0x70b06060304051f0902041d15060d0222090b10080706080c0315031b0a050d05030f0a0512010b030a0c140d1808180a060305061003020702030c03060f0a0f0b 69
    0x54030700c6150740ca203240421021000d8001a00b200c0111403600e001403010740d0744005000e400e000084142c9c001603086200d626141d804240300d00020b002c001e00c1031010407071a40b884031602c58008201c202c550020425080355181440d07245406803402244581c0320f2000240f035130350000d00c010613503140f5681e6603000e40350141903440c541c002401101088a00204a005940b0100709a045503040c0c80e03038401903981ca60741801200314460b00b040d07005042060401011810010845000d018101441583d0305000402103400d070141040003443c0f4045000009100080d4801460058a80402c100910083d0f000140e801d0f4620300883c000e5031006001d8403c0346a4a980915840003040440050803aa10381e1098950340c4681000e0101c080101c0c04500703682000704c1c166025040d11b050030006030400c200002c6907005568079440405400141750400c40d10107002021040314054112034050500f00c0002000b01c50403640340c41828582601081094101d000300c0318400e00141c4580805d000e202 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 636760647 1250 636759397 636759433
    0x81e031312050a0b0405030d151508100b070506061017010302060c0313230a060206040f0f020909011d01060b0d020c01060810020406021504031b0303060b0a05070b0606030405 77
    0xd40640316400303003921800c01310b01840b41d1544a18842d4002c0c5580d131301510000300464100ca010344d0351926000c0000c1c4140c60200b020454207a543e0b05100d4074558400f00e10301c0a002c410b4210f8201c240000c955081002400507844d030003071104a80b080300002400c10111042c1044030a03501e0507000714001003015081203030007480b6500f8400240ea2070507003e0f860980000481c5e07032003030903000312101c0e0b1030ba20742080c01c00d440d595010031034001c50b48504d0042c0003940d174000a0300140007042940101d8041180c4d113010f5640850380034210f580140382031001c47d8001c1182000314202d0450341002c80313080c04e0040c030450003034031034800c950390030070113046000002504005c0158082d0342d41c0c0e0b0801704161004000c16604000314000250707440d030402c0e000905011203003818240c560030100a0100094100d03950256004046214444800342c60a045014050079403011000300400154500c0c0c880c1d101000700091030041b05806516101c00d418091144812500602981c00443e00c0c020117220007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 636761897 1250 636760647 636760679
    0xe06070201030b1314010f050102010c0f030f0b0d03020c01090e0112150e070f0f060201110d20130504050f0f060d0c080303070306031101030b01050904020c070f081e0313 75
    0x1800e4414000304e1805190100d81426807503140c2260040e00401005004000d00c5001c0d040c00e10091008511007030000c1d040e20340a920b0a803d140e2030748c004010f0400c2e50ba105510b04d01000305207542e041c640e1706000e03481d0340558222600040401c000400d1140b6600c606604075888200303890b18400d0b07251108603010051031008108151500190722100f941004444c01816004107200c1c0d140c0e02e45a100d01c11142a0307400641075905109003817000401c200c00fa03880180f4206130229000300d642e81c08810202e072915140100e444040745001684280040100680f141a6010000c0e6100d900000c0c0c0c5240048540c6004442c4280000e80c2900384000800400ca01c074540e03115200d07488101044c2035800c1140c90f4800240d840100308103100018660000304502030a04002041c121000200a44103038100d0502558002580a0b5515002c1041d840141602074080c0714103a1a0b500c9a0f841d404110002d4410400c40420300408540120495802000514000d0710710b514100c800c400c5a440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 636763147 1250 636761897 636761899
    0x90616090603021b03071109100e070c050f100e010e0106050306070c02031006151b0c05040c0e0301090c0f0602160e220506040b10061202090a03050a0b04060506010e06070201030b 79
    0x140700b040303134454132081010302920340c4a60060301405100006022031480020301c08100c0404208003040014003008034241c0142071490a0650801c66007011032901603005c00f002c05c140301d081071403108071440b50f01036004a80d2810084c055125400c506a0070380f4624003c0a6050704180e010a2070075000c2c541100d1b50510240039264004110700d0181c04480072580a55107886030410f070400302d1580101038a06848031030985480060042d2164064000a8003916001d10758900d00864007a001c1e103070001100074001c0080c04010128a8000a928160301c101204151100c7c1d01240300360011803948403100c1105005810f041c98010400810349000e000c1e40c0c806080d6400201c448106489480c002034082c00042609041500d000071103040700a0004c000da202059052107043d9100d442c40700c0d096403201e00580c0314400c070b100113291901a41e00c02002ca1107400c0c4440200030724280914403960042404004075619040190350001030711056a6201c0070401c440401503010303620000c2e00da08 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 636764397 1250 636763147 636763177
    0x50307030312051506030109090b1806040201080a020910200c13113601020607051210080a030206011401210e0a0813030b1305030910050d060e09061609060302 70
    0x144d181c046401a0f0081e004000b04546542000c0244441c0f01001c50300300d40b0020700e60481801c070404194487c1e6007d8402810054542c1c085244140c0e141c041c1c0b00420801410300d08c030849000c40180c4200c403441081d69070040400001e40c0c1c03440001c549200b0503040900382150130f1139402c484000801d4512000c0f42160802d01c0041010b5141d510622003100106000c1640c1c0d02109509210f0b400d100225a41194020b0080141e4a0340c0700c025209103110191403105030340c41e82000d040181506800c50f5401d4452050500280340e17000070450304890302003400c05802c4114000444810203c4a43c01e2120b0101d9240b11a00e00c009510001e00003c0d0503040e9241c451140e907410359264050880e460900031000014010310402400164100c0c092209400080fa80c664034540c69008000c00b0743e114030301c2d441e0300d800201d004600f11403801c4140002044030548500030041c5c07803441500c03c0041481888000303004600741e110020100c15458446c50205032038000114060350007900c405504503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 636765647 1250 636764397 636764431
    0x3060402061b10020405130615030b04090203010e0607080a09020102150403030e0d050a09140a0e04020d050d02010614010f081807030819030b1509060304080f0a0e0a05030703031205 80
    0x58082c80707100650790074003c002d41d0b01e91074001001180030a0798001310480d403829408126400d403a09007850803201908001c00d21800d0400094000d14a8007030294155081c041400030b51140460083c4c031842d500d03210320045440300f400c01c604403020850000d0140c0d101c0704909401c0c0306a07011996001d440b030b1030045407030015405c01c1810002c1c81c640f640017044000c030354201902e4012085002800f02400007150341c0120b400040c0b007154a03403080d0b403410074841001c80d0554803200c01c540b0723459400c0341c11510740c0d002c03e100090003010301c0d105002c10810a14000f1070158811841c0304841d440755034400ca0551074800b8180b00300094605450410f00c5440300000005e8071008c09022404008040040040809907003d429540d0b40600c5501c600d02c890000880300348a1800d0320600702056510b1502c07983c80c0e1601d40c0541c0704000a034035007600082142c041041d0310a0004c0f1044405642c0904082e43d15028103a90b0304650000a022a0941c41c65042d4511035034001039000e8500c0c0035110000d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 636766897 1250 636765647 636765697
    0x80d0302160609241424031603061d1024080609010c0201270501090204020c0a0203010f022d0910020f2e021605060705071a0103020306040206 63
    0x49030803e004955144800c144081e101e0746540780c20060342c4d5138690a000c40b507589110643c020500a1102400d0340790580003110300915400e050300d0302e4001070100da500104407414401006603034403080354480d00345107808818042d00116440d403d02000f0051100382e060081c264068820403241403491444101d01c40c845440402c103650081801b180504414102010054292490b81c03c4a80641e03040006940d10054540d00b045680c9002d68040801c1400d289002c3e4007601c40d0321400b962080c008501807412520205031800034501c03c800810003c908000503000340d004001000c402c0840d4603001d9550000b0001c0903280c80031140340004d281c51801800a54440441440388005038803148445a16100800111600408103146031807404801d0140c80e581030342c014070f09514207130003041783e003503940107082c0b840072684e8803070705072101454004070052140e002030304252510380d854174039040460010f9400c0381c1a00d4026001c0d1100390740d143c09000c800c0d0f101003c0000c80e8004030399000c0384 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 636768147 1250 636766897 636766901
    0x518060301090e0f0a020a06080a060806070e01020d08060906040c020c060706051b03010320041506081e010315020f13030501230f01050f19090c0305010f080d03021606 74
    0x10b010041c200141e40600200100d281004010301c4800c0e90f4004d0070040b0150341c40c0c521000495680e4a4145925942d00c81900081c00301030340102514402c5206000441b504200043c0c3c00b00b034281d080320b1040003209022100000d064801d1500280b00c040030500c81e0038030760008c040b00401d90040b103034032665a40114802e83c3c0010350960700c241d5600705202820120f51617441444079501d04182c119419901c0342008241c90160f6104600d070380d03540d05a02502caa4210440c101920070706a6074090399504040d186210403124445040e05403045210070512840980d03050704d4000040c680ea400c020850381e0300a60083d00203980072201031010a8a8802d180aa800030b90b118000100354050340a064000d0f1003a50714411580c44000010000c52855483c1914112582165210000c10140011030589000b80d544550f101d1000c1e4400300f100e102035088840d034464907640400ca10781c1d03110300e4258183c80724001e85d015074000c62403100c0d846119402601042e51407880e140301c0e83d0400d03640d940c2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 636769397 1250 636768147 636768149
    0x10141611030f130512061e0711060907181116330506090613150b0703080f09190305181e0405070801151b080a02100b010e0d02010518060301 62
    0x3c4010010000744003e003006140b0a85480465000780340a00304406d030200c0b0070485010025285004100080c030b018440c10040078001005010707580107041c55000c107911101d03280580004411025603036080d685151113004d0030f0400d1101801e0401f0400100742e210801760702804e944490600b46540c8400011780045040074404200f9995040707007813000c09082d51001003485124400d06020011562900045d501c481c250080e0001100c4200261048403140c0e0354208484d114400b141c0320b000c054210400074011042501850300550f5280ad0311aa0713001c011480e40700b01d039121003404000be4001c5000c1d000010b100302c1d110036030020003800b08848002c10791410600007a4510900790604203441001c0d00609103152900442d8140360300380c0c83c50180d04110004104081c202e00d12a0741c50004c21003415580701810a6030f079403112000a50f602c41d01c1300b09452441c903081c03112126601425510418040c0502110010400d5800640c1c01d500b00a124141134a41070110728020380d10040118 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 636770647 1250 636769397 636769417
    0xf1506080a03020105010b0906390c011b0c0608090118060b0405060f0603070e01020c1008070f170c0901030f060303050318031c02090d060e10141611030f 68
    0xd46007a181002820b440c07040c0d07c000640102005801031f55100e035070490324044140f0003031140036010310384007880d802d1400a6030340284040369074000180702c010540c0da6130440300340c0e02c03142908810041070003030380003049005001314130f42281040700c14003500185e6032100c0c408000107102001010040002400c1003401c036400ca9071218084050328082c40790913000001600e008007858022004109a8030000d06071078207110a80d18401400c0e0b2003007040003840700b0050800302c0000c242c5940600203a0342030f555840464401413240300910302c11040200b288104042d5112582c48112384100a907014a07030440c105516075082c802c14040c54082c050046200c1d5a91550301d02c0c1030b02e41410041e51001c010281030b0801c02c11015000389080300030040c9100380d500142e1340c40e0140b001036121011321000802d1681407110312101e201c000b142106444003001402e000c1486118030300d10706800116288075000d00000c3c01c00c4a41032040404010701c0c018441103d00e444022601180907400251000c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 636771897 1250 636770647 636770653
    0x150a0f090f0c08100303080a062103021905071e23010905010504050a030b070509130c031401122a090b1203030702030f0310031401020702010e09090a0f150608 70
    0x421541c00d00c0b8802e49070500002e140c14441070401c45103501c0040032070311014040100e0800403518081c1290721036002016481940940711004151000c0d440c80c0410099025004903006001c5d8140714000c20820b032944917001d0618182444442d200c015105036451402d0840c991012440b0f606442110b50300c0d42a0b4807c02c1402d019840004000344200e802407410400306102c100103d889079801101030341d50002425180e0741d64810102d40b030b401003d50f9154000300d00160004150b00991040c1c5040300581e80900859010100c3e40852150030702c40c2c0c144007200070364600701142c0c0c8040c083c00001c0c000c4280000740820030361004401513003504180111580ca07202c00b036451510798041c8281d81d4135800070718114645800c002e500e90140400c054896030000000039070303c00b0203400010166500001c44083c0c0d03c03010f08014001e400c04030040f400b00e06210b1010340c5514101c03420782e100b1009078008040500140c1c0c4d0340b01803030030300200807074000001c1c0300c159896913001e020f800c01400d003070402 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 636773147 1250 636771897 636771911
    0x12030b0d140106081f051801020f040608070e06032406040f0e1003030503070c030314010b030f0a110405040b0105041d0403080f0c030705070f020405013209150a0f09 73
    0x1d12421100780e07900c016050f500c00c443c5440d50300000003c80c400b080000c0c000050981e10000091038046220700c1280c540d501c0014544030641d5420090026140260b850789860381c5c0d461415108012110160b591001e4248000340d000d90b0703245403201c5030407000501d981072600508041129500300b500507603450390089400340180c506205c8035960054850b08089145842d40d1000b40280c80090111420400024920024540a078102c14183c0e074940700180815a907a8042403220b40040d079030750707503002c9031741001c501001c00f0b900400d02d2a000f0a65143d02d858a040100309c014082c0c00d1080d810300906110000d81c400210240f40b100000c0c1c42d1400d40346103464a00200034140080008400090510900c07411009120030f4a9001586041260b5074006505001c60b500f50b0440c1e009520a0030080089040c40c800d043c41a1103101c05981c404101104036214000e18ec161000150800b450000080d00c04500312034480c4080f0001c0d1007d007015440d0442e04070000c04a07080b18400d26150f842c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 636774397 1250 636773147 636773183
    0x90804050112050606030a0902150309070f090c0206160309060515120604030c0b06060c030a0e1309350301240e0d02010c03021603060b0405010f0605040312030b0d 72
    0x200c5110000c4408103c40d18011001a500740405099452440e0756100900119142d40038042e448002d00d444168681c6040d01e2420355503000c5000303141510910305000207940c009070049841082aa0b005003400391788410345001d100d5146850a410991a0095000410410b1007194000c03082003a40e401c01c0c070fa40505001c1980c105060030380d00c3c0d030302c202c0800003c21f6001928641c00c9a00c14000013040d00c8030705c0051f12074000d80d15540424000042e80507030a94000480d840c000000b550140c070020000000041114500e08020b84040e1803e0f804044a17680241126850785004403034400000074071000482c150400d0700803030201a912820601050030b207188020440080f840e003030002e503000c0300c04138002281d9810000c0c1841240d0065108060003400740c14240f1694807112005a55030f0308101c005845c44024442c06945040008100c407840402e902090b189152142032801c0d241d580c0782c5544081d583d440c1f10030142d0394207461441381d030b4100c00503140a0188104441c40003c4403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 636775647 1250 636774397 636774407
    0x260601090b0a230c03070807170313030f110c09040804121b050a14060711031603020405150306011211030109060e0c031b0d11030a060204030506090d020a081602040908040501 77
    0x1000032400d00710280410548104d0010448540542c0403071116124505841e0010140f541c0c860031902c0e104002c01000704070904160b6100c00180260b90342c0c080029405030a0700d60008041c030807580c54202290259050501c802e90580003807145000b030703280c19076404803078015440d282c0d021225035200c8002c6100d2403c04c04c81c07407070103020111286c0c240640f80048000307055500341c808138081d00c07010031701c4400e00c40034540310040400d02505407807010f44102030001e400419400202d01c44d80ca013902142003c10904400c980ba140058028040390342000e0840c1c0154030f640104550091520b5100d2480e61030a00843c2409840f0390004070b42c6000c401040ca040c49840f00284e40a54405005a00a00071a0402c5817100c10103494039050fa00c51428204d40c05162b01c040c054140c800d01c242c200070400164000c1044a0180c01035445507140d2803509612944000e0402005074048507000002c0751030b842c010b050803400342a980903450ba0710303804a400e54808401c03c0c1d400813804241004296080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 636776897 1250 636775647 636775697
    0x301170706170604180b010f051206040b0106110a14030d060501020d2114010806041406100306150504180b0601090302011727100606260601090b0a 65
    0x41e0901c0e0b0449407031080300703a142d04402080075104035140e11003188030500200d04a00700e50b0b00301c803110b0300c3d07581c40d00106441c68000b03106042c01100103140c550500140414402d0180e40d101a8440c116443e1120442c0c07038042001c0000e406000e080da842c00003031030b0110054480355500001d952906607150000040f031f1265480181503400c900700082607503a001680f2000703102d03814048502c0c400820100390081640302000b252a8255000114811800141c030a01c20f030301c1071982d20003100b06141d02d6034640800303450810044c001c24000b03100059007500107203c242c2c55030b4650040c155480300013034151100180c003501072145003600300060200840c0702c240d00040c207080c14201c861440c0c4c0000d085000000764100380c035402502042c06110080c1c031240080c1c800900610b14404c000c64225250480310811010782403a003040043d4403030040c80403406841c2d00c10600d8000c000c00011100c04518002d004d6810402ca4280105e901000340303001e0301c0d40e00c0712607039181c00c0e4003283c40071440004a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 636778147 1250 636776897 636776909
    0x70e0a08010b19210503090a06050904050a0908030103030507150501030f0507171f2c070609120f06240f05040501120201050f09091617090c0118050603011707 70
    0x550300070300014141004600401130400055001a03240781000f42c04c0d801800a00b035401003c1800c0000c90355070000250071a000200c82c200701a4480d050042d08940300160000c001d404140700410109000b480602401c5010b84220421540c00c0c145003c125213090b00201e4041d00090001400d1000400241000e07154040200c00240c260300401640c91580440e6109800402d600b4912b0381c0f840707604941c250f016440c0c40d07001d042e2107100704110708403080011200544144180020128480e2140030129507021200412800c0240c44102c1c0c2c882c80c0f208150fa01680b913001012903c0601030250401001c4000c0b810805410075003030f000e40d015281d1065200707900b441c0c0144210308517400c01e212001d0782420711907520410348004c040a405001403060f807180040c4104044824032030325405413601c041d680d80d200c42c0c8000003665004030003035811310744661250b4511070855006501d07855416440c03043c10450607a88600145a96000740c003c846507501c3d44080c0c0740031410402c0002c015001c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 636779397 1250 636778147 636778189
    0xc08010e0a05062806060e131e020904020c150907080a231204030f0209090d0c11030c1905040b0603190507050702060a020f070f0f0e070e0a08010b 65
    0x1d26610354650f00d00740130b030001d0000c1c080e4184180404c4c141c40d240c074a00e0403240d030092000c03e0766040d001d80400000c541c290b0080300004441800891144100500c200d01902851402d040b0b1030321020007500050350b556001a4200800400c500040101049403821040700b140646010b140c1242041059400f080555210410790400500351607191100080241c0d40d40340d451050040c6145803011045844a14520001d80401400f100c00740c1d85500034000c0d152140b03242c0720580042c0c1e0750704640c5610700000f5003030070640300011a0b0001220400400a01300e0300140007420010340200a1740c48941c0c0480030f20b800802503418103001d00f9101c0041110355900394036214210541005540005403001641d54001136005805541511420781d005441603031510720250010b9501e2030b011044400c2445186000142100f00c2c489d224191201c90301c0131100c007445c02941e03010801015084500b8066400c0d9030110548504a200c0e0081150f1400424416a8102400341380c50681e110300c5140c078 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 636780647 1250 636779397 636779413
    0x207060213090e1614210604020406150509040f0b040606030504050f010b060d020a26150901150305040c05120d0f0203030601050702011b0b100f050a0e190204030605040c08010e 78
    0x11196003408130071108500304960010620900042c03000051452901c1c681500006088913040002080d81c49607209a0701000002d03151418004035510b00c0b0018030000f4410031004500c0e05058101c9455500007400c00303e4617104040020b07084c0e5040c3d4011070002035460042005014007084490035182491000b002100c1c45940460030034419281003001715500010400c03201c0d0310400e681a0b80b000b0344082c1c00c0c0c404424240c00c5107007441c251003001032001d00354a20072032450a460503504030703480c2c000f2541c00080c441e0015005070070014025610103500070000183c80c3c40d102c40d4404c030b254906000c2c1c100d5184008018001d103601002e1901150b20034010010b80c0d0341c1000c11240c800340c090034451921070b090114502d40708151007006005030800700c01d2103820b01810549000340d5443c214484c80a0303490300b0500c826a85603102c1c0400c40c051030408940c01440c014800024020701c0403001d803405840b07440301d00a9441c2950116425840054100b103000e0085c440c1900020304440545281 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 636781897 1250 636780647 636780673
    0x601020c0f2101181703012907060603032001152d06020703050d03060506030105040e0c1203090a06020307020604030305160c06020a020906010c1a0702030705160e010e1b0d0207060213090e 83
    0x1428a421a1035200da882d980c00f04050f6058078181c409c45c5a2100050211988a24000780709603001e00000380039004080c003049200c10103024044580c1107810185400c607242101e000550481080f491020303600c5480c01e002082800b101035809081240c0080c04400c0c42d52501c14948880701e032121040600c1c1c020140419a03407a001c407811241e0444000c60f5000462800501b0a0b8010281541c88401e40a504002240110142c209540704071490210703d275a070310050b6280d01c94054001d50000d0100814400179004102800401d80c220756400305e5a003469031545050030454208a003d40d000d819100e04600d4160f9a090388214203180480101d12240d540032031018841c00e0742200c0c0c455010000340000c2c420030070341d08274940040880314001c03007040c80c00400914038003c0c04000e009600c000324034035a02100c440e0060381a11000040c41d030958010305e41da80c0203210316800d1140c00f0050344010455900150059240d40e00203c03825034500b105a4044070016141d0f8043d81e0084050030b003172 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 636783147 1250 636781897 636781919
    0xe06011a131505040b0d050103140a0213022d070506250e0303090607060f060512071413020d0c1e020307061a0a0b0a080601020c0f210118170301 64
    0x8540511810340b02000c8041c1050715280110f41104a808401007942060300766150003081c100c07030149031030200d14810411025143c400c21031020f0340003208075500c0c03c44916141c1c0104108062901800702d03030742d000010880c01d41d030308414414038240e000c2045018484244513150f0010030458003101601c0100d41d200200030060350b5044240000c5020180c80c580307041c401c035403607060010102079854200785018002050441d0b220500d6614048021a0908046042c040c0000041c40208805807412803454401e5515064568115400000e644002109800030300201c048046c000709841401c083c0003490103c07084461a01c028198402c4044590003000711022203411040116800e0070101d55414414058043d0390341107100389000003540c403c6400500700c506c0c042e9403107250580b110030049a0352515404155409244082440058034006170511049008804c4082c419114031503440d0071542240714500c40b88a00c0c005a80800c541c0d898000350190289010314203650410307281c01c0c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 636784397 1250 636783147 636783149
    0x601060c1a0702101506031a060906130302040906050403031436030403141005090601120614100501090b120a0c120504080a090510080c0a030f0e06011a13 68
    0x415a5031110104107424800c1c08403058100780c0803000e02850309070040c05c419001d0140314490009160050460707000601640e06511028000d104500300340703058041100c240e001c00841d600a00d0708400000040e100e81c040d6034201030140400142601d840d0502509030760000310389e503294032284020000040d600b145a0341d50802c036510f008062081c16850f58100e4480c17104015500e01c00810b0000800080c3c4400c0584002071000742c8031030049001d40b51041d10410381c1c0400c200d03008200144004042c0416507480180100d0000c01c10340b850403540411102d0585a0200850400d00240070951304016210300074008440070620b0544800c10032016048060300700d19200d03071240c0054480520820603040342e8520868100138a05141c07501070001d900c0b203c04200807404a0400043d10320b0200e0f0301c102032600a0326030110741e540391710780d04072917a210710480c2007810341c2c51082030000c4100d031041071504040040140907550600383c00d000d14082d501503c01c3e120700d0400c0b04021110160407014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 636785647 1250 636784397 636784433
    0x40e0903030f0c1b070b070302150c040603050a0f1a01140723070305070b090102010c03020412020103051f06030e0606030703020d11010201060b0c06040c150c0f0206070503030906090601060c 84
    0x1075120501c1d40300304003440701c001135451901d105035400072070700c4004034004001070342c407036000c6580e041a20304984141c140304a07081c80c0521000d2104100a42c0243c001d5a0701c4041841e0000b8003210403150242154403040c001d41d5583c004070b841100340d5800069540003601e441500342d0030300140d9996040d924186161000d071400881c5550400b102007044000c1c0a1940303c8161241261115040041134000c1440d590056080030902d580c0c60740a40300315000d90b86010480840800c0640041d4040e01018080d081c01e03e407a610851050401c56a1008c084c00083d9404506010b4040c1541d28003000901a075109400a81c410070040c0d4030381503001e2090380d00103c001e13103060980c2c1c0142c3c01030061383e000e4042d0510025044c00303001408501d05125500c80e01c100e10b00b241d01c0d5400740c030080398130702c1014010134a01d00d054030129941007601880f052008080f6868101c0705d80e0707410b0a40e00192403265072980030400740156030900b03002041c09030201740307880c03040c29819441d40315001465466030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 636786897 1250 636785647 636785671
    0x603021611030a061806140402131e0218150c0624090a0c110105090709020d18120809010b010806010c0809101e0203040b091908060705040e0903030f 66
    0x85a030b0b141805100d05060b0054401c0100d00d21403882203042c2c0315012000c442d03941c5031000155400c2600e1400d40d00454001c0c00303941d152400e103100304005140c1d845007a003922030b2141e08078100b604180001d00005184d45880301174605004240035000c2e400c0b130210020350b00c0500544102a40020b0102ea0007451041c5003800702e0480a5240c0201503007156154100f035610080020b02222500240d000c064140e8512403401c00c00c0b004d203400c0310001c9d0b0380c080c955003160800300910002500074140e46140d48800181d440828401e080301680e104d082122030561a60580464a404c03010701d0f0390121380c1a00030b0003410282c40009009100060046040c4104060181705021481c8184e40e0201d901030800c2b2003591300d081e00940348410540e032540d060180f0340c1076001d1483c40881603600b00c69580d40468101540c01d001c100d00c01c0e82003441c1050031040100c6c00602c0e03260401c29035008010382d840c3c0b99a603030f0038401c098202150082c1901c1e220f500c10414041d100302d4503000e096100902c4840303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 636788147 1250 636786897 636786923
    0x6060616020a0f1d01050105090108041205091e012003090d03110114160c050c100302070b01060903211b1b03200301050610030e010f0612030906030216 67
    0x540c00b003140c1d0800d6200c21840f40340131424200440c1100405207810750030b05640d03a40e403c0111100d1050361222030000d0030070300205000410311410700aa43d15542001070400301c450b0086821507040c00c980b01d01510600d035511242c1c1d40c02c0100704120780004850818540258041d01e80d41e8441d80c030741c103806a008012154281807094200025003a0200024813604903180d954100300b0005079a0100f904203066180c944c81806106032001c00340d40300000d030103a49400d00822408949070052541456020401100055200a800c40c0030b04101d84031a03170b00904508005081e16440903603540c9612006503440845600400c802e00b184205d080849403003855071030308440040e40302e554100102c04d8600048208409405500c596100c81105884c1c464011030402d030994106032101032f0440f021120241c0c40318070982068080310501000070841d107100400343c100325149170740030f00c00038118051184105548420408014000e0389030030f6082801e10803c12007000090180141200c454003c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 636789397 1250 636788147 636788149
    0x1020d1202090604030302010b103b09070206010e0c070c0b0a0903020a08011409010515010c1a0106050c100e03041e090203010b03100609030807062307110d020606061602 75
    0x445074a0b40e0081c120716240c0740d0b60302c1c4c0603002c3e040c403071000c620490480207a03840310340c8100f01c0c211040b1840311840721a904480102480c5800704c510010900008050200498603004202c07804cd400c01d60040000b5032410244551a44010f041c0081c0c441c420003490000c141540e003142c0c182e8500110044e650000c0030300c20f94048100d40c0c8000d4219680103c00147c422045d4440300c6807036990204e04c0035541e5001810750032501c0072150540110809443c0032160351089aa100c1074074454101101c22048240c6902e4200009030301c03100018038009001c0344200c0d810301c01d6942c0e60b507106409002c0400c0f07041680c1c0c0ca90080d40031703000d040c0c0c09000b16a881ca03190404d03294003e01146a046540303585542507034029503c01c44480c001191070b4140098900c2c415007514084a4120310910305081700e1f13581d080003504411140c1b465010301006003089225807200154000c070f8848e11070080800d182e034020340c200340b044000c001c15500b200003000010340f500f00c100d0b0304040038141034442500b4584 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 636790647 1250 636789397 636789401
    0x901150c110315010f0f09090807030c080d2d050603070e070201231519050108061f0c0201080907050d080a14030117100207020105071103010b042a0503010501020d12 73
    0x803243c943c4000125000080101042c0015000d40380c14403d800b4140352204015003e4942105004010b140c0030400703000030901c00d01a42c051684204441490401e400d2044020340d10244040100c25603803d945a92040c2d8105120481948412003400b90780340c1840003a0321000b562145500041000001455183c0300f035002020702000310340c003400c610303003c440c034002120303001c44001909150b04542c600d90b07032806054214034003c64004122075542400c0c01100c03401000b83c0600d800429040044500f60003403102a8a0400181d40b00d40105045c1d00004104030000f03001ca040e1034020b9030003440b060b00c5500446050907044406555240c1e0180381c221000c04200d8188500c01d4000700021494214a00000c8116403818085400400ac0d5219a200f2445035070f1000f400305004000302000141d46601c1500d00704001400054000305000c00b190540b507800407a0381c0b90800740c0007a80c6040c20950034401111501e8604a82958103090005c0e5076140208200420301c02c480d407104a211000f5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 636791897 1250 636790647 636790663
    0x9080d110f01140114240c2e200904090c081c020601090b011d030f1002091905012c0a03030c03030e0607050a0513030602040e060901150c1103 63
    0x91000b00311582c403074101c1440800f005c0c020224940224003030079440c1d241ca0419042401d44101b280314110348a528020420740c000500001c035801080e40031050502e2807c1100780d40b036080c4540461245018802604984881e10460552240c05480b4500d100a0f00103584a50f00251400502d040541c1010700c03c0007405e6002c80030342e119001224026984124051080c0c00da80e8003126040c2c1d07203a80c104070698246824560005454041e1400d60158440d04280c041602400b40c40e1382030308110b451401c00a48042c0d0f00045500040d41c0202404c10f02c030089811003c017140d03101024108000207010700750545040642e8a481840d070111405040140d1060354002002d000e011a078901c1d0281c5484c10084041c2d0101c2d10b0540764540c0303603102083d4548900440c0e030b10f051900310981c2c4213a82982018501c1b8815a0b00c0ca10003000180440c8010009003407013619180003440c02c5001c01000d80340580100650b03040351402d8602060b04040052035a9071311207800381a825904010034501541 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 636793147 1250 636791897 636791923
    0x5060106051602030a030f020d030216030507060f060905060102160e04060509120712270312031e0603050c03030a0c11010507051b120f060a050c160302010c0f09080d11 74
    0x3500c03241c170f081580100380305030b40070a03540a41d4003100b489a411741c224054083c0b51112580002d4000c000644218010201c10f4032605000901d00d4001d290002190240d8004031101685c0d5414050b89680400074004514502840c0d0200c2d1400d03c2c50004003480042d100030007850703c80c8042030501c807042c0450345140741e1031a440c503195005818400d40754110ba6081c170020507035105034000443e100c0d15440c441a04480314207410f01d4615a20240c1e00810503000070200340c1d0702c101c0b020100c0e0940340c000c0c0c96460040300100b107441c110f0134101e00300541c41c80918442d900c20016542c1301500440904081904a0410900802d5600069405200755a0000c160f1301a9042441d088900c100143d0003069040e2020914112080d01403696070481e034980300d44560250f400915a0303d059080703258090180110a0308018418040009250181d5000c07000360751105809041c499214680d0300842d02c0d5403402040ca00c1c17400958640303d1010a001d83d08012407030072162080e0034108078810b10561 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 636794397 1250 636793147 636793153
    0x2030d09290109061403031c020d0905150903120c0a0c0209010e0406050a020a35040f1202010b0a0501030b0307030c090606080a020c060112140a0c140d0506010605160203 75
    0x19681d410304424401c00d0190703c01161074070703001141e1130180007048000720401a00941c98030302e100d00155044d42e0554041d0720215020401c96446180c50300079600051301c140c00510319054540071030501802c004160441c158028070082e81e444141e050080e03000910b1350000b0780d4070b10101104480c00000400c001e134000130820300006100701d110700aa40720307a005131020802500c8103418042030348a18098140050b40302c0780c0f01c0990300c10844807501021341611158012145d81c94030007030403801c00c5130141c403090911001c250600c02090b1604032035076410700c001c00c8211116030004810109134060281090307510005051030f500c04200355000b42d60810031541a03190340e001c00c14064940c5000b0400010a05404909001440d0095503240c1c4141c1026001c01c0c0c2c01d03c00000d92003000820140c50f03100704003050010151050025602190182c9020f0b141c203403d00c0741d10004003c5001d0924000c11300c0c8520000828004915141510894a8040c0da40d0701910043c0e08003400304000694180 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 636795647 1250 636794397 636794453
    0x1c0803091510080c04060b0f0f0403061b091e0e041104110d060603090b060402030912030a060e010608040c060513030501060801020909010b0c0c0f06270f030d02030d09 74
    0x2842c814108411200c88108031080000241c1c1408190352561294071801403090200d821b141e461803010f040004140b8030f1150a10360f803500c0700c106684c1c245900076035004a507680c2d0705410b40e0060038023001d02003584000c0078107c50b41e0111900c00180d07100d040716a0750aa804a000c00100321171100d0300420082042c0440d401042c0111207691100e400015132524006c40080c0c000d00078003801d0441600071482a07440c1d07a400302800b02075840105071070034600a45400e042101014000b450140301c048400142c801e040c42c802d03201012060b004601800804001c010006413945214415a0710520b000d60f216202103244066501e91a0002421542403000120b02e500f070550140510180c100c0b440d01481e40d880926158505c52014180025000141c0721805418449004a0401006480603203800d400f05000703216000d91041407041c403400d40b4220b41903881c00342c0954016242c102c029108500e01241302a5492080051014455480300b11031804c0c4401a591164181840c4402c0f00382c032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 636796897 1250 636795647 636795661
    0x70b0709050a17030d020705160e0405010f051302010e01031b05070506010609180e190b04051506060d201c1503030507061a0406170c1c08030915 64
    0x6440c09008450003540400000a8000070701e07100040c007004031201451410402d00003000195105010a4a042c03140700b0310044110180c82c00c540040403010008100c900b001e00d05203080d500c4403160701107444d00704030910040e02512214180801c0c0d090801407003020740c42005070080c1002450141c0250008508404440e4004006082d0b451140c0300350746450380c0f21081541d207440385000f0406507500d054010004170350329038811038807240190202d401c0c810440d20055484155400201ca40780c1d40d40c0d0a1008008041158114039080c00206060501e001c8006c10440c0c0146800a94461740300c4001d80b880103030301ea80603000e5804403020107903152842c0034141d01903c5021540f80c40c0c246003103050803121030b0b10401c00c3d0641c0d41c159145458200300d0789860028003022a000c49101d00b804100324400d80e1544159401070175020705404500c4d00c044951405d10800b03000d0f02c0d00800558898018a2454281d40708440e54400303036860700e80e101e0a000a04d400602c0c01c402040c00d203c41c4c10700100d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 636798147 1250 636796897 636796907
    0x30c090d0c14030c03070b03070f020304081e0d0c02060d09060b13020304021503010506030c0f090a06020d090b071a0c0f0a030605101706060d110403080d14130602030606070b07 78
    0x1000015400c075042c41302c54006040d61101c10344175800102d4424070105503c0e0b48268140c020760211481140d0038580c580c07111504080013039448440d40d003503040c04190700b414280403610749841203007089034610240da00071802e0343c840c64940e01422681c403001c0c1000c01000c2c0d80442500000907201b29850700620382804025801a40c0580c0700380404010000c00741041c90440c2c0c161003028104a0458a445917000007640017442084480c5000380180d042c01e441d0a6030501c000e1406500401280701c0000c1d0190005249401c181410041042000c020810030880302040764500c00c0c031001035a8603c0454411406000c2240c500c5600024401c00741c154181c0240003529021904900449145d54058030440c115a01e01c00ca850b0143d000076540b8038000b4054040d903003016001055542c1100d008001d6544590002c84140744045074084403016540b1840e064540750a170756540a050600340d40c6405003d00c04000d021030340010000307200c1d84807441915200d84d030183d800c0c0c810342030104000d42 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 636799397 1250 636798147 636798179
    0x30204022d1e0703120207020a1d01091a0d120504031b051f1e0203090a0f0911070201122c0d0809011a090604060305190501060e0c030c090d0c 63
    0x1a8151618204802d0400303010403035080b50380c16201c44054008400294002c0d401c01c15041c0d900107180b9070002003465000c442407014003810015500700e5070415544800302e4501072240003096140d424000080d4903984080280030340c2001040c8896100e20008170f4240c40383e5080284880e08840036110000803180744c030000d4030b00482c1c0303200c10f003511304100644400041751145c00090040101054080016802c100d44100510503245061004008101803100e594000701030418a180c08121801642c0300324040655070110b410700d003403020780000f0245045400d40362510761360b034680480d0b4401d01400c44540340da01040101f41902c2003082d584d482e0b504019501c0c000c241039500143c02c034a41131003a91609682260041100351100c0c1c1030003070b043e000410240e0820750301c90b808800b040c0200444801403040c8400001c1c2c1c040701d850201d0a41b442d6a0001100e8014030090103054240001540c0e40110700392906a21010440c00189401302c010701c2c06030140765a01c0c40899083c00008481e9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 636800647 1250 636799397 636799417
    0xe0c072f0402030c0d06170d0302030f160c051902180709032406090c0324120302010b0303032d0106021e0307060c030204050f0f0618010c2901090e0601030204022d 72
    0x1488044108e20142c1c160300c03045400c603200c50300400000e03a020102c900c580482a080d0320f881800c80c0143da035400e2030489a110080c0350740d040020301504521349601101d450b903102c10303030f0748696040040015004c01c0060000402d003003020f0f400780d090404480710704624000403040601000340c0e112003001c01080c0340321030b42000a042110345010589182906000c1c1d60901302c080711401c7c81c0c40c8140c4419200e0302c2d000c03401c6540b81c104040c103694080019500038103004042d2507002c41c0588008440026401c1481c0d501c203040f1004001607500030400c08071507030940e40b03070319080d1213258039007802c500c03554900601803498800c1c1c0b005003540c55400f0340282c0300156940c00d0381c80903040410008050071010294403000400400112160032070304943c1582043c100525540b005680e00c80302c484480c0490910001141200303a410751412001e90700600307215604100112801540c0c80c0c03100b005020290180d41c00180070b14003040e5410030901c0068004029107840644107a280200d940b11215032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 636801897 1250 636800647 636800653
    0x30c0318120a09060c210504030807050d090501110d0810080a050c0a0b2b18050a200d0f14121804020c030d0b0a0e0c072f0402030c0d0617 61
    0x85a03036030168020b207104582150720340b400b44440c206c8030840456264408030411206200000001750014042d01140b0b00c2400a46808454000d0080103020035a02046c100164401144810030b4042001c405420407490085040d41e1810104083c1c075820342d204103034500c540380ea244e01f4041c020581000001d01211080402ca42d00c03484101c25004421400c07600e10f42d100c06c84481075a504840314100c800b07640c03011800d010b6400310b810011300303180310641d4250421728000d010000c240a82207862080e0b82c15114080031500c021940742c2c0464040201905034824091091000e82c80307c00045004000c02c81e8048190014403800c1504071803900009400e503500c1544681c41d180c02603641100a00340150704081e0600d18000140170b204129903000141c050021a10802210403144210000c0c20303040d554103801d00d0000085141c02c0c00c0d0303503460240c0c543ca020020300f491030211003100c02114007607200c4c0c4405444088610802e803040507440e1a1a800042c4015260300181c40c2d02914025 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 636803147 1250 636801897 636801899
    0x4111b07050604080d0503150a0605041a070f0b062d01090b040b192c091608060f0103020c070f0806010b190c081c270503030c0318120a09 61
    0x1d001050140f4020130400c1c0d0055480350710640c2c462009580e10202d03004020749034079007500102c0c84800071600231030001400020248031001000340b00049034410310706034501e0070543c4d4640801082030380400600103000e07903002c55500c1d5980f83d1320180e031031114030741160140c449032800c071110700480e0a200e01142d844040010001200c030309940440d445030f0120b524001180500f040f084a030314050360107005030100e460b012009111509146903180e50785904081c54010100820403000409801d00c0a00b0015404c03c80380e882521030360025001c1c0c5020005007580d00044c0c3c0a4042c01b50b103042140305030b81c0e0002c0c000340014006400c6903503140135948545d8907a24044024480c2a90100702c3d14038804140d00300c03078407405407080058000c440a50038965600d036490924205000d400f441c2e0354035044400103482500034042902c2c00160302030444064650b41762074990000400071420b401010000595140d006862526031105610588040c3c060800400c1c20540001600000240810b00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 636804397 1250 636803147 636803149
    0x6090106050616021215070207050f040e0a061d06100303110312010b070f050102130503011a030a020f0a0b0d0903030b0a0311090a0f150302360604111b0705 69
    0x81241c403444200401000607072044e4081c013001d0403925180d5060341c0f15585155410f0310424032094015045c56028250700c030301c2d1400300b00c20030f850300d90304601c00c40ca405100340b5440700000d80015041c1d80160f0104581e55880e24642c1c6408035540d0a42e424050542002000d02d0344500741c2094034440c1d00d0b10000c100c01031000a980c2d002c1c220710200c1c02d00a0ba40180302c2468600c3c0a848480e2180c0d44194051035255210b9080e41c205003030354406080440d8050000f85000e0180c90030081943d00d40c602c00041400000e540c84180c120081c2c001d900d880a0026291604008400075004002525988106020860006084107502a0000307450410b000000b4074004012004580d005091a15030407034000401008074006085044070030b80d10010344600c5c0000d070140b10381031004403440347c1d6480d2550050100d920750348082e811009080f640d001c10190511401c0000c140c0039580540c40796990784000c10001c4c0081003450695440224113101c8081c5c0001c3c5286c0403540240654550f03503583e00c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 636805647 1250 636804397 636804409
    0xf0201110705062d041e08040311010f26131e110f01091503061a040602070b0c1e0102040819120905060307030c020703120306030506070206090d0e010c140609010605 73
    0x195401300d10b40c0c90400480c3c086051501d88481c0310340c88000f008060100c0f55241c012503031003079000311188221512005115038004504501681da1814040500240c50322000c0705038040c1e000141824418a000c02e120383c3c00c40c100c158240b036000c02803041c01c3d0801850040c2c800103000c000c07281e40e03800003010708090610303c0c040300c546201078440c3c21030541007040d14008107110810445c10141d49200c001104103440414082c041e6043c00e9580c0d03500c1c02d00c540282003401d181c00401d200f1800b0054080a030900294001d0600c0480d215280c0d44000c1060309030180c42603034840c15061091510489034007500c060f41d00402c52140364442800901d8142c15100c0081c103100781a4080b00501c00210502d01a0b00308801b100150320655035466100d5480a02d2a08c000c50403c002940d10728060040090130400709401c401d440c0001d028030300d420b6050545c0c4803036103d00001000301640f0f43d49200c0e4000c190360311240e60712152848000c07400119040d070703414003110504050740c24074100003400c0c00d180f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 636806897 1250 636805647 636805711
    0x90f010b061806090307030b0105010e091017070e01090b010e03060403020a080f0d020c01020705061e06060d1103090c01080601031e050903040e09011a090112030f020111070506 78
    0x5003145060030380c0c0690701842840040760b1250424402c201c01e08481ea41840400051481281000032a505100004100d80c3c021520b0a005015000500c824142c0007151401155180980c1e000d201f02c0a004481c2070900c2e60b80150046032800c2d0000c90000c0198100d460403680c280c0e5040821445d000c10566110015a00540540c100c102c0103004034440000030001812203440143c80c154906041c2001c90b80585604032003651f01107020f4040010a019039078001100c91026003001c01e08041c94000980b010b041f03944107000019290169552a4100030500301ca002e6005459241c20f001c0e80740c80b242d00400d41ca000920420010302158068442c10281da140402449010400590000010031002e094003d07141700c01c1c0000540482d208903144d114141c10000800d24400984022401603542500c1c28410340d038410050000394101e1800c05100d58152520400c0045507035010303401000c20307044840700100d0010720002400800188207012341940c40c02c0c00e89892244013511407207d50 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 636808147 1250 636806897 636806899
    0xa081b0d03080f0c1c0f0501050303030408030f0402030726010c08100315060e0709031a0402010e0f01030908040f03030822020d080f040e06030f2b0e030d08090f010b 73
    0x2103020071000f18070b40e1542640008491a464038103074030345080d84440c650400c03507010000d032540782e0488440b00901a603070040809400a40c02d43c10140c1e81c006450000400c10642580c500000406555080280d00010300c0078921083d156007001081c1802d26a20ba180001650700349204c0462180c403030358510b0b1061040b843c5807410141541c3d640728419008401c0103554948450000c14a0300004c2156070041ba05601e401c4051851480c048441c640c000c00501c00b203420001c00c01c00940d81010079949000012038000c40c446034441b006800030808014040c00612000c9000724103025600300145c1500d019444030780f410355a9040040e5880c0b520848240e112100741c50030401810088c240700d408a01c00d042c902c1c00d02903001d00c207c000360840c0d48040b036001c41d5042070021506051010104650101c0c01a024000c8072200c2c8127042c44068800c880c81038401c0042e01c0c0d03003034400d545e00c0f8029a40182078900007040d443e00145400000e071410082405000c40302210150b05120b103240e420f00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 636809397 1250 636808147 636808157
    0x40908270f011b0b0c0a17010338040501020c0106050a0803041a0f0a05040302040c0f140309030d09080405030c121515181506040803040b0906090a081b0d03 69
    0x1804000454246005030302480c0f08040d40c105200c0059681e0103824031411a0122031078640c45a12001042503141c40300100c0d004002c01c00502c0400d0168038640c52141c0d4403428182140c1c880c4850301160a80c090b07120141c80303800c2042c4002c0000c107400403d411000b03403009011858503441000f2501d115031143c980a5401000100224002c6505200c0942d510300001070400710044a858002d47c403030307907407500001e600240900440c5064814400c5201c40c0349012695412401409000b03041d41c0101c2c1d984000f4040000380c1018801c2080345c00741c403800e0205010000442c40e010803141c05c61302076030b442800b800550551600340b10a424660044210080158040b54082a030f031000001c4e1000e808080107181034a4591100091001d00112014a48819140500000181c49031040015101d840100820054288000240c5d8140c45e01085400d96840f0483c1c00a41c0910a0718103454001c0704c0b82800040d0450046103c24500c3e0086048110581c031031010000c002c0311202001303020071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 636810647 1250 636809397 636809419
    0x60e09030c1e2d06011a03063604050105090118030e27070e011e08060303040e190f020a08010303030c020f101a0301060e01210204090827 61
    0x7142010241e9807194442054400c0f0704601a00d040c600e003101c040b1589280080901514501820001c040c014082c510301d00014540c45000c40b2030360b110203090f152042e94542000502481d4580341c4000c245003042c56189010851800301d00203240458056450354a41030004080c014180504500c0803541c1c40c010306400784980c3c06507060810400027541040400c410411034100380000c90801445040b83c091084ca00031000520303204141c00c48904014551025003078403c2821040390180e065801e11003c541d80310808a8a54019a4003441e03862688005018003d00300d1201d40045001451091108901c0705840200b0380c4208040d40740051001001000482c3c0310350300510210f0040d1066a0982c940500900d10301045081403000c035a6444c00518003260482e90f0719200c1c03900c143d000740b28043c9011030000341480148180c504402c0c180d040d61380c0c0314486180302410f1940c001c00c1000b800c500e504049269410210981804100c80c07600000402c40041d0340282d10a0021b01c001000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 636811897 1250 636810647 636810673
    0x606080703030507140f0303132001050a1101110f121003020f0f010201020d0c0909200f0f0408160501120b030c01030f0b04090b062815050913060e09030c 68
    0x30b020302c2001105d90260440d05403510000b8030013140110520f400505000e80182070064080e0f6101c5d00b0b40d04000a04c014141450340c01c9416500d1901d00c504101880c14014805540502980030030301d8000c000c00515184e540306541c0107418144050300c0310031145d542d09055042c45420500001e948503620305450702c003d1900c10400c402800041c8005820048541c0c103802c259100c24000d070340441c500034402d01c014099441444d90103022200e840c9905801754042d14000c1c824070070000c0c9602d400003080046c06120204543c01043d21380d040301c0518207080d0000c6049031a0303000c3c1e030340050b0481040e00c50207111f9005260592030000c002c0c10340c45451a0041d8010888600b00880840c1c407402d035001580e41c3c61140d40303541030146640e0781840c500401003280304120600c003400211400c0e80c6115003880080c0281054038481c036190034101c03445c14004e44490180141d400c0c1c0c03140c044071038000c028003d80c1040f0122030345003184142c140c44805565441e03028804c03000c41b90303920140b003508034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 636813147 1250 636811897 636811913
    0xc040207060608031b0d0507230c061b0d09080c0f01022a03010e06090303010e0c0708072301021c021806030f07020609030a1b0213020d06030606080703030507 70
    0x80d0354401d4400040c180d5540744440c2c00d40d00580c542100c2e0803409002c850081d4400c2c0011003034081207160a602d05189030b9607040c4200c03440c24050041d0041c20300700b0400c5a0b001c00c480140c1c01c0d001042c441d1542d05045108807802c21290b2030942c0c03400750450800000307000c0e2012905903070028014007108140789050022652640103003a04500c80d40c0e1540902c41055240040810340c03140948031801c0f510020301d42034607800c200c200e0340c6502280800008810102c00c0d02d0540d20340d0301c100c8420792208000030b54940101030002d0000302e40001c190040143c2482c0071101b004644403039445041550703030254202d00a11101c0b034034008908a5541501059030b004001c80300502c521070406092141c0418003e1700221081c4d40604800014031240c07540403c1070740d0307000056070020762034100c0085000701082d09201c001e40d0340071465982442195510403c40c0f0003865103107011502c4505003400140584100e11056401500d00a404101118003059810035039030141c4507586800d10710ba4074051 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 636814397 1250 636813147 636813157
    0x1009030b040c17010b0411091c080c0111180a0312030b0109080a03020a0203070b031302010305040809030a06061404050c0f090307120f03030501270f020c01050c0a09080f0c0402 78
    0x5040c600002c0201d028103000040039000308060000150b5010a003051000326044481381da1141d103028440540e15694400b42107aa148244041e030840300e800e844c2c404100c0c01001303d04502d95003032003483c0c1d980c0e0800b40302a007a8210486400c001e0340c03500c50248010000203001c083c200d0f01107040819030a50280d048220b03e000c0602d401070300107641c2c00d107090620342c210340c0840050f0080e030401c81c15031a080225070060040d605210749903080071600303100400c4e010312009062545410001d01070052290546000600c06002d44c2c125a056180c1080184068044d030000708119854140c2a401c0c00c0c0300e00c9104100c0040038514290005c2c44035030590700401511980f5111700d075400318051110070441440709116100c050958585481c0203415204142c111414455022010084006c02c034850740038041006840010600524690b89000c2c2c802d40c0c00d80455582488180503a032107500c40100000c20030b6554600700703161503c0c20b00c3c1d02d505081c180d8030300307684c807021226031503140543c0100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 636815647 1250 636814397 636814403
    0x20a140705031501090507090f05010c020130050112030e0d0804030206070803060423040f0303060f1205010b060408070308031314010e070e0c0f0f040e0c0c0c1009030b04 75
    0x103a0034940d40c400091401e26400400c200c049003210040020a405024550300312001c0d0420303049030350500c40038800c5c4154a1203158100300c03502201c407040d640200000c0d42d03294100c200c80c076110301d821818002d24041d00d581142819140000004085801c0205090316a5050743c450510340c4224080060018140d80151800e031000c210000060b60ba4400505481d403042c00b4903622450102c0c01c01c01100c0caa868803901d0396002c20b01502c200401c001805034001d9010301080c00241071814100c001700700a401144005410020208408034008481060305108400a0080b41000c07c02d0001600991080400340d90100b0300038070009891802a40d804002245150128542901d0305158000b66060800071a55908a029592002441480302500c41c0b410f24085078205a08944003502c40d15005a84000307010416041c5c403250101254001c2210000c0c030784070340c20920304103e4107600c4080f12904611900011041c9030410500c0c407210000241c07501450185161140b00c103141c0010300403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 636816897 1250 636815647 636815653
    0x150703200f0f0a090303110c010503040b070216060225140d0314030403090e1f05010e0d200909010507050909060d0b01080304061d0a0501270b09130c020a14 69
    0x410400750b42e060140400e0585541d615003054034600740900301118460725140035800900c9051040c0c0d030403400300d030381150b84104d005040340d0741d040b8101d080c5049034044c01d100c080c0d00300001170703a60303030007d03640c908480401c0180903c0d40b00e001515414041c039200b40810b050182503035080e40d20f02448e80b903c042c0c0c0681003080d004101020040d000347e2080368110f01061030350905200e09002c81c02346607402804404030b414050350680384a50032403084d101d1681008200440040a40c441c450306035000d55100301c40c0d900300b001120450460070010801c1c41c0c0201448400243c0840c0c1c1405a20f0098503181c640c589006500800d1107145d0303500030308164110030320121480014079915410350090252001541d159418414001c2a03c9500d2018a40564403404e84075030958880c1c1005003111400d007009000c242c100700e41180c956460b001104200d88003100d001489803607c80c000c140d01d03601203031480c424055110102085078400f401c0040140c0c0158010300010f440498524241e4140c1c10403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 636818147 1250 636816897 636816907
    0x1d0604050d0e130f022a100b01020f120a030b010906080103021c02030d09081b01170a061703090a091b0c080c24070314040611040b030108150703200f 66
    0x700d40c090b42c0c0369504084c40258000303000c0c80302da0304481002d044c20300c050107043c00c941c20b0107041e81d58628017001d80c901c10540d9441e2110304c6a00802c5100b80180d2140d040c0c1c2e4034500c0b03c13100b5101c2074110f580031a0200381000900040740d0f104503150000d940403511004140d900350340901c0303101c0410303542d9a00185856038444002da41d040200b04001c40690717403100c01c40b03420140c0e00d40c1000320325813030f01c05070051194001c0d10070ba0304590280350f41d420000665070942e46004124001e004c80d540019403081d6004a050600400800240904079041d50b0a08100d0b41d1602580c0c2211072a0001c01e103840c00c1c003442c074080e581c4207064503034000d409840580d06040032007031502d05243e4042c001d482c2c01040035854507000110f0740c104640c0315406090401c0304403e0b040513100102c000400040140355250964030310030340041c00360f8011704201c4030201d49035a11446007544d03e28a803968116204418400112101e100c0d0058646801c072007000c20100c154032004000098000a1403004010420300c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 636819397 1250 636818147 636818179
    0x50309030307082a1809092e1b0e0307030b06010c050a0503040b04140301060302010c1b03170c060a1a0402070302031905190e0306070f170702011d0604050d0e 70
    0x141e407410ba1040200011713960b903d281401030482101c008840d006480384020000024804282c0c083d11004440072402c16440c100e00014041000f00d81071881c1910380b04941c0448600d0000b8a0009004c0c0c2c1c03240900d0041034010503542c0c540901c401462010942c001131610f5225220003081c00e44680d046814440a0f6603500303007107811130b401000d03401001080c10410b000503d0b01500c40f046007a0b002300719581c15900006d0a10300051409407055012113082d0b010701c00c600302c0c000010364014031008202008006401140c1d80140d014204901c00c000c0891407420462042c56109841300c42622145179501c0c05001c060340000c4400e8041d03000900030454000f142400380c0c42841005e564071071350303403011032343e02840189000d85c000c040100d480900052501e00040f2190410094100001840407545085035490100140303000d059841c51300780001e640e015040580c6843c0c4100ba18407020b804100081d546580c2150068601e90041e5486119030f80110080901004094180114103500301 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 636820647 1250 636819397 636819451
    0x18181510020c0303180d0609030203030a15030c0614070f0c050f03010b0a03110301090516091508063402340b0c0c030607020a030e101d0f040c0207051005030903030708 74
    0x88d01c2640941c200000700288000c2da88944981101a212282141c0382540c40b410036407102c1e40030303080c1070008081c1d0402c1d100300d0100c20340341c1ca19072000011140241926140032010070b907105890180c0d9a00404d06114a8180100807400700c1c00340c0002a814510f89800c5c2e0401c50281d01720b9015541d4030744200204174180112446515030380b00b0246000d14003c0080101d40d008000700c052005041d01c24051a5030105115801050000e0080c41ea20070b406554504c0020300e10140300d00340e040300d0f04504010f0300410350074800d0382440440d000303c50b04400d15412940b15500e01010303600c0614400d209020056016000201100c0c0c102e501009062021a00d00902981d000c00542d05c41c00c1c5400405902c101c400c101004203841c4040c1c0302804100207000d2541e80f65000b04607281e442e084250646442c031040e82e407a84020014002004000c101944558150085034008c00051604c0f001c1680280c00301c0b4092004071b4019032956851403030807690200e0140806080407450303440380345e40719440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 636821897 1250 636820647 636820661
    0x506030a0c180303030e0c030d0f03020f090402040e250215220f06061d01090b0f19180525031b05030109051b18181510020c0303180d06 60
    0x303510001b4200c00000c0c00185001100707140180329512101b004d480d101c0d8800300445100b94141809a1141c000d45021282c2d4002ea80c140c0b600280701190002e984000602d00901038500282c10080840002d0494696440d40f40c0501c005070b480009030580c401121034466500080742101c00c042c0721404c1c4000481c000f60507200b9141c00a000d41000c003400981d01c2020000e16000621601910103400d1601c10000144121024143d03128000c02c03164443c140550b440c200d0061140c0c0c80b000c0c4019840c045150180140514201e203440b80d0800b508aa00c9513a0066140b12070b402c0050544220a09000401085800070991a0410075540104407621f124201107a82c407405d480c4d60502c0341400845030020065680103400300e0070b85003103190303400845103140b046411084250703481d00f0210390354201e00c80c840400c3d0398102007004400b801002c40030642c803204407a0141d000c002401c00304d9130f4801001a590741500104207400542a16070050f00d02c0c1100601b001100e110952101c400301c42131 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 636823147 1250 636821897 636821903
    0xe151201023007020606060705010e07150306080f030f03090f15220b0414070e0a060e07020303151e030f0d0f0c15020a030b1509090a02040506030a0c1803 68
    0x4001c446002ca1045011854110601805900ca00d441c2080d030080d13880c800074000b18040e4600164903403d1201c2900060b540906606c215421142d58040d0035010360406902d100000c2d1034001c011039001c4020520f0010484104015802c0980100c0c0042c0301d6400940f0301182c0b8858a500c0300c081a5051224065103990000040242e1500303080746500c0420804d500f5002c000071800000004050074851508542c10180008010a01e4140310740303011480d030000294040c5100420035200f50310307009941a110285c003181c17031545644206982d2800184d41c404400d4042c00c0c0c9001141c00c0c00306a0b01c0e03158841c04881420281c45402290901b00c040042d00440e40000745c8041125812085a032407515003440c01081c040001d486404042c1811403020003e29000100808064030a40103c03009803c010600c0c1940d00112841080c01c0d8850300e1140e002d0055a0b002460302d81080c800d66084030300c0500805d25564981c2a5080109080710580307040c081d40c1c004010030851500b0980c0042c1d48 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 636824397 1250 636823147 636823177
    0x9090a02070605060a0501210227040c0f020a060b0402070b040b0f0907140105030a090b090a06060e0105011727010b0103060e041112151e100e15120102 67
    0xa01e0600380b0540328000d042d41e02801740d1090811880c2d0380440c99612000050460301c81400c10100c001c40a84a03014200064080601091600096200c030b48800c2c000c08540810465401540940b0301c0300b4020003040c0560000c0f004036012465035081f400707184e10300400040c80c007c0c2031f603103c0d800301c1c0064034252035010141042181256210050f590010200b00c0200300300ea14103405140842c03a001107079810401e01001084940c201900180005940301d04200c0350751508900080d5688c050110544415040100000f5103558200565050310410307500d9079032605031144909002c1d41c020303102a40303240110447c3e4112180d40d6400112884c1d03078000102d1034580080c0014141d8455400c0b090088809409100c00103442c410300801e48041900c44040f845001c581541c02e0141d00040809224090020444a90f03050242d104800e0340d41c1e4401256078841841c20f504d00080e501580d000c20300b513000810508152200100003000004102c5186151008106402d80c2c1089000e0a4940 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 636825647 1250 636824397 636824407
    0xe0c040510020606030712061413150506060301030f030e130f11130504090503040b120406110c0d2304140102012f0703050d0212040c050301111e09090a02 68
    0x12801c180440041c00d100d10081c04181802000280c41d1441031081e100a9080c040305a02045000d0304440b400e40302944060f0341514014030f00089088000130101d0b01001c074030f1040c88078401c3c20b12900707008100c058041410741e801c566403013200201e002c2c2c1c00d409008155100c2d800707541d90089112184154968081860f201307a40e2007a0603581e01042800d0000c00a00c844280b0180c81085041141c0d011900819050824140705040d44115000340e6988840054403082c0c00c1c1f24510b0300790040c1d218100c00c02240c1059181c1c014030340101c010b900c146800103581c1d01403440c40303803454a090010048200d50b003030754000052107135544658801c001050070b80d8900c03422581c0a01c650f04004901300360f4900c07983c1c1300010241041c104040c0c4c1c0c507580b50002c24a5010f25109505490303050111400440d9110b115488646840c80304a4080300c2201c1c848102140d1414103004294403840301c1500142000c8102007480c90f00ca0b404d80003095068000d103e2450507556158000340141c51850300181e0711 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 636826897 1250 636825647 636825649
    0x2030d1205010602070501050706020f1207050301030c0e06100f030e031b070909030c0f03030b060403080d050703110a031d16061107030201050301050409030903050132010302180903040e0c0405 85
    0x601d60507800340007035401210040000766004011500400d03405200103949411120304040d07640601403000541c400d01004000480c4c0c2c2010081d410f0341e0041017a401884d0750354a201761242d80455240780c110041889000c81a0700442c050101c0142c1420b01040032250100082d1a641020311155108003d01c5031030740c40080144807200c040d0000300d005000c0c0c03007026200500711a007800c0004010119500504c0b0034544290302407500010000c00c0141e5543c0d07641003402d21904000800c100d120302e040301255000307009219541c82071000710307107207030811840c060164000c0401c5049005402c0e136610303a401d2120380030f12078210505100b480b400402d9090400003410515032042d007540d90b6002036000d00160380c120098904550088802090301c0485182c21a69031400d0b9000500d15824075035404c8031501050305092419180008803040310520789031411a4080070f10002e50040000100e8280c6541000744031a405540001124600b030390341c201850b01e500c2d01f2a840b41513800007280c14025 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 636828147 1250 636826897 636826901
    0x20d1e0c0905060c070e01030303020d15030b06060f0904090c0f060f200a050a061a0f06040608040201170403020a0b0f1b0d06081c090803030103030207140d02030d12 73
    0xa914420004024100364004080c1250a45000782441140f02241d11141510200081e6004c0d1800701d000c0c1d03001d5696031a0240281d08161009440117061201c1c08501d1803078010803d040300d4108482d074100751501c2c01441015400815a11407080e000c2001503d15182e0b03000300000e613403080d030316190344601e00000070954076401d4009208008006100b060510f901c013508485400a02851004040000c11218134244c0003030f00c02440350107818101c0d01480711540c401060001c0480300c01d00110380e800f04110400c1000129903a204c4003d02050180381e05c1103014940c40352041c1011080075083c1c0540300032001048a045006034031045070181008201030442e500b1400c1e0550740369060030820380c08880e102488400c400c0d18030000c110340c0b0781045d6981040009110389000e440e9409450300c400e11031918010801c401003241c6003c0095103000001c100c80c1202d8240c2e02030020103007002c541590822045115652191440078001e02598081c0300850301e010881e201c00c40401602d61030001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 636829397 1250 636828147 636828191
    0x110a080313050c031c032a020709061406160f02130509120c0a02040509241014010f0e0109090f05330f040e010e0a14011503030e03010b04020d 63
    0x202030b821000b25683c010508241d81203107503645c0d08021070100c540c0580c1a680c410b4011210000c21003150303901202c0f54010070100e09964001e0414040d498941d68401d001004010603540c010204214017038000e4a10307880003110038440c1a441c400804160001099184446082d008640d03949080c015803440c108410b0440b511251096030030603064070212a1959015040640074a131a10005500400207104d803901c2c981c40e01007a58481c070f8404403c01e40da10030850b08400003815500002c00d0340500d08282d9180781005035a5516848641141201c42e0200c41469074103000c500d10340811141c010b402508125022010700007a04d14042480705000d03003c1000140c41c0b019407440d41d58403814403c4101c24000c40590700420074500f1500454000c0425010190fa254030309400b0040060011501103c01030059080c0042d807400d02c0c0020b030072208510901c2400808511080000032b018840c44d1701c0d080380090000804941450105040c1d0781b000240503100d030303603070080c444540702d0101e071702a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 636830647 1250 636829397 636829399
    0x1060f090e060c040302130608030c0318030c0627130c021005090601060c03050f0304050a020a0b04061d19080c01120b100e0a030c1e08060610110a080313050c 70
    0x159082c003c000c0300c036500c0381c2d000280c0078010ba43d145200c80c100399004a80103041b00c0040701e640d48040c82c14561242c100d01c0b482000c1e8a49042007500318a00011100c55206001b03000f61b10f0204a20b0035400d907801c40031480d080316440440c070515640c0c1d844030710403141445080045a00303e050701d4000d00300441e050084443c1c2d4500f03000c3c080c2d0520300090f094103441c107074209404c0b003000b60b05059400e4004c004c8841f0b0314002c00010041005030102e0440c4503a4425038000510079162606286c1c01d02a500910b800501c4250510050340800a40307448000e07806007002400800c04110095001e4240e0001150790340300041c00900741d6030251880d1000748085400300500740002c40021001040c000300c9104000791101d140e0041c3c0e8070501810000c0d076100b000c10764220366500d030012440b4030002d01c41c18680855680051b85440101da00303442028028100c40c541440280142c0700c2c03d4842d01c180c003092090108000c00a16488004c601607100d07104141441300e00743c81c0503460b0026910300700d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 636831897 1250 636830647 636830653
    0xc030507060e03190b09010612140d170403080727080c01030b030a0b0627040201020c0a0e160519031b1704081e03040311150105030307060e030c01060f090e 69
    0x714130b05240c0c04411460803640400d40001c01d40300d803582507001d041a0b41000d00030b40f07140d0fa8070314100510450b45184a1300d410041e26900794441c1410380e44900440c0c1941600703042c4000040009103d034005c1503004d022810203034043d00100321010000d0820444034030720100d41c154144000c00041001c1200f41009180c280005201c1c4000b00e5114106000002c1106040401080a0350758400311807901801d54842016100f0000c0c680385400300040d40d050b80035010700c840d0003e042c10951041c83c2a5184019561001e4440780340880031a046c541413001080014410409890011200000005a00c2e0303400306c0c590310840c01d20103180503403c0f1054140100400508464184000700c2907205810100d6551501107818041402100810081d900d0f20400020801050340001d0010b07248007002080b11f0031900716038000e5000d1503081c003071241c0c0750b40140198000240550011241c00c001c0304184c906000e401c1100d242500c00d40d030410103860600c1c06092010000c9407003188121820768000f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 636833147 1250 636831897 636831913
    0x2032d0601020d2d0215010f030b0606030a0902090a060f1d0708150612012903010b0a020304050a030b061009230303120a05160503190c0c0c030507060e03 68
    0x40d540f6072020102c4014001c2802e03c034000740001d0440c038220407840d132819040c41c1441520094682c502641d0440c41d9041c031900110705812040200d400341ca0348002d070b10f542ca0701d0301b000f00043d54000412000c45651104091001030f04c0c0d100e40e8a0007210070140111720705060420742d6000d0300c41c0c3e230000c50051070001c11401042c00b05c08100d5400400c01d0030301c9801070310b482c010707a0060ba18507008960003000002e80038420224003034985040b00e00600c0410408c503076500c05000c0144101d030a42c03510450901c01840718540800040c0103511182c01181d15056641e030216a00301140e62064407510854410800746040030301030782c84114013038a40092400e0500c8602051501c0320381017500210b0003a00754440c6501e0400440c0c41c1b510030064059014030381003211102030841218482c1040c2e011580f2120121302a1054900916166403074261528225117400002d154114400042161080c14030020428071000900558001c40142246506251001e0071041c003414015019512101b5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 636834397 1250 636833147 636833149
    0x1e14040b150913052a0d061805070309050c090604060509091005062d0a09180c0b09010905060d200a08010f08150c0409020f120601080705070f08070602032d06 70
    0x1003213505001c146201d03001e02e17444040c051000c41c0030742c811441c521482d11102054000314000d08107030340d92041c00240704076510014200c041e518000e07002000c85d40502c821060700d1804003459030344004081c00000f0241d03500c0000544d14001540d02c400641c1100c06451010322541c090309510840c00c2d01c0e00030104100a06d40350b03080000f0480c9a400107040c1e071842400341d4543c094440200416501171100940d50307840380c030005c4d07107008003140c2e1000041c1c400140d095030302e030079948071350016105d81840030f00c0c05052000a0f0b0121250441d2690344070b0b140c10024400c22020107400c5403a2000da5190f400403500a0840ca074107030450360001594102c1000100d0700002d803000d095809503000c01054031f81c240300c45014019078101c084840c5c0042000e40e009001c56003c0e0020301c43c121105281600d036600151403440c000d58803000007a0b030400900001c28a503048075981c00380304802007450240103496010032a0016580036010000c7c40841c000c4000d8080070701c508044210900c0801030a00c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 636835647 1250 636834397 636834421
    0xf05100509130807021c05010b010210051611010905120418020708040909030c140d030f020306092e0b0403060509010606020d110a05030d05010f1e14040b15091305 72
    0x10310003e00c0030100050b000119100c3c0781c0481050050008410031010541c0342c224040c0140000050040c820a0420440380d1103074010305008001c1100500c191080307e80086407a0740100c03d003103902e9034840b0605070010f80204150807484102e40c0c44140c5686c2000d2200405141046a0114460050003003901084c4180c04482c00c03562145000184d500c8546807e0b5603283c2c404001500720900904103800303030180410180c0740c90342a681c0801c50500f07480350040480c0410348803e90481d2103074000640c0c140400040041c5070410102e018a011904a42c8071511111500808060034021808004000403070041c03541000485009026079810844000d6403809120101010481d52180f0030b00510014016403020f143c20030290380d80d070301501400e040070340b0080c41865480d030303000000010b055a036090b035a0348100f10b000c1ea075429507141648000e104018901c681d58016a25a000e03025550b48840b0410901d12442c0704d241c0320313003407101003100c120420704602d04d80c24281410000c01c11001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 636836897 1250 636835647 636835681
    0x112021201051003150806161b030807050d110a030b1c0b0c090307121a1b130b0a021f020708030c0708090607030503010e060109060210050601050c010f05100509 71
    0x6440711821075601c00070480c051718100d0020180116400e1000c035116201080b142e201e01d0080c1e4405a040e48108000c54521241201d013402242c00c0540403000207102d00d24860300b1031134074604141841000c668040c1200c4600c1b6400c1d000319000034401091980500400c80015000c035198101c0c2d03c0517104081e18084071000080c4462149800540d209403102d098400000020f02160810358482c500210600e001704000e4409a03030b0010103c00c000094038100d80704541442c00d0010003000d002d0718a1642d045496400e05401c80d004012a80030f83c9800036040c03c140035401045080000500c0c0f96807012065030f0200c16071b00402a2102103a0184122900018181d50080c0d0b03a502e0381c14000a0360007141c007942c0d804000000c407030061542c42400f0f1810384290b410420744c036840300310055906550900c60040543c000199040b901d000550009511490604000d0310700807a0266860031510401c60708586103607100284040c40d2a04a500405000203070380070015402c0c1450306078032802d81 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 636838147 1250 636836897 636836899
    0x20310051e04020325090615140708040302121c032c0a06020406051206010201060e06090a150603150b090307050d08091c03120c0e04090503070506040b06011202120105 74
    0xd01000c40d08549040125148220840502d11103c84943c440c40558920500c41d40c2c200c54181240492040d16460b004484100c5940340c400480d009e254408070507400110003503030806001e00000002d40c8414002100300b203502c90180403010543c005c00c0d100061b4400c01d004c20145080c0c1824008045801e8102901843d039030f42c041e904012500c01860a1703031036140100707501d002240000c0d1194204028000b40300b440c141350004ca9407000012400c07076140d0b100701030701601c400c0045205402d003c5401c9401100c1b10102207907101d0080c00c00942902140d110b800001c0d41c03651401c407040030982082018242e11919189400f00d900e000a5440180c2e000f49813041200ea07501104201030340040b10410702000d4041b41040300f0b4014085d000b201d07083c90583c00f00f010b00076240c060006500c81c0000d14500e940340c410340110f40d50180002800048000c0b25240310400110000c01c0e003c200240c4110701c51b0074203401a250040004050100ca030420641e00d90062040e503000540e2a580309040d608 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 636839397 1250 636838147 636838201
    0x50a09050c150d0e0607300f021902100b03010501031a10321009140112090c0503190506010306020d02041206060f050f03030301090c030e1902031005 66
    0x1600c104666684140304074112028901852000300020104045c1d00c29505902c0d4200d020444000d00e511001250107030b940200c61607034000aa031200340d88400101d4980c048014140780d0345a840c0101b0703804402401c0d000d64041300c24524905001d0003220708840c000d4000388410b500d03540d43c117180c1c2070180c1c004024003d840000a040c1c0400b010300b90009111484401c00108203041b240d0003c040700865200f0300d4502180d4444a50400c174411161422260b5030b0800785910300f4004a032441c01010b1101d04000a04c400d02042d03d080b03015042c01113004540780007115140c901010b28141e002c4400c5500c00d22031000705d170003040010442070304407078110300c1c00740c0c0c0c0d2042e200055000b441a500003100041d0762800442c1070043c40c0d8824020790b0801c041c1c0460154881003000302403c8400c061aa06600c00c00041c040e0542da50421014456581004103844466428042c148005258502001e10024000b1400d503c0c0402800d642a11104020000c80c10301c4e5080d03054000e01041540c4446c0c07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 636840647 1250 636839397 636839419
    0x9020906130902090f01031b14010e01090f090509010f062318040b0703051506090d05100e0d080f070f031a10030c02070b0c0a1b0b0a0302030a050a09050c 68
    0xe0003604881c2801d43d00401140c0c07117141c001d80048454400b0b00080d10002c5607000682000d856440c000b01c02e8642d40b0904a0303200c41c041004440301040b0b14011030401181c0b05000846110030000d01e4090024400082003138a800c000560840391904c1a00d0707c0d00303081000410121414602c03d000c000c4a0410f17200c19041442c020403050400b00e04c010460b000074204100511054000c020b00445c001d035418045038441c0d502010748461106042c2d03500507801c0103020024030702420011000c500c10700c26a5420703000013070380c4c108680482441002540000c00000c090a500113007240d413180702c5440412450800c40002059504045401001d0507075030591941d030350031000714a0380098001800d94403080c43c3d500c0b006000c1c0c400000140003502c00c3c7c0c4008204642980180c8416a040324006c0c0059151070702c50810001d00b0000780d5030100d20140010607481419030003009100350a49000d0b0380c900f0302035404000c0740c900071708a00c10689048030300d000044d00400d180c5028082203803512000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 636841897 1250 636840647 636840679
    0x7030c0b031f09090b070305060603071206090203151c110625082d0723030a0215010605090a180b0a090b1c05120a032403060e0109020906 61
    0x29260000829442d10585400007900303003d035402000405101e5000f50640d611208026016070703505a54040c0d0100090001802d89441400741100f10001c00001207603c2d650b681d04803089a2041d2100210b591890300b81040504060141c411107a8005155071050702250300c40950200e2000e00380ca205000008944803091100c1e501150108055052500503050310701e000031860b44401c0040410b03800715444000e07000c40c1108113580c035140300c540c040d1802c0003030340e1404545072110400e403007034107030a03002e5410014040014158004e013940040138011994000b031554108160300c10001c20104210740c0c00c0d20389443e0b0400e012038201582d00c035403882e0284000000b81c01c46d0501242c02113407015002440944a404c0000d040300c003515035011043c1604e102072140c2d0251540030382581e0080014041403049800100380903074180c079002800251030611304907a402e0b10140701040c0c114510082c030a10105104640100c48240000c1202515941c08a116900c009291a104803564600f56500d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 636843147 1250 636841897 636841921
    0x50f0301140d0204020d0b0901080d1b020a0b0d0608070f120314160803150904080a0f020c060a02060708090115121a04030804060e060f0103081e03180f07030c0b03 72
    0x2c40e43d40107000359220801d215291004120304074561340b08a10f50700002951041c00f09000030a1003c50340d0b0b40c0d01d00510540e00d100e54040711b0b1412a00300350103c10026410080380040e0001101240000c2442882e0910170307072070310780280c1014400e803628907420810340803401400042950303d030800c4466010601c0b005c0846026903110080e08030801ea075103100300901c07030004501c5202030340601030603900f0700c400b800425202190018070f159000c01c1f64003101405000589a08241881101c09484001e400310781c59422440e0b41c07e01591185041c07240c02078100468030b91082c40712000300815135846050080e14030061096024512941c00d110080c404c81e00032820851600c001d07035002508081c81e006000c0903044a055a00510b480a040342510700400d20b03a01400c07040c010100180d0035134032000002d034807041204202c101046280b800c1c00024401451190441508810310b001264200d107080807041c2d258040310ba00060400c1c40080c611f5040306040e1208241c5182e1265500c80032100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 636844397 1250 636843147 636843169
    0x90503030a0e150304032001090501140103060e06040503030c09040603061803090e0c04090c030b0d031d01140a0e130e01090201032304030f0504030b0f04060c050f030114 75
    0xa05800009069070285400c840140080c06054404003080684102c001015000946008000590007280081210540c0f1510081074007030800000f032101c4684c0d103040c01c450342d8068010745c417610030004209001042c0f04542488004030046d100b245000e03507840d6100c0c80000c0081040c01c00100d030034042600c50b50301103806164442400c0160301e10020815002e0800b00c041100014103210020954031040c6617468000c602c02c2200364142030410300c49001030040310100d03108041d030310341a005141e6200b20040154030300985842c10803640308801710b00784a150340d480a0500c44802003a103459140c000407982c2c02c5490380382c2200014840b5002400c0d00c6500e4400d40c4500d8182042290518010f600c002c540034801d80701009000c0c3c1400715208d15054412a449480c10068005004070b4003c070340b002055680380c60640d18082d02c0f980d510f4020201500d94081010f00b050400c0301300400d6114084840303c00d4241203050000340c01015105120500030340c40985410b858643c081d44400164203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 636845647 1250 636844397 636844399
    0x91b0103020c070521060601143a060501020f0c0303070b04030c02060d020d0510080606040c0504080727090b220b07030c0e091b030613050c130f0b0412030905 70
    0x11180546240c4c031040ca481741c101914501401022550741d41c042c80c18188404811003805007442c05079108102141ca500c4860511400c1c80c50707403a118402c680010540000903007500148450410000a26003281c3d04800055a4004941c20225940001c1071303900d000d41c0300e00c404603180d40e2031070116030748000c50400940141c03001c500c400d024407068002d010a140422401c1000381d440d0154880303000103034403850000d0b400a03030108429083c95005804a1010f50509030701d4250340d500410310f4035215902000d003400d0888642c0101100c10000c0300c1c414001d06e40c05000d500c815440f40b1012000c06441281508042501100450980b00c42d8014554000b04082c0c01440d00b020701801401c00d8490b00000140b204c440c0d91191300d040326500e40518108000c0b4a6420040030500180380c2c0040d20031540002a80103248840d5240e000301c038842c041401d449d83c0c884a0ba204040101c0b551030f00040c1c7c2000700f02c0da05008961401d41510100c484605e0140702d180100e040070303a030200442d088a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 636846897 1250 636845647 636845659
    0x7020301060e13050d080408222111090103120c05010e0a060501030201020607020d02120d0b0604080304051503010510120b1f09091a0d020a12060b0405091b0103020c0705 75
    0x1100c1c40c8800f48042200a0203282030f01c0c3c3d412034450003103540d14002c59000b0285007060124001010031000502220010140c0e40902d0913100c190020885468200c10100c1d000d13880301003c1001011001031104170f00690394180d195040d03a031010014401031989008001c61540c4075014000709401c90b1461024a134140d03484040f081c01d000b4054403090105901503c0f0380c9012400300741c4006181c40c0c0c40712299000d003519489400c0e50b9140d9a11091980c030029440c8d1007041c1c00c07907172054002d000400c442e1004682c3d4501d0981401001c4540c014810140e40e0240b0042045499460b18002c000f0307010300c0c18450001c0801150001001d0343e500c09900446610505000c5040d11078448480442c10b443e88207250381d46040000030784200204001c50310314410800c0841d4200070740082c1d045403004001c1070089072280104580c48204000035210309407105501401402e1900c02d168000741d0304e002403d403115507a1549448a000301d4003460425a0008442c04903400503c03291002c1c007801051 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 636848147 1250 636846897 636846901
    0x3040515120406090303140f06011d090903030a06080a080304030e040603060911150405031209040603080f040915050306041b08010e0f15040f08030c04150201020d05092107020301060e 81
    0x1c4c01c0c04142100402d14100307041c1a0403840121880c49810a000403c07001d507150001103414a01c0c4800001c036001c60f42c10a2000c69468030b0103d0300c540b10343e100541d181e14090a4100c2036600c60f901141194201d40c000c130001c1021f4108407540a0b0701402e084200c5c16200d00032400038040d41d400500b40d54503203076240341001095003031314842c0c5108a80780d011a075000b5440c01c0580c461841074661503070120341c00f62000311784107002e441c02d0500207000155040d030b02d880c1d400c0c0c070703074881c0c4807164940c2e10003e814483c509541c414512610b21600340d20455070b0400000c00d40c0d03202d024101a0052018081380114602d14072000f002034003c100091101e030440d144a2581d9030070b2100104504d02a00c0142d2801c00f0444150f14451b54200c2c00061031a0800e07252181c1d140d00181120002d00420803021480038494007170340f0f802103d1340e80016960302c82003003800d0450f50041e1440c1c015410241c2c103a1000889031100c40204a1038180740b594030407443c40001e00510040c2e215440041078902 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 636849397 1250 636848147 636848153
    0x31d0a0f08030a0201050f061c1b0f0f08070e060402030a0618060f05030c0607030c050705041a0310050702250509040303060e010603050417030901090c09020316050903030405151204 80
    0x80500101c3c4041e8000740300d5034960082c0c1c050318078412910141c01c091100c60401c21141807019850107540110111b60305008500c00103c60402c0d10780100f649640410400c009030041219514024911040a489241d0510034540c1400c00c1c0a80380d0342c801c68001c00411822501139100c60700604140c1414152250b82c4c001c160f020305524403d040001c00c056000080d281008112801004001052076160000c0b1ba40c068545150200e0107480c0d900c6000b801007030603190f40c821100149004190100d801c22420304061034043c401607071200c032074280300604c000c440e0006006000a1440d03140c0301d400a0310b4581c1c2c00b4071080c55500c0703154400c000d80c0c148400c2c180c0503803000007500e0300e0f070004400380da0b200da4042e4240c3c1c0c3d00341c1e40201900442502c0c0c805420983e00990b4000b03440e40b00118129200e82c98014104c6040c0d0451100681d0000921aa51000f54240741da4040d003410010700b02070300e00700003030b07140e000e41c1c030515014031581c1c007504006214003001c440342c040c02c0a140c40200d0502e81 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 636850647 1250 636849397 636849403
    0xf04080a0c05030c160f050a05060a050f0c06070806040e1c20060a060f0b0c1b060405060304140c0316150314010b090108011a1e040504020a05090f0607031d0a0f08 72
    0x803041d44030070b01c0c6c01a400b140c1400e010b112401940d0b80a05103034949060004100c03441e502c0b240c1001ca10f940203021040c0340b640c0500c21280221116901d03421103040203820082103c1007000d106619900080940c0b09030100d1103c846004d41c880c1c201041070352810b412001d00c7ca43c07048581c103414051f4100f0800d584800743d100c0d20580d00a20500ca08150300c0307081c03100551042400f5080c940e8040000d01d610301c40321f59880250b90001030600ca080c03035650705c0410942d80040d50203d030103a51900b040207074002d00b0044000e032054111b0081403410b00b58403514201c45807030700039440c0f1013850070151103034103000740c128140000c03800c070701041340d0743c4e4910403817107a1340011040900044140d4000100503c02800074107400c240c5a0040303107003c901c0d00e070122103440c0740d50703280c3c141072810301c40064542d90700e10140600710010380b1106d40d900030070020810110310803030300c0501c078410038040000443e0303100200f24040090000044d000f600c44070005107000080780e01c08903c2e1034140d0b1001c41c1603003002c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 636851897 1250 636850647 636850649
    0xe10170a05090606090402120f1c090303090e0406020d0231140603041a0c0a120605220908040b0d060f14330406110a020f15121501080f04080a0c05030c16 68
    0x340886254ac05945101214500310900c00a000545604000d1200407a03025070150840c1c41840c00524117800c5030a110300380e0300019181200d440652000c4a81c60004203403070b2031055884004900f4181c1412805c40d00c030600345140c14000c80000c0002070410000c102512400000d00c10980d101c2c0c44d000e4000044c2d540312040e13000c0019851390208070f0300070b4580141810f8401c002c101c4800f00f1305080328000900500c013802c020450311025400b020804060041000d0240040c3c42691014008900b00c15110254041c078001c0120f98000c10816050703840c10f411310b00c02255900c0c41e0080b44280000d03009084201c0190000004a0320294840384400400440307a071030310b86046042054820a48501c01c00202030b400c100c0361400200c00345045a00c80e103a141100010a00301840c841255a400000b00c440038040c0c60000c45200b079544e0482c10255108007611010120b510301139641403094000c42c0c0c000014802c5c3c401c0c90300f0802405000380c9890381014822604005003c0303800708604502 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 636853147 1250 636851897 636851923
    0xd0c06030b0f310e0d0804051e030a14031e0c1207020c010905010f120e100608070305070e011d040201030f0507020a02040c0c051506010e10170a05090606090402120f 73
    0x42011203c20b46041c0580012400070030003400940480c108161030f5054001c2c0200c130355002e120401d54801d0540441003082c0e249000003951070380c052f000084d0040d54004217001d1000301c14020094002481466082d0854501c0740700303000da49407444010b0403030080f40c3d01c60201c10b10340410080000ea0004010394840c00076640c80d01c6160340e42005480000e000301071503001601042c07105108400c290828031002c0000800c803004034501d00c4d074100c00c90740940c010312003d4226810801c14031000700025006421556400909945400f000d00c40340c00044401056a080540c0002d05580c0281d000c184042a400801d1105142542009480d100481800c9100b00d25001046900600c1070381c0d1500119400030041045400c00e0341704000c048401000e06040042c1801707002c003240c8030040c0091440c2e40c6910358014a40b50b0024031818114014a581c0d08135182408028a2900008590342c10040c144d6141150f0b40759800410101d20059a000f0200d00c42d1424868111700f0004c1c205865001c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 636854397 1250 636853147 636853219
    0x30e0103060b120a090c17071806050303031303050403020d14011109030d1d0d0f11010f090306020c010b0619081501020705090c07060606031a0d0c06030b0f 69
    0x14031181c940120380507980103d0021864000040c007180b02d03942c0032079030a90052480311400741d034035210f8000c2500b001648031300d1740e000b02c0c40410030f2940044802d1050740c2440014004913040c18040790f0f40f400b0003041d1000d50340d01030178200d0a06004504807406150082c0c551065070210303040c400007003000303181990701030341ca4403000030300103040c8409a5403500c3d0028003034a214814904201c440714000c81201981e1501600168003982d100046022601d1040c01c210f05a070916007850030020014841d45810302185044040b8031951043d40481600e0b4000d070016290384100b80c2090042c6442952150082e10025502500a2001c11041544100c0e84c3e82c0c04a541d94081d4800c41403408118420b000d81e21030b0105100c2403400300b440344e920003e800010303420481e140c2c41d000700303a404c0d07603000d0008256620001d00442003024440d980340c1ca8180c4d50550400900ea48822183c0d19620616040507503504d0300514550b5620300031080820000d000d28001c158a1070101c80007406c511114400324 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 636855647 1250 636854397 636854399
    0x303010b0c1b03031b01110a08091e03030103020405250504050a0909080405061630051c021b0106032001090317070305091008090601120b0105040b010207050d030e010306 75
    0x4240d6090606100c032014000e54100690502c129500c00e217507400e4000c29540ba02030711310103410f00310090001407000d982d40440ca800d01da4403c0d41040200e000340501809000c80e6112542000801c4034110780c0d0581d40090559500e51110750740203844218824007030030805000c51040e500030040d100395482210301900d07042d41c42490404076488044000d0450200b0b00080100c0d260202c090b10001c48031031401c80900d0850758640b130030700006070690340c1c00c821945085202070b00d400c1800e22070708449080192811000030b0541410315000c3c05c03403181c16500040d83d45d00c00e1070014850340e1040180c6009210050b281c4c9454002407414010b03210300707010281c462003520361007030000c1c0c0c0807240c003c8011202c0780c41c070250b40140c90b40b00c10310a9052210800c40f120064841d80641229259941d071744501d42c0c14030079625418030f141a4009013001030300348a080b01003240c40b41d2541c11211700f110001049200d80e8010707800e042c8aa400306510201b40c8000390107068024880841282e400d036020417401d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 636856897 1250 636855647 636855673
    0x501020708210a090312030203101703030411012109050f03032701060f090b090105061911070306020301061706011403010603020a1101020c032107021c110303010b0c 73
    0x60408035519030003100c0015094285000c680006044041141c80d0020a84d0f0712500c5d0000c40c0102c0700e148500095000003007101d41c1943e802d100d0013502142074001c400400c5901e240b41d690002800181c07000b0100c1c2d181424582c054401c81c070450320010402c07403a504140203000010840c1c0d40083d612400343e02d0a1500100010044900c24181d80790100c3c8902801c40d690000030400301c4001056640e6071001140c042820f900300801005c40040c04150b004009081c0045001d040c0e00140c0031f0702d410f01410184234820348000e0324110341490556500d0004440582c40c10040c2d500c090030b140d10000020900c180c1c0000402c26000d00c02c1e85809094072001300458400c500703c262511508024030060051501c03e40003000800030500c0c0800c03014031005001422a400010703038200340e038000143c50381800c098007881d900140202481546614040b03a0107501d130280b0082521210356a1004881180e0058942c916600e001504482d282e46e12660706601a50003004a03804521400d9854240 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 636858147 1250 636856897 636856903
    0x50907080303040f050c0405100501020d02120904020901020a0227100e0a0b041506031a0607020a03060905030c010203151c050d030b061b0304030c0b03010312080703020c160501020708 81
    0x8440c0804011481c642d1181c603aa0b08941c0c071000200c171180030b100c010344443d980b940a030a004505400311544114a84400a45001da250002c0d00c1550023400c440005805100c0c1a2641500107880240c0c1e40c6441d040102d0504902000095112008104241030002d160002c059508060004405982c8604854802c1e120702441010120a0000e000800002054110500140004d030010494041c886036561a840040d000341001903034515841e000c200304000c501d024050242c81c06454800e10360042004c2003680c0c00f000c0c20840e00e500d0b41c0700c02c100c0d0400c11225804a08c000071074581c20502d0903610760b0520071070041d124950012000c0f040c5007030340c03c6454050b60302c0402042c0d110906071054025101000d4100d81c010018050105003a41c00181681c010f00740c80040e50b9282e0642c07404802c0102190071192407408144014800201403100107040040242001c10581d99120740803406481581c0300403499000b5128019402a91a030402040e14026020340f204107803221551a9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 636859397 1250 636858147 636858149
    0x901050721021605061932090c0a090e0601170a0f15020a0306050a060201062108070204181a13150204240f0f0c062c030a03050907 58
    0x4110344082540081105040c0d0003003000c805021400c5125450303c1e1140317814200121004060b1980c3c8041c00b1b1031842e00351044030385021103110005156074105205101e0718020f0048110b001c09440040b8042d26800c000382140340e04000c1101419680b10b683c3d000c0a02450410300f03d49101d500c5c00802c1000c00143c001c0c00c9051010000c1c02009420784824055400020054a2040c44032902c41c0c4526041d00051100c0c10060701c011950f649400240a00b244c07090f4030170307821a40340850500c02c030305801c6507200701e0110f40400514070072081e080291240c45042d2000354403030320301501298000851401c91003400d01075003401d40926040ba0744101441400c0700c07240280700002032001c0029244881c28260040c840d90014103098481c0802c1c403d50311001815981a0248400d1010b01b692018501d000c258080c80cac041d40c8210004006000da4040d0b085c020040c545800840c407170101c960600c508140c24003195000e0010456503650386a902240103400040e00b0b10002a07509807000a840d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 636860647 1250 636859397 636859427
    0x806060d030e0603071e2003030708070518040207211e030e0c0d0c05131104120204150609140a1202010503060109030606060206161106041101020a080d020309010507 73
    0x10b101e0510100c00c10443d50f100401030f80500c801215a01141032180c944805400040c2d112080c212421800e07a050100c560020f21204e0b0384100304000126034002c0c0326a4100f0081d0402d0703030729250f40650000d205002d4407110350308140b000c02d15400340503410841114002c800c66844d803115094841c100c079450501c24580282090924000340010310075800701012510b607009981000c00c8500019014944040d002e036202207025509103e1854076540558a0f0030070800100252129101103681500844c49480070f10070012001c18250740b0b454205d45444468220000c5919869a4000d890041c5074001c0404030b0188600315019070501800110640e2040307803100c025a9010384c011620399100400540c10030200030030010000720940121005042c2640107031140d0318205100c0c00e540c6411021354000c0000b4141c1340c10740c0c0d1001107015500b0a4210448285a5501200503490311118000c028200400050039007140c0245901950240310342c2d200a01094807040b908030340a81d01003001c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 636861897 1250 636860647 636860657
    0xa0b0a0f0e0d0e01170901020a02061f03170f0a021b03010b0306040206130e01180c030c1d0102030c03160c0518010b030406180305070b0604150303180f0f0806060d03 73
    0x7001d0264043c00414580c0e80f414944090044400c200b02901c0c2102a9907681e001c1c0e4000c180e0b0010b054040c482d0a0303000b43d2520080c0d1028401c6401010403051071300c4064110640301d1910b610000f91001190004079101c09055070341c080080d4000c2da180c021000c03038405910b5002d640701681c50180034500b68010020000d1065403129000c121403076220210303001c2156844c010024801000b00c441c14000d10301142d00342084540b10340c0000581d000110007a04061070251450300464102c1c1005c401024481c1481e1b40c59403809005038610310840c403c808180c4000300790074600d00c184102d01e6a401d845103c03103040d041e1740e6034207020603107c00b100040300b5404a4001400001d1141c07020b981e004c1d01a11010403540300841d02c121016092030010384c00100005808024032017008000c82d0408029542080720031074450350192154068007000b8100041070120030000c0c2c00d0150300d000a01001608148180d9681c042c51082e00558840c042c1d40c1d0264000058113441c01d16244070781c0540507152 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 636863147 1250 636861897 636861913
    0xe0c071b0b1210120305120a090c03060203090c0406090b0111060709060c2d061433031b011e08010528060905030f0708030a03020c0f0a0b0a0f0e 64
    0x90341e05240201034180e80b189118001072803141e1300c0841d14101d8081c1e15190355860a000f140c900c0d0f00001811141c50a04024541b0000b51401e811101100e8110740b0040e140d4441d1422181801c102c0442a58018141000828208090f86c06920015003d880d004080082e030601e15490703403402c503441404034141d0281004094000c19101041e144105080800d5905070a02a030084600030481c0700910013514000080242e00d00c12880d189a014400701c0b003d1410002e0720707402007100b4108540542c84440c1c01c04554140780301040b00840d00400380c1b22194410b0b80d80b420200c0310031801c50f0018100240020318100c0442d05026290300680d40c0e0142a800c042c140312442440e02c100d80c980e525200e5858848503010521000548025038445c0324144c605400c1501c0d0a01250303c0c010107410121041020b4180001160304801c418180941c4400813040200e00700300982800d290980610b81900080214840f600c034860101201b00300031800340b64403030804546008244460681c00020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 636864397 1250 636863147 636863167
    0x90705010c050319030204090e1605010f180801090204240608040c260d020d23070c080609011a0603071d0424120305031801060e0c071b0b 61
    0x11001d4049402101281c0c902070940503102000c000344421180001c0e40420b09008110340c40c0200201c45081200520001c00103034111280000c2d5441824180020300700040c00c1c040c01403031201c00c003400503074141d20500d94645180d80a0f20b1441ca08a20641c54401c01c40c1d61030b10505030f03248054103a00700d039030810b60515100780c0d40f03540043c109564000c1d00440000e0002140241c400501e0b0000c5034030032894007014056480c02e2400001002550001501c42d0003650703100c11784030220390509907000201c05080208540c94400e800c1d01900409130305401144080c00020034500400200303008004401101e021512601c840001c255030001040020071711003071068000070304214100b0311060401070b18500103400c4031001d0f1140c20b0203c1560540e031a0320400c1d0f10704540101100501c00c04a90b49540e00100640300051091035540110004030015036025444040a09a407c4400003a414080f0200000d0f4000a1007110002078402c000c3e49070515140d000c2c4115220510800d0925082c44 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 636865647 1250 636864397 636864407
    0x304021c08181503011517070e150f31050913060e0f070306060e062101090807081c0b1e03010902090f010617060114030406020d050c0306030c030609070501 69
    0x1141e550f80c0543d50a110f102c012411030021802441004000c03001c41d0380528001d42185003001100c0341181d000000c0100c896007207171049103c04011036080440c0003200e00300321480d0003081c1003200100c5004c107d40600d208104a401500406060092810600c155a01c3c1c0182e040c0e00406030090702e0003012940e0590f404000b2014640700303000218a0240d4945001c0c54003140d10708803005075022704400c0041c01070a20550015114030740e00d41200e031401c200801c0c1449001120003135820080f503030034128118207502c0720a0455004003501d5640c402802c0aa1554105103540b0300c0c41c40107140d40c211022894440c40800203400307003400c41849280c41c0c200c0b25000011400d135030555240c64038400142d0b07410714410310403040d90301d041c012541000304c002e22007019645900c0e0f11544020a006090b82c10100469440c0034118a0070340d203689502e000c401034003c903e6010322003800e000501c1400d45071076000d58030503081a002c45038803485460030190355100030b07185c115807900881e505000a501c95 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 636866897 1250 636865647 636865687
    0x50118030c0302010f1e260609040b04020102070b0a020c0f0418060f0e0303181507020c061803010e0a14030a0801031104180506060a0609030201122a050304021c08 72
    0xa820702000c0a107506c072507486210104001c0c0000101180c41c0034012030226001014040610f502444140c98003074017044c000d160150016000380481d0000404680c0300b044040c010740740b00442940c585c1103002019640d5040040c0c203500c00c0b81c0000c050003c0341414420f41c20004089a2403410000c0c2e240c803990b00601001404103006525029141c0001d03004000039806041085c0c107104a170b1141c6450317207007049250110002d07241e00c000705101c2c015030700007260444045c049882540e00c0038040700d80200345114201e002d41650900c0102584103030082207801800d40140036072240e02c0c1010301c2c05616480b48401c1c681c0800e602c0c000510104050800c481c129960241001403c040351202902c62044503040842e4580c1c89082082014100300351000000d0900d810000411400c0d5400a0000003079540d0350004107540301100649951411a003944518900168040da818542341c010280e03031086a042c1c0c015850300b0101d0b019a161203424171001508403510300e0609605007402107043d104e03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 636868147 1250 636866897 636866927
    0x12030519020304390e010e060906030304090506011b1202070605040f03060b0301020c1f0b040204061407030212271e15072003010f0b060306150d06090501050118030c030201 76
    0x401009443c1648203240184c0034143e04002c0348032039850000000c0310f000004102d2030040128005000407070310b0000664065903032004010400707580e40c400407920220810f4481e00c40d48120340722802480b040c82058002c14a142c2e00350b55946e40c65080c04c1d00e951049118a144d0014028010000704126901142c0091001000589440c0c007400c600c41c5011400d112a20b1a084103203c901c0c0c0c0298a03206400b074a0350103880035802d043c58800d002d002d48103a80380e548255903000035601c04142c404d109a00c54040c410565580f0f8041082c0e4100d2514032010141a000300010001140c0d40752107400030131351101d803c00c0450480606402d0000304034058490b40700040741070181c4000a002c0780801001c003140c4102e0005107000c00004c00d804c0d40c01c00c800c3c0c104a207191190390102030b240d0f441141c1d8007130402c0d102e98140b210141c0504440344100c1420540032840d040000c2103004a0307401080c1218000d9a4000130446003c0c198012500b5078031009105500010341080194041c1000d645003100f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 636869397 1250 636868147 636868223
    0x1020c15070c060f1106010302031f140109050a060503060c0a0f2d17150909030d051006020c01020f280206070c03020301060b0f03040f0203030712030519020304 71
    0x319903034104104a01d410a50104444014901d20258407003c40c040c1e03005c0040c014101c552642c0c020a49401045840d541490008124a801e150f0550081c00b02a003240040d04a25a9200d120400400c000d0300ca98580b642000d000140c28500007803424000c1e940312030303820b2400a001000b550281e0401c001c01e001e0000d07401c00e04a002d502003a0300c010384102c0d411002a8040c803c1402801c00329404880d040012401080c0411110760050002185405031000b00c0b0390b80301c01e55840e1450040c000203104803420907081210600306030b0f03000c0044079100d8084a0744c1010303410042e80c8901c205140c0070142e40c080d6440f1240c007a40c0d0240d0060707031790f108101440d04024030340204040d6071141200b600c0240800e481002181401d1040b4001489000d40840c200080c00a01d00d16a00c0080c0020b000300210030300101c15903405100302e44409900c4250505080c42000006d00a80780c100d036003801d118071407641190b1550250003224800d69100040c482440e40d181d6001140d039140f5034950241070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 636870503 1106 636869397 636869407
    0x6031104030c090e1612171206130204080109030504050901090b09070509040b09040308160e0d030509030c09010e180a03200705130b030c03011815020f0d0c0210060501020c15 77
    0x704116210414ad61904422001900482d0003900e4254a001c00c46800c240d04003005004079401501d0131082aa03030744e8500301c120f918120180740c11505a40008801c2441400200500c14004000081e4840071001041c800b00c400c540881c0492810010302c04950540c0680308079901c09854950300b0303000c071440816114102c9801c0181404000306000c141d40d517041c042065185070162408041d581e40b190403281e00030f01510140410090b54520145612004c14148901ca4160b110135960701ca00203540d400d01044085049414010f003a008516035489507050805031449000208000000108250801d01040181d84c82a071410050648000000161029040e001051842a001c0864105000e44902c0c52941015107000891541d80c403c2a80801d0044030264225401004030b03184140444480c2c0c041d030b41c0541e0182e0160042403501e410311b51800350415100038280 = true := by decide +kernel

theorem cover : BRFrame.Cov 636690647 636870503 := by
  have h0 := BRFrame.cov_init 636690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 636690647 ≤ n) (h2 : n < 636870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
