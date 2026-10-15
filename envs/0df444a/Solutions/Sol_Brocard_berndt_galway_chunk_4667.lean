-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4667
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:20:52.867846+00:00
-- url     : https://prove2.me/submissions/91a6a56d-996b-4a4e-94fe-6cc0a4e05c2c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 839208633 ≤ n < 839388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 839209883 1250 839208633 839208649
    0xa14010b1c0e0a080d0f0603020d030c061d1f0b06071704050603130b1b03180c180f09010608030409020901031b0f0e060c120f13080d1709060402 64
    0x401000d00392280e4080490740414000d000700180700754403132a11001c0203140c800680700c0b11645810300502d03101c820400344e600c0540200c407554140c102404040004e0030410b0103000c00c002c00200c004011007000907900c4000421803507600d10f190106406449508640c03007561440100683c1c071030400e00500001c0741c40f8140c54005010601c0045240541d00c0001c1130641c0c004880220120000c06280c8050020140050ba4460721039101d0a129060340c40d4003050300c1c0005040c1402c0549000503960000c0ea080102241042c4014428903240031551618107621900700c0340d6000c0c0515071004a00380003c14001d01d0300b92455003000c1e6040c2130134840501c000b500021081c5042584031514020700c02d10000e49a904081a6580c1100d0354900d0000541b03035000c00c0d01300310300900f010032000c5001d060109545040c0002c060303599580e1700100003004034a028000b4035040103590442c0003d01000002400001000302c0e803250703404001802480f80100004580e8001d194001d480090014600424 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 839211133 1250 839209883 839209927
    0x40b070302030c0418090c06030c0c0b070311070807020a050a0602210913090203010c0507020a0b0c010b09151005040305150402150412060501050306100e0403030914060a14010b 78
    0x2120702d041035541c03102c25090645c580c2141414076642c40072401030001201c1120f0290040341400d1002c0e140000008107002c103100000b40c011181c00003c2980107100341c01c8030003003a000d01c1d10301c1d40b60000b509100c3c10b5503110381c0c4100c0c031411446000088030b091203c4000b044418035006045884840403c10340040d000003505518400c0411140e15117580c2c1182c00051003090050001d010001072051500711041d100b0700100744441400b80400503654444507209031556212130548400000722038902410000d01c036141e020038480d040100e0050410340c500d511007011101048403040c2402c0c180d0f00c0340f0581c0805000c2e90044c01c070601d41030480d00c904582142c0701501c0e2140446010060b081103804c1340e00181701041d1030211040a119507801882e014000441c0070b4160750030120032890f028070701881801d49507640f62001400740343c000e901281c0c10f15080700080101c03122420509032507001c01c880c80d0311481c0c98121007629030140d119070035060b0742d41d002285241c64070410311030414104580c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 839212383 1250 839211133 839211151
    0x90e2b0311070311010b1f031806020415080112080405040504020307171506030d0f2007140102060a09031d0607050d11150c0409270b090d08040b07030203 68
    0x28040300c107000d110000818a0328080e944c0ca0251080341040340342510100d51800f48202c1d0030815901c1c004240c0c0c0078040c00d180712401c000030000c074185070018a07020a2007008e0440d520104000480c1c80761845110301c00d43c0c1076a40d00b000c030ba032101c0210b222216254805004660203200034001b40c01e29512564000380001d044444107580c9213403005144030655030600c110b03045507500035144c5813041030480e0026030444c0a0311251019140090103030031080120010001480300c101894503030394600318021428141500d03142901e0306040d040e00c0c201200321a00620075072001900c0f000d95881078200e400d9040e641e02e000c00c01422140c403511141428002d41c030030070420030b000c00584200401c145e0705101d900d8070032403041407046003414030180b191381307068100c00c1c036082020107611481140d054031010000000d08002d02c0d503203003203040280c1d12001d060005681c0e05034240404503502e944a82415000c540100c22505804c850340001910000d00b03040301c9401042080e8001d4004d564010440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 839213633 1250 839212383 839212391
    0x402060a200106060f08060310180606030f03170423010b0901090b18071e09050306100905090a0c090504110d0305040f32040b060f04090e2b03 63
    0x1031410018030680011145549070f640d0b1100b001659086030341603860310103c1c200100d451030043d000c00d440e0703014a180146015a80c0c0500755041640365400e2404580081e42002495142c3c5888910f014071100184c011030300e0310000240c0c1e01192890203210b42c0e446488003401440303a603c502e0000c100d4442c003144c5c44d502c4411000203500c0c0c850549008151440d000309003d0914024000c4111584440143e082ca070b1608008002e60024856100c3d110320020b5581031008001c000c07a40d596040e0045549402140e05000b60b600c4a051410292400076104100035142c09004607500c0f11034440090100c450b40c0e0f01000f28000c40c3e4015a88903004404035804401e65400007103503074030b00510850102e0b00100d400d00400c0c00c0a188030004c1c14103400a80345181000031903840d005844a01801c2e9401b0043d2001100d4407682c004204906000e0400c5440d03642001680c1900d0f08a8000c0702481450910307007001d50b0100055080391528400b021801c0600c400c001034100a000d040f81405040c2c403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 839214883 1250 839213633 839213657
    0x40504082203140d02070e1312110708070f09110403080a1d04140f130501020c0a060b06130e091207030302030f0a050c160c1a0c12120402060a 63
    0x181c0c1c0340841c14007058200305400c5260041d48041c50000700d411584c0035011504030681c00240007401c0e01d4103208010a070b41d50f5450400706a0302d012000600151617000d0380e81c0c031160403a800d100c0441001060351005d9884581c85a91007080c0c1c415804400d00e440000c10008210342d0220a5444c2446916450584c072030b03c520f8480c2c0d100030111130010741d04464203806c009412034000f02400040301c0602101c1d0361402003400d0044d019044d8066200e01c0c1000c0b450352100c0109160b94654404c000f0341d240d00b0080c103010b48803412100c007941d404d07003130040c1c0d602d09117407800881e1a0049094035200c8440d0805851600614004099070070313901c00c5008041380d241190000d040e10354800da401580ea4a04407032078001418015004c110194204024052020300880640d00c03070381460759902d42c1d1142242002000c601c85503000c040c0341e92050f0142c007061980700000304000787d4280100d4100802106080b0200c2c4507240803000c000c000400480e00501c0d010380100035414091030030701c0400d01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 839216133 1250 839214883 839214907
    0x306100c150216060c021f050105060301170a1506060f050c06180f0111030a0b060c0a0305090109170c010201110c0607030903030b060d270f08090a030f0c180504030e04050408 77
    0x2170140c1d00c0250380046246841d00780c10701c2c0000e07500038249405200f1945804042121030206008260010400320b80000211408002581e4145d8100388017010360040e041c002001040d150040a000940015040761118002c01c200c0d410807544000820099454003004d501f400740d0f001c0080500d0003112103280d1020824000c07084c0402c004414550343e402c090000d40c0c1210b00d45491540150700031b00506000c500040b80d00c1e00b4164040c180303556151341e50001241c0e1011140c02c494004001c210b01c1c084603900018800f00618000c1c0c0082201500350769032300c403080c06521094402070780014001840288030f900001c91031440ba040c080744500c01100060b0035500314540714912550b030b44001c03c01490401c1c13084041c00421009148642100e615020b80c0c485810381c010380040400a1000e07029160f60136494011038001610441d0080603107440d110140fa9071142c2c00002000540c02d540305c50b03003481801d00403a41601c82028508080b02400f015000c000c005640d0700d0824000307641888 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 839217383 1250 839216133 839216141
    0x70c020907050c060112030e1504080307050106080d05070c0b1c06080a0203150903070b1008012c0d09030201120e01020309070603150b04170c060a050306100c15021606 74
    0x101c003a07110551552091901245841d10507403040394000c0d1a00080c401182c0c02070700da02003c83d81a80d281e541e0018180c1712413107600c91a40003005511000581209000040d0f1250302030300c012005441000b0841403003219503000c3ca00c2e0162021113000400c0100000b0003005140340788055074444070b07a14404080d081190f0690303108840303030741140902208600c0c080c007a10402c0c40c8440c08008c482e0a2450219945e0b000d503c400800040000303002c9001c2000f12415540140f4040c0028405549031461103075448000a10350014410806e5110001030004104410701000b240e42300280285160011595030804641601d0141c2d591900c3d0300140c0c101b0b00056203d00c0c0b031000100444c1e03140c800d00070201d80d010b00100640140304402409219040f13030071035040350b81d101003d20f28015000d80050500c0705044c2269840000010a10045500000510304c034000443e505511055004816a441b001000c8000e110211035803000070426840da010704240b1000d413852603118029991414110b03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 839218633 1250 839217383 839217391
    0x12091603030c0302061e0c1c0c03090311060f07260c0a0f0306181e240510020a12031103040b0108010b12030a0804020f090a0b040c0c0506040b070c0209 67
    0x6003403044481e05058040064a4208806103ca02417034405682105401b01c400f814103004554001207081025483e0744215400b294904003c1140103205200503005020116084011907040d90345030035000700100d0701a108424080041e400ba950702c02044851105840c030100380704000700b40d1908004441c9c01a20b114168a201c0d8603900c0c0d01e210006407109078898400b81c02c01d414104c05015444140b100003000300858240451110240b020001c5090700343d966070012180380001c001c07011085210221f90b0940b40b0001c0903150f503294002d001c2c243c18001c1080c03001da0301c00440740c00015a12558903018811030700c1c0004060034042084c00480e4025a0f00352071943c162401400100c0b4281314088080108a88100302c10a0903000c50341c0701c1c0983c500070300522410000040564a98403250800c6100080900540e0302c0c10320a010000e01331140b69a0042c1e1419403143c01e0213015240c04040e041c0c0080051209903525030b108408240010402810045d00600c441c005840d040002805 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 839219883 1250 839218633 839218637
    0x2150f0a03050609090a0f11062502010e01030c020a0b0c0f0417010e06071b030207050a1d0601180504050a06120309060f0e01140903010b1201061a09061209160303 72
    0x1c07810203808010303501d078020b04285c0d07a98200f20300d8800010712944500420683c44450580d51804210008030390f030040d800c03500364001147c001c048204107024000700d00c41c1c6c401d80b00c01c0140f1140e071004400701d88070300364042d0159100110841c003180c41c4006041d40715000e201d00c140b070600f15420100907600948e000342000b544200d00e88181903428041e4a0103210b040000349014903105500811a4848038407002c2d04441a480440500d84244442000703028007030702190f0340c80c1c2d50f0001800e42c240045251140d16076080041440b562149024502003003590074495a202e041c0700800c4010200a0601403001c2d135540c000203007801110072103902842c0262241800185441e10151440221355031482c20010741e942e0300300b02686c11207a111480110f0309a000e0700c0380c1414004c00d004003070fa6902c403903100d5100d07407001048210540003141901d82c41c8104c5d07002c1c036000c1c503003c0d1614040e070141568020350502041148070040b03039109a000100f03108441b050100b280240c0391400c8540c1040d40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 839221133 1250 839219883 839219891
    0xa0b030d030b040f0504050c090703060801060611010509070602071a07020d06150b0909070c030e121006050103020405030c0d0f06050a0b01030b0607020109140105040801060b040e0601020304060c02150f0a03 91
    0x40d01d0329161141c80140001c542050101c0d142c1b99440c60f0300c0e400c0710721081d0f01c64024003020520707945c070960200014085900080000c00c2d140c80020b0801c1680740c60241d4a58280380005e02e190402150715405c480150f001070003e0350814110300320038170401489444c1c2c0c280610840c00940d07500d14865004a000c0c20000070030b40c1400c4003003595041d454111740c87c41402000140e43d19100c0031a5543e014085240400642e4406d142c22a02400140d004551040301000c80313040540340860400e20b1000c60701001c0200a50700c60041d800d9005512a580d0315800c14001c072945814010151001ea9100303400300f5403401c9003540d81d01b04483c4140d52069a050342e4101d501e105513014031074401a850100c0b42d6500300385090340003c01d002d4142c000d440218041c0303114511740d41d02640c00d48000d0b14101009010306500c481074004e4641042c8548400d1081d08004200303554004402c88040d00c0c200c0e698801c2468280e0280011004400c002c007a00680c100255070000c034281c0f0103000004815070303000c9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 839222383 1250 839221133 839221151
    0x801031527020315190506062b05060103060635070c1101090506090409080418020d0c090b0a0e15041e0f05240733050c0901080a0b030d03 61
    0x5142803814422550340001d52014001000341a1084c496500c0305100c0106d40b0b60ba603900801c50303d01400c2410941e090001880355510254074a400f116070b0280701c1e080240c0d98513000110251035544c440d803004505600e9616081040c20704500e0942e14440400000a400c4040d00707409145e0101c1c0c00b040090600130700e2008021034a803201c1d815030004d20309030000900b41400100188120910b09100c2c0750340d41080000c0022040949008100c241c03032044243c00c081d03120201035444030059120f294038000c12002500e020701015421384102024003824100c1c404019200c0b11840c00409502108485501180e2358442d00207001400340c07143c00c0c4092200b0002080a0f800c0b2030381000d403040b4038051091010b40c82c2c146820700c42d03903101114038206100410800c9164880c0c1c04000e40300243c1006040b043c0b0803420800718803606402c1001d01c04070304103820b1008a91081c0c82c1442020010004030398151300c200f03040e503000441c0f041c00103030600d2a02e00191428801c5000341011a480ba1103078 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 839223633 1250 839222383 839222389
    0x402090a080610030515061f020c040c0e13110a201e100509030f0a0311120601020d050c07090b010e180702010b0a030804063009020405060f01080103152702 69
    0xa50401c80c10315404059402c01ca0001035a2040c803100c50202e60109230a4408d1081c400c11131010290720140c400c114480a09100604032980d00000300d001707000341007603060141241c2c803503100c0c0c6054401e0858180041204202c5030310420311102e6030b21011036403012607801ca00340304460030821404d030007641d001041c00c820781c00c0068070fa400c00ea6480ca490100510a500401201d1b80c2c841055030160361401100c006900500944200c01b032001004524841c0880388141240e0151000f602129007d1182038400c607034a21a0031050203558014000c1086241d99a4010340310000e01410f111110808072400f24a10004244241690f5807900041c0200150203104d01d0364002016100400d4850039030b180e55925206070306ca28410840581c0348007403110504000203030b590b8004103594a00b007403c910300c1d402811900c40305911440c90000460613170314001d80105c0c007801068592000c1d90703103151a0344000403046080303031050035181c0040d0059055003a0401c0b150000903016603d20b1090360042c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 839224883 1250 839223633 839223643
    0xb030a1e111e040203090f06090f01110a0e210109030305100501110604080325050304030306090618050c1908010815011a03090709020708031918020402090a0806100305 74
    0x70070b8040d12188000b60990203001d05007820044090341e0243e5a42c891050141c5030a1010f004e441082c090f481c14454008008a40d0302001c1d1306c50f400038400e80d40d210000b410341d0721400c41a000403a08440c0c1100790303400c00d000c07460421141401c012089000c0580c0c010309442c80b0110840020ba5141d0400400c0140c0980c45000b42000780b070320410220340204220345d500e10143c00a030607603e000c800500250140315140c1120071030700070105846912030030f000d8102e8106036022404a800c00001181e94000c0344101d50844450340c11130051401c960740c0780001814045c00754840028100014501e00b103403a00c40da11000080d0b43c42d0b120030b6240c91561401c00c14001002e02036000000010006680b06a01c04055000505107440d80d030748540085902e800030070340c0001d08650000c100c6800b4043c5c0c010142d84180070075200e040b06280c2880c05441110802d62403c07820701c0e040c1c100c0c034001d0306196002e00480310004d041c0032002a21600381c02d10703000303080700c0d2000b140d209500241300700002449 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 839226133 1250 839224883 839224913
    0x501050c091e0d020d290c09090916120506010e090304061d0405010e0a0b040c1211091203030105031018020906061c0b0f0a0305030d0b030a1e 63
    0x9210341000400790016480300c0c03461000100b40d0704031000d00d10007541c900b54040511035005040d22405040c070700d041c900c41203601444a40c2500f090350030500c14002c0040d164450076055401c240340007a09410400302000180c007003000d80c818442515440f030303042021100942501c4000c2c2c180c500d158030f02039280c0301e4140c000144110301c00c02407000000c00002a203003592003905040d44448130502c0b0039202c2c5020300780f9841d403040c100b400004000d080c481c4031340d010f2404148180018080c0c070b01403105840842c030700080004e40b441c840d88a00c02a0754856000ca81c4103103e80f52820b88460001841080c1c0840e0f5060301c0d401c00001002985820000241d00c0e03c0c410301e00f4410044175070341e200902c0424550107406a4000c40028103566550000c44490444c4da03400c2052a0000002c580003e10406e420319000c0c440c0f40f0140917141c42c02418000490341d21000a5292400740d81018016003440030348581c052260001d0000092266021030442501c00d410249910745d203403e20300b4401050035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 839227383 1250 839226133 839226151
    0xc090405070f1a032a0d0516020a0b1501271508090a11130f06140303040b0f0d14070305220f0b07020309041107140706050418021c0207050105 63
    0x200d0400000f1090081d241d124481c42d4401030038200240496514911007000d826940f4000641e10f4030340ca81d035510680c0a036055100b45070718440700010580e668200204060000340740400000c503e4500751104011414040c9444010a2007020007000703588640c11030300600320341d086c0c024030003038117040f1565151185500c1c014400303080800095449031030384000038040c05003010103440c8584890110646581d0105001c1260000b02c1c440390000702600d000c5d00c1c514907070b410300d006154a030000039203094910031300105280c061304a07070543d1550721251120b64070076190348021210741200e90b0b00a20401c8039480c0801c49180c590101c5485061082030b40800c41e002c3c900304001300d502e224034041d8950340807104070526191084268614003d00e20559445400d0010306800b40021780e001d0146588a58802900410404000d5455080794003841d0000b400600c0b041101405c1581400640c00240e00b0052130308403820841104c4402e10b159800d409500040c00004006007413103010390082c454 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 839228633 1250 839227383 839227409
    0xb10030201200a020604090b0a230f1512010603151203050702010c0605150906092503020d06090209010e19051306050303040611060a0b0d0609050c090405070f 70
    0x250380007a0080c51103107401c0b510003948006400c4a568100718042c8100c3c2c0007800c00b91102c3d6510700c024060503002d154103004018996000607007810800d24041c2c10240001d01a521810307184c00d001070340038a00320080d44038a05544400e031803040100102940ca4405403880f50542c18600050180e550007034010207141e0451500b0014040310103000300c0601d90500d0500d6440c94540012a500c510a01d03004c0c10003450403080c060385400c1d04c00d42942942c002c3d03820501d96900d0008200d901801142d00421701d202040c12030b00b41001c20380c4000001d0500f4140113003001803040d5840d0445410390050088140e000079541030668001080310403044003101e010900d42c56a0106c1036026900341700762130084109000e079000000064001c3e8000c6e06025040329203c2c1e6541c0c1e40106248d070240e0344e10525008640101d0428802409042030710030026021200070405030361f410b0000c1c1001401601e132800f40d940f4218180e80c6041e14680298000e00003050031a0400c44142c60500c201d0341700707500c0c103594 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 839229883 1250 839228633 839228639
    0x1208010f06110a0312020c10050114010801050906040c0507050f0714030a11010f050d240f030503070b0606090d0c05030607051309021e041206050a090f110102070f060c0b10 76
    0x2005a00d0f070394546480480c0c0c08000c01d81134041d0041c1d02807011203002d40c002d6505104c486501060490f403111b0b2142c4420030110b4011344002c18280034042d00708204500080e080e08154100468400462500c81c0c80c00c141078581900380040d02024090f0f81e0810b4404220b243c188000403503038806d0843c054a11455940c0e00c4082602c013401c4024144013070b501c01e0121460245d400c0d16000390043c8810300001d1a408a4080190792181c0030610700c1c0d1408034003245280183c074040058992000056103808510340300c40004202c001e0102e54411410000c4400c1034440100c201485807251420403074040c00c107400c042c01c1c120001c0c14001002802d01405810519a002c98400c940d2100d0006944640003110143d4400480d008146815000507001032140d5040012a0034940100000c02164a0b8000c0384030984074400409090050102007503404901000d1002c1402c810500480d0361142d0744a84041c5643d1482d80620003050f802c40a480a000381c0562003640070b10803003808610030341 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 839231133 1250 839229883 839229917
    0x405010815030d030902150c031306020703261b030a0e01020f1e0106031a04060b0402070f02010509040902030d020318040e210c030316030f050f06040f02071208010f06 74
    0xb0110f49200b0415440301c0c6200250f4031401090320384400481c2070725968400740704040759030394440c0c01104802c0d458420002403c1c0d201003100b00603a82d1059440c01d044581e4050300d1985468201210000e180c10490140081030421403c05142c070004041e40d102d404810000d031440a004614605541166542c240155008156801c1ca101c030400040507000c82d60741c1300d40c010b0005800051000c4414403502c45844103404034944198403030003041c8032682c90309040c0001d03801351400040c076141c0303030380c0541c401503029030081c280310840980000340103010f03900001d241c400d000100a0168000050311006414240c0300074a502c081550144080320f5030070341003030340d4038642140401000060080300c20040c00d43c40880c2c061360010303401c903610384c10000c0041c0c800c40950f419240109150240504406416010350b51141001505010381907940505000141112080c0503000550800002e000950103001803004400e0036980d08070950b0410740040741005c520341100b42804100e0905551101e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 839232383 1250 839231133 839231143
    0x120e041a1c050303250306061b14060f0a0b04111602061908070f0e09011e030f26030c0f0711121f0e0705061809010308040501081503 59
    0x5010784032410040310710040c0c4400d020a0300401010380c040002030280d401201d69400c0e951038a00001824120100c000c02e8007204e02030311071800400e141040c000381110480c004220070902505080007090f0203500900d082030012280040c40d080d01c00148008050a031081c0382c48503400f51000c000c10000300250440318010903110102c114410000442191a004280c50320f6007803d2242030f4181c2460a006000200104d941400160303410219403a00e071321038860300808207806445030f2181d03401d01c418600d407141c401320401c03000c8841c0e44001002400c5001003001040c021032038111808100141005158420800d003c024803046c018030455000c0d000c00c444c10004a248400d9480d40e00c0c1c85c0060001c40c0742c040003980f00d00100c00c010302646000c90303c0e0101c030400800e203664a085888211040f14141c5202c00c280364031038801407100d4288080200002c00d64008801901400da000088078000309800450345500041810017055802c0495907400c01001c0d682c1903a66000c10300070030307614 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 839233633 1250 839232383 839232431
    0x504181d01201e0d0e0d03052e1a0301170303071713020d031d0301060b0703052514010b0108010e040b1302030d090e090a02060403080f16120e04 64
    0x880c900160f00ea101041001c85401c0c0890b242078580c1d02ca903903491343d4030b000300190354444501c1d026912400541e10300ca03115662240100c0381000814600e800314010400300c40030440205c40b0504200811103a5000c0c140c40e041140c900c05517941c1398144410b0103003039809040403001640c420700920405c550080c9402c0f0144981d000d2201e9941e50b07035026510250303201d580203500928134441d000700341540a100035000484544a5042c54020352040c075003298242d104a080403c828007032080082d219600818002e250080d880f0580e040030116001c1000c0c8030341045440168844040050b90700c2070180910300c1c402428200c129615154280b80300c5040180000d000000c41b0700060190581203101075030807a00a02156601180840003400c2101f4a009100700501220001917126000207240d02c0ba190780900154181480c507907a0307141c1030300030321030708203107240e05114180300c100c0311490400c24640540f02d8001d0000c0715100242060f81450f0385940218103003803002070f844650703548c50004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 839234883 1250 839233633 839233691
    0x41418100506160f0c030209060a06020c010f03060305012406050a0e01030e030d151a040b090904050a0b070504090c0507020a0608060612010b040504060503030c1c0504181d01 77
    0x541c0310300f80440100b00320110701c0100410720b02c813034400512400860b6241568420748840c0740319200c034010000040d4041c484c8000680c454401d403825948503c41800d500601d030b050100e404c90f226130715507007940c1038034800381c100c2002c141c101c424400c0c0b4a02207000402c4581051890a5540d0742d006190b00c0014045506140d12440d11303500040c0304000b04d0300403e03048041003100311801400d800c800c0c980d501c11304031013400600081c0c11000400c02224100d401106180d031810030f42c00f090046034040200242d40e13a004411f85180450400c2c0383c40d51007400d075030351116586c070b08040c06802114541c08202003008401d005030f5005071190450881952468200318145540300c0000400c07900c544007000c5000d000d9031000086580e807110140064171801c65052245640b0b90050660342d0090103844600346d4802005208080da0078861030320703410703030314070306940713015207030000d1a501c401882c040c024060b07a81c41080c07040d918012001e11071404c00000a00041039920401c0b44110500c680d4140703 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 839236133 1250 839234883 839234887
    0x141b06030717060d081303110f0d06050c0f0a02010b010807030618050a0e0a14070b160b360601140d11130c0c030f08040803041115041418100506 64
    0x680f81e51100004c0c90100d0f4401d1246030340700f0b24600a400c1807601d41c13104035008804080300750494079184102c00e03100d01000d8255004150300307440c1c0030041e01010b04203550800303042140a40a41ca483c0080c81d030100d081d00085085000c0100044c140d0b000100b0364001c141c0707460000d218070001c400c060f03500b480041001150a0300e503040910f00804c0100e061224600c54003200381e0410803002201000d1011030b6003940c000320f41d201a803903241e109460300300c4248403412940c0000101940e5070f040d04000e0282140074105040d0500e10020829030800c002015072030754920084920402007240901a000e440181c034240381d0001c1a20803400341da00500c00710a050b4100ba841d180c450f050044071500c803509110966410308081d140069002090b030000301c8811503400020f0203041c2c494041e42d80a00c40340c3c6180d45a031115114003008000d0075500c164031780c01e003201384140400544050170b0400c0c030500038030141e501003001101c501c44101455018260803c42034850591181c0100c900c142c0b182d079 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 839237383 1250 839236133 839236141
    0x705010c060b28060915051b030c011e1506052710170702160303030e010902040509241003020108060d0609050d030c1b0201030216141b06030717 64
    0x2e810343d9060611000b2940c203c2640c2181e0f030900b12034000854000f0740b07443c3d4100c0d46030000c00f6152004088a10081031082000d030542d45225800e4050ba0b100e2402501d0404d007030500350f1170030356071100c3c102450788280c0700d401164451141b10321110b1445008108000c2407030103130040c00758080e990303c0c8000c803511810803510001c503d5100001e0588010010303040c040140340003400050f00604000c2102c40003c1c0080c01e201d0002a071225500100030f0305041140c40c69800702c014006d408102c0400e1b54076141c0110051b2260700a29009000a4014000c4400404103030048801500c0b482000404090300780010291080d0a401c240c13070b028609090181d0341d042c0480c3d000d21501d00014907a0f4074000c4c01a083c000040345600c0641c810759005d2103488896881143e4070241c0c03584052034524180d403560b00540c000e600410b40702000740b204d29080f08d0b254481c03580440c6c4a003610410307034012103840030350380c0001d003e040007246088a805085040062000300744c40c0004081406000c02d9201003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 839238633 1250 839237383 839237389
    0x2b0903020705060d0b090c07120f0e04050a0f0c09060815010e0d02120a060b010305010b0307120b01030f0f02070b0105060c0618010912020a050c0402030c090103091502030c0a0905030705010c060b 86
    0x101714264009012030010f41051030002d00d180d07208200c10f88980e000103101ca0342c0ca5100798402c4a889144d9039503c0507500000b01000000d1001402c1036044a58940310343c88240414081e02180c184a41c0704c07804507518102c009800040b005080c4206c56420f402c14002d242e80000001d0301009040d43c019404400354400710303500c040e8220365242c092140b1101c501c1004695000050744d01c0d82030760140010b90b601c0300c09000ca07010031754044000c51203940c00a0000001e6500c034100c0c40005240104070b58191584040c00c88040d40710150b00103800185034002d110310100c0e040d004001c2929017510784010b104460741c442c1009001c0c100001c2264108000101c0309420820f005a000640c4406420325507801039614120814115694011191000090328182c82502c0c4215001d2080390703c2c107801c4000440003048203010440b401114184200061002c034406148961480c480c420740d1030801d24805026600c0c160b0015100b0341c0038100038407282c1d1784040300d00b4000d80d00c941c0103d02a0b004d1000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 839239883 1250 839238633 839238641
    0x1e020702130908270d03030e070f061205090a05250b1b0c090402010e010f0203270a090209031c05162307031101050307142b0903020705060d 62
    0x65001c0c40d04150030001808064001004070110034161145a456241d40c1c04484100c01a00c45500c20350b841884400f1038000e13000440342a5008040d00e14081e11140741c040b0460b241c0c0c219100003680c43c1002c05075992a40302d11070708507040c64010445034001c0c0c1c1e112a541c0c10340b201c0310300c000c43c08122000034042c400425000500100b12449884511064400315070200d2961304980e140318142c003102c840e081c0151082c0c06030350103940f056403840c6000c00544240309090802c5046202c1000541039040b0841c9000c095031076084d0070b00d000e0603030860030031440034900d800c2441410310400c500c480650b400242c1c1240500d829504180009209009075514050404a44a9100c1079000342080001d0010b601100781c001d0311414100680004520360f50303000900008005e0714801049100c20340c045c02c051503002c0307071602d0300c00c68881c82000d180b00c454014602548040003039010844c4840601c04a44a8908071403104024110298030000d40d42d01c0c1e14801c4900500000410b080541e8041e00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 839241133 1250 839239883 839239909
    0xf0117030415020102130603330b0d050105120312041e120801030611040f09020304050c0604090902010e10170603011d0a060f02271c050a03090602011e020702 70
    0x10740d0361881a80c1007006030203544504205030301e03109090001f2a0840c00ba208d01c00c0c0601880d4100b4054000b000c8076502111315240c0101c0300a0420b98000808010b0840101407402c940320010405500d41801c1c0425100320480c03408141c0c1040c8041c1100c1e8101c85a001da201d90409000d0141121000000c8000050f4000150030b0b0180c048041c20341e150405642e5048a02c10002001402c181007100000c0340140d004034010b014000c0e20170081d4004c69005190064082c3c030035242045013010002340154400c0e480200c0c950346490315030082d9a0001a4040c800c6025511034102500100000b00a80c6211104150000c4808041021503d0942c001000b841c0780903408201801805041907036032025140803030389c0038145141e420a102443c02a107169102020720300c2e08021800b40b210301142100300210360080090ba400d001042c01840c900e0104500981c090088020700d030400404440ba00d8000009580c1082c1e031400e00201038000003440c0c240c0c800401a2280d200c0e20004003955a81c203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 839242383 1250 839241133 839241149
    0xa0e0d0c06030c0f050918060402090d050706020c0f0f040e0c03070807090e0c09190e10291c020303130906080f010b130509190b09010c080f01170304 66
    0x481c600e40c05901550780203080d41c480c040010281ca2040303e07103100343c64400390401c0c041001c461842c0400c06100e5040400180090309041140c0080343d072244900c401521315a11000080115036014080b04488800c16600050603c0000b00032411500060f030600d40203030369407410002d030104140190a003411004003507c43c015a51180c456aa22550003884035040c42c1c29000c0d403150780006141948000060030740700c490b94542c8141111045140125854a03807030300f491007030701d540a00c07070701d04104128200058804148640840f0b01024003c00c1c9100c154030711894462a981c200b1100e8180c00140000d890b04521032012a045000710001c4451103040f6090206500503140c008100b55030640d0100c0e440c020300c40104030300380c483c444696604080f0b41c078128844155140c00c516401100c00d002c036a10724899401085c0c01000d84c8d00c050300c40c00c05c46000e02028580a01520000111501d4810380d18202001c020502141c1881203488642c095461010890402d00940300140b501c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 839243633 1250 839242383 839242403
    0x6040e0109062c06160915020d031118040f140a0c08090d0504060e010941010912020d0b0114090a0e061501091512050a0903050a0e0d 59
    0x1525114014154649403103007003490f8960aa240c1801c150032280280701150020280c1e502c1d80032000200343c2c000d9110384100440040c020909642c021030000321b2103180d41c0101242d40d0344800003000c42c1c000d048280c02d03030305007002401e0201e4415220001c0e10b400450b400a10540880e00301c6005009101c044080d0002d84d20400148400680c8051000003071900c0d2903940340c0d00c081070a600c581d4168041004120107000c1401400c0c880d4001e51543c01c1d040c1004085961030342c0391580441c5400f0602c03c00c50032056495005100703d0040e0706001d00142c810000c0704c3c00b80703e0005e00180b0041c0155240036005c0d400700c5040d591404407258810f5000041c08140d541c40d0601c292072034510000103401a0003010108044102c0392145013188204034010308456100e44051808a2100c0e02003281004600c0c80c000c9a8040e0314025445061a184c6030300e40c10300e024001550503a003004100c011543e02d080c140d100842d4201044445120085c544124190b000760000f035002010004060141544 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 839244883 1250 839243633 839243651
    0x1c0207051806030d020f0303040b0606070c0305012901020a0803060604050d050f0d020d0e0f1f030213090605060f1b01050f06090907180e0f010f060611030304030c080306040e01 78
    0x180d0380c81c0900500b026001d888181c052294140d94a40015807003420981c41000010042940c407004031b50401c01c001c1201d442d184858640025a02c1940c100b65400c0c0d40d2805410f03807003040c02d90b810b041860890003041c4c0c618600c41c0041e46030324034218050301c2d1120000005a042da268402c03a00600401003503a131078074803642000759885a86542e1150648220005580304038000940344805000c00e40d5014940e04040e000d1100c2d140c0a15021303900702d1080254100d54101315400b610a2200c07640c0c006881d104480b0440544001644c46501000c2c5172007001c0c44980c07181821203083c0a99646140d030350308881440d102a400c03043c2c08401d4107502c1c10040c082c0200803c00c1060103200c04907a1268103840307034150f494541c0828441c0301d407080080341c40040c2c14241500f04440c20078418064130040081214402c0c01d48440049100c12a5503c060a00940342c005205046a00002000f1820b40c605541c01804000f2001c50160030b811010001480940e195004920700307200310b5009020742c1603 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 839246133 1250 839244883 839244919
    0x609050c090a140112030c02031c090509100909210504050f0603090d110f19050d170606070c23040b030f06060f0a0b0310140609031c020705 62
    0x840c0c0c981511401c005070110300808201d01031050840303074040c030000c001d901c2d20005095002d00c0c40c03030484c01e000480048a0159070144810220890101c52a00e680150000020000d01030350b00081e01c0780492606008100c1d82d000b4211040c0c45220700c001a024003642030098000003ca42c940d4886200703e00f0030a00a0380c80000791046581c103550b444d208442c608100034a03800704840448540e4850321a02400a206011607504454180140c0300850040303146503003400f000f080040f2003014030001c43e204000301041414500012031514070803041c444840ca8240a80160a862080002142c1d503000e101420001c04010000c0341206403084082c0310031680701220003d82280320b1454140003000908020802480200e6810007400c0c250ba44c800820103403200406440760885c81c4034401003404d01c03011000b0f50045440c0e02803e14020300d40362801c5000c80d5040051409110207202c0e8840545001444a0250303006000c44e03004031421600407440c190695010a82c0010715a02cac9004520b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 839247383 1250 839246133 839246143
    0xc1903051314031b010509010e04020c030a03020912010c08130c091a01030c020f031c1d1b01020d0905010f2d02061f030b15030303041a07080c180d060905 68
    0x10ba401d0342900d120403e52201200440b0b04126280d011a0b0104101da00a61142903511035148008100505292034604100d00e5504000300e07000129500141307044041c40c2020342d0800f4180414002d22281201c080300400b12a0080c01d0a200d10302c40c14140010850905400e5002c1d00c8040010020a00045d020722100400744c0d41c5c481c0820301d01b03c00c8050031407000c107525880d074005800079441c0100c1c0d46001d031101c0c4205844840d40c00c4c0e40d8000071a018842d02a1103903020a186d000f800c80900060481c2c4481c041240180d040d0360007038400000d440d40181c010001c544d000d0030030f0091f80c3e0140b007082d0751018511000f21848000f800c0a001e0121607401451419141c56003140c0041e9511172040780215440d00d035011090100e58030400009203040300099208529002c00d28400c12100082895500183c1e0b0858004600f00c0d09204c0c000381c41080941d00440510f0107006d00c1c144a20504401c0c07041c01d040030001c0c8034402940c202921840c86c2c07a5032a42d8045d508122030b00307107070a0480d260 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 839248633 1250 839247383 839247419
    0xf020414012909120f0d050703180f030605221b0b0423180f01090f09031e030605060712020c0102060114010807030b1917030c19030513 60
    0xd0b4040e101034540200311060018902c9a01084203483c00d03503100100300380e2052501001c0c1040c85001c11100c2d2201007800102d40344440b0b506c4080c0c40b4512817a010b01040d00c1054907801c001504002001481044206841129001900040d079900c0e035042c0204c103017081c00c0707000100c40c40b0007035100100b203900d4881030b101e00d0030b80c2005024140c0b02c0407141441e12030b03403160038007402c660900c90941d501040c2c00e03a80c211000130040049100300702c40c0fa002c00941210000e680307580040040040302c07458011000590301e0060300300700d215901e41d000b80640030003403032824250881c80c0d4180c176564025070010024160045c02d80d600c2d96424605608549504000300e8014051811035980c1940001051410398458070030b9245604030601c01104c3c8a0340041c503c4003050303201e0440d02c0c06600e0b4080d1528018100c460204810380c280b03401e01e40a4a06041c40c0d0b10158020803c003500d46602142c2982001c100c5180c0c40c2c4c0920780390900706c44c0c5010300c064660202220000c00a121507007042a0b03050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 839249883 1250 839248633 839248649
    0x30e06071e050424031401090c09060e100810051503060f090405151009020c030d0b0306012d0902120115020c060723070f06080604091205070f02041401 67
    0x40040c0481c022209401244108403580c52541052084003642c562036064000c1107180010300b4100301160b0301c64544080c1d004111041d55802d40300d02c0c081e070040080c4080d0201c1d041c00580e0f40030010108070342003001b280070f200b045168408255100100484040200402041c180c1205101f401940d82ca51041d2441442184034005401c0c1030706000c1000c0303100e0346c4c00001920480200d03500444640200410095100d4103a08022400b00050300c00341021309960070003540c460721074004071170448401c80000b51003980010010040031842080707810700040444410340603450301000040ba40c2c4c480b40c000d000040c1c0082512042d05102c200418101d43c1c0c0c103150808001c201103030a03615a13074441c8100fa00b0000c100940000701d8409060f100c0400c0c0e82c40c05036035072017201018990400b8142d07088440100000c610411078954403000d000d420000840d002c01509880343e658201d00c02100d00f00c0000d0000c080340220600c50500501c0503159000341040c840e00f540c41d542008504024010b0b886 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 839251133 1250 839249883 839249927
    0x170717010e15100309020a121b05100c0c03020a14130903050a030218090403050d0f051501030b1c06020403120c030c02091b04030c05030606100801030f03030e0607 72
    0x484030802510540180342c0e00c10410300103055a42404111426040038005050704e400b200801602c0d5000750350010210042103405800c201e28220300500c064100c90742c1e44d03140c003c030103100b10742d0b950a800540000714244507818900790301e0091800036840c1e1001e94000704083c000144c82d000582e0644141c4002c03600d0b03403211190107059400320351800c0c40160009a0600c40300300024040d41c0142100f84000c00030303440034184140010f60740e01017102d0403000a0f03c00318401c1d04d02103040c002e8440c40701030235005008910302403a42100504006240ca410540c60b10418019600d89282041e6110007a0f40c203045110103900340400650300c1480f044941100515082664600c640080c0b801140d00d0740d900388822465408002e00080f0207031000001c2c0440c0f000541c02403120f000208001c40c401c000031400c00349010101410180001c04030f80c0665424081c40500c00da004a0750303410f581e4403a2041c4084c0b152030030300b01e0033400e1140e4403580c00d2141e401405038454011b45414507104601c26190 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 839252383 1250 839251133 839251139
    0x3140109022a070605090a05120d021608150a02160c030515010315150801091110020705092406070609050d05190c17040f03050f010c050f0a17071701 66
    0x10907141102c00648040d50400c410034800648550000c0c515050020b280c140f8050f11500016901e82201e102d11000740d103d50045050650180032105502440c10f0f15041c003280741040d003e894406060403070f0f00c0d2249000011f02c4914607907050740d144807070103034072007060b0903082c0b809030b280540340c3c08251241d2046814480c3c0014030011703094107a03076200c84950340c21103180308a071028000343c1c04c0c07403848401e4035400030400d4202403150104090062901141d0780303100703005000744950303011806011034000d07035002c0c0040d40b00d00600320342242d101003884140100c2d070a420002c44503004655a84400006100014480940c1022403094029020384030444809a8152078510a5104c1807400007814840151a40d014210800c0001d0140c5800c60020f0000c0701e508040303600640102e00580f02d00c00041c400d0082c00c004510b030300306103240204203000340000043c100d400343d041c005003034110002b500042c1510801400c4004503054102d5155800c0102e0003800000002c021010300001d900000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 839253633 1250 839252383 839252437
    0x9151006123308281b0902030703020d05060d1a040611192019020406120605101e091d01050109051b0f03070f09030c0b21060108160314010902 63
    0xc540318801c0748100400414650f83c17405107489070150700c042511041c440009054043d400118422544c41d0b40040e40d85038101e0b4141c048960207808a80600d21000d5400d001500c1301440220402810080440564642c40e24001405030200b031011105404254030400c20f9038501054404406900c525005060081d180742040c8420510189281d0041c580000b2441c000c0c00d2203c115400a0004540740f926002200100c0507514000c58040c1d0340c030340c20400709544000b585405418401b038004081c1080848184026115000394410980e030b03942d1410007100643c0203400031420390030083c42150307569040704000344000c41d5804490b0b0590802c0c4000184500200d0b100854064080390440d120718004407092001c2d04829070501400b6140800415050010140101241602c40d070352699505079624000c4603030b1500c1d840f90324080e4203015a507a00103895607800307001c60381c4030b19440505060817009000c200c159101550f0800001042000031600100801c02001d01c0da141c0340542c18002c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 839254883 1250 839253633 839253673
    0x30c03170402030715020f03040b070309050a0e0a050a1e0f0b0307121e02030a060204060e0604080a020d111201200f0a0c0609060509151006123308 65
    0x4003d51540100d24144200819000040094016841202d01c030342814109986140c0c07003a080786400e00400f0402c10205940201743c030020b030000795108661340d0314000300b1034240d51002c0e10344281e294840c000510038189517480101005414205844012052091031004240c060400390b9041c2c00c0000440d0707503040014081742195003c8000c030340b081c00d40343c840c1142c24800c0701401481c4907860708441c1c00b5960411584220f907015010060b600c5183c0038000c1c00803071200c40342ca0300072101800104105003020900300e28494064800c40d455030b8141c50042105d100b0303d044a540b04c00c0070f121051003018154030000d2035942c8003164010040180c11303040110700401450381d40100703041041e005220301c180e034801d81c0944502008680151950b45030825034008070b440e40c0003030b0b00512400010903082504d46e42c02c800c25200d01516141000320081050081038001e4030038907140c01c10999407200d40075014a1868080d00c070101403a45d040e5044084a1641c81691040c5c4900d40b403c0d019100e861131 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 839256133 1250 839254883 839254891
    0x312022106061e030604090c031a0601092610061e21030c1707110f0a030203060114060d0501080d080903040f14121b130b0a06050f040b07030c0317 65
    0x20110072403d81e80316105843d9200800d8075400a413600c2d52140001c409444450155202d6103403c20302c041c15490000308560003c0c001c90400201e10020070005005c03000895003071811848000908159241480c90070440703c80744e030316440c43c3c481c0001c0c0002c21400054030000c1e041030564401695400300c2c005c20348545059083d104d5034448514006406041c0d404441c83c4559903421800c92031045060903030b0402c0c1002d03035055001c0702c1c03044060300c2c0c00e0320b000d641c1d010b0840e00d18007500c2c159001709940c0c2205000342c2111141001c2484140d41c1c850007035440582c64141d09020640c0c54002301e5440b0100c1c0341c0d410000c1920007000c07441822011041d0f070b00ba142c240707055121f09450000c04400200d920100035401070707054035901064600511507407442040070540d0113000d010a4040c84583c4618070114140180780c0450100b035070b41e405000c9011078800c0c1c0380060f2988445050b1030460701c6203500480c001d04001804a0070507800c1025944618040d403103100d81d41030702000d2070780103140441d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 839257383 1250 839256133 839256157
    0xb090102090916091a2b0906091406160f050405040f02070c290d110a030e060a0632060703080709050a060203090d0c050a06052205060313031202210606 67
    0x8440340ba2106d901003049120074429030040c0e007422040100c04d208498150f10181c0794a5240c00242040c0245808d00d400b03110600802003c0a161080004c101c9a54980d0042c0c1000610000412424890410340c0d01500004108000d142c40f14440170b070003584950300485440010a900150000b020907150f0750303840f501c0602d20b00c12403842e01c144040c0d038000e0302c8000300155205141e01d10041844098040c0c4442ca40300003c03420075514034a46066030090510318240e05002040c044100d080000704540801101c400041c45210030040c0c0c11210520406a000131001c100300e000d00d80c1c40004036010b1030b40c507250030100540350300034814042e50901801016a004009205040c10801c108542150040c4001540c154035100046e902c8d645c6c0d0751080740082d401040030824000300040500c0d08a80f5070071012803903407401001c5401404002c0c409241d000087c500141072500a003c806448600c0402c115501c0500e28050002e0303034826002c0503641c40403400040e845040c100c0448003c08400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 839258633 1250 839257383 839257387
    0x5070909021c0206070f080a020105090c0d022e1e0903030e130f020301060c1a1e0408070501151e08060a02070809090901051f03020a030b090102090916091a 69
    0x75a182090340e030b10090803600301e00100588400f140030300800500441c400d4480c82d030340d8030440314000c1c203440000e0172540c1c0f141c20064202e0000d6690440340701d22607606943d015020444522403900942b00e030102c0c1d100a0a041c07407040d44180d4099024014018a5080080009014041260643c82ca0300004000c21a0403050800c0e81c500341260744a02c00540c88085501260207031014144d8000707900800204200b05034240400500c04600e00a4018119044031030740342a222101d030803140c420300051f001c03035001c010030148221b003c1128081c90f04076009011058084040b501c1400d0103100f09511030b01070320189505064044140c04c2110140e400400d4980c5a141c0108000d40c44030700202ca121004004608054403101400c511071510200002158a8015100c0e41000341240990407070000b00ca009000580c5c83c04004410384c1e4003c80c0400103a07480800140c024800da0710701550181c024010402d00019444442034403424079035410200a50710315481d138540850420040314001d003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 839259883 1250 839258633 839258659
    0x12080d020f07020a0e060a0603020304050615011107030b010608070302030f0106030b030f10050a060e1618051804020102120c06012306040b07060621060911030304120507090902 78
    0x5030080e10940c0a4a9000340c41c20b600e5030b000030030f80b8896911001004803000c08204d081e26140c40c0420003001c441c2415071561030720740d503099152a03005088214106192100001c1381e41f040200481c400280b02c02c07210743d1512801c205044050034484c080c0001d0300da074000788407140b0070b000343c031300070700ca4181c40050503424030109801500d42c1b80d42d80d0741c25118000300f20707455080402c0320840e04101d4080004045c00d0803e515020754440d6081203a00d05016420701c05849498000798060345000d103080d800300244150151000417a0380c2c02198010300d504440384065810b403079018080c902c00d8003114a441aa0409800d09028034028505607404c450f004211041c08040862080f40c6216009080c02c261180004e05982054002044805c800b0450720200308140c816940601317100380309254000b8100c1c580c144a510000c4004100f5600d83c20300008021400c1084064441d0040035640c4031a110741070400e40b00b010b02c40075202d5100b640800650603141d88110080c03640c0160503c000441 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 839261133 1250 839259883 839259907
    0x20d05010603210e1e0a1707080c1008060118032a0f0e0a060312080a140f0403110106080708010c031a0904080c0f0a030e01022e0c050c010c0f091208 66
    0x26007165440a40421034442001e40d46208200c03011f040c500b02c1420100400700300d00340c5481c04a400c001925405007650388035030742da140056004401c0a160500d50740d80c5000049802c5288442d07001c400c005402e8001c020031602c40452140141d04c10070500324080034211456001060344168207081c820041c0174001c0741d01400350654040c003001408100c603a41ca903100641e06203001010000140000d091000800441c001e2503440c0d16924002803450820b24074500e00b0410140c002828020151903c0110300800e411070340041c0705140aa9082540d10002103010b890202001c00000745001c1a1001d2010465098000414062300303400c00c564440c1d480c118154486841e904061003817400c100f03800c500c10081a08076511903526405804403800000e49800d00c0304c88031125240c8410710440d001e0034008402e2502c0c641501002c00e60000d00c0e2000d403409e00c1213000e40d07001942000d40c9440c4141d006000490100c981c1e9841000640c0c6c6e032141e55103503440615005140740010030002102e15 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 839262383 1250 839261133 839261149
    0xa0b03130609050a050a051e0601050d140105040321020309070302040507021501060207170c010c03030c0512010306090b0903070b0a050a1e0e071a0f03070903020d05010603210e 78
    0x684125070004005006448035032030800c00000c11502540001038490030000706105c2907030b503c070150090a60151700c0c2c40c1e029843d400140541070240941c4080c80d0203212403400e1000607900008020403417800e16003002405032034802e00e01403c3c450032103918000d114080c402c9a1060100b1005445581d040d58200806001c0140c8000210302c610001518407064102d5818020300d8030f9002041d103036142403c1042c90008142400f142c64001042d10749299800841843c52181c0c90320b8009a0140c03651810303141409000b000203615181c040000c000c01050b81d00117485180110000c0840e03990380300d100350b9648561500240403a401001150120049802c074541103001e800c0c0101d040910381107100703502c540020441c40e030305407102c51900e1180e8080c442e05000d0644c0192642040c80c1028403003280380301d103051000b548030000000a0065115030070b424069075004202c503842c031050342841070213008640804c0e201d002000c0032070303641200704411440b094146030311140b0303c2280ba403003048115 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 839263633 1250 839262383 839262421
    0xa0f06020c06070c270f06060219080f0c0303100902030103151505040906090201081510050706020f030910050c091f020c090901020a090b0f041505160809030105060a0b03 75
    0x2203c904d5000c00c08111041c1c4800c0d101001d009080c1c0500d1407a1140300a0f42c640e5946000158680321091082c00d0380400c1480c44009055140e00300308401d071030100d140703100d5589100003401001c1031800700c040c00440210700544034024072000c850f4695602000304d1000380310080059901c040c1000366a4010380040e07588900004202a140c0e40c0d9a003c41c0940b441c202040302c1d0b443d0343e01d0b601070456070806001c0b138006c6800000002c10354411004030340b2482400000c2d9042c0308022940d81e007042000d80489150300407500c051620780c00d1450340c66603215510607400c1030f00740c2440d0000788070314103001c1620314464009105030310310b2000307003001d00d03c1094030a07040f800c50040b0310390000c054079940501400f8503250800142c0e6040c424800a09100d00e981150014000c1000900b500314045000d46090302c0e040c90390000403451044082c0d81c1441200109410200140502e006101804020700018601a8020f12040c2d54910401c100041603004120103200c2c00e001203040e42491070b01e00115 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 839264883 1250 839263633 839263643
    0x22030807110118141206250210050a09021201090507060e03011503050715021b12010e0105040803060f0307080312060109180906060e070f180f03085809110a0f06020c0607 75
    0xc6102d0003089c1005850007180d45070011034485040764118140300d91181003c90428000300518922a902d20303481c4c0e08244108000c2102c0d001d40c400c4180e0b070030351048000b0840030201202050344c0c0d20309551288842c3c0304540000c80d91a085141c0240085100c098101891112090b10140101005480581d00f00641c4082d03603119200b850902c4240700c2ea84c01580544070a9840f40707132100070030900b900f1044c4114026080f08a0800c5100400000c2e10f03c00042440009215569040125002105075001000e102c10211800262560780e0748012032041c050343c024841030b0b4480c03a1105c4400d0098031101d0000c5c0760441d000c3c85440c0304139044e0514803494030600100b165183d500e10300f038003141e40003540c41c1b60001440300b41070500d4015101895901d001145500c0d504001754a500c9c144003000d41b0742e80d14901207108407809805802084120322000208804440e506100c1400080710040600600c260b20002c500c403030030640756500700c1e007190b03000b401c603801c081042c040c2c2500040b01c11aa = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 839266133 1250 839264883 839264893
    0x3040b010e18061315020f03130f05071d2217040807030309080d0804020a03061e1a03010c0e0d06020903011d03220308071101181412062502 62
    0x42c403054140145800ba41005030404511551801d15852860303d4040005201c3e104010f000303820a404401d40742d1106594030303034100d60313001401c0408899420001c01006070107036a2000c6212200c0d0030243c0d03a0125100c403130021700d0f6030f41c4e00c120030740c00c40c600c400c41c10341284070794000f0000b42d4161040443c0034016400500b416a1904414030300300d115001100032640480080c0409101000b52200e182c966250a4020342041e80104001c3c030305ea80400703400c1035205c641071100f4441040314000804403625007000221062091440708030641562a03101e5428004060101c40c031800400d0380d982e030003c006146000160f0760b01c50007580490b800130381554071289602181168032040b4814601d00c600515955403000e1001d1541c4035503211000750003003c401050001c2054034080d580e4561b405034004440300400310050f122540d030707005803100c400c040100100d1058900c011140070034800359001c03240d04160004840d1590b608582008807241c9429005044400c84010314054182c3d80c015a9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 839267383 1250 839266133 839266171
    0xf0304230a02040e010203070e1519090510030e190c080313060906080c07060203041a0a020415020109050622060e0319020d0c0201030c0e041a030c0603040b010e 71
    0x280d06218800c000345604000c10070001d50416014040700c40405800861462904035006440000d1350040301e8040c10801300d2080c42c2d41c0c285402c40d1210054491030814522100f0001051203189000b201c3c0182082d80da00c4010078060300499076454500350242100b001000044508a00401070564040719609800551540d06000808030180041140d543c49814403601504400791940104100300000042009070350310351040d94141e50748500056600c1d150b604040c086480c84101144110301100b050080e0124a58010700490b0444494400d000c441e1342e206a08036120000058050703001940040d00900c202d00c810300744280b50345500b980c040c0650720b608003103918046035803503d584005103084c2e510661030104542141288010901d081424400621010402030024103154907600c003084a20301030040010394220103401084260b108020b81340a81c13140a100034000c0c0146000400030341000800c83e0300c80c42d044100100e1503440c0404d04d81e8011030050044001c00409800e01c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 839268633 1250 839267383 839267423
    0x20301270b01122f070b18060f0c1210031511071e080d0608120406020a0b071b0302031306030e060c28031401050a0f14030712120909110f0304 63
    0x2007503003240300c01e0598580300b807440c180e180c10b00c0180181e00b550580f15800204a0000101a54042a2708000c0381058407039100e841e101e405040c071825000d040e0401000100c0c01c074482001c08590003075907141a84d06034105c050b41110049044c2038403164003000400d0200b2800003441d5586140001e00c030500020617102d00030541c1043d81c019600c0f6482d1746003044205002c000b950328281061010901d01fa1400d0400f0b50340b044071540091501c0004000181c0b064000d210305d07444810540d0100040c0307100742c50000d440f86d02580d40070b20007031104000428000d21070301c968184020305400a2400783c94002035445190007042c500c0c1d0f040421200c220a22458051725031040e48c80f5901e012440361810a8501602d078070580005000d0000408208004060304a0400403240c440101c1e60091140d00046030800d0000d400440c0300c18a1803404030100000c59003d50f1841003950741e417820041e04c890074801501d503685006141c904003030010b4007051059100568100344070702c044101d101100750740 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 839269883 1250 839268633 839268701
    0x304030321020324041b031a060a03060f090b030d14091c120e100315050d083606030601050c0604050c100c121b0501020301270b0112 59
    0x1040380102d003c1840d29203100c0000c407413491311080840d41803000000042a40c1d684502202088082584405000d180c1c5da1407840c60403d68a0050901c0359520580c080140160000b445140c20300004a480000d04240506c11511400c20050160100309000306040780c4241034803500307034140c4000f0044076a03142d440d01006a94110040c0040f80907807084d084c5114a22021000103007803000c1010440750036620030040400c2400a130400150341c45620340c41d03207a03842080c0c11143c0c2061080d0070043c01c5c009600c0260102e0000c81ca01c0c46e002d0242d9860258049110b200c0c0a28030120301000000c0e82c0c94200051035002c2e4061400f641003040c04404075103001c0d0280e07030075201030700004c2c501a000d0510b504602035903038982c00d113142c520b1100d680d001420b426480f207a0082124207440c0902e585a001c40b004945030308000295143d5868001c1110010090402a80020071903000044088268016244420030503114003060303810710840c19014014010800000722100c5415964415403150 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 839271133 1250 839269883 839269891
    0x60e0f010603210c3815040c0f021203070c0f14070504060311040e03090907020c030706090b03071d19260703060f020904050c0d0c08070203040303210203 68
    0x7804050340448626400d00c4083c10000d000421261444840100d2000c100000405420f0f2206071046404401ca0f10503210408a0350070b20780c007549003407082a0542c4115500d17041d80448080148100c116020344424024a04040158000002f403801c1c41d540d800146034441003d04200c82500c0c0036a403a40622031128604440110781700c0d200f02c2c00d280c2e0400261000e000261420400c0314110f48800880e030908100e418440e0340c403803020405000050080d50b03045031010b802c80b0781070705080d00041e48070b007111606540244601032000541724443c4c13882c40c040325024200c051a50b219904101c8100400143e107c845203400d03102000145c41e40401001415540f0707620482c41c60412180c4240315115121113100032801980960141e00d02040c503804683e8440400a00c44400114000280c042e40888642c01490030080104441303954000b408218065101001420300044050392060016104600103078414401440002e0041c03841e09540b00d5000b0310494422844000c90043e40d0080b1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 839272383 1250 839271133 839271143
    0x902060a03020a090509060604031103010b0d05030301080606060a1d1212121021061e020a030b10022e061403070909020d110f03100b1c0807060e0f010603 68
    0x580f601001c1d6000d00328401a0000301d07504011800c05400049580c040d6020180c80032003281007401d00c99800350310040c20b508024008002001c0030b070400f0364503a00244510140c0d40940c800244062900004071026540d480c6c44a17030340c0c517846e40400d008004c816030004e5003204c40b062440031041410000e00ca4206205502c003981c46807140d4080e40a9000603140c60312103250340c01d05001d2240c42c440945844800b00d1444500d41c0d1480c20100044e2001001102c3d03c04482500c20401c15a541c00030718002c100f0340c03024402c40000009024404071180750040041c0c201050030840c0703d07080385801c4032420b20b44150071643c41d9000d008200b103031000e41c402c108801d4039044e0300e111410140441b00c02031510307000801c46034649402290507c89500f800030441c0c403041000040f1580c0750240b240400704094111000f1080a2048070300408441c1050392151002419540c80301c05490300102c50180e0105141c0d01b03000182e540c080c042c3c901c5101d040307110b000b104600c0318629000d10522008502071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 839273633 1250 839272383 839272387
    0x51605010207210c1e171801020c0a290c031215030a121812050d0809070b0a0306030803070e04051f03060c020321040303051501050a0e03030f0d020c1902031c02010902060a0302 78
    0x20301f0700224501d4280020b6419904036221071100ca0741c9604100040300e14000c0a0f60500f0072038000c80c034414800462000c49101d0210b4500080c0754004040c260140ca4240100e1140d101c4003401c19aa020240b21958558825000c0ea8001500307200c001081854500b05161407824148400c030200d00c0c190880304040220040c494280001080300100ba5082e80c2001022802d080202c4d0f510350105000301001d00e0000503507401100d2096002c2c4000b0b681041e60a603c900701040020300461404035032a10039400d10000c101d83c4500c80f40940c4c08100b0749a070310401d0034a1542c542000d006052070400941c04240558032020f20300f035503841c10407156040103141624080c078000d4100e40001d0b0041407010a2410711400c04e980210449485501034181800201d04000c0080d29512580716441801400481c1000140035070382c000d015404a03132002d0f644600c511005124400c0e00300140a94554001a1160300900141075928241146480041070010890b0081a01c1e6840002071000007680 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 839274883 1250 839273633 839273647
    0x10315031a07050a09030b1e010b0307030f0e0312190c050309011103060a031b030c0602071406090f09040c050409120e0a0501021c051605010207210c1e17 68
    0x1c010600d5200c0c4041c1420b03410088000e0000b4034026040c0801050000c0035004503429120904443d611200074100f85000c42d0303164601d0752819002030b9a40e00101c1e0410704440310b000000d01a0718244041c0d4001181011500e007051420313010f004c4c0c142c1050791440c11041012034414011801007035890340720756680e030803c16078050845644908008441000388280035050303813032031549412217410400314113080142d80304503580d00c0c00c9a44000d2852074000000605185c010954800310707080d03281c141c140e0070140c40500070684510b811a42c0d1207a030340d804204840c50000e04031340c0c05c18000c0142c5082182c4400104040f03840c0c86d1410703076104c5641010701d4a003030b0380104481c16120080e1200780e001c6241c580040d50740d103140e0886410b02d454003445a5842c43c86034096a07035000c10503410402405003070070702d14003e60041ea4181d50300b100200034542030740006c04044055011036545c564801da6141c41d5a00c081110400e141c510300b00d10b020100114004003450540d40e040b5050703540c5e80b0b00f5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 839276133 1250 839274883 839274923
    0xd060b0a02071e23060d0c080712021218070b18040f180206090310050c0a0206070918180b07110105061203031f0f03050a03090603270201031503 64
    0x10300d0808a1550307040c002c002e02c80480c0c011071344410500c400b849050007011450004140b80200d401c8040028a03103140d880341150710507a068051a0a0b8584040b035030944e5144038141d101d03800d840444001341c00085500c0d8680e41910214071481d000c02d41c1d503500e403641c85001e480d6200b09402d804800c25151600842e20f0248100c090180714007030308001c4200c2c410901440d805000300c0180c400c2102281d48001e42d1000d0010040c561400e440400c1546856040c0894580100810b030006114141c00200340e603020b8510b901c2910848003c0c111441c2001e49d4010280c0311405510100041802080c000240501c042c1802540d03240c8600b00720410001c281030845a008003520b106a0440c030030740310741160100803a600408802070003910050301010040300e681c6194401070b9440070148000061100102e503080c0303401c2c803031740c4c91100041d03480d00210b098031648012102001c25003606d90318021815a80307070502520606000c10041d454982c1c010030002183c0c42501d2144d002c940200001c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 839277383 1250 839276133 839276159
    0x601140c010209091501020606010e01030f0204060c0b0a09051506061e1b120703260103200102010b100f210c390c08030f07061b050a03020d060b0a0207 67
    0x41c032101854005d100035000017903640c44040c052606000c12814110203a034031903000481d515442c648103640d01d60360b9500007400d1301c01008080d42c402c448140810081c8906005107010681c2110003885102c40380c00503d4140c58010f0b0900394820300c104401b050300c2c41071002040c0100c221010321522456511040c0620304500b00400440d13421150342c8405580869099801180d010b18217400045941048021071260002d4006a9509410000420049104040803552200b080030a00640824005a09844103c0e02455004025480049070940714000040c032000051401c500d038140e02c3d40c0000a903000b0b140c100c0400c5501d646400d1005900700704503000508a408224214108882c1d0041e141204011000c6000481d03210790028485010b04400107080a80b050340c2ea103003110f0f0f4140080d07034840b403000c0341d116040c40c1c0b1000040c1403080300390b441060a5250540b9015072100120000d5000074035a040741c076a12040403e55034900c80150010040b1600200b01e0941080c00d00c060071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 839278633 1250 839277383 839277391
    0x30c160302030d0c0510020a0203120c031b09010f12091a010807060216060c1a0a14010b03070c0605071403101e1a0d0603240c0c0503030402090601140c01020909 71
    0x80241000b504d80062000112070217200c10042d001070300d42c100054224114410221050100c016420074401c2c141e6031400214080c550f040114261484404980485809900030329404103681444005290780a0f98040d07180c5c81c218a80000d03034a0030759a03911140482c03e0000a883c0740e00100510078041e003006560007411250004120030701c1c00501440c0d0004850040e0300401212a41003400c2000d181b50030201003c003145810103502e031005008000304005a51035110100c4d1070300006600c40740702c003107034050314160740c03480003600994a52201904014200c00100000b0085500748151342d400618000c10301e0710279082c841840c111806148a0000302c002c0425420500c5c200441c8134529011600c0d05141d1650580f5403103c0840d800c000c001c0d50b80060014180c642001c1b002101c00301380b1410440740d009040001001301c072012039920011590090280c0e1041001c1000740ca0321600f001d9002d44140340c1143c4000d00701003038403c1600002851941d980d00424200740610300f40c0d16140e40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 839279883 1250 839278633 839278637
    0x1030204050c0705190c171606050909062112030f1501050406180b0c1f06060e04090c1a0730050d09020a1701051e07050a02030c160302030d 62
    0x4103180c075126a6110b21540e030039121800345d000900300c208042e16018000400c100303451000c2d0600c0700684503843d07111307c540c80c0c03494143c400c901140301409141038900d003800252a070041a40d4800a00042d0042da41c0d140700c0c00e40b026920300710048400c1150040c2c80b040500d00b81e80768148226030900c4024080d0401440320340f51159003950342d038050191821180703549012688620449401801e40d50250881d10060000003510000000c00050075164507030303000c44540411030820419070454540d401080000380031924511102e00d0550484a040760281c4010b11440d50345896081c1c00c82d8900c0da030135034034100106d41002407010030107030540803035410002d880941070120161046003103104030781024001c000c100c0d0203071405250b0013004407980c041c084001e03d40c0c55104140710282c0e0511568042d6082c00d0024002e42d00c4070540003d000710104584c00b036511766000c01e8445401c100000c400b184802c1c4840340483c081004940145807400c02802000c0382103005141c01c4c40650006602 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 839281133 1250 839279883 839279887
    0x1701140f060c03090907050408150402090901110405040b0102070503010c091505160605070c050a0308090d021902010c0213020d0f0b0906031c14070510060614090904060e060f01030204050c 83
    0x300076a000320407113040d800110b8143c04030b9550f1420a803010b004c0d0390045401403082c0c0b0002500300600c00c5006004a000319403503812503450080380c41c02d9076900c9421188002c07040c4020046818541c01c02e00102805005482c0ea90342c80388042421a40c4c4219201c0c001542c00e9001c00c8442c0e400040c2c004000e010780380c01490a40c6a5400080104203004000c042d244ea031000154000e10814081e44060303030040586580010a040041c241d8005441c00007080c01081c003040445400003a4415691161212603000f503072032034006440340021007400b83d03006240440c207a0780d000315502c01000c4d0910340c05000640c0e04022680d44003100c4031050200e000d00418804d0000716a8005054146d50052003031042002c019014202d1340f68042d41e500114840b00428410100701c03000c03441007090300b2040010040140c0d6810115401c4011241c0380b02074000801203650542401c0304515406401a00d001c900d0010580800d403918004803000044408100f0060007140703483d0085903008a500c819180c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 839282383 1250 839281133 839281147
    0x110d060b041203120e0303090c0a0801090b19021c060312030c05030f0703020c0d0224060105030106270b0901030c1d1e031912090b0a0f1701140f06 65
    0xc225042880501404100f0b007003604c5601c80b54009202034104981501d403a820304481881e034824032403921601c20401c1c0c1d0404070759145c0510400032910381056035034245850b0b540c2d42128a07501c0f6691582d02c1c80d001c0000d0060880032040d5984004401d03040000c840d0304c3c5060000c11080407030000c1c020581081c2d903000301203500c402520380010780c510100d48907440d000c01c168002c1c0300c1c83d14440703124000e0751001094103030080380f034821413211050050402100704e0f202680d07604041f10001d01242081c00144043c0e440b40b049048961038801c0110b00042040900b81c045003060b902141c440c2c2000170354160b440d40d050280c0381c1c0c204914103105080c049214103c0402c1221040e07640e00405001216455505116002c00310707400000d02921402c07002400131056603a040d40b01501d1040740a08400c072000e111707243c200101e03040d036a0342608111400c9130449031841105401c504006803591080400c1c055501c029000b00f0022442d901030b1000701040c0205401e2030a01140b2a401c103008607 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 839283633 1250 839282383 839282399
    0x108100b0d02100201090c1403060c03040f2003030d02181905060a02030f031609081605150d0608010c0212070803010302011407060e0a021f0e0f0a0306110d060b04 72
    0x11070507412543c00542c1441154200d005242c103100181103200401c60004d8200c01950000241240560503903500c2d94413040750040305d21080d17400400451a022a0078003040c1802003d0441c00c01030700320030069141020000e451900142500c503642d550005109070840311841c03010103803440c142c403108081c5c220101340100f0240c9521400c3c1c0600d000003030b00c504a91081c011100703a001401402c0351242001c0b1440d00b11501081500d03000315072146804125454002845840181c2e400c103203c0b07500c0e007801d0601420740410502084c1204060100c503607600024000d90700500f513030b80000250410350020091038a100942c02503555a400c0003000003260425040b641540d4081c00c04c0b07844c80c4044503554035144525440500301030303c0c000c2d11181841003c6a0303501c8090007181e2001d00c00207030415441d1186070605088000c82d450310102c40060400d04080450880002c20000d40140e894603840c0580790303030303200300c2c48003910008082030b0744522442100042d0410300082c9d41068103201c54 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 839284883 1250 839283633 839283649
    0x19020a0312020c0106210201021203012d09051e011409011e150801030c0603061202040509010b03150417030115030e03040b0f09010305062b051903080108100b 70
    0x161241c4030341c00152020343d9501c250800b0000344400d079542404540e04841d00d81c030040030024228010b0040c0601000c032001c1daa41a203050f07600301550301030008203904580c0300245e0380c090002000d16100000141c0070000303104141c03207150b04850f0b1541e400b07040ca00c58051040c0c140c00245044604210310303420740d140c00d8070355419a46404560304098040030a00840904158080d0600d41020349011500662089002c0d040701e100d0180008150b48a1800b076050384c5650145081c02441110b0910151400b600041d8203d88030400001c0c000a0780400329080114900701d22198480c4501408208144140702920403442c0c000041d003554100100b4450001c604a61201010784600c6003d501545c02c0c4110380003003c21640c620f903035614410144c0c5017500003180c0319010900d000c0020303c0606040c450252052242c0241f0001c0d801c585000201d5840d100d40151148c2c400d0b6241c04010201203500c1111050003034452120130341c90000c800e071600d0b40000910748503a00b02442d02201c1c2d02c852007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 839286133 1250 839284883 839284907
    0x20706020c010810050d120306050102010912271e090506010e0d05070b0417190b07210f0b0913050c010813061d0c0103140103081303150219020a03 65
    0x10f0309010588603d10711000e940101c0d00410342c0300041c40b00350010442140000900c500040c2c40c240541030b81c03540160700701ca040b18000780190540c10744104010b4495040440f6403031780d080c0c0d00031545444c0d40040c00004401e0b04400c1024644155148414401180201c02080164000c1c0454038000000901030604a81d88a0241003104e20886c20000c1c1031011a0242580c1c800d1346031100d5540d4042c130300c2918400c880d10111300901c1503030a04d5906420411082680085104030640c9500108440e494103207101240603200b8071003043d4651620740640903081401c9100440d880700c54030304000c01100702a10102c06040406140000554041a50301352640242040e0324140c0c0c03440d58801d0b80c1310100c40020007003440c0480211042e0320802e24222250b100900700e0b00c4081c03040c001507040350309081c10008c40c40c01000042001801c1e00005280c0d6200c0b9a6049030213030390b01d0342d601c02e08044600440685c15000308107100e01861030000281d070882c0c284010038080e0b00c5901c4c05401107000c12 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 839287383 1250 839286133 839286137
    0x807050a0e0c0c06040615141e0301060902071b291e1612050705060112080f0c0106050108060414070311090a0803030402150a050f160f0305030402030d020706020c01 73
    0x800209284444015980941c90403c10743e41d052500e45031070340040c0b03803050003c01d4406015201103071021507140034400280014043e03c254428059246800070301b05030200341e15649501d4041062807450002d4004148950520350004c1d0300e04003000e0240001c5d07007200c014184041c0c90b03c04280c5071604500001ca03030070248580d4540d00e80c4205402c820207501190449030001840d07441c16a81104140051400f6409040341060355140031242c1d4400d9250103802c96001d14014001303c0000c1d10390b041c480e84a400c034540b40140d00301848980d80c1000c040c07a602c1d03075500c1c801000b0550f0400d4000c0ea02c000215410030004030900c0b0304120200c4080c041408046c1d84003401c1c6504812801103442411004114500c07003556003210390b68950003120101d01600d4545010201d82c01c981094444900003625000e05101c03107642011010f410142c81c02c080355103c03510a80c007150847c01d103043e4043c02076860590300d103003900507d807400588040e154115440600108000340d030214211496150034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 839288633 1250 839287383 839287409
    0x21050c0f0313080f070311030903071a040e01030308090120180103090b09070915030f0f030504031209140d030219111f02060703050105030607050c0f061f0807050a 72
    0x11016444490700010b002405450001215007141d00a0000b8080a500c03959079aa040c06495500c140ca0b405480b0200d43c05501c0643e0612041141000040365045464003450801d541c60034680000c260a90007a400b1035004014811114828025907907050440405440705840805098205114200c00d00355420b0306803210071081d80c480e4000303c09c00c0d0b03004804056503041c0600084c1c0c0340d0016116910002d0700c1c141f482c0c0c0c08400e0100304241100d801100e25036880000745c0301c2d22034407040c5142c05c404010b4100b00220000d501203441c0760400410360349102c0300e5400e0101c0550079005030312003548100c1c101400b0708000382d4005111258904160f0030070702000c41d5450959403940d18808000c0d484032948a150051003800340c002081e030f2681d2303801c507903594495800541c1229420f00800360140c00c428001030318140158020f00601c802d8100b120000424040c040b42452410754501d1018408119699034030081c180b0003101400d03e070000307021070f1880c0030f00182c10440503101c0d402d408290 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 839289883 1250 839288633 839288641
    0x6050301150e03010c0f1206030206040504180b090a0b091519020d0e0a020906090103110121050916300203010207050601060315060905062a070621050c0f03 69
    0x40740b01401e21070070010f030090104501d07416024240c801c0003201a00000c0d154800c1400000d2140282e204498014161034602800c080501c405003e180389024045524603980304001802e15016070b111b80084170290140d9421880c0181c0c03030b0304c4007508000045d8410300d16155000c01103444a90856441010502114481c00440020380503003032a0114440c03801d403003101847c00c0415a6500c441c82207600030a5903071070800b000350103030081c0000f4141d0a403405202c41203501445585403030000c44540d83c10b090440d003240e50b0980d04100d0303203c4010742010724a45204070446030104090002c843c03040c201d00c0e0b81201c28188042801d0140004059a0545103007503440070b60480d103805402c0815070300d8a42e141c00e4003030058800240e241300360004441300051a58481d540d200c0640d4401880c2c54540320414948200b0741030b61044800d903041c403031983e4146800b02084114010001600c0e40b212114107a00301c1800b8132882c688591389103082c8810810654454012100d0700c07080c11151b03a4580d12 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 839291133 1250 839289883 839289887
    0x120a050f131b0b3103080f07120c02040522020904021503010e010f12120809010b030613030801080705100c110a0306060314070e0c0c030d02070305070b0702070605030115 75
    0x1000744510310703000b031016002c244100028000d01036840c0c076100c410100c501d10805803a1200c010b01403140d030001e9626050000400d400c0040640700c000b940020705046641e224000700c02c40710042080814454292101182068010b09a00c074824800e00c0f0094400c250782c141c00b0640c007020080c407035496080020110740c0c46503100c3c03015a802c10003490300d9603102da1740d110189500b0b0040c0040015040c03000150b482c2416440040d1030ba000000700d54031150072034180c500e101c025040c040c05548511801456071030802590780705820094002108000a003001b502001041e000203810b504100301c00d000a4840c00e1031071031649441d1030b02c11403600e190304101c10310104058041c2d6100240716800020f01c01c82d5084030b800e0f0b82c0201110078001000d5800c040d0340d044244901e0b0041c0314404000ba0840c61114040e14040c0c0409040e0381c5070130f560b00a12401c031707448420100d01080b00414440103200b600d00303000354880319500040a04074100313400500940014400c0707110120102d030256064034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 839292383 1250 839291133 839291153
    0xa29010e01140d0e210412030c050607020601140405012d0f060503010603050c1c1802300a0b190e030a080916210521120a050f13 57
    0x940703140c010f80c03034103008101440500240c0300c00260f188200e84078240300100b41544815246683d00410f8a0689403008200d030308070860500b94144200007040c0e03008660248452440307211039501500c0b03250304142c2001c0d8000c40560350140503c2c98400140b01c2e90582c0200803041160301e00554080b0b101a204440c0f4407680394000004800d442d200004546411502075810b0ba409900c060090340d94170815407200c1d0082034007814044880d501001c40e80d488036413000356041581200320001082d20b8001c1883e00083e08a6903d100a400d503d10241c80380355068112117040a601a0511004940760000a031202030040e040f421003807144018035038016404280b00031b484100ba01d48800700036801612294080720520920302030011000503c019644240707040c0c840980c9110140c0c21221191075004084080468462089008100e41010b03c00310b40c080041c90048d685644001754045070f04003007000b500010019040900348600580c0d00c2c0d14455014080c3d4028800345220740c20415124 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 839293633 1250 839292383 839292407
    0x3124111c0906060f03050d020d17060d030504151d040905030304140c041e0b190b130e13051903090504050604060b16050610050a030803070c0c0e0a29010e01 69
    0x3ca01304c50000001c2000c0070807115134481b002d800365506d5152100f0140c42d070300006480c403c0b5220300c03100011043c0c6004020181401e00a181030360034151034680c2090800c2145a8050100d01c1e000b03600070b0030f4641e2a1452316001c00944080c0030200b038039a07440b96a40005040100904103030010049010410007005119080080c01841603440200300300f1901454a062180c907a4208664001d981c04c03d12025a221056041d04800700c91410868080c190415005041c1070400d030900000c0e2078001d0001c1500803014a1240d84a001d114540070740760a21000d0041c0c0c009246100b00b20202e6041403511084960680c0c000c600c65a80170300090090840d900302c10101040401c05440403250b1000b00c4c1403d0344900200d50a540300c80c0c0030250001064420540c1c010345c3d4220900014056602070340d0082410305151040311847ea0301c400080340d864105180c6240c100b030801400c8441c40c0686190740d01c045480d50780b4040c12014910480840403005414070100031140e02c3e099118204861030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 839294883 1250 839293633 839293649
    0xf091c05060f040b130506011406090915120d0206011202030f070608090f01180204321006030c12110f030103060c0f05033124111c090606 61
    0xa4501a60480190181654260b4150103020001020a17402c2c140d01d1007425040002003038240e2908840c0703507100382007e64154200d032013801007403081d44800c0296406108080c821280f00304280d010720040d0709102420290a0f44501804940e035034000c564a41901e4104004039210b01701d6001003440c0106080f907240c00b41c130401f440000e649501002c0d42c0c0c003515020342550291100210484e00b0707034280d5a206c1c14114143e10112005180c264401d40040000ca0f0091400d5424000f42101c0b0030002240507600c1d854030310400c8840305100c3c000da40501854201080044800000100130782d550310410302410b80c0d1481854910402007059414414050071450741c0ca6840c0d14103d009401103001c9500454083c010303d4036014051815240316079040c030410403070f540141c020164010303015a04100c0085c50070401c0d03004102e84003490401c40302800b06490402e400c050101b01144c100c0103028800240500c103d500704d81c446084152105000760740860003140700e05000340104102e60100700 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 839296133 1250 839294883 839294893
    0x70212030a03060501031b02060c130b0408030d06090e0604020d17040305160b0a1b0804091a03070b1e0f040b16060501091b0c140607030e10020f091c05 67
    0x761050741074010b281500d40070b9900740b259000f030380340b1400510b401030641000358201d4000181910034420107040304001380200c840700c056598600700182d51042e041100c083c1c1000641d106602c1032801400010000038034200310440004041c283c41d00c6020700000d1141960900c00d0302441801c918490040b80c28129550b80c0307550300d1606541e1500440c00b0048480e02c1003800007010070403003080d5090500c940d00c2e0ba001d03040c084200d01c05030303000c400800c075081202800045146107192288102000218603c009404195001c00d0f217003030f2043e401142100000c100b4044115504c1c66403825803480c6100c02500e85406000151030b40c001c0d500144100580414014155840c000c0f4014981c0d005030302c10004ea0341c0360341c000019030f0001810b5039a8031107001d8400c10788910598100c1c62141c0100e52000ca0304615078400d070f081c88820381c1d1000000b40c0b690707040d125a0005000c900b1850b1012003046107840101c5440510300d0013614041442168100d01d40080e00c000c3c0c100c5c103100d0390391241c00c0d16 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 839297383 1250 839296133 839296147
    0x70602070509010e01060c03050a050f12090c030a05121602030a06060e0903090105070b13140607030e03070f120903060c03020a08090c09060f0109030602030108010203010503010c0f1407021203 85
    0x80d9200124070440d441100c080c0c000281c034030820b24102d8140d654503507401411807007948060320036500109507401040810400c0a9181340d003100a0030309520b080002c1111b80c200515034a103000744c080c981c6486500165104400203c000442d0a044485041e08507100c0c075400714402c03501001694041d40500407180401c00b00855680200280c0300c401100e0456034540940305680c2c1d00070600c00c0360100d101000307004041054080902c0e40061010902c8642e951950b540d201010801040e82540d42e0180c000c0c04070306500345c091501005002002103050601755100c080e01c060031000040c00c01d044807188525030920410405000c1c58000304240070580d1184030080081d40300303441860000b0340690105880540206207070b44608002860484291148000c0103c40680040a00d06001a0000c0000054500c1c0083d6008101c01e00005881e0341c584000d050a40d0340c800c00c081c0030424503200700164180c0212118039041030301c0103031035241c420314404141c5070b82c0071600d2050039100210b104 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 839298633 1250 839297383 839297387
    0x180102091f022b210c120c020a020609040b030c150a080f010b0a03050a0e0d020109020a060521071202030a0c14032701020f040e010e01050307030b070e0d02030706 72
    0x2880301400d00c0d4211040b00c84840c08070b01d4080180700450500d03100e51481c000b02d05102c0c11040100c6801e50041a0b4494804042132084a00c00307559000800e8103912032640302c2c41c051258061503030260001d0201000b00340d0000d4818824047d50700e03c5240e039509040880e403410440b6215001d07004d03107104144054200315411a03080445403100087c488000180e690070b500070101d04072689400000e06201040d14140e029040c010f00120b28070340d441685410b00304080000c00607603034071074000142d11550f600500001e10215009031040c86020040d180f0201c04540c1c002b50046c050150802d9070340c03100c1c4002c48441241d003481c07a010078008801c0c0410305800c4d0703214038441903140d00d542c0b242c030000e5112550203000c102c82d01c1540041d200d90000c4200401c22401c2c1d03242108800051400c1180540c10605401035003042c10f10510382401844101000e0803454090001100188622440c580d1107555100300204600200038101c502084140c03621004032083d594020255000b9546500d40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 839299883 1250 839298633 839298679
    0x110a0f0f081b061014040905120d0c02060a05072718050a050603010e0613030c0c06030c02070902090a05060f0c0d0e011d0915010c08040b04050406061718010209 71
    0x40081c0c1400f50002062014503000040c078211640e40803660b0005204204000c001c7c0721052064945028251548210954040042040768031090000940e0003a1000c020b142070401004c04480d1458101030055554106000403450400c031440c40e0074241441d0858148464a6404071045140b141411001c0380d0854006030311420803c3d1080120b41d985e4802c050907220b100000080540011010a07842021503241907400c5000c1d080ca500110000d54449055403046d030302001c0060f941d0203e440215038103000005c0101401c400540c1403006520004110004600c5110703c60103000404401c40501c1d00309480380910060140d807209100010050000c42000c10341a001900f410184407840541d120301e40c00010b0003621f000e40683e034000d05111812a811049070601500300c07209400904100020005840209402510359203810144404d4501e6070700480240440c014804c110141202100d03030380300c540d59601070030340140c0c02c0c6030380e009105040343c690308410030950091904400b406 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 839301133 1250 839299883 839299927
    0x6160314180f060a1e0c0b09100b1504150e100c0b060406030b0a0b06090a0305071e0b0915160501061703040605030708190c021606110a0f0f08 63
    0xb0320400c480c001c80d0030030480788185054400403600b6420440d40c8024031804a0b11900158180240c00003072548802d00006021141c004099010400181c0329030024002c61240120560b064500060302d074041c559980110700a123030800c400c40700e088000a2003103c070100c1d0040040d02c000e0304c50b40d00030030043c0a507240c04801c0e00e00d1000400802d000f41041d209040c21030b0340050b44074402d9142e1483c60005099400761007a441174090000d0099584c41d041e03400e0003140f10784028100c8524103c1d08a1002c1340c89401040c1d14259801c003084a800000225004401c089491000354180000d81c08810301031117a80415003803e0101c92010402c1c154406000d070340300910168041c80410200c169a403242c0c1c007400001070402d001081c4040e0144607170396080720105084001610181c2e40c032404807420009050010391249c262600c852820480d0500502031601d800310040e0903449141d07948040354100241044041c0c54000c09021030a001c030b0030b07400d501440540d0b0f14168031003041c0c40264608 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 839302383 1250 839301133 839301139
    0x1c020d0216050d03060b0d09260307171314161205190c14030f030a0201020a0201051003020307290d02040509090c03060c0d0608061015020a05070504020706022b0606030b0616031418 80
    0x34000c8041b28618cc0d00b052180d004080b2807003040d038943c9d5400310316044012030310322a403080150400d0054003568210000d441040400c000e4482030342410791a0640304158100300c070704074400d55800709a0900103c42600c07090b84014442500c22004617203021020000d22140d8000428813410319541034006200300700969000344040d44500040686103501803000a606510400c0c04014480c2e8011404800303550642040c40584a41440101d89a00501023540115030000c0d007030000e0718100c03440b1508007650340000c000d242a044007080d07584102400b14107a101000c03442040c00040f03a0004c6018198031001c1d54061b042c580da079020094402c1c042c0710042c201d0300325259070940c0700194074020541c10000034414203251030700b0303c4001d500c503441c240c1e031442c0c007003001400d024101c0302d4400d03003181000c1040403044c0c551000c58040782d4a030b42003d0105810300d9014440c0d40d0f580002e84840451584100001d08500d24060301c6900c2081880b8401c2d00c2d010400c0040e91803e001c1080c40e0040613 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 839303633 1250 839302383 839302397
    0x70f03030b031509210d0c2f060f06030f0102340503041512090506040c0b120f0624070c09111c020d0216050d03060b0d09260307 57
    0x1104142083e020100c0390380e1030700c0d44900240d01c0e80c403401ca01d8000e250505034040b58580305201d03050500f6101e8400611010130506003450490300350004040340000e001c0c46007620284c412035500c0d5100c0758041d0184101c510400c021825640c1d0500c81510302c92403010085685101081c11001001e240c0e0301300071550b011003032010030485011000f0741c260030340c0b00c00910302d030600340302d03101900c0010545400704005518060100003152849041079071409a4024100d5103080d24004c0fa01103d160840350a00070706012200800d6030341f0130002d0700100d10490400c010359030840441c8840c1e07a60403180315000b40788040704004506010092003120b00503100d80d041952512034407400d40d505514200401181000000480d40641101c1100701000501c058540000001d5510a83c0c015020b4524040491500b03402009010032150790040c030036040900503645417041051440c051318011520003a1144200010402d181120034100f40f4204580c0120198202c2a500d072600100c8084003c1007174 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 839304883 1250 839303633 839303653
    0x110a05030f07090e0312190506120a02090a02130308070614060d0308092e23011205072c10030b07031509020304030509130b0d080f070f03030b03 64
    0x400d9220a40c101c1a0040c0003080c41c01c040f14000b000c0b549a502c1060200b4000a40318030200004503002d041d01061080c046038a503a081d40c102c5d0009407400b841303a000c1100070603440d50046905001c060701140c6004003680d030030703006101030710441c030380040da070720070102c1c08010088103001910100b03006002c20402415500041d42c1e40040948543c0e600440840480b80080d1040c200607a00079452826500da1030040c015441e001480c20708184000b030142006103234020389900c9102d010100e80d880070b070212007520351030380c4aa041c103001700018124441d443c002030003000c22004d0003c3c00540912403003014401604407900a480b40c2004100f1008000300342101d9204000400382ca07040f140c950703695200e9801c1500180300c041e40c5101200d21500300001c84070200d2000d140b09901070388416540785006420800000d0b5882581c16a0700d140050915080d1911034012004550080001780c0d141422000c80302a0b000d0a20300900d00b06c0d00070714034410154140c00030380341d5000c00d40c111140520 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 839306133 1250 839304883 839304889
    0xf08070905011a07060b0d05011b090308160f0503030a0903030e1501090c03060314100510080d030f110d090b07020c011205070c08040e0411010507080724020403110a05 74
    0x1000784144850300700203e002403030281424000309000e81c0718290018500c1000b50100329003c60382801510340e41d5403a10708040a842100007004100e02038030b009140d80e4255a14000d1901a88128014511102c0321403000c2090301d402071701d410ba410000301c0703880b0714100802a020b0044080100e000900708404880c06c0c00001540541030420000481c5281e0b0a10b220180100500c1024404058030f80400001141b800100d02c90751907a51005010f11601d14103040d010b880000d001101007546500041100242c04255030031500094580820008100424000a000c2400075100c607400006070405818006034800c040c558410000c2e007010395a8000b0aa1b00c41c0117400840380401c907404c80c407454910f903580c895a48800b036424650348c141504d8031002059081508041c4021079014140000d1000d24040c0386121442440d04500d018a0b9907160788072800b44082c024009a0b011034040740141c00c02c3e4105840e84c08001c02152107550301d00700428030b21940a031031401a40f1501001c47d15007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 839307383 1250 839306133 839306141
    0x130b0a0204150c051506060d09050c0f0a030f030e0a27140c1c140705031e04081614060a14150609060f070f140f0d080a0216020a0f080709 61
    0x140c01c400540ba5045801094442c2104028002c03031f4030401c20041007020656500c140030340c1030b001d040105418201c41040c401a004001e03042d174440c030391000b400c000003000c19400c8401c090b45440e040a85912002c080b400c1074000750045084a01c088a80c2c0003c0b10354030500c11010000f91100740000203081c001d1200f20441a264201c3d83c50040049900580b4091040c14a034216102d000030080e0b58081c050485602c20f9030382a0004a0000601003041c803418884c031140341c000301e00c500413420541d840c10280c4c42020f590b0004a6020074101d011302541c0e2a481500f03000d0002603c0c500e252a0421384001c0461103040403094030f1030404a900000c0b030340c40e00e004404003e00098a040b440404001080d0082210342001c100200105030016000002c060340461080d88110f212110351081c0c4c41c280001c1c2c42d05038549500a61040d03a44035400628a40c00c20342650b40180c0d0741c4811583c04865403c90840030350003605131500000e921401c0011320044400141c20b495000d0348942c5844155 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 839308633 1250 839307383 839307407
    0xa0908040618030609060504170307020c04050603011803020c18060d02120a05010c030605090604050f07030b1908060a0e030408030405100e0d1505061017130b0a020415 74
    0x45401031100340451801440d444080e603001d4200c6003035465907659450203030f5000c600103c440a8030b840a000820800c00d28020007184031107412800c0d07141130b2200940d07400f042d00307a082c13189890394042411900c2c00e40c880d50841c01040b0344099581340504001e59220f40e8901814000d811074a01e00250402c0600381c00d0080c2030003841e07041d40304000d80030000b0070f00390011030140e24000c15441c4400180240302e90300710324000e501e010030750ae03240104204207000c000f030016000d02c0c20038042001c681c05d4080400d0703205d01c0b40c0c200010b90a8010011501c0805d6450106542240b500000b140105002a25070721407c5918001c2c003000200b43e40141d12800395210b0361206510074081880507150000380a020b0200300e1070000741c5a035040e40003070048030000da801e9840c15102c0c00c1208600e00c039801129807000b001c0d140ca080900e1a400d00030115405e046491081c41441d002140504041420b00401c994001083c00302d03d00745a100000254064030407807900001c501c81c00050035014080c42031070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 839309883 1250 839308633 839308643
    0x5180109140c101b03030219020703031407030804020927031306030e0a0807060f050c070b061518031207120e0d0b070819020a031a0901080a1e0f060509060a09 70
    0x4d0f003402445071846980c03041e031013102455000d0054002d109501c22a10200d00c10702c0d4010845545142809805041c3e8524a010645810400c4a000ca5000368800390001d40c1034990310402da59a462080d00b221140768282d046040b050b84a205c01200040501080185501c071441801d40d078820a42c1211000d00030000e85410220000340803a141002401c229401806d000c42c40300c3c60109801d045480403514040041b8011a000c070a0107140aa0107030b20900c01d40c1c071440802e03944011000d0310b024008000040307030150000300c0b003161801d002d800710b000f110303441c901c0d1242c038903140111901d554980801d0024165490307071a000e1070710300340f0902010380010000e2581d440d40320085404910080c52004000705041e030841c901c1c191703032008020441680d500051032030000d401c03a00454040c001a14807a00c140c2006000182020841045007039014405410005004d5500602600340e000090b0550b8856200b0b00140041c98000f9449103800074141c07140d41c0d403108100300c1260f0100c240504 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 839311133 1250 839309883 839309897
    0x17040201020c192c09010b0f06280305460b0a03060204080706140405010c0203240a23040308090a0c151b1505180109140c10 55
    0x8a24140700e900c91110f0070440f841c54080d251101c0f020b003006200c0508040d000408124001c0d0740303440340ea000341c5c1c000301c900e0020712040d03402038002184006100213240c40b070b140c00581c414102d1101c0d800d11001504040c1081110001b0034406001000c040301c441826681c072100740c030f07030f1005030324448007050005082e100b07409202100d20b180c0c003500c1d203100314400b03590b02c0308020703950303503506269200841c4195400360742c41e404d01584d58101499980614184015400b803d440d03600030f1400e03030b801c0d200203281410800000c1d000003440c100c00840e81c02d190f0160032000040c03400d00361983c2482401201020721611100b000e8020480c80f01c02c0d000003d9003000c0c40442e00180c41400800e4008032101c04817400c007206a03d1780c40c0ca0601950000141d00c0e49841180b100390340000013078008039124691108100f4a5072280c0b5940803844c407410400316034a5000400c1140707040400720488a040000b007110041500c1d000100140700e221268040c4030307803020440c0341e1904003440ea0300c0003203d030381c1c0d50 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 839312383 1250 839311133 839311153
    0x4080c0901080343060605031b10090e04080903190f0b0c0f130e060105030108280c030b0907090b0a0902070f05190b0702030301030b070806010c02030118031704020102 74
    0x400581a807910f01c03001d01c1c00d4404210625007008006031003c244007924800750f1355107010012240181e1055009030004440e010304203a80341c10404a1120984d024801c054030020102c807119070680142414028080600007031046110183c0a520406e0b000c45d2600c401406207101a42501c1d03500034198040506030400190341803c0d041d80107001140c60742d0030482d0f403d0300880d59070004400d8011040032600c04007c541407810144e5041a42030a05178030719410210343c0754940c0a14404404008850b0851041603c0c81c41d01000d02c2d90f80180094100c0782d103074645000c0f541e005895449061207451004282080c45104100f01100010a0f41f5402842d0030800130194003d902c041c3c44c5625581d8071032002c2602401150b40414520300144045242885c00e100c480384050903042c11948140018000181180300340c2c0d800000038109090640c0d55500100c810300c0800390029015403d103810350302022419901012400d00c40e1b103402d408892204040030070040103c40182c01640f200ba554 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 839313633 1250 839312383 839312407
    0x816020303390f1e071a04050c060310061205090c0f010302040f0f15030203040b043908010e0c10030c050d09120e090402150a11010f0204080c09010803 67
    0x284204000d002d01c9104020b4524540c0700761034110b52104081c0310b00010b40195003c60403004602841d02e001c040d642050b01d643c50700d254040540c0c403242030a40d4000041001d100c010171240c9041c60307000340801d42c1c0b480c201114265580a0780b24040c0031444260803001900b640d07020b004d2041e9112802040101d6141c0201b1800300c0b248d0140ea03040c56401c0001291002d15500608064021441c00301406417900011810280c40403803640308042c1f040c41403000281010800c1a000390300b11100c40101d401c600621111500702ca00000c04641c2c081c04265000c1c0942c112a404584502c802001820520b11040742c45000c409400e55000c407840d8140c03003255000b13920085441d075403860045e040120101410040300c11804003590000708810083c41210341c4501841070000003a264100345042c07079400f0504000054266481070180443c8900b8000e12640e40d8601c3c1c011404002c8c049c481c0e4140d90301d0020750050103030241c2ca0141c030007004c02504020030400c1c101c0c1c1a03040150f2411200c0400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 839314883 1250 839313633 839313691
    0x2030d050a1e1512060c110d170c0d0e060a06080f070b0a020102041d16031e0c0509040603031d0411040e040c03080304110909160303080a090b04030816020303 70
    0x41d8142c80f00200004610303a58000c0004040710f00c144000103d002d15107a000e030007004058410f00443e80402000b2140326804540c40c802c02280030440b0002e0303121390254480b140964400c03450340700d180c40c01c000b12a220008900c3c0c021444a0020400652951b48217602e03000d46030391491071a4000a410004100f90030f005040c00140c80c4001400c05880c2d5400d405215000035a510785043d40c807003070040608134080080c10741c62560804200240c280074100909801c0400b400500e182d4811102c086a8092011203000e640c0c0100100301c2540c89103030140161001d00000d030303006401d1141f002c0240c1007501c03a00041041e600c41c014103143ca08003501803000d000410403115202003280020004600c1c90165004070701c50440072a03107492400510a0507540145900c01e00c3d404969032892842124000200350f0b0740500c0d00c12500c0d07482c0240710000c1c0c8107480004290700304030b0040009040e170204c5400c0c0103680c40c0001d8440c48040c420200c1c0d40b804242d070324003c05144480164001b40801c0c50b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 839316133 1250 839314883 839314901
    0x7031a0a0518091507050703080f190903091707090e0a050618240f0a0b0f01050f0f070c06022b05090d14030406090909120e150a02030d050a1e 63
    0xf11113042d04c50244107030900d84250f401c10040780000c50311a08042d040040306171f0081586241418030b20704010ba0945925240100142d2250b46420010605100c0e4810b10090004013005400d0001b4480f245580e4084521843d00007920340120352540d2600443c0103225117400c00014002a00c5400048200b00c2c2001d0681005200d00c0141d101d050660b107140864a08440140d40c071039107410041082c206e03c1c0246a90b820a2810192060680d1000400744940e030080c600345868800e4a52541107a21880c4900d00a404010400104000c0b01d02407240642c1c0050b800da510350070480403074410308200500300384444040155000c6078031384600090004080b0040c0030f14840385158070390680d15032080c4141a00e941001034281b25003a00040024014916103500300494511629840c10743d4025841d900104803030b8178407490742691a8034000c03200c0c02d011501d6503502c40707100341c0183d9207a001c40325030110141031000160b2056001d210300c0121a00c3d1500e0065400341c0300107018010b0207011 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 839317383 1250 839316133 839316151
    0x903130b1608280507110f090408030705270a0e0f010506160609050703050d0f140f04030b0a0911220c110d0203041d010602030a0e0a0504020307031a0a0518 69
    0x9a04030845241415400030200c0e213030301c85035541c1100b8141180c05070784c4010b08a015070421103484815444071140641e015421040d2181c8035214480122014862010581c90071310b070a8140841c2005035880ca4050707480110b91400a069441d442d001c156682101d414854206800041265041500040500300c2c0303803810384803c0c11164cd548204aa111100c240e4255202001c14030403c0b001f006070301380c5580e146c20013203001003424000401044080d0104045010007050500203080003006071000b55620800324501442c0a09446004200303400080d29003044d11500783c806414008030700780a040b641c0d40d07a0b0703c14410346400b203006015811106800c0016508a003181550103201c840c03240345c01a0b010b50740e603e00c1c0005051202800004ad00800c1149a00400001c6e0300002115200c24503810b0427101c052060f000200e12030360035400550880d0000041101c0d00e941a03110b0003803403140320151310014071050300f8003110b21079501825400811400403420030324901080e540c6e1150b009 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 839318633 1250 839317383 839317417
    0x1031a0c070206070f0c2312030c0d0809100b09060904020a030b01080307050f070503060402120f030a0309030f0f1b1b06031b0c0201081308120903130b1608 69
    0xd5001c900141e12400081c1c841d450385c01480c40410840b00c02c0000240002d2080c003d03465003180d442c03003080c40c54000941c400d550300c050341c0310100d8090081d80c170505120700c241c558100000c000503082d81001c45405285004a0b803440000c00341a10400c180003601408500081d5215002d04c1500000074009a03800b0808910000001e40810f06903406414414043d50f100c0070b1340c1c68404d24110707070303000b0f50781c86a005454103202540700000e40d154072680494107115050700f0241618100700d8183c03241c85103400300040350b550440c7c02d908103046140c400c0d91b590000c01400c9800310f88107100c4518150018040011810b000d009040441d44000d01540b00701251070000c2d92000e0005c0083d520210110391070311441220035810540042131480d80c0e0614503d40c0040b0350000b00f681100130401d0003602014440c0805100401050321541c500503085400b44e0300301021001d42c1e0750807074484510801c00c2c000300030a6200c1c0030700c00c0d501001102c18450707102c0006555481201d8020307900c3c501c0350b1010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 839319883 1250 839318633 839318647
    0x403120b01112a0d1106030c0705010e070f0501020f070b0d0b0d0f0303110705030a0302030705040503160521030405040207080909040606030c050d020102062a0f0408011401031a0c 79
    0x24040c10942d450301c00600c0714503d201400074005030442282691040000103104004200e0b0f0481c42d224500040b10059601c0da0341e0070360740c880d84c010410050459844c2114003514580f00107051000d03942d82c2038400e2146640d174001240d84d180c00c035012003182d03040602c0070804030421034058040c55604480100d082020304000c00e2480c00e03002d10076151035042d1003000080c15018401d078200010b00c00c0c2507602e0100c590700c84c19604c1c460385c560032003055400000510032521840580b009000000c060741c00c1d10511101c1c04100c40194050603200c6ea680004052451014041d0340901040a031301541c101485d00301044002e4105071010766040000b04902d03c041d55078600c803207118500c03580c0001205400e5060418030512603800031b078012101d5010b500b015030380001e8915804144000281c0d440c6e0b14043c0040300f10701503003241000029001c07170b50001540c40c003000f4000f82c1e01080001c0180010340708010ba80b1031800c0c03002408800100540e0340000307003840c1005a114074210102807034066 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 839321133 1250 839319883 839319917
    0x10e07051821070f0602070b030f04020d1707050c06030123040204080f060108010f0506130f111b06060a150507060b0607062406080a020a140a050408070605030403120b01 75
    0x41282080207160000d44041c0314813040861003034003500740742c0b0040c030109041c03c00b903619a10000c3c0012904c2001540000c007150307540044041820b6002d0b10b40100d02e000001c44e4821034020081c1141c0304d020b40300c60105a41000010b0320304841e1960079881104412942e81c00c8030503010f00126410640803c40800d1480040008410003501200240710035850500083c0c2103515003d1007041c2c0500b040e040c00015560005d47da4115241130348000760441c41100450300406100810741da000030301003108640c5034540c5003a8010140036034151040380c3c0e5030b40204140704c1d5160041c000c1101078040e101c0700491140c8050030016225010014480d2103590009035541c2000320200d0b0710580350070700803292120354414500b02c191400700b400040350900c40050101d01c0c0c002c1489403883d0780400c2c5010a10b2042007151900c070442c0a5841e034031301340100001d0260344540900c54140c4154440081e580740301c0c5045a20a0b5055500c0300350304042c0100c1d00e400740c0501c1d44070a040258103814045090 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 839322383 1250 839321133 839321179
    0xb07051006080a03090e0c0409020c030d092306040c06050c0f07030f021815010e0f0603190b18070f030e15010e01061d0f04141e010e070518 62
    0x2d4550051002c80344500d0700601c54412500300b0f091a03003601c07083c008a0b840000a40d8152003900202686807581100807528600800401844039400d191411042c40900d000038103c2c081d0b22084180031721310702c51503a5612581624004d01081c00f940f0108419407141004d00b850f0b11800d01542e0f981d0070f020381f03551301e8100b860308255401c0d0b607843ca0410461500000e500003405a040c0702903e0f030b1a00c25604038480c00121011414052010805542a66121404074102c2c00c001c0880361242014101d50103072841d00d840c160b14040c50b08a140c0041e2520080c803d8402e60002c00604160740d403040304441c5008500d5420040c136860712100041c0180900203011036591000d4894515031400d40c414147c2c1006a00c02c0c001e00941144084490890b0604a03885110030744a00c000410031002240061004030781904a03d0000700a0050315a6041030310b103e10000401c403000b480c2d07201c100580d940c00702074032300d400424002c01420081280d00e180443c10743d00000c01c4030398026142d0301024030304 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 839323633 1250 839322383 839322389
    0xc0f030d05130201080f0907090c03050103050c09040c0308092d010201060911070f0c0b0a170603010c092105190b010e0403020d18180203071b0c0b07051006 69
    0x5410200d50040d04150038440c95074004056807000329010216000605a42c030007900d010301094180d0700113800322400f00210030003440701076420821494809030040040c0b0080c00116000e00540c08510040c1c901300340980d004d250015407804c0100c2c91a07a881030380d41d00c450b4440781c1050b842d0205000f0110300d1040745900302c60344603942e0600008a400242111090b400c03241c016032921707606441410030306050702ca41507407082d01c590020280d82000008400503500441c010750b80025445140c070fa100514841c41064020a140d16454070340406003039404903400c220010303480040400611074028089603080c10b0000e901e00503030800303446d4a03040071041c01c00e034000504589030100801821a00c0310340142009000300c0b00e0b90415550085d1075800188078102040007034010110340041442d02c0c000100f180b402c124045190f042a803202940040310345001041c2a0b90860140380100385d144543c50741e00c80070981406043c5440c8010f1908954425100c2d407182d40d07000f0943d0700081c4070700009 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 839324883 1250 839323633 839323663
    0x3060203040b1e0106050d1a0925030e032713051005090103020d08071b030b371509090515060d0803060907050f1c05090a0201090306110c 61
    0x2d5280030f418114481410507004408070903040700402600d54040300351040c2c140001c1000c10700c0c0508215405140844469441d80f00e4021070501141c8002c0302810b0412a40b44144d540345140c0d4244168100c42d02c1807824005074004010f030350405005105c0200c0006084196204084a000c011480340c144500520308115600e6041c01500800c904290009040131211241d1640c1158041801e0307888031300c1c006000460200c0c4220420000c101c0915502020050080e2810340e00e0500001906003520550702d5030384580f490310301c00da80001c280f0394500c220400310081403044108020090805000c000d1f42940da0240c0420581c000d0701900310a24001c01c01040d0408440300078840b440c00180440784500311521200c00011142d0301500d9000750100c402950075520810240c030940f0540a103203a100ba03000403040e000f1f00e6818002d00886076615410842a5280c40707071541c1c0c45a8040300030f40480d1809408100007505a0001200d03950710049650400d44004901d5103805451141151 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 839326133 1250 839324883 839324903
    0xd0312020a27050109030f21020a110d0b071409040c050d050108060103031b030e15070615050a1703130b030708060109030f02060a0309150e070f06050f0309070306020304 75
    0x3002c0710312140c2504820303400000c045121032620f400038040c4445840004c182c05e440c810541c0a105490508004000c038074079610640e0f81020800070b40b1034a84240450302160740310041c034607900381600030301c40d1998000c000c00180d03151a0f8090311105080700e040040303110304100e140302980303032750140c0c15020090741c90f01d50b1203068908130075080d82e00c160400c00d22070344240300400100c2c0e4042030a0080ea222140e0002d01c01407182000c072014003c407101950402c400d43c003007509120b9040c00400682d40142c0b002c0010b0b80a140d01c0b81c4941e000c52107072560100880300c050081c85088108199100c020000704c03880c080c00c0d10f01d48960491503a0243c040040702004100031a41c110b50034962000302442c0c801c5405007981e4610003420b40070a000b034000c11000c02c01d091103601950003200c800350080f41c4500112004100743c800b9107480c140702240307070107a004c0018807004114015010f036000c603100c141c00c0038001d8400c1e14440d0030081075030050740b03d820300000105286200550049000d5400d0310 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 839327383 1250 839326133 839326157
    0x50a030e010b010c0b1812130b0906030408070c0905070504090506030d05180103060e0a0c0206070e220b1906020706050f040e0601171005040513170315030709020910020610050d0312020a 82
    0x40d07007102d15403001072209c1003080040100d555100840c0d42c05540300b0107c0d500c0d81c965040c0340c54500410740010809034581403d0146480d00314010700203d441c184020300459036003e050585644210b1250b202080007803207140c2c414141141c18859010061400085180e62400728000c0781c0030030ba0346d038800d965590301524112641803009560100050402c03002c00c0c082280810714a0b0050103000344824400340416450140780e401030003100900406001d24a10031b0108001141c18600c50340c4058442da21000500b640188140d07403401495000090401c0e29016802e50340760381c003c1c00b4074100100d01c6075200300111080b603030340d0180c1442c00e1114032450900082c4400c81d000600201d981202c40d04010000401b42d05201d2a0584034584080c0c407031712141d00041e6440140710036151b060003400c0001c908140b480d80641100d400c225850005d183c41200f040e6100c10080d29003140c0d94008000c180f181d07040031400144024441d25108110b1000c0fa60300004a03040b1005a00c0040c0d000c108403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 839328633 1250 839327383 839327407
    0x507090e0321180708030d050a062c010f0308030606030411030607020d030c0e031b12030f120f0103020913151b0e01050c030418020c010606050a030e010b010c0b1812 73
    0x1001402038100080c11320608002640b5541e005044684d0300e0291a0300c0060b5421000340c001030010518680c3c0c1d945c090100782111302c00061014250600340809c403000040305515204c0a00c2103076008454a465030329010305100c26903100a001b95001610500c104e40a5202002044d100314601c0e8090000659840402000d4608a482140c104030403080b900d4560b0743c3c04903d11412900f60903881210322145030100c1c4260000c0e00344004d003800040344200306000b00030002d00b06450034425000c103e58901d40b0889040c0b000b0702000c2e4000310a5000078070400c00401c0030500e100c0c098009603c84244035201801030b2032006512910074451010040c1d62190804506030440070700742070107800d00384030040040d642d0003148034004400780105502c1800c800c056044030b0b0001545002800220307110078000d00558001030703111340080c0c500425042d0900042c0f150791980201656240c0415619403a65014110040d204d00d100701941c5160141801e01001040c0e50740001c207217010b866112803401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 839329883 1250 839328633 839328661
    0x30112050c0102010b180619080d09050604080a0f080f04090b0301050a0b13090f050d0f0210180206180a093e1614010209040609090507090e0321 64
    0x241513a051200007005640e940400f101240e0304152120001da580d80f0000303d0486041c1482d4a9080040f0000b0403250070200c0c20840c465000d44a140919035502c050102911861140b20081e4208489900002e5169410400309034000c030b84040c20090042003407101940154485a8400d0791a0f507007d00c0c60a080c0501c80e408440071904100707e07054540443c0d0300c2000c4e02d040000665850310035000708400c00810550454108049580d01c605504000e8000c10b4000380f403802620074291044200c2120b4040c0d011034146442d0044e90411555003480071542103200300b951244c0c0079039848829611003910200c01403028071800315540709e800381001468a11510580e06074101c1c85060380e103845d45125003080d000790440816a9a812007902002e1080305900000d100c00f890068581e05a00150064401000229400c12859039942481000c0f50440c40c0c00a100380c018600410a08003e6404000250450303400d481c43d100240e4100c10000000d0b9041c143e41c41d20250910007000c6556031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 839331133 1250 839329883 839329903
    0x1b0e030328030e0105040c05010e03030a0207061404030204150f090624050702030613020f04090b0612100609090c09050f010314030405090f06011205060d08160803011205 75
    0x5145810080007a140e948242030800003081031201000d80c1040b84290301801c03c1c1d03150f9900801403030415181c01d10200d481c0d845400c3c001107545000c0c0d50b00d072030040f08441c0380200076001026900d01c2e240055925200320780b040c84101ca014000040562228001ca800f41c0c00c0d0604035030040c0b03051603405c80843d005500040c034a00e20300041032200342c000f1034454114080403001c280e194040210201d44511480300300941600404e018010100c5d4a030329000d842620031240d41150190040031301c0308440140001501c81544000883c4081c1040c02c00000c04100e00c1c02a43e507038081d00490001520b95540c0328040b817030f0303803850007005019095072604081c0942d09018420790810812205035120103020161006031414280412013130204111070082c400500300000c03034506001c0c2050070810840300640810642c41202c00000c0c6c00d40f0540d446032400130700350192a030498456078034680054030700705150400c1000e55030200b0140c01c0518000c080d4101325000003082d900c1e000d405c1541c504 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 839332383 1250 839331133 839331139
    0x140f010507091202011209080c030a0e030c0a050405130822170a0215122502010b0915040f0e010c0212040302010206010311040b040c12230126011b0e 66
    0x3007403209100c442c1c0c181c100203409181c1b40255141c495107406c004d15403c0300060801b04000751801e040c22000c03024040ca8a0b140d2200080703859800306064a40018040c2035910040c0da4400b80301030315147e407040c1d420480c01440c2040201c1560350b03982c180e901002080316061000081d58400201c0d401104001d8601c400324007030b44d0302001c0e00043d0394041024000b8494485091503010041800d002d8441c040c0c40d01ca1180c2445c2805c81400030f0710008035240142c1c801c3e0706084524054014069581c4c940c00241141685aa03001c40002d510300d0f001030b006600036180d954005000314980a21745281200b00d00006098a4642d4064a0101030b0035031000f240c90709000400250380c0200710349044035080480d0044422008001070010034000080f00d911a00d01325418045030350240030341c0f031400d41248007001308180c0b48002c0a40003030301c4504642521407850040c86510601c8800d00102107814540490b183e1070344018a0075580c030100426040840f0245000d01c0301d6010789480841c40040e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 839333633 1250 839332383 839332397
    0x190815030c060a140f04030b0a0c0302032505090603090c09010f180f02090d0b04020909070b03010b0901020a200414070e121009060b040f0b030d1b140f010507 70
    0x840c08a06a8000d00407001c091010500b64400302c52000012103141611100c803c0307a50720748234940410110340543c0c140300001d240c00380c00e00e0300a010f442107a000c4d030980a03800180d10320310041a10031095403180f1804209040c0110f0f01c058403480301031405200322101400c40c18407103a081c080308410581c010259645941820405d1040c02c008810078030008010101d0b002d06a80c142402034401c0c01e51203a0004407035400a403d01c40c298900314012071084031542c80e2502c2e08001c5540d41d1a06000c0c2c603131007580810040000103c404010704100d071040c0103481a0303404a48034105505c052103a11002c8036405081010b0a01d882e20441400541135104900c290600a0340101340700d16030b07246180118141054195610402c000403d02d05603140000d00c1b008180380790500c042c0a14040c4640100c2c1000c0b003001c80b118131130103223881240000d002003641c80000750040314410300f104113810007242c52000400100304040042600d65828500070400c02910180f5030f402c541300241035904210725 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 839334883 1250 839333633 839333653
    0x10f0908040e040c030807050312010605041a1303020603010b31140109090e0d030605031506130204030512120702060402091306180f0b0f06090a05040819081503 71
    0x184000c0c0da05499a400700240d099035103140103000e14400745c101920300480800c04208124000009040d10b2a5074908a40c00380d0ba141c4054840d4003c40c0200e800403128889002d00d180304007030242800c080041700c0008156643e4000c560107a00a07004000d004c00001034407624080e400440b072280950703410035100000100d0905085841c1e20b40a0344103e00c0d105003050640340e208154500207808818420010840340742601541c031404505c0c03031404213060500004041c500401c4041407e000e03401c881c42903550301d004200c00c10406481043c0002d5003800301001140c410410b01c2c2c1d0104c1120b04884c3c1ea1620800e010101c0f000091401085602c80001c00c00141c43d0210301d103412250103080c06514100606e40f03940038000700743e01c5540c00150082d900c81480008a4040070490160b03005113501d84685400409490084a00c0344d0008006008a0304001c070035809140d100c0e004030f9031a81403102c803c441c030f5143e00030402500005640e0b40240444c80b4a03400b6400301c0150100d0080200e140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 839336133 1250 839334883 839334893
    0xf30073c0f080c030604020304062c0d17060405090a140c120118080906041a040e1e062b0308100f0e04140c030d0206070e090c090409030504120f05010f09 68
    0x800109503074086c0340c0110100e820032010341c100241c404603903403200703103600c50f4540c92425090760840c841c0c80b14400c60f0141c0303050900501c03a0601e5030760070700304c6c480e5595070310024000a04009810342441e44a00c0c01d907100410392004003035140700070f00c1000d0154424a0030800c140060150080e0320140d26200518108003031030013082c031030264004d20031515880140000740e018006d980c420300c4c8490314150420250311041004100340ca070141403501d03141d141c80092602204c0e19030b032403980c1195201e02040036458030f440b041552801301e110f40f80c401c0000300b83c45107403009041001c8010034840014003124040c444540b8002d4000c1c00c2a1807a140d1512030141c0c0c100c81c01a2010381800310ac2d1030714010f0000d06016600001501504170b41d0180c0c02600c00950300c0e042121210001080004100c6643c50314a01480c080d040c0046000d04142e9200d0402004150280f8101c041c040c04110001c0d9125002c05403130780d128024200c03d100380702642415402c4d82c5021080c0b42032249000c1c94200028 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 839337383 1250 839336133 839336137
    0x601050f06120c0903070e040209311514070e040c05040302010c050c1018051f0f12230a231b0f30073c0f080c 49
    0x1040b0002141c2c12600d40460803a40c03441800b00c66505805082404a004000e040505025520070b94103c02c483e0b864818640c8045402007107014082c1d59100700c030109444080b419180c141c090300c403801940100e0244c000448504149a40d00c1070f6822080101c5540c22146000325504d00343e5081c841d00c1c00d04000205070744240e0100a06001c003c103601c9040c001d00301f12950309043c000d054044202e41c00400900000400c01d4490500c2e070852501203180e00b01010b11100780340350b0010050883d00a10415100a90394012080400c1280c4107482c074203000600841c02c03009880e114130b11010740440822880c0d0400100030705800c508244590349100c413081d1031080754030f602c03504001c11a180c10601c68510342e80785602891460740030942a8501e8007480040804180c804980b407040d28000d003580081c51907100003900440349000c0060301c0e00c0d000b100303521102e00940d092012118080c207409816085013900010071b00b20301510f007400a42e006544441212203a081c5102076260041c440c0d02e441c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 839338633 1250 839337383 839337397
    0x11d03030a0c170d0518150105060a1206090204031b08030a030207050f151806061003020f07060203010e0114121f0e0f010c020601380d2915030406110903070f080601050f06 76
    0x5a02b0004410010302d01c5120040c00268003480180011503071100c605019401500043d241c082c500e00d508866078400c05004800c489514026508000c0050000d900075040782000380c405001c0d48402440304201444811212105007650f104035080c0427085c0741c032041c00008090000c0d808407060000c1681c5a0a000d000704907540707009030792105610744240d068000c45c08020210f0b40080700200b1500ca1002d0789078117a48418085d41d000340c00758002c00400308070b41941e2600703d0f001140308250001078100001c034030201c6074802041d009200c0040d40c0c5440d07000300c4100b01e40c0c0d55505000075071039810700801d07005082d18a00b4000304150401130440d82e0144015a04401c4020303d50401c48021407016641011074140e02040390f0320481e004505c2e0242c5007060440390780300c54141602c0f94a040002610113185000c070b29401c2d55a155102401881c030210781c51606e034418059076030960740400c003e0700038141a000c00c0c2c00305440e2417034103031503d581a040a4030034200001d80107080d48034401682c4407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 839339883 1250 839338633 839338639
    0xe07050c0a0209091606020f2802040509010b210708010c02100c120603060b01080609010b043c21170d060503100209011d03030a0c170d0518150105 65
    0x3084d1204c500c4646028400d0340b515442104180700011455000320700c140f0601350600c15100b101443c551112000d5040c502803180b0342100282410140c1050351205501c20300a9000255000e0385400081920b841031340b030807034030740041c4030301c24003075a42230054000800d50f0b000280910100d981e8080d40307a42c800c0030041805039848001d12940e80c4142580b0441424044042007070175140d040000203030000b50611070218590700d002c075410341080c000305812503000400c035a040c1303410400980c1d035415081360042d50303501d903500506c038400d00020101500d0001002c0106207940ca809c061605a064070403a01e205c000765003603680081400d050008010321002c5e0b074410744c0c0701101000c2d00002c05403a0001070309403107038241000da1040c15038010080304800740c03640c42001c0b140d6120300a1800d80c018065415170024004204054000e1034400c503154441e0740241208003144040c2d20f1035800c06c0d0707511003505440d00103004988541c940c0700780d4400d0046010300703407030b041424090641001c180301c3d080c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 839341133 1250 839339883 839339899
    0x1009031b0f030c0618080903011407080c090111070f03020901090902010e06031e01030b09010e0a05032b05040813050d03090332030a0e100e0103092a0e07050c0a02 72
    0x41150310b0f803045c07880c0a00c00e01890103694903410840c0280c0c1240200502a61034500c80c143c0b491f40c0c078022140315106560358000300d0f50320001c02002d650440c42d861814420340c9030020a40840034401c0601a20003c46401041895030042080c00d81069014100b0f4078a000008030250741d0212022684810564541303541c0c1d251212118611080c5445021038042c00000100400008255050094901e50001d01c403040000142d0383e21001079580041107540304010544820010240c40b0315080380c00d88640d05281d001140c40820703101c0c1100c08480102002803241d40d03003142c5e020074801a00e000d80f40c569010f0448c5c2d402404a100901000c1c284144240b1300e0403c0d2280b6116444071218490080c0d012030055034025940c940001c1c05d42c401045c120496441c01e0300f030010880d000da0081e0340c2e600c03403009030020041d002000d4425040d80c40951081074003428404500c20a100380650031280c0c202d5074904102e11000320030103090441001000c0000700d50302ea0740095032908403901211008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 839342383 1250 839341133 839341157
    0x11509061128060f0c0905100c02131104080a0314120f1b0711120d0206070f12020729151203121006090504111204050c031009031b0f03 60
    0x2144107a242c80c0300919413428880c89082103c016003101a0521254450b166801c0d05c80081044941310707070071240300040c070348c03880b480161030180c1c042d00750300707407034640c000349684501d070282c081d036031094001c00c055a206c0400b560805620103070201030f2030841018641085c00602100440000103061104071000c0030011a0040d4081340070141d003212003070042d40d40e41d10a80303000e404581c0d407140214450340f0701c58945828000b01007429101761807240c1c0030745505e50b20705405554480748109040100300500030f295006070ba65200a1400798021043e2980315a4000480d0800c9043c10640281c5024400e040c810345130803100da00040080f0031210852181c4684110074130b1801026010700c00d00068105014180300f0304040d0300e0a071901c0d40d8850444ca502c50042c401503540d94541908000350810900481620030713041c198200e489001036800c1c155080e0006071501540c0300d08200a0381d0307100c114604143e084200540416040700305072640e4a001e44856a00f01e02e043d01c040c041c420ba14081e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 839343633 1250 839342383 839342443
    0x13020406080d11010605040c021510030507061d04090206270d080a091a0406030c05120a0e0d1722150902101b14150115090611 56
    0x800081c124160440e0b201d1031001c14010b004802d5080000155444d14801041031f0505003d5421542c40c0c0d60000c02c2c440e103180280e11080d9000400c0714440d1054800c01000180c0144074410080c0794540d501002001d14400803c415000030350090b01c41d600c1c00400d000140c948109440506101d0324150507000a186d0540380b002840c4206141d00c0b442604a0200700118100584050407540c0c1c0c40503010350300e601c3c8035210700c820441c080200d20070a010030004070f4441d400c40c81400070306d840c1840c00c2c031042c02d095944100007613441500e201e88414961003d805c041200281c0c05905150080790764042c100240c01e07509001d0804c0750b50800002480011340345902407164604d5011070714000780880380d0801300090510312022072240d5035060740c04110602c80e03840d111003d01d2440c02031a101d220707941c441c3c0019600c04a8410b19000d100041d01110200e500024020b0940442031241d842440600410182030354102e0424801b000205094655000034176100d410b00c1d44803080481d008550070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 839344883 1250 839343633 839343641
    0x140f040b0609180303040f0512030420210d031a06040b090f0a090e0607080c18011e0c050c0303030108070603051504050c071106030112080904020d050403050a02060a14130204 77
    0x43d0400740d01c0000240003c1100109002c0c0e1040d00031016103001c00020034545030184400d40307002c4e200110750b000800509805403c15855100014480e040048450b1489410034880c500844403030f810030380c26070007155014001d48407030995140c458181080c090380090303c0b0340568015080c00c0306012070304a0003a03c40401d0001501c8000b4400114941e80da04084d024050320380b041007050203144041600709005622460080050710322880c00c20402c1c0d00c001c60750402505a03a4100501d04810203a07500015404951202c0556541d8414041da420124a4070814400da640280e004100402c4558408a0b6000540719546404103054640e110004100100f070307800542c1c841e203440140a04803100f007004102041c4205501e51004240c1000c216143c042440f8000b0003081614401000500150051150000003000141041c20700d00c8000e044800458084000c1100040c00010041d01009800d5100091100500c0610820103072501c0d2450040d000203800c11300240c21504541e62500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 839346133 1250 839344883 839344921
    0x150315031203190207020f1c021c14061509070c0209010f05100906020c011b0f0311062401081306050c220317160c09140f040b0609 58
    0xc1250180140480154440c2d8001e0b105000030341400e000803000c500850003940d070f4150300200b80030b1652a0341c40c01e10175083d200245815000b12801c0541b40160b5640f40b0f8418035810f041c01603007900d42c552070041ca2030080c480380841c42d9408001045195a440ba14041c000502955010345540782c14030309841800700804000e500c540c4040006c601518a1400c500881e0821070300380001c2c2c24011001da42524a502031403005805c030350850391313003540254250341e4155a9070b5504c1c8044499501c42c011600115001100090015404003011090402800c0e400c8444d42540080160100080b0110b4460403142d10b414440440001040480d19000c0040d2058100318284418139000f41c400415500c070f5040f088003807180454400703002c561030ba070150589034809c210005402414544e840d050304007803c0c080d405103000510344001440365134540000c000406000c68130780000c034540d100c2520028424280b603c640002c00000c1101c200020b40c0000c02a603001742e03d62110000c494900d15068 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 839347383 1250 839346133 839346139
    0x303030c031406150a0c150b1c0c0e0603160e01060e09010e01030609081902010915090c05090c09060c0c01031803020c040e070909050c030f120a030e0102190302130f05150315 77
    0x5080403d14240760814240e0230800c48444645506007042c04100c280b1181c1e01070841e21b520708041c0410540c0c41d0200d908072200030221004a03c03402c007201c0262040d070300030700086408100100015078026602d0024440704440358080e41d81050100e10320345905100141c405a25901a0820300038900d01b1103030b40712600400b0841c2071060700781c003030f02904092000321500f21b18072241d6010180d030340c030501d280b69522608201c24285440204000400c0c0544180038101042100b044d869035690018513080d400900a4082c14803600d0001d021a903401d890b410101d018404510002580800c1450640301d08030340c001805004043d503d4a452519005404035a1400d0f00716810700c50300050b000c003c100100c00311000d250139184e0f0107480d02054502d00420503c01c0c0a800d0034140030307402c00b00d06156a2400142400c080703041101b030b105004141d041c0480d90024016000892814811001d07009400030300c2c0086140c0004601c622058280c0d0005500303000c404220400481d01c0103c1c0e101ca001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 839348633 1250 839347383 839347403
    0xa030201021b0105040f080616080c09010804050f0a12020c03150604180213020d0e07060c0f06140a0b0102011407080126031902150c090607060e01060303030c031406150a0c 76
    0x10708401f550711035094640106800070300c202c03403000714406c0030351610503503504900b503003800b40c08001541c4c00c04010780112198001c142502040541c10021005014000d41d030080761980a0344020382400c6840d02d00c0c6003c1d400c50740740221a02d17001c112450300405c059074001880f84111040c11007107446440021760200a44d6a104003102c03054025207090100c61104100b41d5081c44661a83c4500d50320614000c81c440741c03041000b048000074040445c81c062140481c0c08000450038040340c10b0110740303411580350b07101c904940d1175a09200760022001d08842c5019181070180300580603500520685000f010500740d07402c42020481c0e0051845811801120741b0341c0c031002e01c0343c10a180800e00440040c031559075403061500031f046840d03010311000300c031551900e4014400d002e610b40c030400f020b0f180c0d01c1c2c80d0602000e000c8401d200d8071000354000d542c0080c24954050004043d100c9003240340d000700340c226082c410980e03221100440d030fa24248000346e50b103e642c40000c0d0344481481202605880d10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 839349883 1250 839348633 839348639
    0x31e1c02071d1012030c0507030308180a0b1614030a020706150308030c070201030221010f09060b030604020d090b100305010b0618090402012114060a030201021b0105040f 75
    0x99400c180c0e2104071100c0800c2c101da0605007884081290404411010710b0300821040140c10b86282d8594004c2c5401c1c0c0110f80151101307450004e0603801140028601020030504418400c00c0751201d0700749901070803006109850f5488140005485504015454509207006600070220380c0d050320003106803152a860410748120094001000c213851050134002d111028691f50501c80382586d81c0401860304503222000c1400311900100300881c18503030700704002c00544400c0150f0701e04d000040700001d60310b503061240105203500785070710088801d814950b05000c044100d06c01d40307920000075540161070307425030f4640318041c0c0f81d07411010301503081c84818008802e5800342408250b90180000b030158480d540c0c28001a0320038540741d03490080c8074844160440c40c00e0b41503990845d005140101e040484055107082c0b0743c0c00c1404a0769080d58402c50210050810001c881d4804022680c051000d0300e150000b07904d07411030b807207030b20640c12100c4521021607000c0c8003910301401c8249510200f09403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 839351133 1250 839349883 839349887
    0x11030d1e14210901050c04080601090b01050904050f0612011a01080a090c0b0d060b030103080d0518071d061f052104030c06150b0d020a0c050f16060e031e1c 69
    0x10055943d00259400c0070000390325100d0030701c2120104c2c3e001c580182031a80c83c1c40c1d60600201001d107140380c104002003000311100e981d1800b40e240a262a82101c01007400c01104100c50921100c0f08607480782d0500c07183c0c00d6128028005810000000e0811041c5592010204801003042c0c210080071301c1244007012548800c100042c1080d1045030b6403c00c10240c45100950300c0e400300b44002040c4090812204095a5160300410341209803500703450310304107128100c603052000380e070004291484411200040d41d031205c1e000c0340c1c101000f40c0c0c0a00d055041a002c040748100c0b600d50101c140701d800203c0b030b01c0d54000e901c1d2031042c0035001d6600010900b49450020040c1014100c1555030340d0520006034004401c005200080314a01c460301460301ca0074240c80c0010390000d041c21010300c0003031149000447d4050298503030f01308044c0068401d00c270008001c29068411600b2070b604011004400d249035032000101882ca01c0d408106403208080f5512106162541407503030781e01c0840441c3c640c412126 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 839352383 1250 839351133 839351197
    0x927040b0414210702010c05010606020607031118010305062b03080a0506030c0f0a09021b01061d0c070c08030d0f0f0911040c020a0206030411030d1e14 67
    0x180c850b03995800d6820b002e10000d6910540c0700345610359803000342181218164400001c02c40c0c030f4818184008005229100c681c2107504580c003800158100c0f0f070800c9040c1c0e174584525017221351081d9185050030a092642044280000d400c03505040d0f82c1d13404161540d840c90000409051540640703603c054121000c40c0c01c040c1c4001c0304402250711070000c10040352041c00340c944a410050010551185841c0c01c001019503880b4009800801072003000c16542118001400c030f880c024070300c903000c212013040081e00b181d2869000046031441058002a10200804100e40280340c4540c0c498440000c0d050202400a203540174800c2440700107544503070081c003030300030722a81d00340e0308000c01c890543c120143c016514044401014503d03841c1c0d102c1983d141c03d038000803920280d0710440310400315030b0b40400c03d1580180c40607200010f8446040844d0318007040780701e115008500d410000f000e203c21100c600312500410403c144081103400c1c6040271041c10698003640061100425400241c501c580940 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 839353633 1250 839352383 839352391
    0x7032702010e010e03061f080f01020408101506050708040f0e07030e01051e09010b2206081b061c020a050720060417010207060204031a0a050c0927040b 67
    0x810742c49039030040c4642c0214070300d11861001030003070490740d607a10009800000b4810180310320403014140100c1d0b151004c009241c22810400c3c001030390303141040013685c5441384181003c1c103c00c1c10801010007481008200c242120514104180c8401c10f900e013402441c00b854001d24403c04080d400090000d0145020360700840c0c01e03440801194183e610058243e540031100c0e0000310f1012061043c20820f1101e034585c0c090755907400011400804400503100308042ca00d2940c04c3c41d943c40c501802800c880c40f4031301c0245100f000600d00710804000c078140d20080d01051922507207022540003001c1c02460003500c14029031603021556040c44000c0a042600041030540d140c0030f86066001110300d94256054800c1c000810b281c2c1400d18100e200301c0e10501100c0e0340981c0307540038000c81000072020300280c00a140f00e1190320260140d100306620a5880080c449000716041c6028001ca43e584d07a002c65104281c1a601c00350b0400c040c0323221140320340405641c8000c81c44c1c0b0004010074026003001c09400307 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 839354883 1250 839353633 839353637
    0x60302040506030105070e0d0303020d090803060306150d020d0311061f08071409130c060c0b0604021801050a020a2306070804030509190e100f06020d080604050703270201 75
    0x5961200d00c1458200c1e9400c840340800700f00048a10384075403401c046d584034001e102b85005480c0181007010740080e14103d007021180c1040101c14000580350520083e40d1060300c81e400c41c0c2c400b9481a0006d5618081040064050020007002100b4188220b024086100009040344d13007038142060540342691064001200361240020040b81d03c00e004114078045070b03608408030314250449000c11900d0074000d017080e4264110710400500242c4a1150000245829201c0a20742a0103042210b80d100004010394442c030710410040c4200c508401e4621075030314007840c04540f02c442d100320580c03074525640005000040f0950078000da181c00783d182100d2004001d0142c66680e2075641c41552000ca055400402061061180d500d042c100454480c100045030303607800403034aa551a0000d0403400580740c1c600e42c40021601440803424010780ac9004041a100801800005034001414558040c101034452910746012412052298206140e0f41d03082c0c604040494920001d205080900c051003240 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 839356133 1250 839354883 839354891
    0xa02040605030c010c0602160b091b0406030302030703140c0f03130f180513060c181e061d04060b0d11160605270705010905040e030910030b04020304030306030204 72
    0x5928103001c1440d1800b40f4040c1c545140a01d910b03600c00c00650041d60b2244e0a4205046941021a406080203030144104101801c1004980c00700801003007900700805004c0c80c1461401c0000a82c00021140300c1c503007518103118605110303000c81c4024412650508200d20842c207285030341410100c000d00340d0042582410f11810303699403207001400c08502c51001c1c040340f8034032036920380e1146821041d8014070590340740c00000115500e22003150b45030000080080c86090031100c003204104180809090868480080300b281040881d01141d084c0c02200100301040d41a90017601c1203802040301c250000300203100d0541c9460002c0c030140c028042e1480003a0600b40320110700040c6e541140d1080140010f0904051410740fa0b400c040d0a0240002d407a601034502c100480c41c03c10b032152480035446901900b400c4d03242c10001403212032550070080c0310360320f400c0c2100b0905100100b00c8a0011060341c002e017498114010540003080905140c940240c00002080100340e41035001701c060707030f00c00c9500b04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 839357383 1250 839356133 839356139
    0x627070906081b040b0a02070902040902030121021e01140a1701150c030c110a03150606050c03040512070b030106080711210906040b270102060403080c0f12090a020406 74
    0xc9210b0f151020385010b250002c000c2800344180c81001000411401e004031440c407981c07001448100e90050b449280e110383d0100c0180242070031160708140e074a926142242d2a08056000603000601d0382414103000c0e001d14007502c0c4075900a9a21003c154298410240c80d0000304c4e0b00900380241031103180182ca10080c0012079095244821034034281890782e00c00303a4846c450780e010b442d81c01c00600309840d00b02498100c2035103640c900d04248055842041021102d0301074081f06030580702d258020800748a03091000200728800007003603500b00c540c21100f1884921588030294244507198104041c01e901c000004100f242d00b06140c3c0d8000c660603542c140d85040c040d0074154030799400d0300c1035051890912614a10403541c8801409c101c0364014881460580c0d80c105444450348480d200e04145005410711140044440b03100740600c070400c0c0050302c03061900b81d4000b40201d0000b0005804041c0c003141104e010382500081e076103c86213039404a105414644455a900c3d4001d1004038820b509000d008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 839358633 1250 839357383 839357401
    0x1a1005090d0f060509211c020405060711040b0d15050606040e070807080c070b180f070906080622030503090c210f011b140c01090b07080a090803062707090608 70
    0x109290310070aa1401c104840400c448800201807803d51f60b10303000d11020800d59101d6004040480c442c00c025108034840c0400d00c402d0340c06003507880d80f2541c0c400543c180440d2021f00000d5100c00702c00000642d5030380e103030700145031401241c1044010311035860410401c07680210040d80244056150441c9540d602200004070344503003d001084c1000c01400b00d244002803c180a1024460748150f9035004841801107143c00b529a01040c201034681070204528501400340030382085446003a680c001c00914400b4581006820004082260000000c0e4600c1c90078054200c04040003004541280700302c2100c4001000c0c103403c02d00702c50151040c41d0390700200510a0780f03842e500b04402c4100c01c0103070ba9400d4401d007104100f07404070130104110038101d5100030f02c40d01264500c121209122401c040e41c00501c40c03200203180c5580c10780380140c070101180003103003503a50101c01207600000f9148108101081d002065000c8000000090140120680c020600805840c0b4a548002003a528051f003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 839359883 1250 839358633 839358673
    0x1309150305160506091311030c040e0133030609020f03060906030c010f0c1103060106050a08070905030a061a10050d0e0102070b060d050f030a05040302041a1005090d0f060509 77
    0x42d4a84c861420017080c5100e003001d043c00420b400c007a190002c0c0c102c081c0342120302607070710840704c0d078844650010f0240015801d11705030310b01501c01d076114440c06080e64043d801035401c486810b080040c018a20006c80b0794820340081002d0312600c102903480d008840300e03855450700183e4402d40702c0d108000020364107003000a80081c00c0c0c8016901d00c44450460002500c105040b10380507945100051007080440d201001074900038030007591900d1340c0780e64a1600038140d45010344010104045035000708901d60b40090ba6a40898100c4000100c0204218142c00040c01c0103d0305ca8203d003d0b070080350040c60300140540940d451404050080c0e032508006107080380300c5e03941c00905c4040e065021400e5800d00781c0a1001040c031903030443e00072a200d02c130014a9a04000394201c005800081e042c030450800c0d000b1920105000c401c118086000d0038001501100411412000c00502042e0340e8400d607a50190440ca4a800c084100d134102d20038200340d00500790445601c04c013807203101203980f022a41041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 839361133 1250 839359883 839359889
    0x10606030c0f210f05090703031112031b2505070920160b09060405120a0e010e0102033114010c030804030207030b0f07030f0b0d0602130915030516 65
    0x60744070400241d000d030100d0071014a0070f083d512181c1e510340e03400c0d0501c605e21403a8084c406c204020940d42c0d141d440d0040a00d01044011a519048000500c2c4110a14400c1d203801400903e54001140c41040c115801c50080c4a60050003545142c04007200800d0303030118080c064040c60507030344550745400040003610707482a0782030088500700168000b40b417040707405451040042586c1d903d000346541c030f94400e204401d5640b42002e4101006200402c00d040240200a074180d91800703003880082074028102960340c00d80c00d81030189850080049a109100326442e8910051218240b00c0e02c0801e2100308424602c0b081c03002545084002c80c0303406a0303482d05400c140059440704000310107590111016800500100e0540c403900d40013000040c0c0a1340308610135180d003900f600c5640303818600201642d84142c51040802d185c0804d11007903450f0001e8002001c0e810080140c0e039840c82209000194a840c2d10010180c0d181c0502d5440ca14500c0c407005084034040e9048901e00e80040008101d0110303a44 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 839362383 1250 839361133 839361137
    0x4031a090708030a030902030307021f1d090402011d04021b07080106080703151e02070302162102060f040b030402150406080a0e0a02030a0302010219090305030d09051e010606030c0f 80
    0x40004c844184c0b00303411000b10644094152418851540e0109544c07201409000300c2000c03074410028841503105e40302001c0c00050424580b01980ca810202e04e1f59a00a80042c1c104501906180c071030481c0c560040c482c00a02400c110350b900c52550ba0742240e426003100f04080382c09070060004032007105004000a4661810160040c9031841e51a04c040d992000b03000b144080e100c0880030141201c45160390040c121340003000d85c0d00c0a071850000d007030040321020325805442c16001444802405041c5104070f8940c1010030000a0150001416500880340c11800c0030000186c01300d0700480d204050750080313109840d5407440c00d0085000c024203002c0c40c0a81c80005e1115070002d02071051940058481c03410000903180054819004641446460351040c3c0c0541c0d0000f507800c0e404c2c20301c0c446114071052240b408214250031507541546031300c00d050aa0f04896162010f140600c0001e0006800380c1040740b01c002d41c070846200245010300918031601001c42e00d03040c1d00010b600d000d01c20404c0071403055 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 839363633 1250 839362383 839362387
    0xc0705090f0109180611040f0b340203011a090903030f0f06120f1f15050402070507080f07030302060a020306010c030c060605041802040507170a020a1404031a09070803 74
    0x901c034500a003090043d44800c1c044400c0f9a00100c0c680b8414000505400c903280d5640703034144001e0401100c119440807103001010020840001001e0b5000403c40c1c0c41d0524001c0040f184cac101c640c0c0802026035000e58507510307007907900074800107031400320a4101060755180c1c019038450f4081501d030300045812055903040c03100068281d0101d0044641c0c010380c010010000952101036042c0b03020304400b860955540302140c11005558021010344200845907014040398000d440300c4040e0720014841c1c18003e0317800dc214101006024809000030b40959801c903499504507540459481c1254030041d405401840086590780005008403482050180c440c81c0c0c5c041840c3d03400301d0340d04603100c00c10f0b6071165035204045620b913180e0003000e10400c00d08190b03c5050045004100072144040c01c0c1c0f80074403041c040364031540007003040c2103640702440751001a1a030234800b90079100c4054883d0050902070380000e010080040c40c5081e10102200c00c1d40514080d95148886541c0708100d0007000996441 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 839364883 1250 839363633 839363639
    0x13062405160503041203050d0e16090213030609050a031202040e06090717090a11090702120f0c01050109021c060501050f0a1b08040e0f010501051903140c0c0705090f01 74
    0xc815140304140c0e01c901c00b03ea103416075030190401090080c0e1800c0b0000788001401007101c0c051405086810480c2902a02e82c90100c1c022951180c0c0c2184103952545c0d8001c5042044001075090322401503070400c0741800f120002703107030060b12210f5120084010401003941e04140c20b1261007650191150001008840c0c0c4418003041150034004000c441000941840c0944507480c40303107103500a05221000740342c88100c3c3e01d42104418908001507000b00302410401000c1e070b41c002241d2406081014005a40c6c1c00c03440600341d054071031581d58904030340c00d1000000e5503000760ba0040107605060315214049980401c2c541c801ea600c0751280a00207101030042800090241c0020480c3c0d02d12800c085010302c284680440007120107550507103903540c000c02e081084101e100c40156026403000c5044542c1c2d07040600192846c05404214141040c268143e036400034080e0703101c64642c011841c04d0170307a6071030030717041002242e40450041001400f41c481c001a80b800c0808000d07000b440040b070411210782c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 839366133 1250 839364883 839364907
    0x20306010b090a17100f0b01020c240702060c071e09140109050606090a0f0312090f03080a050c150117070311060a0315060903110d0f020f0f13062405 66
    0x700004903000d45008800d2016000100e40c8503450b5104004840402c0e03a15541c7c0019052117811060700e402030080a144412390b5000700d145054a03c2d00c0050b09880e03503454004140503014520b40a002071046c403c0c0030030ba44c2d4805a041d07810401d20390001401135201e08074201a605520b448085d1041000010b22006182e600030b6075009802904072400e0404680c0003074108071981d441041201ca11010600c00e1200c28481100040d40c2e40c103100003140d1600421080009151001038400f400201303507001441e2248017190b0305040440101d884039003404680340b024910030701c100388040c1d03c05030744100900340c08107080085030f4000080b00611030591041c00b00607803160f03088004040d6550704a1614070980c8404902622041c0c2e42c400c0c00b107080d440c004040080251060748280700d00410700d40052102c507102c40b0380c030360b050310007045240640e004500745030400b41415038012680d40744260074141d268072400490380c0700b00c0800e41e00300841c220481c40f910b952011500081c02000060701c020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 839367383 1250 839366133 839366159
    0xa020102040f3002040b0d2603010f031101050f040602011a030f030f0c03040b04031506080109020607081309050114090f0708130c0305060a0504062d18051504020306010b090a 77
    0x2030002e0b0010a40c02c6c8a2400240d085581e50001c68480da040803140348040000e8500c034911a81071004140b85504103031101d403a615191000408035a194002130b503040e4031500a95490701c0701c101905482d07644842000c0e001c1e203516101080b0318544c0d502601254a40002c01c10020321400d00903600c0c21404c1103a0719950b50108401000030f204c00c000004010a100004100460040c060004284254143c2c40700b514a50707030154681c0d81c1860031500151369400100d482a80d03020300019039540c002c5001c0d40800c2901da2150b1059840e10000103041721074240004164001203803800c4880d50303140009400c0f00c00a403400d0000540030300006042461000480d0f020341e020725a41d1540d140c2d00c0d603580307140c0141192a10141500d13802400204400b0380116038070440e0110420030741022025070507801e84c1105682c1c0c01060b494000c0d509500e2040300030081c5c2ca41d0082d081d0344444d42c0100e02c0d4040090145c40482c068424800001090b075018400d40c0e20705c8900400810409141540f031003805 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 839368633 1250 839367383 839367479
    0x1090605012d270204050a0303020c091b0406110a0c0e1b030c160f12030b0f06190f1b0f0c06110304120611070507050f0f012003040b0a020102040f 65
    0x420b84c00c2101103076503a030b8145c2020055111364001c044c40c0c51007405205541c00c2c050701e05107510f0368680d62820241c11000640d01920f450349881c1c0358410404c00000d20b445511342c0e021340340341e000ca00080360504c0d50040061080c4040706052103800c8880150a03100d01c0101c4403050315900c00d0000300707000402820703c500e1181c0a8140c0d20200c003465101d00c240303001464400740200782e4800c081c0700141030000348500c01400448040d820a4034400c3d00c004440d140948410410948800d85000e10b0301030039400307920030100e2444019140356890440d000a903d8581030b01c14041c0b01e1000a4003c0c030490003102015407001c00f45040501d01401c1036403410384201c0451b030b5907485044007103000c8001009003140e2805100100081d40ca05803d0201c08840c40e041c07140039400c1000905941d0b6003010341d0440c00412500710031402058403083c98113600075a042903400301c00004404004960540291040d00c5506000000413a940c0c6005522a840381c4070640040b1580b0401032290b000122048001e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 839369883 1250 839368633 839368709
    0x14070b0609180d02010e01060b04050d030804080c0a03020309120c060403120e06160201080c16201503180c0d0b060310020409090501060e0919030201090605012d 71
    0x142c440080d0080d007080f80c0c04910f500140c0d590910002c5800c800d0103520014181f00c01514901810100450005413054001400b070082080100c0e040100003011903440040c003100355030380c0240f44d00d0001d403268050f00300c485c41b4044c4041244031025010450b451710040003081c0614042c5075950b4a10781c0b0080700032440a010559625281a0721464010055250502c08010380f00c030f950700c00504803060150000407011402c0c01035100801088191000c0990448205500500380d42d02400c440c151094800e90445005e0b08a14004001d5030059805154441544007001c03030301d81951950703000e081e90425404400d1000990215415502654000340c3c0642658046001d48030300c50242c1e84280c0c07051103100c0d915000c1a003130003400e21410020b0000000e0061341810f01140c881c0e038601d05600c408945001381641c841c1058002d41c408140e0548c050800d000c90340e5105421220005050130802c15506a42c3e00b00c160b0301043c10441023030b034900308448a524294801c3c604400c110400704032074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 839371133 1250 839369883 839369911
    0x30c0f050f0927101a18010f0611120406051e030609040f1109010608091605130216170a0f0309020112050907050310020d150308040303030f020d140714070b0609 71
    0x30b001c950703405158201d404802c17000412002d9242407116042c28a6041c1135000240001441540c0122401d001146c11603d054030000ca800003209050941104480c030107214000360014415802102400344980d00840c5440ca041a410102c40d0307903c000c4441f40d6101c000900000c000403030031149581c903039004a01c0100810318000c0410002d420a8004001180100c800c001d800001041703900b040e0030743d00c114594101d14140220348040908507501c80c10300c1e004511441d88460716400350000c582c010450710101e402110891101c0d40c0700c0340004000811820000070094000c0c090402100e0703069580302070400203409d200e002000060100760040c02003050019881d47c042050b201c4001c6800c40069940c00c0b041542001c6a000e021805658103c550302000400c1d04c0e2000d031411241c160038040b601c1c0007500c83d110f000348103510100b000d407860160186204403500e0003407071044403680c45604504a083c007010020780242d1200500c540020000103805040089107150400d070600d03507641e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 839372383 1250 839371133 839371153
    0xb01050c0d080a0f050a14091b040507270302010f03050f040f0c08011406090709150806030a08072001031a0f0d080c06070e0a0609060c020109030c0f050f0927 70
    0x280682d0300686d80c031501d42d501d459800d03140069080c2c0d80d40d04054600000c10542515904204440f0207164803a071086544c1d000151017640501142c0c3c003011155020114040600074481110003c01d010690005402010507409913010b44079041c0108010004800565100d6031002c41408050798210307504900c1400000d0840c07001d01451905100c82c600c044e80c10300d0110240592210020000d800708a402d400400c02c2552420180d94810124a001e403002d0341c0d080082490a0600343d0002c0c80d182c000038665081c00700120f060103800e50703e15190985091040011019154480c071859049007504207001039600d82442042403850340030b425203203000002e488400840d080a903147c103a94024104101c003907036005486c0e101c00082101d040451904000c40240b010869000e50802e005500c1c525800350380c001d0071500011a03000c520346108903210141e070502c1c0061072040354021076105410300001d1900303050283c4141102c800446112800d200c0304580300103075208603107050280d907140d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 839373633 1250 839372383 839372411
    0x171014040e070f0911120426030c19080603030409150e090c0a090e0d110319020c0a05060c1c11030301060c1e02030c0126090a060b01050c0d080a 64
    0x101c0240725144584070f00900c2e040b0203100380d64000c001c402e4260300c208401038007100100407180c2c10a40003c041c40d01d110001500441c081201c00460440d0301011040000782180040203050402940912500601c10100182c800100c241c2d64030740c1c1a0000e210600c40c0b100e1503404184820141e2000b100b42070380d00c4003400300b08402940c01802d55001801c01907901d0821002d20001426a120104031807006011101c0d261075103046900d0800c00080b180000707003a070400603103061303039010480b406c07807801c1e42440a50384d18000d16400b40908040c041c00101450000c056400641c51751004d041c900300606910b5407040c640c00c034408107028084d81110040102000a9030203442141c456201a4500c1e05000900c041101113418006681488580040e18041543c0f00001000c0c2403035a6132214140c01c0010f08240d095100015400d02c40400070f544900080080c00e450045104001380890480115800d22500c400ea42d0281e2045c4d038088003c500c0384404941c415080100080c240c8805816 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 839374883 1250 839373633 839373643
    0x30411034309020d051b0f0f0906031812070b01150c051b091b0d1a030a1b050916050a051201030506040c0510140f090d0c06171014040e 60
    0xb082c81d0035404101d01e800c8208900c65546c00c44161600c145205000e0302005525100c0c1443c40302c4001d8000c91403c1c1d800700c442081e517091460040c42c054407480d1050b5a11002132510324003c50900c10000304481101141013112122070300210940016030030012501c60104a05110030308021401c9006070209105102e407829842d8010342841d044445641080b5146001400c4004001d0320480321040d10030000c3c08490b00f4641d0008041a491001c40d00c1e2101802c1c0c400442d07806006a103104404c2000303141c0c1102c03070b21a2480d0707101c1c226600e07041800040c0c10704070748414159070701102d8000d0300f0707000e000135101c003480500c1c000389001c45207601005001c200b07a20407036296006c2014002040100b4903e040a410251816078085101d00c500600201801d500c031003400100085032560b4262040844d0946600605811080622480e280002e40942d200b22400640c81001580301c545000a03200d004103003010460039594200504c034440002100c04565000740d0791291200c4408082c04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 839376133 1250 839374883 839374889
    0x31b120f070606080d21090204110901081302011b0f0c0308090102060a140c090f120f0d0207030c0e091f05070e06040b0f0c10110304110343 62
    0x5009481e246a460320205440071a08250354607000703102d40e405c0040c5d114842000741040110404050f050441302d06c401001601c2010350041e04181c01550401c41071002848594420390b07844074159034041070381d0201c58401500030700191107821002000f01200014620807805603002c400a042d40740d4407004141115442140c4021011550030129030f01405990740c410500e01c1c00348440d1101c94105016640000c080c40c400400c041500060358840d0403a40c11842d001901c40203145181c0c40c521561140b0400d03d07480755219180031042d0191000c20100308881e881401401d9550500302010290f5000411005031407042200303100b20014203882e480e1314000a42c200054038204104000c140704124074841340198020001003010303090704000c0700c0c0c00854490b00181c40e0540b1005c80f906210b800400801c0650030300511080e11100c510065009a1148078134184c004042010300d07032140080d205140180750721206da45e6007c40c90a64052100f0300c02c1660403034460364810140c040c000990 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 839377383 1250 839376133 839376157
    0x1051503040c2d08030717160c0b04150c05060610030908030f0105010e03030c0c0d030c0807051510081c0203090d14011d071505040e010e0f010b090102031b12 70
    0x111014142e070420031031070005050004083c614142d40f61f1660001d171071200e10400001c01e40003580d0300390303904c0901c0b000c0c40503540a41c074100300ca5501c02c4064882d40041c05402e101d01c1c2242c03626010180124804082e1540c41009000c103580c80341c081041d010880c898144c245034443c1e120100140c2c5050003944200c1e00361100c074410f035040800052208a112200c0d40c0203910400c103007030b054003002a200c3c05044c4101c5240d8072582581c501110583c0444a00030044140802c52004209003c00c04507011a104131015100d592030a0704030049030940c0c400d1400c590401c03800b022180e802c08000741400120342c0100c901d4002000c010906401201c1429078804006030403030081d001c0c0a001d40d0414403003022455507009000034229031942102c1c80f6000507403180b00d142c0010607026506a500401c0c20700d502c0d0304107680d40c0f100340d40c10010031a041d48942c40550004141d400e81141511410481a4011401c1c0344006000440050000ca01107015100d0000b01301c4114044000070300350364202c0d13 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 839378633 1250 839377383 839377439
    0x6090509030307120b0102030409050603030c0a0c180b0a050d240c030f05010e011e0312110f01050702030405040911030604030521040515073c0801051503040c 70
    0x3420021300c003450f1880e030303441140e08042101441c3e0380d000041d6000d0304e501031000162921144006031031486408010710b5a401010700005c14482041154001c50b11000780c00e16180c0580d41d101c0d0221740c455010280d101743c610380140b00d0360600100c441d44052107600404030070030b062890080268030700d1040700c007204d4403076100c2c0007120b516004090f040a05000c0600542d41409a8806041014003442d010540c11045c0303140004894040c000045400a00c590300041008000405c0c024600701c049600c0c0c41203402c1039a18110506c5803d01c07590103035000c4d5081500b00b404020290920b0b8a069494028128049280b603405006860140b0300ca601ea180c0c1d00c0002044420348816048004000005c40500708000f04501180d0303240100c00c4621000c00b560389881050310260030361102569060418210401e0328143c0696000e81010803114110348403052100c1210306200074040c8540007100241894038100d80400507680081c4510360350500c00e52149928940d0409482284a106604c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 839379883 1250 839378633 839378641
    0x1c020d0b04150503190c030b220c0f06020d0206010e18030c0c1504060c08030a06080d0906140c280b0a02040317090f12011104060203070c120222060905090303 70
    0x100017007081c1e1168001000160000c0fa10713408002c03130080c44050001d203034120000b482d82c81c401e41440c400610031a451400d0850710f09080c0d0780004503000304100c0c80f1041401185481c00011000041c4a043d8000e100b581c2c01c0130845151503402400d002c1c2541c20450174601c20b1082400030f84081d0500c50b0007480d05810b00f00420194000d008094110000708000c140105503211105082c0315400000d0242e0f20384400e4207104c001c2006a02c000c619010b2540f9001c00c0603400800b4800300c50340d86d6900990740c0c0d00faa4200745180304508040540c1da0103d44201d41c000b0390803090701300b10b0a0720541c00c40c04220f80e1b2034501c20417100325144003103140c0c001403d008200c0045540d031041c10740da810f40c1c3d0600d15140e0205208100ba0341c0c0c068170400b484002241c19041c01d4010380052002c0341802507e8583d5043c000c0d561390860542118040c60307108001c101c0c50825000310390039a03001485042c1104000440213850307241844ca9a030f0190305d4403804121989a802a2030050580c44021550303850 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 839381133 1250 839379883 839379889
    0x10b0603040b240627150a08100f091b09290d0e0f070801020f04030201390302060f04050d050c0c040203010b040905360a050d020604171c020d0b041505 67
    0x340172400b0b94840c200100111811445042c2580d89010b01420800040d803515100e010030a0087e9101c41c4001c1c003000c9003c9009482c2e40c002e80ca51092a4004003d0f502c0c00e0399003950446503074024055040001e0406140300701c1145151120f441000c00351310300d03020385008484240c0c0d0f544d4054402560080e508a5210740007000207000904041000b1403c10b06c02c040c2401442c49503200203810010794803d000180001e5407200103500c001212120b050b10150640035524007541e21094015004a50001d0300300180f503c6140d12465102d405800b603c2a101c0303003a103854110003001c1c6464490108000600c0d02c8620040d030103400600422500c503886d00042100741e070001810032a88442944d510300100c030555000c642459004048520b855490007505490200e042c040640b0a00c150071030340306141d40204184e40140c2c0905203c040321054100c0142d41d1b4841c4244520b026866030030100540c990a034064242820700c140085003408102000034152200407107800f90842d10490100214a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 839382383 1250 839381133 839381197
    0x16060509150c1c0506061603020105070905031212090f0a0b161107090b03010b0604172415180a1e15030605040c0e0414010b0603040b2406 61
    0x22000700310851401030211105003862042441c903582090720384c800700740c495032098113454401e200411000c006081c0c0341002406003005941c10400f08420301c40c0070449080100710078070248030114410745071140c000070740580154000c1102e88180287c01e000856014107100c6020a54005d22161101c0d08041255010807943c1034103107410300003424641045554080707418000c403188260000b4086071203c000c031780900030300d2001a510040c0010080740d0b100b00c4101c20302038030a04004542c1300030600c0c841c4c43c0b00005103180d9804004854000905038000242040f20040405080800ea401d01c0c428060f00905040d21710080c801d841381d8a00c0380442d500700c80008044840070b01401003494a50420700c5070f042d170340005071060303484034000740500450b803112400a0030040050101c0b0b02e002c1c06c0c040c41c0000d111200300c1955003454502c01162400c172050b01e0103180c010861509a446d10300f1100f07a2110414403025026080d043d0110960b914070020f0090103502a0340b0040d0303c8140d441c1d000d511 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 839383633 1250 839382383 839382391
    0xa030c030f30021e130509040312090809040501060305090c011e08090f061306050603060408041214011a011403040f0b180a151805030904021606050915 67
    0x18a2164076001081108030800b020080200c0540b101050200e01002c2c0c420212074204404018041890f400703403000040205007440440c0380d2081d620340b0b0420512490989001c0c2c00928422000381248282c0c0e44800034541c4034144861422368018085416a002684144086aa1817042000c2000284a00844500b0902e03260140f038802044030000e66001c017030600304103e003c01c0061081c4e441080a2200c044c004000c80e165890310316040c018047c24414100c41c040e05001c0421607605000a4450281ea8010109401d05041244030894500036241c02d03154008071a50080310aa02842207902c006450455440c00d400000d0014140361a00141500110700800c100804540c00080c0104c101d03134803902d80c1d16951144070f402e08841c00075140820041c061001c1c20000c101600140200082c0003600c24000306040c5141c40005002004024001740c10422170411545020b500518090361070ba84600741c4003030140c40d1102228001c880310550b590110b4940d00019040d000d6050384 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 839384883 1250 839383633 839383637
    0x1211040518090613030e030604050f070609050105070204240906231507050703050313061e0915020703150603030908061603050601200c0103050c04062109050a030c030f 74
    0x1c0750a01242c0c2e903075240401800980c0008640d400c503c20144034128001d45004001c040350789606003424030980b40c440c102130540340c41c442e030200010030074051400d03c0100c550507160796091600c2030b000e21001e131000e04514030a0301c180020303032501c1d00c0380046060094141100005221401c00f80342c0d1074582d081920310000030503603e0110b000b070740e9a21941e90061280507501c0b629490b43e864000d16060140e080113019000103d03180c164041c141d003226003101e04a544d44200c42d0840001600695070b03413110807001840b465400c0c070101401c1d050300801c24107944100c513280780c0c0e030b078540c642292507060094a02d01e80342c1e0401c00a250f80850720071f01601c02c000141c05207040c8401c0e114415101c80781111b060586401c0054050381c000c0e020780e504074400140b420034401016041a468080105006000ca4500400b1030301a0954205503415109181c448004502c0780d00c40c031400c41d195001c8250b05440d166a40035000910a000c0503101e01e10035240d4030303d0f2a101d45006030032003804082c0c0e038003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 839386133 1250 839384883 839384929
    0x10e0606010c0309271d2a06070819080f060d050a03140d0c0504050307050306010605031308090913060c05030907060815030d12050a051003110312030711070e01141012110405 77
    0xb011f00d40380700304841c0056044030101c6c0d071540c6a141c003100341d001e000c40d18400a40070480c0c142d0030704c3c1c20001a030310462001c0d01a13400b82d13941c8801c011003803040070400340481d4082c0c42e01d400000d010708441030300e100c845c5038918100054502c1c048140d40c108030401000030000b08007000300381820044000901001c80c0541a0f560400100404034000148011008034410801c003041c0321340700c4102d03020640c028040340d80a2a2010032110f991803064002c503415442c0c4282d801095110700c041c0c2e030040c1d00c04030140080b1807811404489036603001d04180c0d407085c00c0e16400382d6156800c000300c0003085034035115040d031101100e080c00d085800c024140d5040e2030a01c81008070074450080030106895200c6075144c80e0040750800302c4d00d850071340d0b820183d880c0000001d10241780d4101c3d0300103c511020804455816480c0e02d100c1089450038411141078040d0000d20385201d00d0715000e200b203001401d1a141c80c101200c00c9001e025100ca0080e440c003003143c0054148074608290400322056500851110 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 839387383 1250 839386133 839386183
    0x40302010623090f01240e1903050c150d0903020f03030709030b0907060c030311091e0a120b04120c05011a0111010209010c0305180a08010e0606010c0309271d 70
    0x10400110306c241c2e88035000c065041c0407a02034040d1010064000001d010011250703040c1e0045403010820740002c1d5840c1c800e00d00100380501d4814a5940360784460711009080020740c4400f0360141043c3d100440a501600e100381010780c2c000c001641c8200c8055840d43c16180c034504001d10110405070000311550884241803100302c0d001a540c43c100740e81417070001101100404240964014190101c0d80310000c9103844180101181140303001490071039003560411b9480c3e02d8921803a00c5140d005085805503000640420b0807030b165482096500d06100ba0665425901c05d400c40c0d8000c01000001e06181aa0f0040395a0022028101009140085192281d40710000e808010440c10007410032200080300d02e42031180304000040c40c040581801034041c2c5952015010b09214903540c00350380301d0341000481a40c03044210644003505034075680c1d0541d08104003503840b0340648125500100300c05010a070030b03034507034801c03495070360b090680d4200290303540f000440c04c1c48803003500c404182419074004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 839388489 1106 839387383 839387399
    0x100801032111011e0b0d0201090510020f0a030804050d05030403080a0c0504050406030c091505060a0e0d140a05070510170a06030f0b0f010806040c030803040302010623090f01 77
    0x148045c80c101310500c0f680e07009444010380029811a420811820000c1d0300d8a404c0007184161645100c1320b44e100382c40c2122040d0304500140840d0208009c4c40740a2000203804541e030310b40503155003002c1c1c400500700740006d082da000785603036849074041040c0914200c0d00107040142050040c181d903030800045000d07991184010641c20020b6544100d00f200180b6030558a0040c621420007119200880d501161901841e40041c0c514030801e011030045a000980080550024860683c0502e4a10f0401c02c881e0721140c06800c40354110503140360405000013001d0400e8030440203940d0f480c611000070700410742c03004c0d003190703490f0031700001340602d000b2054807c2420120161069991302d101d03a5544008903805800f4131505002880010400c000031500940244000300c0d48a8640b0078100ba60f00d2000001c415050752802c11100a00300300e4100d6900c00c0b034070308020100e0340c502089c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 839208633 839388489 := by
  have h0 := BRFrame.cov_init 839208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 839208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 839208633 ≤ n) (h2 : n < 839388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
