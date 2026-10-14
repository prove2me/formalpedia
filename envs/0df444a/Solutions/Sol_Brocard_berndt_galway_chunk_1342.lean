-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1342
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:28:58.500364+00:00
-- url     : https://prove2.me/submissions/ae1b63d9-60df-4d9f-98e2-fa53473de05f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 241187050 ≤ n < 241366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 241188300 1250 241187050 241187119
    0xe0c0f03160f0f020a03080702010b0d0602040e0601050322050c100503041221050c04030f0f030215010509010504020a02010e1c0816050a050c07050303160312050f01140109081902 79
    0x111701000c42d00420b8003680c400183c1c07001042070b030a180f0100b442482106012540d1940204050101408040c0c0069002c030f020301e0310038290319082454910b0f003112448040c0803039803030800010038004103000c514120580a072041034110203040005040d40c1c8212001c0d180a140140d81a506511031104001c91017004440340260302c00d0981224010314003e02003445a0404000020001c0c0c031211090242500407008180c83c0d040d141406428030003910861110282810014010b40d42d03007801d141e040d01c3c0140c03001070f141c07071803120140e00401c0d0100c840d0450f0300c20781458924509084210ba00000015a0303402007540703c0c0303100c04140035503242051002c920280550a001c903c00c030040c20341c02c0041000c41d5500390366480131908551000340580001800c01a0207820700d600070013251540749055030104018a468007a030301c21801d040c090030042c801c0c0011741264980c41020f00c80041c240002c05d40721445401a5180c075810007601040340100c03a0b219481440c02d49001d59103851414505 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 241189550 1250 241188300 241188313
    0x60406060503180a0c0605210402060a05030604090f0501051b03060a141c050c0a140d0b060d080301090b0108071d0d060207050d02061506130e0c0f03160f0f02 70
    0x9070041600d000c510b201054030612660030082040170701d842c8018070040e00e80e1581c801d8114007911981c50342501040ea6652000284001629003004a8110b03458a25003070703840e9207484001074043d00b24040c0190400d00e4000e8000c09101065025170b00540c81744200180500080080c20114001107643c6131f805090724504110030340c1d180801c001e01e02001000400e04c803101d4148402c043d02031041c207496961140201c00383c18100104400080c00700d0038100c03e1401c0790100001d0604207a0800248174070f29080215144c3d85404121441c072503404543c1035200d60711400480010251481c0a0740056840307804224002d002e403800381e4071543d817001003010700d40004080c0241c443c3c4401c42120026401c12901004c120140300d05c2c81d540507141c0c060820713400c004100c50340c164619050f2902c00c29040000c01090380c000c01c210000c0780c2160320300c3c003c190358400c41d40200e4090418a00080f46002081000b2030b0114820942e015541d03413100003003903c8040084540401c1050307018056030185 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 241190800 1250 241189550 241189561
    0x20706020c0f1c03020f0a0303050603010c050313060f020405060d02030f25030515120a050f01050106050922060807171204091d010e030903010e06060105032a030c0301050405060406060503 83
    0x5200c1007202c2130090040b6682c1c190041c004030310748184a6010790000765200d0900203589002e00541c038001d169880d11604506280324a0b00c0c0003400c2c004010081540c1d01e24030b03c01d07070880ba01540d0051070000c0c0210b81b210007014051019500c2241c20321081d020000014070403110884044640010154122052101c0d011083d001014041d084e04a461421741852035141d0702e0644104990001d03c0107000740f0303525841d01505d015500c402006060741000d00500c40d82b603002003520199203040311007000a200c0d0200c0f0000740d40ca254481d00032981440701c0418512000282e1004541e001480c243c8005200044603445d8401580354560303084080000f08500e84e100d400422003550030782546d07a288a440401e047c00c4422035140c44000d41c0020800894500c0c0c02e105808002440c030019014502c1c02400003801844014680581140226810501040301d13003030307201c081301b0b80a02465076402c1c103d000c11a41c3d007091007410302c00d5080070b00040080c10240138203400c0740d0306c50700d600f410b68440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 241192050 1250 241190800 241190839
    0x110d090608070e0405010308040302090603060c2b2f070c03030c020103140708070212031608040c0b0d060302120c090a0b1c080a0305060114031b19020706020c0f 71
    0x18012800b0400500f0b5840b81507907482c82564002c501c00d211090f41d5a282d4814002102002842d06101e44c220f0420040c2e8441850100c6000000440c200d0007500154101e4821034400d04840312100c520340244103411381c0500700d03090840140f013004107000503603802d0104264440ca0b4002455030f520024100300090080c0210039500340f0504020070b42034074646d40150380f440100c6040002440e214140400e241d01400024481612107010034a98505100f002003202c010455001c104141c4d10001400e05c10911140c501406403011071503500d42100314a20068031640c04140d210707c000c4886100c007248005403608a410002c1e00401245e030322040030318018498881c405401c12003000183d480c02d1034047c51010200c1c0b0880b85944c0352000568000e044400042105050002c0c1c2520710555050820543e82d004043c904890021b01211203410381600845080002c2c20112400c06043e06801140f0081500d6065003200c610440c00c6081020042007a14196044011050000302d41c100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 241193300 1250 241192050 241192067
    0x1207120b0c07150b090c070b04230a11010e0409050c04090602090310020304061a01050304120c020d0b180c0a1412030a050705060a09020906040b0d1b06110d0906 71
    0x120041d0716040446649607001551441d8860100903992111207010902e040403090b904801c048180178109a4250f40710f00c078000d00030384098807403011008100b43e0b500d904844103a821420134207407811003401d85003914000f2240003010f4045120030107080501e05103482541c9500307400400920340c2603000800e2000612900b0425194683c0802c8074407215201006020560214801c00581d41c0c6000c0c00c241040310940404880e55014000440182c0c0c0e0340101582c2c0c005070030803007429031140b078400107683c40307141c00c07800a4104060351456003c0c00a041c071201d128941482d41c488200301e00c0303c3d1158403500c001c1e540560201800605020301c1894407a00b644591000c3d2400c1840c814040c00249140c12010030f50700001d0001503402e0070440700307011454000380dc900381400700b00820b42c00203006c1c07040144114040c99840d650307510070382d642c0c945a90417250885031216001940740c210112446040c0506004140d400019407079000700042c0c031000c0d250b0242d0b40e50700400c3c204107007200c4480 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 241194550 1250 241193300 241193311
    0x6010906030b010c02061c1d21070c03060c120506240409050c070314070f060b19081608070f030201050a0908030408030d24050906061b0105061207120b 67
    0x9a084c650068603418010f003400c032150742c001050120854064800e07161900c514510088550341141c3d440c00000621011a04622582c520f500c94012072480560003550307400782c08450300060010520144d60301807803130303204950354901c00140101c000701d0580710300703030382c3c6070781101c80700d22400c0d0b8401c2c0b011035903901340f400c10785007a1800b5a0303408080181c0c0c000340c0d4040060320001541204141e0804050782803259460120750414803d038942003c000c2141c0303406089207480c0c0300c0300359080d034a24220480380c1301680301c564080c43d2146000d03907549000c156100410064040e010440070303c0000c40710b040b95021034040103001d007907900444082d04091014014441e00110100f50074005101500c09040c641c0300840c1c41d40030941c2c1c014280c9500c100205c85428082c070301d0b03000c0c0e283c8006030401a030700c0c2505c804c03403146c0701c403804140c00348100282d610114181d42d071101c1c220b07030043d00b040f80204001c4508488000d64814115100c41803032050041602d42801c240002464803c0c0003540034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 241195800 1250 241194550 241194557
    0x3120f0c010509010c1b030503010902030408070503030702160803070f1b120803160f0e120f030d05090601050105030903190c0b0f0702061b040e0a090606031406060301020306010906030b01 83
    0x210040361040c2500d00c10346068280740d46415442c1104c0f603001021401c644100c000102141c801501c0207441b40c40306000300200c03190000000390500558100722101380e0352201c12079a45c4d02d4502c0d8001c0d15070814200e0f4140c201d5100100203840d6400000340e0b15110b401005801d41d020265807844002510103020310840d1010440002d090311881c040080c060b8000c5008581e2413031f00aa04400151408a05005000740da40170700016682c0302d41026aa07207800d5888802c0700101d28140ca00d0b200000c0f011654078440040d13a114442140e81001c2d0007852814200c40d017513600c810040d01c090004880c0740065038000d201c9869981b000e00c0603980304d030b80316082030140d211464840d1140032508540f0701d0207001200041c00001a41045038640c814040e60340d03413403012940795900185104134032881a442c0300741004100314200690000c42c01e5a0704c484104909540da10b00b80c0d8012190182410441c00f0b02c400041c42402c040c000c59110319416500c4004c41820b218064000744001c5800d181007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 241197050 1250 241195800 241195807
    0x20715030b0f1005071a070905090405120c01060303110a02030607181809021008040c06050a0e03010c0309121b150f0c05090a08070b12090f010903030207170903120f 73
    0x803074582c2c01600403c1c80c26551000d030740d100740d82841104031010044e01c001c0c40d029082048030440c0c0c8004002c0503601c0490f00400c1c00e0f00d0301d041c101e207022240c400c442202800010346135548801540000100c074403945a80c0c4004002503141c980f140386141d00030350150443c00010711f68502c02c00c440c88180c00b44010f809050350302c85551005012000c92803920065541d4107060a41c900b10444040108003441c201d0540e1501d0b0703440c400d10594a21980d4140800071a000900d24010188130406c1107000d8020032044040c0300e001000303040011015100001e103518480082ca21601d001c40b2040d100d45080328003664503a40d605080c20b202e0208507e1180e8600b903000009001d40988030326031501e50f84654035542500708002303804640b584034000070b80c0801800c01c280600c8100355200401503070946240c42e43c5501c0f103d81849070400008402d075182c0b00c880d0007059050350141054a002e0303c0c0781d4080108070010200c1a00c9814030581d817561140794042c046100700c0c802400c6203200200070a04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 241198300 1250 241197050 241197079
    0x210717010e1605120a0f05010801020a02100b120f071508090d14040b0d0902040f06180e07080604050307110a05010e0f01030f0906051e070c0f020a0506041508010501020715030b 78
    0x311303218150782640364141c0b01c1c0411540b1500500807035016004582c002c602e40190241d010b9034921001c6003038110300d520f4480fa26841c1e0b5039582000006503445c1e064400310705250007295282c3d00103000380c0001c0025203004807852441803000c03511800305000145a449640c010aa40061840000b410848001c106c0410b240c28180301a1862460b0910301044000042c410842075a03000428402007a03c3c0040410103005a48180107072001d500300b0010360108800c20890515240707401220b450711480c402d000820070000300901040f8000c81a003208440d010003040000103140c0300e0140000c000761001907003440d01c0501c2c40c1414405060000c0d642654004400a9410085c4243c500580c4c610070440c804441b402540a074200514400320386150040000e0f00b280c50b0040050704a40820b1584d1046440d501e01242c003a14008100315101c0340d8661551210300501072200001a007290000207541d4000161035058034860f5035124282070444600b00d0080c4070001c0a1503000304c02918609 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 241199550 1250 241198300 241198327
    0xd060b0406051305030d020a0809190b030403120b0a050402181509150a1709030c030f04090c08040b01150309080d0203091501080d0c0503210717010e1605 68
    0xc02841282c03074180e260101003003007030070740a001c0e808540241c2200500c1032600380e0100d40d02c103140343d00000954039828605c0224051003180701403411080c500440c041034240a440155202d60320981d161051110400220401d440322800380d640c2040e08808244100e1070036030050032076101c02c24248000c0c81a400c0000709800001c400842501e8000500c200c25818080710807403040b121118001c0c41c01100c0750380107090940000c1000c1c03054507a0008101c03440700a008130791084508108880d10303207000c1c010300c5805500034440e007000c0916201014901d507004200c958490764029401201c140c0c1781118844010003e000e44004150703840c50000002214180a0f1a401421100050300c0740f0b4964102450201035840d5101c1c0003d450004005004000a81c3c501555a91900d041e0804562604900e54001c1618a54241d40d00284c11100300c401219414403178004c59031003006074a907004c2281a1240280a0907a9948644001490074040d9071081c0502820500c1c0c4103180003c02200072 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 241200800 1250 241199550 241199557
    0x3090a060f020c0a0b0429070212030403050601030308340302030a0b18070305070c0f120c081603080a0e07030f1416090f0c020d030c111516050705070b0d060b 70
    0x9018480e1702290078084003241c100740d81c90300350b0f071420458140c0d064005203144a00607458000d1003049900c0e5114031806c4280191802154002c00326449961070740f0b03001d000700b070307007100c0700310201818030315900c018400d0070050000450705500e201c030140111541180a50700007043c0d00340460300c899607078503541c440c00950181c111f0301014440050400310401401c0e200081c150b80100102c2910403004a42c990340507401c115403100c4043c400c0ba40d03c80040d22112064200a448480b010032540725400c4c890049200c91303442a91210610303034a01d024202210300c030000c100c9180c0d04c0081c0c2400091040c41040000360300507110340c1b5203902116286850310484c0c0c00049030084027060b0802039200c990180c0c88d802055860f05100ba9650310f1402551601c2200d111401c150f201d02e454a000f078081c10b043c400380e0890105a440c02c999440031003425000640d6102820003c25940d1580a07100f203040c2e941080e0301a0190541920382011942141c06c8080c0e60f140c901d90310380000071100c00d0003004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 241202050 1250 241200800 241200809
    0x21b01090507060e0a060c1b08010c09080d0912020301061e09051506030f060109091a13090807030f1e0801140102160621050405070f0803090a060f020c0a 68
    0x440c80e40258600350b42410b485911150902c00007124580055440750903480903503900385803149142d031f41c41c00e010101780100743d002c204144a10303a010500280c1034000181c4140d1755110300c1203081d6a4a07600740c0e2101c0311065180048c0032500140b124450700d101e4035010701c1c0010300220300c650302c6030009526110000b141a0340c0c40030340c0d40f0802c01e1080500469510202c1d2061200b4800b034600d01049403440010940040c201c00f20002801c541c2c002c0c091100a40200c5404000d41e00510b0940c01c500c5540250b11880351003030003d6005203280c42c1c003401500c80d41c080030301c0e0b0a00c01c50b41d0f0180c458010849101c002d01840b0422429910030b00c40c80d004906455a460143c10b525054641c1103071a02408060704541040f068090010011309600040340c200c4d2410060030a00c41c1c0c01106c0a00f60990b4098025080c00d080c402030140004410b0250f80110502c0300c11140c0e140c0381c9650301c0c40303544d030340c0c5030407c11420040100302e00482080d04000d4040c01520381d80d9640800245030340905810 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 241203300 1250 241202050 241202053
    0x30f0f030105100203030108030f0d090f080a021b1f0c0b04080706060605090906190f0803030a05010b07170319020d09200307030f05030f0301080318062704021b 71
    0x104014078021991200f50205800030310700e95410800199145d00c520008189030300000544500c0820596000202e82c40c2c0003000354200c4190391410141d29030098515074014465011180301d0b02d0809840d840030880000d1011080d4003e4804041c1014034100c5024123000d4024014804110702c22540c900c10b80c801c00d280d0303540d690185019800c44c3d080c0d4015004200b401e008070441912441b080580110701103881031444040603000e4101c0340f10702d170404d0301d60940e0000d0005814800102039400780725240070034070450380c071032090002e14010080c003d4180f482c01580d4440324a80c000042d03802c0342484908031030001600c0d07100740582c2d20040d804280c0680c2c4205440601103031411741c100021590385000551002440025070720480c9000203000d1120100100c070800801300704503081101807882c41612503070b5620031182c43e0b03040f0b69002030503203485111540080c60210200c0d40b601c1a1071001881c482011000e044075500e0242d0074036000f07903080110b120b06c2151800e04200700e180140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 241204550 1250 241203300 241203307
    0x130c11071403240a050a0b13090b0f1b030c070606080c0310110f0f090418110a0b1804090501020d0605190b030f070c1b08011b050301050f03030f0f 65
    0x1c0c1854581601c5401d10081c0404858810341d81d07503000180740e0340000c80b000010440b40c8501d40040000c04108020700d50100070f8000d000f05041068020400c681e006511000c2241c1c0c1d20007400c90400400c071a5004503c4807040040080d40c501806141c108000e0a440c034188404c0e41d554100322607031508070405c5a030140e40010b00358a0304000440101c0c0c038065080c40326003010a85243c09001d015825150058045116400c4011900540750780b1400240709100070080b1030907102c0303a49000b0078140c2d0000ca6030440402d0600340b5a80302000c454100003c0b600c0c1800c0c8100d0f141e5191108981141d0054a0302000c1010078002d0028289451036450b002402d40d1400c41040001c0d941e01480c40000c6060920030041c0006407001e6a0784490322010118040d85c40c440d044a1094614a0040c041c5591000001040ca040542a0207407400701e402001300d50b109080c004207518503c444900015810001808070381001903c161114101604807801d2050352405003250760800000d804a111012 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 241205800 1250 241204550 241204589
    0x270f080a050319110a0c02030c06030a060305060916050d080c06330607081620010806120c120f011802010f0c0302030904090809060d0f0506010e130c1107 68
    0x141d4500400c01c48060300704900903007030f5109801802140d005c1c505014580c1c20203419900c0503c560b03103102030003d1105980c0d26015446800419803404181c62500c1514001800c4000005268184945504c4141d0302c0c18505020401140301c0d880040300d0001040c0542606032404001082c052007a11303010f11006a5402040e8049016036003e00d41c031003c0c55020300c0e41c96142c100031503012a801c40c03249555030f0a02440c01d045500303520002801841081070620b908501c0c0780c030a42103810260b8030302e13006440d00c0b000c200e06201c0b040590441a0089000c1c3c040510f4030281104030710000c0c1d010f48135100031440c1d00600319074688211098880340d034a80e08045607404007002000c0413440c1400c1030078140c0e40e00c0c002d41c1c2e4010070886d10701580d9681c030820300b4030203003800303079030034500c0c0100546d41d1000300102041c080d1007501c400340745180c24075000ca00658010020b803c4d140d40041c01d02828240e034446914054000c046031807081c0324129100b0300d04400d043c08071801030520700900041c1012034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 241207050 1250 241205800 241205821
    0x909090303060e1e1801020403050304080f010c051206091f1d09030a02150c0708180a051215041109010b0a020f010501060804060c020f030301140a09270f080a0503 72
    0x104030780700070318400e41c0381051840d00d241d900d0b801c0620980803000c9140d1504111b40213100702c1c0c001800911003c038000840000004902801c82040070081c0080e6564540a6440c1e01901742440d4005e1402e50002e07000342071000c04503601000c0700030f601d02544912566500380c40c150b500181060030504140f68408800b20003d50f42140c40000250b02d00343c001c6000a490b01313078900c0f00704c0d10016a80d0224180d0200c080c190f27403110703412503002c90b42da203600030101c64100800200c19000380c40d049000121881c14418581c84440104003070000481c10340f803880e440c0080208101da07800180da4035601d454890350301a5018100b8012825962207041030301034500002482101c175103a040c4401806925444100e0759003082d4080030108250b2022403041c1d0400b0310a604e2891030b40f1000c8000140f850072007a000b14024400c5d6070750302400f40c0307494a90083c2d406584402c5000901921030030b203402c150b000c21000c51030003016200c0315100b0a42e6949000e078849011000000d1021040c810711900 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 241208300 1250 241207050 241207079
    0x1104090b09150d1719051c090b0105060a0311040305030403020312030108070e06010c1b1505040b0702090603031e0a0e01020c090f0a0f15030302070608010b04030b07090909030306 79
    0x5644564080400340e41000030400c0d0031080c00280003520803213242d556008010280c600d5401e4210101d59000f0a4500041064001c5038038142d131540c241360207041c6005c4c00e01c91310b500b01da080703444400300713030f0920040c004036a000d0b22605041503a250312035403400b03103800060f1014601c20400355948900c0c60040518003461203005402d540b104000400c030b60100000c1000481e0b0130002203115503900d1500581c0d82c4070700c2034400341034204c04c0c2005050b106106940303030b400e50b5466980c022010000307035011180c50046000d6004815410050500507180201d2100c1d84800020304691a001a01c00b101c00600c4501c8a00540e07200003181801e40b894101c415074201d0802880100314030408c0c07000241c440c0b600a0454000f02c512500840c07032603801a007145944d00186042400603140c6507416401e514424071003035006000307090380805c4c818032503034038641210102c071816410941980c0301d1001104000e0604414407502d404000360802d80c1e40036110721140a6140010054904124840c0605 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 241209550 1250 241208300 241208311
    0xd080d14010f0b0415121d0d020304031a0402041b0804110409200f0d0302070503010c0906020601140105070b0114130e0d03092a08011a0f060903011104090b09 70
    0xc1e0034000911003d4010801c0c2c804030780c0e580f20b800c2031a08078810709480c03608070101408016801c10070720540381c0c202c1002c10400003da1030b0490780348a02548040f43c407070250f400010503081d0309021811440e1498104241c00c6400200005521030054401000c01040034840310003080c000400c2000340420040655400c00b0203440601c03500c0c0c103a55a910b41c03031549204801007a40070b109280584e80399416403101550f0040c1c4202250b04141c00c010f0b40d142e10501c00d940c804d40c01d0600c5004894882c04640d801c80e58507400800c003917424102c4e402800300002035590f040000c180300c241d004c50410400c440c0285000c108000030201c051041c080314020300c1340011411420a00f03c00d002c0c9000144100300d40000d45030014000c9254944418a115000202c101103041520070308450b1450000490481e02403030000c200a001540240303500107907100394a60b100d400d218003040350341403c5009005450005000044c45000300b40d010303020390895040300e014103076074a0403208207044c04034442e500007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 241210800 1250 241209550 241209569
    0xe07020c030c0d02040c23090f0a06140c030706050f09212a07030809030f010b13091104110408010b1503220b07020303070f05070f03030b0d080d1401 66
    0x950822010480e509600e000c0280556506c100d03c0581034412807070540008806440c81030064400c548a03520764200da442c0303a2140b050080c0d44400c0385402c100d0344c003c48040b611100900b6020381e00c80f60f2550400c030305050241c041000300c580010386921a00d403049420095000a50074502d44a0780303014101130041801701e481d4140302e820b032944001695a81c0740303840400070110341111044075500722009941c103c1031288413008800c03c65164090410800705604494039808140201d500381da401100382500454481181002609250801c02c162400350400040000502d00807408492400d80c001160300710109003801110070a02894442d01e1040700c900c8100004441034015a104c00360803480341610f070348101a044100032015000482e00113880110901d090440a5240c1e030045950a0001d42c401e1544100319000c3d03000d43c0d038603030380000001c60152019602a00103104944600e45d115000712004000146100000c056003004514041448080b01908085001041c0c200703040c0c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 241212050 1250 241210800 241210813
    0xb1503040215031f09020a2304050306130b0603160302010503070302090d030c0201081e01050d05160306020d0c090305030306010e0a050a030f140105011a1e030a1401090c020717160e07020c03 84
    0x12644602240b008c0d00c1100b10345082409000304041c818803942e4490754050113841c08011210100322540c035200c500845940e042c81d075440c010980c958000050b091074540d05d110090026511402c040d60348012a420300620340222100060341c4903007032420840000d40d0f08001c400c11540d0202040350060713040110500350080142807400c2c564014010940074981041e07501c014014204600350052014901801a203038aa062607800f03944280000100a4280f222882120b8815040301c402c5030b401030003550460326074600445d500c0e0740704107946130300146148010a4513940e8014000046110303851141400c4501e2802902c5100c3c4c3c007880e0883ea92400c001081031031110344402207101d20085206130385640c40104030307105c001c8080c03841004042c0402006140c0060303900c490006c2c50800040421030f80d8034403050042ea03440f48030020060f04855410064191900f200410f00350f44801030b607803001d00440300c00c6c16040c0980d02c007204000f14442404411038042c4942207500c03405034040c0c0742 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 241213300 1250 241212050 241212067
    0x515030114061c06111222020603190b120f010e07030c030b09010e100b130b060d0905010b092d010509010605090f2805040b1503040215031f0902 64
    0x14032180c0003854044800c0e0f0002c52000300030095216810300500e22245945409280240440399032080b00c02c1d005504085039107040141114448409107a8003c065610b541d071041c0a90015111001d043c03640f2a4455800d400035540d4210182009003e544c0105210090403d03010700796000c00f000760b81560405941400480d40024655050303a42000a0f4034554440200c941c0c0105142294000b5034051328251b0700001e810740d003101406902c120b81c607908155180b581503084900a91840f42e105c0810807840c100f14250350070046143d401813000060680220000c9070b50380004840125511400107254900c0700c5582c020b501144003c044155a03075170501d80840c1919006001301014043c0c0860155011303620981d802c041d00308041d0818122200c0d001c0040700f1052504800000615844804070305402c0c14071402d078071660020308088804120704080c502d00c0c1e10180040c0d81000812101d0100004110003e40c0a09207e890855904001e11410401c8e11503681200046a0040105a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 241214550 1250 241213300 241213309
    0x12030b0a0506040302090406021c2c0f07030611091302090a0b03070c03121803020d030e19110f0a0e1902070b1609080a0503093102070f06051503011406 67
    0x147d020368044401a6680e06000c03400351840c940c030003900c440c3d6041100c50080f139580340489e03845000c43e0708504403040c0807180c5015141c00c0c280001176207a80c400007040000c154103400102404060001c203914041d410780215803a13500c4800b440b90f04d1340e000030b02041181000302442c00101520b5441a05504107504002d000329500752001d000c02c00a0040c542c6408010380c0b00585420610041005044841ca4069103c007048071414021a15200300d480d899200452552001d40d4a100c000c68642d05e42d90354007030070341c086203e042d81100d2040b40d40c0702d40da2100d07000507014000c50102da80341c0d40340281c100e00010200039002c04580e4018840c25000400700f0300411703044035403040650034005d1040000c4071000041c0d84040b030389106103048041401000f00081c0306a82e07060b11101ca20100c11003100002c61100398480404401c50240751341626229806041914807c0703542c00403461154481c90b064070700c00e0329070866440b81d0700c0345040c0342d2a0901c00c100c0c3e1212440200010340c60f200d00000d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 241215800 1250 241214550 241214569
    0x30203070909050c040b0409090515010b0904020c0c030303090f0705010c030903021e03121803030306011709010902060a0306050f0909070b0f0c07030f1a01140607080712030b0a0506040302 83
    0x6403041d142d001081413010b0160a0318040c4c402a240151140d540340c117030b00040d002c802c00545182c0100d907007801c072501c030302a4464103171408241c10a00d030502c8581400001c0d44041c861910074003e800030090182c0d0140700450181460400038181224132081c540c2c1031080d950700c11818400301c050703c4000203030000280030450790100c6088400703102000144050080f10070f0b106905000741c3d00700701606c2d846600034100210401c512040c00d000ba100034150351744001e851031400300d14942d041810038506d285d0140d034440100400802e84042a074040381040e0850403c0002080d110074080c04036040550b16440020801c417140c0406080c01007800391a640e40703001e01c1009150000f054582001d110b82150100302c055411036046a6590912180703074460300408450019550b004a03256006440015060b01d103e03401d18280c0c00030b80c00c2048a550304c9030008550303403102440503d02041211500528400b001d0700d020989800c008104440384805400c035038031940041c0130034009a151640c40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 241217050 1250 241215800 241215809
    0x1003050601140d0e011d010b0102010216110315040f1109060f15040f08030301030302150f070807090e09010617071a07020117010305010204030201020c01050c1b04111204050d0302030709 82
    0x401e6807070340400d00400181800c928062110b6003011012940240d46c0c0c0c2290244040c2c10000b00702c03908469004900703030b100d0070403000c840c054a4100075022030f44840b00c2418450300141102c100018120320303c09200000c89007610b8008400041c0010b02c005004004100c0304121212a01489d200c00060041219108968000c080680340300051b034803182c4c1214060041c01d40d01e6000140e0390600d40c2e03520792090000b02c0c0103000d503a10240e02018003500700c40c060401c03c80480b02e15520440d0032034091500608603002c000b80e070440000c4410151503c1800b4444900c00454890704001c1c81c6190700541d0b05410740c1c0d5074011441046985102c241e40442040c0b0240101d03030f120070340e00040380c2c1e1481000700a0580f4207510000810020b055000300101c034804e0b020f603540c0320721400055680340100040010750350451580c4589241c1000440ca50320300c001000003402000280500d60b0700d8010040801c08031121000b440b05000c410000c484002d2240d1a00307601d10710700110010124041e0307209 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 241218300 1250 241217050 241217087
    0xf08062107180608012409110d0c0203190f090303030b0a03050d05030906010603150303111501090b0109090c02031204050f12090405060f0604140d021503061003050601 74
    0x685100c000320500104000b412000280e010142c0003000c42802410240f00d1040190328010200070000d0044140028688000d50540800c038506952600a40a4140000b20a0704200000d00c414040d506c60040410710b11f900658a41001c2c280762640083e82812510921602503001071000c2c3e44080600c0540358186004104170030002d000c101c240c4140c1c2c00042450103615000707403c3d00ea000c00a58800e0281d582168026680d500050341200d4600307001c54114001130030140040703400fa50910080c9040c5408854a80180800c2074500c03860a030000700a4039115450907403250381c170141c0031000d000c034100108402c846148007e5a00e20440c00040c0c00030003600d0000d01484000c0c003e1040004007a000e80380c920700c642807002c05030b5201d0301010f84254544004035886040540c4071100c0c0910107012285880c0c1807290052810701035005441d401011003454100507103410ba95151400f07501006c0d69140d080800810849140c090700b0401018501b03004c0001507a132045804031400100d21 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 241219550 1250 241218300 241218349
    0x7030209030f07091b0c080f03040312050c180108060f0904030912030306060912030909110c070e060405130b01051003020403140606040f360c030308070f0806 70
    0x180402d0428002403106411405120800140b600580d00702c0e9000d60300c03116850214552000c02502e40050709603024110740014007003850007012650007150402c0c002d00f80a8a04c2c4900780040b010f0b1507003110050410000420b003443c003805c401c60241c035024400d090400302072a00e4004a41850008646548101c1443c0042400d01d8027500030000a40203079980d2481903071240c01c0140103020a8420341c0c4c002005031a0000d513140300a40800017169040c0c1e920000e41e0701d0208010b001e06584034114a1114040061340714641007040024028070403001031821a2600c1000c00c03080302c000400709249010385181e24400200c0c4e001000c2d0541d00100c2e004411440e81c028124020b00403500010158094081410950800000da20348a481304450600c80200000500b1080c0c409000800c1c40d80404054003208034031503000c0d0a00000442110040c0803002034803020050350056200b81c02142c18081032100e15a4030409290409015040103601401c0c0100441c102244116000862203000c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 241220800 1250 241219550 241219567
    0x60b061c09061d0601062d11030f0c0f070b0412080f09042307020f0309041a19060e090f040f02030c0405090c040e0c060712020102040302040906060914010e070302 72
    0x268084002d5404a02e00c200c84640000c00490303440200f8082d240c08100c100171100000d60107c0868880072444440781c202c151140401540c0c01454060200141d02080c400c81e154041444081d2448171541d0000740214108512010b0030322210f90048034001030104018000070b588044454461580030480c190348400c001c00c034859500803140e5581d40705003440d045100083d1071070910402c441d041150010592104681680d4840d95020700c011560814000e5804500c1c02d60704c00c10300300b0407144620881d000e02c00d00003864458842c0100340760000107102484400c0c4c0c4000804405001a01e003a96036040520700000196030081c00200306041d8400880215101032020160381400034009029900b0f20910581d1103015016180d80118a443c042c00c0350840001202c4c0401200030341040c1c0340000d1611070300018003000880f4000d56408100000c010303200c6100b00780810b400f8040c0010945e0905584405490428065a031410890b00051001100d1250a181c001c05541401603650020703 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 241222050 1250 241220800 241220813
    0x2403020d051501030b01150305040c0501140f19090803070b01030206250507060f0309022407170319050601200109080d0b120a08340f060b061c09 64
    0x30075440b51031540a000c000410003409103440d80c1600c035501e6000d0585a500c013821822680c00f2035018007901442d071010402e039409100626845d035404480e1368038122810791800080e512140d0b01c1c020a6240c0000044869400a4480c02500060b80550f2038030b8100d80303400083c00d006010180c0314142c0001c0d880084101703000c101d8030520203c040100b0716026814529295600c0c0c0c4518408200d02c15402c07007056101c0e10444054503030080c1a6040e0703409040c909000000c03d28030f9620300070307010461107001c502c0046640003408a80e400c4c031036891800b0449140603051303030075020206608041c01c5c002e440e0b0b0406458448928541600040c4203028940385014042000001c3c0c413409000402c8118070300780da040030328202c2064401100c00280442c129581b88162a4041c101172020b1161810703101d0407110721111000b0321841228104c070a02080040d211021008580f0051851590b030100031560142c500040c40458405041801c0045180000304070b0b0004000c805d40d5840c16202002007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 241223300 1250 241222050 241222063
    0x120309090415230c130306090f05010b150f09030c030f0105010f0b1c0903030f060b070c1418060a090e0f06070509030c15070503070c0f0b0f0f2a010204092403020d05 73
    0x208010144002c054500300f0000f82700e40c0d01c40690391942081c8805d800c030300386612151190b103c900d004c203160803418100e0b19819000000c046900d8050b60b40741000d155420807204040101405c0001401e51400c9020781203c01e49073311000da00c0406000f5585c6811955030f82240350030300d940c80410414400e00e8100c0062299010314441581740c084040341c5814400d002d409114485c904104295407500c010350f400c0400301c6050f6a01a500c21304103204040c52060b0035403c00fa0203401111510f440301109000c2e200702c1071000040798080740500201020420030302d03070001c11600305540f13422a6807006c0386d2510450321510b805407200303002003c031036110841285c00c07481d08103080d80d8aa001514180040c14124401c070143c44000c9500800c03c03181010071200e0006208080c84d20300150302030819440c0d00401a0b00900450001001503030740b024180c9030b404e04034941c0005940c2c45c140312458084885121100e510064001e00c03510076901411051015241c040341c400c8a1100c440c94100d24101 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 241224550 1250 241223300 241223303
    0x31030f02151806010b1201030f14011103060102160602061303090306060b0702180112030e030c031f0e0601050a061436010c03090302120309090415230c1303 69
    0x501c050200010400500648455400020240c0d4480e981e500d02d12207007401641041040e40b91040010400a1030401d4000881d0348100c141840e0240740740417450071601034480480e11000004104079481d0390500100b035968104031a1000c41e1fa0034144001d644001c020b002e1400c500c10300708103c2c1814010f0070104002c5a00c0081400719a44902510025404c9000c0480c0100e11001003e41031140c0c0300c00f180d0595000000104100c0e00c5500d0495402e800c0c50441e60309809040440303020754500f800100c045040e207009940515111241c0d003c00c40c0c400a0080800740c00900040c4510765645201d0000c5803150300e0300c558450003910644900780b044040010f4a00684190390452150301d41081c0c107201028100280d9050101c00107660598200800a0004078400070500040c40e01d41d10b806070007000c94007240d05080700c0c07801280d150503003030341c0a40f210001005414a440c480d03010703041316070284c0c0e4278417203801020050b000400c0d0409040145900030204841340c000003c82c03141c00085 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 241225800 1250 241224550 241224583
    0xf0d0f02040513140706020708030406051204030903020d0b01050f0a21060212010602060a0f020f030601031508030d0e071a0a0c11060a12050a11040303120b06030f31030f02 76
    0xd0501c80d00307245d40c5036503505c2500e0241c0075020740010b144502200791421503241d42c644500c0e0030160404a2030000b00108120240000b904000c009038991801c61054148940072000d529414801008003c9818802c03440c41800480f009004480d9412580d40055640e003904c03194075441e40ca01403010340520a14103104088450000034440d0f40068580d003e400b14020801001da14405001c1c01c1c0d10885401c04541d41c001c20102d240d43d4031a07030041000b2020010012030032502d800c0300324111340c8004400442e0a44a50704a0b015040900901000b03000e00412100d120000011000c090701503113101109101c0c94a48201c24031101d500c508a840f2001441e895440c00b2000c00584282a4031000c4002e0614280001d8a04a0a0300c142e0200300c0c990180130b810035145030380803200c0b484024910105651505408140c1c0e403259006113018440343c100e02621440c15082035450513921800502c844001030015803091010017102291040e0146008146413142d0750042e880d04c14030b0080f640e8078 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 241227050 1250 241225800 241225823
    0xa11040905010c020304140a0e0f13080406180803040501080c070f150f0507020105040b010b0a020f01060f0303080a050103032c0310050114090103051b01021e03090f0d0f02040513 79
    0x151340d0200052013542d010100c14580101140c05101c0300a042e4081c1501d00750500307020804504010b41c1e80c0f0340c803502040a20b5151001e40d03031000420780141c1d110700c005c10300b90348500f11011400003001010304428801107040901d811300007400c0c0c0d40081c02000c5032000018152050008020f442d004280d0071180c920002103840d000c0800070442c10050351042460034001c0b0b42d100d0300c10300481d40143d41040c00c0d414203908000389403185610a20980041d84100e000b40580a802801000f0040c00021000c5484614508020f09003440081496021518107001800060b4200307020a98050408282050200d000185282402c140d800c0c04c0b41e143c412451003005112007500300605031111030b403846c551a8007003020f00c003040d04203020080c15900003420b0b080112940d0595010300400510480e0410268000f4000b003070820300714540c003990800900c50305a81070030f1f2562038411000707448840b160b1501b500d03100f55002000300000c0c45203840304045440c1000c03110364040344542180083c040c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 241228300 1250 241227050 241227071
    0x1208030f0c0c061005180702060403112b020d050a0c1101031e060302030f010908090621070206090c0607050d0c0204060b1606050c0c0a030f0c060e01022205030a1104090501 76
    0x9040001d4401c01b48500c0c0305131500355051040ca04610f015045540082055031100d0b83c0680391103107450308980c801e10640c20400342c00860764214418807000c4410000ca0416003850003410202280055018414104083c03001242e00c841007021aa4000e20004214000c4000480103444c02800c01c03881301c0c0c0319503d40f080c100c0e040c1d40500b003100d108504540c180000c6030207181c01e0b10b1603803c1c090311900c1c0c11702c80036030700e030410000605421030b503c00c102111145a40c04202c2402040d100000180e100c2030070000c0381c480c10001000500422110b81d03040010a5031015034955040c0035800c100850010200210340b1036800c01006004105c0707050761034200a19000b00342c118089016101c0c01d092102141c6c400d400581102c4034000030350040e004c00d501544083d200b000c00031064008209021a505002c514584a100e00c21000040050303641c0200e80d40c00e02c50406514400c141400003802c0400890740e0000e11404015403040c00c189040003404009402030682c1e00028040c1d5090404450 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 241229550 1250 241228300 241228321
    0x4090b0a0503010b011416021215090a12030c0e09070203120a02250c050d0c030201180501051b031b01020a17010f030618020a06030e071208030f0c0c06 67
    0x480510180c4032500c20656450805090318044500d00e030218078414080916500310380000d200c501c11034000708041020036804200d400c0442c0c010716060f42c10001008004486400750142c1101c1e400380207206954a0f500e80c032901c0d00c031108000003855580d1310707060ba03858000c0b508000500401400003440d0714000101a440b680085105500c0c80144d000003400d40903607100391015100311036520001742c0400070f0311b8814140e0184050f40d17000da00c0c000001d810350384d100d684981c0902c14001c21a110f4514400540388201c000700c402410001e40d40240001d1360701209540c0c41d0145908882d9003110a508840c0c04c500c55450140c42010000200781c1d064030301500104001e0300c0c1c540d80c0c0707400200642038400e800c91082c085d501100f4180c3d1410804204650420700c6418518402040812210750015580003015031142c40801e0b1208020620b40c542408260002e0003c8000a41c074400f95030313201a8070340b100900700100407444101060242c1e103400c0035501509101d000b150000d0503c11080e1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 241230800 1250 241229550 241229561
    0x90b1605250611190c0306150510030203041703070c05060c0a020c061c0504111e01030e0109030e04110c030301030c05040606030e1504170a030203061e01020d05030604110409 77
    0x81c015140d00050015200703118054495201021202404080007072000e42c0d0180c20000c0003d0700c00014030328001c400704200d4031540c1c06444600011a00703052a160078000101c40405508082c14418030070480801d464072401c0803075032192200d49540307a031159030a17103201c0000c1c3c0c0c0282c5584141e00411811072000401000c266410b602215202e03403154023004494880c000702079403d409149000040d0418541005400c5403080b410340c002d07000c1c028040313480389902848013400c91011031800880742d60940f080156044001d0000d01c00a5150b440281040c281d080101d030040350303070b5020b803c00f03030784050252143c0c0341c0ca1105413952541e50341403502e01c0c6807060041c1480750340342441c00264207009100348510310440c6005003031009400000300b442288010300c180e079a014004140070600c00c0680c014080b80c051900c0043e06d80c1005000d2203e110400e203c03054550305201c004010903a00041d101362034400c50714019030780b07550b01000b14000d00301d20024054007140100d4045065102900b05 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 241232050 1250 241230800 241230853
    0x30a05101d090c0907140f09040504030210060f050a17070305060f04050f0309090118060504060f030320030f0304080c0601121a010e0a090201020a020d0f0b16090b1605 74
    0x440780f04003e08030400c070748a031080d1103500100e035904240001c1800c681e006441d440e0b072034880050801c4503a80205040e034008903421001600480080e0b032104a10780f203008090105031601004081c01d10380800c0c5281024010ad494010031240e00e984003400801035100a11b41c444d0507180c8501b010130440c840c50200759000c503524000c400c07203e081002c0c00001d42d40c1c00e000080c0700714074592070031007814003072910102144021a110b030740120f401d89403030080c6001469001a00740c440c9113141401050000507915050200129104011640303c001040e58008401290000e5880d00ea51924001510401400c41907600500b030000030000b410011444006000d182c069190045a10032413900c908240240e90b801c540c01c401041020380180d01c85d94020f441801120700044070f98001800c280302d030000441e00f1090100381e0700100031000d041c2030b40090014049000008040c00090002e402d030b0300600d401070030042003040030100c48801e030340c100c1c940000694484600003031030307484203044020a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 241233300 1250 241232050 241232053
    0x90614070806010c0b180604051e061504150f0f0311010201050405060103140c1e040b010513030605040819120b0117060913081204110405060105030a05101d09 70
    0xd05090044014030302c5040142c1d601c1d241c40500d50f4034a41143c901410000001d8021090402042810442035020b10701034401004035800d0742d01024006042440c5140d10743d0001d01c18440ca0015060b907143c4a00b0341105c02190310b483c0d01101c081d0000b104d6110002d041c1c0d0781030f0005143c0a600342120b05130390043c500d8401c05003c003070059081e5501603400500070351216004101160320703542c0d610b2200303100d042900c0c4000c40c0d4500080c012000071144041a1440d660320300c8507458140304800c4050821700f0a02d080010a0380800c803038170114840500429102e500003010459100700b210700c10804980036400c80380e920031005101080045151801c2850685151403540c0100c80038841000444102c6960740e450b00140102400d024208005400040b45520002201c8101410703050300c0b0703488040d00618090400c249682d0340c444003035004070314110521043d40d900c40100c940c00b407084000030a95031281041c051020745240c0c0003001c4941902c4110707622a08000026011350074010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 241234550 1250 241233300 241233341
    0x2210601030e0604021318151a01081611030a0503090f0c010f08100b0a0302090a0f050a05060906090904050f0709020307121a1201090209010b090d0f05010e12031603061503020d0f0906 81
    0x50b89d8035469004001064045400000000c840004051004690b0862072800840121230b20070298a9a0070812207840482c401104009101c102000321050703202810008005280380c0c0400608860040d0705480c08102040c000200d21039180341030745000b4a49128040d6990503240c8000300203403c102c0030244201605603001464188544000b0b00743c81004108840c5130f46018104109a030120003080d4021b40240700c48213480e55600c128034400c40c010405002c1d2600048243d60900b0305036000b12010b00c2c4144244120b00e03a01c0403c1044041e22140d000505101c10055401c00c0c2c01c43c205941c0e44101540550740074883d0641020310f91a100b40d95529540c1d89507903052080e03000c0c2c06a41504880c108070340d5004100d18003d01407400d0f00440001070400500503811f803c0c803a04000340c4807104800000d00c100e812561459220034402c9140c200906420200207045840b12040c41c1e2040603008207011810102c0c50784203158801d6402810052030403607141181c09000d00d0504c40a0000340c02 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 241235800 1250 241234550 241234571
    0x60306010312030e0a020a0806061c03021e030d090309150e100507140706020616020d080606092808010c231c02210601030e060402131815 61
    0x255460580c0d901c030380901001c2c40348150803001004d41800b83e001c04d20407440c8040140e1215003400c0c000d4108240940580d107003440601400f81044e42c406991034100c1e240384ca000c00d501051114450441c0142c000d200c075441400c1500e14041c2d4440708051a241580b06001c0542200a40045400100040880c01100e14064034640d03a003500b6290001c0c1000e840c810820b2140001f04800c500c50900780860346180d8810a180c0082e9402003805a48648240651200d4907c170002070b503000d80c401030501003d08000107050310030240800740618404941f0451590310481c40da5541d51108801040d402210b500c4500c10441911134048954640201c040c0980d110311207440c4103020407011880d046d162018081903989c0240714265000003603880285000c6810700080c070180c10480e03a82500c01058503503032400500094020742c1030501e04840f1040c2900c02064242c0d01540442d8000c640380050b101882c0904508246000c0340801c0d44052010801d440d895980e1088021400700101e0460 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 241237050 1250 241235800 241235803
    0xc091e01110703080f030c04230109050a1202100e0409060b120111030115021f0506040b03010615030203060a051915020106180f0b090a090b101203080703060e0109140603 75
    0x43d0101501586003000030280c0c08130410700441d040321200c0c0b00c4c036243c15602c20040e10380780b011a07038940e07001c12900c2221501c1d60b805200607018000403a07060021a14082150780c3c0070289a2000b03004d12046c910103000140185003020940d18050020301807260036190201c001e00d5070480071032040e00300103681c070780140c014455801011003c040c282d01d141d0a0001c03216000d0000c03580c000c02c41c4210072009000c035490061002c5c024100b1a80840d10342005420802560101c00d04240203a2401c0703002c0040d001001083e0303c18050601300140c1e82c0d111a000b003001c3d8641d503040590085900c241c004024408201c651088403401021402035100c1c1c000100d00b40c1d411881000400c44065158411b40b5080750300007040c4008040e0b0002e410680000481d420400880300500d0303050390f031202d010034085050f007a5a070014020803a201c900e400d001510840740780380d0340042e08022200d40001c00e628003035409000a070289010304c2410b5a950070111001e807480c10005280d000968020078102d040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 241238300 1250 241237050 241237063
    0x270f0221010b07080304030c260406080a1103011a040506161415040201140d2c0307050d0809150103050309010f020c1311040f090e01060608150402030c091e0111 71
    0x3801000a0b00d903440d81c1d00c044910802000040d01d00c0001e5001040d0076a27103100102c07442c484041c079802e0b140da192003006094503000911580c02d0314240b103055079401d442403003180c3c10b41c0c1060a5005204424094950b0781e0f0285800c48c40d08007100090441c040c643c031442011010740b240c54025081c4801c040c0c03031500c3d030043e04c2c4443c0b150880680414015806400c4c030120f041161020242000c20190403602030f519005083c0300c481200e0344951050301144201c4962940d10b02006500c0d180a581d036150751115018441030400641d8404101010401d0101ea400c900c00140c0000640d40c40741003c81d100da100b03c1086000c144100401c0a025002086108094800030314070100810390a6074000a0104e0303c66030f80d00d00004201c08a10a2803201180003c0c000310100090241d42c280302c854215035590b08103070103000e0000c04010010780007500b107046442043d2000b507181d8031203410601e006c1c0148100d2640c80f01d46140301c052102c0c0380302c8000042280903a148603c031100030507929100c0781c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 241239550 1250 241238300 241238303
    0xa150e012d03030f14030a15050312120604020c03040e0124120f0605040c050d050109050c0f0a0c0c03080d050a0b010507020904140d08010f0b0301270f0221010b07 72
    0x20710032401040070900869031146940e580e0308240c4102e0144a142000e1079008540a10382c89558450400607449911104d002410301a0000d04000344070140c0c105c801e0040a181440c03800c66080000c84d2501c07682c040d14807481401c03013101e4070380d91a00500340c0622400d00942101142c0040010103801c46d1040b104c5100c00c0944800e0552145c14006c070000e04000071501d21900d480700d000148039207038cd10400810846507514561152100702100b015110f0690048410a08bc03105100c05e000030f9808480e480d00428003907681e03a1001000980780001b00e004041c2a0801a0400105000c441802032030000082c44040295540e10307051103045450b5104010b00140040c0709207001800c01500c03030760700b00340100c2000340a608110021440c0281c03c55403000042d83e40401002600003281c140005060344180890a542c10300c041c2488800d00a003202110f44041d10302040414511303845030018200c815000d558580404000e0340d20100000e650341c2c043c6846500001ea26841001903c07240c6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 241240800 1250 241239550 241239629
    0x30103050d080601210c03090803010b12060a05150a030e07140102010c0c0521070503030108010e060a1e0c05090a0305030903100203040c05090c0c010c08160203210a150e01 76
    0x242c030850103817004107402114141450b540312034a00100b10030304041d60092550600a6030b407080c0c88501402e10361000f408450041c074880b801441301d42e4034a400000003c102c06415500d401180000703c0207000404040d0040c1d00031000e0100703c00108584031001c3d55021380091181408204007215075055034200070300260018480035911245009009684210800c02c003410320955880e054119482a03015161583d0f4608a45100c00d40900141da0322505515003003060030503054898248040414033042c4080ea0740c0c1201030a54010710984034050030180203d0402600c0340750031982d90b4401041c00384070f1310541d1301c00c4800d996240200d034401d5034852030281d0402d1400051102000c03021308034901003d42802410407041c03091050f500307900e80c103550380100350503c40070b9851151001c1c1d80304070864104000141e036418034500100000f1031252400140f5990f003184010080071841084000c2c56000740c4002109054008a45e050f44d40c21881e41c0315040c400315007074030014901888000d09 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 241242050 1250 241240800 241240847
    0x203043f030c0e0909030301060e150a080a0204080115060306090c0e0d111c0b01050f1c02041d01020c070504061a030c040e16090b21060a03020303030103050d080601 73
    0x44520a800588103100c0904045075514500f80004040b00c10880e070740b18281e44040700400401e58089040c4120207416a13001d41c0491076050048250302c900803420003070111082c003160010325107a0455000f040340d48020010504851100341061800f88100741c0064249040400d514000d4402c40707045048680b1240a00301d035040a201501c0038002d0156560000903590b04001d4855810003d1228004024094684580c1ca840d04950381c040c2c03c9180603420142c140b154a4a0f0100900c1844d42e0070304c22540c1c24050780c800100a0004c403c100c000104c06a22810b66050054000d000c0c1007000e40151070200340c8072003c0c80304551a030310407880f22500740d0f4032a940034802d8400458105c254491594585912502c4101c1c40a105561610001c1c1c0ea01c000030072002c0e80700700110301504005034403500d4844811031900001d1b044038075141803011400b0100310035035070f0ba0166000655000d415030744c0f65a540c1c1803c9171030f1081c5008180c0840c01e84000543d29600c60f5040e441410301d0101c25020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 241243300 1250 241242050 241242173
    0x3040b160e0d080d110705210904020c0f0f011524080c0408030a05040e0a0c1416170a08090606100f02010902131b03150b03040312020304 61
    0xb1444440050301c09002c00c019500003400a402060ba10980d400b144e1980d0300e08600d03016150050117000e5050000400039460f1000440c1011195208411140503880f0700d903480201d8140381c2c0fa810003881e80d20035001403042c00c070419007000e00ca2140f03111003502c04035a25018120040514080301c068003c000c801d2031080c5016820580e04440180b03840c50a054441c0d00032499544108841720120318007240c00c209140070040c42d298403294505003400100401d82010b4081c260b0080000e071044404a00304030444aa803e401855642202c000ca80b2a1004038030040755030f20041c554800552040001943d150340061204d00401010301390201c501c40c42d034421180003404101300c02c115500c95000c0d20142c0d035032060074100d054100c9000914014846501c1c0014824904907405040c1010900900300d0700c10407000701100e8505ca001ca50341c2d9114070382221080071100782018800c0c800b00038001403107000c0e01c0c04080c0011603a1140d080f8808200c03010160503d0354141a4402d440901800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 241244550 1250 241243300 241243309
    0x30b030f01060609080606100c0c031a0406050108010b0d080c0a0b1f0f030302031c06050904050d030b191401031d010515150a0f021c110c04090804030b0c07120503040b160e 76
    0x51140340540360880c034140c2c0380e40c2c4248e0331346c00c0441d6030909050400144028003005208043c010041080200030340301807800414a000f180f008080d0680c480071904842128090002050172070b0700c104401401d28028410304a03024140c0c0c166555200101400b01d215144402d44005480d0990011410207010320038120700740c1350b0f105407590307032310b03113800000a15880764040140510312820280121b03a1010703600808948000700701501c0b0341c0c2e4100489059002c180584030035a0704408000e404903802d00b0050300a000c000d400c044480c0c069440b00c140d40305040d400305004a5091120030181c0103048100440d944400c801c160480301c080020000c514001c900c00741c000c5105005803a08034018011441058031000c52110204481d40f181c0110000103000a525411707080342c04000c41c0344240c5410030940143e0000030801e042c2040411300070804c2c1c40c00d443c140d6074000440f015800081400030941d8209407412501c3c00308040126200101c1d86402042c0740c0c03156503912000f1201e950800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 241245800 1250 241244550 241244567
    0x302060406020904110f0304030201151401030f060b031603060b070803160e03011a0f0303040e0711010b1f021b0906150910020717030415030c030b030f0106060908060610 75
    0x1036000b5035400c05072403400170031000741039060349403543e06440349814100a425580f140e80401c003582d00000c82484102c62140740c1c0110b0410a29000031f9420305640190010031042c0c01500e0354990107c200042601d4900d241e1040c0c821540c0d00b40076203561042c5885260182e504002c18041c820300001d450503000918094006204c2d00e0084110b0341d100c0c0c00300b401c4880150020440305096004d0121908000240407403010058009524280c94080013000c1d000c00076000070708010542090509031070094200d40c0392200010055900d1b00200b50042c9803200882c20600058000c4241e00b4150104c4001503510103100980b403540380b0390310311080101100c0856100311035500144201c8900340c0b00d00a60030140600c54004240321070600351034500c1300920707000c04400341d0310822081c004900030705000c44003a0420f04021402d8800140300781c024040741040c1075010b20660300c840f802203905410440460740c07192240002c094451880700c0d200c950480e8a96000311811b0500c2070441e20a5051 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 241247050 1250 241245800 241245817
    0x705161202010e180c04141203030f0912131406160204020a0203130b04061b11151908100f031a060a1701050106083d0b04080a0c090504030206040602 66
    0x92010b0031210441c1c0c92a0f6064a02142951003c01d0520042e50750410500387c43c502110100c2041c0c25502e0b0080e070b2480010b00f03100d009440a004518060710070442c0742150b0343d00010050320303020007600c442c109010310700c1607030803c01d42d42c00c625080b42000e034110750a0752405400004030740c4040d001d0101960021190104500c42001141a064403c51000e00601101350903603648600e081c1008002d480c1450741c000c0c80d912080400070000da64010407082031102a2001d92110b40782c424030400700d0184108100c0111004150043c1403a401071042e8070842d0219101c5502d1358803103c803030721b0700c0034140001042c2100351b450403500500303403c120300e83c41003004200011003901da001d80090041c070b8400400d41030b0b440b00e00510203190010800e030b0b071144003c03608250346900300b81c2290b2507042d021090540c14004000f99400d85000081d403038003802282c1986981c49607030b09082555101c03000400d8444900000d404201d045850080394021a003682c002d00568a580d110b081c001d41c4903800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 241248300 1250 241247050 241247059
    0x13020405040318060504030605060103060605030f040614090105101502031215040213090605010c02060405040506031006080a02011b0b160c0605070c03110610090e030c0a080705161202010e 83
    0xb0307640f1080d100103000c00383c00c603035440e6501e4618600c1c00d02c050f224081c1c04039041c942400e13001c0c800345601005603940000d060100481a49403030410500030408040c503d1a0540802c1c00c000701c0c05030540186001d811034030b541410f11903803003104031190702500010400681080010800000390220100d400008090032015150403100000d003c9a2003180f998000c00a80350040100d44050b02c960ba0003400d0130300b4001d40040c2030317a0015520b4890341c01118421a40c5201003a03903500d007045894001880e01108200c10394507410a5582c40d030b943c01049001420114414907891845c111f03910405a00c000d1313804080d2550000302c4440c000b03070750a030810071801101c5103002c1501b50285500801141d159003440b950079040080403c1802c0c5005455584001c003801090004000c800301150b142c0c5000190800304d00301d0a43c214800c0b001030309824170909081e1814031001000500301c0e00e200300c04481e201c00420902d4030321503105100342c60304401c0a075010809940941071044030078030002c2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 241249550 1250 241248300 241248317
    0x3051c06050f01180e0f0403020d0c020303090616020a0b09030705031b100c050102040303080105090a0b0310021602130b18040506010312110607080103060c0203090919020f03161205130204050403 86
    0x40041e80505d08850b40e114200c0244280301c00d054050140d481100058503081708402401e40100341c0d01c1c4540011240248c40003c1c00040d0018641d841c0d80a060f80103040f40d070519928074924580390001d00e492403082c00391440000d035914000601150b200442611401c0400c80a01084440078421016009001c1c0c81040c680000303d080c0b005001139482511140610b505000c2400030030f50b80205424115440d20031710f52816540000c80303000030400c4403005680d45120b802d90b0040428010381c003e4103d0304440000c1c1408900d03800050264070281d034404000c036411388044820b40300954001d13185400020043c40030442151003600120064180800c0020722410102e14003c4112034600000301c8100041c01088020700540c0c8074620f040c07006500f00110000050045440940448101181d00051841c4840c1640549281300d18002809480e841c104e81c040282a1100441e000019005441d10030340308014440c442c040c50710400480e450040940c248402028007030020f500b030140c42c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 241250800 1250 241249550 241249559
    0x629060a030e15010602010c0503010b18010e21010b040203101403120703080f01090e0d1808010507020303101e120c0e0117210a180302040903051c06050f0118 70
    0x40024003c4501da9021144941d80f4050000b82110301e80250b0008015007080100040b9030201c003603c00c0c00c0c12190b0680044001c600040e0340e0300c0c441c1c0d102ca41d040000b204050300080441005402c00504050090005c00d00f2401080100e10041302d26942a40c0301c071505006451000c000c0c141c1d0002d02800303c0b080313404500d8ac08922074110100480000e1016010844081c00c0c2554050040102c900c061100490740b02242c0d48841542c240c500c200303c1c5004031001d400c540d003081c0703100405160000b00210300303100400039100d03402250b8000c075120580f100012000364aa1a05607030300000d021441c1d01c142042c018100c40035000109a07952059108046074811205407414020400144a844400c0d10b26406500b0520312030000650424080829030804c1d41a004a41c0d2121842c6885107501960481c92400b081403030304042c1d0401d141c0b44140f000c264120300102480014150301a58040364000e4100507100c40c0e0080c0c0d80c21080844035800194021401841c02d048802c500303146080e03c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 241252050 1250 241250800 241250803
    0x402030406020406030b0103090507170a080409020c06010b0f07080306300c09040b13030212123909040f0e0105040201030b190e04110306040c030629060a030e 70
    0x50358140c8503103600040c108400d6070944110300c1c1540e0207003021b02400c580c03a1a034a8562505d40301d0900910b45290710789201da40280700c0e010249a01111041d290350310307508044000d400c8581d400406228000001c24840600c1d42aa00da41c41e1900b4a60301d0b10549603248011904090002e50300800c1207203c00a0140b008004114100d0100d14050042c0104800480c41d1060400c0f510f405802c10605002c0850b081c41c0a0710340c030001c4503107201c00d61141443c040f86414542c5120307000100012418030300d00b03440c2845050080c5210003080c1064000b20600524420881c0801000340f400c010450340c419038140301420003210000c00000300c40030a007007400180d03610703040c140794540d540c1c100704403c5603090f1180c5050300c8800e032030707101c1e407041c1c001400303101c0080754019407110016403800181003141034a80002c0f08a40907056400b241410700d08200380c0c0140d07020071100349040180c1d10381c007200034a138900d48a4041a00710040c62891506000e00da0f4041c0079134008050f2140341c4002003020 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 241253300 1250 241252050 241252057
    0x30203011a0901060518101107060807090b04182f0417010b03030d0e010207170d0c020325080708070c030c05030703200301090203070f060210050c1b0102090402 71
    0x2034500d800d28881e86407030100701c80210305030416404d00a0030712400408800c42c4040400030001507074040040b28000106032200644050242e01e244940400820065481070810b80030380283d07151002c51f140c0710b405040700c0d4040c5018494006c000302c100840d8004498100c1c52422034107003140b41070f1911101c00d170140064441001d0440c1080041c041194003e02500200341d1803088000f0000c4000c1100040c1c5c90748142070304040d20701d4450140415007e420b6040364061f5a102c14070485400c0c2001c120010750300000c0884010300d00d0144c02821080c004412100c1c540202e00342c0960700400603013180502c0d0320701081602c0ea01d40c103129242c0046c40d0300c0e00620031940104061819285180707030852000101703822403402604901e40800c0040d0450f0078262030f6010105030a030482121030f0101f40109a07103000a035042c802e01c01c0008a441c0c848090390f081d10810b5098170040381c02a42220141c44050743e000c650003400704107500038008007040704003c020f4a44000740c82c0541c40b100040c1643c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 241254550 1250 241253300 241253321
    0x91511040509060a030210050d060b0714010b010c05060c1605100b1509010f1d0901060822050d0f090801020304051c08100302040b011b050a02091008060a0b0a03020301 74
    0x4001014040c41c9040d07102e02c2d40c440400c89001c20000d045030302140d010ba5805000070188000440c240c20400c05a0b04400c0c0a04200c401c015110840340c03c080011080c40e0004503243d5180044e008001d501c1546507500c00c6400200409568440450a407460b5205400b03001220194802640c0003401c00d002c4091519110314003c80c008035184108000e0a0440f0343c2d0300c000d60b4040209980903600481c00329071003401800d152001000011190304414521440300b54407901e480000f02d12541c01002c400c0c0151200c4c6031515007810703c141c086a000c1400b51000c1d20980c0556052480144924441102d0030124900070885650b03c22041d426a041a03800311603a4015200b607a8000c1c018520b103660404551400100d0f5041034074200b1944c801c03038000603004a48035003c01620364000e512241c44808000545164003102d8108a619400002d1049126042040c0410b250b4204c2000580507a005600640404d40b06c0407400170003480d0b80a4600c1d0890b107100d02c004003690f003c0c82f4060284 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 241255800 1250 241254550 241254581
    0x5210f03091e060118051b0304060618021c05071704031707091206090c181d01020a200a0206030c0d050106050408030403020402031f03080408060c0a0c060915 70
    0x260b100001190b44032112021030003507400400104901000c41c060701e2025101e0910004480e12900090350880d4080c201490003480004140800c02a90350301500807181150000099180c5440c8000305078819034501ca01c000d416403490311928a41c40d0710a5800210604000c0100406500d050b85600e108981c260003290400341000c40b4507421350300e0b807980050549072043e1b81e10300b856840c401d0483c1c60540a0301a940c0c404034a020003207403507461005030010f182c80250240e80403c131200a007049291048401055044000c0807403014001c4c0c0c0c402d500a510ba1750440000002ca036604042810300d056228441d4454400150705d410b03005500031000110030903a00c5c400d500364402a070b030040c1e000e40b0800c0300070802040324210210650302602d070b04540240c0d690311400340c40f000f040e40840405c041411004400000c0008101c01041124242d00603218076540300c4405006c0ba026890000d004500c0031202900041d8843c1c1c404080da51051031603400041c0d40d810810200c820403000d2074101d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 241257050 1250 241255800 241255813
    0x507032106030c0e0a23090f060c13080109020a0303080a1103150103050f1b0d06080607020c013c021c0503011d04051b010909020c06070e090405210f0309 68
    0x4121407410b1259100380d0305d80e0b00b030000300c1d1015071400403000c81c1010b958200d022000403c690800074089810f181904408503401400d1a048110351540001020301020351502c1c0005841a018014564400d400810a2031480d00c0e64400340c40e04c140043c1100c030b17219a40c4410015081c00400618020803c4060000e0300d0a40740c00054100c41d0080d044410b90310b038031801c01a804081402c402d000040319034443d48c41d690200c68000240a050300004118044c4104100c402640005d100c10010000d907140502081c0b010840585030a0300b62130f4042e050440c1c0180a020040385103188180e20b918411501d0b200c108002c0252002c111920160024000100400046801119071826900781d001c00d0099424940d940c01e5a6201c600ca8031394030f035011548031040d640c0c0203515060042c902140103544d41c03000000000c0d12407404030b0b040303004183c0003d43d00d41581040581e86119540c844001e01d070041c800401c60000710140300182100f0b07941040b02c01c0038080803402840c0a2011480140003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 241258300 1250 241257050 241257059
    0x3040605090604021f0509030f0a1b060c060908090418051002160209130510020c0d08191505040f0923100b03160b0315010e010507032106030c 63
    0x556002a124a0726580b0500034040580c1d9040701c001041101020754009040005606640d41c1c080d01070556410b0217003402208500720701291121002d449550844a501105208005401407500801d4005080c60b039002c400900c551744046d0300070380201c2005080207104000942541d1440c4a0301003000035510404042060401c0300c0545d1000d10f12040d42481090b01c0c0e009915030751458040d20440e01c1a000c00d1080824940815400c2d811200782d5954150460391003020b5480300c041b400940c85207a00e10700429108003000ae0180c642500070701c1451440c2040e0f10050b14030f0103110303240e0046510002070160f4480c4a4159207219041b03000c038104500341020700c25001818092400c40c0340141d00c41014a001150709a0700c020350040c00904000c2d8080403d143c81c202c0f00280514041c2d144002c02c400303540601462040140f00601d0441c1c92803000110703200820301003030a0200c1e03000c0c401c0c0310000e805402e41c0102e1a4135000040e6008190304020381c191800b540c41912401c0c1210418070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 241259550 1250 241258300 241258313
    0x51e0c1e1e0118110f04140403260a2307091a031e1009020d0e06150618030307050304060903030f0509031c03090507030605060a0501020106181d060c0304 68
    0x21400101d4000c100c00070901c882c10240d25034264004200c52009440720009540d14201c14440311000340c010070450100203071003000690256425400315030300d2082004155001423004807240b01100c4106c026407208100c10015020203c400c0e0f034000100b0f107903c0700920180f010180f1070301080e540c0a03085460200b2081131240c00001000241200b0001c001060401d001c03a55941c100ba800b5043c80d607643c00c82840504030403034001051490000071014200a00c0341c01c107180744921074003502c0c5503485851a61100c490181d08a0307030088424000200d4244407130b84203045004000d0140c900d40511603460b00c0c2907134055005030300800c0d09401d0034410715901c40c01c020070b0500c4a00303003c0d1810755008002940c2d07001c1c00f00300c950040705411a400360340d4425000f0318000c69212048071a600e40383c2c44c004000c1e0104640c4a401a2103041c0c0008180d803050013907000b200c0d0214510148030349000386601c00750203503e0031008280191004004142030400ca00c0388114400d43ca0740d51281481c0c9081c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 241260800 1250 241259550 241259593
    0x1110a090608010e06150d05040602070b06100e1e0604030b01060906080c04050f0a0b0315040b22110708040b041806030506060d0c080a050a0501050601051e0c1e 71
    0x1c01040300c2c00c00103100b0340c1e09079a103090304000c1c1120780b040b8604030458003405d14840c40e0060740300c060506052108004090f00130300b10141c4103903054102e9980e18424041c05040038600318000540041c0e1207103803030400d07400224071420000300b0ba030790281901e0041641640654012180c07010036000412541350321403d4240900281d01c3c02c000c4034144814104460302881c0186403041004c003850013519550005230b038004102485401e85c0728a040060001e444041010103402030f402e0004079401407800501045608450720308001c2d03004040175600d0028451000a1007844104209240110b65010090300040c26803408880d0f071a0300380791141105250384038021824030700b40001800054000301c2e01e29800402510501c2d108071641c02e250140d24203d0b031107140e80e0f001e010f0460041c490003180840245000e08000d02482e02e030800115100d108049960503910030011542c1d0240700da0000601060704002c00300c1c0c0105034414100e2040040341560720442e0b0380980900860b404411103032 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 241262050 1250 241260800 241260809
    0x8061815100804140c030a140c0406030503090307050105390303040f053c07090e030c190c06260a09050606040c050d02160602030a02121f030803060303070501110a09 73
    0x54101c0c417211002096503030b1204040200802504c602001000004200c82007a0b694020320500c10255203040541e160b902210f001400707400303141008039895000d0380c02c489a068929080002103403050700e40c0c614001c0c0c00f03154046000400101c502c2a00f504102841c0a40d0007409540e04010292815500d001c1124001e500c5003c80840d5042060301800381e541c0074901c0008540c60507520000c0040e041c90500e811408029140c08020620048000046c3c80c507208940708949034031002c2c1e1001c400b41842c0184c0146402c0f01d090381070229501c1a0691a0420710080100c40d15a1000100e00465035040f10815840b0341c1c2d811988041c0441040b0301c0c0d0b0004400d84003001084001000140343d4030450481c16050750b000602e5000b040901840403460740c0d0481411034980c284588450040d62040c3d41c418644440d150105060502d13864465502184051066289500d507560300700094100230002c03503250100707100301404207000307004046403810b402c0c00705565041001000f60048841c2e401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 241263300 1250 241262050 241262053
    0x7180f03020108040204050403020109050f03040611011514030a0b0a090309060c0f022407051006050a0b0304060c05040909060b040c05121305070b130609060806181510080414 77
    0x1080943d0300203240d19001501a10701150696a9090581c05000d00d448003d00e00d10420304600706404c6d000c009481512125541d4401d0350340c00c43ca81d5030a840c40c81044520301d4524030000c0141001840000c04070b030101400f5110100d040c1d8681c2018001d044491403100e0b9203a00340340040503880300900010f480c90303040034441000e0b65207601c18240c2816000a00030541181010302e45100d54242414000c1c031415030580d55040d925000d600c41d28503100c003040d0541040f10216142c505002058180e030240015141903640340d80b00c540140c294408450140700e03040101181e01d4140b40034000140d802540c003c00e016410700240001c940c000c540510800c8001d011202001444008042d009180542041d40b50320072424502d0402034030340d1104042c484001841c858000c1c10505290440f4200c0d181e18541c1581c900055403111000c840080d40209000e40744004451407028030b60700b12000e24446040303010741d03402184218402c40401004a1b01c0c00e4200400c20444c0c3e4000309040380c4180 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 241264550 1250 241263300 241263329
    0x6120c090709051f0c0b0a02160602043803060604050402040e04020a0f0518040204020d0212010611030f03010b07050a17070c0506040b040b030a0902040903200105151201020c01050718 81
    0x5c045000740302e0002c286410b1100420308090460301514480456645040c4018481d494840000d5000f413144224043c0103000c0c0304801d038201d0402180c0488550158404000b03204080962640000e0046078040b405120100b05500c8610240014003507914041e9010305150042000c200381d0b0350320135003001b440c00d9814441501d0f00c3c48242e0744072840c00200c0a0589030f0340700140280c0201c0d01820380440c40030402507030790881420014101c60f210303112410550b1240e0325594903031250359040d17544520f0410040019807201002809050300a034290354281c03c0c1681c41035003042d6031080038404001c0110b19241401303000c01c0018010407084036524039041c50300a8030022809039110303014080c40c0c003000044a01c0c0300c0d504051001030340100100304215113441e000d402361252200c6030b541c1107440302c810500b02e481440381900420101120010f4030441000f00042ea217003451260620755024040701000904c00d02030140254280c1d1a5507025034004030025055000c0356100300340020090 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 241265800 1250 241264550 241264609
    0x6061106070e0d020a0e0a02090a0909021804080c070810230c2d0d0e0c0a050f04060b0d02031b0a0f0c240b01180302010806120c09070905 61
    0x103907100510541500c3c1440d000c140c0e030000031900315042d40094045040c0004000a400c40d5038010301200d50202e1301c01d003480341c440980000b11203a817000290004d894442013804082908136030391740701d0701c44d501d098074203e0307010402801d189090b0b11101e082d52042d07840144c0d0500a0041c45180b0b0031400181d400580c0c0c0078000d502c4207602620030310304c4000014004003c030f000481c11100103103400d102e0070a040d02e8880c41141c3d56100d100411420f074039012222502590200f15041c80b84801000a03a489060101b000000d40c031125085910669850001584c450715201a10100d107440030010385910346481c240303c0308840e4041d0848072907410010440d80b640c21aa03a101c0f10380441c60700007444041c0749088849103800c0700040c1c02c24841003e030080c254140340c00113003a501080ea9105c01c100003000b15002000380501009022030186030016440d8100b464042d50b900a1800848030580e80c55000f00e0040a81640c001d0001001c500080c416403c1a107910281d0301e41603020040c0d07107a4403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 241267050 1250 241265800 241265807
    0x10e030309030601290705070311060f0703030c020f1501030b0c0423010c020a080607200705090405010207020d12080c040f060c1a0a090611040b0a0f0908100606110607 74
    0x140980089555022142c0100e0031603807882c1c05850010201156407080b61f03081a654482d41407100310b507003000000e00c02001d4100031003a02c809031401101d01d4104002d680c0c040e0301405c04024040118440c1800d8540a0354042200750ba01c0b40c8420300000c3d195046090050250b0001054041c020400304401c010070200c10103c10351002c0391650140b800128140121450655071401a611085025002c50001400302d0241e000325020344a41046540d10641d407440d415910b0041c1c1c00f95003050004004604000c808254080c4c4a0000146002d841c1e500141e4503142d284001da0304410024101042a1307005942c0541052101c0b9540d41480d141003144050981c40303000d89400c115550b50740c0001c01c00908010088151840c0803007401d0700d04240030030000d2110800c00c1d034034941012401500081404112000d80e02d0501e50b0300e1420f540250107943c0f12900c004414100710f0203050010311020140051180c0403079020300440c0403858504014443e92070030303071440c65940103071081c070149035003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 241268300 1250 241267050 241267063
    0x170c04050111161401030e0c0105091009090f0603151505060c0f0f01051b0c030a1112070b0a0507030e0c100210060315060e13062a030902010e03030903 67
    0x9092a1a00025040044860400440e0143c030688040f59010228100c03030a4200380181403002c6e079080101c2d4440880b555600d4500b0400c0da07002c503c003006001d0b40390800005500000f011800c4c00c115440da070f00318071801c440c02000c1e0704021960f2a9028003c010b000b082d948a0390384114018803400000704081107403643c040c841c03507115800010301d2003038800052080000c80c0d8500030640ea0100b0340916040e010700b030700301c0d020030b03001f441e0200d1002604030038001d641014010200a60400038490800e94411400700701d40e455501c41c80404100241000380102499885046643c0b81d070b0a140708124165103014014000381030806541403003c0350300180042d19428116003c4564220440307003a0300701004824022121800c0c21004070601661070800558000d054070204440d60760b03480010f120740ba09490340c0c12042d0041881e000414125003080c65000c803454144511a24600c0728440c001c06801101c0c03001c00e1310740b0020004d40da086101c841801d60709078041d515000800c400aa101c40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 241269550 1250 241268300 241268309
    0x16060507081605090127030c0614040b0304021c06020703033804020c010c08010302030f030a020607030207061518110f12090109080f04090b0a030c05010c051f0903170c04 75
    0xc041102102680b0615030301007510b03402c06c00c0381c08000c1d6800d00c4940c40211400280c07100e2002040010b4910b1040413980ba0b241c0540300c6040c00e02c1e0030844980480d46c00a002030381d020542e0f1160402450500700c5000115124803001a0790344502d2401505031542c8406c040110421440b5442500c207240300b01802010001d081400c030114504000b800902035505850040e6292a80da002c0164001880c00d050303c1c02182107030321102554074020765910600f840d0b4401a044903000c08c510500a401400d0341e68400c10011483c500030300c1021042038056440746a8a401e599105542c6100510034141256650342c1030b1803400100003588042407040c2c0645615131405180000c02098080d0302609104e40d01041c01d540c0d0704203805102a06400c1400307059846441c100c407600b080e141c2118501d0071241d01003445014545080c0040d500d900c40700c9000c2c2c0d5203028840704105001c40143c1204880000d00c0c0c0001003000703290500901650a40d44521201074064050049100700201568101c6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 241270800 1250 241269550 241269557
    0x160206060a0303120b0d060507050717090a120c0b1315081501050702040608060103080a09060e0d06020a02030c0706050408010b0901030803150a150203120c030f070e15160605070816 80
    0xd01700b850102ea55500740d10f4000d0006440d003000d12181a03031100061000a000c3c144040004280b01b0740000305215100f01c03030354820030340c4408000b100300302c8080b040c0b614011103a42e1038081e0340d202e4403452540a9070512100724403501d8240054200100d442001305102e103490032039480c01c1002740401e00751035404503060080c04070340c11085680350380041004e080c20380c0c2a914256524980010990040c00701c6801084c000c0c0c901240d440c0c45250841224040200490f000c020b458607420020f6100d070784c2c40001c50100b0441d04178402c1d41081700c0d20040c82103070380f03103660b80d03252003181c900f100d018400061046c06407400400104421000341c0340c00c5140c5403d0540c010a02400060004006130300032005900c3c2303041d0312040c2c00e401002400b103010740307160508240d5880e01d80440c00351008849a4690406e1480400d84092050f428140c071300001600b0040311031010603178810349400c007506115411810200c10001c20255000300c981140c4241454115402c0a00340342c0e541030041034054082 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 241272050 1250 241270800 241270811
    0xe07080a0b030304031a070809030c030403030c0c03060c080906090106180c0c0c06080f07030b130c110708060a0b010e0d0602090103060513020309070803190c0f0506160206060a030312 81
    0xd42d41c080c0100c40c0155401340d4984668403520004881d074107070455040c1c010442110004800c0903001c01107400f00c220481c055072a00b07082d40c0d0b0544840075820011340b424184250084001200c6114550000070951039000c6540742c8007030041d1400ba8020010641c59050502c20000d1078039400d5541c100c1102060003080101c641542195203045228001d0003140220b01c00203116904030301928041e08886000018980d2940c078103405489044c80000e4000c0080c600507102043c85900c45525481c0500d05001c10511400301c0038a0300301e0580107402c1c660040000d0060403034207482607811000080c00c05541146070080021185a20f41401900280e0002481c885a078401d034400806410700500c201101203a03414044001c0d0030803520040644075480c004107081c580042501c0d40c0040d900d030300301c100b4401a1130807103590080c4602118800949051000014418401c0742e100b4055041d604102c0040d00500078500840504064002d4022980a00200c5da1055116080d20303c2e401d40400e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 241273300 1250 241272050 241272071
    0x50d020607060501060507061505010c06050604090803090c09060907020307140102160309140d0c050d0201110109060903090f03020922050f060105130204051e0d0c1d010e07080a 78
    0xd2510441d04024900e0303243c4000810450b4004001e4000e15005500420020881d0f080581078a00b19000e030324041001400c0f01000a015600301903480781d406403020441441543e200c18854000361804c90751500031400c45482401d03d0301c0e60503131004049591b44454103107040c010b9268440c40c80b01504c4c80001e01e514401e03c103003d40464140340d07880c00304501078900d1404c0003040c400103402002c0c400344050715607007228030f4541ba0b24000c603a0400c21003060189400e0820440290041d03040381406031105070458420030038420491a50f000747c0700455988841c0ca8010310024840d00030743c05e03601d81a0000c2c000740e1150700042d5031119405c98040014604000140d118042c2c130000240347d44601e00301040240c030b020440138104c0d00e0543d4a0b4180d8040c21520205034092400f50741d401c0036420200c81c07410300f6201e10100c0e03000c6000e000500d60010644524440c0c14940c0c001000c0e95400310002340c036a80364218420700511000344161314509015000410050300501081c01050b1140360444 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 241274550 1250 241273300 241273309
    0x6050a030f2009121f14090c10030b0405010909020301060602062e05060a020d030510080a020607030e0904081309050403020c150c0d0314090c0616030c06020309010504020301150f050d02 82
    0x145806004c1080303e8900c4c212601c0c0303510b01d02c0c55400d501040d504000c0814001c0c4285041c090081512101030800340105900740a00392500b40d2500c41095100c805c06030302501c4a1207024040c00800c1404185040640181425a2180d90111045502a408000c01c105032801d440f031941440e00c0591213808080e40312890400c01682100741d01042c0024015825a000142c919030340321107440c00d1159545041940340c078070300d40b44070710f0310150480340d0454014a0324000421542d8800e06062100c41c2407000481c2c14a00100c608981800c4e000591041c82d403400c2c6444001840c2c210380911580c905aa0000d46413060202518003d101d074543c000303810074074601519010400ea200b1580e4032003c411008014020801e441c1c00c0b00042000821900c600200d0300c044c4402014120600d4034a0352004801e07001080e58083d001c00070104110000621140029406510a04004199428103004144c01c5814100c0d05811641d154007041060b40d20558072a000c640e001c0315001800281c42c001709 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 241275800 1250 241274550 241274569
    0x140708040504020d0b131509110408061006020f010504030c0618120201090308060a0501050724090b060f0a0e010b0711190305060c03040b0a090203010f0606050a030f2009 75
    0x10742c0c041d00100b04a00d006040354090200c01808030369120401c1403a52840080700c43c0c0149008648841c081d00b44090651500030100a145041c100c40c9890f81d1aa85141040425560240c1c00007103d40c0412866504000f031a205d0701c060002017046040c20303a0091f0407010519001407a041e01d85084070400500340d40c02d010200e4001620b00a8007480200c000e0082004003400c80201e070309030300403d0443c2014110242510410303120716142500310384074030080a80d000d482044807150f4075028600c80089011340d034081d61007000200d01600f0840104490718151034841c81c002c07800c07494208001480110700c281100c81c0201c015a640302c6c1c0c5d08200454000c00100079421010445000a0065484004200302c034011001d817685a1105100a0710910058801910300000780380811207005640e40a680311a1000b0000646282084c007510283d505591000000c544045810304145800d4010040360b540c03408400c00610790100005c2d4240034440005d00d02e450f0000c100c450707041c2c4502180c0d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 241277050 1250 241275800 241275809
    0x50a3b13090c150905090f0414030d0204030308010b09011205060609122113090c1b0b0609070327020f060c0105090c121b0103150f0302040608060714070804 69
    0x140a0071100b400c0c441c84002903807003a020700240c0000c0503500c0034412503941c03040d5800180032058540750140070f00205600a48281c40f0041139000c2611903000c100020312440b82e1030140961110710314200a041d0400503841401c50b084200205840c5070380c000c83c4902d902003400340014080c2c55072000724455005907100c1d182c1180c40f4100c034803101000019001000b8401c15540700e014881c3e0f04460b040790251044108404040304000d1281c240e00d500150402203042c070b0070059004601d500d020345940011801e90f222000101445103a08180e000d03503602001a09003030020800c0e00c440c11541c5005149082d403247c6070050401c0842d6504030500e00c1c0041d000340781a4031903c5860786107000300403d40342c44941e071003141070051141c2400f520318800780403284058015902601c542c684590124903c242c1010f41e140c0c441d501d48811030116801400c54105e500540e2800c0d0320510049074029004496580d000c101000405944614031208000500d1021600e03440c091506c00001d021301d410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 241278300 1250 241277050 241277089
    0x21302090a0605040821040e0403020a021e030c12070b22080304152105040311060112031b120c03090b040308070b0604061404020c030910050a3b 64
    0x40010b00c803075201c0003920948038000241c4008022130075000900b200180c0031010385100600c01000f0b032240d02171049900c180a0b0042d1060a0034680c0081e01e071250019010000c881e88030781c402100e09040060002c1d0382011b5440c200e160070a05080b84d55180644030b4525564000929900d01450035403003201b11050031041224400d450f1541240c885c2c01600070301e000e800b2141680600c10b0302c1400b0b270403c414480c8660311050b83c840c1d1040c0000d800010015014030000da0740c5103000c01c03c10070010b802014034489580d8814018a001803810212600843c0c19100140c80000420805800810010320906100c0d042411741e00c1c0a50b00c01c1c03801d41c00103184203000300d4000244080340004022a03031080590003100d645100c1004200c41d1540035104d030303140701586041c44d281040d80c000c1c01000c169904582c2130180e641c0000305c1da640b0f00c101d400001a408504050400d40001e440910109200b20080c1c0d501c0e00b00c407206505001500b0303901c00c908951403946200d038451205207a10090b0940 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 241279550 1250 241278300 241278319
    0xf041d060115110307020604090e0313170705030a051005071701080607200c01080604060b0c0708192a0e0906010510020a020307090203151216050904020d02130209 72
    0x4601a02c207452010054001c100b11052000086202104858040703500414440c101410801c1c8a00184800e1141d11400d20041007444e005512520f002c4004040101301100035129041c603603810492290310090090f4400c10982c0006600400c084022200301040080d4541e01d440040300d030340d0440f00000c094004404004603a2400205a41e0310465054031802c4802c1410104802c1c940a950440d80040d02b04840c0e4650561084aa040c0c000300c00420200ba21510f5000003c074540c01050041c210740d01201d0108202c042c1070000d80c1d6252141c5050010314841a10b44645980c0f0340b06017044145071b210b06160f60800040360150280c0740382a4000c51603e49440c040e03546190a0040c5840354024000c03c140c0c85100040c0b028a040e80640a440c0325807400340b280e0040c0d00f001d403c6c400d0b4102c11030040d8220740c0b034101c2c02c04a0480020010f0003d0101c07948181e08200b1560032503401120345404000240c0c4410019511141d41601c50610000407458100001d0080b03040c83d81d07000403000d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 241280800 1250 241279550 241279559
    0x905010b191410051b100c020105011508130b1e130209010b040b04170309060c150f1e090a06051315020a020715180e0a15050f041d0601 60
    0xc094191800d0100b80a45181600c0403c80e0300000c900320f4200040d0104190b02280e1074122002c80e030f002c440c60464100e104850070200558080c1140800141e42d00e900412456070070420382010650181410507640c20462210030b03140d00e40f030300054110b032607002c0420082640500490044643c10040043d07504000c804020955184942a8403c507040e000100c0c52340c050703500b110111090188800d04d010b207090707070301440420100304e9603115000a1028004507110f5a004140600340740000c0c240000101100075501440a40307103100a201110030005091007118502850b807071004c00760021952501c0e90503103410320800000341401d0400d01803154003109806408455845401e561941e011500040c0049000e02003000f00140e000306010481091904c00c80300c2c040c1203d21704480b41103e03c0c112000300074181d51007000c000302030000b00070149106110b800185c508001c1c482c0540ca01e040d002602401d1100200c1c0d09c91942e031b6032842c5544020311100b90030391031210196410366944 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 241282050 1250 241280800 241280839
    0xa050103021e0f010e180906181507050702040f0f0507021b24070b01260307111c050615120a0b0a020d0b132009010804060905010b 58
    0xe120403409421140340100510318140030001c611503000c0c009520714255280115009100c4002c5160000d560a04054103042101e00440c031843d6180001e000d18280100c4c801c00044420b10440b040750402084081c10044d080c41030f9800600c907180c00e64880c00e09000050040c5842c01020000901e0800005007440306500441d11071109902900c4841e0000f1070b10300004e5480c5001c0d541e01c6919460000c0000c07803000c00e441900c0d0300c3c080300141844c150745e0b50180380410a810884d4041c180840826040e05a129155003040c900000b85007001150b5480c2000c0c810400c5050344100100102000c001004220030002d035508642190300900700000c00707659900c0c82c5211140241c201d40c1080e900d00000141d20000c09030320040b0381040d6a00c10340071a00035004a6008822503888170b040004980c0c48001c0d00b001c224482200207424001c64400e11034009400c460b080c00d014084c00459060b0381c004445961150f0480400b041282c1d403454482e00500301c10f00b0f11540034940400801c0404070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 241283300 1250 241282050 241282061
    0xd1401060506090f04020c1903031a10050a0e0423190507050403030804020117010e1e0601020a060b040605061b06090106030b04020402090a0305030d150e0402030d050310030204050a 80
    0x104020030031140c440003408407038400c004909400140110b01c03046141040d60003865000d004100b5216a0443e09001c0d9070000e0300e07240c0c1a40001d0f110400030f4114411042c511960803c00c4800028001614801608502510410740103109408248280c140c48581040000e000c5111414884d1007001d02c40100004040c2d4440c2c140201c5101490820a0f00c0d03c00d6034060070681d00c6035420646140d0b002c81e89100700400407070401a041007481100d00440e03016602030a098080d0319403500cec0480c101c0d000c0c00105054941d101d080001030040eaa6004500c2130340c010307000800485c40143c82804071f000b50007940d000341d800010005a5480801c04c42d03281545c0201c0704400c0d00e2054413a00c08060030380c1c609000c00f03009400c007900231a00614003580240f0050b20007500f2240c86956039220b403070654021007417034280d4a460340314519045030149002405070084070441d281c2c5081c5500841d6641e40d004642105008000000c5481040302485203001180c0c0144180301d00e20382204050080c24 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 241284550 1250 241283300 241283333
    0x30e01020a15140901062d0506030109020414010215070f09030b07050408070602010b0915210c0102010f1b0c0302121c05060906220605040227060304120f0504050d 72
    0x100d080c000300d1300440060003800304075460742042400c0342d126910005440300000009100000440e40c0005407500d0306070166008005501e0010f032158a007114481c0d08031001c50318941150401082e1840d80c40707401000320741144051400903030b2040c1983d030982c0c04500c142c20180c5100740520812441c5a4040003d0064940400548518503030340d031020703400d03940303094000c1d9489007603040001ca00d803030b0807010041103030001002e108044203c4000107141e00888810360001d6003050555a08030750b024018903500b01c04010003002a40310070b0081c921007400c0040c0410800005c0380c3c098041c50f108000c0525050000007000b84da82c0e000300c086901c02e4030210781400d441400c00d0000740341490040f203424440d200c041d2004018010150241a80014586c0d946c002c1669074100403c894560b0302c098618140307081d514a0072030b184401128420140030500e9442114104204400a00e03401a414881649401c10801c1242648001d42d0704e0b02071504406d0f00101407800d014140300d01e4001c1480303281d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 241285800 1250 241284550 241284581
    0x504020109052b020409020d0f1e0206030402191a0c01051b16060609060603050a0e0705060d150b07030c110603060a17030d02040321030b0d030e01020a15 68
    0x21560750b0b0500c85019910f950785407420714561201044507220180c449003403440200000f9628807070b40d0003d00f1010404405940d4018090480c1041104d882100b542c002e02c03011201e00550714079400903d86100c0284000e0103406002d620000c0c1c000d50410750303000b0384003402c03440d207500d00c41c0c0300d080402c0e40090345141c0700c560074503010482c0e5100031010102162880c040040c030706204c0da0110502250502022140c003a518080002d44030309500c01c000290403039a03008205414802003100c15280142c03a1007140e50001801001169207260032035038800303402d00010a441e00c0c900c050398100292030740405c804007000100a010103038440d000c91545803203440b14041d4410b048040c003050340400c0700c07100c2c1c1001d083c84d4180a01d002102c041e0342d40e25142800c0300c1c40c158a030019042660041d9008444440c81510602d0300d13501c041c2e80c0650014158034080106041c11400101070f10000f031405030502031003050800903030f403090040701909900460942c4103000c008203844020544803c100e80407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 241287050 1250 241285800 241285817
    0xc010f0b010f081b030c0a090527130501180519080f13080a11270610170f0901180503030106030525020304030308060d0c060e2205040201 61
    0x2040510902268820695500d030b03035900101d006035462900500000500e0b00d19a400f100d040e1054002188204006103606071107400d048000740840942d504101c0c85200030b4543e604000c58180d00031a110008005035044a85407066104550019540c0c094190350030100c10b2501441c449400800c1c3e20310490807549540d807a8406c085251003804001000d05104204000c2c100c031214001d850004180c800e03015078075a48411041c41d0800c0340303200320f40442140481d50305a01e0880c0080d0240e215405408041088401c995480b0b044004c01d140c0c0700360000d03500e0200140c424820000d559401030740101d01414004401241101f040b60446a07540c01e10b024070301c032614103400c4403045603800001141140d00307002e81a005408014100e0f40c49481d03444084050f01c17040007075a0381085664001d55555415410000e020000041c40380d4022404000c0315000910095825030031135036185400f40b02d1030980d0001400d086100303240304000c0c001c5200d203d540a000b640c8894004da01c01d0f2901c454 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 241288300 1250 241287050 241287071
    0x703030e06030609070e190f0603140f0a1a060d050405100204060518030a05060a02040306050a0207050d0f1b11120d0804030e011808010c0e1e041a06030c0c01 70
    0x103280c0b0003151503640024458011656290041485078440d120003080ea0385c01501041c0034004810341640309180c0421462001c001542d0148110000317601c1c032150100c03161600102101031518060a240000740da100540c6521071100b013641040400002d0600360750b048111013040c06410107590555060240c448018103484d4030780f00b100d04403503158540c01d0600300364440b460a07244642c0b192030340600444244200080382030091921071800304e800140c4031030440c2803410071688000e026200903441001404081503002840c507501654a10b4210380d00304c0c40c01c40440b40c000140c0b0302c0445d4000c0340c10b102d00800010400e1180b08010540d030780744c1c40d40d142c0c604040da10084005d80902041c120000f0401081c85801603803007218040c1004890303485083d11007039075241d480c0d0200e21965542c2c0f5040211aa100d40c40c0070520404850442c0c10312080004006441d40741d120b01c9101d40e81d078054041178064201079085442c60024010b40c0c0b41d00c3c06000251080d88150b084548a5180034510072 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 241289550 1250 241288300 241288309
    0x60206090d1b080c03131d07020c0105090603041b0801021e0301031a0903070209040602220b03180a170705160e060d030315150908010608250f080703030e 68
    0x682e001103a82d00d1031440300e540d46401c00b5036480390040c03e959000420a191000c0030100d12200200800340c40350074407083c0d000c0c1d80c946400c0098403003400c542201d011200b650381d11005071089000c080383d02964984452800740a020340c0d002100c460b0314421400001ca1400650161074006100b030000c6941492460f41c100c1a0f200900008003940441852010f10300800881c9944c01556007080700c1c44c118803500000c101040840301240c4061700080d00c80340401403460220800e001c581c843c18030071800c00d00c00c00b1040c00010030810611552468888403510b0400540201c13a412821031020700790016000c00080e4801c1c5400e4905124030000c01007080c40e40e511a9044461141c0d500c2010b84600080000100300403800745c08160300c500d0092000001d040300354005201c01e01040d003d038548000e0291003401664000483da924007502002184004205800c107009001c00c070724100384041a00c400103001c3ca4200f0280d003803c1d0b15011501d086d00003020b1040e40c4c02500c0325034003030b0300080802 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 241290800 1250 241289550 241289567
    0x40b0702010c08131202070b03010e10080307110402091504030501140106020d09050112020708030f0603060a09030912050703050307080c010522030c14010903050301090c0507022404030c060206090d 87
    0x713105095000344600081000c101e0383c078450760380c5031050340c0489540d48044400c035002131f0001850040706d0030501c080b110f840f02c500001420900302035800d0141c0f40d125850f100e11117402241c0140c2c2c0018400d203190350b910925019200084011503241d980360b0034010300030240d0000340940c071400701c000400e0103800001c1000580d1107aa84001442d81030000440c5d03c40c141d991869541c540a1000800090f52600a140702d0b8100e5041148940780c000205131600b1409402020528980040c00300403e41c040300810a031002c64560480310f00e120300d42540f920840e03510107043d50002080c06030070008960000c201d10820340c0001d105c2600d41c4980700501207002e070f88182c0c01e04000403095000078000d02c000c12901e1700480915400d413503045442420740d14010000c5000450000c0140950310681c41400040602e91400c1d604280241c2d0105001007800840705403510903804501c8600c1d0710040868ac043c50340f1485840c42240d540713001941da001d054482798028069404078007407991044409 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 241292050 1250 241290800 241290811
    0xf01030501032a12080d050a06120b060f03031c050705040b071e1509061a030601030b1801020a030c0e01020f100f02070b0c2802101d06040b0702010c08 67
    0x94030100400301000d105442c50043c0740d401c82080f4000000340304108058a0703580e950184e4406542c1c3c4460852250846000600142595203042c04c1403060030800122800d901c2d5000c010000380b900c1e00320002d1f0382030b4454000158148130008002180e00006107844100c9903601c1700c140010380f1201016aa41d0080d4002d0407035103801445140d000c0384a4a00c1c0003201c0c60501c2c102a8420b00a0b21450440e0f00c0c0d81c01c2c0c206501c0d844042c84001c00901c0d104486200300341080800c900c04003400040d0700d4210603c80503000101000215072100f41d142d4280c41c4440b01000219501c2100780c2c0041c02900c0c81d10f40308004520b51261104455001003580c0d120024031501400d64010200d00b0030001700b909032281851250f00f4401940051032030181c1c07a002c4c01070540340c5170b210307501001103c46008901c0b210310329041c808640480e400d40c00080104501c85a070402081591200441041d40102011003901a00c0f60900744014040325080b11360245944d0b44c001c2c041f41108640507100540191803 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 241293300 1250 241292050 241292063
    0x100605090a021c1a0901080f0c060715111210150804020a0608090f0625050c030301030f03110312011e0e01030209041b060201050a0b0409051009230102090f0103050103 74
    0x615061210169002130075083c1c1c1c0014902c0741c220050b000c2500307a10240c000d41d016611260844001007000c0080c031078180c400304c48c59450144260b0f86d0010281d006047d0300925901d6a02120f8485059420785140c10307101d0000e042c507441e20501180c0c1031040d510880c2e850400700c50142056a201d1046140720b41d40191200303600910f00202140c1c140f000508040050007610008106040280a0240641103400c05018650100440501d03848500743d07041c0e0500408019403c000782e80401564110386d0400d404440c400d907507080664028034a00031040b018000083c2c1251030340003440700301e816109520a821603c40320707043e014070325201c1800313180d03441c00032000100014070b070034030a550748030f4400c2e4004000415200c0a03040448843d410010240c0d4560b41000b50741c044503c103c0d07600110450b01442445050b4442c00c4e195004d02204500f125100c15034507080c45003041c543c21075a001c880110941e0781296890358000d42042e146144601c26509540310290700c64001e086c180e981041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 241294550 1250 241293300 241293337
    0x61505070b0c12310506010e1612051b0403080a08070e0607080c031207090e0903120601050921070302090c0f030105061b010c05090102010c0305070f0c03020a0203100605090a02 78
    0x1a2401c0101c07940c00c1c1d1000b941d8404101100c1d074084c0300200e4030102841540104030135410545000d41440000f001080858001c194205519070720001d06032080f06001800912a282d20f50290f01c0900341e050a514420030020b0000200007040700246010049030b507401c00740383c0710713004100c0b44c4195029085520442c280942004221382000616815460740d00310f0b40b40904003c1b0352807031180229004400324040e040c04202500d0750742c01d00780d80318050300040c0d8980f00568060310011200039106604200d40811400f00703907112003402a440c0e4403035000301e42044505180c15551090795000881c042d809800c003240b200615103043c0e030b410507030441500d801d517800c0000f4454150880708541c0815103c500101032800003e11600756125080d5032001d0356101c00c1d60002e0300703450b00032910400300762425080192555101c450006c00ca17400b85400015800c00e42002c0b031400d401e13460b0203503041c080e0700d03014030f602034840c2c1c40882201c1c2c1c15030707400f00745503100d080c41000c901401041c1c44500f603050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 241295800 1250 241294550 241294561
    0x2010b01090b0f0a0c1407030507060201090201021e03090a08060603010b011b03050f04030b090601061106040c15030603140601031b060f03180816030201051803040306050a061505070b0c12 83
    0x7804111644d03203022100d0046079100c841d1024005000880150049002402802001d1210740c001e044180020310050303501d0382c0000d6032028044a0050002440c500707140e4910350174001c075054140c000300070001d0a52074090b1151608010384400e0710944ca0301110801650082059080741140010007806c0402c450714151560350100c0308049607c1c004000c080005698280b03003a01401e40c1d80000c01c440e43c1007400c040d005812018100c2000d52264041000140c40840c3c81c1059030100c403811011001c6d5200706034090078860304010540b01e540d18049400d01d00c00603080b4100c1c0e00411502c40011006050041c21410314000d420000705030110320401c4501030303000414682030208c0c42e4038166603940c60301c0300745030460001001b0b10070480da4540c00707040d424022680c0204040105c624002910b07080d4a0750b0f48a180310040c4295254000601c460070581e000700010980c1080120010f410201c0003005640700c16000c40e0510b1609022402c104890805d17240710320b41e103821482254448 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 241297050 1250 241295800 241295827
    0x61009180b06090a0801091e0506060411090607051f0608060f19020a20010615110a020a030305030405061509010513090606060905040f05060117090a0f0f0302010b01090b 75
    0x81400207821440403c19154a030b290046140010903075800006284c11080c544081140d003624045101d1480c10030800d00451400300f001da400c140102c0e00000c0c240c104100c20100d42c060320090a40c070520105903201804030110303131403058540c42c55104013030300d888040d01411144103001d0100d4540c040700000e4403214018901c590483c001d00580810b140c02c903400700d810780c0d000c80c990b10000342400340003540400d0200c11814070000c200e8000d016080c01c0c51000d02803e034041e198030301002026140403000e1102444282a066000341ca82400ca640324200941030783d205441c00c075524442d01c00040c155807100c00c10f0080c0c6c61802040103c1c1a403810f02040b51210b1904907103848195034041110001d80c1d1031203141c0043c451500d03151001c91a050405c41148c582480c80d0b4101d9007010b04000725a030b4410141c42d05c1c500580585c50403030b26500002c600d032034010a001013019413140013010a00031500d00f01c50416200e42c0c002c1c0900c000b107100443e0206141d01c0f50f4800b0700014094110904003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 241298300 1250 241297050 241297061
    0xc1203050903100204050f01030b0102030f0a0c020904030e2106061003290f09090304030b04140d050d062c070201140a20040609120201030209100806100918 69
    0x10386032490820200000003410010803200b04103606074000303002c12440c1003424401304070752030908080002c09078540000c0c0d02d80c03190009084a2520005880790040c0c040d0740d604580310b8000c0c0ca180420f16003440c010703001c4502c1b105001c0c85448013810b0f2a00c1c03212510000204800d541d8068240d1303403980c8081c00341e00c1100283c44424140c68070040c40f607074000e0800c041c0400d60111450b84901824500b40849000f070031455070700603441002003100070f0000104075800c50340c0c007402d6a1219582c6080240c0f003d81142c1040a540c01900441d043c80c540c48409400b072180e180c01e04002e1580e94000e1840101210892064005d00c0c8103004009502c0f107415140e880007080c00042400c0c2d500c40c0c9440c004910843d400341c0038642c1d034042074068001c50703410318000c500481c01080c581810040042c0a449507881150b05404500c2c1c105011a4032030f80540b050180f0141445800b80c40341000602001c1c1c00306c803518014100c9801c03407401284540b01c241c0807101001c4403d0080341d4402200380107000e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 241299550 1250 241298300 241298303
    0x114040c030b191b0f02030f1602040e03040602160b120a0903360b03060d12120207060f0c09060507020103090525030606060503060130150501080901090c12 69
    0x1c040901403105000c0b502130300c40d07200098450388041d0354240401a0081914140b15002c40d4030a00c2240503044050003215000c409804c54003891141c1480014040c0c0340e503140d041c1d01ca000102c0c1c0041c00580001e045441c105009941510b1903031503a45503030190140021005103e07080c44085459600c182d4031045c0d40502030b140001c210103000b200c0141149020001300c1a41481d40c21002d054060480513070080e19001c003d15107582440c50014640c449012809498122203410350440c4a001d255004030740b18400278155110815410300300b004055401100564504002200c09418461174540d0b080e40c2c0a9180c050034040e081e0011001001028411a824420342284003000c0c0c85810800c079650108032604801a810b40c51700c2c1e415a00542e00c9a42409030910a1024984c0c200c000c06ca208001c106428030500d91102e207408130f030044541d9110046141144080150000e450321609441c420b880d4a9110744507a0300f2203080303820784d0a010b4684042c1420500010404444000146 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 241300800 1250 241299550 241299571
    0x70b06010e1f0203070302010506040207050d140d110306040b0f0907050c07050d05030a0917030a121508031801140f0306030a14030301030b06120d050901050f18030114040c030b 78
    0x1e01c820052062082e42048100580c1c000b041100800d82d090141a074403020540d015410801d90755142c1e40e9822442e2010f805010151101c11003d8002a0943d401030011507824005e810035510b001003a0391043c3c1c0c41e103011714207244281a65080020038140c050318050172030103940c2d40341902103515401541c3c80e0015405100400103c99642c0340c2c4801001c1c6c09100a10390303400e600c800140c6509034640c8400c0451140b0041c2c1040002c1c044182c44c41140f141c2003060003a00e1400706080240300008030f1034451038400802003107404001000c2c21141c0503021040d01001c440300300658040040107040c0d68500002c20000d6015040c0401840d080400941120094440340e955030003a92992051105194004401007080c0411541c856070400000c0d190601404c1c01c0700c04164a0307521007070410090100000f0001c000f42d124404887d480e9640790007080c0c58607030b0391404007013062008421b14030942c02e2010385492400444591405594001c00d175085180c91507440c203001140041062284 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 241302050 1250 241300800 241300819
    0x30f0f0a09200604031703060405061c0204020f04050d0c03141203010b091504030b1012030203070b040309080a0f110301110409150e0103050a031d0a0501030509030f0c1e0102070b06010e 82
    0xd0321341b03011201d40540c242407141c4a2401001303000482d240140441d02c1210010f02c001300e0707441d602951884441e010b42e000742e545c1c0503aa00700700e140e00c075644c80690012020480c034428841041c6820064a1184c0e5801e0001082d0300201c41d580c1200501201240600b040104000f00004008029400d4080c1281824452500404029400c180d001b600e00d40c012108101440e14032400e808054484d01d0074490b06101c01d03440080d030741c1c01a124028000c602d14000303d01414050f10004008200402c21a14900001e20b40030301d44000c085411100590102004641c500d010300500e244005105145030501c0e10b06038440016002050701002c902d200350001141c10090120901e02860061005002e294603500d0b00034071095448072000344032400d0444096641e80c0c2e0700c80c400704031002483c02158688950804900b07512803410a103040d03c500180c90040504040340560540e072401d103a00e5a01d4880090035801e0384186100282134000444c0051803541c01641c240c8207103c0c3c0505881030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 241303300 1250 241302050 241302053
    0x150a021f0f0e0601170601030812190204060f091d06090a061802041d04080d0f1407020601030c08060108030d0f090203120d11090a05010309021203030f0f0a0920060403 74
    0x11280c00840c02e003450f0304180d00600c0941ea49250168143e4000b500500156155440c0c0102d6406020481c40c038414082001c0364802c00c00f1b02e822903038001c0c0144110355a550324200079000c201d0b581c002100bc25094500001c02c1151101c030100550750b5081c21018a50f500403c124451200030207030800c40c0d41d2181c000c02d114806591400804c2c500050040e601ca09111014418015a00c03003d40c680f03440008000c005103440c41078a83c2524040c0f00869040c9050003040040d100c4442e0b011100f03c481010015401d50014040741201e00030402000c40a0300c03044031584401090081c80c2c41c1c0d03801008050140881d6a001c500071104140000030030a00c9607001a0600f598a1030008100c1c801090702790068004c0d120f0190107402c01c080d100d2401c118100410303103450782c0d803241c40d0516545e410a88290349521202c211a07603a030006903a904d28010102c141ca081d02600c11501e250103120001e040701905e0300c03a150f11550001d0f040c03a2240b24051501d402c19107a040703541d4010074280b20010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 241304550 1250 241303300 241303331
    0xf060118060f031103060f060a0504231203042318090609011b021509011107050a0303110703050702280f05030c01020a03140a0507080d0902150a021f 66
    0x8010740281d03640c0c41582d164455000701a03568131001051040f500f0000e014243e03651041c02000e07020305589054070ba1404a00c1a5814003550303100c00490007000d0784041110400350070502844004517284c820350045810341c42e079680620300855800200b41108483c4481da850340c400c5924000601c041c04c480b101c1c841882060000b0385407a400780c0e04c80c006009e1094800e011b0010200f050b45180000c2c9800840029030b90b000503144c0b2140780c1040c5011030303042c010079005000108203140f5001ea840070b003803404941c0c4080f0404180d0020349040301480340d500059040381d8546805549160038045181c080001c20b84495400005400303c1c0310740e0b60110800602410001c22684040309a46403500003410b0802d003036800403d0464110305100400070345c00401603d02d40319440c032015207401000505944a10410340b001e071402c1000b00794014075291542010140341c1c42a1640060020000241110750041404090158002c0c04a545003024503106200b98000368060119103681c0c2c0c514200d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 241305800 1250 241304550 241304597
    0x70e03100c031d1b01031d0a050d110102040b1215030f0c0405010b0f040b030c090d0b0601020c040b09070f0c06020a0c140a0c05040b19060f1b02090f0601 68
    0x10710100751a0101c041c2ca00c8299011061600c0788000030f0300412184010b03c00700c99524602c1d160501d992400d0f255100d00c40003007442d0a903100c05044448040d0f0a0030026560340002c01140b00040e10341601140850042c000e0300d08607411519070324105000d040b13040045100007440e803103200c50a1945001d040e0b030108128a580c41c000c001500c41130941c0702c03c1c803080d10380580221100d0801040701d00c1d61106400200c0701142c05040035541c4135114110000c900303100b03040140e58801c3d8801009010300011089540c0602001d80031100078000710303000c1c0b00a44405040d20b5505c0380054000850542c000e06510b00080803500d041d11682030703165030700700c201e0b00500301d040c0000342c108840e5010003010803105841000c00500038540c0c201981c1e034005400c680e5001e03450180fa102c026118168a84080307007035503581030809004102d51121001007602c0400001c213800501ca022864403140e00c903041074002e10b50041c08030017003941e44222580c00301070044c15240c10058041110300f03040c9200c0703845 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 241307050 1250 241305800 241305821
    0x209030a0b060301200702010305041a0f0a0c0c03020a1104091406220b010312110a03030c02070f0e22021512060103180b040c18020418020f03070e0310 67
    0x15002600b0100d0a060840e9124203c503084e02c84142c01c4549540180300c00d4400b1190309107400704807a43c0d0b0b0307d08000381c00d00d10700c2d84501504020040c011102000c1c90464862103442d041044600d101040450718080c180e03034090090782201030400040340440480b120212006030001c03c0c0c011a80d903901c4003918000c0850023031a00180c0520200720500c007000c0c0d0001202c08460070740c042103522a80e001d000184801010343d264080d603c0080340c0a41e10148442c0c1030038007941c92070001800c000d0003030010003501600500404401150348400714002800f600d828480c691200e607180035024100340006203901c44000c001c002c0f0b260050303882281c4440980d1144450b87c0d124803128803129820407001d40403d051506010884001090703540f4888915030300041d0b02840c40d107560800901c4140700d6040b00780c1031a282076090011585c207800420403070b6a1074201200d0904100c5000040340500e906c902c0380c0040400c0820b80d205e114000441141d0750040a941c038010107101c1440403a100c0951 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 241308300 1250 241307050 241307063
    0x3030703020f060619150e06030c090a0f060f120b0a060207081018030813050f0c090a05010602120c0102120a0902090a0b0307051009080115080610050105030a0b0102010209030a 78
    0x9041095030709204494011100342d172400d400d0705101c80500c83c41d801501500788851040203407003800034890010742c04000001b0b0308a540c1c17400d000b1050355480d48101c00c0d150080c5854000001c90000307600c0d491046031420b640300c10703015640d11000c59413031203c44e0b0441405600d82c507402129982d0f09402c04014107a40e00100314151904c0e20040c1400700f180f00d1541d0b42c0c1e203010070843d001414882c201c400c00350b0500c0c00d4200703507681c00340c2c140d011821010007400364407404201c0c5081c02000928204040d50840d1860700540e01d21494606480f000d00540005030406204d6090340c207452805080200401d400140c02c04440c0c01a6049450040ba40d00008a440e0003580066080180c004d41c0c100c00c040d03400380040102c90001c02c0d5207a000c0d1061500966102e084035200e14803c82c0c0d02d00151601c84002d02c202200f40300e40c029240403034042d00c4082d0050134045064a000303006400c1c02c0742c2d0103854050856440e0301d140c1c0000c0c0103601050741555020044a4000da03018400010028401c90 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 241309550 1250 241308300 241308313
    0x613031e0b0f01080a02060703020a170a030b060702060406140418021306020c09060108070903050604060b28030803040206040b160611070b1302030a02090c190c02010e04090305090303070302 84
    0x801500e0501c0c00b400100324124180014070580c3c00109252540310b40580704640d9460f11450101d190949040d0701600480546201d507840001400041803d056199420700821011100700b01c3c407031166510096110404000c2003101e1405001540300c0e443c034070344042d420141d450b501503010300410106d200306107900080c0300d1101079084005030007910ba603100a22503542e508010507400310f0083c1686051043c00b02c0000d40c3c162189000001650b440130030b462803400c1c1032034014081c12003014101d10581490081c03510500c8200320101c070f40c01806400e071030101d145031103103540c9502c040d1060b078100d401000041500d10f612001400e201c0c2500041c009010014100388086620110445000180400a000c0410f40c441c40c0f05400071070349061200c0507442880044e20b0102e0076070340250410b1a803000c2014800c0908050800b009640b012120b20500c0744c0c000312002ca05442c0000d01141d00038105140904240d801800204d02c2410810728148008000038619000701008800591050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 241310800 1250 241309550 241309553
    0x303180602060f060619020c03010f200c010f0603110310020c07210b040b04110307030f080723070807080c0303040501051309020703050304050123060613031e 70
    0x244a0015812285420940941840002912030742c000e0301034400c811040011030016034400e42240d40c40080000244c10000315100007031b407035005060045100e5403038a40114588a694052050504100d09491100451001c90003120b0b030800724000c5450741d65006000c05151072442400043c6000d43c864203100529001010728200d094012800094018000c3c00c0c942540010700c1c3e01959202c54a0b504030003002e884d114007800704080c010381405030250900c018407012000f4203009901818141c07580125034014140e840380380303200090050505444080208504201800b2071a12543c0d581020300c1b4024075400d4030038050350310008076070003c031010040d1101c2000508020a01d8102074082080c444001a807640141d00c6458103000001801e150b000e40710100714409004106801c40d1503e42d035007002001600100d03012102d5619140d001d2042078034608c0302094440b01e614050030f617560340f18203000c4035070000186804c1e0302c01340c03600100002e408441000e07108441c0e510750b06040c9446 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 241312050 1250 241310800 241310807
    0x602040e01030b070c05030d0e0c0d082512080a0b0d0602030105040b0405010f0e0615040e01180510090216050a06050a0516022a0904030f0e030309010c120207031406010303 76
    0x1138407000903c880c0408040004101100b5101250802c0a000030f005400061103800e14043c0001d00740d000c11007101e4401085802c0c0013070211f04080700110413046411024011143c482d01c180070301114a404ca6401d420b51062500681c00b0601a0300800c01000c1030300452090f000c0c0342c108440141d002310041c060f0341404c0c0305103034020904403402c2c0101d5140540248441251707000c1e41d40d002c85414000b80040d2074000f41030341092000103c0c02c3e511542e40380390700704c506802c3c0280543c0303450280003000f51840a004050240d810705500402e007903c1c1c0f0038454000e503c1100d1211b10b030b041110146000c45e105010004007070f27004060200d00c503c0c0c04100e0318200e41006007940301c0c030500442603890855000035106082c81c0070820800f2416981d42c654407000b020200410380c400f007940c041008041d8098004401101c07107407030780585510114105501d07401307001d41480c0000d0a00440c44e021406213551139100d40c0c880d0058924840d01c1e921200c90565003400d0b01e82c1c850348990010001c15a1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 241313300 1250 241312050 241312073
    0x150e040e07030b13080f030a0207020306040b04031407030503150103110d1e0612170412030f03050106030e0a0303090212070b130503060f0f0a110a021b0d05030909130602040e0103 79
    0x300600804c20104440e9141c0c0440d000350508500203110110000741c1309066a4121600305800030100c5400349850300c1c1500c1d00b010101d80460000360502d41000f441200c0f01d040c2c4101c15455101c0380e0440c0c0c0e4100c00e90000040b800201e504040d103e58070707224217202400003000081e0162201161075900400010850b03901136801c071008500c3c04800304140130003600d000d042103a10100c0c224100044141c0c44040b406590000000314195020742c9080580140c03217080c1c0104151818043d5030b0741c070001501140c401140315541380d0094080340c40041e21a50024015910040014040c1ca074182e682c0b03407a0040541000c00d240030005070f00b0318000b00c40300a4000030403048005000c1c03490000c100c608140400b80c51500d0105000b004070b0070f02e684a801080c50450f034181e20a0701c801c40340c18025611401106440f07030041640c1804401c0742428100c01c1c020a4116009510b880b8042050190000004040c0c05000d4813040301500003da59000800041c03d00c501009510350440c18141401030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 241314550 1250 241313300 241313311
    0x5061305181209060f0a030f060e060310050105010206060105070c09020406090503100207030f0c02131407182d080f0307021305060d120507080c1c020d020601150e040e07030b 77
    0x30090100d40c2c074944c3c88004954808803031401131a2074444801003a00038068406071580303041d040860114030a03141017961442002d04404035049919104245401c03074000307000c0c0f6401a048580021655409140142411882031800d030582c82c4c0d13101000012070f0080e4000d0b00009103036241c00c01c414034041141d10200515500c0441c42c010450360064801c4585122040c1440007903480e9905554038405400d0005010314410b101210350b031004082c41880403280c0801240500101c640c08034850711034001990100c224500141d03000740a500803641a078039800c25100000341c808184180c09100d03a4580030101001151622200d03c1045070f2204003002c421a0303945464104161359841d5520346080d150810300c0002d00c1c43c0d000c0e6084602d84034080001e0f040501c00502141e10440004a02e500c8841000000740b003000d5940040740c40d04020b09407000164070036001400104440b00a07880c584140c1d007004060a0803010214044d55468110b005141d0000d980410902c03414503490356020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 241315800 1250 241314550 241314583
    0x10030b0115021f2405040f020f0702042c0f0105071e11120a12060e0115030b0a0f0303050d0c091208070c2105011406090a0506130518 59
    0x81406034002543c54003101550050030140762880340608503564030080843d40144040031140744101c994084c104c401e44520790140d8640550a02e442c00b035031080d503000c0713085101c545103410002d0302040098281c100103045a0310320840e800001c0511480e0290310415142c011348050221301c6009421184e00800103802c0c42121521031440c0300250390072151000a504043e0b61000c0399505043c0390821004026050354000228030184a800413040f0300381441030704050249644820307550507403400030302c600c00400120791090789016000760070030300d99410041c02c04400c07541d41d1030002c0c2007001c050f80194041200090300c0b000c480020f0089110085071810b050015034a8181841101500020068401d601c081444410060424100c2d80100030044421600f201030311030152100071009001c56466107004407203032003e100f11030114490074004103268001e80d105840c020241c107005003402d40c80100b040d120242c0b19481c1c4192402180848d2001036903060301200d40f40fa140210b43c550014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 241317050 1250 241315800 241315829
    0x105030106080601120f150807080a020303270a0311010f0201050411130e030307050a09120201080402040e0309090708090706020703050607030c0c080a0215150306240910030b01 78
    0x1038a4200481c19000f840038a48100b580505000c010010407809003481310300d506007030311707150540850f241d03c03c1690700b5213041c0c40314035668076070b583d5079010710340300081d09504144403080032100300d0f40c08000b49a01c3c2035503048141c2c0000707001400912580d001280d411002004c3d00d11305591000a1014402142c0004c200d50304058945205544024010506c5413900700243d40d00d01c0c000b5040301e0703000880002102d40f00c1c18480f0024090f038100317255030000101411070004410000e030b01d03000950754041c0c441a01c280c60701e030284005001c049aa4581c5403004022180f17031501c40b03a000501c252070b0340d1748030b4404c3c0c10300c002400e090201d540d0101c0c00310760040300c060002c00e0022809a40026150400250034011018283d888008100c4046c3c41c810000c80d181440350b0b000f10b0100792a010304001005140d031040b210200107030601c8038048d01507021400107080407100b1111410b0807516001c00518440c0114001b441180381100c0149510688400c01c1003001141c0540501510300b00c11303c03000e07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 241318300 1250 241317050 241317059
    0x70b1c020309071802071a060103050915040320030703030e0601082a0f030d05040e0604020c1504020112020c070504050f31061109030c1210050a0209030f061501050301 74
    0x241d0700300c0790050400700304041310b000b80b680c03211358100c3d000305a1000008015504a080721040200b0880ea01c0740401e04100008069000c04140d80c40120302d000c5103d0b10546071520112210801ca4100e50442d203d464400603401200300060144180702c0c2d0b4010a00f16521450b13142080c906030700c441c42950110303501065091940030807524007040803c1c46121041c403200055000b0040607005501800380203d50350791164000d008000782e60b454116130b201502c0b103006020403031203000d01082058004208800c0708075401c09900b60854014900b08010341a6001010100d034006001d44000f580844000c0100d400c1502604d0344c06500c0320f00700b0004d4502400881b800c580300d28141070b000d60801c4032020f00c1c0d500c210b401e4100340741c0100040001ca081002d80c010540c0c420601c5900c6407003000165100c84c46c181551105248000f8090040c0400e03100c246009004060320143d5056000c4c00000410b0701e0802c526244549040024022410907041243d414440c41c420f640c1003001c10030044c40b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 241319550 1250 241318300 241318303
    0x70501150f0303080c040b04060f1106040b01090e0c090109090303240b0c01020f0723060601140a0c12020c0901090203040803042d05060907230405060102030c070b1c020309 76
    0x2200d415050010140c0d9034216a08101c1c8615081030b07007481404a804076000d0350ac41106e076030801c0a0f0322002c4018200103c03d41d0b481c2e004940042002c84400b006010648068000642c954094000c0714880b2141300006007400303001b60402c4020544d034201540500d07516000d120405d0207200444110318200c00640e600344d48480c01184010440090640482c410950454801044100103162209424981030020b03610b039082c1001846090300315034a490380d0200c0c8207406204161240e681e4a078800c10b6243ca07540110038039206101c4204a501c0120350500100f0028440a9000c0c0119110f00c10820940e90810703007111640c10300c14030400c000510710100300c03904950401c0c0c1141004250402849c3d012014014544012408107200800c00000103409805001494140c3c0c201c40e031910121100640703068140c0030004607601c80c40403181010b40c00940c00540c1841981d103041540d5000318540704030745d80024103107000010110003100803003040c1800140525001c1d40785050001e03015 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 241320800 1250 241319550 241319579
    0x8060306060402160c12060b030c011e0e0d0803010303090608041208040c050d0c14010509061b1203090607030b040c0c020f0a1806050405090303011203270b07050115 73
    0x85000300e40c0000ca540244900244e442c03051540544400e948039100c0711034565203820340b0002c071100c60a1171518012071501080e1508400710607074904114000c01002d045545071410101010f1100d040c500c4904c5e9100c0005009010b4002c0703200940d607526502c1d00800400d2203a020204000b800411b1200282118540103005030709450a880540c40e941010160046140e001d03642c001921510b40c002c00540b0800702084842074121200c050202000564682c0b0640e014554020402c116a5000314240003144410390040c108449410501d50700c0c001b460342c8156110041944801c08101c0d19a90601403410000e03000c0c0d40c1880381c610304800c0500301c1226010006c0c0319075080c510784c22084c0c80d2085403c0050041001c0c0410394007400e00d40d5030082c001030260078007990601e000510b45200000889048400e258400856801c240c0c40c02c40e542d44014444e8640d00314140031a80769013200a414102600c411001c0275600c1e00f0710310f0a6801c48000c242d0131901326030380020401c004020145072 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 241322050 1250 241320800 241320811
    0x304060804150501090b0f040c14070501141f080c0d1211010204090903082a031902120906070f050301090906090c060221160201050c010b03060c130608060306 70
    0x414601e031210b240a0054050b600301400070746140c5800051040040d40020410140a403600307145c440b140d4050006a903800103a420105240300840007400304a00014100d0030300580002981c2b0b00e85a11944d045039058901c0c019042c00082c0c4031015101d032222a00052814100070103140f41404046810071401c548050b1a03101d8801241103410f014002403960010244000c5560f292501c0d4640c0041041e490290005200d010005a0080c04620700c480442000124800600d28101c0f801102d0303071004085042318641d586e8100f44031485400540700c08481d6264021140c60440b0940e45440c40c018000b20820155003900b048881d003180480b41074491203600441d403480709041c554041c00316411300a1489044501c002a407590103d001c100d40740e07103149400e004c2c0701c0360b004020031401503d00c002c0111440c0034000c001580158020000300e01034130008108503240c040040d007082d03001c42d651600c0c504005a00c1e074080400c0041040a0a0a8140300046042480c0031030740d540401401c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 241323300 1250 241322050 241322057
    0x20102040510080a1d010f06270e160305010f0e010209010801050f01170408040501020d050f09090403032c06070c170a02010219030b03070b040608070c0204021309020705060708040302030406 84
    0x2c13880c1d06441d03401402111450f41d090041e0448015100390080009082c8001f082e8036000012071101c914001040c9007094541c0118606000d200c5a000180788900c00d10681d03106a0920000700220251321000a501400000802c004800784070760a96014120410701640304000000950f0307007040407a030559105650700707101600ba800040e0f803101d0320529411558500001000308000441e40140284c490a81c213840114000d824142c07454020708214100f02c0005005152440c20719622903030344a8041d14001c1424154605540380c0070f41c9c1d43d0003250091602c1d5284810b034080401c18140c00c0340c0140b030000140d00c11910392240494030841c103082c40c030000261411b0003a02c01d406541d2007907501f150076403941c242c0c2000030b030042041402c404d009000c1c040c40051598480f01c103650444d0f1407502c8461440d52054421a01c0340240b040c12031b40b06501f40302881601d03087d1030040004d4044048010313900e01043c10404d241c030034010084070030030a5080800002070f5012050b102213034010309 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 241324550 1250 241323300 241323317
    0x14240111100207021c0c09050a0b0a060c03030c050903031c090c06090608010f060f03020310090e03070b06030604050c0d111005031e0601210f0f05090d020102040510 73
    0x401210a000d8419032800248201d46001c0c9152500d80d00802290344212007064844e007540741400c4c111041038102500e2004208010402400c40390004c540c070140c44a000200e00d0000c030005840780140b5044100014040b40d526030405800d4824450b189005042c81410001442e00090740e03841441c4211011009584a035015861181c0002c0e0040b40d004000302100c90b25140001c050032440c0c0b080d1400115400300014031102100b403442d090300d00c10f55071803408040810095019502c00f800c4440d003604101c90005034200184100e04800c4c200c0b201039030f1ba4803920f08080040841c040d00700c41c46508500148400905c000414078404542556284001c4546051000c0307907820044a55030040101d2000081055000700118880c40c003401e0002c0301d50000c0e54015004c03a6003183d4550200f1900c0b00b18840c0781e002d00041c50018030b0342510200710740841d51401e00a403400d980320041d240341c84501f44007a00900380f00c60304004e82548021800d081c9440001540d0002024014052001c0390 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 241325800 1250 241324550 241324621
    0xb0d02100c080913140c0c0c091302030607021c17010306090213141b070c060e12120310080a0f03030f091a09070f0501050d390314 58
    0x1c4003501c0914400600b0440040035110005001d030080c40c00c08002c1d405c0c9000080c5030100b290090b11040d14080005101c407020300014080c00c0301010300000c4444480300040300c0142d4041207501e108540320b5002d0110140ea000390f042040305420081001c1c0441c00d0800040c00340b2600e0240e044035085040032840300558004200c0540c07049491060380c0f81060405a000c0c0850038841e40154052a042c510030012903179884e0907409505401820740c055081c040000c5481507d1541481800900701010502c031005140d15094040d11820390040e0080700300a815490070714020020440c60010740001803041c1c0c0c40300c44070080b0210060034940c0d5070f2145007803400a40e2020152550085c400312030445100001c0840800c100c41c00e030610720850101007012984544120200c80741030b10f480c2c1c140aa5140c0c0e1402814074040c420f090b8a89803006c503030502043d4001c1d60040d400790786020346d44a05a82c1c00900f80c41c24402e5004c5034903c004c043c4882284101058807040001e03c0b040040000c64 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 241327050 1250 241325800 241325813
    0x300b06040308121512010204080c01080c030601030b0f0607061a010513090c05040b1804050c0903070b220b0a0f0302041203030e0c030d0909051e0403081f030b0108010b0d02100c 78
    0x4030180d2580000e9519480380403084151f00500075500c040040f1202c0602e9400112050b01d0122062a0940c03014400308045502941026050a10003014a07144040e504042080c607048040252070060700c1e800c110220104285104104401c28a4550320305090401c900413105564481d200c100360b030303400b030002055201e501600d0252103040c00d4250f070758000da200c3c5151921210042445503103080003146d402e00881080390a007290140180c03182902c2c14a41100c00e401114014008070005c1030915900c0c102104290040c000c0080b405440d290a4140144000507010022061601c10030003400340c91621030b1682c10345070345890003007203a11500044a04020008030120340500c51031007642815608603080c1d40580d0110300c02000203a50709030401c030700030850341c0014415811001c049070100741300e050015442401d120341c3c140d0121615a010f840c1e164a5072055407901c4a040040c00034500030302660340318030011188140302808039000200c21041413101d540034800005c4688080180 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 241328300 1250 241327050 241327081
    0xd050a0203030f0301080d020c090c07030c02040f230f130222020a03140f0f0c19050d0e01090203100c12020301260706080115300b0604030812 63
    0xd01400b41c9880b40f8941d0107001c8913400c00c6c002d404031030140e01c0b03a149210b8070000e524480c0a000074007040c4992961040300d0b2080d40b09550943c2004280510000980c0302da000c0c801540c680c440c00001c01c0f42980d0240020403038984100707501d0244e0002442441c2d52105042074001c031040c603061580441d1807002070300800e40c5400b0202d09090780e9080608403559540038040e032040d541c405114234801b07803281d042d85920807117900d010207101101099844c103500445d1588500c3d10b084852a020400031009160f1403441480d000041002a107050080d60074025404e801d95128001d102081007580060303180c00008800080c00740d59020201e148038401c00000c5000000f07840c0443d541c0d611030f550a00c1c860302c0c4e00ca28a40c400d0708681007508942000544100700e03112582c40c100d4503401c00881d20407804813101c8040030842000200785c030390786504556881035103003d44c6080e900b03929000c104055840e00721a40d40700b840c0a2004001061200342250f2007084c4801903000e00d03907120940f402c07103c2d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 241329550 1250 241328300 241328303
    0x10020a0309150b0a0b2506090525050d0812040c050a24020312150312040b0c0705060906090616050706050406080901060b09042c0a06110a08060d050a 66
    0x946400c40d00b030402d0b0b065800902c0c0c404058452250303442d201c500b20f9800b44104110000710b010f00008620400b0804030040003450f00c103410128080d03426854151902414142500c5c3e041c0d03010700040d80100e107003040d000042c03c05451001580340036494201c8140070700c0300410203141244000600f002a00503207079002d081d0041034850b410ba1140d91035491007000c4007600080890210301d05028500020035a420100d011030071158039a281c0c14040d90100400c0c00c81c0f9054851800c000120300203150181000d08091100f007a103c0a130b0a90741032900280350700140c010801084000c0c01c0d903d60780211260540c0070b4a4049d9030b502c81e042c0c09000d041003101e01030164060803601103082c0f50712200602c00c6a603140e5842d051030300e5540105080340e0080c45407421883e01008810054105900710007010080f8941d4000740059030441c000030303100c2c0e4000c004403075000300d01c07a041040340c1845140b400c007081888040c1005d0800030080d100c814007034041413050883c900c07051b04111040140c012040e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 241330800 1250 241329550 241329563
    0x30102030a090308130507152604120801080c0f030307020a0b0a02060702010b10030c171801060803120c1b01240b03101815080d140c10020a0309 64
    0x30300d0104050001403880100480002c1c00d40e20118417003030a001d0600e10203c0e0004040c141c103500c1c05140300c44c18403941514800740654502c000c59024100c000f00c50303034441480051116850249001080c0385000078684041c0140301e0700500c40f2000c00551741070011010795807505e21403c504006842c5000b04d501c001c1d07000030300007070205801810b2000342c09400c11903001c0300c072503032a14a0140d00341d44075030642d103411006003c9240525486904400b05805141c102003621705a01500411010070484150103c5100e01e00c00a6900000b441000c00805240300a903007408c20000c824180c08201402c5c02c1d44582000c14241c20903c0fa54051142560700d0800822040d02c0141c900c2c028807902d108400c2d0742c1040c401e80091241c0001003201d1044d8203c081d460021170520511540e640411041d6101c05035846c0318040300c1030842c503c1c05028000e150002c00c00c610805e03000801c103000200c0140c1d4810030601000124160000d4040c100c0743c4404000350300c610018104a00034203080c000905007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 241332050 1250 241330800 241330807
    0x927051f09170d05060a150e01120c17091b0f010306051c0506060103020702010507022b0b041704050105040605070302010f0203010b070302010c020f0c01080c070c081e010c0527030102 81
    0x2c4040707441c01041000480001444036039550400c00420781c81038451548104a49901e0303a186522490211074150b00505002188030020f4007100221154101c2241c081589407203694101c10401ca42c003640541094000d080300781501800690600c05c181c03405014100c41c070303590352440c1c0c00394100303d000e09005044800e003003444011002c90156034210a8039180105408244654400d000f29282250107840781440c02c20264240800c03804071903910450580449070924140d8154200711402c24000e82c5409800c2c1420700305600c003500e9040945034507510402c01004143d0b0400c09880407582c00d41407068a91040c4d007010b9006d00000e2203800c800b107200100229545010070041d107107560003031340200a195040a0b0990342c50f901c05c0e540004940c03004420721443d622a02d4103e0380301078101a844e050400b6580c5050074003140d60040d403041d030001540206041e020380f588a802071056030007444004c15011018000c0d11178403045010b1100e85c0540285c180402074111078204d100079000715034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 241333300 1250 241332050 241332083
    0x311040e060f0114012c1305180f0115050d030203191106240d0c03061b021605010f12020702101e180905130b010927051f09 55
    0x40b4000240201c0d1440e003001c18000909503c12640d4003020307091450b410403070034010701991041d000908009903000d24900400607041c180d41c05401d0003030081070040705d0220207401c40b0a00308103007028420f000d030b03240150305000b44c01d520000808071a42581e141c11f4401150600f01d04600c00c040e804950840000c11050101d68041003001a07031f0324080c103945058541d06140e003011200c80a07906041c4031082030a002c2440c14482a4031850703c00e805101c4029030b40ea8841c002e54242c00c90503030503c8003600b90280c4903501071101107015880315007000c1840c0c0c10500060040c4544445600400c03c192210114480c9294100c170195900105410080000e900e401441125254040c40e410314140100c1080303580100c070313118464450300c02c01c100400d0400f0082c0004100040802600c0681041e18002007003140e6641070180800407400b00b0010300c0300b40020b90759041c1940d00c0203050905410000031440c04102c407105541d980040c04100e44040e10304201400940f0400f41c0f4907145109600d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 241334550 1250 241333300 241333321
    0x927081b030d1a010c080c030d151e0305060f150303030a0609061202030a0b040c0e010b0a020c100516050f030a0e040e0c0310020307051306030b01020f0607090311040e06 75
    0xc1d42080a506003c2103502425401c002d40040188602191002000f03100207610700002c0d1000300030740d03821242003044800d10002600d18025414001401d580b41c00d2101501444c0000d0440d1440800c5803045441c550764183e80b0300009100300e800900130400301c1d80d0391840c1000c40c58105402000c982e26418a42d50401c0101003030310a50540320714110000132140030f45404241c40c40d800030701510081110703844500451600501c122003140c520382010480d6011070b640f0714043c1050295003070b110001481c1c040d1401c0d050403003407442103221a24042d4481da200e403c032800380451085a1340c008059241482c5010010a0b80c0703000b902021075a002241d0340a00c01c0001010121801c1c000340c5003482c4030035200c2c035205a84981642040d40049040c050903002540c004545203409032501054502c8552000c031160001c40c0001d4503159420155a03040003490041d403003150240400381030098014110a60a00c0000d040760002500240d8940d41c583c00306079100c8226091358bc81d481e0600205 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 241335800 1250 241334550 241334557
    0x50f0d0c08070e2704050f0102040303021c03060b0f090f04020d230106081f05030a0b07030c0810180b0409031e0201060b0405060304050a14060703060927081b03 71
    0x1c0c8005020f03200207501a203400c1c2c0300b03010000e601081a01d00000c1d100311007100c49030010030a50391442051603c60f41c0c80401d1004000941c0a070b070140c041946101041100015424020760030142090300c14808084201d00715484038034014806655840d0460101c3c0c00c400e030f000c4505034841d1001c1100c21030204241c1001188949003c108007000410100d8602a01003c0c050003000a0605001440010818100181208580f20551025540c40780080c1c90007003510340440e44003452406011941c0c0e0140100c034440302940c00c0890349460904100f003240c4020384248403050b482d0f64003090703810342d2030781c0503145800d005041402a001d0304e003000391840c2003c510341460741810481e00700c2d13094410320640080c1c4080440e55440c103032402042044940010340103540314000d00d501c0000150301960140344040076000030389450f2420340c42c0542258500d5101c105060700346089400041c000380c450241180e6104540940c40c103190404214901400010120948440075135042c2004008042c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 241337050 1250 241335800 241335811
    0xa0b0109410a0e150907090b04031a090a03170a020f0d06081c050304061a0402130504050106090608010b0a050903100b09070302090d1103010f0c0c02030c0409080703050f0d0c08 78
    0x82c901e003a500c6403071070141035049801c0601030501c80b01d210b0080c80d04922440c1c203c0d02c245004107600b07840d90841800c5030300c15817044900d00b01c603481500007695146152503020306044040c00024846031806061504080e20315514080c07014001050399260354150394410710210f5101d61107060303160095004003414021a0301c507101ea000c0001c045040c0281d0030b800700310140d590b00e0550300c5070303581c0d00c000e8580f00703180c1071103804c074a90896265100d51001d0304e01481c2c00031030440514613000a11007103c034184c00c4241000300d200c0040c0681c075040500981100d002440d983d03507600744038000700d4050148184580e410b001c0e90404184070a0142c110308034803101100d400c1c0e0349880c2e10506908070301c20102c01c503401107a000f0900006c80c003800c0d107140b80810b019001280249510544104590322007c00f400454554404003066060410491040020035074040140440544602009000c1e0038001810440000f41000343c40d10494151004071505c0803081c0803080740e07184003400341e8004458 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 241338300 1250 241337050 241337059
    0xa050906090a110c0f07080a0f120c08031303030c05030601020a111311030106020c040b0d14010b03251d0105220612060e060f0a0902030115031a0a0b010941 69
    0x72a4007440072624844c03c9902010842e510700d800cad60340709446000322149a041c03250700202c1c0130226910800540c0306800658401c04001054a405400c4418000a0b1402c2180c1401040104d1741c0009821190030381000710641000310590000710203818002030008182d0900021141244881c000b5506a45441e002e80e40b05110b07980a200886030245020f540c07125414148801140000d00a900800380d5030001140b07046421001c68503000c4410b03901d8950440c0e034a100c019030951140e8a0b8060114000500381e110915081d004180301c06003d440d01c1038040403100040c400c580140440d00307c0c00e528080c003405036540060480c449100c6400d540362818209240300402c0046071075031040c1d42c00a81000e20ba154540703c0303002080035075401c982541da580a0072a050003141005d100441c2308440402e80860180c40a0082c010090480c0881504101a00460b030380c20000071000e5500b8030b005544c083d1100811036907100d095812041541004825141c1104010420703114010390aa8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 241339550 1250 241338300 241338313
    0x1507050616180603020d15231f270e0a06050105120714070215030702120c060619090c02011a010c0c030219080304060e0f0a050906090a110c0f 63
    0x40240c1e24202e4400514018140060040c00068041c0d40907040344108100c00090244000c0046607043c880c0341c120100c4040f14544482400f614100401020b4005440405459490449201082041d078054205101c11040b8401746c40031244008041c0c406030002130078280c2d0341c9040d203400400d02600c404401c0c0b42803d10100d4154024411200b10101c000328459543e030b43d41100b1100c88000c42e8011004c0f100420104000d6510224200c108000005205940342401c5901070326241d0684000c4812460502100e940d4080110b480c0c0d50080060b9400042c100320800d013100c0004050700940c902d5840c7c02c01d56551a41c0c1540052000c040300743c080d00310000e83d400155928118100000c0c0104409241403006040c00c0603000d0841108401c80c400c0c458a55a42030b066030495002070380028170070300a42106190a07000f00424041c15200c41c43c0b100c0c206004600c15180c0282401c0c007901c00711010034484811766001400c00309044039215122071054007216250142c0380400b038124812003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 241340800 1250 241339550 241339591
    0x11010206070c020310050a15170c01031e0f0b0a03030c03080106111905030708030f040614041106070302070f0611070f0e061e04090b010905090601060e010e15070506 73
    0x1098050300e03550f002001041c06600d400101c1010f410003c00680750952102080c1141ca020f4603510409040c0000405285a40346001c0394503144414082030304042c01c041005502c404503248100b40040e14080102d15505070035048005802000701c0380d44c119401741800010700d5401940703904058400c2ea0b88001c1039903149011500e4440001580140b0341021425898820b10011060340451041040da404e1400584800505030070459440e60000014000c2200b0084244101c0820402200103000d8600f040c0e11120035001c821070040740034210000e0890203260081100500038542c0c0b684c81c20f442c035101c0c0001008100c1105010641d84202d10000c5a01c1c1e101b0b1071356000342c03822910203648507a1071504020454002d5180384140c442542c10701d410b1511703280144100140640003030407240d4901403510b412a1402401010079400c050b005101c215440300c101c465080382485d000000b40d0f42036000032201031a211038030104040c00500001042400b140040c803616007120f014a171402c12 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 241342050 1250 241340800 241340807
    0x4111c0b10061b050d030903090305120306030f0a12031a042d0203060d12050d02121806090d0305060f0303030f0402030706141603030209090403020a0203010b0301020f04031415041101020607 84
    0x2503d00804640040b103e111616101c0d6000110312402407400542041e0b5a888244c1010701c0340c02d002524420020400866083c1040904101038154004019a02c200d031a100b4140384840c00030410162036084003000b010000604495080340200100704e00903c1c4103981b0340303000c00d90495100ca441206000801fa14480c402d03030b88105405840030300a96582c0d55105e40740a44000c031700041c420f00b802807250340c0d0058405821410303801450300c3d00f60704003030001d0381c08405001c0103440158000d0081015454001c01c055000b89158203000c981a116100018440012211003581511001c000c1010707250301001c1d0140100c0c029000d6505864071400210369038200844c0711083c902c401c10500c46210b400303490707004106009241c018180040b80000949420045c0c40960040c0d1049104400303501e000e00c074400d00c90360224000c40c94080940807544030ae002c4e03440041c10300707101d41c0108482c00c0300030320000c0b1180600084240d84c610f4a80380c0800c0420340703814114014032a800c000340c0c01c14007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 241343300 1250 241342050 241342097
    0x702210f030903070c060305010614071505101d060a050f0114090414090307150507020705010c020a0b0406051e0403210c0203122104111c0b1006 64
    0x218150294a000200e03032100c1625030010300306884034030080250b40301090882c51190301038115030742c000c2255490038100901c6071080010006400e5820002440080c0100080305162007000501113955030742e18200041c4c2070060b40c040104200079440e840319891848401c144182c2c0c00300e4407030180039241e03810301490181c020101d902082c240100528041d88083c041d0544000c010008650410074640b03035201910b09a404e10b241e43e2000c034100c401c0090080e41d410b030705441d40c5020465032401900095440509205060611000d41c2c00e07a807d64840204030400f804000c5c2900f50355599030400105154040202080c04040015850340080c64040445084a8000615011400d0740b0702c0e1494038054a00241c0341070002c8440c240e07005031400e110142d00420500f9049403686480c007210321000d0403909581009898bc60200400901520007851079814140c40004030001124503940902041c403c0c0a0100c01d280c0c400c02c111002550903d02c26034109588011381a402180c41e0b110045 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 241344550 1250 241343300 241343353
    0x3050a0612030813152306031c050c0706051908010b0d020c010f05010608060109080705030616021204080318060a080c0d02160606030212070315020310090f050702 72
    0x307089080400201c0e01c9000d0703698210750f00c40958071481c0a13070390750042555046682503411507100d0b50140c0c0d0340702c0e18001e4015034225510015800c3d03c0d11000080d00c1e80000004003403220f250b41070282c50f403132280c41640d42600ba41021905125240c0902905540101c10025600b13151305600c0585035200341101ca0490f2495100903003483c0108900c40040d40010034041d920759038aa43c48904114180915802800c59481306441e6041c5a000100b400c0301c1038000ba601944142020030240c0c41c00151075900c079006082d4030700f81003c010000c80c24240c1380452610040310105000c40d18100200c002c10000802c02c807054840151001404194050b80c4007441c086640740e000503840400200c0285052038070224010301e4011244145000a090405e0554600e6641d0406000b1820309a40254480c0485002800100d10f1a0b803a4a84a27002d03280c0c0d2100e594000c0b0110301413141d0044200d0292000c0740d01407000b171070003029800080108441810052160141d0080c682c4100c054606001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 241345800 1250 241344550 241344569
    0x90f03041d09032b0e0d03060315090201090b0f040e0c0d0507032d0204090f0b09090a050d1101061502030309010c050a051803031e041404180b04020d120e0103050a06 73
    0x4403240101c244c04600c40401002500e03001c40e044401828014000c2150390741d200058401d06500b0729614010004c001e200c1030350f00c0c00c410900540c1c0c1020700c84040b1501c0b007141503510207119074075110030f00447c2e0251503524a24001e00c58a002000050280da8508210422255990150440c103032000e42042c0308040394924408036003030250b80f03aa641c04404a0f44094030b8280d4549500c1c0480d41c50303002c4010000e03941e031000192482d040c925642c201040100410707802e030581e03c500d82c50312079110300a010b03c956107030034803036002081d0030610003080f03036a940c2d001080e240d14019407039500803500700f011540303032201041c00c86024034203596401c000ca686d40740c20111f000c0100030314000c108040e030354503220a104449106422441c1510074901700110079403610329003402d00c041c031844c20321381c0c80c8180d0a060440c0c200340d4803080340c0e50049400240c0182c00b0346541c00400d66802c01e251001d00503000e844054851260400805114070300d00703a07170800c29590f48070140000c9610074001e001e000b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 241347050 1250 241345800 241345837
    0x4080d0e1f080405160f1811250609030e011206060e150f0c030703022a0409141b0a0e0f010b130902130501081503070608090f03041d0903 61
    0x10755100d000500d52092103001110081001c5080e02c0620308160f0f8000450451401002d000e807061900070580344001c0d04034244000005802901d059026040600848840c104a550720305441c907c0d103c1031003900410b0801c00b40b65a13007801080000404651070110b0301c010410110741d9914411681121880c0e078602100d004440100310034400c1010300d441c450481031102c00030700311080300100b240d021a80d008541e2140c03d403601a0800040340304901da16601c0d030301c030b00c01c002d60030001ca6807121104075000260030400e440c0000c80230482282d80c448a111304d1046080701d030036640281d151940e08841a2040c0ea95809500b10300c00000c07104c415080341428010054210b1a001802014102c9115511003e44610010040303030041d022801020154403400c00c070b80d5800a20107500410100d40030602d440101022a6a03900d4520805041210341400114040d50501030102140045c1083d030b651240c0d2402a1500306001a1002688114040204400202c0002284c1740c00c1c50501003501d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 241348300 1250 241347050 241347109
    0x70209061e040c0903020909070501020610080303010909140d0c060e010e030711180c0a09050405160c03120906020d0b01020303190b0607061d2512060f0204080d0e 72
    0x1070a400440001840024113002c0010796032802018821a00134004140700c9140078002454080b001c1c114201440400030f043c4000e8002004480c1520a1080c3c0030601c4510741c904400c06000b81071510103d8050711210040d0290b100c0c4468503151300409080c00314a0011054030308032109200200500d5001f0040131000466010355007285010062580341d44a40c4e4015945407800112140f011458001076001c0440f5000000500540f0003511b04100d9803030401d04004100f600340c50100207104000c80d0302c0042501c1180002d010105614043c042e4040c0761803c0c40c040d40180d0360b07210009041c680010f0241d4030010940c0e02c06d240380340507404c41c0d09050150b28001c0c036a041003182c10101c20880782002c6403460080b020742844204210344000d0480300d1060600b200313004200e142d210700100600140340341402c1201074410310032014070400303041d29141c00142851040040e8160000c5000030300f140740840c59451211880e00c7d401c10b0031079180204100746035000e4104c0d414158801c03001c01c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 241349550 1250 241348300 241348309
    0x60a17030a081512030c0106060f090308030a0e07080d020f0c01140d180f060c0e130c0c050f01050105090705030f130516090e07080a05030a030e0a0f0602070209061e 73
    0x9400414240c9240002d035a00b90104e80d0304800200d141c04690700014803040c020000f4458a40102100d280c007454010011400601d00d44040c0701c0a0250040400865100012544031240000b5440211034485544815442d21040b54580041c054003071001d180c00c181501090f600030001e41691400001405401d081655400000c0e403c000582d896030741800c10340710074034400c0016000395955400c1480d40d150200944299106030000c1041c0c281c9100d2417511000b12507803096401e503c0c08900d14102550840d040303101820003409a1258611401d007070300041d807045044e14416100c0107425aa06802074034244001e1794412015511400064203880d480c0300c46000c0d8500c642d00381c90b139110503990302c0750840320580c104040c03032a65030303035040d642c1441040064001c002c04005009121001d8035403e450340030b410200c00034540c480d85e0341949c0c2e00043c03050426281d4440d000740600f4515062040080d004608224040d1041201050280ca004c0e40181c80348400c1d40500c5280059810500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 241350800 1250 241349550 241349567
    0x1106060d02040e1212011404181e0b0115020f03040b1e160c15030c0804230604060506030d140a0e120f01021c0b0d03050c1f05060a17030a 61
    0x840c4c020303084003105940c0603a00408484054840702502541440341d002c1c0728001c01d03610148110700d440107500c410740030000c200e1000e6030450701d40b081341c0c20f400c94010018000c1040040260a100c0c0000c142d01c200a07640002c01190f43d400c403452151410b2003107941b44600d0240205800d001d01800c00105594a40340c00500c0701100041e0a08185080c0c440010003031540c101c034228030302c040500c030700c00703111000750904020347c41c0a20042c20310f908042c28505d009000600303c02c20304a891040d4001e40140700d4840e031003150407600e01b03150504040300100310541d2110b01c02c4c080c0400855105100d030f0000903c034407102001d06d140c01444007098481e41402c0042d150400c2a80940303070070000c000c1c4011202040d0003030000d83d56085030701656107002d0700c2e40c1d14015a24501400d525050301e071444000c100301d915080c1035a0b10340f1031003006890319820340600c0710b081c2a11110600d02c00501d42045000380001c1e13501e030400c142c540709101c03481c541400c00803003164400e00c45003110070310a4805 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 241352050 1250 241350800 241350821
    0xb0a0506071205091507050607090b09060702181806070f090b0a0309080409090b01091503020112020d0f060e0f010b0a1202041a04171b040b0609040c020d1106060d0204 74
    0x2d00e0042c441d400708112185d80c80c100c110741c120200c0e040c07050010901c41e050344600310745002032885040484e0300020b40030b86d2183c9030084401203800011500c94820342150154924060009403804811a81ca410450065914540503502c0851201c500039840205061100e403120101c06092400e159550380100b41d01c3c030105070301ca800700400325055800174400380001240c086601242410f181c04d039220181e010400d0745107440c4401c04031a0300441344038140c90f42441c0418079140f5640c0710601a0044242d4801c015140c52019524080c107644040200c1d00c03000303261585907039404069511a5803d00ca00e41c0b141104010f41ca140da80300e16503840c0030070780d102c01c014185621016903080e58000300c10004e0b5070b0600090306219081280c20100b4014001c04010007889074440c1c02880c851081d520303a140903e89404400384542e440400b51100000054020000180c940c407000303580c0d00010003180d0108594900f000000d401c0031440d28424040a49011840e900c5542888000d1140820 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 241353300 1250 241352050 241352057
    0x4021009060e1e18010f120503191205011d060d0b010e06010c080c25060e01180503010203071d0a06020606151c0b1801031e081312060b0a05060712 65
    0x480c0002592449072540800801c2030704d5161075810b1105805a0901c2500304120003401e6001e4a000500008200c600000c2c40010303110740281c0c03001c001d42c1c4003113102282e80c5042c0e09000c0041400540c42c40384804004600d180c0c10156101e000610810490305480580b000d940040140056003a00e240309805c50418900072211600703503200c150007038002c03141c3d40c182078009020101b420800b0025654001c9480300c00488417500d090005041040b441801ca4180b01d01c1a803490080c410280d00300c0c00501c0050001c3d5928074200e07000514400884203043d41a019546040360b0f9810b0200410042e1120f9030024030f0162601020812010f801e4415546102c0d070030022080d40c1307152881e000020075a400c0c4081240c001c200200132403480c6442d1007103105502000100080755400422080c0c1d20000e0140d28079078412400d08510346d11605c40e00402c1d00403005800a64462091200344031280544020420000030400700a914409031150a91001d01802040080b072450340c00c1c82e90800c403504 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 241354550 1250 241353300 241353349
    0x1060f031a0405030c0f0307060605030c0604030b09160602030c012d050c0904060f06081f140a05220b0f030a1202010e060403050301030311150a0c09091404021009060e 74
    0x1110f01d002c6c0f103900c05401c0c607080483d2010400040780502c00240c40224040d113800c4001802041c40c1d8040c0740320180a100030b203004903000240034403065844000060380e0103140354959001075529406a941804076600e000c21452807240151040c41070b00d4000d0306680305480b040c0e581031003d468007906802101c20208007119403683d5610640006091000614003401d1034414050301002e0004e10140c0c0c240c0361084401003201540501d03509464011031a200c3c0d605032000880e4080c10940c00c225040741d8200c4030314004034003010102000c100e00e80000d029140c4e04006024440001e10504c80d00341e80a1100c100018001d9030350008031088074400007507a00c151034040b500e000401e4030140c2c08a40c00000501c1415800049a11080011030081103180121009107051500042861902907500c489a9070110b00c6400800000c002d01d0509000418881600b540011810748040b03116002c160560010f080c00350714000221101c503251801601d10240610061000401c0d80c0700d42d0f0301081c0d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 241355800 1250 241354550 241354567
    0x10509131e0c0207151b03020c040905070f090e0709020a0c0c0906060807080f010e060301060e090609070e090613021c03110106050102072607080f0c0301060f031a040503 75
    0x2203a0201d001000800104850725001e01c040c1c1000d0b01d9802001c0d1602040d084003040b41d801003070340304141244000c0c1d800c40c030040342412410414a01015640942410441400d1100000303803c006d070b0380d84840700010700350b95100c0042100c40007410550a40c1000798104009a00307980903050811075030410750743d0003442d9074800345420125001444440e0b03640301c1c00d0046a070302840c543e50200c000d0618680300e0030b2221f11007150b480140302d00341181c1e07101030008025032020b41000000b0010000c0304040d82c20300802c1c180e1520411540540c07217220b000c070f00113200000e519503140102c3c6600701a000d00c0d2103415029004d812262410fa0700102c0100c030714401d10340c8030056902c00074001d1b46c80748000070352190b2540c252005a48544d0446d0b01542080c1305441741e07001400c80302c039540c0035106500341048440e00e061220355440702805010b03440c000e10400d000840c590510080440003008042d07111041031007003080a020207400c40d030740c4035141034076502001c2e0031603041401001220700300b082c1c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 241357050 1250 241355800 241355831
    0x1020c0f01091401020a0512030a050c03060d02090a020c010c08061504031e020a05060304032c0303090922030503041208070e010518092a0f03040b07030902032d060601050913 77
    0x101c102c8d40f0103040000411030300b5802403003aaa0024240440791317103141000e900080710412a0740300640310b0600c64011170a040c1c01c50741101d1078081600001e100d145c0d5003440c0689001d2048400380d004480d284101c0302c24500300c4040780c06981d032120380312254075407181e01ca04d90603016040490704400f1494012443d5600c0d10302451040d03200e60b4400c10b81c20002112004800d45000e0803950200301d00151562956010041d5994250706849240c0a40d0f1a0401c0b041c41801000309000b50342d60340c40a07842815404001180300e00c3c010b41c80000d8000b04074801f19000c0001710b603404001002054509644e611079401001d0356803101041140318a1010300044000400b0354003003462120340d02d41d000340c409003400c1c1d16608212090605042c0303400c000507194940300041000b840c2c08111400101064000d9005a000c1d036006412690303814020104400303101c16081c5800354450a40b45403c8042d90000f035040c0c0b107100f0607599a0b080c400d81401780503852a45880310f8030f40d191100c000c0c1040040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 241358300 1250 241357050 241357063
    0x3090e07021207080d0b190603020a050702040903050406110a030903080313050f0601090b0910060e18010311180907031b0909060b0907050403031d041e06030201020c0f01091401020a05 81
    0x400c61305070744407280d0646104a80d001105140100354002d010f40303125030b000c4400c00880300c007410050ba5868030717880200c400344240100258010301d00121402810340c000081c100396251502c0c2c0c4160305840500442d9164003000c001400125010f10030b0002400103009950030492400e00c948510b110f80d0707502c030b0800480314031891599100500401c04208940505031048030103a030b0401541c105100100c40341240d9004400038006403000c03016807615650f014441c07021001d07940c00e0255171030b4a030000800001100703a610a504401c05401c007483e6102e01c06014508500041803030318555550004400d0508070380401c440c00c94a00003840207628043c076a81c030f07031040c900043c03100d90000802c202030002504031410410140801d00000fa002481e8100041a8603419a0650040c6000501802c40c0880d52001d072403144902011003015600010b00340c0e80b00341c0a94902c83d00328000d00a00c809806a6140020000c2a00300041045000107048125040c03060341c4103813001c2e44400b440c105 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 241359550 1250 241358300 241358303
    0x1b06040b06041505060a0e10120f0e0a0201030c110d0206011a03010b030c1e07030e030d02010c1409030f03030702160e061008060a0e0c090301061203090e07021207 72
    0x40104081004001089540a90290040710708214480b000c00303101a00c1c6100d0b014050080000040c010300c114040c018805410200a00c0801802d07034034800200180180c051000e459814120311207008041030081c0d05500c15010001c10031500c20341c0046000e0801450030905001708003815072403e1030103110454480906800408040d4034145440d80003075484240c0824658080c00107200ca40302c5041126001440c80c024640c82d2980d8800c01020718890301e0304e07065440c900080c071800300b540024101e891107808500f80e90400340c22030410b03802d0b03604854031440040c8038250301c0c00da80480c250240c0a89480a0b045a0f950b169240019145038070039034800740507034455522405040d0101c080c0d170001c1c1c40c1d502241d0010b4109600411001010820138605010b000380004140da01c0f030000701002454669a141202c0c1021361160704150300090f40d0900950034000c2c0400c0200400d0101502d655140d030719410309602e40648a041004082c1041003180500d01e52500c1d4100041d014040c3c49 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 241360800 1250 241359550 241359553
    0xc0909020406020307030e03010b031f0e01020d0f0b0901030b061507060905060f1b04030b041a071d030118081303060f0209041d060703020c01060306020c070f0b03090a080f1b 77
    0x5c401d503050142402c010301200e00d01c1f0303070b04000d074003089500e021440075169040359050945207920728000700040c0c10740380c000340c0340c542c4046038442c130001c015040071040c082d080b202000340ca0000400d010540d03900340009080d070101000400c541d400c1c11030b00e0315024868201240c0c181045030751440180d40030b5810690702c5134007400c103000e40d031511000d4250700304034111034040b40d2100e0011182c0c5140103611000e09150078034000101401076080c030640300700448280309065031600103009894046024a0400d0050048582200c03a050501c15800c0c00b4010354011824100255190003c42e03200d404441e15640c01d62000100144441c014510041c280482c0076032034840900902c01103c50b403c17502290960241d00843e0b0602e408078525812203428a0050b90b80e40c4400407c9000d41107039031004250b1840000c9072814608045115010740f00e01280100c1c2017580d80101100310300080d6140030035a000203e0890000f02e120005040c00081c11003483d0800a071110810f428030600403070303003036607 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 241362050 1250 241360800 241360807
    0x9020901090503070303090e18010e0a030201110a140705030c030a0503040b06180613060503070306060801060b0304080412021c05030306150c0c01030e0a0209010b13080d05070201030c09090204060203 88
    0x65603004807120340540070650050149a2541c6c074002c1113600d03103214149003a41818040751910030a122102c0010b03610030002d020714260030303103d02e40d105e4642c001540154600b40c0300031007041050045494404060f5503903507620003504030300c24540c2e0004108a41506c410004001c0545061000e000a1141a12160344910f030506207940b4918004180e00e20480c0c03a0900380c905007100d8a100d54001c030f000d5507070640c00908a00c000303006002c0c82d048070383d151007808000030800815070401800d480202d1b00030b200c2556103d500581031701085d20014001c0d40203000901c451f8002e0651000d42d50b0004141ca40c3e01d194070030945151010140701511030f43c100204120260421038503082d010803500030560700d0034286040c11504c0311b240c82042c504040c1c842d60500c2008a08004843d04c0a80003014030b08296900c08114006606c94124071518040442000407030f0315010a00700fa0f200000c1d00c5030741c50404140d00440081480e000c19906000c18208007088400592000c1d00242900d40c004555 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 241363300 1250 241362050 241362067
    0xc030314130f051e010c0912260405061c15050913051507050c07060c020a0303050c0a0c14040b0a051e0d050f0c0a05010f020606130204030c0902 64
    0x15120420308120003514100c06005246568080c2080041d4100e00410305000c190715009003007001200c1d042e181400c0c010f910640204c01940704850121060b210350201c90340c0c800c0d20603046841f403100504961091410413083c602500c108032048980161154a001c2e210000541030343c0000620312400717011f00420280a4001c1e00c6030101480c0b0907020038020030304c0c0c1800901c900c0c01c020080041f4030262010301c0c0400101300a281500841818001c02c00e1414641c000c00c00d800407103130b40c0218814003800041c0c40e401984002000740d0054041a500e6095440a540907402501c103001c1610603c03100c0408610114000c0e0040c1004080d40742d051416142044141c0b00501140303442010541320400141e59010011440b815022088420015003032002890601903144080c0080c01510021650700d4404510f610310b038202241c0842026413a04011221100c0400180d03002d07901540c0420b0003032400130b07030803041c5408501015103841d80301e9a0f4084ca0140c3c41d40f2042c0d019802003070200 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 241364550 1250 241363300 241363307
    0x108010803090f150705030301030605041217060402161e0b0604060b090f0301060e010e0702060703093f0806040606110303010e060a03080313060c0f14280c03 70
    0x500400e0814001c5050102030000208480b42060340301e81315403443e004c1030b02001252000d44075161303040010340342c407580c0d20b081c241e014220454046075101c440e441011219402100020744018402070060069950501448000d6101d01100e019440541c508800001d0304a081c40d011951340319841015100b480c5003501c41000d02400c1c41d407145003051414011044d91009442c43c03190201e27084400c000c50344010900500658004013420301d810000480c403408034040041c05101180e0845650360f0b249082242241c0001f4401000120010141c980040926520b6940503240320410014044400c00c004040c440d8200004041040d00c02000b9103490103115910081a590501d001c22001800e8119220303c01400b81d5040410420007145403030301c8a501c500048c50340085442c0d40c0c3d0520049001010500d410200e84250402c03003400c900b10f109820960088100d81c0b42e00040c800c403c001061542c0126404681c00d80d96040c0444651401c60000c4994030070688400703031440700c40d05009 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 241365800 1250 241364550 241364567
    0x1e02040e0705370207090b060d0906140412020d02011808090f1002010902030f0a05070e0c070602040b0405040b0414010510050c07060e1212090d08070b0705042d050f180408070201 79
    0xc0c8a014a042d01f41206622803004442c050350783c00c00300240a20380b610b000c0000703004044240071900d481c90100010814014a1200460566022158000c0c0310681c00c80c261500f0f0018008a407410206910004d04424060103200304020140d203420a0060003140390301d4141c42e440030050391245040c8065003020b00490100c0c03102400904943d40064840303035610105880342005c91404840080d8003603449400341d92101d50f00c000255070f01c5980e039441d0380344d540103405440d01c0ba900d0031800000600d4140b003044000000c0301665462030b882d001c1004005041d0040314030a009041021010f034403030900c0071001900c00d50311680101c90703010081c0081c88518540c070002550051b180070519400e0507044d0b8030266000c81c0e40190309016031030542c42c036029012004060011040a200e40140c0003409070081e40c5500d180b88134120b00c982200001d81c2b020701001403500328103c1042c030240c01c0403030304803001c903801030203003490014080f00380c4441c150300f12015a1400b80c003059000856a214850 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 241366906 1106 241365800 241365809
    0x1140a03112e09140103051905060301090b090a1a0f1605071406011715040f08040b070b0105030c040623031f1e02040e0705370207 58
    0x180c502c070424040c816072120130102c0921315510a20a1038443c1d84185900d01124403601c548800070940540804d816540307540d000804141c0121100703010308507240050030a0344050620585204812508e103010329400418011100310302d00031a40c0154103100c1c0101e468640c0c140a46082c403030020010035043c0d0444c40307152000d00100faa14100c0e440d98056a8600302c50880c0941c64101c1d0b40500450900d020000c01c0200c0d203e01c074100401c0d032242802c145015142c0c104980c030b6800c4548101c2e01100d680006005d40c2c20207104104400134241e60905c14141025022400c01c01c03000300740e80444921451215140c0e808003c1d482000900c00c0050014a08a55194000e4103105a003000441204140c1032210003440c42201c0c115143c1c0451039a583d03c0380c60f030880726a480f0b8142035880114200d00030b000300b5250003816030b0107514403916040700001c1042c00b0703040640701d030f02 = true := by decide +kernel

theorem cover : BRFrame.Cov 241187050 241366906 := by
  have h0 := BRFrame.cov_init 241187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 241187050 ≤ n) (h2 : n < 241366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
