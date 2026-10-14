-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1323
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:22:22.271746+00:00
-- url     : https://prove2.me/submissions/1e1814c6-cdd4-4c65-999c-ea9afab809d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 237769784 ≤ n < 237949640 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 237771034 1250 237769784 237769787
    0x301060b09030105062b0c03051b09061e0d020604080303010b0405010906020105070f0c060b0a080102220f0b071b08011401140a05150c010e10050c04120803100302190501 75
    0x140c0e900300400b26484111030b85001b1901100030364910701102c041544e64142d10810840890b0b620045400405603410014040c0880c550180403110b058410040540082c0031450000001800e00d0429590105110841c50501c0080040c058003641c0c01501444000b03144401040218083e0074084103498460345032500140c00395002e40c201c00203690400003000071b0158003600c0d44144040620302465422602d0034518010400908015044406080003065511054000300302c03110110308200c10404d0520141c007800308075405802c55034040c09200300820040030001e4840f5030b004800316080045500c4102d0101c02d0158000005071f5101c0300c0b41c80181464075021401480d003101c081495043d10400030f500c50905000701e0784a1280f00400da0f0044c0f540c24140c80d50b070f07500b0030001c02c0404840f9200b9961185940b41c00d003501402d12000072000041001624100d542e241c80702c4070701c4a650358a001d0140c000801000d405404003400101581e80c031451103070050308481061202e1410b1100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 237772284 1250 237771034 237771041
    0x103060b150403080d090303020f0a0306030311030702010917030909040506070210020f091207050d0605061003200a1e05030f0702011806110409020c100f051312020a020301060b090301 81
    0x20390300907103005102c01c00109811000300c400d1241010400900842c50345010350090042c50b1001107000c3c0e0100703e00b00c1c0b983d0154850380580303010f915416440b504503082c1aa80b841604402070000f40c0c100c404204d051000580d5444e02c0300c2201c152410708880d080464407913281260150303000e6121000744071000c0d030144005240c0710341c1c0c10003d500e01100c04048040c81d120300851207000d0080320100000c2003809112a1002c0c11004200c01c121602c1414a600580019242d031440384030b85110f2002040d0203071240c0c405220204c0c0d001c1403440312842244043c3d400586085052044100400d011410403589200100c031440d00c0b0316480307050040205040500003400c0c2c9095a14019103541004034156800c111541e1154011403c6240c2400020b23032406143d211503542c600100781c0d808494800300d8108940721071f2100c10001a43c0d20b410840a581d41a03071a000c803200d040b450341010420841181400001600441e050984541e0101c0d08482c2c00b40c1c0045ca45400201d1681c442c1d181c00c1c003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 237773534 1250 237772284 237772309
    0xb0612011e050f041a07020f01060f17010506030613110d030503150301060b0d0c031d0304181802060904091502031b0f0301141507111516150b06030103060b 69
    0x503d000140c60250740e002c25940c0003008404012281c2000100340d50302c03c000248d007910445000b400000d594010620410403140108036000344a00c180d01d201c0581440780c030b0f0bc600d200034010711300c40d240e20301c01489480300780340156400f520001c1164000c0d05c610745081c80707940c402d45d1410307a41c1c40d1507150800d03111219180188039906208080269081000541310b00c2980c1003030001c4c80907260b2405400810008504a400301c2c0061140b20069070044090f00445803d00301d261030f1a541610350400310b40c1008900c0041c3d8a100303040c00c016003042005022111405440059807507002c1d01e4410319032000424844120b0380010401c05003151664a1644403500c40c2c010710f0400a42c007404601c5400b050049500c100d042d217a0841656a40340c810f003400340100c1380c070350b6030715121400d15620036810b500e00306001c0c56000141429401d0500202d829600e180c4400e83c101040035981c03408049081801061f81c240c45629030149039075120000d40c002c622484002450070001d2041c80003642030b10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 237774784 1250 237773534 237773551
    0x170d09090212070e040b0d08040f0803031306020a21051015020c040c020114010902040f0f05010e0d02031006080102070501060b03070c0605090a080a05090306010803160b0612011e05 80
    0x62000460a002c1079221a030040281e0500003003442c84140420003c1940514042d131142c1d02140d03000c203014003440100141c0c1c0c00c4024403003205484a007950f41e244016600c171750038280c1c416601030208a1582c00703088618546c1c64440e0708014540321100b5168105201c0380402613448082c001400a1b45440c48000d190f110a413040e54040d070702d008dd440d5408401c8590056403a1403150018501c00e50106543c8031000386c141c03a5550319041c80314003d41150003010700e061004d50020030640040140c540c100e40059441c0000d2464510501c2408070410408a030144115000d00c291000e49000341006030004000040c1c84003614140542540c2c001d80c0441207402080040c007814070340c40400116226000200442e12740c9030600068130b01207400038054075110002c124001025817103c02414200800c908445907a600e44410316283d206000c00303609040c00c4040341e800007404c9610344a43c0701d0f9000740b4142a004c41d0a007a1420b5900140c01e1422600014a0203052040c1e244a00758100004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 237776034 1250 237774784 237774787
    0x15020a060c083c040f0c030305031f14062b1e060509010e101d011d010b1803070b0c0601060906090807210516061101090b01060309020109170d090902 66
    0x16800043e6004078452512140d2810043c0003c1c00e22140200040d9545c2d44a810041d5081d9a0b0900900c03c1c2c1050b14648110b01c0e1a0b040406043d10007022070f41541d00100c411800e00c2100b40800c001303030f4042d4401c000c0e0124240600c041061515000c031618042802e4003003002007413101c14540c4003400c5154500d20a203000406c0c0420b4450700c0b00355064890214180425482d40c1c0c0140b440c2103070b40c3d440603a802c00744214492003031420400342030403a004078000311031403807100345102e192420074003e00142c60802e0040f580d0b02c03541240206e042810190030350359440c0d1111890001d661044051915903070004004005403a40400520000d241510784010010b041400d995210f82c100e104803e1080d01c0320704c5980c0c0c0101c038101c2150860341c2c0041203601c50f02d800103030900c20960a2242c01e011890000d66040d0300354060180e450345980c44602c0e06400e80c2800000c0e8003d20b0038034001c1c1e0400c51603040124034882d00c81d02400040e280300b40180043c1003581402000c1102680081e61170500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 237777284 1250 237776034 237776101
    0x51e0303010e0105060f0c070b0d0b09090c101107090207050d080106020a11151903050106030905031b0307080307050405030709090201020c1003020f04120605061915020a060c08 78
    0x401002c00d90641d40101c880315074801032240428143e000d088810040d0b070040701030000e01101100000d0800079003504043c00100450010402c1022084540c404160480150448145007823942d9120050707148c106010a200c80c0e041d41841c01407107400c0000001d900241c0710043c0300007081080748942452405444642c10310790b0094880c613804000030168508000401d0740b9a0b1b8601840c1c1c4131302c4100002075114001110812a20b0401b82c0010001c20f280070001301d007881c801d000b030100072174018005500d04005e401c0048480008100341c071a00340810720581c800120044019801501c0aa4036641c60300e00b04005c160070a8a103a01282c070f851718101e41600141d801007080d07840e142003101c50054480f907401081d40a48505020790800c42d5000501089940d4884511b80019008100410036a990b0b8070500c004800000c0c106090890078200400c020a4424a841c094860790310595000520f25910035050b1002e0203604000300d02e458007006810843c2c00d40320302d25a00b6402d141c251501 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 237778534 1250 237777284 237777299
    0x30f05060411040e0c27011403130b100302041e1b1706030708071706060f0a03022205010303030c020c090c040501110304080a0c031709010e04090f0c03051e030301 72
    0xc50303440b84410300c1d1800400984201013040070749502c030a651601040d0810031080030038810010100c1b440c0818003c54582081c1290101078074820074440e0081c038400221525040c0c078518005003001101d11000001100684490207410051040406c982403402c01e601404001d64008126240c1a98006800404166400045a0720695090201c0956a214500403901f0034416400c40f5403180b00c1c544000812035010307001c07400ea540400307003a520903031280c804008070807200313a0910b90f00894030303403080c0702510300034061602a0b841140860310205a1035581c4040d210260b04c103601003541c0b5410500c1541d0144100402c820b02101d1450451500c0c4500e21924000c07400f900d41001a040481104040c081003142c002e481c0020443d444c1040502e4020006000e500040381c540c1e4040706003814416412068a03080e0105850703030007140c8290010f0000608a011007590250781d801110004101c440d031001c4e000e1070140015181c405c1c144544c1641002c0215606100759004100410070b0780c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 237779784 1250 237778534 237778537
    0xb0a050c070e0f13021c120210091106160b1303030b0402130e070e0607060c030605030703331a03060c0c0a1202071a070303060f0602030304030e150a030f05060411 72
    0x1e2000755000c03200340030310300200d201c200240302d00401000a104086c070502c118004042076030000c0341c2c02c540c0d1002c0341d44207110030380b03505080007003104800c007905460394035105c00548641c0c0701510b50342658601c1522603c103414015a030381411144c1e0000004241a03043c0540f800703100098405614090080c0801a054441031288040c480303420300114013514070610340d80190351802448107440705000e090003001130108121140109246c640300040302c2c1000300d500b20840e50006040c007104610000a1146164607419402c0780c000e90268032182ca81c1c5921400042c6015500e40d814503c465200b031600d0020082c11825408506001104504400180420710580d00c0311700740342003401542041e440c103100b40d00142810400116030f11061030102d0050001c1901035038051101c6a6502d250b080c1c0c02d0603900507030006030000c00008000c280100240045030708040c0111924480248000c1c525802940e40140041e07210340c0403407000d0006006080c4c00c200c040758104541d401c9441d0140ca41d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 237781034 1250 237779784 237779791
    0x50306090a0c02010b130209030f0604021302030c160503030403121505210a0f11010807050a0503091614150903151012030804120207060e0d0206040b0a050c070e0f 72
    0x1410340725000b42d01c41600c01e4012080c01071001e0407040800c91203600b4840070b900106c2c40140a0b01c43c1c95442d02107000300041c1140a0754019080f20801030715205164043e40c401004045580e1040003015104002c0c0c0d416041c4560240000d11748030704140c98010300001904018400590400312062012000c02d54030b481210400c41e44104c0c1c0c1c900200e51081010b0405030b100d140380c000e04a2440502c9401d256101509210700c031038000d9100c1c08001544e545c01c040ea1400002802400340111303030b0380210000d640044040e021900007205080c4201c0c1c8000d0b0340d1700f194441c0d02c18001b06510038244520f40d103440d0f85c100c24559007000f4400010980c0c2d0f10440e0000c00c002100311000c10034403101c80345950040c0c03500481000201e0801e00b4040d082d03920a4804950700072103c5407031240f091010a0050a8507120341da451040c200c04020014400030b084016070388940d0402000403071b05842d00090144810790b803142515600903041207810244150301c5a0b1603d13030000301708101c1c620340c4200030340d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 237782284 1250 237781034 237781051
    0xe030901030f1509021b0307261605030a0e010c0206030c09180c180f01090b220f050f121005041109190b040b0a05150c030304120f05030609 62
    0x1d00100d00000b841c050b1003c0c18001c2c4140e010340402140310f004d590002d25810003c41110310644600602843e52442020350142c50507444402d40101e0409940000d0030307510f1503000d10380c100041c01500202c8000c841030b0841e02c0341d000145c3d44003280d400c50300c203045942c02400c042d601e070156074011840d2444000d004000c101c0740010045001c1d40d840c1e01c02046d00c5454503848101e0304e898162501190700c46030700320b200064603100600c4a881d0913100c1d404c00a81c180d403403060552601d20705c50415001364617072961100380000b022109036400e00b61000100041e60103030000c1440c050a0000300c030b01c0d048046000b101107000a10003d8030019441c2410a0540d030b0004065903a420002c10000621024551115002c1e050100e41500b0040652840e98031602c100030891200d020070044a0852502940042d40b0300c104001c10711780900004c441e01d84400c4001d2406d080440c9050450784203c8040303508400d6003501580403984481900d2000846050551844c20648002100340100405204 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 237783534 1250 237782284 237782291
    0x5010806010e030a110402040b040605090307050a0b0d09020103112d04260a020405010b030403110c01091e030b090d03060e010501080a0218090711060903030c03061009082e0e03090103 81
    0x1050307071b242c650486004010140701030741c03a80d03110b079002003070350b4000b41c1e8844c840d11920b03101191510306050b8010444079641c09052074034031600b40c2c1401801417000306078145651040c442d440c0c2d41340da0f0010411281c4070184188004072000403202c02d1841a204030f45413400520040c0710400f150109100e24a0440c03082020104420810510f02602c0c200025001408c0c100001a59000c20300618000e620a840700618000c00014450741d504044a4030342c00200c0541c010400d80e18090f0340d00d41505c140200b000d240948179106c10101000a40e490701d0141e001001904100303501d1b1092101400f8120300c100d04951410000030b108100240600808941c009902c501d1038a071180001003c0001400769681403803d4400900355030540d14103405a4084d03900040d60b111b03000300440c2c1c86400110005411500c03080180320329000e000303615006002c42781c8030205084008200261184030b494404003881c1e111a1310850401a0f541410296581403c403001503180c40401a104184002e2a000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 237784784 1250 237783534 237783563
    0x1200307140705060d0e19051c03020f070c03051006050a0302011101020d0c02010606110a05060a0b12010e010f0c1107090e070e10050a0f0b030402040b130c080105010806010e030a 79
    0x1141000350641c00075512002c0054a810350b0070f030fa6004150851901001c6da1201c2001c0707e141001c0c110100c0b002802d0390005006c3d021964100351350079001115600c2d00505050b4840d20280781a4050001510001e03451a820810810100200340b8850f8048500740021450040800c18620007070200906000d00d11400c1a102e00003541640d0516848403401d22801c0d2900740080e009042c18020030000586510030140600350000300c003010143d020004092070ba43d0181c03c0b200500b020321669034001041d484050750010240500003d04401000008502440f0030104c0c00312040c1031100d409100c800c910080081c90085107410446100030340200b110070f102411a41804500d800481d0800e00c03001c140300c03c4400d01105917050324400d540245085489007440344e8201310f1445169240c10381000054010305054000031102e800141000c1032030341070046031009450120b071051000441d2200100859a0321809072a0820800e00707011074602c0d0741c040826140c800003400a0043c24158406 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 237786034 1250 237784784 237784823
    0x120c060d1e0b1201200a0509060a090f09060302010206040f080d18260403030e0d0804060c02041505030a1424090106090b0a06080402040f0f0b01200307 67
    0x140c0e1a4410005084101188039900e24000b0a42480c90300d0262294a15100d07411405200749803000345801030340500002c4542079020940c0c04a00400b041007000c0c081c100041d210302001c1c2000703482d9034079100001d90804109100045c980d6114100c628242202080580d0b0007282803074025401c1700a51351814080e05242141e03100e035480303245019182c1140085000b42c10310030b80ca0014444d108508108800202200d07001c4030031a40b204060b02d080008200182c007911442200941c00360281c1090451500e0b52216500260720050124a00740140070451034980710300c80e9807106051721000d6060500700440d80e12909072741c0080269141c8001c40000c0c0320708000d40c01e00840716503611060340c00740c265855210742d0140cad10301416609046001c100d80da000e010320585c06074054102e840700f503d0300358105c5003568090f0090741c0299481200d04503a14036801014400c8000390000314130400b003680010b0410100440c03070340006200100c00318840001100b25085103401038950400404003a00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 237787284 1250 237786034 237786041
    0x1915080709060504181b050a0e0321030406060315050415141512010f0e0609060103053d0b010e0d020a0302040b01140a02010f180309090c0c050102040308090f120c060d 74
    0x1b410130301030031002c00201c4640da0010050904004907074904440f202035105050f41d40c481803000d443c203041401000c2100280b100081c50303019008250108000e0750300e0301c451802947d004c000f140000d4456082000340425880c07001c5c0041c10100080100235220700c40c1640d0203c02903d102c00c812242000142d5039910f8501000040c5030080080201d480030925a0b4000c0501e0b4062340001d01444c40000c001b0032000c50158100c1e504400508642c0c0814009904954403114419425482c0050040b146403002c4a20000c051190400040c9045844001400002c0048801071055031a4450100181c4440c4003010440f0343c1902e02040d0203036410010794006018404404c4040800325001e02040c3e41500180c0300140800010404071020703184490340d2070b803543c0001e808203046c0142007000c01c40d60340c46920401714500c5c0107041000b10b590b40b642039038465407060b2550000840c4d00012468214409100d1003400c40d01030140a0704a100309440c2c1d040c85c102c03a4455000400c5030b00101c0c0c01c1c2c0c0c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 237788534 1250 237787284 237787301
    0x705130b040e010f0b160201050d061d060114090a0504020d0b06070b040c150c11040b030a0609060b01111b0112050f0a050604020c100b191508070906050418 69
    0xa03209a140d40e1260850074480c0d40902c695554403541c2c3c80c0004010400c4001c95001180900c450068156244c00544040e404804458180d80d541d841c0060070740440d95040c0482c4026092004250405000041c15444514228203242c80c0404c9015017aa5074038881c10201c85040d24003517201c3e048007c1d248000e100040880e60484030001d100803c00440c5c91010340b04034402d000c20141107444d011120260641c00f60224041000f9400301c0000c103122464010010300002c00c00320340c5410710800700741026805102240c0303442c0c03181500c500304070311030081c00900242880c01501c1d000d0301015880d07030b408412942c0c8010b03684480543c545079205410700f9420008a03001403115082c981032055110a0855108003150300d03001c00b00780030380750500031070b10f030031814600900844c0040584000241a001242d0ba4040d90140c00341c0c820400500e800350042842c4e003040d1722050a406400b4045100040400c070820011000038060150888156810749065941417015414850a250010007050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 237789784 1250 237788534 237788549
    0x50904050a1a01030c1202090c1309061206060806070504180f0204060519080402010e1005070209150907021603151d010c0f0311160206190206010509060603040b070513 74
    0x2064010b080756040100320f04a074032848030b000c42c0c2980c0d654100750310b014814000307601406420120712842881805031600c55403000740c80d4503007a5180c8211013200c2e2035600c01d0030302c0080c1960303003018080c0311700c0b94200500402018203c0f42c5807105004003584201d014802c1c208141205c0000f02070056444030baa042030101d8215680c90701c601c2d010304503412450320f0070b288902c1d0881d1040c03040e100e44003c41c041c03a41a103a801240c1d00031000c1100c7c0356081c0c20160f08101080c0640d001607503d44c290940602c00354201c03d1000b841840900441c03d00090040c02550702c500c4500202c2c60854504904981d040032000c12304c030300302c0c15075134000d06510520055602c200401d504400f07041940b0001403040c45840f4420b41c0f07581c03100c0642c2501d2501ea08404007000a125080d042d0078040c4006070032a2005003464908001c0514410b81901001038034001a4401d40040c0054141118515003000d03040701c000b0300307500d41603071400d03110803000f8031501c2080408260722109900c01d505080151070701 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 237791034 1250 237789784 237789803
    0x6120f15050f0117010c091415040909020901120305090d031b0c0e07180306020d1409010e010c08060f0d15020c151503032203120f0e010203090a050904050a 69
    0x40a1000e01c00303084c0a0340c14103021030740340210148014403400c3e51044450b190015604d1030001d40807019041003da4640094045a40e1025040c0700c100410180c0b529160000e8075403158018004400720503005141d03400700d03020301c80300425008002c0d9000000d0407900a15841040c0c6011a200c00c0da1000b500e03900d1b00c107075440504200d03880700402c0607280403582c6603407940ea401034111542d11021a10b01130303500301c2d0039080c0040b0704940c000304001c101c0d0710f0002c94031081c00c4c40700080da98011500d07003000d40d64500c0f001180140a0056a1501c091841c118003107051001c0040c251220300300380244611a0505050304000c0c10419450b0440684001151600c1201401e076444403c0350b0001450181702000080284520b156060311284e0082c1c011804d1040c00d640c00c0b114082c520b8041342204a46840000001ea900715502d200c200803591030480c8281200b1001d0604c1c0c03041807446041d5081445407003400d4035690592000c5410840d1440c1894541c1d00b810b030704104802c00060b001011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 237792284 1250 237791034 237791041
    0xc0a02060a02062a0f030406020906040b040e010609140402181507020103060503070828021003020c0613021f1b0c0305060109060f09020f1b070501030f06120f1505 72
    0x20040392262046821100c181e0950586020a94130480d02038035548100100b40014600558810007466110b1704c503640052800710350f20300049072600641c1c0814210751000a007800040040a03c050041c442d5040c44845103040112002d00e01602d400d0a0f400390b0380c00316000e0701d40b903244001c6c215a444090007032000c0c100e10784802c0e2600e40c41032106902003414100700207040e0800051440494026502803c0700d001980b07552091a00b0b00c540c0d000e010300781c0c4907031100560740b1403500f4403511005440061307985e15403d410b1810700301c008110385c00307040e22020150056183c0075088801d0030a51412a040d44955040c19541c01080c42641c039040340c00381403110708100c104040581a00d0150046400680c2e0700ca0b640e00c1a00e038940195041080f480c80c0c100410b02181d000340581440f5640c040d814500040140303244d14281c0b08040e0100d40c4009810031255815104656800c01c043da01880702c1824600300c035542288a0314014640d00d10600030b0400d115040040012088031400c0500c101d04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 237793534 1250 237792284 237792287
    0x9060908130b09061209160602030304030e0607020d03030f140f100803030c180f03030a0f09050307050f130204051009050f0604150c050708010f1a0f030703080c0a02060a 75
    0x100032070300c0000c814041100101d40a03544906403401000000c1050f460300495003428105448041c3c0a02c0c864840c3c40303d10214005400040406002180c1c011034481c40c00c0e04008000003a06800a4000c901c00c215040150701c50485201c0c909805040105051008045100060545040204540c48240207114070016020071701e902801540c52034551a44e110402c0c562a0b11050300c1c1004002c0d81000380a100c00d2100c50032420380744005042107000b8003417601190450340940504030000d0145002c201d01260800f030028003a001c10784c001c090702070803d0040380d60000c000cbc54803071140200703044641040701290110343c05400050002200c40c150701c0c0340030b040016140141c0d44100c0c1c42200404590412000b41c80480340f8502c1640000b80c1c070304c40103448594091000307403101d0180050124414509009640c1c07501d81c00440062018124045460f980440d40807091243c1000340c00720881303950000388041520342040b4003a42c1c1d030042408403841c01040d080c00940200300801c0030b01406 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 237794784 1250 237793534 237793537
    0x60207060e01050f0127021810050f0d020f130b04030308071d01030c030f051014060c0c061b010c0302220501091814041103150112021309060908 64
    0x503441204140007144000c403003103007039500c1120051190604003004001d01c940e0104c25250101180c0b00c20103007418484a8001664407021b40d6001280d484130340d461141c00c3c04008040ca2800a1501c00e00704200062020054440d010170011010340208181e84030300c00721411507030096840c5049074541130362981c0c2203080e9005403005402041c03000c00021441c41c000c81e40c500600100d0003c40406c520544010350042652001700c2041540e02d1100079443d812611406005040303d50090081600e0614420f03016030000f05464003801040c41031a08610001071161003406084401079110b070040f2041c0c800b0142d00c00d01c250000e6083c81012000c407a09030b4001c1011b0301440302c0c4160054001000c41e0131001c0c05120301ea00294852204009549000c0340c80d5030b50b0300c1c00000100307030070200c10729140514409880964000b400707241125a10324003001003103402c0034822400e04840d80b50209442d880850114080e028001d03804e42c0b40988102e66104001051740b0080405c03d800807400c040c00207 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 237796034 1250 237794784 237794797
    0x403090602060718030f030516061a060c030909090f030d0b040c0f020a030e1c0503120f0403020c090c0d0c03050709050d0f1401020405060403060203100f1d0c04120602 74
    0x1d401030340040740e20f0511030716a10700e881c001508201c82c20b524554034903d8561030140107508110060003141880341308001d9007507a150107514049503900580d0130030a449a42900303401e200f09010040c03181c0701d1401206031007030312a0407151440b8a5880001c81070410f1380300c840640d00c5000024007001d0300301140d8400c1c0c1c401001520104008100c2d841b00b500c03110580c410304805a403200c2040c0002038800d008508041c076000c0d140d5001d002400c0040080101c10190450f541e03080800ea814401030070502140d80001c51600d20720a50606450194581c2076520305035003d0402034000449401125080b40c14440c4031141c2042800000d420040007400181d80d100006645001c000419180400800c0c561941011020080307007260b43d2444910184410344061554080c0800155a515100500000c500406000da940d10b00502e0225440380c007500002041c10300c402c802e220068905000b003804e012440c0790b81c2c405440b1290849954069039004203803001120742c00310100200c94001d080c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 237797284 1250 237796034 237796037
    0x30f030b090408031609082e0203040b0a020a0302070b0112020a060816051305040501120c050306130f050106030506070c0b0901022b0f020703030b0f01030908180a080604030906 78
    0x200c801900200700404509450150a0300381c1131001c102d00c440c0c0c031482e41d1050141d904090180310303540d4a200d800d00d0101d541d0b00b1400c3c03602c43e80505904920b0f007030b844560303015060214950700d0700e9600d0114a400180c460764115501040070344441c0e009504681e020780d0060031322802c1c0d684d5072010758401150864124040d240e080c00c0051400d00800405010300914084482c0809820780111001c1d04010b008040c0c058041a00199944a89c45182e01034040c05010401c44681410310007001901a40283d0080e4011400c001c0205064100c0410030390380803c1c0426018101d04295014107082d40000e08607002c0c1b9418004134030380250102001512544440d0b00780c0c0c2c1c85010141c02c078050010000909c0900780ca25600400d510000340389079900b09400052442000c0000c1401c076004140c040f004a17540d0b101a081c5171425041c80e500d01d40b801d1a007402a401ca0b95148645402410540d038032031546c840700c0d9a8640da8801200d00607201da901100e0340c034602410003c00e007421900c01e100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 237798534 1250 237797284 237797291
    0x30103081c11040e04110102062518080c1c03020309010c1a0f061002010b0f06030619300c030303110c0105090a0b0105010f08010618050306090705010305010909023a030f03 76
    0x6c846500215540f88602d44400203480c1c845680c40d403844103640070030344503030420601c1609000703103400c460558000350800350b0080500c5816541804299012010000e608030640201c130350000368000100c1324180d20a00e465241e407000ca01e40381720200c591b00c400f4102e162581081120790120380314481c2c4121f00880e41d0040391420340c08182e0807120020400c0781c0040310f040031a1010b0401000941d003015000d00400800014034204072687c1d0344980103107080c6a00c0e906d500c40080501142454880e40c0c0c1d041c60342480b100b82d80c0d01c50800d400c034031000301815140e400410084c1c0c8a0000d564140d09408001d00581c54244103154452886030000c9620000c0003001003032035482150b40c00d10208182e101d40b20702d6424804240c0d04440441c94102441582d14804912510140205070103021110002c12040d4140030001d03080e10f07016000103010f81d18054800016950344000c45440c2c004440400c1c400406603442e007a060203505144a03500703e02d0143c03030020542d2220903444c0d82030b141e41d01007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 237799784 1250 237798534 237798563
    0x307031b020402120603100b0d140f030a020a0201080703110d0b01093501050408040b0f07020d140f01180201030f060f0f0806090c1f020c120a03090b030103081c11040e04 75
    0x20f1003210302508d802c0da0404001c446000005140e000e803c0f0203007503d80f081760405c4216589547c61680a64002001604a00e88140840d6000f80c01e0171b41100842c14148034010f074400f0f03084c105010340c4000a00c0180c90b201a10210f90091704028080c0080c2c80c168580401c101e8410441401045050007840c1c0c1035500c1182c18240611429006542c008480d51800c2e14081c182501c60300405100049130408220000060ba03030740f500d645034144039042d058400002c0010680c1046041585038259904000d03504c0740c0e8801c0404519025a4242400900d038407100304c031f50006003095004540d00ca01c0100300401c0c01e00e07030100050101c8010004540c0746079a6250300a032204540c601c0380e44c00000e0304002c4000149400e60074410b09980e4030494400a4030540060790800c480c60070000b1907040000b000040c964132888200c0900014580c0310b146525642c2c441d80c481c81010114524034000817a5609988003640191101c54007810085480f580c68039100b41220009590450f0040000c9480 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 237801034 1250 237799784 237799813
    0xe011b080d0227060f031803030a050412112503060c03020301080f150130081306020708100519050103050d0318022103040902210702030c0307031b020402120603 71
    0x43c03e810f120301811943c10402c003842980c03d039030800f601c04a400c018211240c502403200700061031085400302004030700c509050920114503020300f0341d00410404080b2a002d0030328000905a00d0510101081e040c201420f5507040510180c0b9820003041c1c10b0038254502c02807980740d0050b5058078006000c2d1180e2007280320010307070f545400704034400c00c64040700010018000c035420040805848141c0b43c400414071500b0550f03800801d00d02c119858003020540f07142c41c503007580318100541014002864414208021f01c1d5650412411030b402041e11100018000030f01113449105040400405202c3c41d42c50b07203081901ea003007031202017000a01c3d00380100d40300c2c4500d40c2c4800c41c240e006401107038000d01c20076006c1e80b860540c090711650b62000b0000000c800110b40300400801d19000424012801d40c5840120501c0c0050029001c40d401407009140306000407040b1410300303a1600b401c10a5038000c100281c0f00001c0031001035481440404d4400188803048080f500c85c00d012800d40e182c1c80d080006 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 237802284 1250 237801034 237801097
    0x1b0b0a0906050f0c010e06040605012702070f02100809060708390403030305012402031b010603080403051b04180f05010209121605040b010e011b080d02 67
    0x221400000c0c0e880c0c0c8104907260244004000300440d610410b454000008046825500d1074030404620303901200c204401e2116078440d540c09131095125403100745000020600701182c4e41c0000070603545e8000340d0541001801002241d0040d40075140c02002185840060049501220f0200180c0515030002d10881d203d907105505c98030b080f4640d98031100c2d071090120000c1040c00d58180100e1001c0000e8000311a62070301800086100340d502007041d41c104602a04043c01d046c881c00b4000140400090f8803540220541310180806084803142010700e260312030260501d81d00282c04180005000b00c00e0110124499510300003840006080308000340500c4116400049503250100c00340161000050b050300d81c0c0c030b489a01500c0054280380c4c0385400a84504121f1443c0c1c8180c1d0b00c00060684940075004411004090484081281c40034050019200c881c0100d6054100300c5201d8440380245c600c0046014401d8125024035200d50200b103111000f542300c4920070040c178000403020b0041c03142e800c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 237803534 1250 237802284 237802297
    0x18040c11061e04030c0510051f0f08030304150623010f02060126032203210c0803040321061a030105030a061e1104050406170a0206251b0b 61
    0x1c540b12259503d070b0720115045a40200121418040d03c125551910800d0180f14026020f03411481001c0c41c0c084843c580c120741c1a480002280d0070110304000903007001c01a40c2c1c0c03154020041068a900300301a0800070720f0701d9000002c0003200d440401540c9490014074070344541c1c0030789641400b8014010305981c0e403a001d2155032485d40c900e568081a0f0080703ca016580d850705c090489041000c0010081843d820703050040398103c151a408000303102d4a0031011240c0c02001c41c1c1e000091684040003408801c2d2a04040e001ca9400008201018400c40c01c260030003206c0b00b041e410743d03072040080c0780c054483c500c107210040d407840720500340c103460780c404503412201c000b80208446256591441c0c003812203101ca00c050000d028903101d403181001c1c007400d4035001c8803a4034155a281050300308004ca803000e8010f540e6000c4071888420b200c03140019000304440d0120386541d100d10004091000700720001203078070a039043e00101c1104100d20308103c01c5001202448aa5445840b80344c1050030b0b000c1c02 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 237804784 1250 237803534 237803581
    0xc0a06021c0b090f15030a0212030c12040807051009050d0318050a060c06050a0908030901051e070f1103091c05060105010e01020d0804050a0f111518040218040c1106 73
    0x4d40100380c208282030880040c51002400759214021a50001000004e034801052141d410000c1d00719010a402e002805030006001e038424241070401c2455690b440319070003100c0c0611400e85c0e500010f0703805040d1070001000700a000c8845c043c4140340040c090710200b8941da271400c9020704040340c28603010032540152061036403940ea1110264a442c03000d0710010380103015403969501038001103100000114411503da000102d880c2c00d00c1002c0b030362261810200325980001c00070900103069408048100000004d1505c090fa80c4c1c1003030455130541c460306040b2503000c5d4200400e90a2004800b10594016010300300382c07001a82d8510040d030349444002400d41c0181c01442403102c0c0b06009044a80c0c0050150302140c2c040301996840e030a41c80f01c9920103440101400c041c0394003515008400018401e095600d190030815071301c00419121144098003485070340c022402c0080038001800d103980d0028002d00c1841003090300c040140400c07030a042c040107240603800c0041c0341d031000c1e1140c02c42411900c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 237806034 1250 237804784 237804811
    0xd060906080a0c060504181a030a0503030415110307050304051c0207031103010204030b220b0c040e1b03150301091e03080c0c0c01080a0212010906050111060405070b0c0a06021c0b09 80
    0x50721f400034010b1581034044190209480440c43c20303500c040104100d91403284000755620304142c2400f090781c04084c0d1242c1f00041c1040120190403810310240c90b082111803c1640c4c403a1228a40715080c010039800d941c2200d0401c0400450a9900040c074408903400f602c003401241001100740360a03072007140000740844000c04c0210f8040c1248025a11480c042644001003c41b11541c031004500d00981d208500d00c0f80204045c4035a160b0480071b160005110055610031500360305000c461400010700076a55071040760400009620b00790007402c1490707804050344804041600800c0c0541210840540025440500207617072420000201e500c0502188000c01004060784011101d4441c000d1280c501283c00b486155004884400e103a4042c00c4a00c101052042c240400104101c0d1100c1d40185207610107004e000200d807020030844240c90b45c42090955071441c54100501c6d100807041d00030007603480024080c0d802c80590785444c5880080310418003122240c141000104a400d9582007400e210 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 237807284 1250 237806034 237806069
    0x5152406041703040b0d050a0605030a020f090a0b060310030302010501060216090203060120070501030e0c0603040f02010e03030d0516030e0c0d06150f0e0c04080d050d060906080a0c060504 83
    0x34500c500d182e021644011203203010b4a40f01108481c2c0c00050094100984640500410076658001c00020789015801080c4102d480d400194841c03035150b42003405a8400d02c041001c90740c0070380200e4000080030b44044d81e81c0c148801c416404500074402500154038000000c140a440844c40321035001003400d13440f299a00340844c04009503c0a84007505100c811441186202c1c0298043c0324840c81d40d802510045e85030034000b43c00d40e4140001c0d0f0000e5004019040100e55914040ea80c02c00e41100500950482910059600710055007810368180310106007100c0c600d00c240c00c030a10600001202980c000a800420303000e03107101b1103141a280d0420f60058203035044c07450420001901030100401d00c00c00e0402504036a00b4150020503041070003131014809080c0002d41a6044008218840d1820b440c24801944844107000400c0c10404001190300d40303500b4a810140140543ea0410031900d69218840c55030340721314000403521000300030b4000070780c1c41c040c0054508480b41c260b03490300c4105 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 237808534 1250 237807284 237807299
    0x1d03011503030f020304150c0506060f0a090b030a0b0412030c05040e04030807020c041b0201060e04020a050603040f0503122d13030306030501230a0605060f03060d0515240604 77
    0xf0710440c1900c111321003404000f030070703c18201d00356800c5005520341d012400400e003400780c10110002d01d030130300500403018070085580f103c4c006181121610640080d401106000081c140110280040c004060380400c0c0018010702d0100030f818032142d40c40030030902c41041c01c26520341c092481902c0e440c02035800000d010038041d840b070661110007032054410040d01c07440060f04a6254128110807100c00b40d01481075180c0901c9034101620a200030800d15280c142c0c006030003201540030301401a4408004181000706c001190b80c2c4641d8003800f90b94550400c000c21210382102252848011084803a83c50041c0070028001d5804083d41401d840d20360b900c5060f54500000c3c03116085041598034180000030a41c01c0c40703060346a880e0030020791032000d50b07142c4034011450068400c1e5121031500c60208201da462070201d481c51036444070402d4072503807080c0000301030700014000a805400303807000106280c0000500903104003900303038140301604000103100000c0c41480d03800c00e80000e0100b20500601 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 237809784 1250 237808534 237808547
    0x9010503071701150219020d060905030d020f0a1b260d11090f031603170412050106080f15040206030a1d070302100309050322151d0301150303 63
    0x12050341070803480c080c01004500025103099020480d500400d10712802000d60606c03900781c1c2000300302400e119000158001810181c420039004004903552350440781000010300560340c00c02d000d20403c5440d220004400d0740d0035444030010300b000440350070241d4090f610b1031543c41c030002d400622500c00b10f11034140c07609003441c11142c0020b0200c000c1c00000100c2000c0d0003042d01d46580e03c0c01c1c0a0710344a1540034080c40310710540b00c00d4405c0d00201ca100d8003520201000710212a048800c0c4141d4400040090840b4461500100110080d43c0512014000150000d80803280b44c0802c84040c404091840307922504003100c8502c142d540340022902614100025540013000020002004a80d0b03d41088403010981100001c64200401c01c01c03d614180c9031000c01c110717050900b0301540080b17554160320fa200d8006010004005054240070518241c45c0071809001506100e04600c1071080c0d010300001c204951a466042000c0c83c039000d14141809040441c0f1100b44807444010304540d41503a0380e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 237811034 1250 237809784 237809791
    0x151201090c1e0e060f04030209060109032f0a08010e0c0a050a17010b0603071805090f060409060f0203100e090c06030112060e1c02010509010e0607050f130905061804020609010503 79
    0x30441041418110f9603600401040009055044141d60320715503c10320035600001002e00e4103101c40450f0400210303500d5021044c908002c80d07508860130030740401041c544004d254069801500741000805c15840540c0000358a1135000c0449415041400c01c2040c0c2403603074080ca64205c1c00c0c40600304034900005000654020540002050140d40c2c140440c885410403922507000440150816500040e95860320f005413905503080d1030307149845142903030001c9000e009140030740c2e40c0c0c0c0703001c80a000080d40b104940c00e00f800c1c0d096540b414040d00344101402c5901a850140080501140000d0000104014640f402415281c1181e10300450800c1d07a0411042c103594190300c070800950004018064040b0014500038035070765003080c0c50002421100f004040c2e00031603162032400d25003494006041a4083c140b460500c0d92402040c036034800074014610b260400044801001c588100150000e900c540400c0c7c0d00d040e004d0400440482083d0b0701560040d4121400304080c240c1c55100740c00440d070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 237812284 1250 237811034 237811037
    0xb2505180a0503210f0712120905030a0e03030705010e010204080c060c0c01081b040b0a0311090102061501020a080d0515090118090609050f060402030106090b0109051e151201090c1e 80
    0x4107140d0308204035541d0300c0541c04903482401c01c0001000c440d0421031008c6a05c4802004000d035991582d2125928451814010184401d0041c14452590108219590b060340100248020680701c1402d901035001401554464000d03502c044201c2d003403003021303620a41d40840081000c0800d00f001541e148401800301c04100004155260750500102c000380002c1c444020701a5944000c2040101240c0c0032070051429408100070b0b100d56070782d000644607084505441c20796816050714005070b162100354a802401d11202042e9040035500b2507000511510300b0091441d180c007105020082910300074054411811410700420358416130381c0e4440040c1c588a610000b80300003043d00c8652500c1c5030300f4840c10144d4825010082142070a02408008044032141400b9207001c24001810214482c02118007404140c1d840d8503840f4121980c10704d166401030000d4442080d40d1015075642da0050fa0750009584400d0b0000031050f01500c50009000c2076580e07a4504280441d10060b50400d18885260 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 237813534 1250 237812284 237812287
    0xe0105071518020d030c060605010806030309150c0f010501050f0102070e010612020702180403030e060c0d110904060b0a3e0705191814040b2505180a050321 69
    0xd0040c3c40300c0403408016170003503c0310583e000742c900d4581300781c03003c54200301c4c1009401403d00c903003510000b059400d1800c0498000380f1603100c100340b5030300c18092500d5429840c400e08116100b40d40041d40158181c440540c2d083c40080e01440043e070f6075900500c5900c510719164001006064402c4055422410700800090f01d003500940005250744e030000c014411710714210003848101a014881c0a500c070f80c3c4103014213450b1902a404401134054009200d4080c0c3d10381e01c91100c4280e07184100c405140008100f04001a2035100521042d005482041e0120f550141e0040e400c10b070b4400300f1381b03000b801900080c0c1ca6122800407211048019030083c5951300c01c890020074030f0790f28509000c2611840c00c07203854032140391440401080c59209800210b40e171030aa0140102c100030b040e01e40d4400d4014004a0041d210000308a803103844c0102030350645426601c40c114500d0740b02008142140c14800c400180040f103501300b000c5004c051107076652550003681c0c01410200c6080c0d03105000c80b520026107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 237814784 1250 237813534 237813581
    0x117030f030c0d05060a0612020a2006061201090b16200d0314060315060303040902160c050111100509031e0c0d0906120f020f0d0c0e01050715 63
    0x2801560070588610246010120320030f0010360b898800d0680c00007044a40702070320307458890090704141403620b5003401d080d0001501400c1c60302078100006220080ba04c0c0000c1d80c20b0706a940b13500e80200707131541c501c01c0c0c01e41e42400801d00d0050080e03203192600b0420460312622881410884a41054140810f1203c0c4c1041d4080d03a82000701022003580700100038002441c0410350043c116410407011214a02c803500510006031030008591111918041074010030740c42d07520020740303107005540c40344008034000511141640383d01c1e100d100882c0c0c0300f404950b03001c58445005440066620700000c3c602c0d40300701d00940f044201904401c0c0c0101020007a41d2070304101e0b140c4400325544002c60205808000a60810b642c0010000300f0180d4400745000300e03009051440c002d14034205414000b0246031200c100030003004180d41242c01080c4400160b079541c510b200e0014020b44401c0032010301060702d0206c01040c0c1e501500454203240c0d4454100c0243e00c618840e030170000c0403c051600164941d41140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 237816034 1250 237814784 237814807
    0xd093c090b1824040c0201052203050d20030901020a20060a2708030603060705030702030706090201300f061223030a080f0601020102360402040b070302150c03011703 73
    0x4034144e6040c1c84c0e0000c21103280c800c019006801da0303039101141d0381480c103e27607801203540700080d141c05c801408804038204906421004040c42eaa22149280346000010b2094000c0154014090100700d038440303e0703030100c4805404424490303050100005800c01c000044007902507501449561242c9a059a41108404020a03101007054411184c4600010501090389800c202d050703404100c502d04241f9610b01490001d460b8082c81600030300e115180d1141030116801680380800c4540410024200d10300c2020004404000c507161030a901480d04c1c0000c06012140c0c02240e003614904911404102000e07540c8443d110b4403c0e0030703403450204940988685110600042000304125922244c860800189227072540d64043c0c02e050540e031041146400e01c022800300700540a902d00c11413030390b0650540b00c1884000da11001a54850f10000340802d46050010183c02c0290007903084802d100420324250b081280c007507801b407180540070f0004000d41840e50026105491000c8103603400c00450703912 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 237817284 1250 237816034 237816041
    0x3120e03041401200706050c032b0e0a050c011809020c030a1b03081605090d150f02030c030114060408030a03061401020d093c090b182404 61
    0x8140880344016102602c150fa0010301d0901e0583c54400d411608030400e50a96a95552032103090103110020508881d00401401170381e18911a004551072040c140b034544003404042840e003285040d00d07180b480d01b0303800000102050f681c1e600c140142240740b04040155a508800600b1012002c0740713034804500b8868074000327040c0f11405c40f80119100c0d11401005001f40c160015a11050014542c595003c2030340070501a4005142080c0514880e43d15581101d035441003017085a0401504094102044104c0201000c29000140104010003007081d00e04203074801039030740c60004e0f50144014446130021803007003052603600400151410340d0b1014040c0c11a0425044400880d80d42e080420080480701d110b111180d800b4030241180c0481060003030940b0489004421032010800c01d002211105070a06815811402c07400c1c15a448003144a202c000340d00b8091101103078107040106289042c06030820035640850050041e1960703944035113843e200301c40c2000884074a100201941c09848521 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 237818534 1250 237817284 237817289
    0x120b0a0b060c0f0307060b0907120203070504080613170a0e06090f0d080915070b070e0307050a1206060603050403050d090303061206090b090c0d0201110f010e0d08010b0f03010303120e0304 83
    0xc0140d5115401713070a164084543c41425540139078255401c100030030754055260721401560a07401a141c0e214040e007100e103402a60400b00c078512640f414010170a10082d101400c1c80c2c070400d20358070013841d0f010080c0454002d0007684004516803107000c4600749420006485928800790034280e1b49107143e000158412603440301540c0a1700001489249030500d00100030000c88809803d51070b00c1c0f05542c580400840042c0200d08200c00f00c4038803d2283d9050090f48010400100703001070b01920b079017070504070105141e003c50310749140c80b03c0010524000d0003680e01c1075801d1707141d650034100524031007006401900421410540c1c1c40d10082111040107a24041031402000700260208062802c802c0910300685594569444900d00304410b80c1d40c1903804544503820318101c1d6081004040712490300c01c10004504141d400d00d00c500d0001e99001603050b00400d05a51204141d990310311180340c140c0720b05503074003682d04000c00040c40428042c45425040c00300c110780010b4003012200102e4107541164 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 237819784 1250 237818534 237818563
    0x915111014090f070501050f0309010603060c030b030c0406080705090703140c040e07080402090a0905070302101112120c180a0303120f1107030c03110106060c0c120b0a0b060c 77
    0x2040c48501c01c4204160210500d0f11401402d05601704000641076010b0380b059040c001100100090070f52800303421400c0110b50081c81809074819501c0041c02400201c11054000d110750764041281e0300c0c00340140000c850008018202c414204030600461000040a100c00d040e10744000c2c0b403201015205052054103c44115522241822240d4402220207002181000f80d10414000540d840e4140380341c01c40c900f0103001801030200c1c580281040603d90010b540b0000d029103a03d01c00390000000541c0040e0801507908403190282c58141a00800c0c1c2c0d0300741c2030400103001921122004009008150700340e4003580b6032000200024410110a07041140001e81c8125049210707441406552540341100c98140200000515291407038000e140c8050100086924204141030180044c000303203054102c0203010a544a080141c800c1050103021698407901c420300143e00e403e00ea0705924019070140701c3d80143d0301c6005541c4003600900041640c00041008412841c0c2010440640700c191034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 237821034 1250 237819784 237819821
    0x1201080c0103060816180e160e130302060f040f0b070c030201061203020a0b040206040e01030803060f010c02010e01030c1407150e0a170d090807030302120709151110 73
    0x10380c800141a1810f035030107000e0036888403803840c2c2002080c06552080c1d8001465003462500b41d400c80002500100b00945100c0c0514800003034110242c0050344243d03550ba2812038001d440340075902c40e0254041001a00503040354001c1868490401030241c0c0050155450307261103009503c2d400d0100c3c0042e43c003100031440660042c81016028082c2c00024580b5100c280309848480d200a9128412410014140294900002c0440d03907400260780160807885890f04586d078592a04041300d81c01684d103644201456459940c7e2980b10300c440700b50140d410380d110b964040c15a401034000c0c0a02c200c081c020700070502e0712030b1803117241c80d009440b40b94001c400b041004050024000c0c00c451040c2d41000c060303000024040041008041070400b0005042011a80d40d4481030411000f4015034030010300241b0001828402c2c1903054028000b02820b4908801842c1c07104181a0349000b1a03218440f42c2d0280c1015009080b0f0003a1251601c0220104c10382d00282007940600c41120404055440700416 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 237822284 1250 237821034 237821053
    0x81321030509010509030d11040f17070902091c030905030f03090a050604121b0503010204031a06010306030b010b0912010216030f03020705150403030e010509100b030105010509010605030c120108 86
    0x5050040d5900b209099000300014288a8009030302d038821010349a0300300323840d4280e5950558a100482e401444002005a02c843d12440d550b01007a0200020100c41e03c146603010503004890310840d103020500401c00c6085484200d01010703030226425042d414007010303140c0060651014804420fa81c00030f140910703510b031100401c0000d07807000740c2c000d903000700c40a11091081c2e403e12040c0040c1540c110041c0091604655004001c0020a03080550075500224000042103e83c072210340e0012406820885141d80d00d10044040354103c2c800540301c1220540108100204c2c44000c0400e0400036001c05118002409110300b07aa00483c180a201400a41b42409259001d0006c02c07034200d00e480e0962a0070201c1c2c40e690760303c0004120118030804101302107420075000c4c1e80321400001e600b40081c80a4030300b40391116120b4650901e101c0d801e6052043c1d07500306107410312400d030503076070000d04100040e42000011241030b007000700070006d529010080101410f03400b2081c9402810b0f2030b00181013020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 237823534 1250 237822284 237822287
    0x3100605040f0e0307110a081906110304020f04020310030609080a0e031501050f01210e0c0109050102060408090105040f0807081501060e0f061903020306031b010f081321 75
    0x400c0c0091102d2640d1409a22292007940402126451038000340030f440c00c001010006000d9041d103510a84207481040c00c000094101039210124943c00303514100600f07410028404064403013190020740c850140c4000f0852490720790f01454001c10000310020040d903c0382e580380115080d501d0161780c15440440c1d060015903120421030b84903401a0301801031004001e80209022806000759442012400000078607070340300d0200360103011920070400a00c20b54807500e820060202000da8031141c015010072070455401540020200c803010381c001c1c0550b540316107600c103031780d005601c44034100013040000062009181c442c0b60f0180420700e000d04483c0d854070b8000341c60280c4c44403410300840c0c0e80100412519405c82905150641c090720895030040c50040040c10394490000d051380040c14800ca640e01040d415406144030384001c0c0d0032a913001101a0001090400030440b1038002800c040d0400e191174400c1e01c0e6190800030508200b01c1518581e6581000076444003801c46407060094502080103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 237824784 1250 237823534 237823541
    0x20d020c0f01200a0c1205070b0c03010605040b090d0f03092102100e2d030f0601150c0501020409050a0222030c17030714030403170a1d0f0310060504 66
    0x45840000801854000030581c8100718a034442c20980307100081101d44d001c074042c9144209007035000300074400c1d05885d03040280803030f04401c10030b864401c07031407001942d1890b440044906039009919003038109403520b0300c4012940c1c004240d00340c000500d10000300000760452040004140b00c3d45075000c3c0b145c10106c05c0c0c80f600e12284013050000b62045011350140c0c807038601c9010842141d02d420480789442001040c00e10380030584400401d013080c030405210089069103080b1a01080b000e803140109002403699440700c1c01c1c0079046000d1000c807490800c4a0240062600b1035102d4000913080941c0c0d03a01c01000c0381e0007142c2490106400040c840c0c0300300c02038420690031a07001c2040b0308800e801c68403a03501d104194051107020201362005200d884000700140e451060340041145103440c2d1084219440760028030041310005103103402041882c0c910320a44010311050744e80c402180c46207606040001c14007001083e0010080d2020111a0b03c0038041d401510710100004078000345001f0501049 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 237826034 1250 237824784 237824803
    0x21209070506040501080603011e020c0d18140d1401061701150b0310031b030209060d050a030804020d0b0f010501090b090f0d0503040803030a090b0a1e1509020d020c 73
    0x681144806001e10399030001901c064550a191041c03803640d4000220340105240000640e000510540402c0e800322190000c003c040700d0081682c42d030b000700120994005d040050044103800250100380b01451120075031101821005103030006280705910b81076480c0c24600d20313003049030b51650010310400c030380049030415802200c0000c0082d5080608906503401490244074080000000480d8a40e44800800307005540c00c000041480c0e03d5505042a08080341d10040380540c024070001202480c00f40d40b42006181c10401405076020607036400c5454030002041260701c10200c07502040030512030300b51b86109410184c030101c000c0d414100050003444103a40004854081005070390340d181c481200d04007485005651000e4200310351710b09641540205d4100d00b0080c400802000400c03d4a500003813240d5004250902c4580c55800300482507d041c050080403500e201247c21610071103076804500b0f02d5000444e40e0b140c0c0394036803000704107a0788101864080c503600030407809809030041c4101041c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 237827284 1250 237826034 237826051
    0x230c0108061008041b0b130807060504030c030602030702101b0809071a07080712020d0809150403051c0c0e090f070824090c041509181d060a0212 64
    0x296a2038101c4014014180200b0084c0303040725040d5a1810340e125000380d900a05810440d0f1ba449a1103510507040002c1c0d1441a505548540c0100254040c0900300310350030307207400041291846041d0303150440070394070291829045210b9914a030b8580d0005110b0124503041c42c1698010140e0021401440040c02a02880e56600000d40070030070003400340340c01080e62461103c5c1e81c0d120305060514801e5409400d801601c03940e000c0b455541d08aa000c900001859201e4480300c4158076501901e503a14401e40c0c01e00a03000060348003080c0070a0090000c0c10041a0b601d492000c04003007a00e445c0103a40300c81a2020218038110040400c40c54002010342d4448000c1140b80c0861410050081c804680900004024008189003c0000e03d07400b044840d01c035009450f0035801d0070500e080e03001c954403504c15402c8440c0204d55449556200381e0002080301d90503000e03200640808000c40004100e01c44607240440781c10402d17201400420b204091084804410043e04d174818a900b00c00701940c0140241d2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 237828534 1250 237827284 237827299
    0x50f1e2a07051507050111120907030f081803010c0323060a0303050a0c140a11030a2a050a0b0c010e0601060c0803070e040203090706090b120112230c010806 69
    0x1191500040010442da0211043c8082c1001c00e50b11001d00c2c40b424030041c0c819401d00030b0902880031420001c01559100ba046001c482c0d48100300651218058000103000c0b980c00b24440c0c1c040303409031014051500200400c0710101e02800c000a08542c03240f81c0301c4000c2a1902080f140030802c0c50300415000c050310103060107510740000000c403031120f030780802014820041110306100b0b110b098440d150380d501102c6482d000840c10380701035590444440444084450311039002c01030401080103030020782d200125000e03400c040500c0e0b100095030b40004000d542001d180010b035550f02c03c0007880c003c044008942d6900d094030350b00d81e0b0030748007491210117803035001000402c990f96002280116158004c038070300ba10307516048002c807088400c1000255000307002100340042c1ca01c0215035501207441d142c407112090b40d80c40f200341e030082c00380070a440c04007101640100842c1c040411a034003c2882241132aa45001c10144418081204290300000342d00444a0400319600948000d41100d030840314207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 237829784 1250 237828534 237828607
    0x120c030601120b0103060f09150b030709020a020c1216060c020909030304030203030103121e0503060a06020d0e0409060e060106050403050f07050f04020d090c09090c0f1203050f1e 79
    0xf1580c40010b100040a0740d035921000841002c056104e07108165100340001501040300c0840d8001e429642466071081c0900c01e400500c814075482151500e40040d0042c01c0c2100c913510410080d801c440d01d40c0e04150103207100e828168865021014064030781c0d030721542104490b40c0107004100100070000c3c03000341d10420a000c08070743c0010a0f68110ba60200c030024071040c2c0c01c00e00311440c40c4101105140d081848621041203070300040a9480365809039802c4a51640e03410040340d540248001c140c0c046500499008068102600801411401540c000c00c220201851061901d1000d85c0500c0008401280510401200340070201c4801650401080954109000114038072840740540c0d1003a41e0014030014101800c1d0041c1d80e00c950481d124031001941d0307040310350140100c05c200705d40c64028460081003c0120b0542c2c0001d4641c2501801c010644c20b80d000c0e180707644a0484284c80139030502c00c91040c4190759806094070904003428503110308058a94600e5105c46140008c2241c02e0a00d54 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 237831034 1250 237829784 237829793
    0xf03070b0103021e03060c0403061a011d0d050f0703030212030115030e0f010609020c0c0102150f0c0f0a05040510030207030c02060a03090f06050f01050a060206150a05120c03060112 80
    0xd032815682c04130b90715102d0440a0000c030703002004004a43e60940510000c00c902440c401c03015000312409400207200c00c0f00e8003a0005154aa43c1d2100f60202d20f00d031050002d541c5901c2c0f00078824090141040b0400d07a0030b511003d04d0b254044425103403542c0300100c28401c0650500a00e401162514825801c0d941411070f40b100003031901111808040e51200340d01110002008824448000b076002044603075100d0316803030040c0d403181c18200898030519010030450352000401190702c45100b00201c000d610780003080f441101e030140003507890030f01c2400601d0a112a9100405050109440380c59036203107400c0500c80c1c3d0260b0900044245071061240c04c010a802124501c00b03290704840310740d6104003d005c01d8005040c1808080c100b200c0400031241040420b60010780030f40c40030074044969a9981e01008072001c440c0c042d000040e040301c00412284141c00700781c400d89c528000e24420826450740042069a6003031000d04550390300a01508840d8102842254094424401030403c0001182c84 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 237832284 1250 237831034 237831053
    0x70602100b043206030c1305092407080708190c02030408160302030106091808070515040b040309090e0316060603080708031504021c0504020f040204060f020f0307 72
    0x160300054440d0860209075860364409425180e1044044110081c07008000d107005026250030002d004070715000c207615190005100e085440c008002665039000b03507001c0300c0075000c0500031000c94407507400403030401d5842d241d00494103024456000d51901e45010010891040501400d0902030040700340300813415545400205007020003008254003c01b604101e1843c499070344a440c180c0035003c07101596400c04501d0004581c0203c0003800380d2911106001e08030741c83c444202005c4924815034000140e1020007070140d850207501600c24030300310059500d508140488040340c1180d80c0d03804100400d900440280c000e0610b0304020458521681d190710703640d1003140607c5840ca000442c0031010800e1a411140185038051910360319003134189401c1c01590019030b0103108089003c1550482420180309413000d010b0403242030345038440300d14035100091070040c0003a6001000c0c00d03c2060f1540302c0380020b2004040944d2035801035520024000d081c410341c00d098080e0398004004880100d241c144 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 237833534 1250 237832284 237832303
    0x30f030912050913020301080f0106090b0604050d0f0f0602030a050a05060306070c1e080901020601120209041709100509330c160803030601080a05040b0403080c0906040905040212070602 82
    0x400e942e032800342c43c000401c1001c0340344855a00034000030000c2542407010943d1403120360342d14028000f5980301e0b0748040c1614007580c003070781d00484140300801203440c1020752030f04142e02660710f20480807001e03102d103140301103110001d480107030b000030500c882060300d8407806074004c01340ca001700300c02d007028000207894180240c034000c2001100034500090044007c1c0b400300c081c1c00c1d20804a0f8a648600e0414119000f00c20214094014480001071030381452a035142029402081c0c40e01c0c998480c1d64510a4000c3e1041000003410705214094541c1c40b40052a8400d10032921b5842d1554a00c0c001c100060034500c03200d51000100c3c402c94040c0c0b0710340d08a0084005640c000b00c540301c01c10510003500c0d000f1008081951006040c0000924960100085006400c20b907a0120144e071105405420f80e0420348000b094200e9100001d404031384141c04081d045041c01d104646402100c01c00125113030407541000a10655075002d000441c50306007140c00403011504040c121161030181e01a4540c44001c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 237834784 1250 237833534 237833537
    0x1121160c060302070c0b390601080a14030c060604023603120703080406020304020d0f03030203100f081c050d060e0f06150409050405150403020102030601020d02033a09030c030f030912 81
    0x910030301101e03941d1501c04681c800c0707058040303460f10f40e543d00c1361982e504050b0500f5101a4600e800c40c0400ccc0714080202c03112420110014041502da1900307110080d400503941c01c0d60200281c034090282240c000028100045d804070380003a220780701d01050700740552103209901200e800c201240010b5001401d06a00c00c1d0084c0c40140c0b01da4550000c44c1c007070b1540400003422160300f034401c0c00400d038055001d1406030070070aa02d8401c464407844400d074517000c00d00940c0c01a910107880d200c11840c81b070421016440440c90014101600c11003194103a41c4079030040084c2c1d01c1e10104008880200480d1594850b074101c4800003414030b0304c0d01d0f121070362095000c2d04103000e4650f000035043c488200b0428082c04100c12540003245481d0030000d0003500305840140c018010344040784103442c4000f00703a6103841002264524644001d1600c1e400740500003518419403c2c03401402984540640b0032050f103a1f019407030308480b20100389402414519041004401d051034601004081014028540800303000c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 237836034 1250 237834784 237834847
    0x1e01060c06090206040803160b0610080109090c05030616120b06040302090a0b030a06050a0c080108120901020a0507080d091715060d02030a0302010b011121160c060302070c0b 77
    0xc2d800810b0310352145410600d43c900c0002000f940d08202510300010560284083c451a030712002c0802c024405d00e91078100c0002e030810018041d42d92140d0001c40a0340c41024020507255603180401d08010003100c0403080c10364802d050788c0c80d0640001c3c0d40440c205a0b80d00400c9628007000000e002c0d070180d408081d0240801d1000101c03990200d40c000e19140600038126a030300d10041c944800904011100f46001600700450790b4186801041c170903040c1c80d0100054190400182d0040a0f5a0044d007400c0f070450ac22031041f180459801c3c040600500100380213414007042927031b0060031300003560703100c0040000c40c41e180e420500404241900700302c00e10340480480f41c84100004807030291450002e0760602440b200501007540540c09520000780a0300e661500a04c05002035071a4107450b061108161038030200400a004800014510380140c21001c0310a10030903140c1049803415030b00f10002281e8001045814400c805201e0401401d400130b555160031140c001210f401640b04d08010443c000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 237837284 1250 237836034 237836051
    0xe070f0203070f0804050a05040c020d05130e09060901050105061603120204030b0f0109051602031209120403050d1806020c1306170c040f091211030409020408061e01060c06 76
    0x109000701c1d10700b2500000c402030400c40700c0c1072450f0550f1040c850389101f80851880043c450401d8000e401e041501500500715141c030680041d0303a15804840e181801c04000c00011607800b0440c08494080c9130448000c20140c07401c40011401c40f8010781055200e03100501c43c0390501580e0743d44000f4155031610b015618000d036250f2900203030180390401081c900c01d450030840190f64442c00d650480d0908002440141c40c3c641c01a0007110301c0a42c0140142c10820001d10f4044c2e81650382d03900b042d9840100c030302c8410040c401a4594006400c115029004440403480b40c50b8045260100403a988000409951405201960b5110040081405105204100a101c0469a220000520300780d2110180c05031800401c070f44070281c00f01c05520991405a45c6030110701d044c0300d40c000303c0d940304030303030001346410303140e0644010b000000074003058441040041030380380645c000b0384000d20124004095078105103085841c8950004440b10412101c0c5004100d415845051010243d0b040b2000161002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 237838534 1250 237837284 237837287
    0x1406072004050403030b010e04050601090302090414010509030a030c02390406090204031b21140a03030b01112b0203041d01031401050114040e0a0605010b0901030e0102040e070f 78
    0x40d0124201544a850507042005243e010b40095074041401d81e200030340036151008000843d4000e4443d6070001d58031120920050814640542d04140503c4c010b0020080340501c080c00c1d00e80445400050b50004070b00080301c1a014005d139009c40c1c04900141442030401004800c07101103049410007c3c1703c1f5100360540354003000c0c0800b42c0910015109001c0c1985440714100a5882440f044810b81c224440d140112845401e40200f903e602c843cad100c01e4080ba001a5150404141e0416151490340c1880301803d04010070039140d885100b03480100b91560250f0014207805c413410104421038200b00302c0c980100382c80250403242c4800c0d84d806076115420b110b1080703155000f1500903010848440480844031603044812a040760300c0b03149903003508489400024240c0c0d00030f105414040c032090000547c28a000d801220402c4580811554182d0f8540c4900f0180c6a0070b03400700c5010000016103480c1541c0c54000c07541203040c0c1b000207501c2c040c64408910724441004210343c080105902c1d0a4080a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 237839784 1250 237838534 237838583
    0x42303060c2104030807120b150a170a0603020108150d02120703061e05071706090c0739032001031515031a0303030411060c0f16140607 60
    0x6584074200842c0f400c0e1801414244068810301c0116500451000d0034078406d004030244642c4c050442841e00c040e441c0c1444403900540c29540501042c03106007a85440098040c074400c10043c4000b08485142d800094a41307800545034280c502c64000400c0501c1c3c80d00031109040c1c5606aa60320a05d4046200c103604000c0b0340d810051100b400c090001c80ca815400341c4c0c01c51891000b0104004030707220a0400e032103018990541c0b00800000c000004d0b40d40c036080b0700c3c80743e00c15500c0e84803610f000000e694481c260080c40c62100b030300e40c69140743c00b50a04001c0000407100030300610000e00d80c07821916041107402c80340e0703900d80041800701c0707908010b6403080e048030300d28207000c0e00840308035070700c1d00040042403140144210000f8139001454000702c2c0c00c14034913410641c0140107180342d41c6543d200e0b1080110500d64080d0004410440b40c040d00100f0040d0201d141d00d0b140140c1400c0d0000c4946000d2041940d0104c10620310031694810b19944a0080b20000c0e0792100c3d035000743d80325044041110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 237841034 1250 237839784 237839827
    0xf140402061b011b0504090c110a03030507020109080c010c020601140d0206070602090a0305071a03011409071709150a2003150307030f0b100e0a0f06030b0c042303060c 74
    0x740c4d0792220102a10342007400b400540d1403004040c8500d082c9084220f541070701416020340746a00000b65031020070702903070200c0c1e04411244004a895215511101410ba0244000311740a07991160952102ca505100440c09011140d00c006c00c080e1290000a100d001c0c1104042d10805002640608000490341240d13012100030701103000b0380d40d49040c1952540f10a20841100e6a640070b02c004041c03507281c040301c0c1070b1180019050403102441c000d101014000904100c00c4c020b074500700f0702d10303d02000803d502c100140002048032038100300b40d0100303071708015102c60711503800c00603c4e81840c90044140b50145030040d15450b10381d030f0381d0615902000c0080c0d003000e40500a40d107020050000c4481d04100d0140101240728803a190b5000d85240019180308031944241500040350340d04105030041200ca400d102004591940c41e516882403441090350240f03000300300064100103114a42c041c08180300003a0310f40f40c00e401450030101f0740350040100344d03100036100085c15241d000320032220b0f80300e03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 237842284 1250 237841034 237841061
    0x20d1d0901080c10020316120c050106170706091827060506090708040308010b1e0f03010602160e0a09060204030807050a060f0903020309040914100f140402061b01 72
    0x40365a50b0314080342c440b00082c8119008255440340203203818000012141450070012000404103942d4440800d02d444400b400c41c10081d44d03900c1c100c04183c00b4019070000d484c0106801030070000c0300e40d0315840d01d001a0302030018040390140030054a405040f00c850651403000000c2a20040d00380807180341015030810069001803000340c903040c0070855101a104040c20744131802a81c0b540d02d019030340340c1000c8800800199109005221169031100500042142180d90424500700d0110191081d000118001c034010004001000b24035410052034911034115490540c401e400c000b25003200d080018030400c40c080c1c407a03045508206999040f500190342101800e078680b070603072811940716081d8410175914a818400f0803400d5a45034410190169407580045107410100320a010160a9611040d66070301d2666942c40c5c8810810b000340c3c0c480c4180648002508804920700504a5580404800300f24a0b51810000180c940c0e400300e8076081c0764807a22413003d648a0074500d000d030282481c07026 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 237843534 1250 237842284 237842299
    0x6120a0302010e011404410616030c05031b04030c14040605060c07050111010605030106060f020d0806060406110703081b0118050604031101061e0e1501020d1d 70
    0x4141a410b60043d58000d2400780240542d9a40c204a281c20b10300a80d005070821086604940c185100301680292181c42d444281014100052521040e445505100c2c90700d500003504001502c0c2515126020f020410b080800084243c040010154000100002c90b80541e6100c95144880c030701041d074004542c8405614881342d2a80c00320420712008803686401141046004103142c5800001c2e903d0a910309002400928a0400111400c03100000c1e00c050720f5607190004a03203601c1c203004103406072071303551115001b8002c80c8000030f1402c180c8540f10300810001c0c030203004445c1d0f00d400840341191003a181441c0c82c5031750780d1040d504003a42617200070001000000e000b64803481d00c41314441001c546000070070540310a44803452140000c4500140f09810060010300002c0c0039001c890300a001d000e0001a881351100f8100b03100d550451059801601380c1d01040082e4051040500c1d4000c03040502403a44c04402c0d0000b0b0355494007480700c5000d22000b4052510090341d01449007624140090440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 237844784 1250 237843534 237843553
    0x705190911190c0b0c0f0405130501031401061212170901150f121b0f0e0411040b0a0504020a020c030111040e010e0f0103120908030a1d01020c06120612 67
    0x20a0305901902241101200b81e840405620303004a569214140e0840e5402d000340d035070b030382d02d607a015840452042c4031302c41c041c000480c0640b030358a400041e000342e03c440002c0950440c10807400e55404604c0356121030b030400900f0b0204900b4846c10401c26030f4000ea02e40c0b281405a0000d842c00001044482004c540340002c00500c1e07a0150000221f04030410390541941c0d490300c0f464104070b910390051b0281c0c4040d81c03051000003618007843c02c15107803c1c02f0004402c15100c10300c222010b030321580902e00e00d4004800344018450440c540820091045504100d0000300401042542c1485e2045e40e10941d404210101e20a0007844925030002000700200045009040c06108680190150f209144a42000410003050300000c482c081c840c8141c3c8034109a1940c1d039203031041d14580c42070208020101d28000b503000301c10800f0380343d40c041c1ca4542189032901105030414a1001060590456010040d07114060300c8650450701c0d15a2100705400391b0b59600d030049240c015103031621202c540720b0701c00c60 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 237846034 1250 237844784 237844811
    0xf020303180a0f0b040b03181c090b090f0f030c03010624030b0a0b070c05040f021803030415082a04030c0b03010302010e01050c0a020a14010206011707051909 70
    0x1852040318222502c4003050b4440e6442040c1c510540910b4114003800c200c14044128104d002c2e582c410014a003214200079900b403500d0800840140e80d00108451229004015801140c1030006c0c02404e404a4189440d2800143c501060000140c0c040d4000341c40c00c16058500f4092881c1c2ca41d4003500900046503695041c125000c0d460704201c103514014000601803c2c03183c0a9080109401060080701c10b007032407040c1026510400b0300725000e07032a41e04002480d0301d45010b1807480b1421140e0058171040401d400c43c0003e90301c1e0035054841d0300f00f08400d11070404844400903050032039143c1502203030355003003042800343d0190034911700c4d007011140c1142402020a00900a23070341b02d206c2280405a45140d0a010381c0401e001c000c1c0071560740d1040801c154400d001404404085c4000caa420b4290358011460800f00343d00450524501e14000c14955601040224018080c0504074450380fa40003e005443c0c1c1000d0080c141318035217184c0f280a103011130400e850050700002004200040c0361101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 237847284 1250 237846034 237846067
    0xe010309061a090907050f060d06180501050f0406031205130308040e0610030b01020a0b22121d0a0b0a050c0118060605010206040b0f0a02040801020708040317070804120f020303 78
    0x20590f201c1c03400980014401080480d40e03204844000e00f0081045403020308010071034100c0c13014510f22550307807400021281c4044007180d04ca002e07020b04c001019410041402a04100001e2850043e414800f04100059011002803040d00041c034040d9100e02001e07024072020700c003a40c0050404000420f000c20b07106c40c0951401e010b408200e07000e82010b2141c0300c2c182d00396181002441c3c007680003e07101c0c2e40414050f2001075804031100d421400030404490750303030321864000c20b015a1a6601c1e201183c83c1e039908005040c80c044095103240e14240c0043d030000724003050a0140072070486005c102c000206d4021000e03034000138008c0000b840442883c60b03803146503001040c019160b1078100203000540b03500101c0d91b140101d401c82d5001a0070390316018421034400d0003800c207405440c1d08010026401d607081c030286c90030500c1591201d13519031860601c0300c49030340d02114030280507500300114400940e1000465044034408200c103107058403103060020000040f1003003c0d405010025582c000001800d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 237848534 1250 237847284 237847331
    0x1707030f06090c090e070203090d140a030e10050405030a02040f060b04300b0412140408012c030d090c0b0304060b0307061812110324070315060e01030906 68
    0x4c4d00c80748440c0da1030a0400f04460306803421340158000b044062240d00340184242241402220041544c003040c140c17103450012038040980000781200000300c42440c1c00600f03941c1040c254540181854204000281c5840381400002e2086680702000070113041c854102c44014802440c016482c0c0b0ba451340d000f04101e20041c40d90030496a0001c40c1141684650108100c0391b40086110801756182e6845c6030840c0072000e0711800b8040d007404404400508c90000704050329a02001140c4888a02d0340003010010496410f92171282080e00079211010010a843c01c410b6488270200350100725091040703109044d80c1001080080020403c01481415040381c64421410350484920703a595601c1141c424404000c42a5181301d02d5004120544492803201c8499016085d0621181c0c1c0c079000182c0342c400709546452860480d565803450801d40d812803a030340b15840f41020f00c2825107401c1070480e80790150146c6818000751840d0b80500e640721b82d12440c64aa80101c0400c04034102e910803a0002803441c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 237849784 1250 237848534 237848537
    0xf151815100501091508100e07030b01081602150a14042003010c050301051212070309051002030702030717031b030409230103080721200109031707030f06090c 70
    0x600c0005003551240c20706004031900103424250302204190200c0700f030700014010720b400000300308000c01c5020403020308d14010005a100094550280c00000d003011030028640102c0d000885000a8410780100d88500f065510502151495681300e0201d001480a5920400c00c070464004000400800508000d40442c1c61401c82e803280b40400205400c2e511100c3307003940011024401000541015030203522255000d03000d0742e05482c04800c2e0361200b500a440c081e00066210407040245051401c2a001c2180c0e5901c040c40c45e000b100e40100b580c44031940b00e802c0380c41d100c624482c40c502c4414400e4135a044e001e81c00400c484142c005680741e403038000380659000c062425001000010701e4002e0a41480400702104030390f84e103180c440440a030040b032001e5030b4084980c18409050440251103030003000607900e503110100100c0f02040c456100202100109030716000740440401d40103074141e0803105550605103226550300e6011000f40001811540ca1142040d001140c0000c03241c001000500c035030b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 237851034 1250 237849784 237849811
    0xc0109120305090f07060e010c05030708030a051b0f07020109030228050a030201020712030224010603050a02121513140a0e031312060213090203090607020f151815 72
    0x9845401d0b8484c07030020714044451744140001c000540c003a140c0c010201394141890800744000391900ca086502000e8200d030303507603000400c01000340124401c00b5040350a40041d68814076000504040c9840f444a800c42e8413003002c96008116807081820f00c0c00345134090314540100c44034070b4013103040da14065800e032021141100c001c551810262168030071250141e0052a02c2440c00c8104488160b0ba2242682180106044142e107a4841d40030070f4100780c02c400b4409195803404000404440001d070070401a5401000030116100f1034070305140d000540c034050341d0f541a0410b4001a66a1210890203036080d092080865004a50061071485001500d50074010800703005a0680c481c46549100301d030805081400f8003040f900c6160174243d403407054000502c0c1c070030b06600e01501c00000358800c00c0030903000020400801c00134422160411024001490040e10076640c9948401c802184074145501d04000102c041c148000541c0b0340c00240343c241c1311601888180f0394004c4000303d84001c0700c40c00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 237852284 1250 237851034 237851041
    0xe0405090c0a06180f080d11030f0d051521011a01050a1101020f0415030b0a052b1209030506011707090207080d0c1805040504080f07020102030c0109120305 69
    0x240412407010000000704500c501c2030500754103441c0ca0a106450704600d2440800124291200c464032101814004c0e00500c012802071100401d00e00c100c026601e05900305010b85243e0807250000c2e01c41c411801080458543c1d1401a90f00d05003000c070580e10717401040c942054240980d4103032215010143c417802441109100800305c5901002410044e000030403c1104210840c42034001c00300000d41a80007500d030070302400c0750001e150400e401c03843d42c2041e0611503080c000d030507102d1a4040b14003559005c509615202c002000076080f182c1d41401002072030100302546018850082a90350301102c42241136100400c000c0c920149400115181d1090b08004154408035000d903c1464a4803001048503a04101d2940065040b0100803a03040d0400e00860520003075900840b890140507543c0d43d10290050100e4500d500101d2340100c1c0074502d060b0500010035203141c100c8480c034215503450303552603201c2e10040b86980704202803a055540713800705070b00401c4145801c4c186166015038041c4800e44 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 237853534 1250 237852284 237852301
    0x230102030c0309010c020a1503060e09060402101b02040213050901061b060c14030702010b030106050f0a140d05031b06070e0d0b06010327170a09060509040209100e0405 74
    0x1041420a40003a44140000358856116034417000110384050000c13165540c0c0d41281c003444039010315110300425291035050250051040c032255000031080000c20550809402140386840c01104240c00c02403102080c2030050020304a400b00d180d40a803046640d4a00c50035030441c81c0c8060f01420b032007080c00b5800012200c6c031418a50740460600d00d503403030401c84151303640001080d0038150003042c0322042d81c9103d032001c1080080e43c1700e1907443d00042140309516080508440c50743d00014401c54010b0840324641d19140140c0c1d041d00d40755850380c640108808001684040080c000a00034070001904082c2c03181c00407048400f60b20080c044400365160124141d542d01c00401c03d07290040c07014400c0c0c2c0041501480040e4000406040010340c0312004441d00b400e401481e600807003000507030302c038070f000b040f40041c419032480d0400b82c825810050f080e0801001b00c041845104100302c03003c84c500f0f00a03031f1164121096014000c00c0080c070070000c0346001c0d055960021450380300b503140400140b40107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 237854784 1250 237853534 237853537
    0x5190503010501080a020306030a0204050a0507140406050f090f040e0a060606031103060d06140106092405040e0a020c011802120c010f050c03091e1f08040f03120623010203 76
    0xe51050b141e1a80d03c1ea82d01645d24025040241859454401d400c041c40c050380720f9102342801100100c001080c03a18246c42c01a100c3c45104401d00d02c0064104401c00405900c40d0a0b20607221040483c01e603114540e4002070880c130603c52190340c0c01403810503c441c668100080718101e15204034410300405941d100260122008800d0300d0f840ca5504000082040c0341c11850540c0c420300c10500041c045001000f0240f0149098000c00c1c0450060201400b01140200c1e40000c25146610f1002030b15103031820040460007648182502c03440c043e8045601022260140c903c0521060001c1260000c0c08038a0810003214040076806506100d14000d030704100468102c2c4151810785a01c0920a0301a030200c0741944081d59405a9000511440d00c590350380040c0f480c585600006141304840d0320600b0016075106014064403c0c40301c0c43c1c0041c034101c0d040225640d03c00c2d0002d9045c0841c40840c00c1c103a0b070800803511011041403810f40045000f2802c0c2101e0381195041c1c02107405412402801640d03607 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 237856034 1250 237854784 237854789
    0x1502060402030a020906011b060f0e06130204050603070305010908030117010c0f05030612060405070518070f0c080f1902011505010206010306052505120f01140904080c0d0519050301 80
    0x42d0003207079003d005414580400c54020a040c0360540d0642004548801c40c03042909040703e40f583c07a10180200f4528070300550000319030100140110b400c1446048020318034242c0d000f40540c0d11030307001488540c0c05005020086400800a0151a0652400083c0c0e47d100340140b048801e0300309a14042c8140500c0f44091115841d201d600103205900401c1e66190001062154080e010350000041c4d501c0c2884000e000340c0c400c00c0101041806d09007042071002c8405402003240e50034004121180c0e40c001ea604104d5011030800010b44011800c102c0074030300c51040f09050248000030b81e42c100041205a19a600c41c2e144d0003048050246400c01c000c40146124442c0168000310040c40454202e60210350019119415564011140241a48c110300d0f01407c00e004504040f44810f40304c4001c8400660095002021190079130403c0589059111043c10003801400180001010400f0990849021800400403506454900341e40281b1541c00340030386442d445941802522028080c0054905 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 237857284 1250 237856034 237856039
    0x30a1403060d031112040816140604090c0c12231e1605060c130510050336071d0f0403180504020315030c01110d050903010e030a03061502060402 64
    0x1440d642c15242101d585054007183d1215009444410050030207010042c80100103038000b60007100b14410300c8040c0074a95900002c0d0340515002d0104c81591a4011101078a0310b8000002d02d10b0031107102240d42203c080401050300f0044258003001d0368108800e1500e1148881101d59051030001d04021503001e1510040581401a02c281809c44808000f034810400d10a0101d6000c03106600d0315442c00005a400100721400012001024204c102c2c254003d070109a81011450001d4840104684001004030074080003d00329800079240c1e000c201d4001c2c104a844401031700000e000300301d480d800c07548190f613503507214441101d950b08282811107106000c01c02c800b080d2940ca507201502c0f031040151100f50090440d500c0407401c0e65951001d18014454242c04240e0313400440300b031602e00f2080c0c0300740905200102c0f00040d01d004000030b100e0f90484031490a1510740111602007805486a0360f2944482d000100e0904e10b05a41640100100c0e0b480c5031660a102507515030a9840d00000d42e0003a4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 237858534 1250 237857284 237857299
    0x6030f0a050c0d080913050105150703081302010302070609080d150e061c050609060403030c1706210a0609060605182805150f0307261e030a140306 65
    0xb400e85007030004030041c0c5001d040b403d031400c0c260400042e071403900101012041c913074890060183c1c4c20070505807007109002800c100d280c18002d44000d00b80150042420400c00c03032038400c0c0c10459202e07406441c000c95100c0428486403100c0d20700720003140c00000d41020010300e001551800c000038950054100e8540c0da1014030281c440900748200c280c0086110060801c0810030f14000840802c103544c49a848100500b40c603080c42d150040030354019485600412413000d460f0481c034101c4030b10294025900700d402001720000b640361016040307205103880080c2c0c00f800000c2406e00503550400c007150751103500704029460700c6400704559a14141740c0d0300501640ca900044c1c00d00044049100740804d00041d68402000200c084002d0326021950311503081e0394009080001d08100b0302103020030b00100c002c0d0101c1c3c0e08004883c4c4440014102d40031390344400841c440c100300000d21007503d02100f03170140003128402c45600d0581e20b82c040221440021a15620208044800d50940b405008001e0018 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 237859784 1250 237858534 237858553
    0xa0c08060c040f12061d0f070609061718010c0206100b070b0a020309161706090303240609040c090e070c020f0405060f1309060f0204030201170c0412080306030f0a05 73
    0xb9540d2490302c0c1c408983d070755a5040c800740d12a1a00c9114068050448020450b003403016411f141400c2c440e901800600c118118180a000e41042c50ba00500e02003203a407101695480050315806d0159284c2140d941d440c091100c40306036404954039206840f0301110401c46a038a0002c07070058854200c01030034100b19034011544c8046990011600422080200c030581c0382a401003902c011095849075503c100c80c0f4903101210340052110540c0000201d0282d42185054074202c52035041601c50100300b421007014013170460ba10b120a4442054029100b041400340c3e207280070b070a042ca10300403007104401c00300c0081e444602c25603466a000c0c1d4050801d0782f10030301c130074140400b0b490040c00141e400705520b02e0b180d80b03545802e082d000b1401d0150601181c038440c0ca09001084403500b80d08220858010082030000d40d0700b1101400004484008c0820140d842c90b4001400e03005a81141452114003a4050b0070320080a0266004080490554a02c07105108000f50342d050000070007007507500050302c0c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 237861034 1250 237859784 237859799
    0xa020a1205090303030a020a170f1b0403060c020106061701050105090103050a0b100e040b0306040f02010f050d0603030519051606020318030d06080607080702030711060c0a0c08060c040f 82
    0x100300301500309041c042d003811200400242140c00844089008039404a0b660140e6030f800640117141500b055103020690800d0282c00c00d00480040c0103003803202034002c41d2506803125004071802560400310400192a440100a0282006208080004802c6c2c401030038070111460310b0318104d42d416183c9038540204031005401803c40100f0000d031250b039409140307440340c136070407004041e514155a604c910b03215141d081108032400404160700a5020400304000030700c0554440b9011502420240a940146002114980300300c448001d002402c2010000426400c00040c04100ea900e20700c020020001210884544c058444104000034601c054400810115401103400ca210f1041d5041603290480c0c0d031518592040721540742240d074580e400c00c21500d050100320740103034041c6403046640c01d02810084d07583c000d07994041c00032048074460303800300d03a5080c04842070724043e5070030340e083d003000c9080070307408800e06114050050041c00c1c00900003034100d00849042c0d4040500410065091016 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 237862284 1250 237861034 237861053
    0x705180406240f05040509180604050a02010912080409050402030304030c0e0105210d030f020d0c2703031710050a030302010207142802061b0a050723010f021c0215010b0a020a 77
    0xa02002e80c9020701074101e0010620100b03210b2b501400081c00041e16520006200e65660740c40300100c400e00c1d050040015120108a03400c0391030f0b54401040e03a03225800003074103602c00c59100400008812000260039103000410f64125142111522025183c10109403541c41c20700500401c160400408040c00502980c405807805045e09001030405850030f0318201155100000c1c10f000c01d821101d9004483ca4902c210fa82c680000c2ca500d00c60b40307182d643d018081d001407a110b08032004082c40050001403e20400307400400000307003a01d2016549060190003544100c6003618059a0300300040794014000540c83c410b02201907886009011103141002c401680c03020492388010200103640c8000d130541d05540c400e254000203070034030803620300c0d2141c580802540b025084601650840400c007c8000140f246202c080c24184002124140102c1c10211026481d49030074040b0340380c06d000f1340d900140c5a60941c5e04618030300320590726541c4e4481c0601850396010016442040e50400060b910780c2c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 237863534 1250 237862284 237862291
    0x5060714090a0b0a022a150901050403080c100513060506010906090b070305090307090b0310150506160203010f0204080c0109080703121b20090f0705180406240f05040509 75
    0x8160340c0005c6081c4140c0d0f610a0351001e05086c41b05115028003603d161001d1800070002003100602c0c0f0385064580081c201d800b46100240000d41c0100746005401070502c04011801c05501c070030000791404940c0301950b500150801d0700c0c1d076440c00c0001201d55003d004841e06591540e110502800d160100c20407041d030147c030301101003080a2042e1a41c3c0d490812605010303001c092004503e0504500900d45841c0318107510144d0182041d910116120f115103020341502c038140d400d00d80d05c0c2498001c2c90b030700710070821000b90991320301400d42810000e581d02603c1039400002c156541031604000459202c0b0284c0186282504038200400000301480303203441066000d41046a0b80c4200c03010700d40e249030502102035951020f285641c45400d00c0310f00c0c0b210306072441251189100e05220042c40a0018020a1141400380009401d10115841d500070b081c2654020000e1080580f00c1c2e01d010201041003a60340b01d0440f60181c280740c1035002c0c01d1b2220134180c1540c0ca041c10300d85070004000701e428028 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 237864784 1250 237863534 237863537
    0xf07140d030b0301020c330f01080d09060804030c0f080315040e0a08030c070309080f01061508010b090f030111270429010903020a08012f0406051305090405060714090a0b0a 76
    0x1040100701f0820140040c4596180200c4040d250700d81201d070390070314500180d01000c00008034400e00c03107075400007081a002174162400c0036021040340f07402800e2110f502d0024113118400300c20050300504400008410030001e4400707121541001e0082030303440444001c020300f080000e00004480c41c200d03902038081ca9002c0d292103542070380d891480724100304d00031007106081c1e51a00001d000c2604055207200000056240002c800d6142ca070f110030b00c500940700058402d188240e02c50917640c2d000d40207040c9555516489664801c0c040102041c1c0010718800003500c4000c0d40d4000c000c51504d03100c0c45191768080300c28003908622b0200c1e452501050a490141401039414000c005610b6180b10200944140000040c042d6856802003a2a0843c015803003541d0b00d681c03c1a41301891010142c070201ca410703007071507074030b605010714241485010b0360826504040c1d0001040140031000868074001c040d035485440124042c160058801d200c0e00c8507090304569220020400c1c04680d030010032032071145 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 237866034 1250 237864784 237864853
    0x2040f060e0a0e0408070b070f09090c030608120c061003020a0509130b0c071a040c090b060405030f07151b030f030e010c030c09080303010e0c0f07140d030b0301020c 73
    0x351400320000c5030301039134243c422182c041860701c2013104201c1d0706030b0481e4407400c0050142030144401000060b036402032501c50364562107048c0049000c1e0b00908090000d00d416120660460b45a0701c5498120480d101040d21408002c111203880c0381d80503030150380d009000106030034144400d0059500010341410221180318005001003600c43c1c01c1c0c68001d460081d9100d40e1484030b42401c1d45203184147d818640c100d1800f09100010700c001d08204100d4884410100d07030600c0c05000100c0b280a0360340070300d81600840c90b030010025004981320050711040b0a14180204803288212500104003954550381c203025180c0a0200b80646440b03c400c0302c030780c5004500007038075011017804d440c2c50304001b50119407541d51982a464203c010003026240200c01141158986107030040f0140001c1d01d0000343c0c440000b075240c03502841030100c40c000d0390480c0242050680b0302400c5a9110b051190000020745045403401d42490103008aa0001c48040c0c001c0030034086034821a4210040b0001211040ca070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 237867284 1250 237866034 237866039
    0x1809052a040803280806030604060c03090203150106030507020a030903020f150d0e0105090a150c0c02090108100506040209060307030b04061517070206040309120206120f0402040e0102040f060e0a 86
    0x7000204540c3c1841c007819100d00110103551409131101e08034000500a8580c20030519440006041d903105402c000e000c280c101300c000040d002480600006501800f65a0f645004a490048120f04940983d90704001568400c00120784071200c412004000a0341240d0800152404210030012032200034100002801ea440d00c210b010b60161030180035294407607000258a10302071188950000d0b00102401b0240010354458084138003040b08003031403a640d010b841e8500e920130305041008503800360080d006940c49031031065480302002c0c0070710100c0d0304040c0016014180790090b2208a60050640e07800c58072101415005400348184d1b460300603507100000920000301d0041c8010110300b07511441031800e007100f41c42c524a08020090b80642d8040400d2000196005185508448040d101c03007000000358400103d441c41890592803403c00c5880c103000a145080d4150350040d407003120304000c6594058905403d178041c0d440740c00c0554840b900b040040601a00540003010b4008000888954 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 237868534 1250 237867284 237867299
    0x108030d0c140c0a020f0a0609120c0302060703050705060907030825020a121a0c0901050d0902030d17060a030c05040b010c050a0602030601110c0607080714010504031809052a04 78
    0x811803e00d1003107550114125809600344444120a80c83c015903010440c1e40c28aa0080c14406092007070b120040380b004501c1003031144001c20000a10350081c1b0384e5a031407c0c2e6040080882d040a01d0a54203801480e01040c12104006180c008581d407016280b81060070620100001700d004a003c1c0129401c0c0061420060790799884000251420508070a429074003400d00841c2c1194140700c0031204221241805501e0f403c0e501a07411420091818954402e41302102c00f002d8203000000a4141c4524412484100c1e002004002e4003006941da2590f20360300c0404001402d2240e21002c1c0220340c2c030220500080c10306800035800c2e081c0c1030403e4003100e111a5129440d240302c40034151005980401405860360780a042104610b0415008208100106e40040c84d103225158006240f22000a41c1e0401c1200000c0012100c0d007040000700034900e000c0c18089d150610f2251200094201e0389030200c0e0380c0050f4441c0601841c1140c18400b203030841a10004800c0e03034035403224081c82c5001e010004100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 237869784 1250 237868534 237868537
    0x60303021c0c0b0a020316020604021503100e010803040303111c081308030a020901090f03030816030e060403090e060d17030907150e0a06030209091306060b0a0806090105090108030d0c14 82
    0x113200e20a4016540c4c41c004a0258601110340011300441d0031003400c0c000582d403a044990845d40782041c9203a40d940301c00c9d16841c01d4030310580c0045140c244110000980a402002070000c80e0300a031161080364409280072529092a032000e03000c4440e50440f2015200e22901200764040e1358554401034036030554a030710409400440f2504d20264001401c0889540d114102c2401401c40e42c0c07104940e03c0c15035602801e6440c004020a012000c11402c207a606da103c0d03040ba0320711079200425a62795040c2820000c000c64050b00400051040050102d8100d003071250410100a400444c0c071102110000030140c2c07640d0010301081514842d075200400d100e180300650180d640c281d5100c4070300c0c442c1c0050078000c0c40e802d10351040702454418043c080064460482d103540c4801c0d105081d105110301e501c0c10400511241d046117104000208030341c007606d60083c040c1406900112072600d41030303030390300208040040d00340686c0070036030428060780048078400d40110503014545e00344082104003003041614a07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 237871034 1250 237869784 237869791
    0xd1509020319050f011b0f350a0b0f031002031b030106080103030e06030c1801020f060106030b0916020c060703261e01060503131401140910060303021c0c0b 69
    0x104d4020a00640494409105510511418082c802010f481d13690002d0161400c14002c00240728003910f4491032400c00044803620248441c070b41200741030a020281c135240d41c003243d0341e601592900b08510700d43e103090b0002c0010954010000d09000054110600c007a40000e0420302d01c45500035008002a0304820182d4007803c01562910250b62450a00504131a4035242c041d02481041060103d1002c03488100e44d4030740710018130344640583c07440040b4685000011119401c0c0a8000081641603154100c001e00314001c491299181d1250f4407040448480d51040c440503034403c0992000d1030601c2005040d249010741130420715411003001e10400740e050f05214140310b0700000700b040f44210b040360000b8100301d580984880701d581000310241c42c034800541813008060350b540c82c00c1d04120001c3c1050700c001c500b41e4000d100340b480340d40d54111600c00079210309506000e4004003000c030400c54400d6a08a9425500616125400c400386900e0400c4445440c4100110001500701041fa504104c1e0700 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 237872284 1250 237871034 237871043
    0x7050a080114070309020a030b0c0d050f070201110c0304120c0801090b010e07080402030a111201020408010506010908030f030a0b040603081b2515031d030705010b0d1509020319 78
    0x68481d0034202c40340d060440104000c0a042c508000507002da02d44014010640b54003c00241c9251101105540030740100145007601d02c0c02c0c642084061002102d04030f01403140341e0000d0000d146c07002c000760094010703a51884c00603882400108100c1161101d070300c103031b54040c9003641e001a446800450a580000a05594120400300100519000848060703800b00252400098901b0541d00080d121041500c028100040c020003031103180c0e890b442d41180c03100310000211341c0c07151b130b8080c49030103802c08403152804586600c500044e02d440100482e9101543c000741c89245588040504000303001402c805600a0313501e12020001171450b4000744000c1d0701000000c144403007019262480c0c40d0f12441400043c15180d02d0045180300d1080702035098a00c42128120311074131025088000b89442090612080349484040c6001c2e40c3c04001460814002c20080c84008505d0052108101a080c1c0007001081942c3c103400040f5082e81c403110303c1c18401000d486264500c2c0700b0602441481000955 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 237873534 1250 237872284 237872291
    0xa020309030c01090e1803160c05090708041a1e010909060f0209030c060c15070804050708070509070c030c05060a02120112050d0c06060b0d0c111605010c030207050a0801 75
    0x4101d26040061120346082481c100102c10f00f480005e02d840e92020708004035491080c4106500c005082c4151103c4000c091403c00a100090800152000e1148102402541072101260f1113030302c1a0a400d2085070052980c40081041c1c50801c000510000d22080786420300341d01c000455025205454000d216001001c00d04d8815403e111003203c01c11454209000c4c410081c51880e0388001c60581e041080c100e44854491442514a40c04e05083c210720300d070307c031083c0000c0004a64125100c2070090340220116405603441d0034400390345100500545500103498000101160f109140740740e10584039250078024050145d0b07540b4901501a242807110030303008503042c40f10740c40030000540184072649510700c01d6003460b21150b44803582c0c03011a004000034600c3d010148100c03604500001d02d50341400310b66420303205000e48010481d0340600000601e258140555400001407180d0140390711001a8022501e050019205c042c0d40000032419400341b01000a12583d500441130000c2c2080700010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 237874784 1250 237873534 237873547
    0x70602070c0602010c030b0a06030902060708030103060905120405033307031a04090c0306021e040902071a04051005090c13020409060b12060f01050c0f0a023d030209060a0203 77
    0x81c0c20b490180c5c0c9844201803420701030314030300c2d6a95084101180c0203400c0000307104000d4000f003203d5200307940d80900000c0c000000042000816406807107080e006030300740c03107200c4130000f82240d0610541c411554550711402b40c3d040304860340904c0381c220080b05140c984942d181e100c01c1c04050340d400c4032000042980c0e5079216101841c811040028804100c40421090300181c1c0c0d41c030440c203403900010744800c0e8041441c000c025860651600c1240546510035200e6030355501c01400f940c0070500840e560500e41e50302100b180701e032464050049500001a180c19a0304522032401020010005a100c2c4514600c01910752907900400d007913404060005a80c0e030f81400b054800f640c5090b4088516900d0402c8000a0255000d049507004101101c480303174048401c01c0100c0d1240180201820030b40544c0b40f050700542c1001138106201072081c0c445146441c541c0003900d66030303a03040c01030301100718280e901c8442807042100040d100d01d0050034014241881fa5000c074504e80c0250400d800581c0c00000d29 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 237876034 1250 237874784 237874787
    0xb070f02071a13030c080607170f04020904081b030403050706050301050a211205070b0a020a0f03091a090a03090b0301050a09024803250305070602070c06 68
    0x211220448900050215900d40382c1c1441041c1c00400414150050101e01c0002a10816410350000c40c0c01060f03145019844640c2d250b151101a02d80c50045811090038a05041129081e603200d400101c086d10450703a40c98080c4005050010000c81c1c45040803c4085600111000f1142c500f6135810020341e26a0708600d410341c40c1c003643e034215206101080c4010003844ea141030826040d82c2001e0261118600c130076142d8a0709141458008203402005115170700c0d1160700c00060400b55001e00c15604070b0f40c0355081d05c8022031168010b002e00041241e845030700958080d03040b03144010b01c54070700b113070402d202c003108002c00324401d96050499400075018807091583c040d8101014140c012250780c55549000001003034852382c0e12843d0f07240b58001c602e01c442da11085c1c3c1d100d1603000380c4443c00d13040640c0388020700384118004040031449888601500031003280c00019501c1c001c0e80204030300c000c0151141c51400204400702c04070108041005040001101c0b4005031403a684a28081000103041580 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 237877284 1250 237876034 237876047
    0x40303030b1806100c06061202010f0306062015010905040209090c0d0b0c19030b0307081203040803190c05040f0608070801261e070506040305070b030606160b07 71
    0xa20910800002c001202010803403080070303400c208200d40b201166400d40b44103503812125400080c028501d002030010308950034214a40b841803003641c882c104844001c00c250103c2d00315004880010384c81649643d0807294240d00210585241c204032191400301040404500009810440340700d41c88205100c2182003446019801061071009400841e0300740010980d404180d03140640900c0021001c51450012034040f15141c3c0c990045544800c142c11202034080c10781448030f14002e11400078009044600171400303200824020820502d075465940760000c00307420140215440720880c10003000c14820390710901100c0103c949407030f525140341400500303010203181e211005000d110307020080c10692059007181520700d1084aa5041d080008240c66841d020745180e04191050107452900441401c82c80c40412171500d049410140d1100306101050090b072000422992013000309002e20fa1001001e1503108c00c010f8252070510ba01c15980b140d401d000b900b0140c0d1540310400a0054882d170124 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 237878534 1250 237877284 237877301
    0x13050a060e10060806010c11041406030f031204060c030615030b0405070906080403180506160c050402071a0403030f050f040203010624140405090103140601081b0103051b0a0504030303 81
    0x10309070b451240c60001c002d02180401002e9034100440c0060f21000c204038180300d4001050040c004000c00c001e0f1480802d01c034a02075941a00c03070b11030110b807080140030010440d00d402100703510009050300e0b545c1c0e402010302407048401e41455122440421142071203900c20302c803050655004580480c44005000442d1005050300c820000015402e2120710703004520150456030616100b01039004e21b0300c018100302c5a40c0c10941d03011000127600e003211100c142903440401d00841c0a21029651641040201d102c1d116000b0204940e000500c0302c18501620441e03403080c02410301007440d0706e001f85001c0072038004480c0e01500020444c00d100a40c1170034031a0002070030170400b91175000ea10000c1902d96800320400d821081040000b424441c034001e100644008001c050600c3d1100e584900e0b0440f06520080d0703001e0014031030200000b5022000086e8440200e0004891600740c4001000440240c0802031010f90a50000b20506a10351120b000400803034809170345135030302d030350a41c0307401010740d0800c9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 237879784 1250 237878534 237878551
    0xd06271a010e0d0c0320040e06090607051b06071d04060e060607080f031611030403240209030a110a050a0e13030210050109051905090d0e13050a060e 66
    0x280311081666000101c0e0100079404865a0181071000d00d082c1c1103110b01c5410003045e546010601c0d1006822010b0006201d036001c42d4140036100d2819902c5960b01e0301102ca000055000c10b0200d8449030003072000b404001201c0742141181188080054a0004107507550b8000401441c100f00300d0408003601c4495044085a040c00094905205a0b1181d00c01804851041a00069031020068408100c8d41035135459401217480380f41c001920030b0966002c00d02100403074099034445001a40100031501981d5102280c0312441200c0c81ca4043c170a2050008078841540c200b00c0a00030380e40c01c2221101540c4a1842c82d102107844001f03002000116500850086001c40024800c2a041e4002ea030f6024000104d0b000310b00c0c2007418100d1405103200c4000300c80c2c80c40e1000201d40c07814603402079881540d283d44821100450822041c080701d00440b40d90340035030801c1c5211005076228100310f203d00c4000500050b1903031403000c00c1408880c1d00355007030311030319646000400408ac4100d03581a40010b50 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 237881034 1250 237879784 237879821
    0x71103030c06011217030910020a18030c0305011518020d0e0f010606030c021b0405090c0a0e01030605070c080304140c1801050f030703020604030314071a0402010e030f070b0d0627 79
    0x187e0f140f50354518882d2607111554010950664680c4280b0300302040c0078500c94414503859403400c200810318400d0006584650a002061151a030180b94410444104512020a528032040c14000030341102032a40c0120341c440039121100e00381001031604048602c03000090551400074060304807000941c13040155003040c00109541d498501000c100380c41d06440204590f030364039071f0103414050a85000d0ba4030064189021a54002c0300c50001c1c16240715010400164039084000d840401058800030044082040000c001130001c2c0f05046c041e006840c101e136081c1144100007000d540e008075a580600f55010010080d61805004030030180d607058014181b45800d580104596108a001c05410f2003841e19406542e81c01a4003100c100366040746042d06c943d40304480700420303040c064900703a00050002d85266001c1c500419076140b0b2416078801040403a1622a80d45105e80020f042d41c05a990343d8140028050b55241c6411400515100180c888009101440040322680e0841140b644070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 237882284 1250 237881034 237881041
    0xc040e030a091e0302130b28090501030c1401090e090309040501120503031605040801060923160f030912031b110d03020d0b040c0509040605060f071103030c0601121703 74
    0xb070700f010101c180d94054441050344200000c0f005e020308001100150810021140021007032101c4580015901c0000c2c8501e20150fa161646400d542081c0000307400344062000400c61700010010260070140e044c101030203603030360310b4241e4024010704a0b1403540d203130000594002c90b445c3c288901405413000c030441e028041000e444042e500e020040c201c1c8100d010010102c07810500070380030360717004203d104000c3c403030591140410340207040140c110700c2c03d0200c5a46810142c4441807031181c4142c400001060058020a800301c50503e01220050705042c3d03102d1310300340443c2c140c0c20310b18034106542c2c501244000210642c450a00b108282110030802055041704845d200442c04e161451400c1c0740c0961038000042441e001000090101a030061a20b5000e42c1856040006007d650700200c800b0030001341c2e030b08240045441192050082040100130500000308001030801807204043c0443e410034400d203024a01e08102a0040101850f10318102d50030001c01e03e90041e01070380805c01c45821803d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 237883534 1250 237882284 237882329
    0x90423090c040e1c1e021605060307020a080a0c06090c06020601230f01110a060b090105010e010206011203031e02180a03031704031224120b0406020c0c040e030a09 72
    0x40d03022464013410703425a0320240e9900ca45c600b1001c3c0010380403205041401581e010713554100c071001e02000000c40d43c000003501d160550035244039800a801030207003610b07580c0e00d1300c4496110307080c20002d00c0703084805840407410300e11898a426105603203e40400c0c1c02d00c0c80207403824005903c03034031111568044444400915840351181d06c801554113007000040e00e40182c03002c0c0760580c0c03c015107200d181031100600c46241c20001c034551042d02d04038840e0740c03030301c00440b400c40c01c207051540583e020740010050f40d000000714024540c005c0c640001e1150751002040c22080766200000300c41034000c1824001c2900c41e82502240d00e4040b281c818440b45981e0f0007802024054038104860b21001c00001c040c180035000152044ea220343e42080102030f004000c82251184500c46008080605004603001071080032480a060704032000c0200b940d01c99880074040c1d8040c1d21003840a0280d11140085501c0c1c50050b00f41d41a2440061501d44a11400c01008112150300105d0b2039900c0004008100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 237884784 1250 237883534 237883543
    0x3060a020f0d090611030702030307080708060d110f0a08030703030f090f03050d0f020412050606090c0405120a1203060302040f140105010e04090b0711120a05030c090423090c040e 79
    0x502c42001041c90402420104000c11040d0714202c035409002081209171503020000318841e02c1592200c131001c2e111b00e8011117841500b2200d8540000b00321045902003500e04651021000c80144180740380c5a0306404140c0c4035646a000e00c16950012580208054044c0641c0c0ca00d074403817040810103400140c4408913501000c4c83c024080c0100080c80c0041454203400c0b00c1307013325a0640540d641c0b41d4986242c404100540d00c01e603540d01603000403404510389051628003039808041d02030708243c1403004008003500300008841040c07080c6803031140052428401100219160b8030001011403441c0103200640382c80040052820b464407940c8020310202a9805065032802e00c0c000305a1010030010070020060000041d158040340b00802c91000c1d840554600244011001e480550380d603003040150728050840d041c40400c200b4000517000178049406030504d070300d00420109805201004d00711540340703002580300240380070710100500704c02c04100e442c02c401030950301044040d49009035140c65 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 237886034 1250 237884784 237884797
    0x1050408161b03080d0e010921090e0c1c090317070c0b090309010f11150406020f0a120614060301090b0d1509020109171903180303030b03060a020f 65
    0xc85412069441c00d00260601d0320461581c04010954143d80740e04240c1002d070005800c00c00041e08001c074492400a060060406941e4010f03003503030292134548407070074560315010545420002c0c0c1c2034000824140d01c000381c1d4083c40c15030601a550b100d24418032080d451501480c60a500d0529003a440000ea1000c6460808000c010303110050740c0354080101c840b1b44d04480003070036600e400b409008601c07034080700a081a500c2620342c22110055821705135000c141406a54100b41c210b103041c0845402030314800766000c0d10405006291030002e40300c40540350022000600054482c00100c0e000a07000d01c1447e014041c081e200100080382d260000ea46e40c4014050540200d8a5040740c0c411074840c04081e15a15600500a0f0101c41c0091000d100815400105030300061001c000041d03120b02041c0021482400d210203482000d04440c2a07003480184030008030108403201103955000b060107614940134600c250740c0441e03001c0b20b000400d450305101a11240140d4030400800c0d1401c0440d41c101c916 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 237887284 1250 237886034 237886057
    0x4060605010f0c0f030809210418050906010306021c060e06130509070612020702180a050f040c03030815150705100509031c02091905040c11030f0d060302060708070506010801050408 80
    0x446e0350340c14081c40d05020b03146902d40e8800c07520611881d040400200500281c03840f40003404007c10b20041010b0a44400303681004a5070040d03001440802c3c9550010440c1c291000c960900388141c0180075001c45400340c7c0301804c103003018805c2c04101c0c901a1680c42c51034014103400d000300e00300704a4050310340c80544240424414083c0178444003031039940580e888560024402c040302c1d5441041c0058409044a0045510307160000140703219a00d80380f0300c0d010f80d411690303294a45045603002d5541080140110340c3d250f44007101c0c075009544060710001c42010713251425445e135050380341452606c0c643d2b061060f802400d110030000c420f00001b06440c02c82c171a503401200c0c0c00420215180003441040b204e00c1c1c01461240700607810850200b0200121b803001c0e241006844885c4004a6401203580a01c0c00160020400c5003590f04c441c1c00900a80210400c0009100341d80364006001c651145104480707500010402400b0320000340a100d004080100080c002850b096485001c47e100e032200452 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 237888534 1250 237887284 237887297
    0xa0203040e0115110c330d02130b0c070b0711030f0f0c03030301080c1512070e1302090f011d0a17060108060405030316050d0c0c050c03030a0c06020309010b0904060605010f0c0f03 79
    0x220503103c408220464040030608160341d0030003a5140300203076001202955650800c040c0016880414808640030181a00068003295003821103414370b0340c0c441002a5000c084ca040b07111850740c0d041c420140c10f605580024030907110500703100750805844803d16403013600305200400a081020a24540440c1c003101e84140c0001580180811400b8504c0b82d03001c00d020960400000d0b40e000005445e00c0c01003240c440003005011743c0c00b982a8841d020546400404094402d0101c0d4021100500701507846400b9901031844440451a03001141d402005217940c11070b001d541a00052010700d001d480040090720080c980794503015030341d10000d80540110111400d1201e8002e10601c02e880e00008414010300800c0940d0400a001003500b070800d031428040c2c0c010302841e51400004640090226464407428100580c176010000d403c000d0201b040c954135902106410b50b51850a94401c611a12001175003e007800001011400100807120901004441210103d610666a0b1084542c50316001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 237889784 1250 237888534 237888589
    0x1a091507030c0b010314060a02030c090906010306090f0501050901090603020102070621050c070c0605040807050f030312070512010b040e040602030a0e07060908060a05011a0a0203040e0115110c 85
    0x31034242e04001005021521403074004030401c0302404032070070780e0500902101e880e91540305415003240310544408080007010007886943d81001c2e01a140c0c400700504000840303541e2809000140c0d0360200c58042d03180d03921401440305181401a03140501042d030020001141598000b035654030701805075405002010051407292201110317001c0580da6000020301c06410600141445a044070904a45194400307002058540c421000e580480701480d0051441618000074480c008c8450b101083d014041001020020b03408141d20900548082c0d96469035143c1000b000502200706030095207425404010800c0400318070010150000c4c1c04c024016569103e080d0b044004005460601219004903030b40043c00b0b641210503203080760b440c0d81c2035601c2942d4030402282152024000d0180f002e0712041c4a04d9082c503013401501e8a51100e0046a01c0c1540b181501d13507180f1001d0340440c42d2401c0d2030b2507603180e0550080c0c42d98a0407064000400c0940342c06000641100c0b40d522540444c1c0c2c0045494 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 237891034 1250 237889784 237889787
    0x290c1c0603080919092a2d020106030b0c0318010b091b0c06010305101503150c0513030804060f050313020f0a0b1605150108060127020d061a09150703 66
    0x40310300406074443d08024003a4070b1491b240078808550b030070389140381036505d140140a00507104008551011100c241e544030380d1103104c255607001c40182d48119075803684c022001070140d0b46514000c192140c0c00c0341e00d80c5003030404040b4001446007216081e0741000003c11440e19209500d54025800350004d803003c3c0c84e6811084200d00555481da0389610a0800010501c6000306002040c500541c0091146a91403020b5450000061000415500f80c1c1d0071082c0101420b680501c03071703028051a00b10b00d0040350750358860b03410425070001d84e02420001030030000d06410180844501849041c010304528041b450454098060301340a8010404140301140355034544284a0192003410402511340240010401d1240803000d0221802e100c2d0102280340700c645e40c3c2d03034a4100ca03240740041c0001d07030812491107800e824040583d0f003405101c09068040c8a1325001600e00c0b186002c0f80040c19a10b840e007111401044e0803c2010000410014030506845124a14080c00309161b020b50b5500b115140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 237892284 1250 237891034 237891079
    0x10f0207061d18180d0210020306010207030507030b01080d030b010e040e030c011404060c17040807060b0904030804030e06040605180a0504090503030a050c0313290c1c06030809 78
    0x11a9403080308001c1e8003122070080954503000b02d40440c0c07840c400c100410003650b179541c02c906403030015900c204082d51080307115070011603201d5410300c15034100c0342e902c1d030f036191500d40c040c0c0041364000344820050041c2e200801408270a56800d24060040b15003030780029094418103c1c02d60301450316076401144524040045a010780440c0001b013202403c1003547c40e9941005a42c202d400500f80f51070384442c0e91041c200070003814845484c22155440b169030700c0c41c0d541c0c06150202c92554031009020745941d41e09500c24810b50003034490a0305840c01d490010030034240e41210074420786080c0b0050251a40c4903050752441c2c17441942803104151101c002a00f001e100e80c0c013181d40300307003401d0b40d0000b0801d0100c0030310f008241031101030125455000105074140000c6401e08038640344801c1d820040b460305010760343c102001041c070038600000c100b5000511041103a220030102c1d800255400c280d8200320421031341e160864020021981140e640c00760301c0c4140e04550f84a080601100c1d80b60204552 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 237893534 1250 237892284 237892337
    0x82503020f0925050a110601031a09100c0f030c0903080d0903020f0703051c030501050d080d020912030406021207020d060e0f030c0601090c1b03030507030b060c0106050a05010f020706 81
    0x50207103e240007600001051a40800d15200006041840e213035101140041d14034141d0303134454400480d4504400c03014036007003c018405105445003089040c030041c241d01c180d18503211245c5d00c55803150010040a4240c803c00e004006c100451540100040f800c0c510a8651783c140d0080d010928014030f0800324640580010651200d016061001041080005909508403d85840c03000746a92800040c0c1c12580700740f0901350891444c80390140040c40310320050058501c2d14500505003c07403c400300300790f4191785010340c50070b03840024144800d640400c142c01840e0810000c06e480c0190640c08540080c40d1020000c010b580c541c003180031010fa00f070141d160404404070840b511119402122640c0d4002072081c04451483c182d805484140300d40c901004540c04900b80c13001025080d6000c4004150040414003056030311b034000409941c3e20402440d001031500e001180290410382001015000c40d0b001e141440070007540d907030556401181c2081110a01c1c22300c600d2100c28081d052103c230100c030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 237894784 1250 237893534 237893581
    0xb0a0c03030b06091e031c080a090c03080703080603010b0607030e0f1f170a0c050901080601050405041419021c05090307060f0c020105012306030a09020406082503020f09 75
    0x2d12040c5081051103403001d60802c0032070880d822070100c030f210b482d607c016000040c0d000170303210380000f51024850f03003202200c54844c8000c0205c095403a00c4003601504074103001c0300012106000e002e083e2509005031940c0d0301085522900d041595a4003606850700e0800319405901e00e082c84035a1a84d07854070004541010039800146c0251030000105040041c0c60030305100403412011a4103c4403611929050140344e407039092500b105000103650b8507000070b1480781002001c010206a988883c01820381501301c040d8804054103000c0c020b642442c958400310141e017841408003600400741c081c24541009072515001503661114141181580b00303c000240c05a420030310441e422503032076840303182112480da000b0015039884031100100c001030700180040284980350796040d01c0c6040300013541c001d403942c600080c42c1e4a0359804102a118a0350141800340c20030104a45504141c1c96503048804040303040304445410b690010380601850050b00e801a240c0500184642c00035014546080205 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 237896034 1250 237894784 237894799
    0xa140f0405102103180e0a200c0a0b06100e060a0909110912061018200408060f0f040f021206040c170106180507090909050c0108010b0a0c03030b0609 66
    0x88960b104012400418120300217003510001652462828101c030094550905000c030003526480f4001028003030541d50715518151303011440c2d10f25001c450003804c130340c17036400c001e041c1803407031030818501d0030a00801c0d1a001e0640300189a041550101c50ba00c4403400c00c0315040d44410703040c07400700c4d02071440c1e400021529250007400401500d00d100585400101101c1662000c40150305c42ca894503401d0301c0d80c03814042407a00c1880246100c11144014005c51040001d4000c6040818071004920690342ca00c1e070200080c0504c03000c0014010564001d003001140c00c00c90412054040121a00400150403410100301220465468070300000f500005081198800e050078100425108c2892040c0355001701035491490720100103010f004216450101d49560443c030644095000d0300c8001c29850402607000340100b52900c0520401104500807001048880000304c00500103d0060700f00c101c11400c2807040c0301e28123a000c4c00c4450001d901d442c1c0820010b01a502240070343c000d10030b8072a8031000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 237897284 1250 237896034 237896069
    0x9070b0c1c03021207053603120304120804030210180209041209050d0209060d1b08060109290d030e0406092a020d0804080d0e0c0a140f040510 63
    0x9054010b0001c9414080c0d48044c50346440000343d03010300c2048042415180000b44a40006101d4440c3c520441009a1a0700c00c0c40707040360009082c619040c4202c10640340100510083c440013002e03004124602d0704042c0f10904250310080d503522010041490b041ea2103c2d000e80c042c03040f6541ca140741c20340c05002d590150401c0d28004054404846850300000d500b00030014062030319241c1240000d4010f40b40000540b0b60300184100b201c0d03200c0081c0c5501c0444650609000388100002c0000d07c1d80c00081d042c0303941014500029540130b61180e03408915490780086000b80da929405200c07260807101c21055400740d29007501c40c0036040000c103500c18034140e00011480b03060f4100844000001d2a04011080b09034000e1040030704115843d030059002c0420509518003a403c0715130000d0103000c1c12400c10000c00030040c2542c03503150311032455412510308004c16040824028000c0c01c00117406449446e04013000c10700040c2e2202c46544a41e4451010403424104000460042c040c64440181d07800d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 237898534 1250 237897284 237897287
    0x2f0603010b0304231e06072f0f0601081203190506040b0604090207020301050c0f0f0a0c0605100509070c0b13140111131409040303020a02010e06011707080609070b0c1c 74
    0x700049141c10450014000171450400104082d481180031783c071f801c2200c8198262089030750550b03000440032555601000e0004402c20410905441003410081a8940c10701101604000740e4540861828000348180119026200400c113004c0d594400005456a64a0001030242007913611141e0001400100800c448160790020300a007030080d0002d10554880131a5807189200b00c0c8901040328109010000101e044513000700400d0009281494654219484d82c9007101e0b820f80700c290070308d408490204600e04110700308552140850a188940708215156036150321001005107110324070300302d0204108810018103442e8440d800e8002c110f111001c2400c040268007030240316940070421500080c079501e1b40c402180c40000e001d000000030351907582c1c00b0b03000382d00488071440a40d5210f44180e0300d1a1010484a4024480e040c500c54520b40240304140c01c07e0503e81003585150000c90401c8402200081c9500440340018241a134074a1084001c0d23080c46c0b81307208641c4030352003503501c0c81c00010b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 237899784 1250 237898534 237898543
    0x1090f200604030804090c02070b0c0705011214040b070c081206011b030504030b0a02070602160b090309030a02090604110a09051008040201020d0c06020d092f0603010b030423 77
    0x420000516484602001007069901440c4070007000c0060402040c84286010b40000030312181c1401203a4405403112254410364105070522022035020040030086580c0c0507802c1440c1141078101006101640102041c14170001040a00440c00100200d5420340c070507103201c1d500e1a0402c10040d210a03400c10340c008140070a5440d50300007560405040d12000707588511454032036054684510f4103181d9070300d101140d04020600c0249a50034081c141c0496900d00080080d58019030009922042510b0652440305000e05490420f5100780100111a100012180c110a804403101d100035a21000001c018040104803820305040120300301030f0a0780c20402c0582030754030440c0c0100e60090303484800c503030200c000c0b5800717401a48043c18a00c4801d0240b203203801c903103000345c401502e80304083c071201007554040c02040b11407408500070190484121155a0511095240c410032005d03262000070301c01d408180642070050758000041010856408002c4681c0c00f0040c00844441500301e0003151038 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 237901034 1250 237899784 237899813
    0x11010906140903040503070e07091508091e0304030605060d05030a020610090515010f270905060409030e09090c15120f010513020c0a0b13120f0c03030c0201090f 71
    0x1040307804408120551004001d40381514030140050400d186800700f000010f030742c082e014a0034000400c401081c070407a02c039034a0404800c961100c448a0404030819031500e84102c04414054550312000888244080b007281c0c1141c2d00b000c1d000c106903c60704001801c14280703190040c014071002aa0109044d00451024450000320a520b404141e0300d051020981d1800c03100c0b402c0e00004981c0a05046d8003c440c50000340d9610728180d2480c04560100030443e0703a00c0019061018100d580c200300551007401801c1c0d0005098600744400e10041d940901040320a2600c0d070311649100d000600003940400200012540042a58400d5543c0700039400c00355000340b40400088813000b00003001c00c200004020704940c405010b000540c004520a00b00130340202100c009075000c0c03400c40e4800300b104840002e0080c2c242200012030200145041c06450800140c0300050140c480208204a500701c40c61080391605800e000c03909078260f4104034010420450001c1850f043c00e01c1c034034103229010300d50205 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 237902284 1250 237901034 237901061
    0x10090609021e0906010c1e05070503010c050c03070f140115031211060f09070f09050601180e01050f0411030403020114060102010b0d020d0c051005091305070c110111010906 76
    0x12949800750481000c200b01182d1508040200301044240d48a0309801070100e0241101440005580e06c0e41d10b00310180030402d90f6182c1c06418180000e1800303110783c048003445030400c280f411100e403180c651240115080a0704042e5007245803000d200e211041c3c4100108040009c02c07501c2c0e41c40e00394a10500481c00140c40807141807154100d81801b44000e5000b40c030200700105525500d42e03483d503562103801054422240504540000e030301151905400150804030f0011426180130703800104000702c50413200010030009c0c0810800070948160700360544134140e130044022004140814090b040c3e1103410071182e10004100028140e041d4090080da00c0c0c0000c2124003621028012826122000d008030750140a0500850051900c0c006440c400d80c0310301d1541010550301d000242d56580ca02000e00045100000c1e85203071072034440c0300c3d015842c140ea1010001810681b400601c4400715520060403002c2e2107110001c2680110319058480c0d80010080c070602b41180b1744080540781002d4000c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 237903534 1250 237902284 237902299
    0x1b171e03070f030506061902010b030f010902100c120302030a060e04110108010e0126011b08010812120412020a02041a09090706020a0f17030403050304051e10020702031009060902 79
    0xc511403090041c14020000101218248001449110010700f069900c11080d2741d0780e03240021700340d10140000004049100c2c000150381d0b07107500500070800d402c21794041c2040307c10541d840004070a0300b10412003101c21711780140c890b603039076001400902c21604050080004082040200400c40c540b2010600c02a03944080700c0c1d0780ea80000c40c14000a00a44181030012991a0260890720444416840340300001189142e180c90000400c0d0192807041030010344d0840c01403140200400c2042d942d5035801c02d503180b501c07000c1d01583d0000e110190004029440250314109014420440c1050682d00108101702803155050320154038807000750228052009100003a40845010a03800d08940c03070340e005011030002640e174494a00d08019400c8030320940d0821b12030041c100860103944928401d483d03030390b5a800c3c1810124605048500d0541c4250f15514003452050701c0814039840000c01e606000da2039070a1480001d040c40810502504032524000c0c000c0103001c21a080100d100d8006d131681c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 237904784 1250 237903534 237903557
    0x120812010905150f030c060d0b0a090501240c030c050a0b0a0c030c0201021e070212070303080415090c061d06160b06010503010e1302010c14070303030c1b171e0307 72
    0x3040c000e0300025207070b03499048140500141d01f000300c02400740e80000c402c00070b284500b5000081c00b010003500301d8614503603200c005006c01880050700c1200c0c558006581070032614501170043c6541602180201048a404c0d08002042000c101e1144844da2040c900007191078a100c080c030091021403e0500042e09141c1440c11081c0184210f0b5062480ca5014901100c100402000140d114520803a00481c15410403900d0b08400d001d00b00c081c51195460480d01e08003810003003600a4402207402c0da41e880c1c10071200002e0002c0c0003800c00c450007030a0500031003200842a1070b19030300740300d6a1500003d0010b403243d100a031011549503c00d200710f01c0303250305403034010044074140024051809082146004100015602600d04204a20514055210031240d5580b2100400420b1303094dc125800411306108064060040d101084030310b1410a1213080c000600310040c40110102914407101d010340407032203400041c100d60010420802c440c1c4903512035031003140b65510460b1900c000840040c480c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 237906034 1250 237904784 237904789
    0xf0904020a0f0212070512090d0b0a050f060f100f020304050a030f06111606020f04150804050f0d0c08070515090f070906050f01111e150a05040c12081201090515 71
    0x2d403017051b500701005020380c41004004d5090f96102034212a0300412200003000050b2482c03640318030501c80c000300030032a0b04000d5a13400811a000d440c43e4411000c1c400c080d052070b221050022800081442c001c0164803450006a00350311960300080d0700303c0e401c00c10200034800414403443c2414401c40041000c9010707505540810b004001035800200c0d2136074136030404202d454001c2c1c40704041e2018540e103480d50b15183c4c00c0240c3c3c0d0100220000c100e152040000340030040c44400c4940c1900c2005d441c01d5141030500401d0701441060042c100300f4041490000d1090800040600034050fa80206d080e082000086548000e05043d1a20b280700d10400852014540e0207041c040354000f40001d07a00c0d529002c0150303000260702e0311143c82c601c1011407044016002d051170000320b4009070f010b81480c560741140d000d54071b5801810340000d5810302c0c0c140310004811040000480d090310061000804503807414907080d1040d41d45c8800ea68680c4c200100e041040c540c080b50041c01c6046041100382c00d100c0a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 237907284 1250 237906034 237906037
    0x7200304060837060e0f070e0f012120270d0305030702010f0903091502120301030807020303040b070b06041a0130060914010b07050a0204020f0904020a0f0212 70
    0x200c102c3c03600e400b01407515122824002c28081d1264150081121901e030041c03400d00c040308403a01c1516201c02014401d4141d0840c104001c141c170161103840b03103460010000780400ea0000c6040c2e612412521200003606416072202d00303074400740301e481a201000c2d07198070800c2e9000b400500c0122b10078440300542000f000c0d9081111410058845d0890080f2901c0581e5190401000791003555280c014030a4010880e1007900031b0301c2d103e911004100360502108002200c543c10307080055600c9600c03002003092008007982d04407580001c45035510141480071a003180510b030702141d101c18011500c40200700380040b03401d2050b41c0a0b98200b04480c40d0a48180447c035541401c540410341c8502e8407034030200b2200403072031021851840c1400824619442c0d500310740c0f059100f61300440d030390004440d80581c01140365006041c103012850604040b9210113454411480c0004d01c034507400210804c06030f44540c00c1c2ca0410100800454a4884466024180000c0c01c0c11440050182e54108100701c3c1c806270 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 237908534 1250 237907284 237907321
    0x703080907030b0c0d0609090c030605180c06070f0f0b01090507080420120d12050903070503040b0310090e060403140c190503070f0c090c140304020405072003040608 73
    0x301c8000e64640e850900882d60004000c411712035190480071a11581500440f41c807544200000c114491450400708102c440241000d6104043c08480d9903800000060b000c00203070044552035078401d203502e040e80c2c0700f4148401c001d2101908540d51010300c803001e00000e04031940800c040c08140d4403070904495810044034020b1071141520b545461503e4032040d10f01c0070050140c00259010129440f061030302145000c4c5a0009210800a0511002c503003d4079411074032010085052440ca552401c1c0c80e03008600410340f07490004000a0b804003580c44030b81000700300c0711008001e00c0b24241003607602d56608480560108001500d6203500c4c508140442e6145000480989140e6a5102d014452040500b0069a00e88400d000c0d02d40031645544214800c03070b01c9000302100aa140940040c180e55842c152481884100030030070301c40c81c0d00d0302c0480f54015412a00054290346015003501d14102c02d010303641d4101040780c2d003158078110000042042d580d5685640a5a07510709101440100c03010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 237909784 1250 237908534 237908543
    0xb01090302010f0305100f080123010501080c0309010219110f0a080f0d09080f0717040e07081906060504210f06090f1e12111e0102040f080102070308090703 69
    0x30003000501c0d0303219034000d54022503001c2003046c59560392001c00c0c400ca180d0381c104014a035504c0c4900589000654108061100000740c0000da0b5858000060000d4200900320b240ba80c4c0300000184a0440a604071101000c41072440e0401c1028800020244114902c11030407510941541c5000e0f81c0000411004c40c0394842c908510704000e207444006940c100103c0000e02d81d03200e074415000030f02c9100180c1101e00c0704040184d1540c000c0c0c1003103a805c2010104000500c5001c00091002c0c0011700d0f17400382e104415040c6651180c840305201501e1100007441020841d00d4010041034243c2d003c0001c104890302d0903200741c4160340714610190080c61611009281d06401501300000441b80e4000c0d01c056401035030b05600802d4a07032140418a10f859180b501e4814411894108100687d801141d0306045490030100c481039065025948010307008524102c5800c000c0f280540307400c2501140c0181071210100007800d9518407101e40070b900210300440100311000e00060b0501c200288042c101c9800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 237911034 1250 237909784 237909797
    0x60f0513030f12081314071a0904051806060f0d02030d08070305010609061d030312100806010902090303030a0e0705120f100b13020a05070210080609091b010e0402120c030106030b0109030201 84
    0x551b030f40008001e40d02d070a84116006141000406641e5505004100c00403000c50316940c050079020401101c000920300c0d0030004100b03020001011002541951051060707824011304200e01c00081d01d40c0900802c025414030414680d840140e51052280780640c40c991401d019a0b40c80703800a4564000c01d000d040c000402404072010710b800710088003501254003a00360380c5001000c81000316086001c582001802c3da80c1f00d802c104072582003007007900400401038214100a40070000a480388000703000c03d402680c0702c03030b07098590140521000c4c000b048014010125140c03403140c165200d000c407803185400c500a0025401c80c44d11035000e03c05000c50010200c51032412522580e400035040b2002e644100f0009000d8100103880710100a100f10308640c03203100359460400200151918000e1800c1002d401c43d0442c4000d4500c10303591400c11314001d080c00000262200c2c00315000780205d5540c45080c0603540d05014004015100450682d80d06a4051040d400c003640151600d120381d202c000d00240b031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 237912284 1250 237911034 237911071
    0x10512030f030a0f06030f0c0f2301140d0b030105100503060106050a030b04020409050108190b070e0312120601090f0803030c0d0915020418060f060f0513030f1208 72
    0x404011030b44500b0043d070000d4070618144c2200b08403000c50f00200c940b03155520600051103d941480c030010441c001c1c1e441c1140f4100b80141c0c076103800315410b0b078030604003140010b21580c0c0102e5482d0140010652450344905080340b81e20090300b90b07003035494080e51a040104000e1152070070350205940029005241a91030140e0888290344081059400c05566851080c8140d9840c00217000510100e04007150a5042804250820041160446c02410030a04840002e240d0301e1010340e0220141c101403020f105c1c0900403a0401d5003480c10600d03600320004659040b8450010081d00401c42131f610032002c0e5441cac00d030f03a0690380d005000340b03c001c0d4020700015044c00c848100900c0304101c8101d020404200e0b40e61800b808110506400210075004101480f0707050300510b510351542080310b420701004c0c0c5081d0392421202d00380d024660401c0413001440c02c100e409071049400c0140b080301100101075503401e004170202010700e07084076110540d03040c922000e8400c10009003c4c10604110310710341e40c1d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 237913534 1250 237912284 237912307
    0xe15210402010c0b070315050103020913020306043308030304050604061e1505040b0d03090b070c030f030c172107020f07080f0d0c0807170702060c010b0901051203 72
    0x400100120b0400070280c0d06440040e0114411303900528480d240031481a41c00005a5146101ca4020604152060000d0030f515a03800b19500003110310341c10f00690380d45901d000706010741005034095441c03c00b040001405074110401030421460102c000300f00b2140c8608043c0d841e4402550054206e5001e000824049035160b0300681070100001c40c40c80181748503c0b10401071b140880110b0070b52103010300d010481030402d4010b43c00052011030307030481503c80030340c0c01410b00a807034000d04045140c0071805400b00800d00541c038015640100c054007200b0814a4002c150314120b07101100c4000b103000e80c60000f103c1d000305030303031000e1103000700c5152441c0003030690888218002c000c001140320340c05445e5013855051009201a00c0030101030416a001210308500c2c040c0d42e80500c100300003401c203420011503140400d03102016402030b0703410b80040c281545640a40127401c4042d600100c0060861000481503100000361242500c81003070a0703a80e01d040060000304800c00000325041040380030a1300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 237914784 1250 237913534 237913597
    0x30402011707032a02060609011d060310180c14060f0a120f06031109221a0c09040509070308030a090602040e18060c0a0518010e0d030e15 61
    0x4920345030004021100074940003050034401e040135002900514241d04443d410b00020394000c0341900c8030103c5514002e11980b140f5180760041c22a09020b901040c0103135000e1101c134044c1ba070b2100c400d100684102080d00f0a4800d007000c120380d00c40c103000e8005400c0c400c05d030801110704e5008200c503040c41510030341e078089944840104400c200e001150000d8007065171069a2460284140010f4001c2c20b620f00010350f5a40b40020714800c01c0483e003001400d0390504903407440b800c41100c06440780d15842c60642c850002103824030300c1c400d11090800c811954004094101d803481100c00b4041c503100e01c00d1003038035171481c0d001c060718950b820800210703410500c1e005055803610540d4018586584d803440c10903000c00680c0d8103601001401d241c1c41001104100c0503070003080c5d0701000c510785038130080090031512500801d00440046284041c0440e03024900b07001501e1005814a807107581c8901d001070104031341100440c49a071444104842e20740b8940140d540f1010f1323240c20800741091a02807950b04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 237916034 1250 237914784 237914791
    0x30115111002031e0906090c041803030b0d0f06290a030201030b0f0409302703080307081b13050904050f070815010501080408030604090804080724050304020117 71
    0x41e540000010b1842d52402500c1d00c901058001b410243c00c1480c0b6075418030745040e0903a407045080180045600c00c0802c22000caa590500700000e0040e06880841d00240584001402202400c400c8506001c1d40ea0007404144482d008540c0541d0012095840712141c40c130f01207a0810310808042c401940290300045d5010b10007025a1092880300b000901600c0650f8000c55074502001034903038907030110342000c90119003184404008070b02211310040483e0812445011500b000c1c800b0b1892041030104404040c640203145241e40b0300c1c1c5058040c00d03a944c03d0340c0803002c040c955101d0402c80d200e00000e440ea218900d02d8440140f5242034200226a0f40140c82640c1c1c03401040800c2410807000c000f040002d100440190031004401c114500e988001640802e041c80080d000308070024000c00c0890b64889001c51300007440030b00a0400d00c02c40d028a4100720214400c401022070441081000c141f200703041480c03440031913000d500f0126940d00054500134003052050500d5a51018013460040c0d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 237917284 1250 237916034 237916051
    0x307080c0f0c0109020f0603090a030e04110a030507080928050f030c06071107050f09040f05010608100509011b050a030f18050f0111220f030302010203011511100203 73
    0x34506403400390045036100c1400d44441d69135a154200450810b140c80d85d41003102203035410300710b00d4000781007602ca0b0b408000040412403500b2441711030341e42e079a201191110766100e41545807200e5034400350083c41c05032088804039403420006082c50f0400110201c8030521414140c14642942d107060050111076141202c1300d000c3d4140321054468200040e0541e00506001010503044c5000c000c1d00340c1c41c02c01000085500043ea003440f1036107410f81e8401341e03a442550a014150754a05009864480a540c01051035081060014150360009642c0707200d000c0540042001d80c0341c18006600725041544c0b0504005820403031410318030b00a101415848a4506010075004a21104442103543c80260b840004007619101401e00c6420024001d101d159940208042d0b4810301c980c0281c0c0c041ca03181c0e001e0301103040001090303000c00f183c4518001d02894100c00c1c10a500d918010303020350024080c28004c0c0418140c1c00303000e01d11401c168112400c841000c1c2c034500d02c20712218400b941c401000140c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 237918534 1250 237917284 237917287
    0xa1203090b0f03180304031e060209041d0c330d0e010516020a02010207050f04020408030d09060b0d080405040903050424030b0105070c050409020409050d020f0616050307080c 77
    0x41581e1040020701c0a90007020b850780d0f40e49030801009100704030301011a44560302c01e01060002030481c0c03c0f51141c451400c18a010039140c03e29104001c1c1c4180c0c00d00c03c0c1c0003814407007001d920041c040c00a1490302d120b041a103e00c21044814005040b60311042842c0da40410201014140c0c281521010661034102c6901e14060200e1066815180f40c0801d00321103039901c5041241c00882096401d1000130309201500014100d074000030f640302000d01483d4400c0110f604034401c1c55859904440040c031091382526214202400a80d0040c6010300095031a0350801d40303003800d68604103800c40800c541c01210141001e00386002d001c0100750020084041c043d00700030101d449484942a02c1240b1014205c0004490042030020203503292a8903c1b8141301040c0040c100003500e80e409501901d005950000d85450b0034000207000e4200c00601404a0040c05070092032035a000c6408005803440c54100d548030388a613629000d0400340d038403c1d103000460500114100350311401c1d61710b0300400042e0038103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 237919784 1250 237918534 237918539
    0x20c0114121807030c03122115120303021e0406020607030c0903140a03090e01060203040b070203101e0506060301050906040c140d020c010e010605011707021906090303050a09020a120309 82
    0x5516041c03160f003007540c0c00d400e8480100200301e102c04100a03411950300e4a80125440015001040d0404407112235245448510b8500056212103903c0003d0004201c800410031650402600940c054842126900e0f0322482c220030350051901203800302c0b0042e82c010005a030f2035013811001007820040e10000c0040314840000412a4410300c1e0512110304006130254184030328025250f51519448092402c4c00f0304010084144c010081d5070448120880503a41c89002d44006810a000000200085850074440121a030284000c071130301c002c0490f4082040341c541c0820400d15010034800c0550010701080000c006041a400214a00365103050500d656950035556080c2500316861144007243c2c003040801d60341c50b0902a10100b0030200c0c2c0208001424040024000c00a4265446130603840f0008903240900c20421503d5109410f6030604000341c281c604003010f4410400b0a81c00a420b2101003002003555214940720960f000300401c040d10720f00310f8140da081d02055416418425a000c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 237921034 1250 237919784 237919831
    0x80702030a08120a200706140709051c0b15030a05010c1d0405011505030712061203080c0a0914040209060c15010b040317031305010c090501020c011412 67
    0xe0403035051003155015203825440f0400c1600e0030b001031400d4480c0c0e0802038080c000c4d542c1d111540c0100e01039440c40c03550303a844909128002e031441040550182c09500d042100350b60348141e0f01420744000b1110340039140364032100042501e50040005c2c3c0400e4016001c90b0045400349200620504085d059415851403a1541c6003101c904184a0011503560725000e000101d42d40ca280500721402c6400700001d5041443d10040d40c5403056641c0306006001010401740c7e4010107043d900149030000034054141c50703512145a540404001720040345070100401c016071030182c1690188043c0c0d540f241c4109152171001188504800560380e006607080045e0742c41c0d501c850300103208004500d0001e20320924000c0c1c040301c0881f0164040e40c001c040c103020500c00146c1003050b00060030085107480c1d4403610b410304001c003000034035030000342258a010010003c0c0b40c0c000941c1004c4a000f60280c0319001841001941c61901084100520305410420811842e020301c0072241c01c24800d0603844052008200f6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 237922284 1250 237921034 237921043
    0x10e091228170916140103060e010f080106090c0f0f0e150315030307020102060a2c011a01020304060509060c01151205070902070230030a0905120705061608070203 72
    0x102400040d100b10018100800d14584141c005400c88001c00c0952545001c080340020745001d0100000320600e00c8801aa10a400200142040100e228010f5035030309018100a422441000420b500b00800001c900c5154803484580500c183c6821035165030201c007c440c0c90a0300c04084040c401d20b52401406521a0030f8100e40c010441c5021503a07038280307084403030498505501185c1c40317507000f0481d100060743d02041543e0841c00032040400c005101e00c0345100440080e4007025039402014400309810501504801004603409604401d960443d000498076231046004c0c4d2808608200141c0100d400c20078010900c10316036000000d10300c420498052900a81c0380e00c03584500c0c03c0c11481109202d401e10000c8000c207004401146401023507408100c5200e840d417a008145441c3c0700303001e0310221003882040d81c81501101504e90b10b54050f04080c000100038082ca9000b04181d600100c9885000903d40b0240d40000f013001c2d060201700c0180b450050405a0100c5405c00c00b0f21098006803401c00c07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 237923534 1250 237922284 237922357
    0x10204060e04060e0c0708071110030506010e041512151a120705010c061d100510061704110621010302040b0613062006041208010e0912 60
    0xc1d100448040a81e0400040d218140c00c5405000c00d20400c4c89903070b81c5880205c5502590109140e620380700340381014140381000c1550741c1c1c0c0244030300c2c1c103d61a1650660201e880750071f0989684d03500714602402c0c00211025514115401c2e80420300c18001d171090034816450280c80b54484c042d200e0841015501941c400041c41d8003d020041c1b84010186000582d000458004500511280e0714010001386041c4103107070064046980e4018240d100c1d81030580006418885200305c03005402071910b0080180b404132002081e107140c2c0140030480500c142984400b094030f1130b1005520340c07a1034540c1620080e0322554542e1020003000942039100c1c6a02c200c0140c10320342101d08805600d140180801d88484041d0940305400401101041131203410100054505501d014613032640400c540e41849419081030113507500c98202000300700418500952108400c03039131012510b0b41d90700102d030b10b1301406940b10051600115074641e0282501006041c6409516100c5001c65030130512440d00c3e0901c80d03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 237924784 1250 237923534 237923537
    0xc21010302092211060702100e0a0503121b010b120d0f030e032209020d0207140a0804090c020304090504061d07060c08031e1305010506060403030e0609010201090501020406 76
    0x100010025032805840d20740c0e020b4220380350000b410030701101100c000043c01d0fa00800203c0124a44501601c0311000e99000340e40c0544881e50312440c6030800341018240514051180c0d14810010489080106000c1c090039440c090b03180c10000440103440c91030000020b204c210350360781e0007a80890b03602c40c020a400414507401030039440d28000001020f400c0c0306c881078024142004111641c1346000011a210028018241c410131402d10080428810341907004001c410b00200b400314506900e03500400b0194800e8900201b064074020461342c88155090019151400c02d01c4100009221074010340c2c03990651b0f00c1a40e1409484420210445606032401d56500f42e540700c01d2b164440164410440c03048001c030043c2066460b1a000500000d003000e001000c1c0307030011000c9050000001d03c00d580c14812002401118a000d43c0c00c411920150002074810b5030815000c5225810701d1811035003030780d405070360b4010342d21070000511009500c21804141151b607221301110208400b0310251001e451a0b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 237926034 1250 237924784 237924847
    0xf070204090f08032e0e1810020426010911100302041503020309010e060408030c0d020d02040803030609150d170702030604060c0f020105090d0c081207030501090e01020306010905090c 81
    0x416110540c0440e4100180945d400a075414800141d04404039a0f104a0310180700c003480003a64442800c0c24145444c200b1403a0000c100442d0f4400c00907445c90640f402c40a554103d00e043ca1101402d0320079800003d4240c0340c541c8010021820f02c044098505005400d016150980c2d50036451104644103503010000f80d40803040c000b0041c820302a03070b0799040482d0700620023800c00d610303000d0062101808208506000103810400c07001030760181c030160614040119100c1d03941d6590340c1d440744d01c2240e40c6442842148005204010030b409141c2481d84043c0c0031091005441d0350714401849084cc0c090381c001000d00850300140d134204810b51090303128030070100d1014034451b006000480103180f12010b59040c0002c0200e04607000030786189035041840c1c1665a0740d410300b0100f4540c0709071030306c280e85a03400800308002580c041e000301d81221801481004050fa5626a540c201c0c0801d60f82640006c18034041000f092405012950b00940c1140d080c0389040c406507039074034840102865154900c0d60307 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 237927284 1250 237926034 237926071
    0x30b030f0607030b0a23010305092103040b0f011d0709091b02060612060a1802060d0b03071505070b0711010608010504051c021e070f0e090d03020f070204090f0803 72
    0x1000f025000003883c01242d203e246e01500f4005005215001e0000da040541e00d50001d9204c400c1004a420100c80c1d40d070b00b11480c0d2151075800d464541c02141d06442c00f002d800c002c02d0f42404a8440c0c14100c800c002040d85c0b038003e6a0000040344400a03000500b0407841c444d021546000ea4400c1005000f003100503a90700c00c4a440e00607060040080c2641e104241d464040c00403460041080783e071088841e40e00048501124042ea0348031400540083d42100d808030740d270b0043c61010b0380b0040085000b24121041c0c659103c0740c4007540140c0d103c068000070000d10032a000142035500306600400b00381000301c4a40c90800030702c1d0031a4103d40c4401e002ea911101448240881409603c00e021002c071380c43c9448007400d031006580c50500049000700c2a03d800c2036079441003402c1c080740010303140b8040740403000e80d9525800c01200001750f80c0c000c4a4082d036040e1401d1917000b442140c002ca981505034034100912502000000d0400f54800c0e1072809c411125000007801c10b0307000f0340c810048002d40085200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 237928534 1250 237927284 237927289
    0x3180a080a050703031d1605041a0d060f020c06040302250608060102120c070f090509150c071a010303021903090b09030709020406030203012405070b0406240501020f03160201030b030f0607030b 85
    0x140e90703021900592901508200c1c111041c003181040c88015a2102c000c0d0302d442c0303040302c0100f455001c37140b83c1902c0400c00c18200040414020301480c000d90880702e4000148d84944500c1071a140b0310b800e0400f00c2e01007001007902a10701309034440740500540c1c4010041031058104da510054405100d034201c040180b0100da281c1d0080360182c82c5480c01004549400f0901a0341c445041c1c0a964086005000050070303407408000700c88025030b104d614100b442018030030340050342f030302800103c01500540e168101503d201031028034a0b150599511180946000030540710f42d0701181681da01401140d002055030a901d0006000901459a0050742d942c036014000170690344021905a000741050243e041141d4407805996040f60401c40c144807540f6a0314040000388402d160341c81e02401e1106100d1007490300c20302110100d503000c0e02694058000040803540300c2c8038900740401c3e03141000103c1c1001d94840d60152101000150032030b036260303603041034040c544602180c01a0000380c882e50300c0316290 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 237929784 1250 237928534 237928573
    0x30a0e030f0610150c0804090b21061e13020108060d0507030b160203070807020402130504050a0903020d181701020f0f040501090902030c0a11031e03180a080a050703031d 75
    0x4080c9040c00d1700c00015903401b8520b00c950711404103c0c0c0e858000315000341d41d44092285858500c400b0180e01c0c030702070920f180e403a400100c0708400c000303200782e0f46400702d1207a010305a4480d0700380c40324448040300594019248010003400303403a0020b000c0700c1d4080009104208003800b443c052200d1030180e2500d50800140c008500c0307800380c00c6400a2001070001418102a5441d650f4126030140e00c50f056001e2110741c20301290b01280c4e2207800c00d07051011411040e404041240e00a5081d900c048080082c10f950b050b041851003040402c89032400c112080e0b000141141e074002040001d440c0c441340c01e40810703068000f00140200a940000c04004641e017120051008242203a0150700358944450b101c40a03000b400c40d076506021446c0d0b590941108103000300d8004850035134241c121041015140c40d00790b0402c4400045020700d0358005200b0141c00105580c92a40c0010058035002017200704039117981040300c00b142856111602e0358510407210b500c4800c03001e081d10050203d00e06070401180603 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 237931034 1250 237929784 237929819
    0xc050f12041e0c0e070309020a1d0609130308040510020406080106020606010918020a180b040914010b0703050f040905040b25020304090b010c0605010e0f0711030a0e030f0610 77
    0x50024502c00c90740000c1c0410712003421250307405080050760b540c001c816030151194003c02036104840707601c040f8820509003110790340740054801400042e80d0300018043c01c1b400503109a03207507200a9040100080c0300c2c8410682c418425010b641d2003003000328155040e40c22607000385c40840c130828014085030740d040000035488502442e000361480c3c507000100788072661915a2900d03a035000108c2c1900f09004408607070780c4004005003e03032000e94402103e01d4a80160045500c040c1c100006c48030b0101f24441094182c034400c4607500d140c10800c0d501a40c003035014000b0030001000902000400d075041d442201e00c900d00900c070780462890400900801d25000c20909034881600d03800b010b017032543c004150360950700c0d100b500280c500c00e5400169900b03903050100406050400b8004a0030072218011240240c10038001c0c0b00160720f5000050340c840d02020000c21590740188150800c0c20311030105000151000b4040c2e40000310640103841c02d040d000ca03607111100072000c1e001c00078000075910440d039 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 237932284 1250 237931034 237931073
    0x2100504061e050709030f03020c13050901110f0d0519050709090b010309321c03060501090b070305070807050d031d01150306232a1602040c050f1204 66
    0x215103010b04c0d02800030262804050a00b102d051949400c043c0204030b9040908402807880c08203440b0343d2003820141404882c0c490b203650030543c42d03074540b076082000c1c4d070f0201e54030f0105035090070140c00c64100103110040001980102a020b00d10610b0000e100c1c03135015410315600d00d480c49050011084c03c2c0c84901080e10f040624140382c1c0004251405c403280400c2d0040c0c034440000c0b000c00041d2840300b800610200d0440c1c000d40f41c946080e80c41c2c1c0c104810f92083e480c0c40500106d41d9402c019984140f40d032140500040c0c04109940000e441480208201445040440d0078074515465032450b14001004a001084d51448c150044642011004c214005100002c1c46a640d001c84804003c02c42888014031554403071290807000603049120214886900c1d145124600c0e00481c2c964440071f109220606000400100d00300c1900d8020460f00503400d61130040c901e010060b8240b2006080c6041440100300381800001d144d1303560030f80140001d90020a04449a00b441c3c1040f000301d07441c0818146 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 237933534 1250 237932284 237932291
    0x60109030b04030c0201030e070824010b1602060d0908090103051609050f03190b161b12031e020c16081504030e03070b1207090302031c02100504061e 66
    0xc005405020200d034410b5162078500404c0e0400d01c0140d005c1d00b5060201030443c020701e6800304600c1c3c00001c4041c41c88215010050340c40321003070681c1b0840c0c9405c3c0a0300c585144104000311010740c181385e00d042d1640c4054031652414000342d40c08400c4034a01601200d140e86c00040148903907915014494100661030301a20036260441000703854200c4920485016031031800c0151965501440700e410260345180000b032910701c1610301041180303411a4240312400035181c40032403003849240d501591180c0401c1d1800c0001130350f1030350708000760710405040c00c15498080c1c04032038800d4403c40c4051300c890030501684820700c1c0244242080c400400c040f07481e810412040081e40780001d25142401301d4285090303416119810115040e4242201e0240c0511800c0800030300154800c0c002c4c050710030825074984440c0c40307404048409403068031001c1d605500400c5074251221803115883c60101080c0100c6504038050042102036520407902611002e6903200d280d03c3d5640d40300103815445000f1402007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 237934784 1250 237933534 237933539
    0x71503061419050409080f0f03061c030914030307170a020106050405060a1703040801020705030d14090606012105091005130c0306050606040b070507060e030a02060f030703151706060109 82
    0x3040100107202c1c0e0f62003583c940204105008910313088844203a0359240913542c0d0180d40489055603441619100c0c024296180800700c8a260201d481607119031503941c2c200d40c036242154200513041034501e520350601041010340d00049640b108480c180544800c22602c0c3c0c070401070041d08681300303940002c1c00b80b410a000c115403541e039000706005440d02c0c1849403000c040a4035115280d40940c0d080988107601c005426818410300002429040500800501c5007600c1c0c03001001524034241d070408030035032000000c55515030140000503606584950b989900300002c161301802c2e00d40a40d10f6848503040718440c00c41c08205800340590012000c918104107404607030760b6500c50001440090003071aa250301040181d9078002c12180140f00212072191034008504266441d0b510070710031400400c459400c10300c442e017001701d00884401c0d00141005d081c00c940c803145e0549507000400c0f59080503561104000390030200020700c4080c00c42081c2c1d40400000024a080ca00700c00506818188400b14208 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 237936034 1250 237934784 237934819
    0x40e310c03140d050915040302030601030c1a071e0201230d0c050f0d1104090212090c03190308130219060207050f1c021815090c09010813050715030614 67
    0x48621010058880c0106c5180300110540c0a00590b00700a526000e03980c0000188020055490282c909150440100d0840c04200010314421a070000f0b02c000c1050b480d5107400d94900c20b0340502c2c0c0d801030415100ba10030010380914000c01c02c0e02c881c10114000b00780c01811621074130510100d1441e03400e10501d085240c400d01005405000c1c00000820b498880400411000c802901d0003011190401c0d907e8a44405100314245022111007600e44a480d0840d4803030300c1e000032103140d00b01c0e0842070118449941e80b42183c65a00c004c10108414800303c88400060b01c071440c0340340c0c87d041d00110071042315040c018002c1c1002c000e40d03c4188a0140f803c0309000b96510702e09a0a809084419030703030403040d900c2c40031a8090160000f05d54800c8400b00400c8040b8440b4134806064103000c0398030100f0341c0c0da000b0010005001d011600b5001454030000580039407a040303041d10005001d0b4080b10003181d40d8035048803144204480c0034000030340701e41003044050010381203c0038462040b87c0f44001c888840d50b4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 237937284 1250 237936034 237936037
    0x301061208031008060a06030201020c031c0c020f28061103040e090c1e0102070b0f0f0c0708011b0905030628020906160215040e310c03140d05 63
    0x10060107007000080840c549000c40603030980100f120105494252800e0004580140440c0c17005038051f0090510140e100d14012980b0905415a4005842444a4090204d0307810400503030407600180c8021900140d695055101031102c1050360407200905102143d0b500a02e446030722810a20040200c42540700d0004410b403820b40303d803c0300754451541c504214900e4040300181203238120413564031041070341602e2089210310b510f0a030215910300b9030312036240009114010b41da5200a030180024904240c240b401001da01c42407000f22814540c03035140c0f00d8211042c2c002001d401d0802c0360b50b49010542c2012000004000450182c000341c900400d13511801240f81641928150085480c1c2d5082a0f059055031904240500300c0750700e82c1d201c1040d08400c1140b00318168414084680c0111802403c58100e80684444100140c1251600701565011409440e021108407000c2800b440c2c00b55820000d03988118003c070608002c107451401e140071400340041e014082a0080741d07002400300e03080300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 237938534 1250 237937284 237937319
    0x1f24031712040b0c040306050f0105032104030204090c0506030c04030c050105071101121503061e0902010c080c030403020d0501021209030a05090108060d060c05030a11070c090504022806020c030106 87
    0x19200103c60b500c200b04c0c00c0c503620590b00001c00262408060140b0381424842c00c2c0e0586100343c0854842c2d40c1d0903000c40001c00481c1c0c0c581c0f600414200820302c014181030b0807140c1d07200c0c07042c0407520409860b1000104140c108480040d19244081401c1080c45400300303207000105021308040e0715107542900e40301c10510f0005200c6050041d1580300703103e0642541d100d40082e400c1150190b40d1580caa15003c4046e0441030000000f40d52020049500a00d06d0b115030f80e40268140c50365110a411755499901c9504459280702c800e0105000000168641c4214240510701c281c00041c1d8500c98070b00c0d070700c4d24164040e11041c0d180d4001d1025101c00b60300681150300b4048242000e072500c0c2e484800107800f16040c44c4005240070300f84040d400113103802c0005540a02800c000900540c4159020408ac50083c52005040803006103410407600030b00703600c820782044c0081c007900b25031901c01c061410342c4007107071000c8030010269060400206d641070182c0013070085c00f100203100c1c00c2d20b000a5150400c4114 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 237939784 1250 237938534 237938543
    0x151d010e09040c09020301080d030509070b070b09011e0b100e06030a0b030a02120106210308041104021e0d0609060b09040b030f0109061a01020f1f2403171204 70
    0x41c000300c0c090211900b24940103000d503030010341d41ea41e141c824564455403d0143c001c04241410041810010003003100d0040c1c1d6007070411242000c2c12616007080d0000003800600d141d56031810309490b00005c8000c4000241c194080100e103441581040c0321541c54200d074402c04000200d5205240c560713407101202e0300400921008a4051400380000f418002c0e8110004c2d444036080c0c03070480f509601034026030121124081420095041020b032503110075120310004002a059200080010300e00000c086407100001d4001414110449503405680e1280680b0841c403c02c003241841c0180c20380e00071000a041d4680091048900d070601e960090f028290a00348113940310204401c071078034204001405008070400078420101c060030900c0040c11b0b66203008540c00d004407403420b829400000da52103d040144020070828901c1d0001c0c402040e0f4221144d483d09440e170107000b03000700300c44c6900300c008021504160300180c42d500d0f0001843d5080740c0207040208040c0110103443c08082c03503059009410 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 237941034 1250 237939784 237939799
    0x6010303031113090b10050403050c2106040308160e0d02060a02010b090112060b0103050609040201030b060f040b09090709120b040204090c08060412020705030a080d060807151d010e 80
    0x403a200c04034280603140340418500f40440001680da141c0d5004401612400c1d241c0c56600e158602003240d90303208502010340540d105c05180c18203420410002400e00003e40d43c602903d8000400040c10310f4019901500050300d110b0602c060510210000d10710f4a0207411301003281c2038240040b45040c132010340040c1c0f04980c08141102214009c0d00985d02c014001420007481d907846407804600654402000e580807490951802501e50180c0720789401800700400c1c000141c0e69941c011000340142e9404603401c050207102c0d10b02a4107034840500040d02c81e401c180da8480100e50309024001d0702c0200040c04000356120708000e00400341c494503000701e030080c03103054150390b0703d0012401030030800c0c400401d40c84641c2c40c0028421000728020b070003503100b1181c204414458000c100c0c0e4404283c0240e0f54140c1040500e03c00080c0544000d241e911000440450750075643c0070319505003a281d80c4200041b181c0c0b45110414141d1128141c801c1d000000e5641d06038944000c0020030303c00b05090b6150103660b5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 237942284 1250 237941034 237941051
    0x903030617120c2503120f05040b07210e01080f010501090b0c01061a040503061e0106050c0c04050403030c020609010515040902010c0f0623040b040201051b0a0305091807020601030303 81
    0x2410701c1000b100104e40e074941042d0b01501842c0500e20a0300b44000d440040e0f1181e030282103548180f04011760305009543c0e031414203040a00a189540c4052812244085141d10000200740ca803130800d00d4105640d00d9001080d24004000762081c0c400a1031240581003442c0140b2150780c0111020040e130307010103a500d0300c074075249047c140180110b0300140d0014141c900592001c11001c0010f00070ba400c25070a4903141c1d1240c620b4500010305410900c80c05124100040c4210340c400c1001d406415110011100b0305071800c00172a0031550107407003c0c0c002a0321032125400054040148035008009013008211500d0030680321414003914051591040d501e9103000d006685c85118640b03509030b041142c0e000406402e01e00b0600604901480c00c1041200304100900d9640c554002882650002d006540f544d6841d4011242ca5200a5018941c240d4074007a041030001d0400200d54101d01c04c0e200c40f542c6131005010003981851101078a030101c41564100710000e640882d07030364116907150070f002c1035458 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 237943534 1250 237942284 237942307
    0x30303040816050601270b0a0905131403070c050111030304030311040914060423010b0706060f081f02070f03230a0e0f01020708031608070b040303090303061712 71
    0x2c010702000e0018801d41c0300200354400050101c50b03a0110b080d065100500f0107500002c29a00181c0380c0d03941c005450401040310001342d03080140c1c00403c4216400000707905543e01d0141c07002c80240c0710030550001c0781a804100300140344174090b002c01d0920102210b1b6140d0b4481e624440100020105612000ca0412202641081e80d0251030403200034010703500320712180c1101d1401140e40c288994246102954000d61101104180092940041c04175a0074081a00c8071a800038100b214025924500015000c9044c208080a400e600c400b400007403501c40c140091080310329100c00210340c41003101c08009041400c810a144e5410304044240c00b034000c00312110500c0384441a507000800007010011075610107105000403004071031804009004400499848410380140c44543d401005200c0402030700c80441003800d841041d10500e8039886544034440c84000791030032004030b0303110007a02007010b030140200c0340176002c000110701ea84000b80c242e1642c1c2d072003401109580300f180090054504c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 237944784 1250 237943534 237943567
    0x1e021b06040b010b07052b081f140d08040b12061c030e010201091b060206160f110c03191109060a050f01020106090504030816142a0106061211090303030408 69
    0x1100300c505007d0911814290700300c00d4503040c0c110600051500c070014180c5d5016280040120100b01100706010b0b040031070303d81c8100d04071840c01d540013000e111080700050b000e400070070140440040321503c1c0c20721a51a52682d5070068039140c40307044168001c80c60559802c94503208507400d03103441c4802000150043c3d005081c1404003410006544e940030714081280c0240d42c040300c42507800c8030340d961b66400401848412140040c000070722000d00c01400705210703440301310002410a050303a190340b80e4140000e107001c00015600c052440121001414051030400e50f00c5040019540c0180700d1610b01e001a0b40030a05005042c42041d0347c00c1d84980d00e9100758002c00140028800c00c1026040500300608449401c41e1b04000004165085a503481e00c0b6200d03102c401c1c00a01102e9081c09140d0000c510703240d0f114a082e5442800c4100d2a14031040700740901d40080c0b030075450307413000b146011103020140c4150300b9000390070b003c0412000a00c2d8a000003102d502c0751b00a6905516100705a1058209 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 237946034 1250 237944784 237944803
    0x201020c1209011209050705030709020f070308070908030d0b010906030c080f130203060f040b061c02010818030d200a02060109090203010b0d11090f040b06010809011e021b06040b010b0705 83
    0x40529020b21740d81040720000320441600c4040b8211820300d030b60341511005a210b810f0a00700d100009000380000a40a0100702c3e81144041c18030040d529203841a2514540010f86542c00b0785884030751544003540c0204400000d0401c07481c0501106c120b100025003d060003a10800e483c0103c40005810550302c048040b4403258020700751152410080d01843c0895010741c0c0a40e00b485518000c6043c2d490090031074580d83c91036590805290307074150015a65154020241c00340c0184400d01c005d5001014002000800c0c1c20360740000da80c0c1189070401c0719410000345602c00c1c6080c00c01c0a008030036000189207045507111000403804100c4c0c0d202090140c1488100c0c07980000c0c10200400130004002c0c4080e03000c00c800d0741e25040c29502d000356020f00300401e0360f000c0c1442100f440800c3c1103501c035203a40e5900003c1c1c10008600c058200003042641e6103200c1000d500c081c2d022800c0c019403085034038a6016881008014462802c1648941845a80600c6040302d0004005082d40800000340140d503070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 237947284 1250 237946034 237946067
    0x9070e0406080a0f021c05060c090d06050123010302031b0706020904060f06111b0402070507210b0c0415050a0e0301050c0403050606100203031306140c0a09060201020c120901 77
    0xe148400e00e804a1280e0107461300320311035180015800d640c3c0003140c15031012140c04c00024492512005003030941a4001c2d507000c3c5d00400c102c441000400c5250007114024100240c071102e5042041c1c540c200d035415a8100c00d41014010014080e0341c10429990362003c552540915a5800407440c101000740310b5034000300c1d0014141800000ca41c1c088500700001c6940d00d0700d07601e4031b01034a410010703200c88c3c64000d0444040d4901485d24014185940642800c5221b01c085a01d0a6101c4200344c4040203c0211030b01036805665506081006400781c0507000a00c09207018205400e0110b0046070300940150740c0200302e401b045c002c0401d440344800c150010781c0540204104d040c5850000050f52003408140d819100c1d030000b18815080400020003e078990368080c40c1141c60749030380c0b1400c15451342c4040d1006500c845003040e04505030b0b000c00c0d002c0c80c9540c01080e602e601c040c0740a003104c10b9940c860025a441802140e598141c0490b40c4400081c1ca001c03141c0d542c1c9110801a00d80b007284808070f00c1e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 237948534 1250 237947284 237947293
    0x180a0204140702060907080303040305071505010f140603130b04050a06020406080a060602031602060f0f0309010506180f1b04090213030521090d020d0813051e09070e040608 76
    0x4155015440300307020300c10710750982d010740d0798002d00700c0d540b401240310380311f00c13680100001800300c0d110300081d004030352140300003203c903000c3c3e0040309059400a820003408640002e81c01c200381d244208140c1600041034603280d0851030300c3d991003030f91102c091001a2111942000081c1000424003000c41001d905c0705c011034480d031310b44800901c1c8000c121448144a4500103020982a000100762000e84424074030024001c00301c1d03401e00509810952210100030402d01011890440110143d4401c00719100005014036000080085104820103a000d070f003644002800244803050840c9a48054100c2c10322081c50a80741040c40c5074407032a408092002d202041008498503035a8404084900550454440e246070051000e454006034070103101c40344041141c0b0b10746081450f030301d80b04107000806255115a2070f40340c6030150380c03100e089007070442d5041c4014800c03458040300b44410f99615840c00d00e5110800804682c283c0d0010f03000340107029050301107a03a030303994030f03000ba60281000301c042e40d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 237949640 1106 237948534 237948551
    0x4081902040e100212010906180203040503070b0411010207060206060f040b0303090d0c0305150103110112110c010603110d1a04031403012601050f180a0204 69
    0x4907045515191051412102807100210481a0a00150f55110f0b4042c240485c03c1058205115042c50110140301500700303c3d01c1042402e0b0104c1d80181c1e20303211810202c2c618020b40c100200020016820001000300c610301c107180480003a000c5900c074603228801641c0743c500403180180c0080d40d00c1041030551370960080040d292001d800c2c1d81c40c00d080d800115210702100001560ad11181c0c01c001c00402908020603009400e9510100c107855045968000c8800c40d09440326042050001c44000c08032456170004140514900300e095480c10302164050103000d4a100a40e40d90140d4240b00c0300c68201a10a801455400480700c80d00c500c0a40240c47150308005001034080080c5c02c1280c91886203803000850191084440d55110220001d0410340e4036039088488510a906080178010b11260520f8256040510001c03021506264191903e2600f1030111010b9032207414000308 = true := by decide +kernel

theorem cover : BRFrame.Cov 237769784 237949640 := by
  have h0 := BRFrame.cov_init 237769784
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237769784 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 237769784 ≤ n) (h2 : n < 237949640) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
