-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0582
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:34:28.994624+00:00
-- url     : https://prove2.me/submissions/fa1001ea-cd5a-46f3-9135-62bbee2f31f4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 104496402 ≤ n < 104676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 104497652 1250 104496402 104496439
    0x90601080702070b0c030714070302030d0309020105040902180d03030c2a081b0d0f090e2a1c0b01170103050706050a0302090301140f061e0411070b15 66
    0x204494201c0940e10444041100c4c3c54490010a00b802c0e21605072402c100507540c0351030a80c018a1210412680540d07401e00541c9418407811010010600f401c009003446a40080e015020b98811303507030328507030201d08158a40d0240101520118008244004127803007031801600402c0d04401d1000003900710a08034564003d1200041544000710300c40c0c290015441e92000480d91181c1c80f150f2441c140700c2601090030404021080c00219540c984d90b40300505118010264007080e4445c900c007c03402e0080c4a001c0710900c40340603030302e4600c00c80300c0c0d00324100321311305240340c0b144c0a2005114081401d645007014503e9000c10702529090307842c0080440980e800c20742c821000c0c0400341454004c04410000140503500a040800c2682409400c1000360070020f0b0071505000704420201d03c0143c10000c41e003c0081c0700b50342c860800c4034100029000302c89451600c50036822441c7c00303159200c0514540c41c82c07038019180455400400c4070880d2403c2c03618407014603104c0d50054041c0e52000c2403007201c081d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 104498902 1250 104497652 104497667
    0x90309050f060f0903070f060207051516030c05011b1d030607050d0b011b051509010204141210090507031101081509100509010f0602160503070e100801050411090601 73
    0x141c024105030400c054800d040080e540403520242e41449201c00000344034145010403001458943c01404006140006201c101622003102d4a20001d082100510051005000c203840940516048100c20540c5c5807640c01048807072040a045807e0500900a156000308407030b070710241c5c5000a00c7c00d4044c540a050740d80303005607240c602003030090205e60403080d100c1d07014664400051606100100402501e2280308480050035159a0000070510103126502039000d82c0012801000710f107040d1400180c840d05501a0000310701c02c2c1640da80755a82803c00700316240301c24a5406080241c1e600d01d1510326031b59400361108850300c0c4c0003007168140d15805000384a100301880ea41456844802c5410403101c140b00400003851405d001c4808210364a8031503020b40640802710801c1c2d84d5a0910300b0107854111048005540304030801000d22498a011902000b10381141c64050705075180c121000300c8802080e00940780542c40c003400c0105100b00e4480c54024000c00381d801254036266800110303800b1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 104500152 1250 104498902 104498929
    0xb1006020f121e13090911150301090c02010f0501080115080d05030f192903030408100c051605010605151204080a03020f07050105010311031c030b0409051009030905 73
    0x4030707007070000864098240e54910f641901c522200b5150000e083e41411500129030004541c10740c0e076020901c2046a009014200780d02d00b16084545090805010000c621050040441c03560712000710010040c000d401840104605c0c080c1800311b036844500490003032440000750900140710180003d00d4030404102d0503040b94542d91041d00d19a40d94000b500d003020094000304405400c5d01346060700f000f1070b21801c3c4d61110082d04640c01600d0b48241098402c0351511038030303c41d8004100412210f030f4000b031140c0f401d160201020a9140c0b40300c8084ea03450140c840c3e4003050081d0b42001030704004040d8010b005a8108654502c0c943c000f89035412080e000700c0050b00300d40584c07680850041b03a0820098109003c00d03103030240c82d05010840044103070f0401402120039030344400c014410055600200e8031021000d500400310001e440c07056074540c4400c20041401c0c15a0340400300c0c400e4449400c40084035800000b240c001c01d0130301140c8002450328403400c2d4002007503100085418600168684103d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 104501402 1250 104500152 104500183
    0x60907061b170d24060f021b01020114010905041502030105030a110321090306010918111917010605030c030c060d0608010c020703060c030c080c160b1006020f 70
    0x240c1c08956489280e40700051540d00003200902400d00d0000803402010f0b005100982d403c032544190030401c1010318038a0304603100380820020180b05440e40007518524013410051050454003200005038010f191003042c0b2210301007150000b03d18401241c01c6a4050303807044548514244940d180b007001c9000c02c0c06041d5164101d0048130010590307402e14110754800050030346103564104201c034101900c810702407105080020416010500d0280714a83c0144003200c030500c81c41c42020507843c00000710f0000104030348882c1d600540103848100054003080e6141d040601800c0d110b42c000d0b10405c0f01010780c60129800c00300003142c1400c02003040901d03800040c00500031004c009041141507003040802c492400e64a03000000d07514400d0181c4851007260350040c04042e404c5081c280266200c90700d44805160500e0011481103902031180b540c420ec440d91040d4a0740b000d913070f50300c03900c1d034071a080540200c5042c2c0c03d00030703000c00c0d44290600300e42007034003117660424100010a4079164600c00d4940d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 104502652 1250 104501402 104501447
    0x702070e070c0f030e09010f0503011a0a0510090806040f050105100602070b0d020c0a0f0308130b0106030507020a061d0d020f030901050703120f020307080c2d070b0906090706 77
    0x2100d01c00319020561080c01c050b1719690018012071000d101c00d81c001c82001181201c1004070382000e00c0365045480100051300e4184c4034100c042103104c2e0b011312400303005000c1c1ca820044241d01c1184800050607071032081d00d050303041c582800c1142c0c412095054400d94603042c00b08085044840c0c0080031900660040c1c02a1450030640340c0300e84d0001ca888038480c0d41c0070000c880c108002031011000441c85881541c0810300f0608006110200045c4407000303d05861021070045088803604038115001450080f985a07540f4ec030483c1417410344078004240d0307410042c050010011020092041c07018002c200e420f07032529441c08aa84448411018039540c000304035607a85540b00b90f000b020070b28060f04050031482006a5500104c2e0316071078030580d0865000c4144a00207038820710b595001503140c40020709000500707004041840361114102110410400e414500705022400d80c3da8240c0c006000541524040074a40c2c1c613040215803066442c040c0b80c00c0401c0e580d003d1559401c0301d0312180c50b101d2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 104503902 1250 104502652 104502677
    0x606030506150a030e0609060f010e01060e09060f09090c041802060702120a1407090501090c050d0507092102040b030303040b0403110709050a0c1e050f07110a030b0702070e07 77
    0x201d54800900001019160007100c000c5c4901004200d028800307541c020101ca140c043e460f164001c2041c0c020540d002d510b42c004200450380300b0030940c40710104542520f415124280006c44100c28880041d42060f03002041001c150800324100003140000c1d0f5041c880017030310800d08190405d15403030084d400034051060354050b05166440c0f107810450b48080341e8188a950311903482c60382080c01602d94950041c9010b02490855009080c01407406030801d100503440004c0150260040c21080c440d8999140009000340e845040070500a14130040721600101195298003203000b040c074070582c010b81c10036155030340600340002100d1090780c1100c200455a161a601290903072030b070022901140c030500d503000c41d040d038140c4181d44c0a16050f500015062511705000380440709120142480181841103400003035400034100c4481302042d211150382ca00141c5400030b40071901c0c1c14183e8100c4403040e000f004010f00d1010950042000b40c08450741d081d81d6841030040030f002180e02c8400a480710051a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 104505152 1250 104503902 104503939
    0x201050106120905030909041419080403110d080c07050a050d1205070305220e13030203041806030c0b03060114040605090d02030a0b0c0d0e0c0604120f0501090f060606030506 77
    0x100700c1a0300c0360f005d881c684049180001d01c001e505030740599482410450515200f542000340c060fa080c0c84d05990682d0885988520700306000340d10028040d5407110804107981d54510f205040c280e90b000710202e844611075100641d13a2000da00036580545910382010400d4038162030b007404c0503680f18030344800e0780b004524100c8581d00441811028000c0620403862114020104281c0d001403403402e40711114681190002c2c20400500f03008094500700c103030b50000c01d501100f101e066401c0801c3d4100c3c0d2403150803102c001404954005002c90451001c04281c2406500040d4080d52090fa242c07400d8400b4038100c1d03005880356104002c0410010801410b05042c00065040550f0004007940d402e14001c1d1242004042d0469208540c0403001030300b200b80c006031744a00721003841054020315030050100080340061085000b071541d207426010407841040301503183c500e652035101c0024000200740b843c022081d084041d8084480608000c000310b1605e100703100d864402d48009081c1c103840b640c6c1d82c001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 104506402 1250 104505152 104505161
    0xf0b03060c190203070804150806010503070906080601020a0c0b0d051006051e0405100804021e0a03082b0504050118030c0b1b0a08060a0905011a1305040e011b020105010612 76
    0x3842c00c0d80818042a40483c18040150005000c0441071080311418003c0041444600400a50503c142071090004980d80001c1d92000c2d5419418140b80c55240c200050303203440000701005051066403000401c2d45000c0402410350b56000280c140180e4030f0302d80f903080300b00000c1d010340f100140041c405142460107081308400e91187c481091480d01d03848201113014195940d03c0074001c43c0000d800e000450400200403505a24055000703c3d0b0008100c00141e8015118400030b003080002007000c6507000390404405001341c1c0d80e1a8401461540040500c0142c401250b00752407951900001c00c4031408191110700c0903a03455a03c02682d04503a0359110250040503001507a039909008100f6111240704004161003005520784082a107026010454a045150080950503080c00300402c448602400e54410b521700e6000008c0e02d41c0823507214081c0200c50b80d4400c1e0f074000d062a0302030318070746019400072030b4880300085540340e24803203400d050f0709980d0280304010000c0d80f5407548984a00b0a68031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 104507652 1250 104506402 104506447
    0x123090a0b060a0b0a020c03070f0b0412050c0d050a0b01060309110111070e0901060905061203071203021e031e01050906130b040203070504080d14070b04031e030f0b03060c 76
    0x10540c03500e9100c070144d641a4021100303860140e8007038503a0101d24641001450002d150035014200f45600f00f06840000780150b00c50f805d0b4001030066a8010043c0501c491000098042c09400c000107040c10881e0b80e6a00a22040d114600544004036455109004000030a508050700c10f5007040c0074401107585004030200041c5030300401402184696800e21600d004204410000c20f0407411700f030711801150005018188542101c0b01d0021030b42c50044140c400d4150480030301d0541c140c4e6240c05501920903022400e00c0d0040e60b10f0a03c1a0b0780c848406540603110030026443d40300d281110301e4003101d0b0b00307006440d440101200058070030b2400403d0803c42e0031402d1000b18240030000c0108007030b40c10170349689002c01c9010070244040082004861300c204450302e800000440d0744141c10101340305591002d09200e20b560001030a01d40a0b41100d0003c40c0030740185203038495002002001441d80104500c412420241640d5052500080180c01045404801d524192890b102c8443d070400700030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 104508902 1250 104507652 104507659
    0x302060f15040e2a030a03030b13020301030503040303030c03090201021c05070816120903080403030e0a0e0f0405011b0509062b1b0302030403050712030b060c0123090a0b06 76
    0x2900c1280c1c1c0e031120b0207922043c0f503c2030028214852014030100c00d00b66118a01042440d0701225001c0c180d90001e54440c41c15010705000401d14600d50106038070310030f001085942d0f540000000820050300100800c02c0780d000e65002c01c20b6820340c0b02c085040d213042001c00713401a8018036440079200358a00c080002c0710101d0920918110550b590844550481c80c02c05040301440f10b088000d01641c04020444080140340803010340e41590307035082c1103004030301008c0c0406c001c0c01c4080c04503849940300c940142c80b034220308424924140f003032224128000c90342121154200080c0104103500040d0030401c01446449060903e81c0441c18815240c0002911500341c2800d40d01e410310b01a426204892900c1c7ca00101041d090100d0b01a111014040940c09040502c10401c00011a03440b0301a20794213680814520b99003406000d045000c0c20000a1045d4030a80008084a60f280158480c043e01c03200d403d101c85681d80884040481d141080320290341c5038204200e400001012141140c1d40460002c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 104510152 1250 104508902 104508931
    0xb07061d100614010807020709050703060b03091608061603050603071e0812030c040302010c020411040611070e04020114071403040902030a1b091208040b191403040302060f 76
    0x8045451a180d4044407407880180d45010501564038640b43c1c0100001080c2002c0c65035081c0050300030340d10b2583d841001520740d51500440d25070b13403194120900030640411415140d04040d000d180d00c1d40d490310441e9540c01c0d040080014a40b10105c1d9a620030f000394861440301180d50002907010300b400400f01036240c02100c20100d00d072001c0301c640c0032421940001d0000b801f81840a001c2c58080c4240c45030214100c1070040065002c000401c94095039030a203842c0241e00014030104001e40040b82000324019008503000c0340b980c1e030042480c178242c9900c9003101c54003a07540340250b0060744183c5004c0e0000b8058000b081c0003d01017401400c20310300c1000000704c1e4902d0006482c2c159009900b01c00c2200390000144076010000d4040c40c06014400c03040c8001d8150207001c0609106d2030b900c901c402d4640300403500c04c01d00031003074161002440b251030901e654013118104181d24001c2c0300071103800b00d000c02d40e503010040300002c1940c0c86140d058000b00683d0312401420b17040301400030a00002854403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 104511402 1250 104510152 104510201
    0x3050a0b013905031902010501030f080f1308010506041107021008040f06060815010602010506030c12031b0102040303032412060b04180506060d020109090e071e090f05010b0706 78
    0x341002e020300d1a0003035000d0740d00c0d906944501085240440400b00440e8180300051000c03a040e5010741001540c001400c0b69600410310940c07030140200041000c42c0101690000703040141034024034801c0b00c0c204c50801500c1da44207580c030030a001c0e0b0748001e500300700b03041550111203025004a41d0464040d2151406091003951108103440058100c440c460300815800c0d1203800110f6030842c05441140024012442c2071030119560b41446c5400c144910300e00f960161a000c07081c42280ca44151240302e180d1503d42662089000c0c0d4883c1c841200003e1074034502400e129402110148140c0882d136004000507d45858501d540d0501c010540303005540d03c00b0b00e4525960b902c142c0d88003800800d02140b800010382400c5003019402030406004840710808500140c1e40545a10280c8100200004840310700700403140ca0400640c1280c0140e4001040030a503800b0300f00180011524103020034440c0724800b040c0d403070030742d44203110328003a0240a0001400151594104000c80402a8488030b481040b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 104512652 1250 104511402 104511497
    0x40f0e0f030d05010e090d030915111207020609070303050903010b13140105060a02100e0f2505041116150501170606191208090604060e0103050a0b01 66
    0x301005200030307070310016080480d414180102c2d40185022010302d9850328194801c0c40d00c940940c42c010f4105035543c4040d008000900011100420108004001814080c020018150f00151144442042c0040010000340c0300042c0c0510403c0070300d010305403031495650281d0780c035041942c0ca154155200c180d6200d49031601480c402c17a105100c4404500003010381c13410344240d001a00305c03074050001003200886c0c03150002400c03003100201c078a0014141d82c800080a040003551031030101c05000b5604038411060408d6480c00f0350402079a41d001c03a8503a80c00030002101c1c812091152015428032420001c0082c05481035019405003981d0b62039036542070000801c81b1400d030400c04103c012041b4965615034104500c0d0707807001f4251370030086202c81000404240d1620b00c501401445003100314402c210070310702030300c00125000e40307030546854503800701030040c0c1455000e160000e8034100003c2d03080d82d00c90041001090040e182c02c80f0b241180b0302c03544070000d00c191070100d001c03040301d401c11131f1800d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 104513902 1250 104512652 104512663
    0x1050f01030201023a0e040c0824030a0204020307050702010f18170102160c06030c020105060f060f0412060b0405060f100f02010209060d05010306050c070507060f0c0210030c180f05040f0e 83
    0x5c885507070345504010500200310450b41082e12100801c0b45407400c10840d210515504154040d440d04551a0300002c0c400007031508000200007500b040c0084203205565030442c001c2c1c02d000340f003625100c141ca1400d075021607801e5041e02c4010003000c0d40d10020404803212080103482c86d50410005031034002800c1070100070035807811040b5403201c0014001c01503a0744c03502c41c0d1141e849a5100030302517402e194000951a40711000024483d46002138602075281070042218001c0106846171340d1007101d00d083c00f0f0024010110518002c60600001072200d1401031a01c3c03000103001042d00401c0800190201d420314071040071a01999170030003141b80d10350740b03510107001c142080e04808603d66045241810170344001406060354002c00b4410040050030218171032056a900c0d18004111200b041001c0709c440c01c501134081e410950ba41300b40c81c0d0040e03050f00443c440302461b03210605695010710940380d0b602414440d401c0907408050f0140306d2807401d5008444e200c0e003041e101092105420341c109080c030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 104515152 1250 104513902 104514013
    0x314030c09090906070210022a070f060521090316020103150b0408120a09151823060307020d030e03070803011d1b030a020d1b0504030501050f0103020102 68
    0x582c0309400b00141103604000c4643c8861f44900190704196840c6140c9254285808100445203605010040703422010803030b490041007903900320f803071465403500060525030003902c20170503040d400d08032482d81e80c0564590500412100004504c0c1c02d40026400310f03410350309a000ca0415440b164901c0b10244450420005080c900c101c181e552890007100d1480d0120640660f90700e00018130007085169005400d003011684082007030171690b07911800c1152001d074000c030740390301d00c410201d4045501848492111010000c1060f0b0404600c1d022080021a0004a0b007210040e807000140924035446500708010a0f001d0000300d9040400540c0d030440d07103070400d8101000120020310004098031030320620319080250304c4440c614422102d4800555071000514514490b83c0000740402e1941483e44841c40403040301c0c132000b40d0305010313841c010010340c0a03104c141c1d001e40c20303d408100d5424192080e04c0c1283c0d4141c0092a80b10001420240a1034444c5803803054048003000340c420811035034103807403000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 104516402 1250 104515152 104515171
    0x301060e0102010608010902010c0b10080703060b0907021612020a0305150601081509010603022208030301051509060405240705010b010f020a1a15190515070314030c0909 75
    0xd21990400080c2182c0c06548103000503070403e1a41e0001d40d03001003540290310307004a030701221503403000c51102c55070101da84400c0b2281305004000050201039804069026001c84010885480710b1204130303918003101e00380e54014030100004103d4016030b101c40d00d4415102404030343c40305036203403103460a10443c843c2c2d2403603110b011000c0001d203690181d9180d50200c92041c04801030320301400840c101c40c405000f1403041c0b40d40001c40d0007801e03c0080482841e420940b441c4032040c1c1d12521aa43c03240c0003880f503a8000c0c0200303101d16960765803510940d1042032026002a04252070202040a0101c020b8000c100294503046403172040c804002c0107100d2a4094800400c400d0684d100041210103000000c10441d01310b0900c21300041c45a6102510f03c691041c211191919a81103140c82c000b0b41c90f401681c00b0407005c80300486103030304401280031143c0485040c40b525001080c600c50b184510b0358014000344140150000c81e0704818040c540000c0300c04107050070712048201160000205a600d441c6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 104517652 1250 104516402 104516417
    0x4140a06090b06030106050a0c0f0b0907030c050402040b1e161202100203071d03190b090607020a02030a08030c13120b090106080a0f05030c1504030e030a0b01030b0402120102030106 80
    0x1564078030340680402c1c1c0e442540d580f4515807620f00010050302400c40318404000045c8005420300580c070b000e000405401450b880032070308102c075900b659942c8902c0304540c605103451001032180b403e803094404030f440d0b20a0f1103242c44043c840014202c440030501e10701e101001d0000c0c81d07142002919210840744030341080360048180200c007134940034080b01c02d8079805004000708404c0c070364030116260140c1481d241c0c1450310085000000d081540380008644031100c20610842031000200341c1500956090301590241d40302d242089880322440e001c0a501a03200a43c1e010000b20050010b550006c0340d201e071141041e6400803552096450303640402d05200440c442d030810701c03500c0340c0d001c0d40180c070b180004c1150354a070111854590343c03d44805400700d180d80c400c3c002401014800c0754807942c50300090350f40886107032407045030000c0d00b690150002030040c00b40d000300e410006070500b451500300d600701515a1031903075103074a4104000d001700e8000d40d201044042604003400654064481601c40f601c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 104518902 1250 104517652 104517659
    0x703081c0e031314010509040e010f2f0705060708190c05071b03021f03180c060210020c030405040906020d0606200a02060304030c03050c060c0a090b1201060e04140a06 74
    0x43e082581a080881c1c019200e102206042ea00130b41140c10200c0103a40210b021000454518010f0031030440080006090801c920780b00200e10300e4046019050581810440b00d202100f048240030f8500024103c0d4030202c04107050030701401c07045038081c14cc8144213a0490305803000f4401d4400b0305000c0d1000c104082000404c01000032103a03812004500a1050315074507640004195007800007841d00400b1703040345038032070092003030300516900440140d4120f1481d8091a15000001841c446d108c01800b4921321442d104034207000b1101251024401142020708220812009000010049403800c0d0300b00288045450140542002007509840309203000c0c103408400d01411500c00a907007102e400c000130307039401607403540103032a04243c161038248080040340c9002d030380030b2245500d0202640b2415040015000c03440e0001c2c060030109640305d100c810f907505404002d0f8000c1290b11011182018014070019100c2c0e08078204d41440103001088038400030004050a000c162613004446072280401e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 104520152 1250 104518902 104518927
    0x60507030c0c200112091202070e070c06150302031005011a040b04090203100e0c0403051204050306130819050304020f010504030206030109050a060b040909050606030705030703081c0e03 82
    0xc0070241c4090500c0e04511001d5914200340584101a621845212998503602da92140c4503c0899203041007003040202c01504180ba40000e88140da14010b108070607000c41c4010b8407458282c040e80d0b19031210003000306190785000c06000280c4055849500c080c40000145e0740c204014081c01009510001d502e50405543d1100c3e101e02000b2404e603008100001c002116600c1c0803603080301d0740312000584a841d0805c09108088a81d8010400000c5a80078489010030200c0144201c0e80f00340f003159215100ca001c88103481c000c2d441020f5154000000241a19444184501c1018400d04902d4a040408400813030f041041c21908400100040200300841c1060740b00a0b40041d0242441402c01e891a40021403503c01401481e000ca074503a400700e682c0d102c442e000038010306030003100181c913a501c0e490010001c003d659401e507620720981010542034103012850809a800140107000c0e0542141c440b510f083d801400c00c1854103080d50003912040c5914828505900e08490146a6400c0e81c641070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 104521402 1250 104520152 104520161
    0x60501020309060403060e03040b13060305012c04020f040f06050a080a05030f0c0c03010207080a12050f01060e0117070801061202090a03030c1505010321030b1503090f0a06050703 79
    0x606550080200d044a40d60300f01c26a81101e9000c040032544010003150740f4294092540304031030102010488540d040d2290015a007616160b54040000c0ea9072840c03030521214407449400f02c00300450040441035080240e4a540c0680080c2c00365103145103100114041390994814820117503a24201800a8902000098000e00c034000041074000829219182c0f28403035000c00c04140b10b00003034810015001800f1140380b03080010000c544605071410509202c0e809051030a00085d40c00007004031311101c034442e40e40075145004a0b104103a003442805d48071061710541150602030300812540d20304c02e81240c0d091058669696140c2e4039490004060511502c50f181019014010310a040d62a101d9089010840b80c240c502200311240908120405040803441c0c404110b0070903001000b4803607001e0021444801c445000001c008544a04500729007050514944c042c06504000320b00c0c23a40c001c05150400d0180c0b0a0341c00700702404900601e40200010211405520740c0100050b00d40c05209 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 104522652 1250 104521402 104521409
    0x30a090c091b110606010804050a0602070302100605100c060c0504080102031512030304111009080d020105150a05030703060b0a05060a030c1206052206080a030203040509101d0408160803070306 85
    0xc0201a0080f04410365460746030040c801410403035220000740500004011401c246038116404541c2c1c0c4103581002074554141e40a140d080b20700300940050a824541348074035910081d503458500c41880d540d80c0402415100c00800d04110f4203000200701e01100384010350041549504100303500d040707001484421489401d07501800c0c0c0080c0200710108040008001940d034003143c010024044441003600d2030420740c0c000d4540c501c14034a0070001503405612141c081d0301403040d5900c1c21036a500400c80804014042c007901070700208010800100150008040c1a10091180c4980c42e00c0d50045806900a04802e800081c4c892101d4000b45401c060205809000b2000c2800f0260411002c03030303e0012050322100e030f4030404c00b800107071980d283d40c00800501510015604040300d2810002e540e41c000d0b0050301d01c109001000700300e0080241c6844011244034906a010911241e0040881140300400c25161190100021101030520f2a007404c1018480c07000c0c180c8906000100074100c0d0780e07542 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 104523902 1250 104522652 104522657
    0x80708150a230a030206070f02031203090d0e0a06021915051006090815041202010b280b1806160f0303140a06140613030c06020616030b1302030a090c091b 68
    0xf0020302c050b0700e5680841c0d140c80e8200204070414030140c40442c1c03030170b004141c0c1140c4c07119011060040c0040c01154000c5200c41541da030403804102002003081541440c03050340701582c00345c80340c0010030f4209410450100e004802a082403051440030505441040310501d5607840c0c0684103100340c80d004114a405000180e00503e00f8249900e00802c6c19040648042e2500c0d4040981018452007500701e42c02d180c0e8041c0102040701902ca00c44039104105e008082281c00c000c12001c2052940101510590540e458002d54001d0820092100300d6003e0803100e03d82070f40d01d4020201140035003102040d00c034841c0c0c1d40083c1c0012205031b908107050f005401c80080905000003048040842803000e1041001291940e5441080700f0b02c041c1104440d500c005c107403805030300e000903120343c011810074030501d07107000c80c100e100070002c030308804407040061603d03403240c1c04540c0d111003140143e005c0e650119081d000050070b0065600c5c0da01001c19140c0c80004140d885982151400e840b404a80c40020100d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 104525152 1250 104523902 104523919
    0x602010905190212010f0203010918120c03090308040605031503010911040b060c0f010b0f120a0b0c12040f0212010209150304020402040e1f1203080708150a23 70
    0x50307568030b03190a0004201242d80d40004807800c10f540e034040000540000c2e440081000300110f01c03034040139400034880c5009a41c0342a0034001a00700d1041c034040d4560b400040103e60050404040c0c6a12041000540400441c01e00100003c2d08a8009202401c10354417425203901e010380c1d500785d0002c1100304881c0a41d041202990004002800d44100f03040211800314400c0c60080c00b08000b801036101c01c106500c100c3c0c908109100c0c066000240c050402e440d400744c0e064a141c240b080b189618030940e00c040d440383c0c4d030b01c0b0042060315485640100007410180c0c41d00300f10b04103961001e60f00341d03020b45008480d101203800b10301d00074008041c6038200710000d43c10200d1135400640790b9000f0315036288010300008002070441d90380f42d0444000d0700c1094040b0810f13040c2540d810001981d20700f021114980c080fa00407507200050840c42c01c002c3e0f4140e442c05001c0e80e65610031140d1541c0604404644c1200c0203d20400d56a031002c1b000280c046105922740d650b000200003280340f440c00b03071014000c0c0b40c0c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 104526402 1250 104525152 104525171
    0x100201091506060203090f060f0a0c0209090601050904080f04050405010b0d051506041403010f020307051909050f060703020a0b09010e0106090204050102030405061333320d0e07050109060201 84
    0x1001b03480701c01c5001c031f4407005280c041c000818010710030303c003100b204080e0020b40146025003017145c80703101c10f009407000d06080d0f4810051aa5602e006c0c000c0310fa100c1d1002e0000f40014003941c2c02411010400c041302c9080c25a148081410789500382c00c900d051000218429407021024032540d540b10500340d2044c4400001c80010610500c102c3c0641013029041003600010340d2800d406c0004c6507810188c0c215613918141e04000c24075040310034603007030030100c215003441014802e20b0140c0c00d03100300400412441c4c444804112065202d100d08900354060895100c000c034010b191024032408410380046040c4460044e00c0382181caa80e00107201076403043c48148501c3e6800003d43d01030315001d032401d56542c0c40c0d001c0a0342c00c3c408c00f039101d29511101d0750481051542044601107180c240c0d039550340061019580c05440404a60298036a94003020300e4100300d283c0140d5114079000c00d01c0ca201c40c41d03c204101c1850589031100300c2d4a10651114004119550740802464002c184900c000c0003600e04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 104527652 1250 104526402 104526407
    0x1e13060e0d11011413060302040513090c0501030e010b030615010f02070e1611060a020a0e221505040f0207050f0607122a020a11010309050303010e090c10020109150606 74
    0x91620b0001d04115a02e49040701e603070f012108407030849101500b450b002d60780d1010010043c0d40a400381500410f0984806145908240140c040840d40700e0342404903135043c6801100100800d84180c0010f64841a00c1940b5490a10000b40500030903290120501c280100141c00d00102001d142c0465001c1a000c00c8101d61090702c0d140c204200b4454140e00350001d0108944680c3c070507402e560075002c0d030801e000c40c4c1046a8010310441c0a2901c6270707075558403001c0401410350380c50481442d1aa08400d072200030000303654021001c0d10072155103030000c651203001280844030701850450710580c1c00500442400000c00040c5100c00d05640180380d50301d0b04c2c080040c903514441180c0105182c40b0348100103480e0076903480700e42551400303020307219003074000c43c0003507039501e840c2c10584c0c0314400740306640215482400340488054225009504d16440e14100a5000c5001445800f25004101c14007065585111000e212425141d0020800c8605410f00402102c203121046019a2508900304a19034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 104528902 1250 104527652 104527673
    0x609110a02100509031213021e01080a0f020f04090b0901080604030c0809010e100c031812150f05090601030b01080123091f020a020c150f1e13060e0d 66
    0xb06000c80c04581a1180c510083c0f550040400852410803c48100070000340c403494500d031240e0089441400302c480306014081c4c4800d180d10302c140040e106100203410f031b8095802c2404080e4561400610340003100421450035001a04020b0340709840c0d9030381f0301241c5042000c1d9030141645801900d9141026a005004000e01c01002440f00030b000c1043c0d4034aa000d250200506070000e41642d04044000d00000d120f6290500700302c010941c0c2c1301c0c900154122065803c0207803100f0400e40005503186854140c07246080c5200890b0490310354650038041c400ca4050703076004d15401d0740104801d5066140822640354142c014030480d0b0b01d003070586994590b2001c0d069429898001201880781c652141460070702e000d00300011000f4001d032454494100c0c8550043c0300000003503003620f44041214040100e078080452410b24030303100034440b035110560342e20003c2504c010701041201001100e0010b020050b01311806100c51030f44811020824203810200c419400a0126032a00c1c0328501d03980c3e002d0811 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 104530152 1250 104528902 104528923
    0x601020703020d110d06020d0e070509270d0e030d03140f040303091b140105071a06060c01090b0118020909191107110f0603100911070b07030609110a02 67
    0x40300301402d0340051001a1840b13030800c0c1c0004d004d44c000303d030f440e00b0000041c0d0710011403421a1071030449800d0000da4081107180564100401905040e1100902c1c0c025214841c15000020644009140603025081044ca6507840954a86400da03200e0b5504041c00c1540701074141c0149410300740da0508003000700744001d40c042500d2940c55030750345550608600030001d2500007810540085006038405003512a00000c0700d0400482c01c1c0300b07401c2c2000454050191640080c00540c0302c124400100a0546010380c1c401d00280401c2e060402c03814075582583ca02c41415a01c40a68600600405241201400d1444503c4409501d402012404240d003080010114049450b5107115030403000c010341c0100c108000c03609a0a62140030504010368001841103515104403030000300e9060504000048e07034440c90700022001034040c034000149003d8290b9643c8040c81080402c0700300b0001e4a0350036480c2c080e038401da4000900c5810414440100e909800c603109002d43d0501c8041c82c1d2079800102032000c0d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 104531402 1250 104530152 104530159
    0x7091103010f120f0f0b0f060111031b011401090903020106141e01140c01020910111e1606050903060901060b0708160c0303110d0504030f3905030c0306060102070302 73
    0x400f540b50038100007001080000825a140392088501444061429203010b02031446000310b46880d02001501e44d0500c0310a104420740040c0089620003140c0a140310200c00c04900205810a0070351075a0450391098000254544e603c8580106141e07091040740050666801c01d110b01c91140717000070301005a5040f400c41035941d00340c1100b01c00c3c2d200e40b1000030b1502c45c4414054495034110040e030b000c0d40194801c5400b4803904860b030280c0c144100e04240b01009450054107030403c440c074640e81d164401c560740d50000d01c51020503a2583c1022280300e40249030a94034a910340791800c040504003900a080540039a0508006001a40e01841203501300c07588807020a580300041c42c0341c030403014201e01d005000d034101c5803000002d064024810943c0c01495005a500c07000d105102660b481c011808003074036400003201da08001410b0240c541c01c0043c440c8502e04041d203d41d0443c00305030300508c1541032419108003020421420200b00901d20000110013401542c0360080000390350f0941071001920 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 104532652 1250 104531402 104531429
    0x32808010504021c110d0f020702060f1809040c030201020f0a03020d030b010c08040807060f1106070309020f09071d0105121f0e09060117011a040b0a080105040507091103010f 77
    0x182c3c0240c801204d06000d540fa052141c01c0136001d22202907007000d074440341e101d428110081000e1030140308071940d4990082c110350070700651002c0c0b10b001d0380004d0305466010070f017400c00e40d0f030542d01c8142c0030348120700c1008240302550a43c03000904007415400c0010440d404001801f0000e9008505c1c403a0209861034000f503100315080c012580724100c0000130b00f0260001134081044200842d4000075507005480c0e16504880117802202c5039000440c001b29560800404140014860381000c02001d0000340f1031034080003c8000620206001d455440125054101070112000e4008181c032180b8030909040f410b00c00b0b54004441c40c2c11000b0000303400f041600036000d1001e10a28941d201400180400c400c1510b0410b81d48c9075248000e000d02e06811002480070010040140600c401483d2440401101c8070314507001c0c0000750000c0d092090303110040003004030b0483e009114052085000e00c000f005203a10b0310071581c003280c0165419002d10718080005012088282010f00c00b20b845004841c0c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 104533902 1250 104532652 104532667
    0xa0c02061e1f1205010c020609070504150b03090a020a09090f0b060a08070b13051518130e0102090405060118060e060409050f10060201020a02190c08030c03280801050402 75
    0xa070100d68000001000380ca20202c089030768051084444000c500c210002c0054080d540400d0344e85180484041410b5070105109000300d0030203401c0449840452594100035a450340b450040a4204545840190340710740407030000c2d4501303401da00005259000c0200b204650a0701c8030400850340f01300291091560b440407601c20345400281c0c0000746000c40a4a1000e0340b28840001290f200300d250a440d044940c1001c00c0758940320004002c0d1919642d115868010303c0484100441441d81c0300c50740c0a0706c00004d443c0c1802071070041d408410050000182d40c0c404e0740040008450014080d141084501e1b6800494007014240c800142c410a092489070415004009552440703280c20410700c542c14002401804120104800c0c001c0c1d0014030400001515644104e01304d0040514100069006003c641c40c3d0221503041d0b146101d00030040040d01e140c44807001c910303541c0542943e6619600003d1150083c14510300030745206424008241180361640c04010407200c418050241304a60004504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 104535152 1250 104533902 104533921
    0x8061c0809120f0c0102060f0103060b01031b030b1c020609010503040501020910110c12030405060f04080a1b170a02090603030d06170f120d09020303040f0b030a0c02061e 75
    0xd5940d030500402050b06900d15590780e940b500d01024582516104107449803d00b5130020401922641003100141e0700c40c0e20b9521020090306030006010b042c0340c0e44800c03030001d580320500302070080c86a42d1000b0840c40b1582c400d0003030324100440c1010000f10080c0a02c0c00580d503600c2181c58200302403904035100d0310360b030815500a1196480203580040b80020382c0d5112038028228900f2910380300f00303851501d032901090240c0021030506c80c201c00d8108000a100900c1c001700504215102e060b4490f090548a006c550b1074188440d4003918204030340c8840e0450410284081405890516054202d40400b0f00d00c03e0356804018400a11030407400000072148c0e10100305a0740c0704d1071442c3d02440b8580e0b507410b0740012643c22415614050040e41c82108072403000003080b4084c0081c00314000d140c9001a5414001820b01140c203c0c0c1c18082044000342441018002401410762102043d55038200156008201d5100d5003840041d500038808100141011941520b5042d241e00c007406141e80e920b2082 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 104536402 1250 104535152 104535157
    0xa020d1404060f170f0708070206040203060f07050f072010080109050a0902030a030815011d060c073c060815030c061c060915150e12010c0e0108061c08 67
    0x450341e4138400841040648010354142e14000d0302540c4441e58151528401240c607503404840c06501540100041100010354901403603200c0d1051900c0d42c03c7c0704600c00e4013001c0d075003c03110545801e039240301030000e441c4c0c07021205440c0b5001195138501d0100880d02c045c00c540014810511210355640c0001d05025890b002120501d5005040c2c0d9400e032114900500302202c10b84001c1543c0c01c40d20081c0760175500681d03009401c0d01444080140c48010441000001d503c075980820a80c060844005541d0110b050a50342c11700402c0942d256542006e81c40d034904a000003030b02c546031000e6a204005135a00003107016040382c40040103203103589402001c2441c0802ca0070070701d500403070000b94000e0400700c2c1d603031850345079a42c008003070081303035903913201d041c291014421031010441c07481d0010000344001003c55292000b990070012210540c6000054039007004506400290351140d40130300002e544540c0c50b20312a41d0908000e4680d00304100402c9100d000c03030000c0c24102c43c091038608203000c280c60a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 104537652 1250 104536402 104536427
    0x140306040609020a020d0210051003020f0303070501090308012103080114030109080d060e01080a03080c0a03090501060f0302030d210905030c0601090603020a0905010303020d032408030a020d1404060f 88
    0x1550b581084c01c03c003c0d661a070320258100140141c80d050076420800740107907409036941c480721462490958007000f07030340007045082c82d90500c010069040010001c2c02410343c0346000380c1390380d80f2035854600344110911400c91404402039006031000000707038001a45c1410369040310303212504200b4100100f13005018409014040c40781c0491114000c3c816030700600c00b502d400305090381a903640c03180c074165a90f002c0070b80100495003220000d0381448e901c0c000390842454600d0081105801603c5450071202c5035004505d03002044442481541810090034000918521740b4a50803031288441d608810301d40035118400702e8682c1c0e1750310140841001901d04180394441941e00d556903035424800280a140710880c02289400000150ba1001d03114440c101c0c2d4060300a03001001103460100c00400307030180320400c510300c4001c122612890401d5400080c001010046544030a0104082c0c42c10f030b5502c11500800c007151244100862484003900c04403042802d043c001d80103076900690b1403410412 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 104538902 1250 104537652 104537669
    0x304020a2c0c04051c05030304021c1203020a0f0206070c1403040308120402100807020c0105031009021206120d090302090405030c0a03170606070b1501110f03040801060b04061403060406 82
    0x40c24011910b050000900c200c2c0e0040b01c3d6034811503041c18081390425507441c80541560014400140581008403000c00301d003440b00c568540d10031042d61a28aa00340c15034029000a601054500c801d6802c10b020141c2c1c040790340010300d03144c40d059400810340d503207140d07000344152000448400020020020369014642c81010540c8400382c1d201140040c070b034200e600764850780c80031612040d02c501500407076005400990140111400c428010b542941c405007421400302140180011200414805450000784070707003100701d543c1045020072580e0342d10345644c50640d1b048034081e00c2c0103a82007110101201d90503550382e1039a40d40c07410140d045020340c0d20044400d0099028001c1011707071101c0f603d845440c42c9200c840c0244c07030f00b4080c80003601032141c000300704442c104d021034448616181c071910500014540030041ea00544406800d0003001d00200380e841d44040380c180000075080c00342d031000d80600383c0254182850003000500c040342c0e200e010b90900d000040420115192900400c01800900 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 104540152 1250 104538902 104538989
    0x80d030e1f050919030212030403020a060c03020d060504050105010e04110408120a120506090a020c070312110c03010207031e27030b15031c03241a0304020a 69
    0xc41000002d0001107540c82d025006804040e080d425805940540154256005214032011055543c1c41540080c3c0705506512030300c07801c140015458003c40c00110780c555809a2540c20b0600407400b50750302a00072910030b40c100310060126907070200700340c44800ea0441c1c0100f040ba40003d0102c903d845150422310107401030840c0003103240102001440221a80d80c0d07581180c15080d940d80048440c251407481d400600300340420440110782c2c010f0804400d5450543c0c81d490740d20f03034814607140e030400380e440042084400c640703054203018000442e140100350000d40c40c0600b140d800134030801c00b286802085010b5040066a100c1c481c008640040c1c81e8903d04001c0542d4807079403500c4010082c40100c0b000000503001851381c0c0c14245002000700d00280007014a402e0302d45075480d80c20301d00c40390101056a0b4040401e000003251040ca010313200707504400c101d020704001281034003494014403002c82c0c01d010024480140ca03101303180d1017100c2d504054922204408540f142030701d4003072642c000110041 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 104541402 1250 104540152 104540203
    0x2010c0c030c050909031e070318060906020f1b01110703060c050d05090a02030706080c0d0203010902090f100503010b0906040e07080f150a0b0a0306080706050c01050709080d030e 79
    0x3194600282d0f101100c2ca403c2a41e1007070040c030b0b541d1084900b50207041e6070880c0381c040c100d49502d010340420b0f4400c0c182030300440c21000981a0300c035605c0e03002000041003441c0401c9010380510141c020007411402619084080403a510711280d04c1c012502e0400990f0f030443c1c0010101031041f00050b580c401c038141b041c0028000010100d41207904152881d030310381070101c0c240c00400030740c9511b010784c05405000d5292922000707444812000381a030400c00000c04c4030280300b030039600c001c43c0600303007d41c00181c0b5a4402014000021070071990079000c0d9816241c0c82b03480390b070402d050703c0c11603510000706a80c81586c8400301c2c00034000c0c0d5108500850919050081590304034202c14800c154000300c00303d096681c0041c2045000c410300d0801e0300101c409130203004941d040c400a2401c44090f0502150955171440514a096015806803000690108480c800070700280240c03034014440d403826015142c20007110540b107100d14180300040c5a5240042c0302c40020034042241d00050030042d01101081 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 104542652 1250 104541402 104541413
    0x51315090308162d0e060a020d120209030f0a15060b0f0a1817010b0319030305060a0e0f01060201050106020303040804120309051302040609050316050d170315010e0d030206070c02010c0c03 83
    0x200c000d0450041111030b982c45c1002d090a05c1a0f400c1d100306a0b000707240303444001c402569030907030101d1281c1c0c10f15020000140162001c011b00401110310000074000b541080c18a2503428451041e030110860a1141c2002418a00002c0d50000b10104403016901d500040080d108480071003140c4480d4030b4a8a070000f903071941b45106d00354028401000744000c2408504050316650442c03001044e1118201c8440082403003944400da2055001d48103c1906840d01401e10708050b085401c4c070414503144006101c20ba038280600c07401402c0500081d811801c0c80da86241c2d160089024001c600030381c02c5001424140b1400030a4000c26001c3c140400340c0c41c045450001940c030900070b640229100103000280c0e81000201c8240b1101c951400c00089800d0104112080d03407070000a5900c0000d01b4011142101c0020095000d550100d10106000343e40310f0006d0180142628030274400e040061441c0046a0046200781d803000141c540380c80350b00c003e840165a03400300707000c0182c000200301c50f01008112 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 104543902 1250 104542652 104542727
    0xc040315020c1006030b0c0c010e0a05010b03070602060105060f0d0b04110a03060b03040807110d051504030e010c0210110a080f0702040501051c0b0a09020405131509030816 76
    0x4004906580c0c01d11502d01c5440c040c4c880c40c2c40010070a001e000d00040d150b5441201604400c070900c00041010445244181c0c41c00c01c99103803e0b01c40e46d43d02d42c0780120503d410401e40780107080324006001c19614040014100b07008801c074044910300b0000b0050000ca030117a21a00d48840c000740100300c401c41b0840007607000c0c2c110780c054070046031915402054030f40c101402c2d24802c035031100007586006450ba480d48400381d10010090340120341c4081c8200014010301c4109010f280450b04040c41d49441e0400070000203112010790706000c400300d1440c0158503401e0505c6d024101d21b003008182001c2da070800078648181c200018280d4040407442055821802009101850080360b0501040c1d8941d8100010030010900c03841e0a51604c200100c0012211140d0380d0340160102c100086d8100c00742c001c6419103000320342c52402c1200b0090250304000b500c84034080c858040760001c020050300da5901910081000c0d00c2c807183d08088080038040284244008030022109071580c10560030301403071783c09150 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 104545152 1250 104543902 104543917
    0x8010e06090708030c0601120602090d1b0b0906030a051b12040507050301020406120b031006080c01080c09010e011d060403030203030106020106060f05040302040b130515012d05030c04031502 84
    0x601481600040000f400800e40790f038440000050085da03407a0a40d1f00704d20b100302907400c03151143c00b03102525013550f45007125a4620f018030702c0e0304058010140c003412a081c44d50000008036800313210030010398071074030192984004103020014640e00e400f401e001007264403511300c6895200001e94440f00e14550842203000e2442907007144e6141c1e0f100c0b002c0500741d000d24043d4000107048200c090440d80e210382c0200e05400405002e50311003c0000c26000c0980d12a90441c01c25640400f40251403542c0c1302c101103a010100d4421103080441050008191405400e51503042104100c05c0c480080c4bc2c07a04800280380e00181825a00c1e40e0301d1801070b499410034418080035520306100021102c6c0503080701030030549940d940515050a6508120060142c0c141c0540c00c074031048001d4104841e2882454011541110000c0452403404001000311402c0c0030a00c0c042403801003440303030000350415102442c0a542c00c2c8681c80780e4449a452915002d5907202030503008005031030f02b278072401c103900500d40c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 104546402 1250 104545152 104545171
    0x317090414150118150c1202060103080405040902030c0607030c030f0924020a0f0606050f060c060403030209120607030b0f06070b01050402030c040306060e01050a0e0c2208010e06 79
    0x548107600c8440c00c1c4000c04950500c80d11080b00002840c540c42074501c0c083d2071a0307040c040810140c4039000300c0320045441c00031101041040c5070220501000641b1862280e103d840100010341c155035840381c45002d035124290089458030000c1003155804d0051100003400600b045031242100e040c01000d0a81042060f0081055040080704e224458041d141c1682d1880d001c40c03008120b0001a011032019442c0064114022840643c0c0014051448606158001c1c100840c880307023003004005040311100501c51086904000c003d444d45404201e0725071103505802d006850f03112240108500301014004100c150140740100b003241501030f403100030394050546240310741c8040a0240640d51040d0500900403000000041000c1d2900341c0003140c1c8400ba210300141000e80d603988400c159a43c6812005218150100600071402c00b005240700900b0700302159a66410002e4070b0960320300c100b441c5400124120040d81013000442403010005005000080000c05040e178075058407001d043e90034454 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 104547652 1250 104546402 104546411
    0x3130b0106020601140f0a121a060105041d0a110706230402090f07020c030d0302120a090c0b07020103060b030c03090d110d05070c0b0f0304050f010c051c0603170904 73
    0x142640b0024540741a141001201041890110104501c0090310185a541302e0080b120104801100e0680384000f9031040021400014405003801981c2c200103000f01d0401c0f105020402c0000585030190b9400b0f203400c180391130180c56803a41e5130003511800301d5600802c1d100003810803c002e0305030f02c8000780c030811040c1c0043e90940d203d0045902503080d50041e51103600607000c00c100841d803580b0150800340900444d0440700c2c543c40032a081c2200c074403010010a5020230250b0b07000300c80b04841607001c051000e041010129617584c2001d240c400d401540010800400d10b4000c40e4007070b07440f1070040c000303101d4041d4480c03501c50501101c50780201c0d1041d405016158060446900943d4448404030504014140800c2040400c80729608621002c2e00c030b0464000300020303115000c02c01001001e11400c01980ea918140c24518030b84000348020030081d0380b6040b0301414485e88201a214130741c841810758140104014010000b404190b04082e001c42440f010340b040c42c2210000401720300500391010301 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 104548902 1250 104547652 104547659
    0x6020f1911090709030c060305190c0e120708010b06120c37031406060306060a0e120a03140307090608060120010501170102090a1202031c0807091e03060b010309050303130b01 77
    0x2e0a43d10140cad0514100700040902e03003014070301a04804041c060614181e054440c50f50000f5a003e03450390420280358001005c103102d0300381d082c01a18030544050783c5c540c0c500100071000104e4400014030282c0f4031140030030301001c0c262800b02d0f10801003003500e0840030171081c03200310004449183c41e18030000c40d1a14034141800c0d805901c41e40d2196000030242070071071ba100401d0020660051081804000e51080301c10100c0e034600d0f0000710a2440701000b045041c600c0e15010b040d01c1d074240c4480514003410300c100064558080b503602e05580c05454104520b88414005940119111040c5a803d14181440c1125010158031039070403100078004a1480349411182c9500300e202d030701d41054002a16040a2004811601009501c00e20241c101c0d01c1035203c040b0001ca501c00410440c030f0000d041403050164644e4041c07000d0002d41441e80f0314000440c460085052003040382e1000400c0c803038580da10b20001342e009500c0b000c1155004803c0d2640c900c2c080d0300700d44402c08084030072a60000d1440020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 104550152 1250 104548902 104548907
    0x1e0a0b0403170a09020d02100c0b0108030301060801060206040c540c05070209070c02030a0c05030105100806070807120c0903050706050c030708220303170106020f1911090709030c06 80
    0x2d10301e00e50040d00740490740190b50280145002c0341d422231418458017036480700c0010f400f204030034001c0602c034000d0b42d103950400500030011030061340944215408401440003140b00002c5d06000c452005840780c400f00c030183d083c0c01d02c8450089100780041d24800802440041c041c010f0100a01e0103404c01120480360740030314040302c204004080006605000d44001400e2910f0825000348003410030341c80c076440302e90000c0d1801454900803255111400c404200301d06003406282c2e0004411201c18a249017050102c6031303070300b0004100004002050307021594042c0150480b0895130810b0200b071042814100e806001c03403410b44400c884030300ca000c00025185202d202070740c0381503840401031480d0103040e0f19201074580045860088074110b001715003081092005c600030080d0301c41d440e6401401121040303071064420591210041d034010600e9403041c40004590401031a41d40c01d420040110f2508240b1801da415003515504580da040c1401101600450044102c80c82091150166034480004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 104551402 1250 104550152 104550161
    0x2090a0b1c0c0e0a061103040314010e011b0905221d030301060c0c09050c0418020408070f0e090c030303070518121e0d0e130e0a060e070603020304051e0a0b0403170a 73
    0x6e540c03040d082800240001041d010010159103045000404c040c03468506090840320a40c884954030f414298198005030707002500e200051008a581104a0242e0a12461810112800030060503034565050b5414001400b0305085020124100d90b240d42c2c5905015182c80368054040c2c94040c0b40701800500c5e16468001d03603200701d0303003040f440d410146040412070072001c070018180c81554080c000030031800c20410800c5c0090070042d410502036803074010b0104403244d002e001800302da0404150704400351400001c80b80c01442d503184c51503071008810b005011401ea41c0d45130316032200c00c130000001c4211000414543c6c01604042c8122245050804180d035070030055595804100e42500703102e03461a000d0003121560720409404650003030034020503801c0c10094070f401c6402c25950f40240b400c204081150101410841c20214603604094a445030385115075040130020841050440f8a4980d00b400f003c03002603440325003002642442d24016120080701c14001d4205c100c140006180f50600b8010b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 104552652 1250 104551402 104551427
    0x3200409050a1403040b0d4701030b0406090501030b0f07090302010c02060c06090d110a15052203020307020f010f0c020111160f03050606010302090a0b1c0c0e0a06 72
    0x2400700b02501d985055002c02030361000401070000307120001c0c00000101c020041e94036402c80018495101c280e07405180103001c03002d0198140e00803104d242529041880f5200c414003010324084942d21080102c0207404607021317468005e03041c5000000c038440240c1004d4144e078419100c1340466503411b07807144c81c2c8820031920708000800d000400c01c050f5020f01c0b03400c1e460f2070014003500e182556000b282d900d414825034424049501001400c110541e11035113214100c04c21101a001000d00c40e16000c00c1d01030303d0315540110395642c030b000c00c2c0941c1032488407110a00c1e404540c010300c0a0b1904000e51a5040302c01b0690080030340c4142407541e5031090b40040c01e4030b0a01e071600c0015044540044420015102480301144201c2c008074040c42640018140142813180e0713410007131800c6103030850601c04003034025814035005000c1e03c01c8a41d2143c00c920103039544550000d49543c04003004419802a0181c3c45038011710b040d01e20f01c00150303c41c00e1001100415139050300c0391036841408841c00020583d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 104553902 1250 104552652 104552663
    0x31101080402130203040807060516020f03041a0c0106090e060f010f03021c06090c15031b0504030f0302010207200907092105010605090a09050f160317120103200409 73
    0x10f039090300c454080d8003940c0c0142c010340c0810308000d1207548140440780c0a40e900e0701004a00d000c82c2c0003080d4108480d952440000002e181060300d02111007040d1004d001c0b94200e880f1b400304498640c9242548108000e014645d000d0003d8044115550380310790341034441801d060000000840c2407070081041604581d406070201600111610625103c021185011503200303807a04810300106035a104264042d10070980361854040700d819001e4102e8140200076840d03100c1a15112031f605400400b13541c1102d0300041c12148800152030120300a22a60f200200745c800608a1151041c03030610840702500c0043e101240503464a800c10b54210745203200350b5000d4410040e000f44c1902805010501c034a10903400071600644810028045102c04c440390143c850b40d0b14100c00500c0790411070303e00c9441481e000b4002d404d4022000c80581c00207408054403010002072216800c06035101281d1902c0240e8500188558480c50817240a00c030b21500c0c4080c0003c200080003882c6060b1191343c66259011 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 104555152 1250 104553902 104553919
    0x190c0e0405130b0106030209190f0605031b0c0c120f0d030e1906020903060f070c080f0d020706060504050a0623010e031b09100308030f10080a0804031101080402 71
    0x204110107040028640209481203142c66000140079070519806042c00e81c8016880c1d0142c0d03810710103003500718102c1c010246c84583c420060300a00c010a841903401902e400c0c4d6507559280c9021002040d00c01c03000f84004000110802135441c0461078001c06001141c49944204030300303500e503035103550030030b0706c0111604194030f141c0c0c4403030090340b019140541e0142603500310081100c0c440d508250410040e2030854000460303400a14040c441240e110a400f40c188a035404d10200041c0124080f0800070001d2100141d107044110b1100d0946481025100d000c1d95545035600e03003507000d4a240d11800d402203061402191490301d96001c1d240640d0710080213042014821005000c20100c14401c030343c1444400d0f0b0b580009518280600c01c50044850104c14803d00200b00b4080300d04030082c125042c4c4d0040040034000225410f0813281c00000c90310010569450700300c11124100e140b54403010305407068120a4007003003800400f600890b401100c0e8401c121484400550b1310000444000f50300c500c0c0f0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 104556402 1250 104555152 104555177
    0x302032509080304030507030b0109230604150b121005011d1201090305030f100e0606030402041113140d030504030b130807060b040b030a11010309020f040c08190c 72
    0x14880e5903040c5258500c1c1440407680c0e111003603800c5500c80c1d0001c2d501038004110074400c0c061405109030040c418900200324485400248040404240c101c12480c00b83c480e020508030b503030b150003140510305842d02c201c10060361030800303820302c2c2d02880c46a550105404002038a144103004040708840341a1074103030f21640c1d69000303078a980792a1540d0341d42c8442d03108103540f0011424460100400d21a840e880d43e2820301d11050030000f076004000c4590300100300d509001d8203094000842c2c000300c083e0388240d2030352214400100608580404404d50b4a0301080100e61041c280700e0a008031140403c0803140440e0950a01c00e18040f80c42000c1e01241041008000050800e440180d0001c045029141a00040c0e503070b440e45584610010384001d0344400e51128585000e224503014500220000c1810031010f6070741460340b0f10280720007410b1550381c42000096460b8030b0b81000080c00c0c000e0080013640f464000140c1030390030586a05501411850404941000911941030100724940710300c2d540106 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 104557652 1250 104556402 104556451
    0x18011107270608060702070503070e060f010c08070609050318010e0f09040302030c030711040f0207030c02041107051207060b010528050d09060906050a111602040b060309070501020c01030203 84
    0x9000c80003181103a0b0701e44001030005410301145019900c141e01038903005192504062401c00703a50407092000056000f8440e550361481c0288801d1f90003800c0c040c41e0417513282040d28081c003e03450084c000500f0442d4450411401000401d240d4070058024a281000c589c011251201c60490310354210540881c440220b00c1c0008500742d10602ca4412a0310384007200040b94199041001e049412046d01e00f000c05c1d80e4a80b500640c3d003240000c17041142410410b4030024036a9170403549c040e0055a03950307508900500800102d03510645c1040860340494101110a189036004036015a0454504004107250b584200e0840d04007003035804081080440060050300015001c00090051000411010b0385140b2140034000441e030160704006114011805c00f0002d0310401851058480e1502042441409004050340c003c0b240d41b0003150340d21041440804c0c0144501c4103038590110000c000c04c01001c0c000100070055410aa00740c962500d134040c01035060703000603500302d241015444130b000313103502 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 104558902 1250 104557652 104557709
    0x40c0b160b0c09030d0f02010c0e030303040624060801050a08070b03041202160b0c0622060506040b040216050c010f080411011709070e150108070810080318011107 72
    0x5207100e081610f062070700340000e850040900d20034008a16032802183d050b03502031040c5007a448650900303012042101c000a034583c840107100034072045d92959080304006189602842400380104017000f21915020041e10142c0c0c248a07062085010b42e01c00315103910040b48440031103401d6205181103498660303511002c2c0310024082000c51280b56102810007016200b035100030a03d403090540d0703480e1188034440c2003490003003804071811568010728000c0881c840d6080303421074220500040544030103000030042d202c0c0342c43c2d5950290002c1400703207216408400c00303075403c0c0c0325804907082e880220f001951a00191010440420060400203001c034204204081140c031051500074412100d4000d00ca62024080e29007500c02d5000c060207004042050f420982c001c9203500c40883c0d14880b071000280a41001001401040030b000007160041c050b54110001620800d07055030303250b01700301d00c004401c00c541c1160b95000034400b88100c3d40b0303040045002000da4404080490354003041030b003251a41e2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 104560152 1250 104558902 104558911
    0x181c0804050909030903060c0705010c170c070c052115040c05060307120c030506010908060103050304030318090609020904050c03060915030a060203090c09011e2112020105040c0b160b 81
    0x1400308000305c2609640c1800810722541c1500c100039100c82d050f0400600311030060200c803045c0888007800a410020000200e540075404d0740000d650340720b40d458040002d1039a980482c4c1c0066034032201180303013042d0002a40d90ba41000742140d458508902d0700302c2200348160b4010784210745144050103030341002002190320007602d080021500380c03482e40e110308031105143c456000070307075400501045603800030181c402000070034018000c9505640b5410744034417884c0310040a000b6410310003040c0111246640c0d0050840c00d001700442943e0748058001f0703500050000b0b02c11850a400105188402c0e41528095080601405210350b501100c6c0300744506407201c020780c1445000d00700c800080b400d000461155105a02030019000450305000203030700f041c5c120a40d0303601c09600400d0750b401c40030104811030f412280000d9503000100f801d1382c9800700300c040c0030305100390700340c491503005030150040e03402144074030f42e540e0f142c580e14034010209000d00e02c9107400400e040311300403010504038070030523421 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 104561402 1250 104560152 104560171
    0xd090b031f1d04060b04020406050f0a0903150515040c170a0209041d070611060a0b0d0c0e071e02030a0e120115061209021f1103181c08040509 63
    0x715901ca00e104100e0002c503421038445070202c18100401c0015038003a60700101c9003500c0660805007444000340150144041d000030700b0f1804038101c041c080c402d0011400454028801c6085040c50040b02c00240c4411600720044064200c00034036141413501c5990468442c2d6501e2100d403946112041030078401c0135040211280d000d2100c0c1c1c0050741c40344101c0601d80003150008803c128858401410021150300000500280c150015200d000c00304070b00f81c0c000f41c0c48400081c081001400560800310100300900038200c110000701e00070000c2d00e400b034051140d940301c07100802c40c101d0008030a0121404040016002440700030000d50148011840300f22008004281640d064485030b421030305c1d4903100e00c181c404500c2e02000f025800c41c20502c81701552500c2440480c3c01500440c00440100e440f0452100c0c44441c1469024410351034803090150300b1042c2d994404c85e690750344822403010201e05214055181401410800b010b002c40c0100342d2046460342170500e0801081803610b07004103213401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 104562652 1250 104561402 104561461
    0x101b050c15070b0603070e01150203040306050408071a06061b0a0f05010501030314040f032406030c14010207030c06080603071d01031a060109030204050709050405040c06020d090b03 80
    0x4440d9194441e04074001c045070400c588801143c20072940518010309958020f03001903400b40402800e8081c0141568142c07521050f0710b00e10010103c3c558400c1d0360002e081a481c05050104011400f4000c085481c003484020030b5061080108400c011300556074154841070401c6001501240c0c000c440e003907249944241c0320070740c40d141c988500361580008201c80c0f03655510018010140c02107100c000c500c3e803404599081500303256203060341001c00d00003d85a225046020102c9009035030340c100c05685491014071020341c0d0380c03510b440043c481303001e140c603100810b40210b0120751000036010101c03a0401c5010705084c0c50420190740e05480075001c56054042c2a1000c20480c03000c0790819403c0d4401e0315034034403541c5141171610410000c0c00700c04040e80c6000040c0811a0b90200240c400c9d07980407178001800f03031200c60065070344c8509640324a4006061204003c00d020b500400c1c941228220780aa5000d140c40c2001214030081c0c5000d42261200140045011010a150328204a44115402c00d0703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 104563902 1250 104562652 104562673
    0x18061401020c0108090f0f030d060e0c0a050306040603080d0b030c031207141213050901061706131811090f0105030d080a0225061d0a150209060c03120105101b05 71
    0x14145000c0400b83c07d029070001882c00d00345201e0b440b03000e000b400051160350380340c180013410703202510a2107141400c1120201c00f1500c140c2c1c955114400843d4807042083e07039802085c1d80d100103072006c0345a05120340103060180c40c0074200030601106041c103541d10b441c42d1400a55620201a546c0c0c084244688200c1d030603000a00082c0c4000c04503543d05805511503286032a00708034134008143c0005003044010440540703c440c2034100c103a0889000c80e61283c069400084c1e600003045500108401c80312095030384018068412a041c410307035010f5811949a58070707811503d0260800b072203141e405510002417107101ca4401e44240b42c0200c401c520140c1340249249150b010012141410b041c5c140f8030003014000c01200388100240300f85816950458220a040b207176440c0e10443e10040c0c8019601425254150b005504482c600f8000600c50358031142035a089550365080000558030b81a07081e400840c161506c034441d40040275407651403e010185400e00d210510100e5030b8100c485110300341102 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 104565152 1250 104563902 104563933
    0xd0807080c07080106242304090e0c06030c1204140703030906110f07060f020f030304050304170c030a062304050607090e0108100b0604030b0118061401020c010809 72
    0x20300c031035416440100740c06400e285000d0708450041c1d12003043e0101035150030071461b070794490024011641e0b0810030002d14030403500b07032401480c820141c0b400050000d008260071295901c0900c44100000444180e0354110302800f01074031003600d40c00c80942060141c3c0190003010711156911070312440003409a1010b02c05082d02c0e040c0c840e001100030940d000014000c080d80700d480500407c800400038602c2001007102551a01010300a040400050100920020b0300170040704036464140b404490ba2840d040c200b417506d9070458000c044034050045401140140300181a0b8900c49008003d000240e800d83e944074024865142e0070b4400d00c612182c02c01242640f10213143c8900e000f0fa011740100d00e8403480042850400e500071608002d442801400080070000300a003150504039000260b401641c0c0004000c1c1c01164401130880003490001f0a48940140d4040c0500700001400d004036521078141d162000035494020740164402e088003402c40d03204403d100d03000800007060700e011035034200c3c40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 104566402 1250 104565152 104565157
    0x80304081b03100e030306310b03030405120c01030e07080303010902030411090403030f0c020d09030b0615030108070f060e030a020910120308041b060c0605100e070e0f040b060403020d080708 84
    0x102613081d003002c030410140d8203140c9480c840701142c80703840b594211b020101010140b8022043d5503416503070b5000c0c0c407417a03480800454001c0c0400600c40907240d800c40400d10350b10724503211441d00090401c1c0c4508401d00380040d0340401e039682c0c0009036007141e00b0306207010000e410003041a41c1514600c54005801d898840307655001d80d029940c00b04800c10000007403420f540c0644515011580120342c2440340e282c1c8010075809580d8001c80300038543e00c03a40c00040c0118004a440a11013400000002d015100040c5503001c403181c418001c0c00003a91044192040d00080030900e825802000405005241100c009540301d84201000b5045503160200c12001e1041c0c5a81100070800140c1840280301c4814406981c4120850321407407a40e04089000b8803456401400510b96510364000c122070485820684000e8401c1c0071038041c5525060304010001340300111103a018052206400030507003410f002e0340b01214006002189007034512790070b0114140c0c1618040c0c452001c00d1080b04c0014400303400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 104567652 1250 104566402 104566421
    0x30a02060408060f1f050103050c070501050709030b0108010207110d0212100209040608160614070f0f03081f2105070603050105030f0c1c060b09090f07080304081b0310 74
    0x2442c0501e0400d1309010442405000a2204606600c5903080d02001c240c0d8141034800a01e00841c4544a155443c1e005009000d4010300035420f160820160684c48900b00e13040700d001e090440c0241c1d07651407182d400c134824000083d0800c4045080c4145a040c0010759181503440900464480c0205146803814401c1e001030640500e40c0025001c2160319260180001801c9040c000d03200a07601c48c0c204520a40701486088148000d002070400460200016103400503001424450f08020380d02d840d100d4000c00b0301080b4040350800010800c540c1100b04050040400e4400c8079120707908180071350200442422408000440040c880e0000039400d0010b04000c226a88020075a07504003003c050030421140f04101c2c003035100f6050489166110341c0c0c440c8143c0850588184141c0081c01c0c8a805413411500300c64022100000b0b04c200510001490001d001c0190207a545040e03c0701505600e0744241d1090b801c180c1d000d580400304a510000b00d82c0c0315441c0050444064800c41c12280c0d0540300d41c5035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 104568902 1250 104567652 104567669
    0xc07120b0622060f050307090b06161e0308060111010c090513060902120618040809060f040320040e0c01080c0307020c0a0311150a080f0a06052806140414030a020604 73
    0x4c42000301e42410003150b0080c000d0010705000300c951070004201140185210551840ca49400042c1400580c800f01c074410010b0310100141c00100c1e00340a0501c0784160303160b60014010600490399084184101e1000b14030b00c2e955801c91900e07040c1045100c00c10b040889406d581da40c000099100c00510003400c03813400e03545c4814210310709881000901001100c6c0c8501a440c9441004000bc0c0110100d520a0718200c0d403036511420710039016605d6000e560001400303034800c90000244540d10301c180582c02d200498041c00140c076818001a201c140121180340410020001700d4030458a4401440d0b01c0189881140c01d40420324000070000343c141d038402c0e05c5221851014000c0d0341000c804210f030703042c03040300c6d21454480070000040c500c04000f000300b040e0411000200300c0400c126040480182001401c03c05000c4804041983c0d41c40d408040080d4440400c02c0000c01038007404410591300f820b84003940c00e0a252101c0c41e0401d480c880007049e810301a4000c1c000040c1d596070040c2014007582e8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 104570152 1250 104568902 104568929
    0xd030e03091c1119210b0a090c0b1306030209041503080418020a050a03020702010e0312090f040507020c011211030403050301080105071419120e030c07120b062206 72
    0x3e00b44450f40060103441d490140341c80403000c01c0c58402850680040741c2810403620080000c0310001e50340d0f2802d1440003498001c1c0c200a00c01003602c1500f1400792113010740b41046036181e58140c6c0d281380b48a061103179200400201c40402c1014001d5000e080c060a0144c804514100341544100040c80d0743d8100b20382000c1c0208040c07041706080004001205074211045181c26003003500682a030080409075020141c0004100086902c1043c8601060303001a04450504404040300d083d541c009140d4503014a84400800100c0d24060050764003503030717898024010a0800b1801107400c02d075100700022806454442e04820226600300640c030650207a5603298995040a40710790070350704081d02d400c1c02c00032221480d20241c0c00600480d014500311500c517042c0e40310102002c0d00d0506407006500402403910700a060001c20100082021480d04000d4502c425250103980d1810040654003802a03025040000e001e030a224040702011000e0b901204240d410007161103056800300d400019014140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 104571402 1250 104570152 104570209
    0xf0c020f0604081507030603020904020f030f01060e01090b04020f1614030703051809040c05060c100204080a030206070212070f02150711090c0c1209060403020607060504020307060c02030d030e0309 87
    0x44030b03000341d0001414030342403028502c5d680003d0b007807100140c0042d1007000b050a00d2423740d50f04101402c81000c14900a0281e15580c52640740350090903c14614001c2c00e200c4c555400b403804c3c0c030841c4e084085550450742031058042e040d505000c3c0a00e0304403591b260444003040280010006031129612941da0590395031040155004001c22043c3c103980502c9000c410b10002801040d048019208266401074440c0482078290b072a22600d0a05448401d02c0003901203820203022a81d4540740380250210b91aa849d803c1e0300b2662142017841d1601d40c24003c1c0207400000302c2d61004d04030501e000415001126039104401d20360390344106002c6402001405c01000c150400030403169110031191001814490724508041d103820000031022000c000000b000e0380d25a403a00c00781c82c00b551300a450140c45004501d4000010001642e00341c1c4240b24a0b03000154040c451540b01c2ca4145e8007402514a11180c0303a020340140c024031071200200c0c0018030100b401c0d511520000c01c401c2030103503090036480a1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 104572652 1250 104571402 104571433
    0x51203010f050f130f180c0504051e130f082206080105010509010806030a1e0309050d030512100504110703110303100e04110d03051213030f0c020f060408 68
    0x40700e034021401a00a46201d80f0140c0d264944241141160b900100d9a0f101292070b0b10000c11103100f1a216003c0e4000b00c4805104d102055403007555401d41d4100020b890f000b1201c40c0003036842c04071210342150b060001d810035000301ca6500c05c0d2403040c1160301d5010301136525012540c1100310b080c440700c17031410150f040461800381480024146424480030759410140024514030400000c94140004000440c0c241d4a007004070b94a1f064206428104114140c1201d107507201c80001c0c141c0000d888004049406c2c41c0007800c080c1d4156054407110b1406051020b0f40b40030402c014800e1a0422481c000041c0da40c56038080c15804051020503180d85844501e00500300f14441070082d0000e42c0107200300405044060b41940995051007903c45507507a0768580300740c0b129000c1101d25040348011040340c1c1010340003000b409841506005024280e507600c010001208429100540054802e807143c1290700e02801c0281c203624005032040706507802020108641e98032a034060040c6a22240f415220100d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 104573902 1250 104572652 104572679
    0x105070c090204060f02190c0506090a12050a1b05100309030201140c0429030408070c091b080603030a0c060b030c120c09070503150405060f100305060109080a0b0a0c090305120301 79
    0x4407c1c0990a0107120549900c64900c10390701070035001d0440090200c00f10380d1055200300040039208103460068440c0e2401a4640304040c008503020540c145600c603203030b001410303c0020380790302a0080d01640c540030b0f8110050b00c0c0055040e015550703101c40c0e03542d8008011031458856a211440c03507558a180269003000e03074095030012081342d06c40c08840c3c2d501d06000030403a50003681001300c0c3d0340c6404083c1803000c0c004905074008642d0502e0720540e040b083e1040007042d84600d81d6511146959a10441815141e214030b0800800107512007841400064555111840e070450160840b00344ea08150040b4000f0408090140003590144206940924004541c6540010303d86011802c3d8107000610a24171072440814500c62070305c0c1d80c00034005844403210541d8400e00248141180d0301f64500240050106840d20390000d40c4002001c210210000f840c1c01e600f039440100c1c5d030180c0c0c0e5401c0c2170200900c0007020711810059105d00000c0443c204001109032107020322203060703032945001044403125 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 104575152 1250 104573902 104573923
    0x1e0b0108070605030c0a0203090303070b1005180420120102030103060f060b0a0e01020c041d0f03030c07170d020310090606090f0e0601031409010902040b03060402030c0105070c090204060f02 84
    0x154071012003840450740c000c0903281c026182100ca540c0321303c0d065000f6030070350164003e025014400403424800780440805006d0003264514502d0780d25540301c009003d00f080040c590125808020800700b00050f51200e00d4a2032105007000d179585000710311000030920265407a100300c00da07401000500520140c0c0c455580c0d019904101048064640f1072010040c0c002c40390300d4000e0000d501417100440c2d001340141c00031134100030b004006401e48040c808075052403ca001c00c072103204440303006e24441e40000413280580140c4c0901b600301800b669a05210445100c41a65003a00a2010100d4080113001943c001d019040c22840c5d002c0c00d00e051402141ca542e4443c004015400c1c40800030401705624000549580443c1c1040d107039544030050300034085081642006885003820440c40c1c140660001030120720840f0148074208000c42050b135035110a640c069070681001c0200c48070340d80200010200c46115000034817400e0b549243c010100e810070380c840303030103e40302510401d682a0305100d00404c8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 104576402 1250 104575152 104575169
    0x1060e040605041407120e07030f140a030504140d050a050a0209070e010807110c030a050606011704230a0602030403030c09090c0801140d0507031218060203030613091e0b01 76
    0xd4500c2c945241210341c018180c40203100442c6e4041a0210344e0b40c0040043c0d180c01c20803078008586d01d107481c0245a03000340b01904c0d0f206d6280121407032150045400c0b04e6054040e50b450b41043d00b03001a29000000b000030705944010324410110000d64240540c944060107240606a640201e006000c401900180420100680c00a00b805640c1c1c11640190b004501803412441d140050909140b0f006410301c240d0303600d03114500505042040014449200c0e41c002c0c0d070b403034001d004807801d8110541801d5a008203010090302c1501c003400422004524001ca0031310440e01c0400346171729110101d03401600c00b500003030b03100d000d50300c40c4a4112004100900800c801041807150104e00240340c140f060040b00346000d03407a03190340c0881d07451940c0ca010480d00182038404d00359491510200d14107134900c1070070120704070101c091a941549480c0b24201c4402e60086c40c69640d5603c01c100c8407021403c0e41404140d6904130810104800b6401c110030210b1605960300c085030036060154200038141d108540 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 104577652 1250 104576402 104576411
    0x1206050406060b0309060a0b0a0308031612020406270b030f040308220f1511040806060a030c030b04020109030602040b0304150612031404030b0c0403060e0606060a0c061401060e04060504 82
    0x11817007000031394141d10240c28900001c0380824500000d002c240683d00c054113402c0c011090028040765242580c045a90580380d151800c00240e03064401e9000d540300700c0d0041091620340042c0b140c42c007030404800c09400d00342221566154554182681c00603501c1324815469201040201a0807001c09078204a1070004504070382c0f00030411992500e40c8460081c14040d01c040110304000c111000082c074807100180601c5030b40b90340404c8010542061240382c4a500c541404914241040102d001c10307245c10094060398103041d61196140008050422410400001c1d03000020400c02d201a0010700070329071030940d4034140b42c100b440290380800b415403003e525001041200e0840958100c07007045d85420251482e01442c3d000754514055a4400741004003800304000100d055500140140c074403407541003100e503084000f803035910a0101d410540000040120189250140280181040c46924080340310018032240c2c1803003940030b0744042c01040b149440d46000c0e140c140030f0030340075280c02d032010003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 104578902 1250 104577652 104577661
    0x10c0207030b010510170c070302010b0904170307050d0f05060f010305220201050705030c060103050d030203010f0608090c040f0614030c06041e120507060f05161b1206050406060b03 80
    0x90044062144d540320341221070b044a84180252042d80c10000030001030880b606d00b074010383da01c81d07010703030300480040d440d18501072861318000600714003032500403032204060b610100912035282d001520a0f01401014003007286100043d0088822241d14030700007040d03504069042c0070b8051010383c04941810b09200030000d0306002d0055444441c80000d84400442d0400d00050b0342d00c2c400d00c074024080780000201d0410500c030005400f4101c0c0d114808540c503407401610110201d010a00a1a054280151007002030a120300300e59034011400c030003130310150b2031580b0000f411074608509182c111512501d041000340703040400a00c0010050780a441171610f41c000081c03d03441075000300c3d1a12070310040000142d41440c240711020f0400384031881203526050400300e5554040744070301e200144000f8491228180b2031402e42e58111402407202d001d0350340640d00c0c0315811813580740404542c8410301d00054030503002201e41c1d9005002d400000303400c0c14241840707010f0300d0180c2c1207099004410420321 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 104580152 1250 104578902 104578913
    0x10203090c01030f0209040e0a0b06061819080109031d0d080906070320070503121812011b0e0301061703070b04170f0a0906030c0516080c070f0305010c020703 70
    0x1d40c0064091800107a41e5241c01040c038000c4c0640c1340c8042c1c00518000041102c40f1000610044142c00b0300d90030042980d40b58100f19441c0700308200c0106540414803c4402400c092070400e00f501040042c1c40340d000d44819049013140c20a240c02d400140710130128103000746440355080c130705503c2a620035804070040e4880b503129108490003d0b005a800050341000d141c46401004050041070441404503804948045ea5489081c010144640200d03640c60203070460301c008844003245a07900700d01042c160312042000f00e04c48030304010119500d5090541c0d40089801c1c415041c0e11070351300c61031364908288051600315085d9810501040c80b002c02c40303185400b0000b0a45410303603806009000c0e140d9a918000415401485009140c1000810b60200d200ba84030054403080382541d88001c206035131403a04800741c0300c40c07101407000700b01d080000e5401703035880c004642011801003075007600d0080c518071610f103400c070254040c0b00b4100000d0018030801c44203001c1c81d045d44081d440141f513094150b8407031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 104581402 1250 104580152 104580163
    0x50a0309140d140a080c06090105070c020a050609130f15050306091203041b0e1503060412030903110601060903051b010f0509010210090b06040f140403030b120f030d050901020309 79
    0x581410f0b04100b07001a201c2040003c844681e6010740d0300f9880e82504e000c515503981043d03541200a509110000c0c1941d84900014014960010070603203000b0f25000520500e5846089074540110404002e072110503600d0086e05241c1352151400200c01c114002d10a080141e0390700568400d4020787d007404405030002505c8044a40c04901e41540e9448610b40100001c1064400403c0641c0c2018001190003a0443c5248541d18000e503080704040c0c480300f0940c0362602101c0050541d4003000600b951079200c0d500c010203452190418080e10f100b45a003561400409a0240d00081c629072424410420709002c04880506100d64202e144040d09001800d80c50006000f203003041004211000c0c40c1e882040101e44011061004120400ca01d027406510488100c3d1403030700036410000d606040003144e1181003040800c000c02c0b40070549071350783c0c101c0203024004c6c41d15030302003002ca07400d2154030400d110103040c3c0744109006540d940908800700c4140c6070010315215a0fa4030600400054100110344e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 104582652 1250 104581402 104581429
    0x18010b03160201180618061a011b03091511060c1b0307050d121d01050105120f03030105120c030303070302030a14070203091203040803070503070606050301061805040c050d050a030914 81
    0x8140004400c034046c0c2c16600088014020506103803005442c89402c11809000c410300fa078441081d5020301c41c446040071500d040081c001018032500708a080300004005411084034981168500ca104440d2486c01000b51048141c0b10f1000401804c031401c3e1112507111200d0840145082000c591100d41d1030b8100d00d2600d00c180f04044c1380d40c40d40d01d0290742c800900002c0481c8010240101e82034802d00811707003401698042c2c4000a903400030244001641d44408804c68021891603081000380140f001400303510366030707130310414185108542d0b0034000346109038042d550040c1c0703178a00091040251403c50b5019040e40200d002480111980802101c22a200a035212000854014522461442075a1010542d408003284c41d80030840d003c00107001d03030b50260780d0034450551220205400c84069100329144420307051001008059240c100e690700c075000b0a0007003911070b41c1c2c00108804001c0310101312141c2d00143d21902c00c140e0071903d5440501040300e03124443d40049004070b15034900701c05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 104583902 1250 104582652 104582663
    0x2090607060e010f090507090c210912051c0e0a02040c0f0e0a03020d0b2a04080708060f011211150409140403200f150906150a030803040218010b0316020118 69
    0x40b030840d405000b80450000140700ac20002090015458100c00030060003004031461850000600740b803910620644075030b01d40c11100c00001c07221050848000f89210000140b0314000e281415001d41d849126042c105007117a154241d05a0361240c000380500d0660034003c1c454260310000340003607120041c0c2c074202607a006030702e0809d41c0c41c0c4a4418244000131900e104100c00003100d809002c0c4600000b40c01152285000c90300042d460713000c0151104c40c200d8444441032030190040051110154412005074000c01e810080c445110b00401c100c5082c903c00320800140c00a01002400369038411140302e00b03110382204000b8186950014103002c08590000784444c0c0604421416203000d024a4103c41c00b0b0504071801003502074590002031074100c4000c1094080c0030001804500126000081c0540081240008508558400c40070341c102600a0b6040040d5400c0020040c02160000f07010300a500d66540d140d14151281600c41c08809044a0441e41090035010074100c0e11480e401000c0e0340b05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 104585152 1250 104583902 104583911
    0x1090f0b04020d02030706110d1e0c02010c1506031401020a02060a020c0304050303070b1008071a0a05040b0703020c2b0204020306010c080a080609010b0301061e0302090607060e010f09050709 84
    0x1400060001c0003c01c8000c0d42c1409003800004040d6004203c444c46402c010701500c0300c103010440169003001d2507d4017054441c18034240611171510800681031143e10506054280051a442d01400700400d00380c458201542e0798410300c144020080c0001c03210758654001e40c604410300e4002510fa490141c230000000350041182000c0306400e00544000e050042c0480351121900d040c40d104454055850302c080e2180c081010a02c03100104202041d1844a0310546500c5c4030b10744562000e51021400d1001c00c201400089442c1d42d01e400101503081c0250b00401240c1c00c08010004202c0410160500304420310050300800d100014684001940485005071655100307401030750700450010000b0701c0c0410004040c0c00a81d08018407500070001691210309036078941401015511080c040c01012680c14400400d23030600b0303020403c00300c1c1d69501d009030034010400d0214030540c1003d01d084960366103c036804551004240301d8140082c07100401807000000d19214036858040a0040d00300b406c2c2c81d07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 104586402 1250 104585152 104585161
    0x305010e060a2c0c13090b0f060604150e0a060e130225050c2d01020613080702011106010f031403030112030c111305010e0601171302030f01050c04060801060201090f0b 74
    0x501082d44030f5440039100e5496110401208130017010785000454100121034080350502310400034480c400d10000c0c0c01e045c545400c01704d0f61840c0610425a1201b00082804012001d071214a4060001c11094460f1000c68041c0c0e410080d0400c0c04501c8568010b1050002044a15082601c0480c000a0001e55600da403068100142440b98114210750231114619811008014440400c5201000c1c0c0c032545441c11610b01c012600c503c0d058136208030120070300d65284040340c20f6500528440d40305040007002d5a51410803d42031010903880360000016440080040c00072050355416445011000b0758078540c100f005400300750401c40c0024040081c8000e0060411003031100803031154500401e14044030340300c412000013502c400d0240c40103484030749010a00ca940140c102000d11200c0d24110845aa1820780000da000520001a68180b0880007800e49801085c840c80d8001e01024910507074540c14107130042c03c20403044e03010808581c0b418141401007290b0103500c81c00c081d40702801010a896 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 104587652 1250 104586402 104586491
    0x609071202190e031002040609170c0d140c010c0804030b0c130b04050406050f0f1309080c0604020f0a151803120305010305060109060b0d0207020d0c0305010e060a 72
    0x5111030303540e844140c001500802d140c003d00403e034004402c03000c81e000c1c6119810120180e001d14450300010940c0c554040c081080004a00f071010280c0e0342c1181c00c9a40c40c8800100401e01800e003ea0740c1810000081307007501c00512096001d82c40030702f40182c0d01d0803540c0d20624544600c1c440546414020b1011aa200010f4001c4490200303001c0790700026151203105427100c42d4800d104682c4218541140003540f030808403a428034054004100603030328140c210a102c603e44122184106269503041c40e88002050f0101a00c1c140411070b00402c1355281a10500c113100300312001040c45443e00d070f141003204101c0c95480b8103044c07215144c1980300000000c03808c04a00104d41001b001283c000d1150384181da030592249040ba40103408850060740d8510000341183e0340c5005a8008590400c01c00f100200310703070010709105102030420b13114510307a9140e0740b110400c15001140d2503515420001e000500400c00c0e1900480a0780c02001a41c1032081e001103c03820807a0f80401441018409015944 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 104588902 1250 104587652 104587657
    0x81504020402160b0601080a06080d0c02010e030d090801051015030b01020c180406111c0504020a0f0315060e0601050a0305040c050a08070801050108030c0d0c08070213050703050604050609071202 86
    0x686403d186041440c2d1818105103442140c103180080c40490008441c110b9a001d414101c03658400070703100c40040808203c440c2130711154144c3c14460250352520454800b0048203103642d105555403183c45052401305800e680380130f4090403000d503c01206103c08400d0350380002d0704014034100015500c1c60503005038106414607012541c82a20301081103000824803054622803485440200003548280c0e0b4803101c076008080600c0520301d01e040c4140c8196030298099600b050000746540022503407001140300c4c01c401034000300c031000b101a001416100c0709e801594040c01100d80304450528010000928600840225404250311040030800f805903207a40da5001e00b0018200d260099240c00c00c0541c0c2e100940301d64601507107840700000d2000c0020003600c8841c40060080c0440c2c8040c03d800b1076404c43c01010640310070004008d850016500e002e020300042a0b11900800c6038502080c1c06403c85100030321541c02030381001d04000541ea1130302c02040e44a5141d080c000c03484420104500e0090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 104590152 1250 104588902 104588917
    0x1081e07031203050708100803030c0c010f09060e0607080c09040f020c06090f07080c281203082403100c050c03120610170c07060e15010e0a06081504020402 69
    0xb9885810103030740d165040d0000c034440c00c140e840e2010380d500d6610706e8140b04a080c0c810740041742c2060002c03410600708a07004000e1510403038000f240c1d44a211200302d0484640400450b006a40c410000d028060300340320583d032020311030402130090f25004440d071a00c0e00c19254101d200316540c00349261300340310903410f8515080c1048c045030342c54a048045c150340c4003e9882c1c804075500c150f205c001200307440015489910b210250402041001c44c40034010345546041e1280e50716552013001152064001c0414004107019946180c581d0412400038a081c402d4031244210901d010ba00800554500061401e00702d2000c4c040001c5240d000c600490b140d000712000030304c5500000990110f00e0b030584040502a05080701c82401c0d64444643c2600e1307203500c01c4c0c050ac820103da08000381802c580f460203001c3c464012213010502c1072071501441e003005409030108008102c000d005005e01c11072000103c0c1c0c01005005c0c108456400d00540301e540d188508000300e0301011944c0045c04544403174055500b0b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 104591402 1250 104590152 104590163
    0x80a021b010513152c0a0f0602030403120e03072d0602030402120105040b010e09070f06050a0810060c1e1202070312030c09050f120607031a0901081e0703 68
    0x440c1010380419044401d682401d907040b00d103000304d001402103103100d511001d82605402c4207803003182d40f00038803c020340e010b420106030140c1154000841d141550034210315100f03000c01a5285000c0c0b0b4042d00b2108220740440c2c03802c0c40c10400a0441d800081103903c0990440c0308044c0700d801050540490807240c82140e02d40e1001a1600410011140c001e9400b0703038030846580c401c14802c210607d01303c0e8006c46014005018008c01040101031060645800000b1780040d00e100740d0300c404130780c0c04000041c1d0040b4005000010600c164a03444207100d6081320300504154911440c101e802400e041d251b26024140c410340300303070580d1404c1541224200060f48400d801e25800403e84002c0d40f42c4944d44020380f841c504205051030b0180c403912136856201e0540e02c0701030405081c4002c0c804814084c405d8181c00ca00859280325042c80d01300f20007071151030245c0c2c000c14500000202884444980c0701e0050044c00842b00502c40030380040760f12840000d07503030030641400b40219502845c0040d0381c1c1c005040d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 104592652 1250 104591402 104591411
    0x110a0b040303110309090115020f03120402010201050f06060a0e040b12010204050102060c0309030d020304030c0506040b09070506131e0f06120e0604030c08030901060504140403090f06080a021b01 86
    0x95841014000d0300031a806621650340c400c0107071406a850f882217000700c80c0c0c0240803000510a945403c100301c3ca1451140c4100d5012903001100c40317203076500c142c152540c0214501c003003104660b42401001d90007100906942e4590a200740400d00f81d004001403030085c484084d4079104141c64992282400c000001c011128500c25260458000c0d80140115070041c00f03460700084210685030f0842e40541c0e00000150f142030b0008100f4002074001070310403000c001d020007108010800802009024078003418890b031003810007401c090300c0d0a50641c01a40038000500c0900c0a00b9800711b92001110341000e541624172140795040503203000c485d000701400c2c004500c804540d003944109485041ea0b90000100840030004201d00e039158800c80d0700400040d408004400041c0290b4040c40d0801500d40021070003644840019090315020020000e604409800b000103055100c00085d004040716070300a810941000c0005041840040c001920a42c000600207217001d881c0441040c0d02090000810 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 104593902 1250 104592652 104592659
    0x301140c0a17240d05070302060a0903020d12020d032c120705010e06010506040311041e020c030d0b0d1713031703070215090a06090f0602030408070b090706050412110a 74
    0x40032844801e41c03900f02c03000c0032411052a402d00040a24040b50444001d0001c40c0c910b508101c45940400341201c01c01000110000050300d4000314039010318807031413000c03560140348240280740c525645040340401d800d00c44000180c2c1841d0700070040c2d4080130483c481c50504070740710f035034507000305000031403161100040c1540c10b111040d400420400000419504240d903514100714981c056800064031001e0300001e00c0200d0714165000303d00c07803001141a405a544480e100c0c1017240c0047c030b10100e541e000001d800d16802502c0c80350100350720084401400003800c94882901300444064804005007001805643e1504074401800085070300412108024201650740710081d003060303c550380944264001d04911140c1c1495140c42003002d50000d02c0c071450184c0fa01d00117013000300c005840403139058420301c000c690a8001184070707a01542140303988500da0b1401c102c0000004040c503506401c50282441299401412101100c3c520705005449000c035003411400040405c61180d03001d1008031000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 104595152 1250 104593902 104593921
    0x1e0c030a080f06030c01140d09020a06020a0215070c0e070c020301061d09010e030a03022206090519030c050607020424051009080705011808160509060301140c0a17 72
    0x114410a0880d4400e602e5440304418107541c5d01c0e1200d10b49003c60180c0d130300b011244210707001a01580110000c017040d0200980c010a80fa00d84035004840182c00050380442035062444101003c00080c2c12007504c0c003841034a4110f04500c15002d003140c00c18682c008959154400c0d0116260940c00030004c01040b5030f19401004903152911401c42c240302c940300040e500d00030602c210030101c54a000035515206002d0422070080d4065411a0b00a448145500c180c0001401e10600030b0b103455100c10310058200000c011001ca50b120604000030131a2006000140142092800316081a944141c665005100240140c000061291003000c00302d01100c0e89298140c0d02001212400d4031448816007008a04a41d032010714043d000e9030782d1120200304280d5201d280c002c5400d040540d04401d8454a580410341003401d01c40c04800d18411500d4240960b203082c682490700607908900801c0306981041d150383c2d8541004081400900011038108082070003490f030301602e0200c0420f4940b151070091240b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 104596402 1250 104595152 104595167
    0x105010306050702030703020c1909050108010e0105091204060f03060b07060501031101020c0a140604030b01090f06240804110a060c1e03020a26070609030e0301050c1e0c030a 77
    0x141c40e11410400415070740b0380040101d890740343d0140d02a090510401c028020b0410084454010303842c0c0c0c140c3d0008a08000380326040c081c14002002040104e81d0100b12400c3d80c03005415000b55412116420800c296107800b120300f12038050074070145052a0800541c01003103694031000070b0741c8000412404200d000e510140c166803140643c42050380c658801241d82c5d01540030415000000d4000a0001507036510300c4e04415140241070600c0c2589035500c000d0001e000703901c05100583c54008100e02d0420740d0040401505804650308984c191098180d05400d220403a08400e0080f8100403e081c0840c4200d8901404005030200001c1e83c1c1d12003009106d14105e00381610154000000c121417424100c410003006a09039008002c3d000c03041e00d8544000944030051041c100c0211890405100340c0e10142417158007844e4000b9600500d81030251001d02000749280c42079141404121106c2d400ba0140da0035503110a2000d0300503440042062030750b1050840c02d110f03500c07012030300840080c5e1202070b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 104597652 1250 104596402 104596409
    0xa080a0b01090f0e1f080a0605091c230a050d090203070e0106050a0908030403020f1903020d0803091b0102060c090109050301020d021902030319020c1c0206010603110f07020d0201120509010501 85
    0x1880c402940750100500d48044d1700740140400c43d0481e440490102c1c5094102541204610094855041002280c0c0200b468504044d401103131040603214944d80204c00300700d0300c0340c03403130084607251030300e40c80c001040c5101d60002d551402e030751598a1025034030200408005440c505604010740d503101c00001d09650088a0b1007400540d4030000459a00310120507101240e602601c0d200c0c07020441000c00c003050b030326490144c25011b50254004050f03038803030080940c214024180075550b4100f008000781426002002c00e410300d480081e4903040340c0d038001195544061061400350b00ca03585a0012074813421103a1106505600205104c0c032a015541d00070140200e480d56402041030740040142d880340000c41e440d0b00b4004910716010900d03401500201690100281030320440c00160020114601c3c3c060300b0540140e0004006214140c3c0500c01d507141503584550700c50074a1204000118140701b0018024050415082c200c011a400340d2076180c04001445402d104601e040588a03008240910 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 104598902 1250 104597652 104597671
    0x5030c0a0b10091b0309153b1e030d0608030a0201061509030f020f130e010b0a0311040c020c1c02030d08071706061902010609060602030a080a0b01090f0e 68
    0x1200010701030703280d10405030882c40f40c40b48110604000e42080c0c1c000c143e140030680c0e0061554440c0206098107100f154006104218500b00444030440d0804001d41c82504186074441c90601848c064000016048034010503800d11000040100d001c690550103003e080c04003081c00c00a000c100e00c00c001c4080c00112210b07074002c01c071503560b0f0740140c00176440401011002c0340c84224144042403005140ca541c960000d0100e40c00074400d900030554007040034481550302640c844480f42050401e0051880c280400c840640d82503007541c448407540b9251110880c8125555a500c4000354003e100e420f040b8540148849400e518800d910036032040d10301001ca00c02d002d0b020740c650201d40544034050281e03020395107014107501d00901c1c0e1180060041c102c20362007003040c007000780150440940b60b24000074681c000f28810385885c100c04195501c581022043d9041841544200f0f64003445042e8042e1480f01c002c50a5090300d8016181200c1d550002c02c00c0751030030b41c000f0450315143e1036450b00462451 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 104600152 1250 104598902 104598931
    0x302090c03071b020a1a0703030b060a0905010e0a030b01080a05010c050a0807210507090311030105040f02010813020d031d030f031603030b09010915080c030c0d05030c0a0b 76
    0x180a0301014441260380c00086480c2d000c0005100c400404a0f4003c1440075094a690a843d0035003094030b83d070b01090040340710f1400076024042503894080e815081c40c0c103a8095051100c195005070400c29580035850404c03103114201240c0340e9801d400c03400155045061100b055844d9600035881e14800c2c1c2081e0741c59030030030b10f400e1031051240040740c0c1400980d549020081e240c804044034200e4901031514100000020b00d0440002d00344540c0e4040da0b01600d44204241c50f501e496403440451409061003a4582810403000c034030324560b40e94580358246040c42580d0b540640c05001484402000381d0404d030911114020942c1204410240104515a01e41d4034612078081540c1c581d130422a52100c1d82042c418940030308401c80c621165540b190402080c0c94610101140d0b9818090740485890b40d20b8103d1007041c111030324100d50282c48107501400342080349102003642c0f0342e014000b25000c2e107083e000c00310030b0003001e02c1510020010507086e5948101207003850103011009803085860403184 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 104601402 1250 104600152 104600161
    0x32a09030b15011409060c1b0f010813060504080d02040311090a05100902031909110405070215150a03050a0b060a0803090d260c030304050d030506061e0f0703020601030209 76
    0x122409802c039005941e030311110100000784d0041900a0450550000002e00c000f41a624041c800e04690f130f2012110078007002c20190402c0240e5450001c440e0510036807000b404080841421040040c5800010114064031540340104280c1716601c030f00340d20a840410044200014a086990000c3d400c0301e084409455010302081200e80594098100c80c4a801c002c0000c84501e4000d180e003c03545840704c0b01075810385e00940d401d850150301c0403695080b40d2500407083d0b241922816800c15802d02c010106182000c203050300c50340c40075103290703640722002c90500d8241e0b4459400102640c0e1140a541000030185443d2440300c1080d250b451154400c01c001255180b03001041d00d1901c880285092042c501d43d441e061f100107101c021450301030300100e0a090440c3d00e4034008040314001540119600c0ca41820018188a03c4c50215400c150038601400640c1c2c1d900e41c00e680c6911700c1c80200a0006444040d105040d00c2244080c07103c0140100e0394001b410780201d4500d041301e0090711201100e070340307 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 104602652 1250 104601402 104601421
    0x303090d031a03030901030b040213030311120a02030a0e03010f060306020d05012c0a0e031603020c030102090d0311100e01090302010509030f040e070c0c030c080d020f030a032a09030b 81
    0x100b8508031074043c0c1c404d1100d600d0541c8280c01c40d400c0c03840043c100512f8500c03104007454031045e06410640200306040502c10004404202081c040070410302800d003000b480200c029220b02c1034444010030003141d880c4136200c80e9005e502c6828036000341c10b020024207540b403403c900a0b4001c0500c00e003400c1c0c2351000026241c112100307000414800702541002803114040390394048140504400850b55648180d9a85990300b040180312440125440b1040212036140007490a00ea40d06500e00a900502956009894110590508035410b05040010707070b5032070880b24502502d40389200303045405d01d2541c00a400041d841856035601130342c02409190f07a04090340e030b030b20310032021051044c0c4010002007054103e070842c2d00d508a145480e001d0380300c0040b0344417815282110b4005030740e4404a07502c20452134004000c15079055070180043d0810311040084941c41c0c1c003603414410140f6864520fa942d9042544289501d644440c5041c01c5500081820007001c141c0300380400c50361000c214010446401 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 104603902 1250 104602652 104602691
    0x90c030703030504060c06060504110c06090a02010e060a05122401030b06040308091206091506030a0c030303050604090203030c01020403020103050c04080613030e0d034410080303090d03 82
    0x3501512614078041c45e00c10121949144000207580a50b074980003c2000e5440c1e00807100d00f2440da0181c6070326002c803000c055007881c00c05000200254404400d03800141d030060081d0030034010880d030307181e154074048509564902c5180c0a0403640310b01017007044030701502d1840c010b40001c0da100c404451101d1210054080711803241d0101e511080c10301041000440c0e41004251005016055804c1d600e019401c207450000300382c03009040e03604060400e803106111141e5a0b940800e0490090881c140c298840130783c00c040324040502010b40b503e0000e917164440350084542c41d40c1c0901100c1d85c8485a9800c80c1c002e42080c00201d00003801e19011900b068248000c0d1010303243e510b401350072580c50390740c545054a5030340071045050044c29410000c2903910707220020480b50282e203031801c1074001c068428481003007540b41704500c04002d0001c5640090712008010898904605c501c00c1c5446100b51210100b80950021100c2c3c807000007040f00c400c02c042a80e203c09091503c040c803507280038849141024 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 104605152 1250 104603902 104603909
    0x403051920010b1c0f0f08030609070302070b060907140d1413020102070b0a090905180c090702030a03150803040f0e011508040210090905070e0126010308030403050d02030f090c0307 80
    0x5030304c42d00070035200c02e450070303422460303100b5100c03c02c001120355a20008040d01038016580d410000c0108140c40c10000c01b01c580c89900c51800b1031800c2c8143c3c1c0c1d48043c448025040c03038041ca50350700004002c2805039440b9032150220311031290f2039048000039100905404001440b1080307100000c20220502010550403150341600586400e41c1481c00082594012a84c0c000402070034140005820301c0324400e20b030240c0107460ba4904c1015514030010b2500449801c2c40c0c3c0142c4d9a00300f0460314903800300036251203c640d031030085040c014070483c40c4104041750b00710007410f010000700050a256210748200449100d0203000400e681e81e03180101c9540503613000c0380085500380740040c0051400001d803110b00c2e00e05092100416854030501003c5400840b08840403c00c00c6840c0901507820045004244042c0d01c4060660b12000c1d110668200041c84010000080400400c003014040c600382c0d1140c0c0003610b0115100d10b001d040b0100c0e083c01c252031003441d41c0604028402c25082c04642c503801e4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 104606402 1250 104605152 104605159
    0x1090606080a0c090624090b040f05031b0f060a0c05030a0305011d061005030a0f06060f02012706020c1e0618060f07050309070803070b04170301060806090403051920010b 75
    0x200200c0c00c05030031070740b0a031b6400b0070420803100c0001c560700742030b00d020b80302038502e02d071318540d8142c2804180b619010310312074031034103c000d852110065a91401200b0414890954860740c07907241840f026102c080c104c401c010800d000100380d03820201c1d03042e88018100c07008880201000c0036081180804008160f83c1c043c0c200244110780903803280203d0055421040610000070348a5034550100225a0160040790004414540740105150f09006503001540c8041c4600d046010a0506140c040e658180c0144200d0b000b041d80b4490403030500a5030440c1400e48440007002e540d6489164454000702c5401080315414801641040e2001903003038460355440c6840700c03540d102d1032410344071900000c10809480c0300725100440e01d484140050000e040c8540c40111003030a20707140450300c104814442821024082c4010040d42c0da101c1e41040d040203054404200945942c00c0403155071040f61500740811000a14100805d0790210307090f100c004028400d600c4000c0550803450070703580e10f980525070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 104607652 1250 104606402 104606429
    0x1308010f0f05061c0f0c03080a031e060503030405040e120c030703030f11030a0902060904111801020c100c08040b0415030b0306091b04060317071203090f0b0901090606080a0c0906 79
    0x32403002204c4085401501040806d9175240d440031460b610146d1003c002036120b19040c1d90036035415104490101650f442400110b04050200340d40f1700a51003814803858891036000718416041c441e240c050900c0e050810303601c45151034451354070740c01080e00328002843c26110054000c91403084140d2703000c0361801d503461a10752240c1071004d402c0c500003d981c4910108180b07882a0795500c00c22001e071140310041500c82d18146034a20301c074050b000c0030505540201c00b80c4105a074075001d48010140e09801c2c4406d080343c0c1403c0c40320490103550401e800311000007c001c101c0c00904480404444400c1c2c1e03042c0095101d07082415110b500a4409480e542d000300e19901c0c403900395200550107c0c9000d800021272a580362240307810203030007102590520070005011004d21010640c1d03460f1400071818140071610041d520801c3c04c000610300076026141105c08240c0365602074010320301e155000035043c0b01c1e440c6c0742d894507034a8045801040700d20b000c0b900d10008284646006460840710491010007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 104608902 1250 104607652 104607709
    0x40608010b07050708160503150105011710050a061d0f09070e031606030509070602060408040501050706020d0603060b190503060103020f03031308030d0518060105061308010f0f0506 80
    0x22140c002140c03c5803039006400001c2044c4a040040c0c034100c1c1c985000424116260406060600000d241e460045c0c0300300b8001407040340d03001008142030207909480306810750b0b5030031780c6846190a01d42140350700001d0320500055180d480740c0c40850044244000c0c64951f00003008220391a108502c5854000004200240d001801044580d1200c0310150031b5403c000c4014907440c00604564001c1d070301103070b61001400a107010400c095800746c411070000740424101919840b90b64040c42c490300781005000105241000741c4c54040e110f06030b28400007404025280d1a040000e0100c07944190300550000305022164005600500704a500c060083c11061b42190244801e0030207840009805100130081820703d078a88003910390003040150069521800400140002d030342c409404000c10204104c840040240e012880f1340c112070044891a50b02c92255461440f4544260f01c400b000d9407826162418070019a08403074140b0000c100104402e980c0c0204004490003031402411110300c4269004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 104610152 1250 104608902 104608919
    0x2160302040e0109080d0f0c05030f0a0b151308010b0d0b011a0909040807030f03020c1e1c0305010323100f021603020a0303060e0c0d021308031306090b04060801 71
    0x7403801c2d42c85000105014446445001140d0701001e20302c80569600d0f07422030003140f014402c0d0801d02d4004e2030306170310394208a1940c000c1c1c0e840181129030132661b1641d9021080d80c0317101c03a2014000070100e0380c540f41c50794500c414034680041e00c51419107508003400b074401450451401c8d1700d00d0b0340c0055076a505e64240a00742c100114200c02c03d8164190800c00030031140c0c0d4030841144940d00c60706040d907662a5500c0c00a02d0021041d8525080c14018805101d01c18000301e030005195014003603078810314a9920341e4520384106140d030014040401c01001ca0980e0303060f0007135030699010b010785103201c00c061207003040081c0440030000d0068021501000c0022001d42080d091140a50009403c10703888808500b04581d84010032000f591212145004040d014090f0000901ca20490084140743c00c2100340d200e88220300902180e00da0009106d581c03980c0d1204040064103002d41102e480305007082030036400402d0b6016140104030025070014044003186c0489040d1901c030303520b07030103642d1030700c00c21 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 104611402 1250 104610152 104610161
    0xf0a080603070b161b05091311040c020106061e0f050a11070e010603150509060f12070b21090a022e090f0905090309010804031b050a0606060216030204 67
    0x20698540110000041c0d609604409001003030700ca00c008108620711480d25001c4e02c51740282020a500c0302d650100810b649450203594085003d030603801030340e40c0b1071070880c0018201c00d0f0070a900c02c1c6030100d02e04150750b055210009864954481c011003080c220020004110140c01c01c20000d011419003405061094000e0300700d00d212403c10034002c02001040c182044119041144070070b10b1840104005a814021746c0794031034810881218160424000c64694100108140d00400440182e40d4403501d80c08110301c41c218006051b01c68141d20750100c042c06501c11210683d1a0f9503400011698689082c080c50103150000000c205030002131f401d200c0403404500c6403107518207550704520780030204c1403042d150101d25543c903609072504100e5182c3c004030746070704120503035485c20301000b1100e2000421200802e800742018002a136403031400300c440401144545000070b001c06c4240c000c005000a110103920b20641c014000c00392a01c0c1d0490341c3e8071400c840d07002c0d0000528002c01c05810726501 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 104612652 1250 104611402 104611411
    0x3070c020d050d030213090e0601140a08011802040b0907020a110402070b0906010305011503150e031b0309100c1e050f011112010e0403050403060203090118080a02070602030f0a08 79
    0x24402070001181c03212814000740250040110782c0016800074542c214013080000780c00f06c010704200d0400702c01c113400c0d542c02e8140103144140d050945001d0290b9100500480100000070003440380d071101c44013044400ba07144000301c2c0114104401d5488c1460110301051280c079680d0700901a1007101d854911100c45100217041e04264200040e00218981f00350311441903d0303c00003004554510703d020350071920422640030040803100024070020b40055440700c40d0440381e480c0070480006c0d4105c640c0c11031142d0f01008120110714000b2520324900440030301458403084800e498002042c850503a4400d12a5030018245d070040440900803004111040781c400340182c040300c4940d10f0501c501c42c2110814001c0c0640703520003082e150034103140c022409014226140009640b07040a40d000780190240d80402042150084002a040d5009510200d140f031510081581c004c4568101070169074401c2030002c0042c09500b10200da202c3c00003080b90074070b4103d04002450000c000c08200d403000000b07007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 104613902 1250 104612652 104612659
    0x150503100903140d0c080606040f05010507081207091e05010c080d09051603050601090b03211e09040b220f060f0905100f080c01050703030b0a031115030c03070c02 72
    0x6955041030702c60000d00134010820a000440c4610490050410800104260f200305000c01c01071040105490144c8222402800c09944a0400d450590000d020385203051003040d4050080000c0301d54481c01040480d9155240c900e101a105c03d08600030b01d5003030164a0202d5041c00c145000074082030010554000d030f0340b0b400a6008032964505090583c0d812040103030078500d07070041c82800000e002040c0101171180b0700700110b86c8410b02080c4c56084c251034408000b8820401102d041c100141158160b5036003034910154404980104100c580103180200d00841c90702040b03100c5030900c10300141c4901000603480300c804422484000140c010201c000001d540c46150010700311b170340c10101201030700c801c40000c107441c40c02180e40000140c4c44d500002c102a03240b00b080042c2c620220303031181e000d0f000b0301e000d982c0c03000107040c150040c4ca0007240068011405003800400c1c4428080c000b0301c007410440d280d4640c0385200c1041c007958081940c0d150040041040030412290062542c3d0800f10300c0070703 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 104615152 1250 104613902 104613917
    0x5130b0303030412120515041109030c120f061303030b030a110f062106010e01090303080606130506160201080108070e0f0406140a06140d03051909150c0501150503100903 75
    0x145c5c04029150203807000303260482540104a9645001e0140000c5181d11030706650a00307440900103903407820301c07400c1ca9000b1000005800a00e8005001340d0400c0034820048070402d0408a007656650b28007400305800003894503080c6421490049501d01480350404554030805842d01c00304103481100c00300240e400502000002c1d4100c1c4c1d4002d00002d201c18100c54a1090700c0e0281c0003605000038030703110030b04004801d04180b0009400c0301c0b0954011100340e40c9030b5110800780350380055400c1c80f5041554807070300101d2560681c0011104401c2e0080c03003a6101360141e40d81e055259071740c112074012200d4138080d0000140000450b20811948280680004950511000d21892a12138183d503117026040e115801481040102c02460080c02c03410b40e10040542d2250b20002e05901030018915000c02c14860700b20b032a50b10983c3c001001d003412501d51119848101005040c204100b5000c4900f0350800101001c410981c440c0c06049440c094042c01000c0044140c02006150850040b0207210f03c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 104616402 1250 104615152 104615177
    0x1503010f060311090c0a050d020708040f0806041b08070317041d090c1e060d09170a02010f02090f0603070207030b04060203060906030604050c010c080f1305130b0303030412 76
    0x181c001d1900941c01034900381c541d09a11400e04c003180703800a0055014032410084110100d6000c8112400c075142840010789a0b42c085ca008082071049030f01442c0c0901c411140070504003804a80180a684110400010020304542505240e0440d1180300c00319004814200040703012035a444022506600ca454901512001520b4031840300301c1611124500000403c04131410070040900c072800c04640030140221107002000b0150803241c2100d00030003020604e880c00a6840d004030a000754000301c41113005002c40d002c00c050b5001002448015030a0185503500310740b0764030803507030780042c0540200810303040042030240952001e001c03d0114812401c000008c02e68400181d4000d5100c0d207005692030600340108a503010015080c180b0a8120710184000141c0010354407419007420b003440124a4050b00b014030315405803060850382400006800705240c21280304403820341c0c10403104441140d860b0712502c000c968058840c1d030f0b0164000c101140100e0801a0b031140580c55515011058415 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 104617652 1250 104616402 104616431
    0xe101101020408030703110106050306040609150e030901030b01090503030405040c020f071202010801080c01120b0307050619020706050a02100f11070b01080106060c05121b030711011404030b150301 87
    0x2680300542c036400105040c030400d94051000100300c40310000a0000d1410500000ccd255030014100501a40d030b00c0390311400b0006410140b01607103070380c2d0404014900004244070f440f03502c20460240001d1402e41d03520300641c0142400c1c016140d01600450401d030801c010301c0000c02d1001c1c000d4003075101d0845404c4401c0420404040a00343c04901150480003a1001408001040c2c2100540382c0002c94000c1c8140d0703000c400400510241000801d50307204403800300e0305110b440e402c40d0360068030002c2d511251907040c0348500d1002103650700b154985075865108907401e000394507032100140c010442c002d200c0d4466400c5800000507601c000525035028034102050303030307000c40b0044801058040040090304800e1190000400c181d04005405c4a03180e51032603202c1e5a149582e000144002c502511240341c005008822400e904040303e07070320b000c2030520b8040300c01c0d10381130940041c000c8000c15102c413000e101644e040303d500c01e01d4403070951a00b016040c0e000b50000551901503690b411b0042d031058 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 104618902 1250 104617652 104617657
    0x2040305060106180e09030304060921090f0603050103030503070f02120304060515040203090304051302090910141f03200a2c0108061504050d060501140109060e10110102 75
    0x11180d21141c44201340003002a200380f505600c51003070441c018041200002021048960140e4002d10009104141c0d1030f043d6040d00e12040c110f246103e418440310010354100f0b1001050325042c207020010f0903983d410480a035030007404010000350701400450303100c41c0a60030f00c900e90802d9005951144408100240d0f041d081150309480e171680741e01c02d00c00300c0d21442c440b005111100762400d41c90341c83c0088116999100d103114150140101c020311b10044901981a1000750340024901969414014100e4401003017500901e402c68640c00e50b0088245000514110412104c0e01d13601002d0302141000c1c0e000b0a0407600030200c011800c180449244855002862401038075214031852448048821f540304540004119002c020301000c001541c2e002805250b1101041352512140c6c001c00d03820784214000e90303010a4120344d00d18698410031803207800c014165401100440e40aa00d420011540c07122503106800c04984042c0182c001410142c0c040c04c0000041d042000805444065590890b07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 104620152 1250 104618902 104618909
    0x5030f0d020906030f0a05090d0816030e01060f0e01080a020a3015060e040f0602131503020306090c1305040b030c0a1401020607050f090123070501090318080304090e01020403050601 80
    0x615143e08000281c86c0c1c40c4541c50300601114020040c1550141014082c26030140040701c41800b82000e190940707209420615007800100000c0c40600c3c0c0c1d41450110044090040d88098076480d000404c0c01e440c0051160035154004000415035442c1c020b03240310444084441d5800c507004510b02840c103204c00041d005030301d8451180300c0740b05108450703030b041154031070b0b04503a1040c017101c001d200c003040c4442800241c0700e4218100503030b40d9001c07010384118440700b98866241101c90f088181c015640603400b6500c1580140c41081c41542c0f81c00c101245803040994650941c010790390103011500b0503600c80b2100260240850b0380503803088002401c62082684800303501c4025041d15501564180401900580c907400c0503800d142c00f5802215913401444680740c100720010100303e980c800c0c3c9090000c3e203100d500c01c00c25501c100fa0306016001e0500c1d11000d030041a81c091510004e0201428030004071507514010394102803c00d01d130380b8050300400c4803a010382d41d028000030001c47c10a00155008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 104621402 1250 104620152 104620171
    0x7030f0b04020724020405060d020a0201140c0a030b01030608150a110714100902030a0609080405040501060e01090b040b040e10030804081506061206220204090914060405030f0d02090603 82
    0x30141309101901c800c9024040c034004844c0140410481902c42c0302c1039400c0000c2ea80b8001d6200c8900703480803801480003400c0c4104440180702071000d00320100000700780020b540c2d6000c0c08281a403400540076121948241001e07540310b03105001210180d5060b56401420815020030904801e0100c1001ca4209540650341d000c5408070155180720200a07150b00d141002c102840b045406070002515203084000161480fa1a4802403042250003002c440261000420812240d40c4802000380313a000094011404921500301c0864443d10090a440c11501011051450320382044080e681d082c4026103801a10340040d2004000205410b001d4000f400d45c07000100400d25109000b02041500500450b007ea0010054544420228003009a120700196419841840c26000c061081902200c0e140e04191000c5804070f04000203400042400f4082c28800032a028010b00c0107844440c01d40f07005001c0d50041108142003031000000d8a0222903500005041130451004205c5582c0b0841e000a41c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 104622652 1250 104621402 104621423
    0x80d03020a09050d1a070e09070908010c0c05250b0d1509020f0711010e0307080607020f240612010204291e0f0408150402180f07030f0b040207 63
    0x8142e000b07060200405040320707421540501626402000391030341d0080c105c843d000ca000261810b01808554440c68800782400c601403a0400009001c40b03c5805006920f50a2640203106a4400c040c0c0c1c424417a00013010741410780d034410a94100ca010341c215007001c0540910700040c6464090007421028070180d00c0410b45035003c2e102000c00400507000301c8405441800b41460404a100a07034104581c40901c200610303228a005842c9005664030055044c85000c070007250000740420014007409554080b10383d640d100015494542c0d8a412160b000c41515100c40203500184040307054104401400c5035030280031398030125003640c1c0130341c0056003002c448800b005210345004034202000e07410080c0450400070b400540e00301e01c0d072101d1100d655070b540101300b00544184000407a0f004000050440e1598120f0000072543e4040031201039124008030340ca00807503020b981018070301c182c0300b00c00d07841e0b2281e0700d800d41500208603901c401da861903034420703150006848502c010320016018500162 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 104623902 1250 104622652 104622667
    0x30a0b030a0f0506071103040603050a06090906090204050c121b070c030305030702060c07150f0b0406030f02090c070f030c03120509010f0e01270611040b07060e0106030c06080a06080d0302 83
    0x4e01e858000f0b86004100010110142d5100002000b40c1e01620722916021645490304c4c1c1069016141135000300130014170b405100010003443d940803041491081d80c042c401c60741c41e03440640c9180110220700807200c0740d070400140e542880070140b052142034004070314200101525844150a451741040f00428800803e12064a4040001c0d50380021351459a6281071110ba494400384944012504030558856882c81c40d01421500005855813000c0c0003005455500d04008401c100309a40c1070b0b0084440304e01060000481c801198502a0004d40d8010b034045980c0d01158008821941603080140384540c0003551000c9004450052500c840085080321801447e1400c54886840041c10b513850040400c060b80f8115040b954480c02c0e83d960941340007a28107148010700701055280001c00000036010445c0e0811f02c010308003036405002c00304200c543c0c840c00d80703080f581180805001410684c004000140c410070b80b09510902c61600403614590300e40b030b054941800b008007040807031303008110078 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 104625152 1250 104623902 104623913
    0x80403020c090606120601030603020618090f090606062b05071704150b030f120304031d060f0703050904050103080c100513030302210f191a0105030a0b030a0f 70
    0x5000c490411207400d03505040c030f800040d81d00c0c4119100f100d00e001601000a010b617010740e002000840d0060240e0703990380e4503000c44071450314200c0001c61140e0b000314040394068001748481440741400700018440f80d02d540c0f04004041e0070102c003451701c039520070450404101207940c00c4200d0700d00032440843c0b5400d00742c4015102e07002d244400041060f8040c00c01c004a03010b81d03e003100504c1a0f10300007449240050100c0d080881e0b40e550f8140500c02d9212040030300706010015413255019540d50060b030349050007112000031040904980c402000d200000d1000900c0008009040c440d0501e07525140320b407404102a20000da01c15140650040340408030380c1014095115880140e4104002d01d01e415260002828200764018080680c0805c2400008001400404e40e0b0040990700300b1b002c0c90544c11182002108a890b40c0c3d0101c2e0441c00583d074001d80c2c0c0903011701d03d0340c2d04000081010100d00110b429802c02420a01415101c1d03000325202e4605100f140031050141d41101d8002d0800d0505 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 104626402 1250 104625152 104625163
    0x1050414010903020606010809160816050a0807030206030a0902030f071401090e011a0c0303010e0a060b0a0e0909120f030405070f0e0a090c0b0f09040c08011404020706020d090308040302 82
    0xc03404241d0501000200181d80419040d40c440801d081030019519a00a06440c00401b50140240c0205003000490400000188144c0c0b10404040c100c00341c1c0d4481091044800c0700d40300790200f6a0000c40140018070340388010716402a1074000c002840265a00080d103132009040c00e00b041340c2c000c0c1d00d00b8005a0300c0402c130802031620a090442007140352500c0000412070510070005607500b804135070002c5500041c200c44c000c0001e40301b00c0c1d859507111042c4000724801901e0018405140590014150322070000b501d2640301d01c0e4450364000b101f09018040381c0c9100806250060103904451a0b0708e99200000d442d0004150002c2070b102e20301840e100b8546411a0010010384070300f04010031020410f047c4151740807840400200345402107161401503034103e500030314094803000c2080d1030030b103080703c002c0c080007101190140f03e080301c000d4069850800a0046500c0044d40803040940750074290024060a0b1188200500d81410907400100700c40e0041801c5000401c044140000c1c558100003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 104627652 1250 104626402 104626433
    0x30a0f060531030e0409020d030f080901050106050d0203060a050415140a0e130503120f07120c1209030504051003090209100e060d0f12030c0314060609220608010504 73
    0x520015959084580110140b54008010100072040d072031810242c403545c000003152039000e030020821040d00d01c0c0c00b0340540803481c508000203880200050821105009203812181d4a450300c0346041d1800c1c0109010751720040056400c4854644005a5511a44200f4401c58403c1940b40622400e02544c007101840c4d200855202e07034071100c818003151101c4210f1039006001d403039000c201c000707440c6030050940c091765a00d1004214000c08100c00c0c94550300040d4400d000c55500c9210a028810840f000c940c0700303d180c007000a4000b03241d2114040240c2c060b404060007420040c2c202036031500040c0c050400c00300701b8000603880324a904214203200343c0582e00203110480d00120681407003041a00030100800031841a50b201122100f800040e2400c007a02e02e4015030760304c2c6000c07120600038028061070929940005c0c5002916200048003c0100340280e400520403450003c05500700100c8616615810043c2e042c41d001c145074055283c414080144000c00c0081200e01e07260038501101814040c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 104628902 1250 104627652 104627701
    0x1107030c061808011104031205070308071b141b060406080a0f0e0d020f0607030905060a0504032c09010605040513050c09030a05070503060705041a0306030a0f0605 72
    0x14024800254401600e005550712480c0107208050078800d142d1000500da44208203c0d403030004220b10000d4040010000d9038000c04103240c04030400700c001c5400344074050015002500580c00715011a102e0000d902001400001920904011742c07114100c41020140e582066400164a912403282c0d41d074001c0c01410080302c006051616100c0003030580003004040c2002190344211181016945522882c0c052001c002160450b41c0f0380080031390380e5041c802e00458244030b180c0002e0744184c464003440c00303c964044007900c90350329081551000390002030004c606000d100ca4130249080219015240c80820102c02d40c401c20305400e0074002c400b5010303001101040000c21050180d070b110040240c00300341c05441c002442d81d032a04001a0b2600a20880c1ca030305001d800390400902400240303883c1501d0301102918502c0d100c45c3c6c400d44091007180300b104c1e10940c0c1e8400746101064180d001c0d540c8040c01a0645800b8442581c900c80103981100003140c08a603507000b44544441e08450205001e0000c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 104630152 1250 104628902 104628913
    0x80601031a071205090a1a18010209010f1b120801060807020d0c030e0a0302060a0908010b04060509070c11030d0302030f1308090f04090807050a0213020f120718030605060111 77
    0x1850300a041d901c04983d403c100c0c648840100b10840e10822010b100250800742c1075280700b20122418001460a403899855000c003d40c0110070030f0010720840e92140c605071100103461400c1101601c0350700d00c1d50000e1441e10b8105904502103040101403889e03581043d03a07040c100350b040a0014189100207842c610441d403020000c200d059411441c80c2041d180c250810342151288100040d50090664100940081021500f0b400c5035412802040070f862800c4000c3c443d0049070300c240001c4034104e00c121544108080301060490b0700443e800341581d4003660000c135141299070040303441d02060100007800281d0010810002a06051105800c81d001c0558214800c103281c8480740d02e03002d08500c0394031924544040e6861035442e0f512003a01c0661003601030342c8490072800c1c46500c4160b01c1c803040e0f0044000380d011044070401c0e4402c40c0c40c41006081001d081a00c6503203080f0080314000d04080a20054003909501c21900c05070301d000440c49100d003c16149070440004019081902030910107030b200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 104631402 1250 104630152 104630161
    0x409090b07032309160f090b030c090a0504050f0303010608040b010e040309050402030c1c0e010b01170a02090d02031902031b060304060e010b1503100b03010806070f020f0106080601031a 82
    0xf907040030345490410780300c051040e45401d1800c0781002c0800c03104061808403500d0001e20902d4084400049030040a001c000302981802455240d100d08182540c6c02147c100010300e405502c2e44c80f0a070883e00681c11243c034610400ba18030301e140e0003a00724001042e008410030003004640c210765409084c81215030201400c00d6500502403145a0107038500c900d8000c00002c00403544074007035400c00c1c954042181c6039820b0f1202c410340180249108482954240005014954041d0101e01c010f07000880481503107640d54403840009410040020354015416501a000759400300641120412884000d060144046c030405d403a0040304100b00d41c12965100b00040c2d40d0f500c84007565842508402d0110364403c45101040c0144910051230341d10600d20316404003c00b0361840558400d1410300f8002349256120841701000380001d2060b0302d025800b407030004001d5807251032802c02c4d0309043d00450746000278400701c07603013980e885401c501c4c800e600601c010010302c41c00d560403426050701e80c480b104281c1070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 104632652 1250 104631402 104631431
    0x51c0603051c1101090b040203010e1609020715060308090a06020c0f190b130e090606060901030e0a0204051603060b0a08010e040507080d0503150315060103090f02060409090b0703 79
    0x14140c042d005032440d241051124240120500300580b4104402000312503068600841e0700041030b01d090307019604e0000c940c911302c5030014507000104101e0242844081c54181d010029600c08601110545150048880c054415000d00409107103c0c442d480d88809006050002202c040d500100071540081e04110003a1104000c3c07aa951809591420752071031070403403d485107111944100d403050400640d00702680b801c100d009054554074118094141c41d00d2a50980e110800d840065014808000402203507000b58850b4801101403420707100c04404540004003266800c40342104d0a00c61403142c1c2c410700754148070b0719000e4141500e40d14148584401d00030010034050080d40c0e00c50070360034040340600c01c042100340c0c010050f0382c00312000c9000030003008195420995400d8020301c008092070b40149004105a04110840c3c40100f00d1175440360011009000705000594040c0701221200f40541c844000800c00b80c9070002001c1008455440d28004040307005003d0008c042ca8a4a0340b100801d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 104633902 1250 104632652 104632663
    0x180e07030803061509100305071704111e040f0e010b060f04170f030703020c01170f0a02030a0204170304141905130b03010e010e0f030a0e060c0705060406051c060305 73
    0x5815034240d000350b13070300d000007200b24442c4824940e48041060b042202890303160b005188034540540d100740340e00c284040c102c003030190103070b0b0300904a011440002e2441e0400c80401c003420b1030701042205242c160180490300315540e075a81103102a440340f03418400c19034240500600da14059894600c0e18400b50210000d502a078060711000381403a15000ca00c0d01001c21241413400d0340d580650340d80361380c030745030195a808504448602040c0703144543c4602c00960440c443c4141003600700b24106541e480c1c9584002d600007030a4104c1241d09000106000302d10400040b52812018010342d600c605000301003100c45450002c1c035129a40078103200c0b201e5020600c900c42101c03010303035103011296550208940a0705255084a41540c44c0c003050a018003c1500701004403802d440c240d40b0702c90394040070709403a8070440c17105401103005050394034078500780b540040403042d2258050320406512940022240e41c0a54840000a04081202008404c1000d4140e03a020b10f01141000b50a155595081e01c58 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 104635152 1250 104633902 104633911
    0x206090c1c02040e030a050409050601080915100f0603050108120c0703120c022d0108060d02150906040305060906010807030c03111201060902070b0609011a0c030d06180e07030803 79
    0xca040107584821521030b900305554076031800094980307405444000508030b8200740b080808050030303c0c012500c03e502902c0c4440c0680c0401d000f600c040b828402400004400c0648022a074200000c400a1000c0c8020003071400740016903000310789035241c0a662482d222000603071416032081086540380c1c01000092010460fa88440c0d04c5050611b84141551035500200c0d01035088501206084c0880c10803407841c210035440e03000c905150070000e2004440010341150700c15008002d001a940c0946001d8118104112031120101c2c90005000013007819504164000c888030790004040c0051080240b0601e80900b1109005002242c590340f44c1c1d20301d034002c521018115008c1e000e200c0c24031f030303c460b18068001d07082c1000a01403079940b600b100c002548140415030302c05d1a010041170307441c50b0020545040740c01d100c400c203001c4000a241c1c1d500726071100c1030391341d01d41c4001c001c2103441003043c1c060040207241c45078a0000d00545440c0e2141a1260300d107081186401019080c0001081c41041d207411 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 104636402 1250 104635152 104635189
    0x10501081311090c0a030c0e01090902070f020d0305130b030906010b030a1808180a0308090402210a090b07030c0801060f02010e0609011a090c0304020d1109090c010206090c 76
    0x341c0054108a801a156000495000210401000000c14000b4020305894915640400c0103105801c0200c86002d09880080d0004000362010000041316801900000b80a4201c40c0002907090380014805600c0301d008801290021402d1003c41c0e020030ac0e450001c01c80590407515524000d00351540fa2135050069030707a5500040089002e81c0306c10b5201501c0711107020003218044242d030030007031415002000317400e40d8101c05198004590501001c0842202d910490490800ca9030104000c040d4200140e007909112140d010306a45014181c101c6000b50807260001a104100c0d06008980340740003050342c01031500300680d00040e1540700f601a411186d251804912402c66030b84104c1c0074000204d0b04604902c15041840a02c3d2419407150302c2480d9402d14042001075204184004401c0c00c0310700c00100202880090098103040700030705d0001c4d1042050f9101501b080b0001150101c5c2a40c0c601681c0d4402042440c075946c0400101c5d812214000041160b070402900041e4001c0941044546 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 104637652 1250 104636402 104636431
    0x30b0903031b2503080a0e010c050d0c0e190503060a050705070308040203160803031f0302010c060f020d02040308030610030e120c0a08030c070c0e04020901140d02040c1106010e01050108 82
    0x6100d503c0311008078078000503414007a0800400c1c01d00404440040d00c03600e80051a003807503402c82e00c005200c0c48081100b05d0321400d04040f140c080700802414069801c905025140554100580d640c85804000c2c103000000703440564140006e25241c01070091102c18020301c0c21080c417078480d8125064400281d410f1405075a295641c1c4042400e0002017075509105c14241900070032080d1012019500c1402e04807684032004c41403111281c0304803443c0c403000c0c2c04101403030140c002241881d04071040244070410f000d4a005100c5044004030703803140d4030603a2162030200502610749411408204184041d280500c01e8003203031030303043d51500748501ca81c034100440000e403040c46d4641032010701101c0341c018544075164a00002c0b000c40652100c00100d803903004000001c40c91503041035101c0e02568016085182c1682070122040411107610720342540450785406580044e035940c065403040c0c102c05d42e038501e09103055100046c40e0444c1a0001801d01448100601a80c1d81c4000b01071790064001c5100c10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 104638902 1250 104637652 104637667
    0xb040314070302090a0606030b0a051f05130f0305100b03030a2601060807080c0a140f07050703030504091508030f0f1908060120060114120105010f030b0903031b 71
    0x34a03001d1180d1009401010580410001400c0c503800380e0121151610188101c400303840c20422001030a000b1a5071160000c3c0400c0e943c144480c3d5503103060140c40c2800c91421003c2c1d0581041d24a49a10a080304d840d442400d004110041c080c0840110701c5e10000e110400d030300c0000070f40302d00848400c90b04011906403000c5601d150400040b0540305048611400342d40c50300c41c01800d0100803a03598012035680b0010541d0740c0882000c07100c11010555036683c036900c500c581200c0f41d074041108100d8406051040130007003082403000c94001d500c2910b545680728a8401902d0507501c65000b0091000e900760300c10009400d006c01100c1213103100075401a0b4500c0c1300034103201c40340180b0100341c00ca49040f10164101c623400c00750881c055002601d59000c010610092100c10201e844580b41042d0001c0004000c0d40181412034a5110b1004041c0011040e40300000b5003100c909030f0102201c4410b10342e0410a1180d1404060340101e030007400f451461030100c805030420485005100401240028680c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 104640152 1250 104638902 104638943
    0x2070c090b0609090109141b09011d1f0e010e090606030a150306050603010b090103021807090902180f030106030305070b060a0506030a0b040b0406080a060e161e08070b0403 76
    0x1d0b121180c000346000c030302d56114651b000040032421170180515103801c01081140303925002c0f000080f03183d044942d180422010044502d200c1c03da801e041051510043c5007420707a00d092004483c030025140c0c00b5034100c0e508000400d88a21106118144612103252036000c1e00d40c0c80c0c01c90f81c000404d0790129030300d8581903009002014441c1100c00b01913031000000c0700300485034200740e008641c118001c0c421020342c0c904015240f0070070f01c002540440d01320b456924481c8148542c503402a00c900781070310040d0740c41c1250000daa20882011440d1500d03864502d03120703c0c0040c03100c40484d005400070044581143d401624521400c1c40140031a035080c1d00040d0b6503500c0e0ba1001001c4d200c06441c0b5512402c02035402c8002c5c4c4501182030b40b0903804c0c2400200c150500c0e104401c1180c408800415031058a5203404009100c0d070304c0001014003c5107400b02c1410319040000c80102001906500701c0f4140047d1203207036021903003100d0ac503504860000c11644200c80c040e076051b40c0d00174154034502c08158000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 104641402 1250 104640152 104640157
    0x6040609030320030c0a171305210f0708060901020a020c090c0717030106030e0d020c04020d0b15030f07141e070c0605030603100908030c07170310090b010302070c090b06 75
    0x20500d107100004440217030100c00720f49140064864202c150040d1084580400203000d502030f503031400c1c1104e0301e0800107450a00c08003020148281e182608421201103a00d050449900c240e050b0350340081c9040282c0303001045115404a03a0390001c43c00c2070440304000b500c403440e844030b03a40701d2020a800302c0e00c149051801c4a00d4998002c0741514a09084e01d15000389801c24420800842d1508010000e409004548501070002681c041d00300b862607501000001c0d0001d41c904e540c04c2765a940d44101d10b8450490360510002002221a00d81ca004200000d95200051090040042c201e0b02e182400c00041d090701c0d0f1120000703054500b4004002c660b0441405510342c00380032407105483c0000c02a402200a40c05142c0513825500d10701400e02e0f81500b40c0b001c1e010018141030f001c00002e212101d070f01000d010210300c1205143e403101074002c000060754000b925010f1103c1e0445008000705820792095000801080c201941004101c0e2a004203040141c0b0910903c940c032080d114a0643e81c0008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 104642652 1250 104641402 104641457
    0x3030306240d14012304050c0906030907030b180d0c020d0615080705120a080c0705090403020c010e01110c011409031009051908070f030909020c0607020c060406090303 74
    0x44a54841003450140c00c06450040c41080036418000000305e008115200062810214020709090305984182400700030480245017000f00c0e0824080780742d85540da50b00660050042070000d29086d800c5080c00c0c0d441c0c100140140114042c00c4085c5071203100e0201e400210915541451980c0e2051800850074000c3c141070010041460300c103d5120320100c224608040d41e4650f8111a9120303140d205001c07482c0f034a056821060341c40802d03001c00143c0b40100074018803078008240d8680e10f03900c1c00030a45400d001c0c2c404070702581102c00b0214255a200c00d0651840303500346482742d4002e8409211980303805041000e50304205401c0d0742c2d007140041c5502222060413000d0f040380c01e48680c1d045014000c3c24912011216030003000c400d41d0714503a03450b0001a030150800d111928248084c2d45e0300303a250400701004c60a110048800182003c1c0e107201508140e00c241d00079041d68504008020300700300100320748500c104400e010900c0b0325588103030004290ba52504142e0310850580b81403816001c0384c0b02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 104643902 1250 104642652 104642719
    0x902040e28180803040b151e19090912030e07030305091023070521090d0f0b1315052814041a07020102030714030a090f050c0109060206040203030306 66
    0x18002000b0130a02601d114406000b01d81f2400c41c5100c0800050414403005070f14001c4071041e000749649000c141101801c910200040240d59036490980290707a03084800f0b860314a08418103007411a0180200107048d8880c3c40548a46411a50041c10b14014004074074017440c422251707608440c2c01070300010300d2080d5064842d00340d050381100501d03803640b100300d0841c0e40c0c0c00b4984c12101003032024050a0641d43c8180e54241c1404070704000d01290b100659400c0c0d0f0f0503220000c4100110702e00c452030501410301c840d080c0544086500740308511690320b28408412038600b07810481d40c1101d44007141444151402c10241110080c40b00705d002d850003520030103c07070542206100c1000811007415100703088140c1e485e101d55444400030303402c03401304a480d540803c07c107080803209001c011000f50b40c040b105010000b070300e95a988941c100483c0940b01180c040d031103500c1e40000c0e50707000000f2000500d15480101410700d05070740840c0d00ca000161005016240680404950b10540c8548440110507013 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 104645152 1250 104643902 104643907
    0xd02130806010602010c020601030f1103030706110a0e030a0222091a090f07030f080307110105040609030206090109080f070501023606070302060403081009060902040e281808 77
    0x1050324944580003841014099840c11a41446030340c008240345048940164010b5554041603d03080d4070742d024804070640c5400104018000600180300e141c070140512022a91241e00c0c01c0005030180540b40c0c1628425800b88104d0301c01659a4825108001c0c8102d42c844084041d000191011b859020b03401420349100c910850100c846003400140300750b51030300c01c03a007c030022145d141c0c1d21007040740009418640b41c90310f0440070402550046811140742d1601091032180304024908540055a0803144c042d2920804014158104003480c1c00c1950000200202c3c403031a078400c0494807681000d008209004180c240c14440300398192120604074040c01c281c0f2151004280403401200c136200361201c0b28540b4911458107013013060313a01c1c0a916400800c001d4030743d074805640401c4005c100181400b15010302040c030f50301c0c5005510091203452805601e49040070b025070940540102411410b0080460144814070540003940c9020313110382c400a038120500c0d100007039400d0a54000b81866100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 104646402 1250 104645152 104645159
    0xc050615041518051803031303020312010605131a0406140405090f04170f070303021b0f01020c07080d140c01060e1005011e0207050f030c030604060c0917030a050d0213 74
    0x410440444100c03030f0708101e243d0b40d051228080f0003282c03d14004982c0180002000102180b2101601900900403242400100d240c03c030749690b801d8018500090001c2003c0c2145a8030400d00300c0076099803040810300c260440c2429401c0c0c0036a1183e0f400304030300d548540043d402c080701100d0240001620507001890501040e050115060b01c04030b07803107400030402c0750802c0410800d8809510b030206420345002e443d502c0c201d0181d0452604001600f100c01c2c00d50600103410044c0d158141050390025803540c00c0c900c0600d090a00c4c0354130000c5181c00141c460101d20ba4030039002030841d07400800c0b45031100d0403062010300400d07542d00309072070503414081801892040b40401c1c03021103600342d846002d0901c80d8200040ca04001080c1100543d02001c1d043c055032904601805000c10080c04640e104000d074000246071a00a072000d88110317540b0708100344004d42c01207005000c3c005c035562140d07080203449005660f91180305007d404101011851a680400741e404850450360b61a01100320180c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 104647652 1250 104646402 104646419
    0x30c101e0c0201020f060c040620070801051014030a0221030c01021201120c03151e021902030301030b1906050d0c0918081207020102070c06020f060105010c0506150415 74
    0x84800e082e405441161403803048510300248003446041c0c10000181081e20b440419203003502140444503580041001c4d85010030741c1000040010881c08002052a0034000300345030740003400b6003003d501c49692446103041a10b0005580010340c0c0d06462014200e2a502101039092042c00303000751080c0000035004180c40c8054010b020f40303d0108103440c0060f42d07a0000818010300d01d8100800c1540e034803104202107801c01d443d40305c8458103110003094285482c840030103a1044806050440341c1d000c00c2500305140c6845003a0540b00c9107000461540d41151110012044018400074108107440211075840c0e80a0304030b5401408050105413034035182d443c0484401c2c1c0b8501030048130600d400d040b40c000488101301451099004842d5038030704103210342980540240100320006540d0200b1400700010020381c1c051008021643c007070300091505040303041c03d00c501130340710398104840304003500041000801c030b40340c0042d040a0964400080c800224020b49003d80c81d101054030b15203400142d101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 104648902 1250 104647652 104647667
    0x10608070b04060807030e2a060403031701060c051e0c0603010b07060b09010b0405010c06111c05070f0915170a02090411070302190c09091103011505030c101e 70
    0x1081c1c0e0300c4103409a076803801d08401f1100c017142195420fa00682c00f400081a40c01d04043e5503001c8603450a1803644002c000c00c001c1e6020358022000a1400104110802d0389881d041c0d014028504d000d103071142d02d5454440c1d4424800030480250180c000c4031070041031041180c61130001010f40a80e850350b940303010031401a0400c81040e260103081c48200c002520b8040e15042c1038800044100e0308050a00004417070160070b503030f400c03600305070f0702c050010722034864401801c3d0080018440c4050104aa40c0c1c85058903400303450b007010f00c0035010060610f19003112004040d160f2414081002280380380080765003110400d4001400c640741403d00080c461190001c2c468032806550a01c040c00329044110500c6c81801c40240041c0c11081d05103c00005202120200c14000d80401d1043c58580442c0301c11110b0204045940400b007255116640c1001e0084000e1b00c1941c00b5909401440c00c400300751a0318241176164400c48030f910409a140c0d004089038659401400034203140240c0b0608060b0001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 104650152 1250 104648902 104648909
    0x1c0209010b0d0c02010504080f0c01060f080123060a0308070203010f0f021e030c0a140d0e031317060402120a05060406150b03010b0a0c140303131103010b1c0203010608070b04 77
    0x1c0c20410f07401c09050050181790702540e4420341c0d0f98030700b0002550f001d5051700800c00b02d1409540b104000248108448980806014a000002100e120308622030f07035150700c03884e0310700031101031582000510390300c524200341201e800148083c0da40031203100282c01454000c200315105407408a0070300704946150b001e060300f038041ca10031240c100c5c4008103400071400200d030b00604240003002069180c610542d198070381007415051480c104400d41180009480000a41070302c15400480d05c003100090050942c402040300092307095004038520440c5881d102d0081c400f034000e4003200c50000204c50102319010040390001c003a00c00e82e04181c40e108010300180c18003840d11b021461808509069160708590407030361000205440c0608040382510b0415120900f0f9410f898219980c5071042401e10045110b10032031066038404007020325120b444030415400241c0645c0c5007c512100d00e4070f5115a034100c00300c0300320340c1009004d00383c800a0b01402c2c45420864040c0650700340001c0b03103c3c6500240041c3c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 104651402 1250 104650152 104650177
    0x110402070b2a04050906040f1d1b09010b120c1c02030f07030e0703030804050319080601080702010b0307140f04020a020d03180f08070317130302010f0504080301051c0209010b 77
    0x4004103515042e2070085014040d842030500010580e5460f15601000ba004207400000c24014030200b100e50b10020401c0880c6082c0c5c02400e01030f0391003000e450080c3c041c81c00c201c65480603541403801602c41c1340513103d0b4282001304a103001c69004100e003c15150a10030200d08142c4603100c2c052a04065002515a0710f0481c80c0f000c04071b08524040d0007250250340c01c8500505030a4503686003150f2503a4060402d0340d0302e0208004103014180c0c882d9028070782500e15100c00d9400e082c108001041c6c00802041e200031139244c0b40c844d16039a42e0100e8040c045503a080011904034105c0800105000e1241030001c1d4000d1001a005040b941c0100300c1000c0c60342030b5107040082500c41c1610558241d0741700300081010140e01400c20000d5803101c050030701d05012f032410f10605004200351070124042607401d9019034401c0944c6608060f42409100c8200210410501850900e650f901c049030006000d254411919407140c82c51036032201000351407a07a00200702d424507594038034411304258440506403c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 104652652 1250 104651402 104651461
    0x20c0a090b18071e050c0102030a0204060e0901060917030f0406020705090c0c06070f110f06090f070b0412021306150305010b1207050c07170f01050702070f03110402070b 75
    0x3500c2c40a01401d104010944070100400f1200310564042c219051148080c0f104c10f011100c6504800d101940c4503c4000c1c03001030351103081c400e0141442c0d030281c003003d215406400c0140003603680070041000b00d404010300c00c1000503044088a00754042e181440000b800081800112140d000641e4400c803103059441781c2c407a480b01400130703616110781d440b282d0050380800c0c0441d9845214078540e038910380040c500340d10700c450740c0c400035410044906a00c0b840d960080c1c00b400300d0b600061105040c8400088010080c1c01d00d01071829030300d40074501c5a000481003002695003551200b0150f890611207580c001c000c22516030070b01c20000c045075441030000918220000c20380010010450b02d5030f00d0440c2c0c1e0000b00da030f0744840c2152aa445550000e0a601812400280040d40c1e034111000115010b4041c1000684d101011421540014406070456102c0f41042124640f02e44001084e2030704000d040c070080e01d042d800304000c0e00c51340d90b0003041207900b20304001c6c4140c410700c50b5112901080c41400d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 104653902 1250 104652652 104652679
    0xe06120c130b010e03161a03040c05010f050706020c16051008150a050d05160f081902040615030501030b070503011d0403020109080a0c03030f1e1a0303040803120601020706090e07020c0a090b 84
    0x1f034940c00300301c40c0206250794100d0144982d6000d41d041c00d031f291100e4600185070400c10ba603a10107a07005562410798941c0a045000203800418041c074000c0c0005840f007646410b00d206004091650140103540054041842406162512003030030010f4040a0021141a1514a0050759032200c0e54041d0f519900c2d080404661600c140c103915013102d0307182000348098010002206005451a0001c0764420f079103100c00940340780c0b08050032303050420741c3c6c03400100c9615505005241d038a00528540420504000500804100c02c0040820000c81e82c010604c80ea214901070380100b12a2401070114800840c00300220b1f80d201b10400c4a0b40e110741d409021b079681441510382940e803038041410120090a0200c11418503039070150200007000b10203402641c00b01c1010a055510030780151580390130026100808003048001113402c400b0a1009020711352400ba0001c003281c80a00808540c0f280942c0450300c00b0f84200700c1d03a440400010301050015988101701402007004100450045c40b1a00811 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 104655152 1250 104653902 104653949
    0x4090c0909081216080f060409020a06050a26011701020720030c0409050706030b01020a06060608010e010e0106170a0f050106110d0201052511070e06120c130b010e0316 74
    0x2104c07100f998850040640300c010a00c542900300510f000d80140c1c2d5101c0000c0941d4411802c0d400404040e00c905981c2c400748a0020100060b1051010002e00b00d0240c45181c4122414554115144144405483c000307440300039019100b503040c0904200d8960610219410440b18000d0154000301c0480b8820f41928081c08241d505101d406400382d0024802040b5960298020000e9640c0500c1980e107401140c0e500e42c2c04640300c6070013050014015800501c03080c039482e04101c0c05411505200c088540c584040100008051001002442c00075070116020843e540c0201e02c0b0b070016404103000d15a100c22000b0201203154000803514403030880d1031100c1c68010f1007178038042d60051000300c1155581a840b5024108036160b85401c00150074410007048109000c95005406c0c110000d16003420f1401c100301c4000b5078231482148a07080443c1074041079840c052070f2248801c5110340401d940c0c2c3c0d40401620380c07055071025103805000d1003e41031010400c42e2400c1c0240c520008a90b0071401048e043e0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 104656402 1250 104655152 104655181
    0x60e0306061e06040503100b010905030f0a060902010302210912040f03141203100303021e1905010f0906020324102d0201090b0106020105070e04090c09090812 70
    0x41d641001c400020841120a1074508052509028105501c4e0582e100046071820702e0303205684010941c0d6440350358156034403402a100030b0500f14000d00502100810340380e1a15040701d0010945907451503e4001c590090301a2510f001d82c0c0e440c1181c04000c020f0700c48641030b100b25562055809410f001803c00c040d250306171420b507006000c10088031030039a81d4020103070440018070b04440c4078910302980741c8020340c002136114501042442c003000d0300d58500640340641f01a414003242c02403022903d900800040c02141c031044000380b0301002512800c0c040c1c010080f041d408074401e81071500d1003040c031489070006d40c0228250710030700d8a150248a810303001c129150f000103503c40410161740b00114400c00407000c00032001c4070110501c0710303110f118000404003032010b040540d46407001c1a0a10449025487c014011400240b1007440c0a08006001d06d072110003492080ea502c200005c18065040c060b940078140a4004100e090030500340035450b50003603180e076420381c107140000a003010104000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 104657652 1250 104656402 104656411
    0x9011806020d0b091311040209280b0f09060703090305190b0105040501050d14071e0504050f010e010b0a0c020a0b030f0106090e0a0522060c03060911070303020c0709060906060e0306 80
    0x403211700140f035a65101d00749990404811b50098080c48440559682c90502d04c40c3c0011144040e00d0940d07120a03ca02541c0c11580010181c807410310898480c044d40004941410000711440ca0ba51a1136140a0310b100c4465003000e002c0b13104201c1da1004140002c422090142e002d280880e050303aa99134104000e0b1202401002d8101c20100c801c2800074200c6002000e20042400c1911000e03600c0e002c100b1a4103400b00e03054003008144407010407003800d00d8460300390080c0e070716001c2d00034035810203241008511042c400c0070001071000481d15042441a00141241503004100f101d2065503040420b12641040d9062050200001e0001400350700961900080b0760550803201420368400c1c100b0001010000d01881c01e41c01ca0410503034148003000b00c3d0b40d80c051301c983c400051005100740003c0c11140700d40c10101c001ca181c0304030488203440304000e43d0074060b07041c500503030303280ca40003609410014154040d00c8204e0030204003151148607070304500d00342c130780c01c1d90791102e1040048200b47d501d41c82601d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 104658902 1250 104657652 104657671
    0x26031f0308070b040c1203020102030a050c0c0a0809060d0f0c0e0a0e07030209060d0227030a050316210504080105060607150f0209130e1902090f09011806020d0b09 72
    0x1240300000f891980501d68042d01996000000d240d441c540400c0841710080e00b1070041c0d5002007044444460352040640002400880e80d0400c611a204150b40f00d94030400607000303000204450080f66a184115150b0f41c8401105000f2a0552198175001e270450210b1180852000e440428070f508002e10544102d503c01c4c900a84503840d00b1300190700940c0003410454000720100916076603950180014443c1e91001d08500890b1080b040d00591484400c00313426119400038484403010034030001c19190351401c4550f180905000c20726100126030304c0c80305213640c220207100420b144207401001400844010000a000c00c0c1d94640401181d0310541c82c00074410200442112250070a0f58810f580b405030b119001807a10745e0a500041c030040301c5820000b24a501c804120100000c20700c459030180c949500385a8000c0c102d80e0005038001c400418140c003081822001820481d401d400440c06200c410810780d08d01d44079400c040d0042d5100ca03400345070981c00d1030b0b42840c5906100c0c003214420203600 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 104660152 1250 104658902 104658907
    0xa021002031c0216060c0c060f0c090915080604050a14010213060c060605030105190e01061203050703031512140c0a1a070204020c0102130b03040309090926031f0308 73
    0x480b40d480003508200c074681d40c1d0814001504000840b14812000318003041d8448460550113850060160307940052200250350500343c0312459143c02480c41000e48502c1900450044090380101c103c01c0000c1c0e0000b9154464102444240040030030800c000380d000e241440030103c4000e43c01c43c00d034407505020240400d1011020807c19208500700301c009032180b400803d40c966610002420b40c4d4060b1101c0f42c44001303001440340309000b5032049081c144a01c0000b07100b407a24026118050542911004e0240b01000440204062081d40307c42ca50341c44c00101881055100d036203a0f0340c07041c10000101d032800e0b03542d6110b03106180001460741512100400c070003141420041c81c410555000007054807035800500c050303001680c49001504031090440d00042e110b0006100403100e0940985c4298140d010800610021a0b84080c0003016a03920180c003040ba071003d4a81800360040b40740c1003a44c40510090b00d003290503802001540034100c14042405040c40f00001804d210035513100003040d18504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 104661402 1250 104660152 104660197
    0x10030b0f010c0f051209041d06060616061803090e0f010b0a020f01020408101b082206180303051006120b010509030706020d03060b0306060702012a03020a02100203 72
    0x340c44100c070030340c45001d0b0f40c41044910390314036160101d003080301c3c203c4800124081e07106050600c210710b5a40c8540d510305003460b285481554403042c01600c084d0241d44001401d85400c0c0018541040d09580710b01c042104501210652081e5401c0c48812400207011001c0000c01c051601c1d8214001c0d0000710151f1403991070301c04590407540c09643c140065004003400101e00e01800c2c40500001c1400b0f0024059000c65942240111003400c4015414807500b1155025415804040c080e8440440e1007099040b81d002806041135180002c001002c180c1040d000c141c4c3c1075600754103820703801d12989040c0140d840d4150a1044901d032805036400040880305039139805650741c0c1081c445540d060410034070700792840c4042410a0403c0e0006409a401905003e910691510070640201303502c00d101815820709000251143c802ca40c0081c0c100103a44005101d20300c603c2022941c0104d6140303103040b40044e640750194849604144c26440f070320803140c4080c1c0c5a8004402c80342000c10701d0100c01c002414 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 104662652 1250 104661402 104661407
    0x304060b03152410110715020f0f070e0a0213050406181103010602031606091a0114030d0e010f0201060b030a09050f0f0a02011b0204050103030908010c0906050301050d111302030610030b0f01 84
    0xa001c17000fa109449805800a100091a06c100c20711207090350150220021800d2442e14140f2080b2311010309031700c1110308120b810194810741d6000704038880051390310160480c5661038080203401c000e501c00d141010014401c03440c40e00c1040c2841d828a0b080c04200c51144036844c06000920031280541c104000803a600d090300c240031f1028910900300001c030206e807500c0e000200350189024071542140c00006004032000b99100042c520700440051504540c1100700900358901d42c04900e060005455100212500030b40098000d0701d95014178940782d1030700c500c880018086c00305090310503005484102c06030540114407901c54007a0386008001c41851613004541032440d072120101042c3d01441e28078010381d1580a040e000390300950b600260b1508221202d421204120480d40a206e10484104003168208069904464003124020030740c81c00c0b0b00741031000c200a41c01441d40480c240b17100d00b40440e0a94040d602400d070a5030300540840d0407070030941c101c0d044400c856a110000e441c1c04c060035803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 104663902 1250 104662652 104662667
    0xb010813080c12090909010b1008090c0904110f0306131202070b0c070f050306060306010303080901020d1107060b2b03030b09040b1b0a090b0304060b03152410 70
    0x1442450001d02d00003a07904041c1c00c000c91501d0145600c0030016200c20b2501d003000c0d4017904141400020000410800c0006140d0882101da800c1400759007000504405003e0088654400010f41042d009240c0b43ca0401034198007000400e03c035804900c190207050a000407624440d090070106281c82c494140c45188110141088040461040c41c00c08903005180500cc1c01c942e541c1e080041012600700910741c106032441d504464000d5208108104041d0b80000d005c5044903050304080c0440e41b142003125000e8031136603030085949810544603880c00c40c401d100500c443c60040760100070300d1800c00100465461a010104240045003043d40140c00c43d003001078041501c45e0070001982011407000c240c003d002120f0035203d611a29080100040c512500240384600d600c80c92450025100000307407820010b40956070000c0c401000007000c00550f81d210188201c0014100c940d52400107840c4e01442c18200c07034040e0401c0c003c1095100b03900d20b0010808500d1001003c4040b141e0004804440070b0303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 104665152 1250 104663902 104663941
    0x21002090d08071a131e0201090b04081006050904031d04060e0109020d0f1b0804050c040207080c0c060f031303033e0a020d050f0d050106030509100b0108 68
    0x301c14046a4030020700e5200003403080b01d215803004550f00c055054018407016005142d403030706a00300b081440005a211aa020b16003100c00c00200c0c150030a070004035400501034010003040500014085241000002c007096210010582030280e9521403050000300300007602c0040104800b00303104104501c0402ca41406d030200944002625540d40d0b641a130154402c0c1d1100040980c0024030f500c2d003c43c80c1c01207241c1d030031401070103000c526106034014001014400c100004c01c1604800704040140601c000c0b4a080030041c800e42d02c444250400c400c05500c01c0004124621a0407100402411313700d06644840c2c0c0d02049150030341d0b80da01c03081640707818a141c0803002c050b52004440c1d0b007048e0f049440090555070b130310014032803c08803010004180c10308030f01110716401801340041840e40040c0100842c1c01e6032030510303240e080d420741c1c00c6c034640549800c425515040c02c00101d407440d03041d0701451203100c2c2e11007241d10100081500004440500109070700041d6498000755001c003400b209007051 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 104666402 1250 104665152 104665159
    0x20a02100513060302071103010921050408031b060702190b13060f05060f0405061c020d06091b120b0703020f0c010204030b04031806090311041b020c04060605040602100209 76
    0x4240d28101260074a42c15900100d0101c0e40c04110b100901030031981c01c07504254250000c1000a04a48510b451103101c442142c01041008881d500703a42e1054003518000c1c00302d00300322501d82d0280c0c44052850056206090814450a800180744038400140c0d030a074143c03941c07000503400919403142500401c0040c89842e89015458135800080d481d4443c3e89200c0c0c1d180e2100080c0c40c1450810413354100310f40d2220321071070501051160640d80c0c0c851100c0760a499041540380c1030901d01c0840c03515044841c001d4051303464010742d0400c1c481c201000c280311400090940e44d40c640c071003c2da0f01110544141c050081410500050700039806540100211400008503a05104a0364583d9099a2103034008440038480c40041c00b00f0540c0029100001031003c41400742c0482c00c04500408044c050300c000b07030400c5401d03102c0c041ea6845039840000354460000d01d0620a42800700041d40c0e076080311034818040d07840c0070000a6114401c600b80c0c0c0a4621950150204001c041c54a1010b07401c8001070540c07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 104667652 1250 104666402 104666407
    0x209060d12122a030608010603021806210303060f0409080a030506060d020c030c0f030a05030a0b010e0901080c090601031503020105072d060c0903080a05030a11040914130201020a021005 82
    0x143c41c08103400707034402c02039004002c42809024020050545a2640c003070341c1e0507070618030140700503501d50a12105001c099861a062079840c1c20014002c0060700a001420320101c010b240200d280101c000e40c803134041901c0c1c0e1295000120180310440c0c0d0300c20005483e400c0c040c07020221851294101c10b802c104001c2c6120300f070a4040641c07404a82c07010041c20803030ba000150203005100d050201c608c407a82800065030900c004020081d2192200400c18103e031035888100c904c0d076031301403034040c408100d0107082c1c03164960b120b410490f41c4034610840d0714407800490740054101e40c424054054011300d60030300f064805207990300548203034200c400122841c0c0303100c00400c0884001e1a01c1c0b201010803202c0300c00b000d00d055090010841d038035816104204001441c0c00e1021441c03000494107103101ca0710300269683c0d43c05082c5001003081103030180103420001030000b4002c04a801c5050003e4045980324040d4030f4643c0a201c900d0090040240540c111540d41000751903e034403c01c104081030304100d032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 104668902 1250 104667652 104667671
    0xa03060305030a02030c07120506010b1324080f01030c062a030807090801091e023c0f150708070c0608010612022703030c010204120209060d1212 64
    0x2d04580002900c100140d0010031740300f040c100100706031002080003040440002000f03868154840038140199002e034803000074040004a68806d003500102100081c002d54280065019509020003030380250012f407024001c500d01d1850749020f203048a500030601001c1d00e1502c0d4040c1e13408511003062103030302c11680710503400740c00f0102c580300802c52099032404001d01e80030501a001d040160098882c980c90a66481d0000e45119002ca038050700d4010000d021103200e01c00129540c101000c4c00043c0070014001282c40780ea81050a07071500140e8280c07555160766007080c02800c8090840c180c3e406034000703520b03203030b01f0304068001c01803140540a00e500c1c011040d1280414220f00e544408002034040e40100300c00c03940681010340301e03000160301b5031070704002200100e13410786070001100e0721290060b1125619035042080b55900d4104000135500c90359602c010f00140002d950040c0d000b00c405c81c002561520f841180e0100c521707841707119640c030f900c80180c04590582c510708450406079660410007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 104670152 1250 104668902 104668913
    0x60402090a03060902030f030307170606090d05010507081b0d020a03020405061314100c111908060105040e0c01020607180b1611120c270108030703020c1c02060a030603 74
    0x460146000e80c00c045113020003841414a404e9000410104540040c000e01441d80d5010000d0495a003002004a555840790400692a0b115910b4010b030b019034210701a078100a41908154030416540d10b8400c0c00f941c3d43c61543d002030b40c1001c4100c2c0012000c00143c25400030940c003426141c20f16103001400c19032590003203075040d0f20030300c40340c104050300880c10000344c514140c0214900c40107403103c080e8030301c85880282240c0546c0100402c4c0e540c10031651120342d02c502d45130b00300c0000c020408654850f41c9001945d100d078028002c2602507424200c88200310b0400040d807280b40c500c1a0300510080e56200c104903850f848246915540b0107162200003604021400035020050040084007042c2c9014640222860910100310780a542000300d2080440c0011034004094a82514144a5440c40e890016000f8940c2500140a001140008030f281c0c07400002404076680f09408607041030311160104507080c0c04e9010195102c00c04114117200504040d005400c4404803403c0104045850ba80c58 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 104671402 1250 104670152 104670169
    0x3030e1906020c0f190b060607080307110f0105010f08190803071d03030f0405040e0a0c2303061018020301050a0b0d09200a0e0f0402010e03160909030305160c0b06040209 75
    0x885c60050b04400c40c400034041951030064028400710307000707851300c0383d25034031201e440c0401484030003842001d00f126540c40e0b00600501d806940c20b04020401e540e11101c42c2c68000e021070254a50074460300107407204e40c81c422101d11036100d410043d680d0460350791090444440d04407030002100d19252041c2e645c038139282000078010003c140141140c0301c07410a002c2c803044440c0072880c0ca03290f0340103114003408150b40a10314016240c1c0d00d0703075421354540071021a20310040c1e00d60305290144100402c000b50800452505019902135010304909220031a403002e059010a02401d5403102d812481003001404040090186841c044004100101c40e602d41c40c1e00200b150704411505501d80000614501e0b00c103001e40040e00107030040d1a000e0a0011840e4204071004200a051204e0400311200c142c0d130401c03181170b202c0306e4950003004954481d0f120b100600300c044c10403001b086c10034001c240e1602043c1c2e070300c0041e001607640d03208954005488941e0031007406011540c00590030400c003040c0c2d0302c40514 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 104672652 1250 104671402 104671423
    0x110102120f13030c080f090a03050c150408060601051c050a200708040e1003020d1a10030213051506071103190b010909210c03030e1906020c0f 63
    0x4800344549040000940108001400125000e0040c4401800a5045054003216903001701e00c0a45910008440d0034481c4a031020340c41d4402041d5400104000f030001b103070303680d4040035907401c1e04104810645820601450050b089160000c0380068040d520500107440c103502401c140d504400380880c1514200d0b0b0b0150351840405844200101486229451001c0b0b140118281e407464486c0030385401e9228000c034015a43c000a40a01140001a0740716414004c0c1d80c00400d1811b040405242180750080303480090040d088888000614031450001d5207800c0ba038010345076148403440d101000c2c006101c001c0140c0e044051440644c0400c0d1a0031000c2d00c103d61150030b50820030003121007058070f444e401c2600d0b035481082841c1e00a0005006c40700307060440301840380106000440b89014a055449a0901c3d02480101701003080000c1e4094200c00300140251401c00400486800c416154001c101e481000c0440c040c0c120300005606900520300298403005540180d900b5410340c505100d211072 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 104673902 1250 104672652 104672677
    0x3070c020f010f050d0b04020f0313030801050d0c0303080405010f050c0a090f0b0f1804020d09120c08091903120903030807050c07090b130905060a180f02090601110102 74
    0x698204500302a5075211107100309091841100c1d80c8118010040d101c3d07211060462074848501249513140c81c0c060303603404000e0110300b03612482d0201ca900054816003c0503800658a407000160300c0c10f000d4114207035a40c000b13011300720850540d10181c501142c0904110352a641c0c4405a030081e10552180c540540b451240c2c20f0765624a882d0010306022107500245003200c94140104444584a001c07a4450100c1182003a00c80c0341184e44005140d0115408a4005000042e104070720207065001c1a5100d200f004581c0c1c808041030402c07540340b0b607a20002408010204100074080ca018200b0400340b2000d03400c4041340e0382e10307651070780c05003100740d6141c3d40420031407001402092340003643c0c0e540c8400726182c03903810111200c2d005555101113100350864140d6911140d28140c031658410b80044c0c0d43c0f5030082c07001012500c2e016a80d19001c44100c10b5580c50320200d1703110420a55114804a60007984841d080d01c040d80803c44620005030006043c00142071013913103010001e001901d00f030075146 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 104675152 1250 104673902 104673917
    0xe01050d080903120c0c010201050f060108092109010f02031303031404031703040507170d08181f050601020703020f0907020304120609030f0f020307140f1009060c080c04090b060f0307 81
    0x40e8924501048800c541f419a41440b04001c91080b09015007980500246400c00e440e490f540702140c105540e22808040c0107440201465812186c80c004101403070080ea84c01c3c8000103080c204903140d00415a0080d20180001002c1010078402e203021650b60846c600706030f203819030f25aa49803410010b20034401d00e0035004000c020922005200c144010961f000600d5145140035480a8540800c9528042403104003c00f02c0c50307803002d483d00e04400b00d21940468105800090340c2d000040660320490500c20b04140c00a0041d500c04101c10013100d42c0030703000c11408200c42c0c0410003140c0f001010101184003d100000d001c6210035416401c040c080c1c500081c1c07079406410b0013400d02c250301022000b4042407501070500641c0c0001201d041940100c0c07c500c6056034420414282126441990454854012042d2990013158040c0303e031076104420030002c100460100703503981c580480d025041d0110502003000f5429a54200802041d4010055403814914030102400707904192088000620078 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 104676258 1106 104675152 104675167
    0xa03052209050705091f0525060204180609020913020307020c03030d0e0708010b1c0f0b0117060601080606160c0e012403060e01050d08090312 63
    0x81c00061046041801008096400c00301d2510703c07402c62602d21102481110003086185201601c03541c3c103200b0b8072010380030a10200071141100d28001030500300058590710082000e042e2108962440c0c0007180360030300c2141c01642080b00114410071910039140e84a038202d00e1290300c0e0103030140e901e540b004c03000c86c14100f4102501c0e8041c071020601180e0708682e0b802c00c0d500001e07a501240d04242c1e45000d924280d500142459800920b81c402d615041c41c2c030529032440c0c2c24042d00c20801c5161156451038a290341c240c1c0001d400781424a08048420b100307000103a0403410910785031509041c44e10000e0804d216030b5103c0a521160414681c0403c004189110001c14030420811010b6941d002d980034032a40b000c0c1c08011400108446031a07080c001d204100550300304902d0382c000f9030b00742000c2c407980988108040d1640031051108400d00e0b50100882c00c1c0441c1c030003110584440c2c1c0e = true := by decide +kernel

theorem cover : BRFrame.Cov 104496402 104676258 := by
  have h0 := BRFrame.cov_init 104496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 104496402 ≤ n) (h2 : n < 104676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
