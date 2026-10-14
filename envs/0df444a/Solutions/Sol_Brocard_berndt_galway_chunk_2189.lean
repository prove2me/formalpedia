-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2189
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:56:16.143708+00:00
-- url     : https://prove2.me/submissions/c6b07884-349a-41ae-9684-e5fe7dfa55b1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 393525179 ≤ n < 393705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 393526429 1250 393525179 393525227
    0x9060c09030127060c0c0b0c0307140d05040606080a020607020909010b1f02010506010f0c06050402190803030a050105060703080f060f1e010e01030507020a030e0d0b190b01031b 78
    0xd1480b040b43c1c14491072000d401142440c4410480c0b40d003d203581104003854017804007501502d60501ca040040c0c02d102d00b00c200080482e091902c1008a41c20302c103c42000340365145482c01c040c400038030041343e00b621844d10306000414990008900019115001440517003000080d400f0072500d4140a4080e02c070311366882100b003416840b100080380c009042c10060020f41e00f14910040d09484009192078108100b07404000300c0c190b0850351000c401034014400142565035803022030001c2002c04404d52440310001000a11100004011407080d14403840a200c0c99a8070700a03c0020301501e50300801140107540010250149846607551011004140c0e103580720441001c1a4115010807003464910304581c030301c0d07980d941c04c009041d120607003c3ca000c01c218603040d00700945440c4441d500500700118001c00e2012651041c101c3c041e05034002c46a82d019090011448500c0400307000580d00030740c10031480581341d601920401c900c042042022a400c101c1d40941221108040b1f8900458122002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 393527679 1250 393526429 393526451
    0x30e070506030c25050c04020f03010b07050a0b1602070b0f071e06020409060e06010e0f13110409061509080c0405130b0a0b0111070b07030c0515101502010509060c090301 75
    0x403a030742050844d10320107203640030b0a80c103000d030401210b0b035010b601880c01001011000303480082128110b45200348401d40710040303031034450b0420060350805000416a1024004280c000a01c40c09254100d1b13000c9407085036442d5008a004e004526001038400402d20042000c640d21081c8010b11075212043e83c1d100c0c03401513940400f20b03042078000215581e03076200103200ca02801d070f2009820120909107014a00345040004020416540400713000351909031600c0c034081c1c0f1503003200e0303018101c1c0021141c41c0c684420030040100032600c6621071508151910384445402880c0e42c03001d0782d00380c00140c42c0e82c503181c0342807001600d00504142030800d16903021710f01180e1400302084c0264400000842c0c0e9680b44400180103540d071613108450b40e00080400c01501c00b007201103c5000c0d5142c01c0c005000141402e0150401c00c01801c00c6035411005410000c8070b00790082d03814165041700c510b4030300c2e0424040c0100d0072928110f070150001d62004000c2403090900e41c0203003040000003400132038118116 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 393528929 1250 393527679 393527707
    0x90c12030801060f0305090a03180308070f02040b151e070803070e0909010e1f06080303010b0d050f061c0212010e07050a08010b06030106211a01030507030e070506030c 74
    0x12841640080e4000005202042e03000c00610000c104518051003542482c0300782e15210900200c0040038440076103402c480500812140000444e08001c100342c4800450422041404000b03004034816490081880740302d180082500c0415048050302030300b05203410038414415407403699001034103070061110030b00080c1002c2c000d521900780c0b5515981100c02030000c3c0103801d640038004a85a9040c148170b030104190018000d540b10003240d4500e43d8542c208043c9800800f0307540c115190a000000010903517004c00801400c4000c840c0c1010403640d40d0340d10031780a0000c4142c402c0d640c8102c20380054041c101810030a801c490707000070018040629004402d5084030004240a00a6003051200b08401d03d01160100b00801032000280401d059100005409100500410040c0b10003100d1500c002c10311502480c280d1014000300f0030205090791943e80d0b40644050440c0e000030308040001e50b4140c840d00030400c400d00c0300d07002049102e0a00d0304000480d00014440100d0010a0103c0c0c1c03050882c1d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 393530179 1250 393528929 393528959
    0xb09120304050313271109030a0302070e06010e06030f0a0b0a060315050d03090e042d20030c01050a0e030a0807020307090c050306040f022a0106050406080a06090c 72
    0x10a100840d61040b200e841c1021003801c0c0d611050004103405200c00c00603010f0418200e02544617540000c0c3c580c104000c0e44c0d007501440185d55010311845a15004040c3c00280e0141500caa800291242c0e41c3c0e45030044409200c08099190895800d0000c80d4102c084090302940100a104c4017003070109110020440b1600d0942c00080001d84071711340f10702c40d0181200b056000e007205891241c1404000d4801034180c803810712481400d840d440e000a000d021003051803907419150395400c2c00d0080300b20328040c00d1100703c09a0945051024801d6039000e101080c0704058000e0020f00a0700c1c910710300c038005455507009026110203001204807540d005980500c4204c2d02284100711300703500c80965005040c60207480d5040959854039080e58048806d030801c003500d51000b01150f000c141d1001a5130b80c900640076000714000e0000316a0180c0d51000d0f01041d1005440900400800809035901c0c00c00054940d04d2165099a0b0400c1c1d2a01e030204419400c0590000d01940032003070015942c402288458074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 393531429 1250 393530179 393530183
    0xf06090f05010b150313020d0804030b0a060501090501021605130e0703080a0e0a0305060c130e0a0522081c0b03061602010c0906020616090b0a09050a0f0308070b09120304 75
    0x5582e0909600c1031509005044e00803003810142030079840e20000140d0b10300b465600107032150403507800f17240800c00c1c180211805907901c0310a8003024141a00b040003c1d0000d03009840c04141340d010085403e506c00a40c1510300442c0c05002c0000510700400d00c45940c2c0f4030346440706044c0d05d410f58200038420401c0010300640c818210b45075591070141c001040310030a0301401c0d12400070140100301103600007a405400c40d040c403856581ea01508119210f0401c40c0f940034040d041055030030061109520780c4414403c401084d1001208540200d1500c01d01d13221a00003424590f0920120070705031000c0c0501c200408d0f1500c8009007151400d00000e103000022036007034079032601c440c1030403056aa0a00131010b01780c8840c1448882c69042150103503c07590b0042c506442c0b59902550113132014880c00308040102101144a50794102000005200c0000707030090901820305101c00203280107101c1010340450f030700010308034104501a07031018003007203000d044d41c500303481b812100d0704007440c606008500940c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 393532679 1250 393531429 393531431
    0x4020915070b0c031306020901021005010314062802070c1205100b0d030801030305030601031b20070f0312030e060c04030b1b09010509010207030b0f09070f0308070f06090f0501 78
    0x4000d42c585000d05020040036031005000501c02d00409249400c0700031911030388040056103845040004030719054480301c1030304c059420980000284410a102481e01c5e020060a403029540d610f050b02e0541c4c3c8581e64503e240030604d12840080c4180c6a01a0584c54821081010a50781d0b0b03031001c41080440e40020f8031541c010b11085072038184a441442c88680c0150380e11504c00703159480c00b03040c0b160b05203c00350901c0800000590a0703842a88907810144201190003441131140750000c14040440c6a4541e036100d818441030a10700740041c0700741c1280c0b050f891149105043d03075100540e00d00c121910005041c0c490181c0c0a00404c10321009100f0890202040e031241c0c0b96040040880b10060907d10100e00646504074802c02c500e0101c40415500382000d40d6120283c00040b481c000c03440e4030240940f4445070611207040070740040140144184412100216100d2006803098a083e03c0300805105007040050000740c1d108158814080c0950f90000e51100c442e02c94045881801030708550503 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 393533929 1250 393532679 393532687
    0x51b0d0206070b1603090210030f022a01150509160c0b0708070f0e090106050c0f060c09012a1b0e04051531080705100606021513060b04020915 63
    0x51104113000703a000d00650314003030059281d250041360204449100280030035807100344c0184c442c83c071a01100c01d821444001c00300640074ac0d001c031003400b44a02003400c1c415400c000c00125102c001d902c0c418251075000345403903280e0712001841c50950344000795a0040c0040364a0070750104209001107813050501e600c88240501e4407080041c0346d11801440c040034000d09610713034442c907100c8007441d9040d55030600744182e40d146c01030b254078502100c001040c9031911a03401049040c0140c2d03000313030015030001e07200c0b040e544904691761803070140845884001301252817801c90101d0700502410304215240c028104109484001c10402c1410456003658a540040c0007510741c2d8044029141d1311181c08900c2d0030a41d0143d805028002c4901120107041c1140b0040347c40500000508942c1002da01104407020455000403007030103000b0510456015001e0541112040301181d04054462412860a9a4407280c182e8851000340120812184c00aa00740704c24540368541440100c081199804010b8503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 393535179 1250 393533929 393533941
    0xd08030a06150825120e0a17030c071205070c060206090d09081905010e1501030b1518370b1912080706020412060c020a051b0d0206070b 60
    0x860b602a140b00040103800d0003000b1403410080040300d280c224402c280c8100e44088803040703e5a100d080b1100f0101450104a1100c1c0302d00003c500d0a1540306148840c0b0301000a131111800340411519900106410030803040012080d40803020807220608296051001caa1100441c04015411010243e40084240550440c0070041c0149000c0c240c544000f4250419280075210100c050350048800016440c1208212084d000300c0c84051255084400b001c05030081f07010668020700c0180c035580c90140115600c0c603640000003d44c507030060109540000311400400301c04034010044042e180720131806007602c08062016000301d00c40361504a68025160901e901120403809540d441800e500303e0079507644caa255044407c27211140510032140005050a808500c54460003d240314400107002c642a047c00c034030300c0e5241d40160030821032464600000c0e81e44101c0f07044041c06c950f00207801c0c44081d6902503c86040b084c0007500c42215406594040303034031034010340811130310340d0708070020020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 393536429 1250 393535179 393535199
    0xb120106140f04030609200a18020f12040309060201050c070201051602030703080c010e0105090a02010c05150c12010801020a080f070504030f050c12060408030403082509032a050904020d08030a06 86
    0x107e00d80d526170054004001110000d40d15821074810a20308001150310480b050b44079505850505800b000700903520014105440c00c0c030001268100c0104c4c004000200e201407052007403901c2041079a0f030147c0307412841e40055030b9030b0704119a0b100c402c100350655000103880601c03112000b1071058400c0c54640c0c40d104070040c292540d4480c002420780c9840c0c10420750700000100403401070303028201248802d1103420854213180c0303d90003da00c003c804400b8880d0440a040c01488140039042442030b090b40c0303c02009003070b40728151022000800d201d01040d40711071501ca81a42042c4c203418403d02d81a680c0d501e03408028580344054071203803c0341b00c4000701030030032118039210615054080c06903440c1580d01c150590002900107020045054001080a403584001c18040c14050004041d01d24100d40004e00c00c03d2140001c9424000071002412018440071601c010f8681003034100c0c03011410001840007054000303005036480748220407000040f4070380c03d000314064040203001003142410300340882 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 393537679 1250 393536429 393536453
    0x21091f030e0c0105070b06210a1b0803030a0e0106090c05070209010f060c06051e13150b030a08090d1a180309010f0c02030c04050c0a03060b120106140f04030609 71
    0x305103a0840b8080d0300083c0c0c0e1040484800c103070f1000c1e501071182c89520104140c0071011441d02d585440c1109401c031080c0c000a8908030b0b241c03007050585810030a042c15103001d401e80d072103070804a51081c404107503062026000b901c10084820f0000581a45d00c1d48603105a581825244000c10400030782c840640c00e000c14020302400c1110a401601c5242400091100d805d4010240001f40d8070b0010408407083d00100cad41840300c5813503a500c5182029129000c40081c805011140070402c85c14418a0541c64007403004031520007800781c001120607403107081d03a0b640110640c9510041d80d8249000040c4034400f10451415918655845440d102c10080711000e00c0080440c92a4801d001e003924aa074000d0403056000c0343e078605884072075034610120b8a440240028a80d0003030600b0100014210014064403100e80c20b6541440400e40c1c07251400010b00c074541c0941a0000201d005114030f500030550075000c02c82a41002c3d141a12100203040c03141c00c00d0b00216071054a81800d201403014901c40c01d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 393538929 1250 393537679 393537701
    0x30e01031b090317030c03010b03100806041104050a050f0105061c0c03090507080a0b0c0a05160303051506030f0f100f0608010302210a030e06090901030609120c0521091f03 76
    0x8515600301806c1c0c01c04203010503c1002c8e800180000029001181d02c084200240b0b900d0040320860b09291038115440c1007504d62803402549400000303403501c00580140d078080d00c0e01101080c89070b400c100911215900c103494400c80e0071002010204074001c684940b2040e902507550005280099240090500140c2d5200301ea0343da0180d0940030110b6002000c60750441444013034070303584a50726281555540690b00c1e0240055010282003402d25406030480c1d031107019083c4040d102048410100700c180d00040d118107011640d8480014586800941c0240d000200c20070b00c0c803140c41c0d45880d800100c800e1074000301c0008800c480104114108405250886200d0011a0640120084549079104840b80000d030030084400029500c60300d0f09001c5542ca413901038032241c0310390b03120b06015020340b82040301110f0451034052401c00051203000740f0300c2c9555128001c1e200030440307241064004200601424840d84040080381c0542d42c0c1d094912410081001402d02d007440403c402030100e4407090a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 393540179 1250 393538929 393538973
    0xf030405031c082a0307030e0f010903120b01030e07180b0a0602150c04090e2112011e051008070e0a080a08031008241012030e01031b0903 61
    0x60080c1e0b00c0e00a220107a00c081e408103658a00b8090600c01114201c02c40380042c071801c000801d1124040e8190000d601440d040d104568a440c2c1021199003203a00c84100900080c59695060f80e9a44c0c10741c005d840302070360504d008114202034030031032404c05040c5d40c441c01085261098841001d0001c1c025011011003c480e184081840d08001a455032510003801c0c14003080c510024000d074800e542904c0c00391100c42000c200300400d406605a961491041074a6580c4600200514031f500c0c0c5411580c09050b000c0032946280d19001c60300c440810350382c4601503194107240001c01c580d01c1748050006a15039980d612415401c00750b00150400380100d4040d4025000d070780c818008503c00064408500354420340c40d542d6aa00c11103100c0600e4483e810003070a0b400350424a2040380700200001c80712503441e43d15240113803a1300215002400580c801c01843c00882c01000c000709003d180d03284a0081306060115030304100700d01e080d11001001d0850004502850801e000340210003e54040c0a4000700e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 393541429 1250 393540179 393540223
    0x3060c0a09050919200a03090308010e010b07020d3e09091c09080307140d03060510030b06070c030c29030109090f0b010f0608090604170d0e0f03040503 67
    0x2050380410035281031294a80e0b502c0f4400800500491841d0340c41c5c02114462680c0c07190750007040103010700300102050b0001591640086014150b20079154100e50f0202ca01601d0140250709000208401c60380030b5071054030084076400b0b44018418040d1050801804c0c10102c51024542101c1c4903001008040c0904c03011010844c122000051481c0782d0145007035690114126010200c448612070340000c01180008143c000c2080004a40c59103e02a000251401044080c0c0b0450444841e407103180e504c000005410030340d060081e408443c1205d00a000d83e171a041c0540c81f01c42c641d5032241d00032207001c90901c0007000525066441900c94506001c030115200164415078866400180102c2800e2079030ba81c0010100304c0001d80c40c0e0030381a807041030034009683d40c4207000120311041c45494086545140001c0d9800705c0800e4603445207070f008000b441841023310350701540d42c001d02ca4440281c2d0383d1307040300304030040108103600ca840b4100c4025a41e450800742410304000c010700c03100380c607520418 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 393542679 1250 393541429 393541441
    0x3021203072018241203130906050913030c0606090213050a09020c2805060405010f0c05090303070605060f031506120d0f0c050709020c0f150c0901030506030c03060c0a090509 77
    0x25411508154030134403500807102003000070014000e04408450a10000030301460440801e0102c0040340e00c140420400b41d981c134010b2002c120801c42d08400300c640e00402e07410000c1d000c1e0001001c03081c0107160000b038a0381c49003070340412688041c2d00300700464404c203410082c5142c04607002029000c40f08081d41000340d50407082d071307680e41d00780e110040d00002200d0116416001380b00750843d264014003154014102401c000b8000e001150780c081c071090519034282c10040c0100201e54802101500440c90707c06030f51100c10007040040d08103131307000601500d40040c9507801c10a0104010468103a080036042c01c00c104005800c0000d903501c0103130480c010344056a6000780d100f2009400c05c0c244464a905c007807078058240841c903000365103440d1020862002d01500007800d0b41d8407500702800ca905c4c1c40b40204290a540500700c41510700b000b07040118818652094200d15040000981100c3c82806204002400d01c2401c9800101035000452081e107819880031052004010503500c180b6581062 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 393543929 1250 393542679 393542701
    0xc0906060504090e010b0622050307030c15021c020c03070515090d051c030903020d021606030207080c0109082802030a0305040f06060806100b0903060103021203072018 74
    0xb071060351035495a13070080c1d5141103429000360000c4240180081d0f41c4001455800601c034159580c01c218090041d14041114100001d81c801500e42000350340c81076910b0015500f09a464626101d0114012480c0913440038405001a401c9801d035034020f08800b2080d0800e151401c040c682c040d030b00c0348090071041c1c0b044c09292002c032441c0a01c08d0382d000300f0385101c1d420042d14081c4155948140701940e00c00c0e59901581c07507481440c43c10b100303070f09543c00c203803410360120b03520a144828410084003035801004070a0182d401094418815050113003400104500d2508585100340d043c0c500581c0015484030300c40c90001ca4107500707910350103003d041c1602404000d5036030040a00307a205141d2707120b000c2004d0100c03900749400300b5503002009004007601c402c1c2840c1c030b40b01c1c1690304950f041e500c0003000c40c10201d0101587c0d40c41001400816440c0c0c65034080000d8040207081d001c00602082102c40003080742c404400c03405614688941940c0107c1000748048a282c01d5844d5440c61a00703000e2180f86884 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 393545179 1250 393543929 393543937
    0x120e0406140909030f0c0a110102010504020a090b0a080304081005070903030f0f090e0a0b0102010f20030601140a0504030317060d2a08100e0c0603011505120a090c09060605 76
    0xc1922071562907903c141840e85103200d0076210508007000440d1004114400180135000c03984900c078968103400c109170043e82a1142030703c00940c0f000261009110048142d031144120410003080348006da50303a0703107119065501c41e8002542c20b8112590340c05195125029194010510749001d42c4194515207009003160000c141c4a010003400c20302d81c0d1350f40c0c0e200302210400380c20021406070442c1030500070500200b42c007011490165081001075124012184152045000d01076450001c3d01d031013604803001a4402001c65050240441d00302d41c0008100018042041c41074860b650740741e042d82409450070b42180012590301c102e0204204468441000103110740da403004980c0d040c0568407a5a820740700340300301c0004070610b50f2003001034a00f0002850902c0c03d20780d94800c0143c0a40041401c5c0c5030520444039541054007080100000050310320fa0000c140d03460314105090032400407042030381103010385508a0168880b07548105118045010400a00051000b0006203203000c0e40a851401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 393546429 1250 393545179 393545219
    0x61202090c030907031e0b07031506051e0301030506010f0506070c0e09010609050907061205040803010506031504110d0c090608060f040e0a030503010312051c05041a04120e0406 78
    0x1070040301149121a0030880840510740c8103105148002c40161005600140c0000a071030003200c0c000400c08480c02403080c6044902000040300d01d0504003081924103034031025051355031064441d00c0780d02d41c400b0a00954060f620800141100394508a00340c109040c89412041c8554400c018440000d14081b82d00c2c1d08460141040204030b50310340b00c2060041034030740d20144229091404000e101c110110b1840c00307551301c0d6164480300e85501d21800c806c441e02120010211042000180005c0c6010000307164050b00011610740710320b0440340401c3c2950012140001e8202c8003245620000c1100c0c05180c00400440c50001272080c9020f10042003004007070031190240300100c000160303686070780d00f01c1c02005071300d00c1c00c6441e5003813545001052540244400e840b94100d04201e000180e00c5001107410500c4103011030604010080b881000038400900121124281c802d400c0c0030301651140c2e481c0c86203000c0c18101c06804403c0034080e0104410ba88a14441d41c0b4100061010b40100b0b5030b0030240c44 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 393547679 1250 393546429 393546451
    0x209030312070e0307030602090a08010204050a0e062701030201080c03100605030c0d0e1b0607080a1d03010905060f090a05060a020f04050d060902011205040b04061a13090606120209 80
    0x62520401030303e6031000711004a4060080207004018004160024942c0c0c02050b0391709005990f603107030400e00b00c1c0500e0180a42c4694254030805c4440b018420194002c0c400416150703450f030211004801e181043c12001c0ba07400340c030200404c117568220022a510083c200b084516501d4030600080c0c1e0030716103014074810710074080003241c0403090203020f9400b80408000104607130401c4489860340c4800c031a21141200c90b42620300f5409041a0094943c800e51104006040c5680503105607051f61a4040940030201e01080c040041d0303409000310115240180c0107044241098688441940c5000708016480e1f8800e50446002070300c0000d202e580241c4940d00103071540c2004002e000207106075803017644e20a8aa095100074011613134818180140300342c80c1c90311091109440308050303a02c00c40c0c014001450030341c005408110990000c0c04010b208408481203076000c403001500e1b03000c8151a0300e000316643e13640281040194850300010b010f603400b07040b01046a82c1c2c0010b42100c40104616482 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 393548929 1250 393547679 393547681
    0xc0c030d210c0201111210060906020d0305040312050a050615040b2506060807090e06010f090c1202030c040306060b071e0f0c1205011b0f260412080a0209030312 71
    0x240c03017988005d446540403a013056540d00e051070600020603084c2d915400c00c000300d50340003490038098031400007103d0140e00a811080011802a0002d01c0001c02c207805018480400e44080a058819a48902003d0400040d18109501032100b01c413613032405000c0c1c041040005000c140046400c2c0c54030064091039003400791410a49005018003003400c02042c01341042c00109082d50082004801d48131980e00800068040031082540c685003031240c0050b0090110703051040e010380f03400240b04001e044c10940e0240410303011040480c0c1c02116486a0480041002d20070032605001d40c600400c1e48400035400c02e100c680302c001202c42808069110031910041c02001c0101c0001002c40071900002c902c880700b0340c0e900780b950740d001c42036004883c15482c01c120350500700200c20801150021550320403140304c4003480c064440d40806040d045105001c400188030060945055501c16841250104e08211a0300c0c4082c0c00c9990181980e1003232030050000344020789000054039035000044040d0302407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 393550179 1250 393548929 393548951
    0x60e0d060902040e010b2d10020a050f010c11010605092e0b0d230126073b041506080114090c0a030c03060c140c0c030d21 54
    0x2400d12101c020b41050400c00e251044090650280303c50b00401d4900759800da02800001c07401c030443c090054006d8403503410040355800e103c42e5650342e8494600448840208070788a003490f01e010508111321a070b440e07c0201710a40e500619200c403200403174000707001d946e0802000840005000304101c40340892005840c2c40f00b5621440c0340c1184d103070500c0c400883e98032456203a4040d40995011181142411a0020f900c0080340d0b0510280944801d941c0d5243d081ca0341d50300807083e8660070060480e1036502001080c80c014020b610082450610f030794050307203204440c90080c1300003000703196070b0501904070f01c108595102d101c03550159018a60042c0c0450752441a8018013098020b403400b50300e480310203008035249210f140c1c0030b070b421070084540d5a01c02e04100503504506002c000c00070109600d0400c0011a26000040c00ca40c0c1030034802c4601280292003031454100c09109906548124044406400c0500032034120317108034a803100700010318031110070714020323001e08000601d07a681c40900d038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 393551429 1250 393550179 393550181
    0x1020406170406140103050604030e0904030507111306060903050609012706020f0d05100f05030a020d17030403081b041d090c060d0f0f0507410c16060e0d06 69
    0x103044c1100b09040132035616401d00d541d80300b108441c102d020aa010003270a078146403540085110310382c980c2e0380b140fa140303442c2d51342000003100366505c0d83c0010640c444032500c501207014030406000640d440c15020351039804c0031031030604080c120750041e9242c40302040700042c82d680305001c106000c1c03450b92425180352400c00700034407a80d0040504800e0215010038000200d80150303000300755a80d2865126501c9100c8010420382e42e10403907034075520890509005007481e80440300800c0c0261015406880e12990000e0940c2c000c03903046001031108802c07c404401d191450001e85a00080114201400c01c4001c072110250850300c6034000c9106000284000d00401007260800030140100341c84400012102010b040f000d18002061790500030b800c001280c2c2c2d4421039200c4c0b12599038048030044c004410001401c00c2c00150208410300c1c003421480509640703440b4280002616030399640703080070300ca600e003410780c000401621440400f0b030401007658001c1004130000c0c2e007294980c4081c081458020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 393552679 1250 393551429 393551441
    0x806090c1e040312090b0d11120132030604021e041a0a08340e1e0f060a0e0c090d0f03090b040305120a0e03010f0e0f01020406170406 59
    0x2044080d400007000c00041220400b400440e1311507039603840c900c004110140d8070b4543c14096841b5202c0240401c54410440d80c200d8040e415210780d0040c9003406802c0920103540090308142d080800c2041d1981c0c0580c40c1d500c00820b880641e501c1c2c03440d18800754000070380310036006d00040d1140c10414001c9100280c45540410a071200500c2000544402015880d02030101f40000d44074080c1e240700010610000b2a44940000350780404a0035a00a01100c1480b5003c19580400321b01502c1e0011a5113052800c0c0c80d8001e10780f8020000c0d0304012000301c60400d6200500f0007040c50741d80020f00900da21034101810175103000c001803c2203a0f0300c81d20b0b8401540514044a0780c030400007100e11003444502d5a01d004202d0181d030703562034000d880d032070109072511803440020280e40c00715840329401410740001d440740304e035149407e80d088005440000e003560a40700308482c601e5035400100c8060603003001540d03120f4404200035030900c0c1c98048060051444801c03030740c0c080046000000d08009081d4884 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 393553929 1250 393552679 393552697
    0xa0f0b10080609100f02090a05120a02100302030a05071106040b1f030303020315100207090203040302012319180b04021207030308090708072102150414011e0806090c 73
    0x1d8040b07203030a2803a01d0303540f13041c035100591407494407074801a00d400600071640362a0b400740102c0c1c1058a06000d002d5280c681c3d03900c3c4000c0b03000d1072240b40d0050355094008000201141e80c0941c40b0700340180c202084a60142069091142e285450f2070001d401141c0c8603441030304842131a0303199980d0b0368222030f00c000319244908207030b041201c084105078140e4055400340c42c00c0c1b5128842d9840100512000182940c20400980e01c121000c101f402e80d0340e001540d1180c480d10001c0384d55011003101401001c45141d1032003d4a00e004100b145044010181d0b61503420b5000050000d1404020640070b0700044080181c0056441d500040135900c40360300008900c01307442c045030b401035502d003002041403206590f1555035010b2940000b401a10020f0580140c0b200001d06860f40d5031105840413851442d050103e8000040070541e2014000b400003a00050001081100919148100040135040f0344425909000080d01c2e80700d107008d034440b840c954001d01c1038500d120b580d01d440300c0c50081e43c041c1e0004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 393555179 1250 393553929 393553933
    0xc13030b0702010f0f05010501051215030615120a02010519050405090a150f0305030f0a02250501022404060203090a0803010305010b0a1220120f06040b090a0f0b1008 73
    0x5101d182a8150f006500b481e03044241000140404101707981920802c0c40f40314001041844001c4d00810101d101540001d214020248101544004641000411590442042440070304c0030500c0c1040c2c00402c900c201c600780505240d07034113580040d01501880c3c40d10720a01040e800401c0c103071070164040310060003008280b0800b1345483e04c80352010740b880e45414a0300c2c0700a4000010702c0640810740740250703944030010707509103141c40414122603000403c040d4114800c83c01a040c03502900311454040350704400a06107070f00c0c1001b0002e454100300030f10f6061113051205120360b980e50300780803140d00a82e00100160340c980300c442500d490107440403409492800c1c004000810050150720001d00d2820540b1f100781ca541d550304444406c104802005014100e0206000c050b81d00480c0001402c848020107488880c0c03441d106003440c00c041c0c042c149442d60301120910060009144403a07500014600082944841640c0c401506082030503000b407840c90801e001c11901e10364030800030003800b50300017 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 393556429 1250 393555179 393555181
    0x90608070225030b0f0901180f060b0103060509040c030c0b0a0210150302060c060103060c03290102031e0414040b03030f0d0b040e0a060c0509010c030c08070503030c071e02090c13030b 81
    0x14844803030b030301614403038100d601e84600ea0ba0201108c1241c00d000c40d800c450b2050362111a0b8513040041c0c01010740040c10076540f0507000c2038a54824030713418042e5009061000c4e43c4d504500e0100380403040d607080001201c0c02405101304640c5d000030002c0440c01c00032004640301294a4001c0d81c0a80b00741c0009500000116642d4900c8100066990482e07000e80e000f441144402e02055045414000802c0c601c040501c04aa8131088152220341d0b200340c0600c112803510444030300300c034080c1c488071007a05181900001c3c10402541c0e1400710400d2001c1c1190100422040c01c00060368911941d01d0411081602182000a03940140d02c11101c880c40580b0a1066146604500307444d8941040201d41092401d03c00010451040b0261f460f01501038481490b2402c1325141580c45000048046075a0b000030003126000550134005140240150100e144c1c94203400d20b05001c0c400382030355843c0c42160312800d079080565034600c05143c01240121070540c0d5031058071120501144103400140004000c94 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 393557679 1250 393556429 393556441
    0x30506091b2a0d03060614030402040c0908120c0f031911010603060c050306240406030209060708040816080d080f15100810050913020f01121b090608070225030b 71
    0x100e00740880a8041c4d404020454540a081e03801080e222072150307501c41d00340006401401d1607030042100482c542018101140d40f050340510340543c401402c500c0f8817010840c110000c1c020080240740c450800003441c1018111210110350340c44044102c002c001c00c17110101e1400c5000c0d03209502440e00810280480b18613948060010360040e20340307a000304400c9900340f21080001c100110041d58070702c00c40f458a0f00c2c1c2081280a5044104607039032112042110320000340444000f440140404405000312000300000007050302e40c82d074080811500950500e0440581c000c01c030075401000d03910300010f0758070380c1e400080c656040c001030541c00040d4115500300742d5402104084c0b00d050248001082c0b0340d103038024044140803d1320302e4031800c400700b9032503c010318100c20024104a4189082044e42e08181b0a000540d4560481d80f8015440b0801c04011946e04c4170f8408080e100505140c0700d14204007100942c0d03060080901205e004090b07440465a11840841100554210031460b40900304a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 393558929 1250 393557679 393557683
    0x120b06010804291503010e07050402030901020f190e03161e05090a0b031c02061308120f04020102060a05070e0d0201050415020c0f100f030506061c0507030506091b2a 73
    0x1351021002c41d040a04035561601d4140180f000e02d04011001e03260a501c5d09084c803020b500060044642c95400703000b5100300d2030040000d4044803061000710034001a40304400342800666141e09030294002d091015220b88903808030708100c410f02ca0105c41c080740406a0158034800345d0300803503070218828060041130f28168101c8c5c000018101c0c02d44040410300b04448040e50128209400540c0200c00000c01e070181284403401402c0c05103601e107192000380c150342e410003141200c40300c00200106041c0015075a0402019912000c020810491810500e1014003401c41480480e8850003006826a003164030540544000300b140000048080b09100d501a4484003080c0c4828051a14125444000d290451000c0031b8240252951103048241030801c4001c1e110007042607130041d408020320012103913842c80c19407002c1e29001e0006901c0c00d01140040540320f018000905c0b612410081c0030550038481c1c043c912140e403601100f43d655400c0390a820003607980382d05000b0f08590b00f0007280400307800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 393560179 1250 393558929 393558931
    0x20406050d080306100e01170a0615050307170c0306100e1306140a0e0105060c01060e0c0703081006080c090a03020406080c01080a060b0d0902040905010f0213120b0601080429 77
    0x8101c2c0c1280117040e100104881c00d090b07000603d800540e500310407006032500382210a1b0840c2e070703050020408035200c03920500d42c55082040080000c10000407c41d0865012182c1d070354000c4680601c99550400d584075111600002e41040d06c10791040d184607240601a80c1d080300302e08009005108032013001c0300c002c0b000780b00d6486500d61181d4480d00038032051030601c9000d000e86074940101507035a400e20050000c10340203422a02c9a66694101c0855400b90b80001d0034400c0740700000041e52003203503182c028a641d90141160351418a01c84080c0308060304410119400640c070381000d5200c14048000814080c01d81d4406074202d80740020219503042c002c40c161503184401e0301d61306400d0f00c0301c80e42682100c06c2840f50000c0c08070280503410301c00d4244c0e0032201040e03000410200761a1300d1074072114219000314499030341d61035002400a03020f0040c18070903001010f00d0401c4045102558036107840b01038008080d281002003001c00101005400446480842814102c4010760364080d258103028281c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 393561429 1250 393560179 393560191
    0xf0e011209050606010210020310171906020405011e0f030b06070611040504180f02060306210c100203071703090a1a10090504150e0c030102070303060f050a051c020406050d0803 78
    0x541e40401201c0d1f8654001c0300e000e4541484100012440c0c111140000301840c15405e0b2180142c6c10b0720903410b03a0034400c014080d030040000580d540c0c5040009400da04020840c241002030503102c0c21489900828020112159810301107101d000c0c92000400c14403413010000c01603403a08020300c40d00c48102c409442658001e0b44c5c10020740717510380351800245000c080010804c484050842005080c020082d5400010140c46010b0382d82640c1001c404010020f0401041e0f0761204c011b50506103000d01d6101d8003402c80780040c511704103054039841707100c038189170825039408000008165078410400002140c07541110f140030700c02c1548003181b409136070181d40c0841d855402a0000c140d124251140500850340b008000501c860060303244000303004047e1400c0c0e000d0040032030001d6552130a000600000d0f02c01ea0300004d805040043e5403200420f250881401880d840c2c07000c1c01913450749425040c001321888001d029615441c80064094000e43d0409a0081003d80304070080125100146002d01307 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 393562679 1250 393561429 393561433
    0x150e01080709021201060c060b040c020a0c06091d190c05040e0a142d070207090f0b030706052809080f0d0f0e011e0203040f06080105010f0e0112090506060102 70
    0x82d519480381003680250748a002c1d8900e440401042428000c1740340d00f0f001c520802d0045420704c2424006003c450744040c000d009a08035803611030401074182c100101404650074552480350078000e1110a80c0d070001481100f64082c00c001c03c00d0401003800d500e49108504600f480080070a4000610310b80040c4165901510190082040b4001754022100d04401400030003c1c19980d88042c0b6854100d070549844000001c8240c0311308406081326113521415047d001081014035003980c007000c6a40c4201503400c3c05280840d02e50041c2c0e8041076141c105e450602e400e40e1640d1f01c1042c10320340070b240b60190080809681c006481c10342d81059101c1c00305c619410585401ca0b01500e8402e0f1100c070b601510400091503d00040078040c01740b800b40070508818980358444690360000c0901001e9580340ea600946c1c00854200141d14064600002401140c03071310402035450440064282c880114004003402265025142a030744201030001903076080c2a410311000711142481da44a541c29540e9034014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 393563929 1250 393562679 393562693
    0x503040b220303080a18061406100302040e071107080d200102092b0c12110a06050406121415151c09170705250b030415150e0108 57
    0x40810010401142d4041c1c0313403401e15685503983c101c018420540300b5a030f00340d925031420303000c47c0842c864031494040309444e04045080010800c850301d28140c4003042014010031040c41000002c10302180c00c281e503418007032072842c940341040e07050591a07004240e051080d01c4910010f141d014212049a116189010b681034841c40801d070300341d04c41c0c807151a030081d441c0c11388800c102d101280b120400341d40400e40d02101c540e560703450400da980250704c00440d6903c009164818000c0c400c991f0401c0300f000315242c405a0380350840182c82400360388500400d21010200d015890f03012038210381c01600309038035010113034a00700311482a00b002c11b54295020f62180991404407011110448400d000501150b803414003110501c0750240801810896200b802c52030300000f462011005051aa44100c001d40b6107007640b155017103102c03840406001c60003400420300300414501d86046a4000d5008440c510102c260448a4000317031203031807480103540c1c9030f0110000c3c6a00380502d5080c1030303854500c00d036440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 393565179 1250 393563929 393563977
    0xf01260601090e150f1207060e0a050a03170904020d09050d0306080313090b030a05120304050f01020901051602031609090c05040c301112060d15090804030503040b 72
    0x741680849010a09030b01c03507040075440e46010004520400001000349256100c00c086d01404d214040e40404003140c01d010401d040d500d80048040d02405007075035107983c064a181c564815880f18203031100019440081d904c0386a4039250102d450560040300140b28040c40c9181c110303502c07c151402040000e18028002c03417940d40200c1141d2400384012285a405800d0820303400c0100002040e0751344c54801e103602040014000e220300e0031030030080ca074520b4403440c05062003814081500a4940141d1041100c3d10300b0380c1e041000d403000152000c201e002d41307030042d1000ca85070100c41815140d513070b0303841c600c005042c40f015040303021402e11603604800059a26030900080c0c424140000c004a501ea110101d90030441828111a42841c80840c8180c01c5002c407a410448000c5c0c0c03a02501c4500c00034072318210b024070444c141c1c3c101d03405980c01c00588169485040c540000c1d150181500c130344071030958091007054400d5030082e540010990b83d890b41da86000c2a41035000780821182d42200c40c084001c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 393566429 1250 393565179 393565199
    0x39031e010303020c120a0b0a0c021908040e0c07052b0216061116030303060311061c0e12030901060306050924130503070f050115140f0126060109 64
    0xc1280d5242d002070404a80c03141c100302c050004401e1840c62845401c0300305002c01c0f200c030040c2d401044014800074044051038002420410140002c2226024100d08040040d05480846084034a505196405600c0f8020a20b019100d034140181c810721500c40e20364039542c4081000c44611700c12a048014078154243d0603a250855a90185884462000c04101e843d0042c80900704500c5108140c4600610389911404e01807050740040c0d0002c2e6460742c0501c104174104171010b42502c000caa80c40d0401c00a0090040381b10b03030809074100c12540f244010305a00c0801c00c0310703428512000c142d25482e4075200c1c010b18006e0a40d44070603110350342000080f44840c00c002c2030801031841d1080300c4000c50303020860001c1d91000003802c81011044a944050b01180040c005401810722884d0421000107680c100282516110261002d0310003527040c0412640101080381d4059150a03a0740d6902d040c0c0c0c01d0016038051009003454a050380b0712103480d881c401e01c640c6c10309200e000240c032110030b4151a184524 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 393567679 1250 393566429 393566431
    0x50c0109140a0b0d02160b0618190e0f071d010b0a0c0809030c10020d030e01050c070611160f0c0b071109040f1209060311090939031e 59
    0x150052100b41e414040303e20000c0c0140310303084a80502510344400380d6915141e0071080300040c0d80100f2000280010b41c0340c03480d480c0c81036480700d90f90300e191401c0002102000351400030096520503580d901c03030301e090070080c8001c08012001405442103d9505c1c103510076102001c859149086500c01e0001c180124003000b80c85144000740e070f07950307a40213065441078002e9100c407100e10b5040c80341d01090031007945c800d403206060000c140d0180c44ca924004002034103941c0001d100b82c54a905020811009001c20300945010903080040410701000001e210745951141c41160300d06aa402c00c211700922241e08082200c0d14411901d110103141e81d00d14005290003050740007001c50a5200d440d0407149001d401c0d642d040744c010b2414a40150340f90b559482c85480250081c40480e0100c40e00b08101c54041c851000002801c1c4030440c98a8292000200c0140300109021a1180c0f04511403003001d824520b00c202c0180002c80c12000c00c14000e0245001da0000c40d80d5000030ba000041e41c5100c1d030f01d0070f0041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 393568929 1250 393567679 393567719
    0x60f06020c240304050c03010207060e060610080c0d11030a020c0f0312042003010c120e0a0c170f010606030501031e02030c1e1c030f090602070510031404050c0109 72
    0x10342c080704201d074070a50181c0c0003400c140d5044c8100c1d07000032a599402e10050001d24030505000800c2060301d00f205040c64001841148101b1034241c0c07180585400c00c1040d40c1c05000d940c04a03540c1d050b2916480010161141a456072240c04410426202480d43c000d003111451130084858038001c40052503a07a10822a40c1100381140d000450b000407110500310310319681d1000060f20100d1a0350103e82102e00d01042800011554441b141d8422064400c1008614120f800f801105220f51500034441c6a58855a0229030300c64100c00c840341d40a211415203080390740c1c001d00c00c2c9070b52041c00a014101c01c2c0019102c0340714280001326203103040b406c214425640034000c1c00050312007100b0030210045200080a0030b80c1d0042c074029860741c3e011282c410880740080c001d10341883c0c60030003d11020200560409002900d003060080940000d400707012928120340e0440742d10130400049001e40750700484c91b610091a00b05000803c0720206c0c0d50900140d0030b903648078180d9500e14036040c0d01e0180d4001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 393570179 1250 393568929 393568969
    0x3080f070e01050a03060b03190b06091e0f06130e0c04080c04050702012c06010608060303031522021c1104091508060906090624060304020310060f06020c 68
    0x44118075500450191500700300509001410b1541d0380e41600103544210350f110600f4803880e011b04403a5056210b0301131005015078445043c4150325001c9001d038144209444030a03c0044030078852a51142c104001000d0042c18040c4c03034210b0805081100701c00760040124207080b03900080e050201080030f50b07003102c9a200c010302590001200344001041e0141c07501c0c0071952030740405118805980c5040200303c00c401c0340841003d007051400c900300070301a0000400c0042920501002c0c0e80d0000549401021514100c005140f0b20400078030019021603003060180c40000a5100001040c2e01600401c49100032404100c500c801507042120302010346400140020b00090150958a03484003000d1300c800c9040d41e0105417200701b40c1c0d15182044480300c01a9000404100c07d000061002c00c0d04203441010802052410080d0712003000c4100c0c0302c0134050040800080d0943d901006600807903a0030300401c11207070b03440358841e0340c00080fa80200409445004050100c0b8281021142d403805c00c0811 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 393571429 1250 393570179 393570197
    0x2060d0612060506030a150e010e122718101802190e100e060c03070602040f0906260a0b0412090519140604180506130b010f050a03090605040f03080f07 67
    0x2103254024240500440c00540d40d540820108800c1008410036071000e2f186026207940804458010322103c0d0b01c481e840307034a030f080c0254146803244468001301090b0402250f040f03545050102044031450f900000c02e40f032540c0540c26125880740d008003000001402a030355051107030601034030050a0000902e4115581040c107000541c441d42c8550b1a0f1500282a2440d211707a004019103180c011100a076a1382e070b4005420850001d41d002008010010394405000240c900003400384111101400a0196401446000c51050041c0003c1c0d40d42c551014540045003880d0034242c102000380722800340860008140400d03140b4110344040124400f5001102005041410407018404c10148054020700c0520020809200340a05880942422240010f440c98044c0130010038140315000c6602561a1400d107078156640b0812075804e400c40e82c200940d4450307040100310001e1100f1307030014080c2d5141106110410030000020f0942c43c0c00f9540e4010a80c49076000280a16000e54042c00030031030540c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 393572679 1250 393571429 393571463
    0x180b0d05060a0f14010b030f0709080a24050f0405060903090a090c0509030f1006050f010f0e0a050a0e04050609060f2d010b030916080c01030902060d0612060506030a 73
    0x90000b039100f0403101c4022842c0c0507500c0c405078003030000382c11544181d400402007140803460001d10300d61100a52030100002c074908001140c0366241010090080c0344c00301c200312800c0c2c00c8030f89004907001070303e40700b007246142001d82000200c40c10f40e000c035014040d12010482502001050380d0300d511009100210282c0b074035540000500044206c282840070078041e01009a03011301900e110003035184003510404829000718021986590000e034402d0032581181203441c1d80c041c1e080c5d00c240001d424010401e2100c00002107951800340d100a5000f04101c1c400305107002c9005405020b1481a421078466450b034000c0c003629041d045904c100030038140c2c80010700b682400c00c0740345003115001e121244205481450740d034121000340c001e06e40800e03000051101c084410000c00c044220b010050f46115030901d0206600c607900c0450301c504054403203180400b959101c60490356119540d905c100f183c999500880c0c1c0b02034414a8007560910b15100000d10300b0306020903498800c40d1320075000391809200c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 393573929 1250 393572679 393572681
    0xa061b06140910060503010204050f1c0f0506011d0106050f09040e010f09030905060909070c06020f1201060e031f09020a0513091707020306011203020307050f0f120f07120c0c180b0d05060a 83
    0x1810195078202063340d60b42011402c10301000c0303c00341c05234014150075814422503000800c084010203c1c0742018100403c18a0350003c00d540c40903190003c03071541d0703914890005001d0142404440029440c2101a05041e400c0c0c1d4007034200b0501c2600d8881c0555516005c00050303000740220144c0050801000404841c0310313404d10300708144590401403c0a040b130f081d081242c0c10036807400b2041c010000050102c0b980008841b400a402203000f400b1038100318a10841711060300100039034564403070641104640d104080300000c0e0101030314040b0140c442180ca00c014100629040d030343c0d04581c60034090101c0f1054101e481c0703150090014034042c0d10b05180d501501c1d884480990131800140501c02c001401404108800c044038002807601c4e0300704494590421026421027040d440c400c1220055090210f400d4070001c0e50028204c20300260101e5040c0c88108551100170405011880081000303d0856501c03052085582010000364246d00c083c4030b41c0040800015003203921180015400c3c2c501 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 393575179 1250 393573929 393573949
    0x305010510140d0203040c030c120309030b070219080301060806030a050604020108100e0f04120c0b01032604062f1b03160602030c0c0a061b06140910060503010204050f 74
    0x8540c81079842c0200001c600c201301e80040d14211111016802c1c20414062168070308005007246055090302480b403079402404944843c4001401802502c0c002408140280000060071000d00c1d1621a0545035103001000e540c024001d0401040102c0c0200d421030500090180704103a0120040c42980c5454005407981c0200802029540003801c1e0042280b0500441041c0604041220b00241d03007054039224105044140c0786608102c91100f140780400caaa100050440717400c50703420380000d0707001203c0c01021070760300c0381c1d054441000103070000741658050308a100982d2440e00a03282c10700c02d8140d02001c44240c454180140e4071040e07029a495001c0071012941c107038020115074000c5030514415408409aa10201c00350f000401c05500d01441402440d00d5810211030a4554900b00321000d1b015210743e240c4589103264010300d42c400c000c002d900440c61a41d40600190b0301e07142003950546c2d9180501c0c40d1010b2142403400c001401d0405009440036120014100c0072002c207004180242030f51 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 393576429 1250 393575179 393575207
    0x1606080606040b0c0a020a2907060e01090b040b06100f0f030b090901060609080307050d1101020c07030b060112140712060302040c030504170703050702062a0303160305010510 77
    0x2080000240d109440001000301e42c082c0030242540c2186030041120740900343d406034107240b0850342c59a11b98207000c04420740b074202382d840e007640314801030404800402040600d15607541ca040c1110051000d00c1300540d11580c440c60181040755034010900000400010701080440c1c80300c0c505028846c040d00c02c00e52001480c0c0f4000440078820300c0003442c4803100350389149403a591624140691548600710708c000c0c1032003000441c42e20f1125550a40c0d0f52103980d01080401035840480100c0003400c1d0125541071100c40200ca15043d200c1c02c00e401100381c01c0e54006c0c08201565a42b00f440903060042e1000501a0502501280d03551032003a0303000140582c0207116a682c81c1008001650b0724802c4d144889460b0364009810701d420f151035941c0f10241c450b014444182400000b000950150860b081258103660190311450800c0d10f0610044a00100041d50301132044903003610303440000594480d1290080012010320000410b800300c1d10280601c54004c4000703c0210320140c01004006a180 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 393577679 1250 393576429 393576439
    0x50f030103060507050c010510061b0203030d090c120b150f1e030f0f030405010f11030a0c06020f03070804111512070509060a030c030c1d1e0d03030905070816060806 73
    0x180301c00682421110101c81014407030181e1036051245650100d617207403017040bd410300c080c000360054000941e2800749004500c905908c400c0d0f210100000000807200924440c07100070b590f041d4034a042c450305a821242041800c142001c4810546440c585107004c0b03550141080c50701e00b981581c41c0b00c0c8070301103800c02601880743d413a800302140b00c200001d105004125002d1612103080c41c00052140c0d110030b05400c200320b0003c00c51441602c012084940ea000c05080c0a40c000d403131494200040c0c020301f00c03d0440c4020100030030500c26080306d022446148519800c9041007104001c01840340c4003441c4441d50000e00b809042c0c00c03984400d40d80740d000541030a00905004030f040015059901030404000060740340c509000650f0f4160085d441c8048180c10521124403410440c51540394005140790301c03a80c061016002c401d940c02c44549802c002c0034103442c42eaa00582070140151030310400403640e611840b000000c0318a80800c07113105400c0c42090700303a0407030b180c40030494130440301904880c0c1c49 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 393578929 1250 393577679 393577687
    0x21305040b1b090d061a0312040b0c01090b0703020315041104090b030a06180c090b060702100e0a0603060503060c0301080a0f031701061115010b0936090607050f03010306050705 78
    0x3696440801d44c81c15807081c0404180d40d15901d0040314000c24a0200c94083da01113808c13505100700b1081070b1009e84600096240d141c40c46580c0745c2c3e025020380400540810705030028000101c1c1d00d500210722808003056480b02e4010b01100b440121210385410701110301d800c0c1300a00c804100782c1c2007c0151400101102c074140c0894481c507003168144c0f03078010358124445c2c44400800030f0400000c4000c04441d00d0801c02c0780700650100785d480c0700780800244a06101103944d40314900500c900241000054503040d01c481c1c481401070b00400c424051688203200da840015005c8107168201c0381030799004405030010403025079034142c00b08005c140840510240281d0b8004840c241c03d070082c000c001994481841009400580c0c2c02c180c440c00095090014110041c424021400c0c110b03074021100350750241005880701c2902c000c4054804070840d29889206040c261403000703051442c010080b0030255aa50740f01d1010a80d070030b00c0f8402c1034201200c6e041c001000070444560090760701c485142842890 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 393580179 1250 393578929 393578947
    0xb0c070201050903070b09011106060a060c03052a01060e0610081003170702040b0f01090608070504080f0c010e190504180206030907080f0a0c030b0a0213060c021305040b1b 76
    0x10f05c1c1036034205440c90708000c15202c07190340e800000005c00b407030171602034a803070306141c008201c50f4085805290280641113294204151140c6c0440703c0c0c400050b082c03180701c0c0440080001c1c0c100203e1119181c95030800350041418028005054081d07c40101900306088800805445040d0020b040328190340036244000003141c01c1659023040c00300d21401040e42d4440b81d2041104440b2190302c4203004644404003425566000100c0002751000c40c2003400c525510054200c803d4810398004103258010311903456841c090010b05106a01800d032a400c41c1c00d10803600380245501c205005d900c0c0502084400c02547c01c180d40400107500720f0755a100104001d68012461550058621401c540d001c0744040265034030030b00c4079085e0182c1c1440030b0a08183c5079180c10314204100e00000d00a02e01110104110401d00e0341141c43c07940d908600c910090742d440300c02500f410703825502680a00c04540c6041201d5070316100f047d01c185e910103540d0460343c43e4900d98400d01003810070b0080700c81c6e0003003001c03000d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 393581429 1250 393580179 393580183
    0x2104020316090c03060b0a02030d0504061b0c061a030613031b0f0507050a05010c02040f090f150c05031603020a020c0a0b040f080d0f08071205100905130b0c070201050903 75
    0x301800000c08080392100650f01c0c000c0895141e41c1c45040040c6080c46980c21095000c07040b80c1c4071189284001c43c542c0c40e0b40c20034000030082d07088284019400c1a180c0b91200b174000c200c261803180650410407130000883c0c00342a001880c1c004041e40750b0400c100207030176100c0c02c1c0030442c1f8480c000e140441c200121041e201d807445901d01700c180c0e0114100100c00040100400c01c50f0040c09007034406400c290300e40300000e0210520301c44000e104640396080c0e10741c148010f0384900c0e03c041d00907214150314940e500307061400360031042e4101c114a0400e9402ea12990054040700e000390740310080c924451502c1013044000390070000007981140504007074080c41c0d0b6640f42402c1c0c0a07005d0a904159a1460550400c407a8003656112400d6a00710703040000c5540d400140192010401c1d0400400ea540d0321071040b07810345510b24081d019140f9207000e01c001003003880ca101c000e0b50407443e1708020644075102000c0600f861071000800104002d0001881441c010001e40002403040c10594140105400028 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 393582679 1250 393581429 393581473
    0x90904030c03091a1902070305120c101803020d0306030809090910060303030f0c0c0c0b0912030c0109020a050f150c011e090b060108040803011203050f030a0c1421040203 75
    0x1c072140001080b2075903007400c2c402c00c2d1624015140000c2c40e87c070b46141d031070035201c0035030221a404200b008208541c1544082c0941001c0c0c190307000d01008448070003003010445500c1e50006034010300c604c82c03403200342500034032880040e0303a008851982010040e10410071a4800100b01d01010b000d5007184c01803541d07080c080c00e40038501c0780e10301140589502c9140000c5405581660b420801455090004100e1085408040c6d17150424459a04d0210b034020400d0103654180d1416148000a407211220344d0640c81000654410c40f401a01d1035603960801100944d40c084803503002c80c941513805aa60500c50090203c24903010003c5110f8002c960070303a0303103200c160b2040b04c041600c401c0e03420b042004407564182c1c04582400d10441c6800c0584951500e40014001c122048501c20105000c1c18000c3c410713660740c0d0744010130056482c0b03000780f0703540e01074009402580045003030080c0201c0e8121059065481665030701000c41c9200212452207481d240001d40140d030140642c01600070010700300c918070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 393583929 1250 393582679 393582719
    0xc03060504050a06050a1401050f03210c06070f1d03011e1d0a0f0803040606050915150c030702150d0204080f06060604030c05040c031d01060317090904030c0309 71
    0x2406100f07a02d802c14200342c500041104c0d910500d0b03e0100d4a50400f000c009034191842900c10f1022007404034003091400360503010454070855992440c072118141c1200030210506c6903401e4406644403103000356401c0002e510100085405d0045444028003801110301341c0c110010001f01d410100d10090001203011a0400010b00341c8480c036055800000c25028071503012003100811045005484240c0000007004006064102c00400301d8244445500304802504c4014840e514604203101e00d00180c056842815004410a1038010010722041d000d891303141e0a0302010750310b40007040d07082044030710347d1804800403500148440c00300c2103030500c0500041c00c900402007142da014030f6185031404200420440c40b64034104420310008030003403003180403030310300b41c40c0800c41e4401c07918150060040d00445610b045071000e200f5000a00c15040002164022038001c503801c21108030304404c920030540340755004501000881c0c0000e200c2c01c0103406c1c090007842e202410359211010b0a202c10014111 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 393585179 1250 393583929 393583933
    0x100306020c0d18080705060d1524080609130f1203020a0915090608090a0f1104150503030a050a0507080315011101020a09050127090906051803070f0c0306050405 71
    0x502e40007203411107043c900d042e8106003490b051625112219554001303a01405001d0003005c1004040c4900076000520072031620403550841546034601d0480741c6011000d01500001c0902001102e58041c4042c14007400c0c000d0b00040f059a07903429844aa0360b443c820490b940c200304201715010900255035461140c5150b580540d0312054840d0080142070039800440c0507500b40d40b4260740d01d9400a440800300c5001e42801e403403d03510400224280940f03800013820401044598030200049080015408001180c0400480d608281030f103581000f18040d0325050b6100300002c000b524064405010740701c9207850000d103010f0b200da94480403a0020b541c0340e41c10b2810658100389031b41e00849010181d01000300214200100c2e00b0f030050445102d445604d040c0007110f201d5440c1c0f0041803682e00300350340c421803000701780c640d0380d41c0e50800410359250182ca1592504011994036010b181c0120004c0803010f00440c00c00b26591030b00646600104000c40300407085170700010000d4514024644594000c4c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 393586429 1250 393585179 393585193
    0x6030e0a02040203130c150507030c032d03114003080d0c03020a23091207052103030103121b062310031502070b0c040305010b0612010608100306020c 66
    0x80c141c886d81c4201c0d001008003022649a600d04150711205860103182c05161a140102050900b03481070400b02b03010210040401701641c481c2c070304840801d56100c01d070b87c0c4e080041d0040e006050070b60780074000c40b0350229076048c41c89440d4800100703d1140200c011982c5c80500100080d40c804060301151708c200c680000100341d400b549401d51090404d50307109400c0c01e525141c084880100f55a2030300d585003d0f026030070909050740e244004207460020601405c400250241e2000b126500d02c007038400e207441212405031048034035945402e00060500c00000031070841c1d09554851000780010190b0300300b080802003448d40c000554481c0d99100a00130200000c142110a010300c400b0740f00f01d5080c2e032507032154800f0b10403113400407400081120f070014040c1116008250483c00684103085003e0b000059030410b204080d140e000007801101c0c0700b0b07402000707250b03400340910020340501e071012a4525035117401040641d0203908203651000750b0f01c1036070101940301e07a9510704982102d0709024143d80620 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 393587679 1250 393586429 393586433
    0xc0907090f0909171b060703061404051e13020316050d03080c090a03060c0206060a05060a0c02030a052b0f02100b03010e1605011713020415080a050312011d0106030e0a0204020313 79
    0x1c0400c5030054841c3ca01402010301740b0324012b4000c2000800b03140503c0c4c0e1140001d20518400c40f041c4a2035035511400d41107402c0c086d680e1100c0c50004d00090b8464040d545541c18411181c000071011107130082c040b00c05200c1c01d618141c62001c4001c182a10948003000303420b8032030347c40300c104002841c8501e00000d01030307002c2c000c02854000000c080f18004c0c3c440001c14001e03552010151290441185407e075544403052000c603041c802650001807031441500c41504596070104507484000c03194091000c03210850a8007141c0d505e00d249100340c09070304070400c10000401290420241d1001c060004034610792b4946a0074034000004c8280204d5000e0610140425030b40001c2c01641c7d0142a414147d01d400c04170203c600c500350141000b072265a40d9005a41894162000a801040d81c5420f59040d000f1904240e80c903035026a4240031180d140c58004592090b041044807880c0400182c1d82c83c0c96801d01c1c0083e401031030400305c04084e41c4a0f1100600041c0e40d43e0004521441d248800350f0807083c40e0b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 393588929 1250 393587679 393587683
    0x10e18040b1905240109050402040b0309010c081509040c150e040c03020f040e1003050d05041d071e18060e040b0103050f041709040e0c0907090f0909171b 68
    0xa0040c602c01e03541800c2c24400e905488007481d200c2402c00d603150100c41200308006840c00213160f4404d540243c0041000103031480c04201441c07007080554024015070310010012190008112410310013034051040c0101141404210300764068400e0860b0b104080d116000d422200e03000116000008080c0c242c3c400e110700782030140e19001100344c1810740c2410540040c044860140d4000d01034003d10820014448441218504001715008019211074845210008000c0da02a00800010600340c03140e88140d046900480d270b1081005603980c940005818142c1d0500e068081342d06020440e054091501c00c2102d00301000040134240c90718414040c0c039100f8082030b13030105d800182c145407800f410004002190410b030365006600040c029410a0b800d01c4014083c02844a0160018541002520b82e5180004c185080d900c040b988080b03039a90fa20012140a10180a03040c04101031210030004441c107a00842c0040d031044e840c05100c10980034501c4100e401118054000f1410144000100c40381 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 393590179 1250 393588929 393588961
    0x405070509091509011b0206090c0a1202102705121b060307020a05070b030f090f0c01050c0102070209100f08010b0f060c1903030605030d110c010e18040b 68
    0x41500e00324142d1900031600360320b4041a88403034184100200001364104c50a50155201800c081040118150b009400039601c11044502c550140b1910945000364904509411b0441e40c0980e060001c00006a083c851202d24a15104041c44805030030500440d0510030000542035505140110031443d02c41040b41641d412040c030030242d009184440e18038520702c100a0000041076900d9a5240c540440491038809464406803c81c0141140401d90420401c000c2d4002d815201a8203016141d4080b990f498262040111070b40798403810481c14654081c1d009046548a0040011308104640c1c0108512000403100c4410011310380e8024008001c000b040d15000d411810020043c8400700c0c4049101004404562403140f0f501141c00c8015080410901d01010450798122950b08864a406800750240e03008051080c0617004203c2046445202c1400040302080014030300081400010f644001c06036841c69081b11500800707804035480d454086008038070590340d42c40c440c80d00641c1e0500403d2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 393591429 1250 393590179 393590189
    0xc031211130501170105010c03211b0e09070827010912051801140706020d1506020c09010314070e070c03030c0e0303031f050a090605360705090414040507 68
    0x2080416a20740d814131110b4181580e00c2800c0c40054404581415514101c03010064580327070203140020302da8401e0b140c006140e485000d028485061020070340c10b55190380c04100082c0c00c10760440c00980102d200d40c0d0200d400c041060000c1d500b0803a0483e91074000168034411400d56911012100d0400c1103008070001803815901c0c1903070426545518030b13240903141c0d08600d0b042049081e0500485403000c001c82d10740300e60252085680312035040014001e4500003040326030420600000290081c0003242c50b406080b0002c1001016a08650b1860003080313a143c2c0c4842203200c0c1c0c0d0000303d000d01c00460707082c0c01851987ca80448403407040c500102a102d2408005007000108a0014140d407400010740b6009040c0070592442c5503000c0d00740000da003d865010507441000b080c2c00056176100c0387c0c010300c00d60340d041d200c071003400c6601b1100a007801202c80b80c130301d0301c02512940d0006c100071100c82603400002c903107080c520301a942c50000b025168441c3e02014016120014481082410818640149 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 393592679 1250 393591429 393591437
    0xc070602010516031413030201020d140f0705131205250f09020a0c0809030f1c02010f02120123040507050405030f0d080c0c07080a1b12050d0c031211130501 69
    0x128090380b00e02c245d0b031005010b40c020711016034000d10415000390107aa00403072101c0700811045054441c11140803c0c107407280100c00244030085880944140c04485010881d0494203500038a0305030580e4a40d088200c0688140c01001d0100800c80818000b17030f030380e07142105514181c0905240c0c1003c1102c04540c488029a032042000c3c00e85070341c0000101c04034540107001d450f190989070000c281014411680328046000b403280c60364520110280350702c0c00286550081040700c5400c12410205e00c104840c500f601c1e23106100401120610140e42043c032520442c0325039000340014042408c2c0c410545541c808508085005c1c0194242046035240c1f141b6604000c008004070400050020500607100e040300344000100d01d0386000081212000070f0002d80e0031182125103a06040181c00340000c001120004803041c00252020440c5070301800e250000064600826204420703188560701c184110188400b0b045500f814085500c04c4c4000d086496100c65520340032107024201c0c40240d90030a038140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 393593929 1250 393592679 393592691
    0xa0c0305070b071e0f0903150e010c09080f03070f1712090706140a091a0903030d020901020d020f0c09070e10020705040b0a0b16020301060b0a020a030914030604060f020c07060201051603 82
    0x3030303021b160401281c2c0c1007010510320840424214001e0138445207504440d41c2000d4000c00c410780d000c0b41001c2102c5c4002e082c3d03001d500080d000d41d6100e10405802030700d451404030345100400c040309151980e4920025182c0c1c07034a1021503801003200c90496120102e03801c0b81c50100a5550070410071030079403006000e854030b045880740c0c018120000d140502c2c0c0000e281d42241d001d10040d01411646031110040449880384142c85d42c5074040c3d030145040ea4010f02827944480071107400066840820b00052020f0300b200b421280c00d0140d5464000c04480030801094201d5a1603220b030315141592142e00e5010b003c401d401c042c240300988070110281c2d8002c0b030100b1402c2001492540950344004400c0b6482d403030100d91400040d024281a400c04040d20134002041c001042c8c0007c1c0c0200316601c44c0d141c0c1e6424039600d540b05031090522101417a0143c01850000740001d02c141e201020200181d200181003056290b82d841c6002016009900540e41d55000d1280e0195024090651401c0311311381402a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 393595179 1250 393593929 393593957
    0x150105060301060503070815120a110d020120160803070611180409060204210c06080f0606090d15090b060301050606071707150b13110a0c0305070b071e 67
    0x11354840204450708010700311001c1070140503a45201e04001c0f01c018109170608922400064640c100320070220b13031400342000f02c140b550520321480c00c40160141c50712007600c0d42a0070050301044040080604c1d9008180c18020741e850841101c07806041034030011600d58107a0700d44002241c0900d0038107140d00d107061105202c00c50724034143d4160384a00750340101d905015441c203d006400740e5040f00b40d406544002010400d000640c10300881809900002c09c400c1c0d40711425600341d00181c424040109003007002030400d0400c00c00420101e01d000d8001903041c001134990044002d1005201d046030741d140d0305d0030014450296003454002e01d040b00204000c0c181540018003500c95968000e01180034903180300c14030540c0740d0945840a81150603418055401d0482000400d1620700180c0b1403083c440211012070034610420080523101c1045516100354500150b60003501c644c41180bc0010400c0a81d00258488001030b009034415140c2d0183c03102c801c0c1c609a101202145903a04004100b62403500c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 393596429 1250 393595179 393595187
    0x6190b040909030216420c03202e060801020c01230601320912010b0a05190b0c060a0c2316050a0b0403030b010302040513051f060215010506030106 65
    0x58038800e0410b610000498000b000443c0b00c06a0781800c0e0310240401040c2c0708280c0020111f42c00e40d12075a0382c0c5a440c2d10741c0345800c41c3d490030b04000300556485140c000c108401110102d440c0b003446060a211005540d190300002d0b1041a0008003044c1d401080c8240418002d000c4c900b4034045480055041441c1401d8034887c00d10001c140c3d0341000210301d01c825425100c07181d224140c40c16075940551a2890600300070311588003c20031401810110b03241e5101c0d00040c070914180400007024116080c3c5000d081001f1048150458682c80003041400207010007084001c182184ae18405892286004600501103444041c0b0000920440071000e82d0302140c1c0c0d03104007100782c5100507801d80780d426058842c00081d0107040003d0140c482d00c07898100f84808520307130030301c16442560b05212000380880110305030300952040941001d4000042400303492a50040c40c0d10a0800b110b0b500d084030384800020100c506a407001c00076070019108220389040b100906c0f0b0240c882903403114995450702c20020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 393597679 1250 393596429 393596459
    0xe03120715181b1505070f11030109030e041d060c18090a09060605150a03180c0f2d0504051305010c02030a1b0b06190b040909030216 59
    0x186040d94021401c411181d81d0742c8403403204018031100b441c002c1c20a03e0b149000784000220443c412a40400000e03503d403280514440c04030469880900307120850b0746464401902c07040480702043c2c8084004180c1e00c09100f007408590080d500d540320048080d00b40800c498030314000c94507180c10b660a441e514140014581d401c54041d00f0035540e24079940e002e841003207805410903035002c0c41c048140145945540c00c1011054041c00c010030a40b0390756005c0201c0d0018640080007040e80074048000307070310f0003603004039481418111020706140d140d59601100c1506900030315810a040042402110102ca000c00d440048801d40c500c401200000102000c000354404d4070311070ba84034000603084d0a084c1c01a50303c0140c1c080c1c02807180342c603818406500d0b80c10003106400059080071400e0180f41c15107400c80c00075504001c001c6c00c6500c42c0018444480b100710452030710055007180001c0c41e10003c4006200400480000040d0281c19150003420915400058940c80342c81e10414841e900ca4550a1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 393598929 1250 393597679 393597683
    0x304020108010e09212104150c0203130902070b0a02030f060607030309060c03020417150a270804060806060331051009050c09240103020f13060e031207 67
    0x103011107940320380c9021703d050f1401890181d00515801c00d40e412882d01030240c42a081480030a08071108407240d14410440221000303040841c0e140d44844000c0600c0d0b00041c03151700e851058a01d4003002e452092080b10a07a4801e240103a0f0028040d8148200040550b4000040f90300a40c03440c01c0402081d00c41046c0600f0040c469200013800400b014042d074803170b101042e070155046c80a40300c2d200003e0001c0d006071003003007031103140301624174900e010103c1c5204130084174092404050302d035106584002c003010303000069020400040d0300f1844410210450b0140c2c4079180c0c59603038034102a8020b050040203003840d40906c1040c0240010144c1c2c013254140b1080070a10515180904000781451021000308040e0560094140c601c1941c400d542103810203078016800c0310702500040e0144a000502110407400301607185001d440a0300c41c0f405900c6400c50145009820820482c061a45c2c9a101c900b40450403003141c0c0c0300b0082d540d0480b40408009004a001d01000c8075840429030043c8121000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 393600179 1250 393598929 393598949
    0x50c030618010602120f190c060605010509090f0a06180203190b011b020a050d0c0306050705070506011401020c100e090a0c090b07020a0b0408030c0c030a030e0d02040e1606030e03030402010801 85
    0x886c60b50114410036108040d21106181c8031305000c014010300201c070f2658041c1d90321420214085843e5000303004842c00c15001404152107580c61600070a4010006403641c02200d031613210024115106410f00c4443c01214070300181d032400c2c03008241540c40e14400043c49180e06015050420742e8000f148a02c1e0b281c4910f804081600702032002450100d00f0750401c1e50700c0303043c07007089a05105040544c0f200382c1c1d200300400c01c000d403110f03e410381e00c500864400030305a500c103000510200303002c00140c0140150600458403051088000207540400e12515000014030440b1013101919201d17005640001c1c2c02d4808000b0704c0f00c40f0354010701c80c1e80d10340649620003100040f15021501d800c03000c1c2000303104e8501c1c49512540c9408240d03440750712030044011184504a0030b080c2900d0301040e10351030070b039041d00d405c102c00d420340060040c1c1c403060b03840c03da80c803035603407191180441030600078520840741032280410000d081000c0541101c400c00b00b40c25640d8014410400180d03088159181960b100c854 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 393601429 1250 393600179 393600187
    0x6073c1107050603010602011d06061516050316020405060d050709020903030f0f0a02060f1005090603030d0608071d0103260705121201120302060703110904050c03061801060212 78
    0x14a807070184540c2c0401d402c100300000014030f442d81980100e042903103000c0004400b02c20690001d0351102c00360b83c5a03600414042c40d00c094002c0030700c020f1036450341c410310042c0290080c0d119982503422491082d52142c03402d4119404500c3c0c544039030b07603000741c0480341038039452426180d20340c0d91450703400341d40e20190380091440c515903801c0040c0e80074441c0220102da51220382440e51005034110030380c118094401c20000c5011025503140c158441c5214004a0f1103541c17400d0100811204043c1c108c40d0507000400500244144601440f00a0280714008000c250b10380b034441e28000071218226080300c03401e24010700004420b503420306485580d54000d215034108441260390036201e50f100080032442441041098890460050041e045490300a142d9907031780d40f1401c1c0c6140202040040040e00074000061565000794000052280344c64282e500345004040490211003040d40d036903409040c0441003009501e080080d02c1c05180c80403a0340002c5514020001e960b03014040c800454030300000c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 393602679 1250 393601429 393601457
    0x2120f100c0905190f300c09050f0907060e0d0f170d0f0b01110607200f060103050f0d170c0f12070e030601150507060b0306073c 57
    0x1024140580f100412106130354110401071001c20809109200308101103100000d06903050015040b0b90012141031083d0b19604007807130003080c2ca01620111500b41d000c10b0301040c504107610655104079880f140d00542403c081804528140c0691300810400142d054060040c2d00c44070051520290702244002e034454041c9000c2815036000e04040307024810209019044040541040442e12541402000500c1e4a0001103480a0b085c6095810560103a0b000c601494420203805410603030351f1030441e9050710740c61403d0341040d1400c0c0140e0a2944000014414010244220702221901314020048000c080002814459601569010321112000000c0301c0c3d0a0307050454007180a503c02a980e1020011720040783d031901a1485c50000e083e011202926040006481d4140c920074489800e8450400d50202e0f00e59020f41411600c0c5031b202c002c400c046071001c0000700e004484580b203207050041080200d80341c1c1411039040502c2c001a56258140c6610645901780f00f0f2a01071030080b01c0c442d440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 393603929 1250 393602679 393602687
    0x9160b03060a05041b08070e010c0803190f020a02010b040e06010608090a0f0605040b0709031e08090603090a0b100510032a0f170c03130201171302120f100c 69
    0x3640b0480d000350030300160b00c0e41c4a04800098051750f0a40d00c5403130054444090444180030b41c08091030108000704010004074009002450780f08144420b019511041c8910160070380d5a80400c403491550089101c8901c2c0380c0a00411440000c1550700f000740401c001c008903501c203418810030044c00076042c0890403444040c800d1082498005170490300c002ca0b10725101c4001c0004890590b0309030204030109900c5846801d52404580e0000c00c4e16504028544c600d180590100368205c0e816034041001c003c1a4950760003552048400801820510003981030181b51031400620360131140c044801e00f80403a036900d031142c441007040c52400040b030700c0031071800028100d810782c8980130180e41d0319201001c1c2076000032141908043ca03074404600c000f44921480300e203401985c4400742e05a00b440062125207100414140c4e03280145007040540b0782285c003910707110406440068510f8050784c865002e504100d8a1440d510140740d00618055500440382d41c3c030340c00d490444081c400c0c0c481001d60364051103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 393605179 1250 393603929 393603949
    0x302040e1203091014060901031101050c07140901080d0c0609030903150608010c021605060c011e02190c020d0311160e04021806060304120912050f0609160b0306 71
    0xc8031003920365a00f08020190350326194040d03641c84c01c07400c00690100c0b2516052901c1d00079031014204201c140d096556030500036407500d00c5281040400c0c00005075607181004a01d00603c1c021a892002681708001d0104940050704400e48580c02039500c0428150301c0f001c1220782075041080000c01d400705180c00c449050241c5e001800d01a402d82210769003841550064003162084d500800401491900a9840e0404007400b500190b480d0001041141001e174001c2045081040000400c11800d40e00b00303859030359a40c8a0f0344102d60119144c0c0d00810b0814003040c43d000c2608210551002650000f41e082d1002c41c3d000b002c00404945c88004c01b0802c100c410400c0c0303241034050305180d03140c6681600c0220125000da114242c06c3c01d598034170041c00d8841c2c0c0c2c05000c016051501e140e841e91181d1454440508a00341000420000011002035841c00c2d210041d1050340507000ca000a50005480d010024001003515044500c0181c200c00b010b441c0341d000c45611000c103e4403603492000003220342103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 393606429 1250 393605179 393605203
    0x3040b040b090d301b0206031506030f071202031005011808060718050a050f060309030904090c06110c010e0103090309090203072309010e0d0f02280504050c040302040e 74
    0x14060348a068100450980820311142280c0040c0c000b04404c81c21202c4000d002d200040600000c5004800340c1001801181d004200c0100c3c03115018107078002c900319a000325112800e0003110030500c4035440c0d00a0050001c80f40030075055080d03042070001c1441c4035039584074007410b0286103d20b1040300c03171400c1c60509c001c1400c282501c4a61900000180c54014910b0401c030404017804c1000c1014038040c00d0800590707101603c3d884100d115902484607951001c4d16625103031100384403241280d034403809038407100b41c481c01c18640101e280c040060200301c10080c00d0071182d01b203420b1201072a44e000d20a248290300c01d180c00300301100a0b04059528541540080c109940004108813803681c2042210148440c0700c00b080c0680c00b20051204002d000301210f080c0060701046401205150000840b08250f000c0c04140d075410302e00b0b034009403190b1070031b00c0b83d06c81c00140d00b0600e681b280c040503010801400300f0f4906001034a09241c080c2403500c2680402489142d455105550455080060f071310006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 393607679 1250 393606429 393606443
    0x50f01020c03070f06030c020115050103050c04030506090a11060703140d021b0304050a080f0607030f020c0d020c120d08190e0d02100b0103022b110f040905070203040b040b090d 78
    0x280e00d03042004034005085c01080b000c2401c001c141140b00344148254000500e414440800407428103004401521001c0c2c14540d05500502010010907030610420f03010f40d6000c001001500034034640000c5003c920743c4418810300e004d000e09000b21341c0000c854160ba8070310900080da60354416208200038040d92540e488049510401c411032040d0020041c01aa5000c8070030888060b66400d01694031710003492105e02c2a00f010020540682c060b41040510080c0098003604040122000302c0c03400740103a807403100690000110304941e060a06913007402030680406041082100803014003660806006110141074941d08455520599031048544201000c165103c200038024001c5da5a03200d500d0402e6407502c0e10310f041c20f0b650701902c21100b4281d44200b0003941060044c0e29134401140780381004941d0340d2101291400d691803030006106664040c0105621142404100821180020400010340d4801c1005215000400cac06907000c9802080c0c0c05a60340e4800c0010441040980300018070403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 393608929 1250 393607679 393607693
    0x303070309171b0c0d05030f0306040b060f131e0b0c07081501090501060302090a03110109090c05040e1006022d06070305090c011805010507060212011517060604050f01020c03 77
    0x4050700741003075043c00d41c02e40201c49081804008000ca004141301c4010080d030b00401c00201c81e5044400030315030000c0000d00c0000c1e41322846002c984603900040b24072a08031400200307601c40383c83c40010000a820715200d00320400150301e1501d00008001c0c0140400344070007007006100d40c1c0c0100201070151000c2c4065618541024040e0601c5070400e002c6c2a600351b04280011480c0c91180c4291078a4200c001d0000c40301e030341ba5860f01801244c07c81d008904010780300d5004034404c0c02c0b5005180c0190081c0e074030030307980b185465007000c0b005901a2803175200740c80c852410400d5a60015800c2410040740490200340c20300030b822003d940900c80e104c801e441c000c8204014205405500442c4180d90040513645076001c90001107844404007034043d808540d03801d0741440294440c074007820140b44030346030051030300050b0000e100e0604400d030302c480c07100004002259141a40510304400700c007800c200c05400740c01c00d28005511809a809010301803c48151454026882044a0300c040031024081d1081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 393610179 1250 393608929 393608947
    0x302100906080f041e03030f0501060203030915010308040302040203060a080d0201051e0421020f0105040c03030e100e0f010e090a0501090b0102070806010312020f1002070b010f0305030307030917 86
    0xc80d1128407500000c2851203002070342c00007105000c180b0807648603101044044070440801100e1010b03043c01d8041590303650114a19041600c10a4041c0106400071622440c00503112071510010024000c0c1c602c80070001080060b00e071000341c9051320750445000d42c072a642c900204441d10f583c0e500180e42c2d442001c903202206501136200c54002c00b1107010407004401000d20100c401c1d082610020b0204c1e080030444400300b031783e1114605013000d15105440c0741240b07480303d8509440054806035070340e5031048001c03c01c01d50841d00385040c01c5401c6c1c0d80041100700460700a0301c0100d02817071040c0030b01c0d040411200b0580c82002038040d0100c005140d500310381811040480280004d0041001c424036044100701c4540c000501d160440301c02c10000d2481da825541c648005100d248884019846140c041001c0240306210400100c58401001616800d05003054507440030182d00c0200218500d01060001c22008001c5a41c0070115042c04150f007481c0b0b03c3c1c44801200400d02c0d14515031000f040c0150 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 393611429 1250 393610179 393610187
    0x1b03020d0f0b0d0609020112060617010e0c04060c08070f0303021c020315011d1804030f0504030804030b07170907050f03010e0703030c1a01090f0c0c050c19030210 72
    0x140610266010000e080703001200d4011911042e80e034590100c1050503010000f44c2640210003214070614011700c2c02c002102844054a1064100101141c3c40d08007403a07596580e90807580c014030000540c001d8a007440e400620882c4201e0103103400b003055424181083c0001c1d01d08482d542940400c0904219400b0705008009401c080300d02c510303c500380341200d03403055424000e9070b0144c40d404410722808501d000041d10504080034800c0c4501100e400701d4521a0f03202509150071018072000c0100e5864649030081c140c4001480400074043c2c148018400324040071b090b581540e86c82280120b0740d0700c4854003a501e09144211200d0045403810030008240380100708007044450645201204007490b0b410142038035485502c5c1d1440f607021001c00c0022910446801d10414040c092000e02000004020b00d52880242c0008007503944520030307407c1c0100148180d1124061a140c003850520b90365441c503032528622a1858810610000074840385d080326076003c001075a000b010f5482c48014464054 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 393612679 1250 393611429 393611437
    0xa080d0501060e0405010509060f03010902090a090302070602010501030f0b07021f061701060e040611040806040b010f060507030915030b0d06090317010305070e180303040f0b06100e0f01031b0302 86
    0x140000f0392014010140d41410f0103024103031000285000410794403007090082d0495002030040c0d040d92140e20150160310f640c098a4007039580100c0100e25180541806454100154045c808680c901801000418001e110001e01d440d8407040c18051a10380d1780c0100c2c41d044a50200e6a46d0440c0c2540a000984c1c0e15840101218140e90f014101ca07492080c4031400c03102d07070b4402c84000344916800900042d103942d021450024001d07060300d090035140d0041920f0309504990498400c40b04400500c164400030f40420010316183c0307012450b001d030580c0c1c0100616001d100c0c00341183c5000c000058503c2c0241c001d90300598014022890b1030200d414900080c0500a000b5400b095500c401c08444e8200e04803001e058031f40080c0202401490500d60f03800346480101001c810241001d0341245030002880114040c900512000180a040c1e040840c0d400401602d03042c492648010000b030740c00d800c4503020a001c14215000d0a0748104000140c003d003003450943d4600d4045090420401901a4064 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 393613929 1250 393612679 393612689
    0xd02060103060f0b010c08090a080607034106150a0c14161a1303050102030612030a09050111190305180a03021e0406081906051e04140a080d0501 64
    0xf808035810f220040d0b0b0803601c0e401c6440780011000c4a025011480d14801012655005011006000d83e242c080600b000000d0b03074402c0000713450b1100d400c3c0c0c80504548480380054111a4407110a94181a0380105030300302212414000caa00e0014400307680302c094000c01c000141c1001540c81700c01e40300040c00e0841c0c0420480b1032140600e030340f158a2500007070390b040400c1c060b07264110150800380040c83c40a28034180c03458180041140941001c644003407000114400d20016890b0b042c00000c100780c1d4003d549030410540e00c20321400c0c41803136000030500d04642c000c1c2411a6100c1014019a00b080c800320003089145c0b2101440c0010964090000c20a00d0046280c030707034482e0f0340d441c00c0281000396440086d501541c400002c00b03601d01c034801c508084002c01000001c00a64813130165040480700058840560002c000e08410b00c00140110707544016800112404920400d80388034054901a02c0549000016590814140350030009000003a4103c410543c99205e4102528040e08090240b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 393615179 1250 393613929 393613931
    0x7020306010f03110112022506050603010902090112110312030115111e160e01060f0e0a031403072a05120c0622030501020703110f0d0804080c0d0206010306 69
    0x900d142c0e1509441003a030364070032012800a1804401100d10085510400c00b50603400c008210714500565205410300341c20f5040c070707a02003e00707040140441e10000c101ca402a410041d5440050340c0380e0480c14151405903c904200302068209451003054a18040d505445102070803d5a00b03660000395048402e072920703070000000000803c030b588071006100610030340d0000c80403038400c020080c902e030020104202110030100001011140f4184c55a10203e16000c00c440140802640300c20100c0c410381e1142000782c45508010049142c4c00355a11000e410b81c5104036035441c42c01c60078812a49035903003000d101031030081301d801e44101070401c0001d541400074442500140c281040b40d0f80c40c1e0740d294000b0191004409440a014641d4081451024540700c0c241100a004014042c44409540110001a110741e12480c1c0030b450064040e1040595a1024405841503d0300064071040c0481c1c0349403200e1292513038541042da43c000c180003082c85005d90b80743c0c5030601c0d50001d51241201e0058038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 393616429 1250 393615179 393615181
    0x2010b09010b07060e0718090f020316090515030a060f0b1201061d040b0708040c0503030c25050303071101051b0d0e100e090c0d061502070f0f05010305190e0307020306 74
    0x702455550346d46110f917084400d02040150201b6006600080403203029205400110002d035000070f06000d000c4918041c07030408884d007400904070078410745078069000d41c80c2450064403103000a42e02c004800b001407035507448400100480320950400f0001010213441d14104103558440389000e045140209100c0d6020340044030b81e00624014541d0040c3c1d0000c03402d013255242e552045840f048002c100744c40380040301d0310014494074108024103d458411015060003030500740f1000c030011040c100c0c1d5010010105043c070a5640120841e042c03035512110380c0c0145a5803a0050300c036401200300d46400ca09060306420324100007c074419804490b41e0341e41003d030205070020084401d450f94602c0d800945012107403035890405212040e04500e440c000c01d0309001c0e049941c0d4040d10f040d90000e003080d605018051001c2c60b0100008809880440c0600b20702c03d0a000c04080020a180b00e00c50426442d6030215081404454400b5175030108160140302808104106030f55035030000c01b0481c0240f0880c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 393617679 1250 393616429 393616451
    0x213141305061003020f0904170d06030605010518070503090f0d03020a0f09240c021e090c0f0904050a1d0d09080c060f0f0d060609050109080c0102100c02010b09010b0706 75
    0x49000741c2540d5004006e8816918050184074010b80024800c5507142c4a113115003840d0074284000e0000b1b03140740d210216051381140382400503034030b060340064010740c5100900c0710940039007402c0e25405003182c80c00d03603205d9071040c8201d4074046660f00040c4290081100111810358541c0003052110741940b00d505040c151401c084410802c18400c540240300d2a00c02d862528005052341804019180341009064200360001100105080c4d0040c10904407204464498201030035880d6018904170000340c100b0800c02c400608503c644011135200d19030300c00c001010504039a00c03143c01078025400c08900941010980d980c1c406001c124500443c0c60207200045804002074007154120010389410b00b40b0600311030340141138000781a00c0d182c0079014001085080f0240c03082000030407030b030780c2ca0200075850701001504891064004501c1c0b034000b074440c00c0d226600004c1d14030360f0300c1d04c0c510002803080a002c0d00700d00410b01d03a9411903220000780c00006264204038003800702d560042900b001442620 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 393618929 1250 393617679 393617701
    0x10f09050f1e061306090c11030c0a0b07050f120f0901110d1805150a1d06070810150819060f140303070212060a05090c01020703021314130506 63
    0x403200d5070101000c1203150700c07030880c0c1c070070b42e40741c01c0b20b005440305a181c00132030281415103880c0d801042d401503460445500080c0d2052a085814072800c000e1071610400c0b0b0009501c0f032400701c501424201540003c60b2803144250300b00e81000045144441d110900c850421240e80c030142c4913403030a1644e640100704114410320456401142d08070002c0d00e8044048100c90261801402c6180680000c1028901141c4144900c1c0408400071407100f500345404004039044400c800c0700481042c0d0b00f14040a4003c4001032104e401001a041c1000305a50300c1a41100001e01d03500002c0198088480e0807856580081189005000d098040c0e0281e84000520100b02c0d83c05109440ca21041c20004220724075408401c0d00d90642c0180641385011a1600071a0752805c189141031465403101c4201b10034450948641c1e43c0000702c20024044080c400f00000355100e03032901019102d11820307180228440d03155404102c40e08040442c045441c070300000a40c403c124059400e0350f440c020403001626601388 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 393620179 1250 393618929 393618931
    0xc0111030c0a120605040204080d0305070c0b04061a1002160e152103071226070f030b03010c170f0601200123061c15180803010f09050f 60
    0x15550101c2c0c2001410801140d031400444211141c0d582c1d10003000c1526101c0340003c002134072410000701400c06040760000c0846000400d0720041000a2040380002841c0000d13032038006030880b4002c51500e4401107101005182c11104960012542201c01c5003030742c01081c41e03111004d800350740c00102e55444403842014074089600645003113040d400700042f441c011004a1400e910807020341c414103903c0c1015891507100040550300750344030b0759907103246c1948505c51080c885000492035404180c1c1c21750300900900040c02180074041030406442000d4483c0e401504101070040c024010121104805860301c9403a01e0b900702078540c21300000703160036004103400340514410b81d106401881d0303039040c9000e04021060301c1002c1d55250170300c07a41a14492070345417580c241810301946090804100708100400c00b140390781100d4035080b485d00c012401031021054480d4101034003080342d0f00d00454190308001e00e4074001380307224804400402c00c11003a03d03800094801510b000c10003511030680145035810 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 393621429 1250 393620179 393620191
    0x1050a06060e0306011a0c0303040501061401020f0718271e0309030305070213021b100603050312060a0506040b09040c0309050a02040f020d060320010513090c09090504080c011103 79
    0x2204d0001000926002154403168106046e000707420032480c410814215402513505440c107a4440005000041061140d0328036164240000c000b020f03d0229055100d007010b108a030b00015001640713000e03e10340380d0081c591700064246450030a0411503540aa0040b040c4002c0d111074410108503075072000000040d010301c3c0c1d01500da003a00c161443d41d00f229150301007242240c22050a000c030ba0044d40050000c0e0129280101c050050515a09441880c00881a00e8265403508094042000c2a404002c0703c0000340c86081c505129910003002c41c2d0803081941c000d9802c0000040c0000b0b5a4840401600520008032003e0100a0082d136086041c0c510400e009002070f001000c400c001407800343d12151144174805d00140c00d249140700680100c6506600070740c0c942e10380140e0300000c00882c21034904000b50034240241004101034086408924134003130f15006642d18030501041502601510004001c01e8406104600e058500b080300c036009103024103501c0d800e20503000c034603c09010035284504 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 393622679 1250 393621429 393621433
    0x815130f0506010809061902190e030c0102061501080c040f0b0d0e150c030402030a0209160201050c0f041a090d0c14042a0e090a0603050d020102040305031c14040501050a06060e03 79
    0x145850000945650800080700c0031940e0803c49107001b010300b27450703c00040d0070689034058849080d4040c1403e1031400803030f060441d00220b0800042c1a00701d0012504214280303000880759481e48401d12240c4a260843e00441911000c00581c03260071400500703c183c1e07810018040c203914482c5c0d0a540e034103404485518042d1200029000ba44084081d65010340028221050307036103540c0100324115025280d249880d41c0020841103060703024010180c11003208295540350a1007403600c2c849a0250780100e012206148208580c0202010149e1304c00d110000d02040c60040ca900d0a8103075000c613031003804080380945000c04000e02d0544941c1c80818420b10088100d00c0c012451013550300c4550f0300b990180090300906416503203034110034074030983c8281d4000030050b040d401c00070b103031180101000d4110b81c0100300030f200044002c429200000d2803a56100200d5900f50715100103000c1e507054449031128940100801d20005401040c05040d081c8402c01425440d200100c40c00c11001c400107401d9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 393623929 1250 393622679 393622681
    0x807032414010b0a230405011803120503060a08070801060303090504020a08073c2304030f080c0d020714030102040f030b0a02090603130507060f0f0815130f050601080906 75
    0x3900340c0b10000c00e0142505d15161090150070403004403c181e2184070a40a50000f182c184440c2d60003100c0c043c0ca403c0c1102859641078903654942d0b4503c03084d2000c007000c0001c04404201c03503850781140d5801510304641503803686521804d03468024a007611054000661000b400101e906240c400c03610310794655503440c04550b9502c002075400720399030600340840706591040181d058031014024003210707150540d000c0c10501c481100a12070101d0f2a0929440180303000c6605026040400700c07070460f5800011030358464818101801c0c140117450800003503014820089140310760224620040c4c0c1c11551080700080c2003041450700300c1c01540a0a0b0300800150b070240003052001c071040d80d020205100251504196001158007600305613101192256001c00032001c219013400004081c180714a41607401c60711048005100c2402201911300344000e01e00030403101014406041c010400203006c6980141d2100c1400004040501d94003024610342000f04010f0b40c03003131030000d000d906180300030101 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 393625179 1250 393623929 393623939
    0x5090d2609101118040c02070e07090e090d020d1d120a0f21080402090403030209030c151b0a020109030b07170a0209090a1e09020a080703241401 64
    0x14a003001c1d00d4200e0521400d000303110a10814081c082c40c40d290780100702e0301c8840300c5410705980c10304c82d0b000900c10742c144900c031032480358002009000c4138041d0102c101f05444411050f5200002a000355200360b20f03490400161a0000130687d480342000e90803038000035421f41c0300f02c41e07047c440700c18078400390718801141207540b03401d840c0740f080b840e00303441900c1002039290740d07810490300108421543c02c003000d00209407648032000640503088036410301114920b010342c0090300405004000078207050380414400f03442e46082044995001d000b401c2451040c0603400082015046000003840c1c030100d1002c60300801c0f00106503074100c1c0d036040e100e03019802c2c00c1d50345060308081d0080c6103a0070011128148138550140300402070062070320040060b03070380d038202040c031a2154000707001c500003508010307201c05440c901c01d8007811003047c0f948000905002070302c00102c40d001164081c910510800c0c00c08030600c030b80c0540360031007194003940351240d030741e44008200d00b82d8244405500c0c0c0040650700401c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 393626429 1250 393625179 393625247
    0x1020c031612050114010e0105100f0c03320c0d0c08070323030703020d05090a0f02040203090a0204091a09060c0a0f03060b27010512010b180307080105090d 69
    0x2c030344550008140420f101980c0380d01c0d00800d03807040710031111010041086091031070394000e01c00c0e050318140103628880301000c0e002005250008041140c4074060032000e40c044080e42c0720100035541166859008a11103146c40d400010402c01903004041004814600134601000e45642c4025524144400d9440c16585a0b0412001801d04d0450000e031200c0340000310011403007148961001a160b2400081e0359046402c01070461009521014184004c02c0c904103a00744803030303070455025a0302c1e519003514600388000840002c0d0040c5c1000740f0301c01002048070200e03c082d00710045a50044d52491111a511300040d202c1c074200c000708012084840d4070030300284501d0030a9080c04076140380c0d0340d80c041c1841d501c41410805800340f402c80a62162201e1031031a5000c80c800d103004c40c2000744809180383e00d18011f03c02c3d62503001d000501088008014050135003160001410345041c01c0d07948011074003030081110044082d014501e0010480ca000b0500b84440d8030030f101101c810382007600d071845 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 393627679 1250 393626429 393626459
    0xa1d041b032118081c0e10080406050a09030f030203271605030c0a1e1a0a0e0301090309090504150c0905040b030106050906060304060917070201020c0316 68
    0x412010000d4030100200e450320340b0301015481c0c100201c0900e00019000140381d221841e0034032160840c55901080401c9000442c58484070108032080600d0b050480c003524a48419100c164000f140c022964081030782200c3c03128030490180605024079668061848116584044000c0103e0156601d00390751600c00c3c4c0c05540d01c40701601c0d07000031359400c0d80d81244070b0130b15401c0d6442503940142030380120201140c0303580008150540c001c082980b42c21000960010f50f41c0074800c0e41d150102c10750401c65806c403080724014410308820fa01103001000040d035260b4020f403e480301244009501c9038241c20144500070400744c059803000880c508021061340503081c09801651948480a2480c001c6038640c807407902d0754240e603169010117030309e031006000994040600703d51080e407510340100100d0311140c090300d9100314100e5030075599543d1454400000c0c20f000001410300d456040c40803892441140050401034001d07000c079015074070060201036031180d20583c80c0b000301d0015981004900c02800d891 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 393628929 1250 393627679 393627713
    0x30804031412150117060303090d0c090c020706111605040507031e0203010503071409040813080714090f090a02010f03021c0b1c050d0804031709010b0a1d04 69
    0x462421020b52094100d01c1401d883e48110074902d0700855049603040560f07140398260fa0b122462641ca45500082e80364001c401155028038070941440c020840d0500501c00a0020302108001d049001d5070b000b940d411940c000c001c042615280c0d0b052034154000348003201c0200c4040064020380c148418003010309400b03489001896202c88802c0c8501b0312011030030440c581c04a400507101d41c5441d04141c604016540a02c451000200b440003c3e501d480302000e0b0300c90781004e407071956815010400b03105000b0960004045010303112000c0742180307000c1c0c6003119401080350031118139140c04c001d00c0c030180d5040c1c41c0145158404000d410041d4028501c0002d4a9410b0a0050030940c0120001682011141d03103c00f99a903182c200c0106407030590010700d034038590022001c2c03c68109580302030741c079611040410140f015940c0085e08042c030485003120034904051404c40b040c20310341ca6407800707441241c00141c416421008041200b00140100c07501c00304001700860243d84503030b03c51155039401c200c48 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 393630179 1250 393628929 393628967
    0x50d140a0318021c020306181b01020c030d02060f0a020c0c040c180909170a051b0705040c050a020105010506090f011b05010203010806090c180708070306180c0e0d03080403 76
    0x41203001d6500d881c60154203407948054000e50790400d00c100750410400900075800023003880c0e0020507048000640c450381d0512500c4042580316002c0050b46411260003616a1501c240d1707840080b01a400b0480c2409145805051401929414036860507409010354084a5501c1406a01a90b00e030541150110400701d040c10f03101846801c500b010480300940101c0d4516440d00d24074020070400458801b228180e01d042e460078413a203641d000780544210030440c5034220000c01e405840724000c0c04460700406005004002604042e24064081d4010202c0303d0059440d00d0000100c0d400d054048482c400c0000708500700e420384800054608c60306080310340815845501c00080002c0c2c0034401513028204010081100b45041c41465160a03662515240668103510062101c3d4001c420074980007071290900e04400d5840200c1107000f012298041d10008842d0303614065a0112540802d128039415980c540c00304441c5000d20101c011802e50040009100d5800030303000c02e1080c040540030704a8040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 393631429 1250 393630179 393630221
    0x91407090b0603070c14100209030c030c01080c070804051011250902160f0302070f060507050a1e1b05180103111011030c070906120b0103021002010209031603050d140a03 75
    0x2e03030b900c5c0031149801c40b11f901d540003440e2a01407808120000c2d20f20b41c1207000301484c2a08500080c202c150241180c500c80d8004100e2100300408541581e0142401030030444090641d064001e00070018504e11107100c0c00b5070a60008071501c841c2001d0044a5400001d001107440c004150009600c05414802d003015803511490000341c042e059070024034001e6000303104142c100741c407188000707202e60701030020b1005c10030040001900c0491026002c5030400ca501107003200e405c281d05201104e54000511506198003018000401c150a0340705884090351800c00d426100c40b06c03010311b41020b00010b8034440030503c91f6040c900d00a80801d001c8a16807401c01c00ca20780200311949560000441500c03d40c00c56581841041c1042c8502c100034110f124011059064685505d0044038041c00082c0c007814801d502c90302000d000b501100d10240c00902100c41030080d4a0019000c059035000c1103440b80520140d04450500c1140d0300d4807070707400d00c05030b040c903204603800254018041c04074500780e0049600 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 393632679 1250 393631429 393631463
    0xf14010e0a060501060f020303011211060405190602120f07060506060f0f090f0d0b0601180f0f051c20041b0309170a0509040e010b04091407090b0603070c 68
    0x44000c08201e4840e400208155060240140c21590280b02d40760440d4014001005004504040160001c0e046003960540082c5440400c50a01c6a60400e0341c02882c407a08060f0015a80303040700086600e9982a100c0c0c1c01c660450040f058810072107448409101800f444001ca889c03940b1140d0003220040161b89004640e000700b20352074208041250740420b000c60b52903140e0a0180c0d00b05848001155428078000690f030711400350800137090581000742907800b0840304505840703014042c1c0501d00d202529903644880b680c14410043c09868000d541e00c020301080702002800708a1103513880f085003603490b03da00c13908900c10a00c00d10907991003900c90409401420319092000c04001d090354010614211904086040d6000180b070011580401c20100d1300c503941c400709540c680e4400721030206012152a41c01c0d40984044525181d01c0f515006103803041000d20b07a40440b0103841c0f0300079108180e640d012000121000380448642100c8204002a00300d88145081490540704480c1041749000301 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 393633929 1250 393632679 393632683
    0x30b0a0b040e060d0209040b150a05060a0f090f090b030c060f16080708130806070206070203040614040305030406081b09010207060302031806040309050a0b03010f0302040b120109030c110402070f14010e 89
    0x41d142a5009007508c01808503c3e41c0c9241b00c41000b00082d655200c05c5031911020034858807490310304900b017054006060084520a0000380014281944400030568a912840b8000c0000c1c04440c1c2c403d10486104108900703141066030400740340e00040c24103040102506201b907419540341226140320400001c00056142c4001c3d00d0030b4100d80d1003140b001400c1210103807070854003030044800d5500c0310081100700c41d4000111420759881346000101c0400c5580c84100d00c7c010b6400c02840d90002042c04503095134070400c0c09104d0001c1c051004802c03100b0445c030002c503200740c161142c0181c102c56412711181e8003a400843c0c000040303044c08600814854452401e040040e1000c40000d181c0103410400c5217861b0300c00c40042c1680069080c510352418a101c1c0107031001d44002400303a500c40e1101d2007180e580f2040113a40c042440300134880c01d00d440c5401802844018022101500d02541c00380040c1400e10a90303914540c8a460200c502041d52969102d200b1400e80c0140c0310342d200d10490303420442c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 393635179 1250 393633929 393633931
    0x20307140c0a0902090d2402180307050d0804140f040c21060608011208040806130204060b09090a0e010e010e100615050d091a090d030b0a0b040e060d0209 68
    0x3a002400c481c40e19042089100c1041c0d0b8840c2054600500046910741c1e06d11301e0010005038007162080000480c00040140701410b00742d68100d0030310104030402850b9a03000c024000c91030450503503d00c00c1c1c0781c0041141a05054102402481041c002400312280e40a80300400420040550501480803000101a5002d0307107052400104450003a082c080c801380400c4481a000c204180211420304c1401002e0070814480da080c01828038110205210031402100c0240c0b03e4803007603c0c21807038103104c42c140c000c032032040890241e440c1c102c0002d04600110140d4207420001044c1e1401512000d403200090940201c0a8481c2d55883c024000d030803409114950711596401c025007038a40c200070011084903c0c0b94007045440096031124000c05900c14115410081e2801000612400a044c2020990880030312107403406150020b00171000320002d911070305070803995411303c000e00712001481036003030461107181030a8030180403d22030a9046103404ea80001e0280c414003071150290001031081038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 393636429 1250 393635179 393635213
    0x50615060d1112010f051003020f0d1407180303051614010501060c0605060907050a0507210905090a06050f0616082212020102030d0209030a0b040b10050a180b01020307 74
    0x1400990f40010b24102400b8900400718440300459061038100410344041b035420b2903804066000820a00142007442981c4224070307100c10401440c68000d2540c3c20920054440302c001c00c0040308507200307030a0501281e80550340d2661700c0c582050030180340b8a18905d00c480b011644c0790302c0b010000300d511609214560003010a03a4583c0d8007800b050805c00700700c3d40d014285c030f400b50044204201c02160004122500b0005c1440c0071943e0f03400c03034141110005103200907540c03c0c030302080b0660902170340580c112058420444280960703440c0c0d54580300440b0064425580c20800301c143e8800c0501d00940608000703000e40c4100d2075a100340e0342d10000036a01200e19840140d00c528804542c5035415030440e006881c0d03d0001ca10301c1c0b2000e0b00040c0d681d000b00c4542c0303003000d42c0008421100761003d0041488195000310001114101071030030035807000045540d1a5a140c600b00005841d00d0400d40c1102269000250300d01c014400c2c1d0041400b0f0802c2a00a60641c802044458005034503080002c203030702 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 393637679 1250 393636429 393636461
    0x5070506190c05160f031b050604030f05070507030201110f06090a030906090815060f09040605070806040902150f040e0403050405090c0304111009120303020306041503050615060d 79
    0x72201c0d03200300480d41050604001c0240510600c4401003034040140b20141c1c10145100b0031411a1038101c80c00040141245130b0105090750310310812030001811801a2300c0303521110b04e00c0b0450001150b042c000c010b8064541d81c407440040000d9405135084440000c1154181c440001d26141c42c2890480c094401d000107a2020300c204052581c8052a030029058030f140218445140024003640e51203030715081a000144c18000c228207070350f288880014110060b003d5600c038034041c00c1100c02031004660304c03000300e8052400511146000d2007046611a4028400d40d011000b02903a02c1203608400050561840204008220b5000c4058428030a81c131a0344c540755100c0c00c2c002440480c1c83e029103103119109045c41400001801080910b0008030159800a5514549281161420416032200078000c1e81c02c0d03507500a240d030640080d803003000140e07014000542e14584d03528003640c2074800a40240c0200012131048080300501282c100b00c02071440f8100f05948080700110f403821145407600c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 393638929 1250 393637679 393637711
    0xe0f0d030e03150f0a0c180305060601030e07080d0c2306070f03060b070f02040f0c120e0615060a0207270513050c0111070b030f06211b0105070506 65
    0x40c50300700b03c1c41d2882100000e6603412810700702c13040084108050000c20010740c60301e0800714910310840070380500c110b0301c0010490150341e0303017002a11803a040d5545400030b410b22540c0140d0b8070000034a08115040c05000740864a42150f046a030b07101c0c2d0200c100c03440f18074126540400012210445047c0740208040c00213414414400341413400350028a20525041110400038901b02c0707001d48240c540c01811001602d81640700080007420310202c41c825281ca480105a01d00c1da00040c030012164488000f00302aa01c01144150349a4085603002e07102c11f40c41c0110281420a080a4020800540103d5081076102c00d640b040680c22107501e2102401c0da43c0418103402c0c03481c0202504901f2000344101c200b00140c81c0d0f00c1d2522042071981c3d045c08000b00300d000442e0401c12170b0340d0080c8000081541c9a00307201c55078912065007621042e2213100e2000058aa080746182c00103090b0182c0e100070008258850785802c00d91a03d21a064103219050020b07202064007801010b00c11a0310301809145 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 393640179 1250 393638929 393638957
    0xd03020702120607030221061c1515080705031c0507021903080702041d070504051012080406140f0301050405040c03140109060c050f040b0f1b06041217070e0f0d03 72
    0x2410340d0b4a4000665800042c0501c0a9512800507039449c0108030510035211415508200115400704d10405019614140c503812400700b07162005010749883c442500c0c0502ea4910402d6500ea04010780d802d14240041203620b4418000e030001e040c0306101501086c0c860980c0c81c5288036000507640159440390300010404110700d8a84034a120385281c0e8200080d4a404992040d030340d44485000b41c40c011640c400c0461151500e0308840e40040414900d0107201c41c5040c501180503410920401e000310703d407440b00c10400341c0407000351000004c4042d000c1741941c0ca0442013102500c0040d0090390b61101291020001c80c0303420010718447d408200000c6207002c1c1c1440c1650807243c00102c2d83c0c003088030038400c1d80070050140d4201d43c00c03121588103042d1126001e00c035000441c814100120105142b969600c00500e901140a030310681c012081a2241d20400720203850b04503800305448142c0580c0000a26440c0c050f0005040a54014000803001e24040c000302e07d0f0314494480640c08190700c402061a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 393641429 1250 393640179 393640207
    0xf0a3002120114011508180f010c050d0606030b062713020c060106080c070303050a1b1805030102130b0310030c170601050409031704210503091606020d030207021206070302 76
    0x10052003116003c1e5040c0c6401c440c014030130364011f00340d600d604404c9501c805015100f00800358241081e076008004160390032102030195801010030010250505400103a06400707403040c1140c1100107045a4506441500d1031030581140030324003190301990015100e215113a030303004811848881a001a603e01e02000030501c0d12005034451400c0040303280802580c2d40c0040f0a075280203a00d8240450b5944850680002038024041c00094040031502c040904a030b0200070b030125003071049060311809845a051500703038170400c0d0200c641840030072001c2121040040c015030303002070309003038140f00f854a0399550105440d1a9100303058120b80e40059000e10501489180c2c0186400c071003c00942002c1d580c060b0207140340784080b060395a070a000260038004c0b200c0c2c40c1ca1810214003c0905000b24014000d4080d400541d110002441000c00001c001d0405e0b646400607a07495230010004a01507100850180d03000e0201280c00403d07020f442500d00e90100b050a00420480d10b0250b11800350b804404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 393642679 1250 393641429 393641431
    0x80702150f2509091a03061e0f040206040b0a18080102040612180b04021809061005062d04031406060f06040b120a0e19020f0a3002120114 61
    0x42c5100c070b05140d00012280c0000c0307001c08682101e800400d01050b0748400310b4508154411040d010301640c802c2019103d000c629400e00c0c8440c50070600a00e84612943c41202e40c400c60b0000c2d0080c41c01c010902c401000b24016204400c00c0b490030700340900d00e45807070b9105104e95074042c1c202607401107801d204503030300507500c2045808408410402c2d4038181482079001001843d001d4032013913800c0301042c10342d20340c0c02a000c600c6c1d102c00c0b940c800c00c0c203009518079620300e02113428180d50b0b00d103203002103081c1ca4414101d60f132941030b0540f200c0d4151503034528040c081d407001c0410110f49404110000014401145506411207884040d088500d8417205000f00500d0f00003140784200400c1006010180c000001c0ea007070f80c40003c0d08500159107407841c0c80000d020f403011140c107500ca48600e584011013180002c0d0801482560b207a58007400303c00c20301ca0122a68041e241e0b12005450f07001e03440408074410302511602243c440e05030b407015a00418070031000d8070b01000141c1d440c0d29030071388800c888190003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 393643929 1250 393642679 393642721
    0x8010f0902091302091c0309150e010e0f03011508150c1c02070305090d0f0c06140703110a0b10080d0c0b24061603020105101203080702150f 62
    0x6514002c424070000c1c403c1c500480105805641c0030641e0303425615036200e80300406414813031000070505e0074100682402c0f22441021070307070004030300000c014074030503c0b0a21661106071a01c2d03015800b100f040110314001201c21036015035954424052561840706032200410b8010050144486482484003040e0b100070081c008415007080180a03150003900582ca001140300001600d464151408603031a214100050764070620300d00700794003031240043c40f084641c1e208070300f40c64520341e8030881500c0600440500b401d00c1141808404042401400010344880c083c00c15146404940c1c1d071800240402a02c6640c01300e003003041c0500c6000001c0244600381c1106050049500503182c0c0c1d801c0c00a5001080c100c18170b60f221640300c2e18031503029a12107882d040241142d4440c1c0320000841d4184a26110907401982808082406071280721210350aa41e8440408106d114180e24180c50100d409010081141729130b050007414803041c10316081c001d03880c0049c4440c060402d01d0000310302103600703141 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 393645179 1250 393643929 393643931
    0x5190b030c0d0b040c080303150f0901060503060d0312020f120c04080307170702151c061508040314131502010c0207090b0d0c03050607261f080a0308010f09 69
    0x18400d05542e20440384080c60340c000d90003940790f030701d40c07820240c04007070b0358407201280c40013006006000381c0904200c2000401070b1030200310fa110510800141c04420701ca00c1c00425405c001213005800e002016410301ca029090100d09140d0100c1800c5c100c3e0b20408003030b04e9698000c51095242c0d95400059030b00513280ca500c2904140c201410345480344a0098000c1603003e00201404222080a00395045540c00074000c442d06501a0042c0080354010034004070000800d000d00c518006140c030506050700c0140d5020a00b00103054826140d0810140c17040d0140500121003030324400c40840100700d40310300140c40d0b140c101d1516411040d19098109030030150390520041e036079440d5001485a0860344400404a180d40360b1f200440c0d0401e0006c90090841c0f00803540c0442840000521035003e04200c0d6210010407450145541401d04801e10f0210159801c0c804111341e09902507000d0701ca08814040c0c1d401c0940d46218007841c5c10441d0a0403008101c0070401000001c1c005072100000302a5400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 393646429 1250 393645179 393645193
    0xf10050105040b0307030b120607030911030f1b0105040b0c0c03070b160f03050d020f041707150f1808010b030c040507020a0b18010518120f030a0f090605190b03 71
    0x1c408091808000c003207001b00340d40c42c240030320590b4a17141403c2d100450740c0c09030f40c07507810004d80040240510350030a0300d050101410106042c10000765103005181010301a21292168003106c40d10760b1007100c100b03410007405100110f030302c044040c01440603179003d4008003808600c981c249401c00c40d00e03510101403d41c0500000c0414044c056030420703102c1d03110200c003000d42c40914059449005140804060074404151402c40b001a40003c00c151010301810030112810100381558138201c0340540714144800002110700203001e008090360044c958100490b40424419104440680951000700385039100d80c00b802003400c3c144a031030528201a10103102902e003075000a90b565480b540001c3c80c94905000003660b606a010003408a4440701c0b00034001801c01100e0781d06000c044088140c20b0313001c2c45e60401da90183e0401128550b020040b400d50441e520600701d00c00030306403400390711001c54480034a000012894801c66103c0d14411003407090320703541803101310100d5142c0c40302c880c041c0d40700c42 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 393647679 1250 393646429 393646439
    0xe15010507020f042d050606040f061202092d0a0f06050d0b060403030207060923090406020705010c050406120203090307020f0607060c05040e1609031b0e0f1005010504 74
    0x30301229620764054504150303490301d540c00325004005040080100e054150329844000d2149502c1e52600004802c00380204d8030b8240c20440f8601c2244203201d400000420204070442c000c001d180c1c0400c003a03080040c00c0010640208401050500c41c00c07180200c2e501081c8042400d40c00c0c54440b01b101551072000482c1000d154030070a08941c0a04000d00101040a90945907542c02c491a00c2c1d10160410340c440ea920b14001c0d680704464028400450360f4140003040d91483e04031841e04121402104003150b2000f2000d1052804002c4c00a4070341680800488010500900801380000d10345d50325142e4803031511070b00420074480c84d66a01e2995004000b80302a040000095550307582e01190110b04070310101000810074429080c0050000b400c20041110143e0020301500071103484c8852500c0707035984c07524503503200c0f902c1c0000319000c5810f10340b09001154144044180d00f121040181c4262500d030030581080070400c1f41d011409007510030802c1080c407000c402400c02000282015810725080c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 393648929 1250 393647679 393647687
    0x30c0c12080c1303050303040303051605070f0c121b060c2402041805090d030606021902030f011802120109020d060b040227030f0d0504181407090e1501 67
    0x10440340820040302030301040211280000b01d40802031071248141d5510740d20710346242c5940048a0941c0440d18000006164410700c505a04014026680c0d40d403900c00325a41d02694043c91120070744091240203030204840c4440501c40c0c2d4464082c103c880d0400130049a41c0400301d003e900030000304282c03011010009042c11040031203c1c8800709202094041041d0880000d0245074820394000e840d01c0c511701c5c03401100d40e0043e13000d00701d090107481c0110411042502070b07640034800d9500692041291090301c051006c2618072840c8024103a07281045546c06003420b6230001c000011440d045001e0741c10440c1781c9880d03040e20481c1a44000d018040043e0000741c141d0403800c2024041c5500c5050800031a174482e8101e855064080752014860320707901d60344454510030381c9800c0b4064820801c060312054000207a026070020b0540d603131403506080001e5000d484c65507150f542070581d1101240d0f8030300c6481d0b00a40703208080654403050064035121000c05019400b500d40c10304004440074005150340c0c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 393650179 1250 393648929 393648953
    0x9120c0112020f0f070c0f050409080a0806030a0c090605031509030a05181c300c03020715230301050a150e0a0b1309050903220b030c0a030c0c 63
    0x2501a005860315509940c0c80090312404c244075070030800000b04c2e0310030030107407a1101c01600c0464072144d00c041d0b12413052101300ea041c80c00240c00500140302c240400b502c900c400a504c03e0000c2c064411300c4c801c030f644510b42000d03241c0201003ea40c42c1c1205204074241004031105412450b440d141c803506240c09803a440740314210700f0780b042200008800244144181c40d0746041903018242d13a800015904a01040b020303440700c02c49007156a11356140c1d13039071180b00010506910003a00c0c0085a10350150999124500e0b1100300e056014109001808060488040030b480c01c0c0d60300d83c1c681c0d0311810b20140d0b0f508c00201402164680c0140300521242d26404228000e6800c0450703c1c0343e103a0303216001a261406040440c950010741140007088480048018016841e451042c44000c25110b10000c000d0f00e500302d0311040c82d50300502c40c3c01084401d103840511b142103e00600800b268462001c440c5607442242d046212950000c2d01c640180d03130611034090703044d41a14028400c0010b590f240c54900300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 393651429 1250 393650179 393650207
    0x15040b03011e0c0c152a0807030b0f040204090c11061b030c0d0e1605010203040501121d0304120209160c060504030306080a050708070504200a020c0907030209120c01 73
    0x9942c03c01800f503d13004903000c08046030440302c0280d20940c2511a18003500740040b0700485848141914080d28604882010f088215a00c0740d072425512002e04400400c90350b014039902842124a10005859501c001e10141c28846808070340e0803125800540320074060300e03000c1c1c15544407000300001002d0580d5103981e00505800c5447c0c0d070340c403064900055401000d04d0382d0081032a000324052112030018100d0f11140c030a402e24801c1c3c566400040e610b034003d521806011640303c5004540c00710780d550126075900505414034414442803025589560460340000c100080300d40326000c19490039070500c1c0c5d0301c045202c2480a410004250080445004000041c0059100d40104003058080e070081d0000d42424001c64100040c54103109a5234055841103120310300440c00c0c00700301400c15000c0c0261910311003180d00c60b030001c400800c294503844100c10704214000c00341e00240680d250032600740036000a40e00580c0701c60300c40381002840846840310000542c041031308001c403641c1140c4d007404058 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 393652679 1250 393651429 393651431
    0x709020315040212060a0608102105060708040c120f080c100510060809031201052e0908010e011a1c0f0506071706180a020d0515040b03011e 62
    0x103241c0c0c080c0881c11a0000c90700c6584140003040c1010390140e1851680c1c1304000403134079051029510074040e240d501c0e040e02c1d50040703418110800d110010170007034180b00906e001949201c441450741c84043c21302e0fa0a480020000c0c60b04410b00c4140005030760030101070420303010042c01c442c44640e034000741e0800456004001907404039620400c800c09000300329541d101885d0134030541c50301403188118211540142c2c40450504004030351045c0c00001510031007400a041c40d40b481c2d00306070811850b1080c0c3c080004021070108900b440c0540074528441e0010020b4480c0800039051100c410700796030b500381a039481a80740419442c07005203508100c02d1801d90030f0310206414204690341c580d1403024160050400e1104065180421100060303292103180070b691400d400b0300c1903003000d8030301d0482981d610358000c400030b0102c0d514502c920841608035643c28801482c01401500300020344004607015008a0708281840348181080e008940050794200c008129810f10003407509080405041800152 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 393653929 1250 393652679 393652681
    0x801060f1701030b0a0c050c07030b0c1c09020f010f090302090a061a0307020c0d030905060d0b030f010f0609021204150e0a060605030d09030308040308190c0c0b0f01050307090203 79
    0x14a000d901200c1c418020300d18219000e686900b1306125000040d07406100041c0761112050542e8483c1050310078004046018201d01c51440d20340c0303940160080c240c82c4002000304105030000c0e00800c004013443c140300030701090303040d8540100446131311404441d40c180401c004200d00d00c039500c401c0001c180c0f030b4102c58a00d5a40c607110124002024182c2020707075141a00c0349045c002c0c2c2015009948030700100c0e0300700d80c60714410f04240071450f46c0d00c1c10000d012031182c0805021030724246018046541480f0b000058014030080003900e002c54050003d04035954410010340c00841303500070000a050700301c00562802c070082c12080c01c08200100042c00041a102d0a0380200c1c031705420019115040500701e0300068001c1c20300100524443c81164070a114200400048034000c9148038112600b54031003060f5584c850302c003070300c014a00030680440075200c000061400507240c42003c2d4241c19940e20050300700304924090b440710300d0141c0b600c040002d8810041095603000180c00065500e000320150701d03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 393655179 1250 393653929 393653957
    0x3206040f020d0f0911040219080a02070b041101110c1e040b03030403030527150a02070b03010801021e0424032904290f03070b0d020406020d050a080106 67
    0x34002c5800000805003032040c0081c006086402c071040c1c0c1c0d80168040000200c5003400c11049109480c080e10300008185880e102d11800780524640c01015844050b15001c0c4541d10741d6800300d0111021107900c4240c3c000340c0c1055a00800c00280300e101c2400400000402c04001600b020721000d040145400660005c101038645400c4042c11000260850307442e15228034000d405a0000702180c5200c02d8820f243e18100905003021012900c00a001d981610301004948810340d4802070b100010340c0302d1000d001480025080c0154000c1001c42d00041e1601c0310701901e00200d129002c021f03010040240301c1030000c8183d24503a0848144000c20226070381030100826000b91843c00c2c0c54002034001c3c01030070003e04901c01698584008102c40c20800391010400510101c51180c000c1164001295240c5602d400c022500d104010001402c89451660f03d42140405511060420386100e802003070400001d0340420107420000d4003401d1482c00c040090500601a4005224520030400040d1042c15 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 393656429 1250 393655179 393655181
    0x90c1e0a0f0905180c1302070206070506090f190b06042f090a09050f0621030f07060c0f0804110f061303050c010507020a150e0d03033206040f 63
    0x80103080d200c4610324502c0d50342c580b09000300b0003182e2007442c00e084614080b50b100d40104403240c202600500c0c180640d240c2e2803445000390050740040f0780041e001c011101c0810401c20000744241001c000170400c90401c00c0050b800e204c5084403100721842405589000911600040f6130f211a06a81c002041c0f044201002c3c00703101181e8280c042c0d0405d940b000f13400030804c1001000d12220580d40c4c0340e203850b43c0345042c000320780007105c40c00c885544060200b800392a18400c0b8100324000c0d01c040040701e6564422240c1103901081c90b0660814000420500300b0585009610006116003000d514a4203003034405081c040c40140000c200220800700c551003607480c10954011400003426160705e405580302d24504442d490b0006549502c2018800d02c40c0d503203d0300c00c0b508a10b034007404940400b45000c1c07030780110014443ca8502805664880e0301c1c0399484000806079007a007c0c0c0c2d40446d003d08030300110007031060307000d24031008038007000000d070100c3e4440c241041c0c04c20816200000c0d0040010305044c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 393657679 1250 393656429 393656449
    0x2030c090d050f0d0f05160503090a0e0108010b0102030c0d08041a01030b04060e010e0705091003140d091d04031b0803100503060c0a141315110105090c1e 68
    0xa03484a500e074070250601078001804124a045031080b2942c6001802040e503a104e03242c5000c0d00002c10800c2800c101801e4291448006481a000c03681410a140002a04003400343c0200404044540040007846824056584080802c0c0042e514040c035010f04603842e14608003030740051003400e1001c14108100d50101071f011180003101e5190075616460300c0c0c440500306032000e562140c00c015801c0c0d40b100041c4102d180c10070040c001403864501d06814403841801c02042c0382c100c401c6910000000c41c2c0c071a0806405011042c0c0a40080d0b1001500078000380903603040400c138840d02081c000b00003c0b004c0081b036041601420205102000b9500381e100c00c0d1442d542c000e059000110a01c40302a80d41194a41a140100d0903207003950756030b440404a50080e9040d02000a4802410b1401d45030f0b080b000b4216004000c0d0100882500e604e01c8101c015a02a500300014406600f505460070b828803c0711b41001c1001d011b070003024100000158440e00d81410014590741e0808071207040e03070340c0b40f41d01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 393658929 1250 393657679 393657697
    0x105032703030a020a0e0a080d030c0509040606020c15040521010902120f0d020c06030406020306011e0c060f05162a050109021207030c0b030403050c1501031401020a05070602030c 79
    0x1260741c0d1030110b031103c0c0079400c20030030364000c165900c0d005412483c11140d900141ea900c04d0040410101110040f40542003051054080c1324080000c101c04c0d80300c5000340800f03403145070010a01c0200f40001e010120343c1c80f40f003104203584184002e0113140c0e21074002385010b410f03520840c000041c5030f126003401400d8610f402548134031000a00a041400401c6188101c0300c60b0702959100e15404005130303210030242d92400d500038410400140000c0007a8003460b082041850311810b101c040940800a001c451603100c00402c0c000c2e091a001c01006014014030079030100405c0c001030612101d001002c500030100700c01400200032443c01e888001851100500307200300303200009080c681c20036900030010400241d009120f00418480320f04c0c1e00040000407203034401c6a0b6250302c2d1a00c04012450341000d03000300d0401008102c0c0940f00b1800300302803204820a0000500c065142d4904800310810940180c22140d005000c5215541d0300700341a11061604640c003d0798903510500c8040c8244508605 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 393660179 1250 393658929 393658933
    0x609080903030d0e060a0605061b150a05041101050c1504020112020711120105161107090203090609070501030618270f120302090901050d02010c060612051b01050327 73
    0x1110400d00c3e640d07000b01000807850000d452903511408241e600fa6406402150f0f0040010408404035402c6005000d00d1147c2500c1902d80d107a000c015200310150302030324a03100164403641070106001074411400e000200034240f80d803404000000381501c07005043c00c0c900020407107800040030340e4090103128501e410f41c032400315500d11140c6001c9094a07041070100b8018050035040b032081120510a20b4001e10740c21440701840401e0035000c8902d01215010203015004503200066601e0460014500600291018000ca840c20014851412015a110904060404804000c4510f540818440c0042d600c0f00c0481c001032480c010b04a84281940005034095160401c503060003250310141103400e2158490000005400d0001c900741c2c081c20982e00d61141221004000c1803401d003030352458062042c104950f2100c01ca48901c021180d00f5800000403000201d000d1080200c10b1145a64245184500e07050300c10300440024503901004000403080b080e100d01c41d03070045c00c0100d13414080c21100c0013 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 393661429 1250 393660179 393660187
    0xf330403170415181406010e01030209070c1a041a070503310807030f0302030103050309010e03011d06060f01230c0a0501091b080c0907030c03060825060f020307060908090303 77
    0x48862134209600409440240340c681d0400e184c0400800c04a04031402094030084076400c6408200c10340e40301428030401c1c0445491004001503103854803850300700e0f00b00701403921781c13030513003040b402d4081d6040e6a404642c9101c0104115160028140ca4000c071108018501c0003140b00da0130300d0510b41d8030502d40c0200f03064100420030002c0020040080601c240d179401e0098012240540a13400300b804018011340091100204952041e0b040710740850008001158200802004902032003070b00017045513030740107207041048038240503018100e801020b00e40166156601d03401c1040300070100800d07101a000000361800b02c413104100500886070810000c1103002c40503e80300c014500b8000c0e4901c20698440c1c400100e80401080803a00c2400c050520f40c0245d56082c01180244014050b000905541d41c0f030209044070100003020401c031500210350070103101c451080300190040c0c1d02a100700445130b207160750300310350200544603902d52254010500d5505442c00c85280e01410200d544c15101c081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 393662679 1250 393661429 393661451
    0x2d030c0a23060108070303090509090d180e04050105060108090a020d0f11060a020106060f140a030c050f0a0e09160906050702030307060f0203101502070608090f330403170415 77
    0x4030b03a12085074400e485080b00c0aa907001884240d10040700d02010a330001d2499404450140009a015045448921400d078bc0c0b20f082503020700d20240d03402d8641381c0d074030401c02109507003100000f608801e0b1200104414806540002c0c188501307400c00826141c1210048000c0185c2d031404106443d4004026603211244954020b00070034035071044800080000c070300790b03080a01560260425106d05024180ba020340c1020542c0540300107041c4104000007040502c150072110000740c033b45103450b80d4a4601c0d00c0b41040400c00c21910152201c421501c1058210003040e8101c2100c2003212041d04129480e41c46034000030b811340c0201c2c40e020b440c140c02c02020035410b4201c2e5006600ca403228094203c0c2880d26100c1080400e11075003011000340e8000d81d81031101074000c02065038001c00400844514070500000c86041c03290b40344100a00300307001d5581c0200b4900701842651509003c0c0441c000526141d1801000d41e4180c4081070301ca04203a001140500c282c0e02148856600758030403c1c054901c0c1b02d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 393663929 1250 393662679 393662683
    0x150917250521030f0c160605270a03120e0306220308090f060a050402010828110405030106091509090804051003020c070b0a0f08010510031d2d030c0a23060108 70
    0x2079200140d43d0480d0381e01190050061003624608107905800fa2070102c0035004192160311042450341c2e0040ac03501d000030000769612240c8030403128540d101c0e41d41d010f04009062a042d0003800c00500e03d02d201e2981005104071200b04400550940b40821071070f02c806d058142448420041c0008038050a4101b10701989142c1145004070b10070b0f41c1e500030344c2d81d60308411142d0340c0c100030481c80400350712800c403000c2c2c3c4c070603820042410501200042c509070fa1440042c1c2142c45660085012644034003d40c400328058240b11001001841070038004815503650341e81d0503106502500c3c2c4103507941c583c1005454400c4d410790b20302940310402c0b10340203a107680d04600c00d42c000134050340c000740010401c000c1c00b901c80d01d82c1504841c40601941e1601e400040150058058290b80402201206002c0216400200184484545401c407810301ca40105081031503030201019003ca040c0d031042000c1080442c00040c0320f80b0841d04850170404441d1410103900f0403c203007085150320b0744106800071808007c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 393665179 1250 393663929 393663943
    0xd1a09010203180f100515211204030f0b0a09050313050906041a0d031e0f020c0108060f01140d060e160c0201020601150917250521030f0c 61
    0xc081400040e07190701005041d0341c2c0800c50081003060300101c5d1808549000e680110350080d00c101841030304213440e00d0109540d200362a5440355400641c500c2540242014410032650314901d2419a14150458607403060120a07071100a040e0f07881c1c1800160b9040703807913111060351581704041d02d5940d20b0780c2d50480300100740f6000320751007054100086001c40c5843e00c140550349000c2d01045051000c4070040080c1981d00e90b900350203010005030300c420740d03042c080320710440c2c034200741c844860401e00404000e1400e0000212107052140007400d0021b076a481605140a50009107081c2d100340c40808401400f6001314400048558180b10020030210036401100e885080700121107401100c0304070048030000b8425001a0250708800d00610150b102d400a0075603807211410709900c05071341ca84e03a82020340603a12002c440e030b8006161041a00e160301c4061400c14407504481e18805003020000b03605414803a65040b0600e1020254050445003030041da08205052610262100903030020241c8840f1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 393666429 1250 393665179 393665191
    0x1e1206051206062107090b040b0301020a0903030f0c08120a09140d03140f04080d0e060c071202011104292a0303221b061d010203030103050307020d1a09010203 70
    0x480c00914103409990881d102c43c0c0c4035256001845c00e240345c02e100724003e08201c40ca03140c12903101e0b15241c7d5281c500740000c09000985a8452800d1481c50400401200c1810401c0c2e0400512500e0030003c02e8070182580c0c04403072a00c1d100301540d12075021020003000880401091342e481b018910800c0d0401041d1040c0340d0499403814850a148100d4281081000f2102d404a21442c40302103000b080400c4043c1c1600c0071402c2002904802d40e002d420302e0908101ea00c14110070000840034104036100c40b808070300542c140003d11074070b420710f580c01584d03004500400d501c1031000a000c4402d140f00e0142500104480c180032651181c442c0204082e06282c1440c450ac1c2c0c0c13000c10800c0034019000411a840340014504400078900c2244040c06110030b400000c1d10018510141d03102190b07204120307400101042d85803800c0c504269400c66441d110058005410b5400078401040170800c08400ca49075190b048400c4c020664070b503d4100b20301041000c07413203928807500d010401000e40560095001308 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 393667679 1250 393666429 393666439
    0x5070b0106082202030706080c0d0e0105011a0a093501050901150b090d060b03060f060307050a1202091e01140a050a061b06020f070b0402101e120605120606 69
    0x195080504030a41207402c0c40c002d4050b840031401f000168423403d6695046001c0301017191400c40701c2c9103120252608016400d0180c0d54560042010a50030b08440a00b0b00c9800c080b20b003070480000001c3c0c181891886020007010303c48601a060814460700d0140d00311100b000a030a074010380000c6070080504450341c8507103600c1c2501351540c0c41016441041100c3d98450810324014203007013403203a200303d010401c6440f02c0c0c5030042041c05650520115125040c64006040c01c0e107000000c140c5410081e1b440b1501500b00c0c60803c0c03120513800c440c18111280c050f901d070310301e903103a00702605013507004280041c035807114806c0085103180c01c9407146501c03402d0031501c1c0300d4142d032140c0411410350518403500d4080f801c84d900320002c0343d080400700003196004403030042c14684da0110341e101c0c80c1e200450071500000c0140810046291021081a4602c641d1a08044200003810795045c0442c1b445070900c00d12098654402c18985c1c19040b10000c0e00b80500701d80c41c41002c92200d039035034510070b0b15014032403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 393668929 1250 393667679 393667711
    0x1181103060711100c0311030f0402010806090621190804090f05010501080718031b0314070308030f04050f0706050406021c0f0525080901080c13051005070b010608 72
    0x71880340100d0341c080e41112025044c0b03070403090308030f40041c04a54248003d16032658800070806c40d03080040c1d84180402d0304a90110700d401d100040254400400742d5204450040601510303440702d400b00d8202042554081994651a41029160003000a091541560340341840b2041242610103030003221116503062010030f0718000c08105540090041c40d0028401000003200144110b400c842103070324030b010042e211512500c40b5106200380b40113049003110642e500300100405496404600590b4802070300c0303013a0550396508041e1101030110070301c0b03285d10400710703052005c244426400c1429003c120b8420a03501c0030701034110741040c400c42015000340c0459200f030301800111381390480541c0d41d5560044402d40d4095a4940001506440b011240c0714802034040b0303c410040c859900405030036848150000c0010065030000340184400030043c0150985c900c10798503a4019194100d505100c4101019000c4465010310b4401800d2820329900000b01107410402c5c4030700800d4069051250 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 393670179 1250 393668929 393668941
    0xa020d020a020904030c030521060a0902120103020d0c08010203014a090102090310061a1e0a0c0203011b0807091a030c19030b0a0e090309010f020118110306 69
    0x1035a501d400041d4000c03000100003000203209022940c40144282883e5040c06020042d0f80400d00c0f80b081d4820480231480207000540c980314240800800d4031f074200f58641600b1a040d90403020040c40000e00454942d840c003810001186920000341c03203910000c64903981d4941140020040300d4032000130310310b025051a001120612080c5140362014240410301040c01c181c40019a0700091421701207540c01e104c2440296020300001c0c20094400901141880c10a151811034100300301102844030030402842146a8021405203801d020048074103407600d60041040e01c200802c044000c0d490b500c0d102d204041f01e0f9034038004200300b000e903580d45241c82d41c3e8000241e450b040b050041c04403408603180f82403041d07101e0030000c55002401c018818140404200d40c03035841120848a0b4020989031b5a07118120b0811116020042c41c142210f4600303414255940c1e40c891040f41d00c81410091900c03905490a4000d4201c1c1c1034591801e50400e1501c104c90409980c0c5425013029030f8441d02660010810b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 393671429 1250 393670179 393670183
    0xa261b1e0d031508060f0606040807030f0210020610060513030c0e0f0f06030a06020702030f030a02071518061209080d1e0e0304051908030403060e2a010c030c02060f0a020d02 77
    0x2520050130040c142501c0308048a10101001008260301c41020000401c20000c14000c020045200701034141c4000341e203204204031250b40e20074440465000c00b042105440300400e0701d10440f005420101d0f518003111190609002480c8c00250030301349074400c00164100e400110320300c14000b20004900c40d132030311980903144040c02e589065240d4000490f180c041541a030007004468030080440c4c1081140005a40c01d42c9c0040b0000340143c0c20051080020841980c040c121064091500b100700454104c64800032000f81c0c09800100301c4143c8407003920351815030000ca0881e03004002141c4480f0381a0b401d501600c101d0541c4910a205101051004069405041d030401407040c043c42c00c050410051000300c1e540224090a90300b002440029582014402000614010000450150001c0b1041442c00c00040c01841d010120000c070070701c4043c9800e1341c401d068602441c010807142c0c00d07030a08407000500458083d5124400081583c100c0507000010507200c1c42a80075205c806040c11420b036 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 393672679 1250 393671429 393671471
    0x1020f010506130b031c170109050115050703050d061701060b0306090408090d08070f0308150a060f0203250501060e0408090f060c06090a261b1e0d03 66
    0x2a801c082c00c030f0782c0350f2485411600b001c038103008064211a40d070140d00c0364080c1d600f200d1244e210003240c407071045000445841404680035040031030050210b54501004001807041d2a8554000c01c030300403030f4881c00c0510801c222588c4003c0c000043c403110b61a980c401c3c0140c0c422b012083c50350340c40d1a0300051001c8450007902d118440090100c119a6169111411542d1081005a034032890400c06080021720400c090040c181c010340700f100c5440021300d0090040c0a01a00c01317461303025418101c03c03066850f4022682a6203035407030000223506264109030300d54020680305501c00c1d00b10115551030b80b0408104081ea0500642c028007250f43d84128100052509070307030280500c4c41c1040009a6810410100070340c0c03072030213001507142c4180000883c1c148481685e2805090b04030032850300a001c440030400301c40034011110030f80c0505901c041a4403e110310a1901c4a24008810400d8107a00c280000500006125001c4206810a103581510b4241104500010038500800d04030401544c84800c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 393673929 1250 393672679 393672691
    0x1050111010e0c130603020d0f150e030a030e0f0a050a0b0f04082d040b0d0b01210905030f0c060a0609020405181008010f0e060a0209010c1e081801020f0105 69
    0x250440d06141800e1200c030003000b00c00b0b40144d5845200010041c2c90b005941800e081c062201400801d1061a005c40c0c030b0103602280c484950300f004020f030180000441114041364080c01d0010301e50780440d5001c0c1c00d140440e5051010b41c05140c51210078406d000c5841c0c41d82a1140c1062116a55401800c082103902600c0103001031005102c0a044015420100c1c2c510355a00201c184016803040481200d82d80b203138114102e82c04011400e0110302c1d109020340000c151090a007100003a0920100300c058080407540425802d8aa420080c00e10030180101c070525074110b40b5040c0d842040260440c0d4644055500e2a07000341b80c080b00042a040620a9405031080180030040c1c150b55074004607500d1030050300e2a40502900f40e0f002a101000b441092003104044001003950b11800c608141031080003070903d1441401004000d60716030303000000d07814983d402000340e0000b8000c02101d4140c1008850010003007a000580b41481c1d41d440c1094002c881c1d426421501001420f65505003626415206 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 393675179 1250 393673929 393673933
    0x6060306011a0f04050402040303050a120c141303080c0106051f0504060e010509030d03050126030708160f06140711060f0a0b04060b1305100c021509040507020601050111010e 77
    0x20b041c4900402100603c0c0c1140c0700c1d00424203003920307080098200e030721070345c4228041040005c00400c84e940002d070b100c582e0308000908001c1031080600c06040462103420442c05031030002003880255454070340b8000a0340d000390fa419184e42c0d011400500914050140303502c1203000e03621000400504841390451043c83d07603510760038240740c070405440305402204040d062140c18841a10103440800c003154941c54181d4000c00e082d458881010010303140a50040c2805c0410700105000010000031620429031004017150b42c1c1d5a801005546c9000d03d02c0000d020300201c0c100402071003510740001d2020a490840f20196440c2c00d4410313034003108440c09200d40c40e0007842c00180f20f03050750a80e9950048001401150000d00000010125180307034000035280d8401003802c49030480300b0407180000c0c00043c0d8005c44484800c0c200904006040e610091040751406446800d040c0180e080d10b00140000d0424001e5041040c0042c0d240c44090080034002803d098000c000200140582c07000344c0d841c580 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 393676429 1250 393675179 393675209
    0xf060905251b02060d060303080603010905030f0304030c0b010b0406200a030e0109080d031401060c0506150105091c030212031003030e0a03170c010b0a031728020a050606030601 78
    0xc0e615a40750380032408042460b2511040581c407000000c01540503540000240b040c00c0d1304e8090300039500500254001da25040984d030005200100702c4141b002c076948215125901c0385000c0310168140100100350418100c00020f1680c1c00c07002400a80390b0365103440702c040c0040e05503164a08069009449503030b009280407400b1901982c109103001da0180f5205203010744030701481c2d00c3d087c040e80e610710010f42d403200418041c044100002c0d015241c2881d02e151401c3c89611903542c0d844000c0d000500c50141c0442d040900c2e805a801c89070b541d90084d0040c0200784900d80121a032180150050f80940a141c1d40030803050794a10850388030382243e828a540a078115107044411202c4807044a400c03809603600030010500701d40c0c1103420710709884211607441510700359481c2541d0b1910443d5004481c18242400001d000606051442c0580c603546030b1a40d1640104603543c5240c2c00c1c0280550044416441da00c0d90f0205200c0b620301d000340c00711204c5407940c00505a54103800d114280b04141c620ba = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 393677679 1250 393676429 393676501
    0x70c0b0f09271005030123011707150504091d060a0209042307090b130b181f0306050d02030c1009080615040f02031009020a020703060f060905 63
    0x20010039a80e040a0342c041a00540c000165540c41c8000c1e5559640c0103042501000b061809009104d0b078200c40038510081c8002c0f11015070303040001805001c2141011141500503c1420000b02c001048180e1007513404c1d200b030603c0980541e11138000e0130000350130076a0031404070030151105030511910800074441640c4404549001703400040720164007030b8941e001c1c207620b051038400c91400300c64480703d40c005d542084a006044a180c651058a03151818081c24290602c000707804401c89a20202c6030f07a40700d442c0c001d00c410064903084241e030f1008120700300030208166014a04106c1016450401c00c1c00d0b203070010011000c04c0b098000b54164000c20001915090030303218146e00741d10364201129007a45034480d050815000b1910442c00411480e01c5000750702d01801010305880c80101c0c11451818682281383c0100418040c2520640e0005180c402c40c52080210600664000c107041250040307400124014201c2362160154103410301002c41c5e50b010608007000784d021284504120940c41c40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 393678929 1250 393677679 393677689
    0x71b110405060a030b010311030d02150a27121404030c050411070f03050a0f0309050c0d14030a030501090b0108070203030f1504020a120e0f030702190506040b070c0b0f09 75
    0x8000b5600007409440000026040c030000303602071841185816117401160040c1407801d5210b44096007158440000344c4074440426030708035002038000c0c1c00462460307481441003a079100707003462071501c50031030700a0f40d010b202d4031050b600d540005d995038280481003189200c3c000340c0070b50f001c06051403100c15010045440e01e60300c6042c28007003060b511424800c1549490241090020081c0d01189000801410056008019841000c0349003400c12140c5042d460f00d0b07a0380c01c03c412429014000b00090741c1c09120130058428103864860044a948040448009010309001ccc419044a43d080a141032855030055410600c00c04440d4011400c6580341941d8101401d00641050340b401e8800a520039981c9071400200301c0c900c02525091207a110701503013101111508005816190000d800302c400441010044070b148940445000d80800f41e644a4103500da001503000c15401035001a00144204215015021040c0912404100a555525041480d10540751450b5014004201c4c422603464a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 393680179 1250 393678929 393678931
    0x20f070618051005131e060c02040b030d0c0b01150e13020705010203070302030f100f050f01050421140706121d100209040e1c11190803071b110405 65
    0x71204840c1e0541d654101054600c0500b0220303d0006400055108120100007040801001c4204902106620030795044105407490b000e030f84e040004400e841c90035503a90750090142214002c080d100c2071b10140e10050009400108101e640340521000010003811500c540312a11009440c1c9540500e442c9003041004000080580c221b15801d01540020440134030256100c6c1845407401652410325078001403545400401444e021014400c040c48103012210300030301107a109036021462488800300503662801160040480c8840103054410003c8a8125481c0c42901400e0a0036232100d0f20b5500a894814500850020881c0b40040d8600c440c20356006060188102d90841103070010f08503d1418034201d0003083c18560380105a25449107001d07c1802e080c81e16000c01820040c20a0a454002203580190401401100345075014010410311070025041c111a1f0300070703901c040c40d10b40304000341c000fa645a40001c0c5d00c4003040c0c550b02480000710080c9500000c0362800340c80804100f2010f050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 393681429 1250 393680179 393680207
    0x15120504211806030f06050f010c0803060d02060309030301060f23030a2702131a0609030f0f0a060b040506030a0f170d0e0c06070c1202030111030a0b030607020f0706 73
    0x84000800030704041182c40d00d00140002d40c1d00402c04240001144042e41e007a600403510900200c210360444ea03800c417407104841c6078400d080503101e0b560b100000b0032700803c43d440a900b0841c008108010000c004c40254142c4080e44c803105082c1e0607070081140c1c05201c21200c4c4001d107031281c0c041c2540140001c051035018001400c003103038001c01303980400b0380e010522079007400d10000080b0740c90071403400b0001002c0c00c9150300c0040021000c818039020403c07034003071121030007030000050503c1142c4040c00031981903c2c1c1c0710212440c15406c40103580d40c0b0001c2020230b640c0e4902c2e103800c0d00303a0b40c6440d001d110b0098500070001c050202c62038030b8035556030b005600220f41c068544104000201c0b007a4010300718100c09400000b03885c500c00e41966042c021a4400c80384070781401c0000304001507a4801d00350039203170703404449164000d81c0e1000c40d004200e120300c02c00201c10b002c410064494815040001d0005055040e0b03070203074440600c00e9a58403101c0950300540d030000501030000038800d00c5c007007807a54 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 393682679 1250 393681429 393681437
    0x71d0a0e0118030c0308060108091911090708010e0f130228080309040e0c010c030f0302040b04030b160903110d02040b060d0501151e080903090405011512050421 71
    0xa070b410701c4450200b1408501140880c01d035003020740c241900148081c0d4403920a00345400c1d01c1c034028000c507885030150b1990385140d030070a01c212401d0000003182c160200d980501200e0580c1040d1b01c026150240074400d111844580e00001242c0e10803a480150080c072000c1628103508403280d080080d14402141c2a4841c401c84070002d06041c000500040e0044c6042c10145541740310140910041c0c41d2980300240f510303800034450b00e110b40d038440d000582c0107070035241503008201140300480191003198480c0f005400d001c5008003e00c098100b03081d00460004040c9500c40280480540340305c0154030000d001c9010b40400f070441e41c20550b658101481c030007840050007800540001300903402c1081444091903031280180701101814154141c05500341c1419008440481d02104d02c2c40514440c81003041508000300d02045410015181c060000500502696840340010881943d079025400006407a0307401c1808005024842d00d406580c21188280300b4000e0100c10304841c85a1403400c9d8100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 393683929 1250 393682679 393682691
    0x30210110f041d0115050702012d0f030b03030903071202120304060203090109090e06040318080a050a020909161221030b010305130201120b0111030a02030c07050f030d0815120a05071d0a0e01 84
    0xb00420ac2e581682500c60701c480c4401564401d00a0031510143d101c14001c1d130080040d001c042c2ea00040c098100d4481400040c807011892000ca00b88001850210301588004580031500c41d8001c00500044602a601c02003032990312140981601c2181c20406402d030808800705010a110b00720b5081088480f4008644050341c2d40b031028a0440407980549864000e04000001c500e0300581c26900166641c00030320004d01110f142e03031800480c42c41032010380304542c07401c03100f08a0141c10399800e50b4002c0d80c09040700d843c41c0c40045c0240041e454010300103132030329000403010114111068003594044e5614907449a00c0b0004034014a560015075061200180398903450803010002007002582c1e6a0141d601c500101c11003910303040c85604460b02c0b510f00150b800581d074400051440300502d1a291a44030b0341c48080603817120050010501c0d40041c1255002e1071050000560005803a00c40c0b030490703404c0c1d0399441010300205100200b1020700c40c82d1001080c0d103408a900524000c8001400014070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 393685179 1250 393683929 393683987
    0x108180a08040515040b04060c020d142b0c06020702040e06100312020601051302130521060a02071e0309050d0f0605060d030210110f041d011505070201 67
    0x141036901841222100c1d000142445541440c8150f020030400990b1314900f814100380303169000d0301950050104000e900d200a10a658955062844030350704240642150380c0c0090940d034031007480110080d41001d40aa119074107020709007081c1100d4009030b4a801d0a4460b0707070f44403006980440c0c8241d030310503191540e1a070380600a00c11203001d82000c01405c7d440d01e14624044d1401e440b41480c04003075422090042016444080750030a810685503401a41c800c3c0311700030110440b0303d9420071600b000302522079400164507042c0410001d00d0170011540035944090002c000d80c82031071401086400c0c0c4800808481e2801c00c07410541034401c1c10510342c03054641000c00e06603c0b1885082d50000b02c0c122801081c420341d03200c1c05800000569448910f04000c4e1030281d603034040d001c0c004031301607aa110852a50310f020b406032441340d0400408290b40b269142401e20340042d031081140e0754000c0c144000210821140c032100c400c840540c1312181031407400e400544030001d030798000d414404008111128 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 393686429 1250 393685179 393685183
    0xc0108060d061d03071e08030c0c0102130b0310050d0f030f09090908090906040203100b0c030403080d090507050607030f0e01030207050114090610030807020d0201050c0703050a120c11010818 84
    0x800340e80c0f10001141c4804860405255805d200840d480455001c505e40402003181d070000c80350301034007040000d9500d46040312010f009120720300c250300c900d0121a002140c1002d0f510300660089c5800c1c01200c1c01140c403801002100d04100c50000d288841e105d01045c0040e00400003640f41001a00781400516034401c044c8043d502406030444580c0300002e060182c514101c02c280c0c1d0000001c1d40c1c2181107281a486403103000019003e903880c0a48085205d4404400c10022140a184e04c88129070711642000910030140000700c0c0200c2d001d0141280110b00b03824000140c0c1d01994066940744071181d207498050340c00300303500038000307040580801544001c103009010f1607070382400d00341d5826214a00400003d08010024102005100c88800b0820101c0c61201c25180d5850b01101d00d400000c402c0d10050b281841030400440244c0a1844c001090042c0400d100c20000e02032210584545504039003180c41707801c83da0000744810043c07509442d00d0751140305244e901c034582601070041d055100c02064 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 393687679 1250 393686429 393686471
    0x906062110180221070f080a1401020c030d0b0306010b091e0301090b010b0a080604020405010c03080a090218040308060907050a0c050c06030a1a03070302030c1e06030a0615020c0108060d06 83
    0x80b0413100b22441c0092500c208220f100500354803089102e918104100a030322030300c640343d02030010643c4490092026070294101c0ea0072003202001c0320780d191002407549028010103010716100380549000060817081c3c00e000c030780d61010010100400422056041d2204e483c4914002d5095907035500360600040c90682014060314400c03107510313100c0d0344a00c002000c1e0710f8000c1c6018015030062108003e180d810503414100b0b2907041c100005242d0b1105000780040000d00300207540705048042c61491f98130801105805640265240503241d59240244000788074140c07001030008a08010b0030011a101d007050020341445001030b1a000001480040d00542090700c4010240781e40d10080d500c000c2088110b00c0700c03000b06801800205240d5000203890386a06031404e4041c007514441661481d00802c082c00014400802045e16400d00c1d00005004040c00e008005400c8010000b00c141140005802400700805a44195060f40c403401440000781090b030301200c1e19030302d030342c254003c86440078400c0d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 393688929 1250 393687679 393687709
    0xf06200a0f020f010c150c02030c010911150403030903110d0f0305180307032105190801050a05040207230307020303031305190809011404090509060621101802 70
    0x7514881c200d40c010049822100c05215041c0130900c03c0e9940000c101d80c800c0c0041c002c10320400111111160000d07401c0d0712400c103910100307501e0b01000e0340c10040c000302c0101114500380c0b080d5061070400c4e80c200103188994000500410140c50b0f08000007008000c000018400c0907281c0f5200e800c40d50b0f100400d480c04040210049400404d1000080016224000032400300301c0080241c1ea2454031100e4905400d520030507801e0000d4004400024010001c40c3d10751032960342c2140c0640d07003207000282055130a02600d403082006200000d10741c607042c020b441c4c02537000703170141900b10350070101740001e20410010070817240020310070700c1e0260f5000e1000e54490b40c1d14006044a0400c0da20f4118240310b503902e001070080c50144118004038001c0000d035100e0307072400e01384000c00300400d100710f00c124000c030340c000da103580d08007803c010715441d02040c01070040302d058031158039155101d0301144545041c04803200307040c0d0017009507480751a00350300700c0c10019500c1c0904400c0f81d40b8030307000715502e10010111 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 393690179 1250 393688929 393688943
    0x132319080d020d080f040302010b060d0f0501090203010b09010f1b0f1707050a060b0a050907022505030c010305040204060e070f110705010f0f17180709060f06200a 72
    0x800c1001460600280004000714405080c69218500c4090044500a001101441881400102050300035801207403441c030021320321030712902403c030050080e225551160210350308040c00050216114003d481c10f9400f0116001d08024004004490b540c81c00c1000004000380311007500100c1c10b01c002098002801030b241e0400007600b506000c5030560042c0000041003200300880300121700085171410b07074254052004200b098201c4001041c207003454000c01d40c0301c080c440510a0f0940c000507512082c1c5190030180d00c2104120810f8019800c040c498a0b805400c201c044000b95807090340244e42c400d100030000101c194540d18000300242d01195200003142a0425185015401050081042d01c0c418000c120481c14500001c1c00762010804810600c140100c1481e0f0b418010404640089207410309000c1500c1c100f151444224903c00d1440010302808038049a04003040c0608001c4d250f4501c14010324616010045502c44008402d070380d071040c080030600d80d04c590240040c4100320700a002c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 393691429 1250 393690179 393690229
    0xf030f060b0d0b060708041208280e030601060503070e0109120503040828140f0d0e0f1f0f0c0804080d1101181202072105060c1323 58
    0xe0102c2226062000b103845401c0600ca0b00d40003444210448050f104444003030b0080000d2464001c00501a05016218462940e40c11070a5840300500803410740c401c90303843e01b1100d410304050545031300c420f001e400c0000d0310820000b100c00303001c0c00e00b00650503010304d00403840380e94840007000700141d20141201c0381c1d04000b4007000074030001c01859444a0189a0740301041c0d0304802c0884e00f510040390000c1800340f11b42140ca002d05018003402c001940c800007070342c0f46417809070402000300c100601580d01c1120480018041424090304c004c20450191410203110086102d00740d9501011441013010060075001150000d2010b5002c1c00040103c500200010030003480043c01050292a504c1c0550389800d0015a581c02210807030588039400224034189020708550032410030341150408030b801850105810700c80701c1c542103910b40b0075005006070b410546814492841c00c1c40786100500c4d010004117000c0c0484900740d1f0f41c039100c41c4c40c50750101420780c204c140814100c503600c0d029642e507009440 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 393692679 1250 393691429 393691447
    0x71215050106031e02310e0f150927010509070b0a120b06190504060207150215060a0512030309010f05011a090103020409050108010e07050102030f0409020d150b070c080607050a0f030f060b 83
    0x2000316508201c1070f2390141140d04d4003131400d0307814540f01c040c2d85101782d070300c240401d04c0d280741040d240c4054907130481002102000200d8070f501030201a68842c0c0306204608002450100c0344050321f00380340e0a540c0709440c3c0c03203041d50341001900415003420b0740f000b42081489103103c2e001c5803d015803c0241c85142d00e0b546000c0c0060300f0002194060ba106142c18129030041c0c40e0b020902515038456207203068440d0f00d0b6000071402c00480360f003100b0380241003002d50112043e80000a14414942807000740200c11008415106840302842950340240782030701854003505541c000303002d001606150050805076542404c1050712001e9008040ca655a11034208000000340b203610090042800113515101500c802d264007807041e031240b0381c1c1e030399404114011180350030340200001900706445400c00507140d09140101e079010000440d17108502480004400c040407800902c03800301030f00e8a9081c2000d0703a00c15110503202510300c40c10140e07201442c0034080c0c0d06115920117084070071051a1580118 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 393693929 1250 393692679 393692699
    0x9032806060608070c03211a0a0f0503120a0215010603091104051b070203070807060807230a0507141204050103150509040212071215050106031e0231 66
    0x10b80002040020320340c108520181c0003521421a07540c14509407120208000400400c2100d209480b14411700380100d460740d03a240c1110030100040304881d201c8008c5c2e516016113a808015100e1076806820076081d03181c00c2d07446440607140012042c0151800c0300d0340c0041504c000e4901740c0080c0003080d9a0200b00050000d0120543e004010079103040095003044201703400b90350001f84072031503a2080000c051046440030b0100000514007030044905660711f988000d032080788212007400010f000101e0381d1842c1807800c49a00d1251014030403941c80c243c8a0700701102c00341e000c108152440c581c420180004941d0070000802424400180141c5a07810b001c00181500c0c4c0c851001c075000f4000070001e0207a685ca07480600d0300b041e41190203d44508130107031850b0420781103900200059a4401704001400489080355101c0a0810800c21040c0e03203460341981200c040300503c2c034010711610a981b1201c81254010321741d00540649158813002c0c91000c04a20005448004c4034800182ea01080001a1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 393695179 1250 393693929 393693941
    0x60a050105030a031e0903051005250e0d060204030209071707020a050613061d03030403180b030402010c0c0b0a05120106170a05071724011407020609032806 69
    0x4070b01804582c082910002c0c0140f8407090140d45040f12200310940c05c5e4040c0012100542c1d021b4180e40342503400103464030041c941111002e00c040e00c41303907054110349052a10004d82c03982c16214060990606024062540595581154a10350800001c40941c0d140010f41d480740c010340e6562000070490041030943c035000540700e0415540700c1c44984000800200d46281d200300d07002004901d084803400d1140140018401075030f140c0c0d54040d00070092714808401980305500984900d4042040802210040041403094501c0ca140910100300198425001040c00d14083c142800c9444d466040b10b10f820345c404619013010401c0040c4100603071015010250044c40e0504004045540d01e1051103203c1000902020180b07030b0381d1002a03115030164010074072840c42d010030f5043c0c0d403070008400c2040c41011004446141003075503141c038056205080c82d1140b480031031440d0342410280e0742031003020f42101d0001d03940f5002e0204803400480c94403214880c0c1e070117201c08518803c61181840003c85030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 393696429 1250 393695179 393695189
    0x92307060e0d030503091c09080601050306070f0c050f0105090106030213060302030c0d06141512010507020c0607030e0405040f0b0106030204050616021801092c070b070503120108060a0501 83
    0x8018800c012503596039841c0c2d421040c1c02d810180d550303a90f06021b482c02c1803220780d6002c4401003d00300e171b1040c184c0d01840070001e1b10181d1040719281c0e600e8008042c1d41d807508a81c842c0015108d000f80d801c80602c110045490709100320200d0340d400400c11401400d44d0b20444440d01913079541d800c10400c0d40b0700503002c841c07032004403403042103d54103580100351078501d0180e44d03601810903000c070541005001e51102034898107490141d410b80c24100d240044d0104588030302803103100000e101682891040c8205802021142c005050302e4006a0500660340c01c003100660501c81d2618601440e03031079134015076100f2482000303405070202580c58120459181071f00460101441440144050b0b1504411034100d003007200500010101c0a10002d0089141d490841e2480c80006000250782440c0750450100380d10710030003140004c8400080c2000c080446610300d0441d03408140100440b400e80e0009001c0c250150081c1c0707141c0307204000c6442e240e100a0f8003202c0c2c0341d401481041940c0c03001d4451540505 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 393697679 1250 393696429 393696437
    0x110a12051c270203100b0a0306020a0e040e06091e010e06010e0711030301030c050d0807140d1116090e121303061104060c1209080d0e09090d05030c0d09230706 70
    0x5003081d00403c3c0d41d802405000c0306595a071b06a601201e40c0d030040044011a4083c00965035841c140300000c05038000c0307c080718021420501d9100c004c48003c521103100d00b6a40300101059545507480441c0380342080941e038019540e961090101000a0220314040c00f85094200d03514280414020495209000130301c4a41c0c00510041c00003c840440c91000c5400c11600b8032800307246410310052038880d816004210030500300c1c400301c0c1032501181140c100e11041d20703584101003040443c00e0321041181c00d41001c004403000280f00854440c0c2c418451900c2e000304aa0031251480207080d042e900010b035060750204070800030020401103024541c050320100c40d129007880d1401c80701501d00c0c90b91080c0140003401c240e014012452090003a20b001b880140c00300c40390040d410401528400764050b50340e00602c45180051100d100000752040105070300d5640c1881c2d5a5251040d00d0381b90031000e00d4180c000c0d210580c1401003250b003111080204481101201ca612076040b04925041880d44504140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 393698929 1250 393697679 393697751
    0x140a0512060703150909030c0308060609010219080912070905010b1903180b070914090906071b08270103110a030c031e1506110a12051c 60
    0x3032500400c8040e0842d115041c08101c5030794405a24003c00416007101c03028600c0c100c000c0e004d1650010300e03519640e000340c032480360035150744c403e018480c807800d11400c1c0582d01c46610441c0d22460948505459405000c169042882c000c0015103808888090100e1540c802e4100703000a100c284900c500400382001101d2404061000042c44408002084000c0c0340d540d5081500d14501c031940b540344281d004603036000a1520707090103410030700c07240180140d107000054220503904108050034024104e0300300401980e0b42c4c0002c101c40d404607070070106400c0e00e0032800200c0003c03160406001c1c1001d800401c00c25602c440542c40c02c280c6520004a410142480350300c404201460003128180d006520300441d070940f0710305054016040031840c04c10a085c0e0725208003540044c643c040720512146050194005e0b0b9100c5044908224018101c0520b810011808000074484851089590b01c40c2c2040d50910f5412840c003055044418212221292229174018403540d032840741408103011011402e000d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 393700179 1250 393698929 393698959
    0xb090a2c0a2306030a1407140406030b0c1b0132040308010b13120c24120c0314090d08070504030305040e06040902030d030c030c0306140d08090604140a05 68
    0x85500040410280b0314180700201d0020f4506100350880b080e080542000440c03044c81c1019910300722442001030419810003050410700e05230080100b1a60172007480303c11600e6241081c4041c1d801800d00b40e41d043c40c90300310035102c11400c0c003909a1402004484000519003045404150f150043d042801c0b0300d24501040000703500009100e06540084400984601c22042c030f00f50303a00103a401c091801d121003030000b82000401c250703810545a84405400100c00c0c2c41c2e1008007040703000ca4170710021490040e03084c003841c005179000810f420414640030448004400c219012034009413091110b9810584120300209d40128000d070700582c00303190141c42c03e4916100142075025134003c0d8010705407103201003200d0f80da4640150071101c2d001004d44242e22139011000d0010505540420042410100c40301d4510b406441030301c0031690036202440c8400502c3d001c002c07801e03407808000c0341d5044040c080c1c0c00403a00c4500181014007212802c40c2c02c00c81c3d404017003040d10882a031200b441002e101d050326007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 393701429 1250 393700179 393700211
    0xf06030b04050c04052413080f0d1b0807050c040f0203090c010504050616020307050306091506010f1d131e0e03340510140601030c02070b090a2c0a 65
    0x1400010645521080c00c04601c01901a44550140140c2912080307c010a40d03400120783c400c181c0c40024121021100c41990035107403070302d00804400e000c0f03041c20740410200300d90500508000780304000b502d032040000000181250b1206103d41c04250b070220400c004410100005d01402509003040c41c02d045c5040c00080321440381d000c039000d140c0c16060025045403400c00c156000380000500b60dc40301e103885004542e0303c40914034440b59807000c2802003605075001e18401c100c4070384103a071944c00c26031100c04810340181404404c2904914003c2d80c0101e8071200d4842d642049a03c4031101451252109000d4240c90a1804618140d0030820845a80c00401d9008035901090800f83c500c0031012040c2982d01002c00c0c0001400601801e140c160400e10658000303540100f200c0c078403d81603214100110b044a0504030840d015a200150600c6400000e001800b4107480003131040c0101516180f2a40310040188490350b450502c4a01c0c1c038000070341460032580c2c0503104400070040c04044400c219 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 393702679 1250 393701429 393701449
    0x20111011514040e070b03070f1403060d05032b060506041d041703160f0c0b0712020706180c0608091507030209120f06010603060815060103060f06030b04050c0405 72
    0x106041502d1071002c031079034449070015060b54902c2400e03624032035030300c00d4015007130303481155180d002802c900460074102d03000c0c0c901c00e43c024012980303030350031640d401c1c0900000b0b01c1320010980d03007884107009901c00d034000e00180a10000311181d010140000000070101910213070f8020320700c115010312081c4107504464000c0e03210280c03840900c140a4039a402c20400354803100c0311103900c00c0e00c000100718051082912140c0300083c01d684500c8083c0c40c14500b121030341680c1000800a02000000c101e01a20075840c031981c3c41c80f0000c0044c0f0305582030782c0d1503084070740d809034440e01c203544540303c081404111250400107200d00d081c0070806151624020342c45802903178038104d030540e003c40400c880781d00c030390306440110340b01503c2d4485c0c01c03048105088d903442c840b030b1160b80188122800850650700c60301a036000ca03102c20780105885280117114001054000303008c641051399420000411103e000d816400801c3c0c00e803000a210b10700703d81131000f42ca10040c90b82861880820041080381c44040c40c030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 393703929 1250 393702679 393702689
    0x60c04081218131b031103130c260708071215020f040320031204090515030105040803100609060c030c11090114130b030606010c0606210201110115 65
    0x250740d4000d218644007102d1610121035410500100307a072035400d200303603000e4080c0390b101c0320211a41403001d00040301680e0280251086003642400890000350002c1074031101d0610801d10842440d48a00c54a00d031181c1c81000b5402c0c01da0400c40f4a1607081051203000c0243c41001d01400c940e50400010400140c81d0420080101d1008030011080a040350b040e9881c038601200c0c440e80d5039a4030b0910701d401c2d0a210354280c00011000c10f0000c1c241c500000e45040400621103080d04007403030004000300804000305442002544001110050707a028860244201d20582c00f1940340c0c1004103031500d6002207a080ba43c244040d05a0034040c4036004242c0d0508503901d0719010f10349507110714100f054840403c4509400550000003c07c180008003981810701e031041d201c5010000411103060160f47d1502a42a0541c020034041850f952003a005205514012000424810341d01d00c0010888220001126450702590020380c08560f40207507906410090b9000900204c11940e0090303450031018031032 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 393705035 1106 393703929 393703963
    0x3030c0f09230d080a020708071220120109031d150d0b190906060906020303100905061302070c0303081b0711010e03010e0d02060c0408 60
    0x700c001c99216400b50107040084075004846244045030040c2c102d0903800062011902c40701c024490b05603168010501686443c600c2c6007000503d41041c0310340740c1c0600000011625054801c01a00c60400d4407400080c030480018a014040400c980c0c240d50801101c0703400d26800814202c51074040d0345e00043c00c9050304d0b08100540004c1203910020407420b02411401c071007585d201c5940c80d00084e00d00001c0d2000e944240c0190303a4150700110017a501c40c04140012036002810100801460008504600b00304240030f02d00d0b4201e00802503125130b140700046080d56400001c400d03403011604110358423000f5080492440c03005002c142c001c40c034404003182448007a8148480411959401c3d1360500c0400d94400307401c5440034a000e410070030701c190401026642031086400202d05c1d00300400c04400040700190400c44028450444200c050004100111010407200c204c0900315071 = true := by decide +kernel

theorem cover : BRFrame.Cov 393525179 393705035 := by
  have h0 := BRFrame.cov_init 393525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 393525179 ≤ n) (h2 : n < 393705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
