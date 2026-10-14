-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2849
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:55:38.014006+00:00
-- url     : https://prove2.me/submissions/e1f4fe45-5909-4461-a950-6ef1dcc5ea3b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 512230215 ≤ n < 512410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 512231465 1250 512230215 512230231
    0x302070305040918021e01030515090402130f0c09061107030c0605090d080408030c06090c030601030311010209030a0303150519030204230907170613030f0e1201241d 73
    0x10329401e00503591500b00064041d841c0c200c2c00c00d9483c02c0e50004044510040a50741202e00d01cad03084000070b9070f4550005d40d120b0f50449006902003500b61081015201c08400c5403e060700f030a00ea040c00310340000c041802d6031119a13610131007064114200d959010b8620000e081202100e605002d0240709400801000c1c10142091000101581e201d02d05540f141c2d101d050180c00114903042c80a805000306500a0b0011000309900882c004c00a5100e00061000405210180100070703c204020740690301d181000800b560810001800e01030041c14152110403410301c1c03401c0000c2034900d40071850b200300300351140f010b40d281d500791340c01e000050502851441d07a6070340a02c43d59a01a24000307620303124420a20160803d07901d46401300709a00c4400304120761541001302089081100c00c0c1819240e25014640040003941c1240300380d136081c8400e808160445220600c0d413075408815000f45030310110b981d00c0d28400c1140340340c0249000a031400707501c001c18140150a0300c5c20501413003e9421181f0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 512232715 1250 512231465 512231501
    0x1c140a02120612070e0c1e0408071503180507030b070512010909020d02030d110d0c050307150e07060203070c0b041206020c010f05090d030605100c2301230703020703050409 76
    0x107441800302001400c1b00c1844501c07030001455400400302402c10303c11103085c110102c2c00c040c20310000c45e0b12080e8902885422201c608910080c0343d11941100001c0b4801e5081c2c02610407650030030a031600c11030b010949203241200b020030001c0c0c1c496800c481c251907800e180c0d2100c603401c004480d0080c04400c0d0b01030380c2c00720b0803406a20150342c00740808107072550303291280080040d0b0b003000c0038200034a103c903d109000c508400c80300814000300c04c4030a125403001303c10450b20350800b02c031380040401c0940405144690f840101d9019000030060072298040c0302082d54959440c01e40c0d20491140303008070541c1e04c0d000054040020082c0c4c028010701559100082881c6214884900403980122803024141d404002c1c00202590544101d5018103070035140d04104c903540200c05040c00082200c01440d5840703814586c2ca13941c2c800d140768450f21502c0c500a01c540d413060404220301820045104074440342d808080b0300594083d2086030302c85035140d10351604045c644080d242c02410343d80703012040c00d4a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 512233965 1250 512232715 512232719
    0x114042102120d08070905010c020a030807020a0918031701061709030c1207021f05030619080307050129090420031614040504080d0905031c140a0212061207 69
    0x501401051606111913403506058502290014071402641c2c0c003060600140c0c0104602607151340112a0980340c211006940d074944600c04a02042c500c0e500003030556243c403446a0a00c01018140300c2c09a000c1d9460b07451440c58030140c840041d10a00c07500010030076040c0c4503004078011b0701c2c0710f07070303000003ca01540d00709010072001c030f41084000549811813080001e070141c11403902160410b02c490041105001c0420700c035601409900c0013402861048550010640041010640d51809008071350300781d0f502c41041e4034115028003c9204440a000c0002c200e46203072001d049802002188010811a060b403210b458070b882c694208608a01c00f1034040d07541c00e41d0707604c6c1000710004540d031201020b48110b00c1e01d8203021281a010841600c2141004240130200e04490700350341011030301d0140065820003034036001e840e500c103000c1d03101481c003071031958401166819807000407640b05955800c8034a5817804101800c0340302d1290203d0883c1d80c1c07803000c103686c1d01300086d8070840c9203450030880b443c0035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 512235215 1250 512233965 512233999
    0x80c0a03231b090c03070c1403040306290d030f0e0a051c0c0b070f020411040e01080c090a0b03060a0e030c010f0b0a140114070201030f05070e0114042102 68
    0x1c22800c02080000c110b081c0403481d0520b102c1a543c4079082c02d03000c43c01c601b03141100170040010080041d09442d822079204c600181c061088800565101000b0800c018407608846094040340004404a880c0d91003040c21504240245020159241c0c0d90700c40e609032860815661031100403809600321046900109590701d038420460035001b1210300c00384506100f840e10290b1421560811860250248000000600ca40251000d80c44e41140c002c40c8007004003403140343d2401194406168552188000540340720003080f0445221750070388440c11039503551044281031303c0819035001d0301544a00009407035240c50382e10425004110b502580d00e07007a5210324440c2507404d00304040b28500d982c1c4c460340d405460b00f03c4007040180440018910416800000600205032030300c8986c400c400009205011a807080c2d004507c5007d20640801040c144400020041224514868080741c020302c041080000ca00043d64101c50f01440416402d659100310f2107000b02200b04101e030485041c407072884100c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 512236465 1250 512235215 512235223
    0x40b062b020a08090f071a030c0903011b090503120d0203070350010b13030210080106080619050103021e03010303081621090807061113080c0a0323 65
    0x1400b07640d0b80b0110581010110a420080103071074901a5a100071010403121181c4441600013404100741d80da200c0d81c990b011b004041c421600c2c11a410751038500552400c42030100a06100101a56004121502e81c0289560742c01104041c885001e0144100620b0024640080d0360240d020310b80803034040072a1480c0c107182107485071608880c4280d0240400e42540414404822040132101b15418003c415146240071006005860a0301800500c03054480c012a80d51401984e0160040204d1703410518010044802801001c00040c0c2c080c000c074809207401c4004240b9120f40004645016140c8401900250b2088a14804152030100703010100099000614021400780d1111552403a28506901c807403104840280e040c8486880c501c0446001e140c090104400c1641002601ea100d5003410015401071020003005503041100b45032949c90480041c001d46802a0140981d140d1501d08040e101da2503142903c4d0843d40c0e04200308041021195450302c50050f0003c15500137260407802818 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 512237715 1250 512236465 512236477
    0x12070e0d151e0608120f090904141515040b010e190506070c0501201009030c21090f03050c0906150c01060302130501060206060f06040b0a031a040b062b02 68
    0x2d5903200030400502005000c00c07455440015021841c143ca01140100301d802000c0001d40075501ca070303001408010012146070714115100c02110300100500030ba06003400700485805c01c0c6915101035440d890300381801401c1e030301c04050b15441043c0d026607003405241d1010043e42c0c1c0102ea0603250005068440350300400c40c4a00814050741ca15092500140400f4481c0e180c0360301045100142d15609a4003041d103804150725444d0106020000341000c90300a0a000c070007138a00c4136402c0c04464092044000e00720b00360790355250f0300800365403200c1c1c000202c1c500b444050023941040401003150320340070b07901540c007d400400b60f5036002180d0614482c103410010400348141c1d500c00040c82985046c0d030650b001400800820301140d0b0401e84020745650000d01014041e00f00d400e03940c5040e648410a0f80d01800358501c860340c99640403140180035200385002420996044070100c1c020782002e0180c1c0140b600050402480d181890f24075400700d10160b540f03100d10709828451103914000c06e00007000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 512238965 1250 512237715 512237771
    0xd0c020130021324140904111602040b09162a0305041a090607030e220605120d02030f0c010204030c09020319141305160b12070e0d15 59
    0x70f14504104201c040e54540700116043e640c1030803841c0b014a54400100e500c526040c0000644900448001c10050414022410a205004145403003107840d0510724400141c000c590074424280207200740001034406441da4104140141074241129019076103404050307258040141006200c03511682131541c1c80c540440000f040001c1c10090350000407590440f00a1060304c852410708042d0020341184070b01d100003400e001c14a0044205540c2e0140f840d0120580506094018450fa20846006224070b0040314441c0c80d83c1c604000e01c0c2c2200054500c802c04c20b54008600d0241e01141d46d0055411154410f0490340d0208008000a1030445a00b4018040158056100d050080c4001c1d2030315484101000c4180ca00411940c0080c000800d4a41020190741401c85840150801a00f04140844402410000f00100007518003135000200300d100e02c2450080b1490304c503400120f41c5070f0503e540c00c0713038800d040e46500f8001c100b8a45600300c04030107101001411075a005805002c54030920744000d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 512240215 1250 512238965 512238997
    0x534021e0f120a0f0e0105090d0503030907170703060506032b08010b0a17060109031e050d020a03020a02060306131b0318021c05010209061603020d0c02013002 70
    0x300040d074007008051410008500d038103050a180c090b0081038100d6510a060400c100c1180f4841e459004030101c950b0750402410b00d1a0b024098107189590f640b0560341889148144000000c418548142002240704510058800740b0310b1901c0305000303002e001c0c0c01c46600d4000d0250b80c0c80d800b050b00080e40344441030b80c80c440215002c04440038103040c0050340040b0f81d4501c1041106406544000e0000c401c800c034809140e25900d0751001210405030075000200b5040306100b03029840785e80000340d01032861188040f1b500940701101c049071074503c4090001d001da40203840b05001441d09401456011002a221030300f220030403510300d4142c450034500507907200a4004050394155143c0120044100708500104440c441079000c19884210020808403595840e0644420030a00f901140c400500c018090b42c4c0700c40c00d000c0701c141e0494050004602501c5034140d490000c50049080903c02a0161200c0944005d400d181111240d811009844504904121500f10281d144050542800700b0b1600c0c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 512241465 1250 512240215 512240233
    0x10092a020a08072310063b0c0f04090605130b06190210020a0e0f012a1a0709090b1009050603090709180c090203010506091315030b04060534021e 64
    0x82e04c94115101804e4601e407100c1c00b01f06149004640f0304c140e10910f5202080f030195504180500c842c0900040d000c00d280340001c0014003840d103900180c0a03074104030ba240aa0003001c413440c5041f25040311200e034001d40284948030942250703030300b081c1c10351496005035000c180c40190048200c0e070148001c3c6010960094641c6d0031405c1070000ca0100000c2070824550480e880b1004110340b0244681d0a80d000c446100140100202030002ca0100c611041000e031181c1442d410140503021540545103010389031850f21640f618000c06140043c555544500a01c0c4d81030005000e0150300c02001c003500703445090000224080d40f031080a101e00a580c20030155034125107003214a160a9030f0044410070f006200601c4555204800c650510304d085440740116003100e81c40350003a10f40710032410918000341200005102c00d25444501c918460102048990344440102011a0030b610213060f24000d4007200300100c10000c10301c03420403071441c0100c0d804554075140640081481d00c1801d00706030000800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 512242715 1250 512241465 512241479
    0x1c0c0e01090608060603161a070206070c0e09030403020a0303030218030714040f093908030d180f0206031009050a02070507060207180510092a020a0807231006 70
    0x4100e42140084002d047c1c5140d880030125002c24050082c40e070124500c0d540d041d0317014500401c9a02d560f030b01511040d00d40301541005c8644030a0b40c2301d20003c9045c1080003660034a804400c03202501e9004020743c0c2410304503142107000350006080c2045150300d01400d0045aa400c00c03070180100f01e60a040d00b1080d0a40080c001646c00e110355000e8880d0500c2070080008a20f120150390704550280ac1c50003000280c840f20b801d0f0401346907180c42c503162680c80071460f000080020441040304141c10300c440c02c10454510360941030754002401c0d406a0001c034000500e4504015500151005070803080c0c2600c1c0c4442800301d0760b040d103019605603070000700801003000c18000c00001f003031a40050706c2d85c245844104645044071885e11200ca030f41e9040012031a807403016110024010300f8001304a501d04070030141055030804203810030744484008021075294800124017016541c00f160036400c043c101d0b0303505248a0b050009501c0710308120140e4600c556410490200c40381c0c0e603c000401e1262070300c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 512243965 1250 512242715 512242723
    0x10e0706030f140114030a12030c0801050108070e0108100801110301030c051903080702010302130324020c07030602070206090d0c0e0603030702010c030807140f04091a1c0c0e01090608 81
    0x840c00018204221412940d83c40860181110441764822016000c04070009080c4803008078001c042c1280b040303031000c40320b80c945d201441c5400f0540f506540c40c2d032141c0040d11000c20488902d000965544480701f40c0e07502c00d10a494000701d980d51101107040c0ca4010040c06d4a04d01007440c80c0f1400007000402c00c0c05006880d62005140640b60542111800d0404200300462408007600040d00001c4001c1164403075412103002c2500708200000040c1c0780c0c640080798050841d080005040c031440d01c1c1035051564401c40e40717450b040c075001341001450759032032002a402c024001ea0740032205200d101724070b8451b000b15a8050b4440e6145004190904188540f484009000c03c0c0c06540184108401030360005200d21900d9014100300244d9603d0310170440c0c0e03c0e02030041651a00902241d4440c0c0c031001d44001c0c00c1682e80f2044180000c42c07480301807004030f454082c0c805600a175081705d84082c180c0209000348501d07000e0340d4881010783d21000118900d60003030788030480707907581c9541c1040101c0303040c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 512245215 1250 512243965 512243981
    0x60307180f06170a2f0408030d0504023a020102150a02090102070b0403050c060c0f0703061508060415020a1202030106090501110c010e13090b090f06010e0108030a030510030203010e070603 83
    0x64108101a4040c07280c15407031300d4002c17601030030314000c880031404146a2016500245100d108895585003000a0000504401c4c4e40c124095841c0382500d0b1140c00e06000050036800000948101d841e011800d8603150f0b80380143c0a1741903001e20604042200c14030000c0c24442c1e8900140940d40701018000240f4000b03059022002c40b007000c2c4414030000b500407880d43d1500000f1100c080d01d90190381c0c40b2600f4004042d5149045200e04100007040240c940c01c5464001d1140c60501c01c10f45d41d610701c0644488003110b0007800081544c110542541d01d80c3d0161081e403403945001038100d0000e1440c4000c0341d200fa0010008540301c40c1040185607230000b00a12400252400f40801003401d0b4000f03004584d070100c40d14800d0b230700030711000540d1520303a01c11080141c03c001c1039800380c10f00901e456120000c030a030040440c0946c034000315505080280503812140c400d40207601d03200c0b0080c412002004003800b800c20038070f403003c1c00002503a024040c2208412140e00a09100c91134814003801311a542 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 512246465 1250 512245215 512245231
    0x115080405070603020708090402120106180302220b1005030a0f0b0105090f01020c0303070812060306070c030521070f02010f1109040e0a0c0f0f05040209060307180f0617 75
    0x105040100280010400074103d541600340940c517003d03030746400119406980081078001e4401718004080c40c0320280990704850707560321020b1030180074000d02c04112409020207500071003041c0e01e01804415403065a951030490f89070004444400c100042d40c50f0b02c0700700d00c02c0300185021042c021106120b11030500303100201c4500b00001c952000018020b80640ca40880c45180c15004643e60341e402070000c160501c8005086e02c1e902c030a03611b07081190707070801c0110190142e039000000e00e5504002822602801040d00da0750440c5480340e5080340c041d0300c24207800f4913069803a00700c05030407000d41e20258041c61306500c8046001382c6801c002800c444079400d045d1a55418040b241d16042102012280121303c00c1e01c000c50800c003e01d000030b2500706506c0c0d000303010710036050000807160400c072107107020f0b07940d9001e903030103210b90301c00405c001c0c2d0061141c510790180c070070000703d04254056040f941e1500c01032640500c0b01c0d80d807511810420611036114002103102c154507030000740200340166500c2140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 512247715 1250 512246465 512246477
    0x106030b040902010e06030a0906020310140307141e040606260601120f02041802040303020d080f0a090201021504080405010314010b0a112505010f050315060f0c06040b0115 76
    0x1030f80c00003040303842000d1710140108800004181001000c0d04542c1070b464008200703558904152001c101080c00502c5034041100081c00d0f0180356242c0030a01008544400b0308090042d5510b904008401e01c1d4480b03040d0307200080c3c100b41d802940f15402103034001c103026142e01094508141450307a401910060954941e14024104403981c0e030001200d000b12020b802000448441c0205a94024070854011050b9a110007031200e046164607001002500d100b83d003595144001d040091703520300303020307071396442403c0140c40015400f4890354007002c44c00b801403040302c402801c10315424800e1a01610261180400010180115601030094084211040300e04100b15890043c2e80000c5000c3c1b07604500030012921100845550b080042d8408107200095001d00100414039040e00215a842024003092828580004440c0186e0681f486500300c000105207442000c0204613047e4080c2380c0a0811314002e21045c000d012040200754407582c80380315076104550400c0c0d01d012514414659400410035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 512248965 1250 512247715 512247731
    0x71203020315100804030305100e10080d080108030a0e0d0b0a09050606011b0602030a06050619031103010605180312070501093c0f0f05010203071e022806020703080106030b04 77
    0x64130400c0c8640c003540500d0001130741d4483e141d4035194030802d54010112122000306100313113103600d402d03020101d50024085131070210f072061040c1e078103103800d01c10103215410501440c12020b000751400b0603031580007005042604903980d1f8400c04490280c849101c4a9911846c20f000c103e030801c94150807070390074205001c200029070000411050000c000804603600400407403421521908444054071b03001f006240c03102c8285da41c025007212040c90980001c0d00b0f10701c4003030140103070004a80c1a21007d41c1c90394a8040d070080144000c003040250a90140324421880d0709518a100c003030f04070b5520a000208079148a03060a059200f0a00488000782c0303079041c41886101c403401113a90440c3d00c5001c11418003c000c0c10425418090034001030540380e4546e00501c20050190f000b184141caa41d26040c100d004044006c4450082d0215540c000d41e200701d00308842c02115065510781d00c0c10040c03800c411024030b603552109a0300000421808120410014007005415001d066440c90050740c081000c16 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 512250215 1250 512248965 512248967
    0x120061501021c03090c030209180c0907090e09120a0c02030c060301060804020d0f0b160305100e01060e12010f150b03090304230a03141204030506060609030307120302031510 77
    0x240c0103c150185941d6806200030028940d800300c00035074004202403502c0c80c2c11140364110340c1e203441c81d40c0e0700350103206200001480c00e484d203580942410307625415600e0905100c0100400003800f01035507403050511420501c51824028480c003211365442d10381403103552041c1031801400780e1032203101c1c00c0f0070310040c030116500151007170b0301c150100d600440c0e0102030300300a1f0700c6031201c00020304101c0307400040044c10f4810481c2981c04102956082020303a80e040c070149107800d158041c200511000600400009114a0300b0000841009040700c517650410040d41e404c41d0070400c14881039644442141b0440501156100008c1c440d011280307142d07290220b001e40c0c40f8459401108011100301144040c140912800220300c00e00140030824074944a040c1090080d08d90714445070144a10101d102c004403a60095600304c2e0340c0140100310310f071200002c000040c1c10141d01203070507120a201c01e0000c07502203451350a00071150f890050b6030341072008580e5460f90517156000c0c000e00b03030005450051 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 512251465 1250 512250215 512250253
    0x1406030c0409030c1208060f04230604180c030b0f0705040b1e030901060e0a090309092a2a0503090d0c0807090b030105070e100c02012006150102 64
    0x903801c90340021916281d150a684820701208050028450202850f4405401a01d65401540c080380c44592403110842000240c404d000400c110f03424100e00c0340c00d032888d005003072590060001032000c9004640503900c40801101070308290f0304081d00b54003c10902600007541c94000c651500741c2e42c0246400d5030051300b28400c0340b06a01140707000250b4403c1c217007024400b00480c8180072021598a090800201c2d028084c80e01610307a90750500310128602030018444c0501c480da02d034449101c0c040c80c04407540010012100d1041a2244884514040b00603900d4411320680b100d8807044510f4070200b10303000c1805501c0c000d181035004000c1014001c10740020030b880b00003104440700c3d2000d90540c60031703d1900c80c80d0f91244042d427007228400b0440d0340c0d95030081040541c06600230041070f916113100701c03010301040340101d400ca03c14006801919210301a400d6110b130043c141342040301001d00e4070030403540040100002917040003003807061552410341c4d070401c0440244010b141041e1503420b01800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 512252715 1250 512251465 512251483
    0x4060f11030c03040516031505150109090b040e0303070f081e0c03070e030f0a1b050d02101824022109040917070b0f07050904180501050c040603140603 67
    0x1101004000075007007050400810000c2880e07646c010741c0f02507880c0307010043c05008002c0c0321851400d210004d039003021142c0c24601840c20513503072016010318050000c1c00500c0d030b65000d660040d458080c88202d5202c10402140140c40d242e0321020104a60306c0c00901084004d400540601039132281c440f0b94810f025000ca800000c440d010316a079481e030000984620400301956505400303601c008054054011450800d42409030174900201c115070040454802c08500407240d20103940341da0724000d41064072240b600205581007201503503080c00d1151004100940c04030119410754040c480e1201c50401c04204420080d00041c0b944402c00c0c0341c0e1200f03452105480500a080128013a02940d4807900440700f1160421074800c21885984d40d0181c203540011010380300800350704086034400d046021001d215944d650b44882c04d1410440030000070346246022610820040010305010a1007842054050000d0718141582c4a01d084805020740b9506450020800c04420401646880110749042 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 512253965 1250 512252715 512252731
    0xb1b060c030a05130c060f1b2003160306020702120c030a020108071202030a05010501030e0304030c060c06021c09050c0a05150d02040b0c030a09090c0c06092904060f1103 75
    0x2030144d8420785540940f01407001c000d82038090060000940d541c102214402410069840403034510494901946004207000010300400503104085d0201102c210500c5485400405444407113a208464400c03401c3c2c50380046d11007a80c0010f81d0070441c038100180d1600c520b031381d00140034802c0035000020340312906802c0190601c0510350004003698030805281d4002e440406c421074590405171103401c0240700074040d042c0403a20304a4107060360040042907804603640000100c00190a22404071540a00b2810448145401b07000c0d141d84000030f6641d02162188010340024550b035a401c0051400e2040d01c402070041c0c0a6107024001a1a1069a400c1480d0601d03005544c459419600e1002845554000300d805070010a003030003d83c501000810210546548400919490fa01300300301f1104d0b881545030201e51060807000c001a4190880c0c10303514040c050684602500500218107500d542d12100e90310110307082000104209803045109100401004100700a2401c000c0000c900c00513120032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 512255215 1250 512253965 512253971
    0x609140406050421030b1503010312140904021c06140319020621100621150e090102070606080d0206071206091803110c0609040906060306060b1b060c030a 68
    0x406210b0203401c02d40c00130380e0041500d40894807400340280101284200c1d184a8800a101c010700714003d4808c1c1c9040e0f0790800d40c0c0c00c1d0402c131b00c0001500c81c009c0142e10710594620038810440580e681d071000d004d070903843d00380409a00e168914031a044400380d80296070541c10002c0210002c3d100024000e484508401e51018204002c0c000905a802a22824600d40d5401c1d4100d84103048031448280c00340a12040150940303031180c40956245000224a0290460300c0ba5111150320103904011080c1d060340e0b20001c2000e459003000c00784000d044841c1ea1540e0340000e41c82c000c1015600c2400004c000642c050214100040e0000b0b485183c060f0654042180c501001d404405a5600000040c0040c4400b0040300880800740c10b600d5589182c00d501141e0580b2048034070010200f85440e060030004c1500340b0745072441c0108130003002d6809090b05e85a85d100400b0001400a1040d0009086c101d00c0103621454684c0c044d00750742a81c140c00e180c130354001409000f903014150082d01c1c3c10184d045004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 512256465 1250 512255215 512255221
    0x60903180a03020d0f0b070c051506130c080106320307050c0613020111010b0f0907122406050705030a05091302030f0a0e07050a030f06200c01060914040605 69
    0x921500c1d041e41020350321503074101501d01000012003050000364420300c040f035019074444074180c62a481244002d0807507046882030101911129610750f611540003801c03a40c0341d9901c00d54110488000a00d0071006c110094010301500786c0091040b9014210900c50300d82c0764070140e2400c0e80c0c91100781304c904070712840480400c04250154081e940074003030742001c450b00791600002d98400e00c071050304107174003007031071b8001001070f80506000311248240f028000c80304540b0210144401030b0320081c0054204258607040006880c42401038045942560384c610280021020210349a1945070380044240f01e010071498000440200030358808035000d013050754407041e0707410220b450940710350b565040d079610000400664481040040303005018802d020400303d040b40341c0711980c035409030080c568044000c1c48104000f4078600d0305035850520442002c41c001d41202c402e0780104503990750340d0f440f071400803c0c0705c20720b060301744160743c000c083c2d001d4213100140034140c031118081800303400942032036191400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 512257715 1250 512256465 512256469
    0xd0503030a0e1204030f061a1c025b020604020f03010225060213031a0c030c220503010c08010e090d0f0e01020c15040503060901020304030f0813020607061b0206090318 74
    0x20140700e25406010050000c4100303c02700341c0340c000d40700201d21603241a010b100e0390b0030015092059141000c12404e001d40e14611086894440e0f9810714810141c10710440c07410f54850038015030708440140c000f0111070401c0c0c410003244140e54907260b8040c0e031041c06000341141180f8100710400382918200000d80180b414008080d02ca06038041a103030030000c0c0300008100742d8102c0c143c803000d5407400f851f4036620b8010600c0181d103c2a104400c0c808010302480e440b00b01158049003000c00300044484189940714003103400c0d280904110350108040000401c4540b9621000681c44024540074101d880c150010240c0840b6018000c0030802100400050081e4000c1210b0012080d00a1002c507114400c6d96100c04641c2c0036000e42c41c001c0c0200c801040b0300d0f05050098074006c5515440d0400920000030040340c000d01c00420141c0480900b605540158031070b2360007010200e016040100307100e910f1506000200e040f03c0006803c40d8400c07010042d8102d804001d460348900203030180510700d03541c900 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 512258965 1250 512257715 512257751
    0x5060d03110a05011b033c020405030703030507150b03060c0d02070b090309210a1106210f0114030606040c120612030f0c110f0d0503030a0e1204030f06 67
    0xc8010203640c0317014821148981c41151551710400e00c1d640c01e0280da0b0002001e4030032644040801604915000420340ea4007070f0540302018003400714070b001420315954100207464042d071944181d01042001900ea0f042c00b040503c410322003443c140c0700f408011004e40100f1394411008040b02d00080021900151892190301140c0165030400000c400b1800c1c041341007526544420b10f0705100e601c1904920350001e0680d640c11241c05406405002442884d0700c52000c120004031007035600030010401000c000844080082007280d20b040416010701d441c116840c03818606801400440154080c0c40c00580d400195150344110140c0d0041850a8403070001d580344186080c400c8501340c201107020030007510b01d0115250780b40c040d40d207200e840e205014042d03480d5010030401401d01341310408401d1403406c04c4c1c0942400c008010f041180d03801082c0e241c060842d04140d82c007198041e1580c140b024445402c2140c80c03100c0840d040e95900d003d2030744d80c44040c0400205401800d8030b482d00c48c030880c4d81c0c004cc0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 512260215 1250 512258965 512258983
    0x5091b0a0305010608060312030c03070c0b13060b15090f1c1103120901020322090515030c03060c1b070506040e010801140115050c1f06050406080105060d0311 70
    0x404a192a4664060003501610090003024005000c0f81c00082c0036240000d540c003001c2240050380c0746162130303c03004100d41d0391008040c4001c0c0661290080001629030918900c03583c250b04102110a10a01d8003000343d401e4a00c459214082a4101040080000c2d084507400300048520221640c088408078440552406240380b07980d00e41e8002c482031040e02c185441098108805460381c078040240740790320501490105600603801480032486990480d07044c0c4141d85050301620310101c1d0380b00464801c3d07510031200c8128802c3c2800200f0311500b8104124421410110042e00d007900e000d122040e041c3c0602150007014071024092a01030100a0060901030030000c0c0ca2250342d5074a450903510a024280700301c0f40d0b41c1d03180c02c0120909011100f1031605a40300b038042c801d05010919400c803440d4102c80c01c2602e180c01600a8902583c00c0c2c0c1d042030126000110010840502d06410001196955802007545904107010403040395a00c0d00d00a14944d03160400039004071030b90104d1482e0071a10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 512261465 1250 512260215 512260261
    0xb04090b0f040c02031209062701141003020117061318051903020f010e03070312021201030c09060b0f1909080105190501080f07090f0b04020d0504050c06040e010509 73
    0x22000c0f40f1425076011004003040403a0210b0b60703545403601c40001d030b991902280d41f500e031941c94115a030b10b102d00750840c0c15440c058242c0080340d00d0a420150451900041c0c516910704442850204210350b0800000010641440d14561003850148046044928000e03104454556280e41d01c20301c501d400550452082e800c401101c00c0c0c4800c85030b4071880044500f105030054803c8078586e45981105000d1210f240140c00d024509205065405641200020008040c0d0540070b00607400010180c0100500030b500035000443d0382446d00c41c0710001c0b110741e0380080c1050b0b17908001240045500408075940d29410307180114400d10400011546c038003068001e584070b5420041803103403884003000a554000c042e140100714599948000c03564401340300605a070036400c0f0355030800010030942d0002d8680101400f002c2810711508000404a070703c801c0440c0172007960380c014442400070803c040308070301009070b800e40c0c549401e114091395104014460140715055a40019020a20702400d800c241d07008 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 512262715 1250 512261465 512261471
    0xe011407050303060901080d0f08040201110d02060a0509072403060e0f0405100204051c030221220501170a150b0a142502121c14040b04090b0f04 64
    0x285025a100d82c0107503100ea200e40d01c00000800c00440c00300710300040f01040e440c9d001415000c15002d0ba400040104181d05001c40000080d8075088140610046c2420341d5000d0b05061403d00c1c0c0240890324090441c900640c0a05403e002e01c5d00e0002da0350200d452124282c0340c0c44200002c0403070203800d694000c184082c5022003444414420f20300214013440c030403000c0c2c403001400c459042040780a180b08043e800b031460b014a24414005511010001d40244180c444417942800c01c2100350082050742e5400d00000602d1404518060740964035000d46040107100381c07403900d00000c140a4291030041c1e401c41c0100080b40fa110513551101d0110b100080300c0d86245a074680d031000d0700e5000004004d0200da64148540800d101110032101d004400c1210000001c100d05070012155032200c030200e802141003186814061010045118106414075800704c41d405421001041c02a100348290303002201808148059089981aa81a0780e05140c0000340118014001800d1005c90390810f60480c0c6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 512263965 1250 512262715 512262727
    0x30a0501060b0403060e030a080c03042d0302010b0a0b0a080709081204080607090605160f06020d1b02190b09010f0921170106030222120c0506190e0114 67
    0xd02d100180c02100d00920042100303080e04030445890b4410b0780c10340400254200d000902c040080c102854000b80076040a1020303601c0d000c1c02c01840d260691051607001e5880400b0020994240121148404107603070208201d85040b0100416000d010801001e004038140040d4140344101d0070600280043c00450380d48401c080783c41d98490b0b11070f00602003180500c50014041d14098810001152995a01c041c074240d00603000c8264191089801c86000750110852000702d60300d400685041d0104843c00128010b504035140c5040e1700040c1c08000759044501d8003c0d01140c50000d14000a400c100510810707550399030002d00404024070780000b080c1c60f20b03194070103210000c542d400490003846000f0310301488a80c5c05030f070b030007000220402c0e84040940040c4030581c8030350041c1412800030302c0c03029070010060707080c0b40c07141599030003d0803441449440344050103c05440710000700002c1c2e40007860700b101480591200b00c0c10380012002d02c2a24841c82c2d505901c580082c1512020070060b41c2e803502 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 512265215 1250 512263965 512263979
    0x80f0a05070507151202120604320609060109080d05030a060312020d090503030f1815070b040204050f070f0f050c010c1101050a0608100f110705030a14090d020609030a050106 77
    0x13880c0e6104a8005203100083c03601d485118401c40e0007541007000a00440d98841c400c1101900c850707003444070640ca4803103124150250060410501a000314806081c2d4038100060201c030000060aa604000200104000f13010300821000052040c51404075078aa0344c11100790b02030011039000924001407480f90b019190790100e00308070440d2088d41c0d549052655001095501d00605d8102c0c00610340400420b130366a000e10421000100b009091500e02c01d034451048510b03a0080201555101d080304100402c500e02071080d03030fa00010070040c210444c10b02c00c500a098010400c060014414440c0050302110b000300280c5500200c040000d01c02e01060004c0104200c0700c4400b00b213a19800c2002060310350000380030708010b441c01c4400030201000d00341d54120140c40c01d000500541c80e5502d100181c045990401860100c0c001c4004542c0c80c408001300904805089511642450742031000c19047e036103803000c4414840c3c0440c0c0d11138035500d141c000a0b05120380c0440042544d8a4140002622 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 512266465 1250 512265215 512265239
    0x4060f090e010f0b060a1d03032208011505101e0320040b03190f09030804050d14040b1b06070c1202060103030f1407060f0f18080f0a05070507 63
    0x100c1d4800081c041c0402900201c0184c2c2c00958455a00c48824402c20107258840c41400b140815500d400c0d0a40c128010003217415035010120444501100140d50107030501510401001010120000c000010b021500600d8a11590042600c903810b403416201d6440d20502010000c880318a40c144240300780480068010940a010b004100b0518481d04880001c480290381c00c554080da0310a04d955500c00b4450142c180b4038000e981c25036501c0304401d060201d5441107120b1305200e0b031114075481c280360030414904010b643c0443c0400040c103a56200c05d64202c800e48007219120417030f45071103017404060a14541d26001c0400d0076845407404100031142d0000ca0600c049000c3c070b907401140405098102d854034400d00000c1c01141e441c81c15000b8091060f06101003405180101034101080d80e6640001c0c0d8024080380005141c56005d0921840300610030b088511484040c40310f850702450f07541403064010605c1c0842a10380c0840c042c114140100c08a9450b00c1e4840d06840e01c46848600e02108 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 512267715 1250 512266465 512266481
    0x50f0901030b3a0b16170423190b0721020301090e0d08061903020904060605030d0f171b0307080702010f060e161211180f011b0204060f09 61
    0x40080000d800007403d001c00c0307924108043c1c00c1001152617599202c000c03070b030180034513801004103d4401101d40304000d0641c4018001c80c4528085002146807602081010088400300d1855801102101f0200ca000c03000c4a42ca103580480e6080960307446203c1034403c0d03010b0a03003a012409240020000d99074480d0300460507208241020021190790070070056854107040d0366a4041002103010441a1038603a001e80c035035a110003201ca003055141c1c2d004c81c0e00d0f41001d07101220855160101030155240500c66039002d41500c2c54025600e10040f00014400f20048010700d018003140004502c44405080004035550380749030f0b0184d62410403410041001d03208445560041d442c02100c40c00c0c0c007042d4083c4000b01d4241054009840e214200354800e08074030384410f03800340604900181650038040c040c0c5c0c0700500d01c0d80c0d140c0791150751101d2074107100807002404034840c444d208011940c580c1c0045031100b0a408901c030404040005102040c020441c0740c0041226110081001444203010380000903 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 512268965 1250 512267715 512267779
    0x409110405041a210a020411070b220312061505030a050105061903050603010b0a060c140313060c0609051c1106060f040b01180b04030212060601050f0901030b 70
    0x2180160f60f0b85119400c030703c418641030340001801c0882c0e400c10504100c18544150384810394030000e04660009040358600c140c02d00c40e250012800703105012201c20f1050740240f002851203981c000c40400c00034201c24001009050060b001031940703404001c0c0d4070840103005085024a00c00f84a0340c000b40c6181c00486030f041585042000204440c100041650365840c541c40315004003096111040e00644801040d107a05990385e09803000043e512034a200c0014031003911038a0400302d031030900703d00086200600344c016600030054007645026804151003190781502e40000410410f2900d100038254100303015040d4403807a6032040c078000c50049540300a10840c0c0f00c92005101090905440e014100c030003582c03007068552880c03ca030601c1e810411083c03005152100350703410700b0801d841b08c1400c983c016429602001c2002d10850a0019840c0c1220300d42100412040c40c000c4002401403060000001114801040d1180c603a402034100f540b622800400980c1c10708a80750720000381c1850340c01074007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 512270215 1250 512268965 512268971
    0x9050304091410050a0510030902150d0b0609060313020a09060b0a09080f0d080a060807090c17040b1501030e0f011e020903120315060408160501091401110102040911040504 76
    0x42d4101c02c3e594100e004545015140040441c60602003014a00d1101161001c1c141c0707d045000060381c401d5141c0d80c1c138460001010745c5403c6814180d00071540040c92103809030340308004500a540e0380e02c1c162580b08002e100400070208003403000c5025003945a100b100d5140c00c2c80004214003c0c2c641c05000c000005a68484c501d83d5101e07181641c4011098010a40c2d070411118141054410014254010032002000c00c030256550f4010b4500004d551045000b255a00c410350350307039540a0030203c920315000b01410321500346511600b4030118050a0007110844a002800150340a46c02c900340129003541541d400f000001d410354081c04600f07500c8041c000c0400540c89505400e07100303581803018050300a110b0302129192004c0c070340d030000c0c3c1035411105038a00f088607256950b50084c4050807084010341140e14154100c62454582604421304bc050342c2e034820700405a040002d03a0610700c0c2440d10384490844805107600921642c2c101c5402e03142040340394a0b4042c0c0c0100200120343d03050b6420 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 512271465 1250 512270215 512270221
    0xf04020c070b030709091b2316080301050907050301030c21060516090812040621060b0a110102030705070219081b09090d090302150d06060903150603170d090503040914 74
    0x16080130304070101a01141e84003440b00d0290105124100e00d24200500d21403030143c1100c4581d18104030400215401c1e42b0000041c0414285042c2468200f00c4a0420070b045506540d1151080c82c0b03580144101d41c80d6050903e50341045114200c803c0310f802c840200058100342c41425070752500b42100c880854107002c0002002d120001e5050180d07180c1400c481e0802d0704042c004c43d80e88070810b040c3c5a120108694140030b4124910640700102042e410b2503a41d50350000014210948079203104040b41d00c180704114500341c02200700e41c60f9a50440320a0f0340c501d8407560307580e203074680c540002440b886809031090211542108042c000303842100c02d07040d81e65612081c6641d842c0360884003070014112410410041c14980c1070140d074034101d8041c1d6401e0082520309081258000d500c442d002400d855002c20600003c019143c0b07042d55803840601203d401c507101d28460a00ea011040075842c07002810744107403030b0340364000062150304c10252a03840c2d50b1a000040908602c0030380c000c03000c02075008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 512272715 1250 512271465 512271491
    0xb2502062505040905010e10080a170d020c150106030b04020313020907020a080a0504061407050606060904060819051e0a06020703031806090b0c090f04020c070b03070909 75
    0x103041c41038105401000304a4034051a40c91803000504000301804014400481c0d4101c09001e0349028142d018840c0360303030b403500d555410b103010071641c4100c2c0e06401060060000c5240d003040e0368000f81448482c25034030305038405500c000303100340c00c82a0b1b0540600b407015100c5e15000d03214039040f1405954280304601780382d02080201d220503190000701c04810700740c0000606203500055806802c90068500f00c28190325200d0403984200343d50000610009014049190081d49148014070b6424005081c00c480d82c3d200c554880d409820365119600106168100d9900c1c2e402030f4000e0103c4905940200c600074458404005851500311351038056001440800250000e002404c03206031740084c15110300c41c0d101e1100035800000282c5c00c16407a601012481d105044030b03000300f80d21072000000c4500b12420000d01602024154400100d030401001556541d07410030200c040b0303011640141e40b940d0a001ca60b203032001660000c00b03801000700410103800d40202c107410031604817920a205c0740490381c40e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 512273965 1250 512272715 512272723
    0x6030d090f0e070c1202010605210318120d051305120d03090204090b090d030e0c0a06050c0a0f1406010f0b1204030c1e06060e09190305070b2502 64
    0x35141d0302112444080142e6485001c60a80107080c03401c00007140d040c03507296031202e020071450039030140c0e454060810090410000ba00300b0880a0022204042c40a55000f51284200c400c98414580341014032500c80d80c0358200c89090080100890b5030101c04990042c0c103681040500291600e03800d0400a054101031a51807094600384c07028081c00f040e6410160002c040e9204248c0c0c00c60360f158114400117100183c003500880802d4007c1951070310802c2c004003030340c034610f81d9001c0344c1d084000c24103080d854940301c5d18181d500340c1c2025034691002d8a001131400712801c002401c00e0828144031070074040311000025803034440c4030a43e00c140e81c03110100320070701400c0d22840003c203030700700240034007600200100c5810600c685400c1640303203203540f074190352101c80c4d003e0300d0511500101402c08120f114460540280108120421140345c41d554171a2141403131418240d902d050b0f8403242301014411000c40d512203070700c200d22203801d091040352210111000085d80303080524441813286030f240001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 512275215 1250 512273965 512273969
    0xd05280618200706020c0304060804050d0e010906050c0f060c030403170432010e0c12060c040521030c1c1814181303020c190605090a030f0302010506030d09 69
    0x2d103581035070746290006070b000c641c402c0209a400303035406d02603500210400e00c01030008190503561410786040a007081030424442080c20320521005001812282e42c0011000c03013114064185152180e06010b00c180c03c00d644802e4801e924043c440400c4901034501c0055800341b4043e80ea10590a400b440301078400d21816180a40502400d015031002004a6031038001c01100c403290b0340c01902d10840807942900c0f40183d070042540c00c01001c030351071400d1021440400c01102c1000340203a0811550ba8803d074441e900a4600440401c0b5080313038000c000c0001900202007100407a99580441c48000d900d490011031090003031001e440c450340b4110b01c1018114440c0d070701c01c0d840c2c0440e246020708451400100e400e00d90f40141401100c8151440241d01140c81400005051409080e0a117402418010111039152060a190004409100c2105602410b40d00c440c100103940d20221130016003040040d510091403080300300001410154190007440c000d8030290100c42030718000c4c7c1001d58410303c8038 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 512276465 1250 512275215 512275241
    0x12230714040b033408031c0b0301020a0906080c04030b0f0a0204030f0f120906081f05060d050412020303091e2b08010b041206020f07080304080705210d05280618 71
    0x1030201100300e000710b4003216000034513071f080020030080700c0c00401d00f6604080141e00105101a6040120642200f00c06601518101e007441c5014110b5803621407070b80d005070001c000b0808160018903040801d60440c5c02850700312104401d1200c0d80e103440310100055800440f14014002c0c45484c10300e01450f03144054418ac0d840b540182d954014003080d4502800c069000700480300f080008130364840d14002d182410702610085107034a0641403100c0110140c4c410ba004550081080042610022407000b480301a0810354056608052001c1d81c43c0c0f550841c00980032000f0310300610440000c0c0301c040a5101d80e02d272100790740f90fa6a00c01e00111400f881c0302d017000c440142c1003031305d00045c50347d40208158003d00c00240d080c45240e480d142e4080e0002c0740d04440030140020420240441045814907014031051100780c0bd209503103810440d8002c3d50011290141c555022640d080c1d040c01010490711115410149c2c0c1f51082c01040d80a07040a200e1000e8071420460202c000c801c075130090790004242 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 512277715 1250 512276465 512276467
    0x6090d0206240a030b090f0c0a05060901110f073002030c1215010b040503120f0f07060b13020310060804080703180306020412230714040b03340803 65
    0x1402d800425204a840d99026180760000f00001d41a550724030b000c1c902180c028404440900390052521500b840030700c3c400c140e400d4003004590b03111b2044520400c02071805035001c0140f40c00c428a400216494040c1c0780c050a40040b03450050000d507107a10390111003007049417201c1020b495005040e031442c0070b5019007005400c0545800c0409075101c55000740c2082fa0340c070000307980d400e0750030a8080c0c0003100c2a040c0040c0400880c41e00b04024503c09601e010a2844e144003107014040c28800c400701c800e1800c80100b02a401d025050b0302c40210040302034030302c0d1020300010049900075407040310202800f607207221b00400e066104a12442c0300b55404000d8520b007100d44e450980310801c800308415030400315440c0100004442c0d0000d4402408001c2880c00700311070903e856090a007040300b1140300c00311221120400e480b00000c0304c80441d801d440d051031482078003c0210b40580784d40d07410240c140c464030038401c802d02e0b41880301d020801400d50026105420300c50b5056061611403082d0480d0f948 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 512278965 1250 512277715 512277751
    0x308061f030e0a050f060105210a020f040b040207030c020a09110715180303090606060f0c020405150a030809031b090109050c04030f05010203060405160f0509180906090d0206 77
    0x100a078005048507000000f1110700c240d0966440340b41c00079080240d6410340110380100300318107000c1c41502c1c000c0084103000d1010072102d0360711548d54130703146006072240308080201003ea40341c9502445c2c42c4080504190b548107039038100a803110340c510408030300a901c0c2680019441015200e950368607a4415003191810803c0d484075101d0500e48010f1189803684c1da082e01c2c9440c01000f00300da8100d4403a803030109881415040002c1100d0060744404140102044e204d048603038406c40c0c6418841e81110b0001d0151581d107101d0310001000d038101a00822403200203c203016041d009021020b004504413072058600302c1c00c07605104454180d06400004210052242100a4001a03480683d41c4801d6003880c0d50ba032540210050b51800076903241e503000091007410f007018058550300c80c5000b0f4108a100c0d030102001000c0035840d00c0184c04103d00468114603a554007101e50480c51281e404038109410960001c0d80c643d581600c05020074440c291003000c0c110b0001c20b8640c42969090031809401c3c0c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 512280215 1250 512278965 512278967
    0xe1e04020304110d0b07030c170601050307090506041e0504110f0d0b04090c0e130203060c0a110312010815040b190b031c09050402042402120a05070308061f 69
    0xd04050811202e20400f00303082c030078035159202d0701c2802d02d0007203034481514106001c2c003404486400303084000f00405550b0141055141c04880f41e00f090b030a1030300c00d981ea51003134002c480ba030f400d0740c2085911071070006000501941c038080c1e040f85054030034030300d10502d56224200070482c1e42400d4207540304141480840c15000c05807014085200d2420401b0440f44601400201194a0ba42084544008524050158060200c1c41540c08505200c02509050b465000260b0f56000204240f249200c0000c16200d02442082241e010f06c0c001012a901c880d100c0c1c43c0200b60350401d000d8040944030700750207460240e404800050203150000b0350b203d56500d031003948640301c41c4e001030701c0c5a900d07498000342d12183d10300b00b00c4111412864100709030718a000200080020869610407481140103000510a559840c07c40490703910b0282c01c00c0106036450304c03050b410142c1e403c030800140d48010805d5400f1580103001802c40500c81d64903140195940420040b041c000000200c50030500c1e581000102 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 512281465 1250 512280215 512280217
    0x30606050c0d0f230304140604020d0b15060d05040b1f0302060d141f05010e0618010207031506050a150507021504090e01020d0c0f0c080921010c0e1e0402 68
    0x202c0d181c3c6003104813001002c58490240f0b6480380e10f5801003000004004c280715142c0c0f00c0c1039044602d03c001e40000d080507000500417001c00140506510ba14a0100d40750302c1d40008554182d02c0040c1c0515100e800c0c0e10030100041604a5094490710b4000001402d24030251000f070100644d0108500035050840c0c083c1301c01500840000104c030342d900c4c0c4540142a00c065903140c070814134455800341d034050440300001410300641c00941480001c1c3c01142e01581c038003050300e4035a01e002841c41190740e005030040f86003c20552000e0004d0b01c0030000c1140028682e0400e0080d241b0654240150a40e41c030071050b1144184442c40300020018010400146804043d1401c6c0b0b101d486480ca0401d600c03a04000304131102120011000d07940004c1c20700054074a406030800c0f00ca89420030740e031403138170120001d04400c45066008016810014401e0802d94401007000400d170614114110038000b10381c8100d000740406440e5801040c0780c0b82c0c181056140414410480c42083d00810b01a09481c6040c080a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 512282715 1250 512281465 512281487
    0xb0409050601061404090e0a0201020705040203100b0f220e070203030402090403030b030a15020a0207050a1401110f060106200604150b01020a060905061008071202011b020a0f06030606050c0d 84
    0x20004c108000100c1403c18040c102132805110041c2010389440e01c0003a01d0310490b640900e020300e0040c0300300501c650301d0035561001c0302d48480840c1d5913200c801818400d10320500d01101d41d003503040c1e081001302c0001c01021a0650352861880480340e00d1325401643c1d00e01003290025403040402c40002e00003031080e00711000c0d1240250458030340909554802d807150006421801c42130b9408100d1001c0e0590410247e0002c3c0804d40e2080c41981c104200c0b881121144c4050906202c0010700003500303a9420003600360503c1001c01038583d9035842c0c10000b80804801d07452a01594203110f122828110041901c500856118201e01c0703420b07419040c0d80e4041c008100c030f91410360089095141c0400d016010302114184a10041c2200b4504900581d5011155030425200e0742c0c082203062040c200c854004150450b02420172007011b450f04040d503030303999010800094008606e8040000c40254210038002550001e440911100391a030a0403a6140600d8041401c0b680c055040ca443c0240114200d0303070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 512283965 1250 512282715 512282747
    0x30302041a04080a02270906090d05090d02040b0a0b0c0a030306060e01021c05040f1404060602031204020609040f0e0106061e02250b0f040801110f0a11030c0f010506040b040905060106 81
    0x100041c050381b00707020248044603025850340003c000c001c010310042c410450204c080d810321608000445021507203100004c200203004641d01c1300360683e243d5401007650001c1a41c200300907940c0a25028403074507070003410803c801003428002e000c16001d02480c0703c4898000c06034000c00e102c0034000320407400050382410300304c28400b0410022460782040c14269000c1d0403940d18144402d4076400501c41101c0603070b441001190428801005140c1e0480000703900f06804139141502c2d601044000f40013800310401340e200483c6061841381c0d5088044d0002c0045942c1920ba40d180f00e1070940602903080c1c2034414400040e00288103058060304484c42080003124010b42d2005410344440224100b0750014178005071448000c80e04000c114001d000349401066034039422400d110041c0141e1605025109c2ca81003070102c0d0001b5081c0100040060b02c01038403c6a00301e5a0842200c0d1401c1c3c0200310a44000b4002c80c10080c516040d801c0501914228640c002d00a00140e0300c2c0c454110f401e811040ea12003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 512285215 1250 512283965 512284009
    0x30b160912060603050609070e0106030c0e100e041419020d1104030f050606060720010309060501060e090609010b04050913120801081608060105130905060103030302041a04080a02 79
    0x46409080301c100358209034810140010958114100a0f180000c0104869460f80c01018144410b0411003040ca0440b03055040105048141603030030b5588540d103a0b4620340000e5581415812581d02c0000da1004a005460800c1641c4114104400d4008100c0d052145040584206444140302d41e00900307240c1b16400000903400c0354185c0d95a078551082c0c1c801d4441481601c0710314144802408100c1d00404103c80003881c0c21f8040e500d004150010003a1083c050708a2800c100032a40a0741010304e0003944030208000c507686516016044110b0102454094002c41d40065040d04080404e44d050314014080b1a080071301e071008008640b20000c0449060034000074000d130000345685566500d0201a8803004071940c140701d801c51416a04041156111180c001c4c1000410340c04901a81554411398112440811100e03a240103002108801021842010000000d00d40c1c568003034002c1d28030008512480640400c0300b2646405140035012050b001039001d0b000500e4421540012170614040705 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 512286465 1250 512285215 512285219
    0x3041206020d050c0436050603030717190e090c0304020a0e0a05070e040507080103030f0309080d020306030f0a0c0e06130f0902040c0f0905040905030f04230406030b1609 75
    0x840c05845054404820001d0041010300c241040a010142e0f40881c003401b80001e1641584c545440b0b07110f003840c86010350f50700d4004c1403654a00b402103480c1213030049a0303030040200000f43c4921a50142102808035503a1619007203806125100400c074440c0d005110034520f4a0715980360480390b0014000321b038450340041d0000b03074102204529512031951204d00080741e24111501400107103544400342c0c482c61901c810081c03102d401003100340c103603905031400741c1511303051240c150014903008c0700c080c0c1210343c0403a0800c5201480c0e0001c5104640075807d9400c9a46150340403030359129908001018680c14003c14402c8208069410f03601c200003d00d441c941d00c5607041c0c2c200031200b0101a060700151261090740941c18a401221100640d43c0751440300e003402c84130000c180403140c3c0103680c4541e03219064041071003004c1041e034011004002030550382e542e0702c0d110b0020384054000d020080072a00d0144444038909440b400003269001060178040d41e44140341c2c00c100c1060a0070300c9050003500000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 512287715 1250 512286465 512286487
    0x105030a0b031e0309010212070519020342010e01140607060207030203031b04150309050715050304050d17041103150a0614120c010507110310020a0e01020f0304120602 74
    0x5480c3c2ca400c00c48040d44c1c1c2d41e408480020b081c0200c03800072402d90901001800b0006800244ca0080d00c9a04143d24051526030320020b0f04001d0341034a08100040500d2120385003070b00322a201c02428445011b01c0580d019000c03059035501d9024400c21320b0202e1514010841c0c101290b0304510011002051185800f12030742e83c150480e04100d0007500147d10110410201500d1a002c8100c01070071060b5090070103207096101c0c0352200141640e0b00c10982c03258000070810804006c128082c200c40802060941e1040a0003011030304200c4003900d01e88103800000308078030b020b1741c965031407080c10807040d10507603541352502000108900c04141c3c1500c034850211040383d41c90182c07607000700c6901e400400c10a2420345046070322850317000c4192084034000c0d407075010000d0000384500f0700503003820855210155802c2001001e03261081c401e805000d070043e0410414007a60050140c0010358031110410402180120307555490710380c5620740c60340200000e1140700380b00030b03039400a94440e030005884c0184c3c11070f17 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 512288965 1250 512287715 512287753
    0xa1214030a0503090609211309060308070b160206060607030507060c050301080d05031006030b0d1401090b090a050a15060801060b07030f0815090a020412200105090105030a0b03 78
    0x40c4400520003106104940d0000e000c41d1303806c01149030007072441d4125520345a82c201700303a022600c45c00390001803540004406c1c40c2c800340200b03800744007088510b0b0b803403c0c0382d007ca0b4040c80c011074500b0790410002d2216194099040c040848683c0100020703941c0405020340350b8407201c001c0d414050280090000280140140c1d00800e22569909440b540b4008669282030104011070041c48428420428181807a0741c3d2041141c03198036000c00d0b290121008207a050035842800341c01318020603a99040302405400881c0c02611034000b09581307554035804c207911051440c400602c0d640080a00002160301c0c082e681c804c0c1042c081002440540c2c0d42c3e145802c403207213980a1491800c000c2180e2080c5604600081c0c40c1100a05010b40d02d07141c07038000140c44100d5498114400c42d002d1011440d0149158113031800341204241c2004100320608110f040081c6d00c207110300c3c10441205030500d465106005540451506031110381c1103032160710341400130307210311034410780c0500c1842962905180300803 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 512290215 1250 512288965 512288977
    0x6051e061c0503031f09140a1d0a030f120902130c02010b0406031a0a0e0a0f0f0c14040515011706030109050303160e0103090210050c0c0a14040605030c0a121403 71
    0x31804d1818628117a0310000051541e03c41910545420056200d034901800700541c05002444002803111004c8090f00002035034110007035682c4a003800c000105034100d0b10a4050100039120034018180058098082d20301c0410001d42002480101c0d44522503503401c0611001c015000114804054102041c1201c2150703005441842d0b14468000070241003030340b100e411001621043c040e08103150315055854146480041c611f2424020080a10024488106443e41e116100d2482656039119401c08109108019031240f032418010400e2410b0502c80e403035071504184c65010400716003030051060705400900480e010354076100c030240080c2d0144001e520400a003004040907a0406030010a902001244181070501e040580c1c4050ba075041c40b01c0003500603e20348107550f210010003050030003030035410746500914014000709134178040c8250142e25401c195420131000d6520010180d46414045000e03422400805050210703030303002d0201070482801071010300044110004c03001d103598040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 512291465 1250 512290215 512290231
    0x1419080f0703020f190b070503071502091305040b06120709051f0e040302030d1a03121b0a111014030f160806181b040b03010306051e061c050303 64
    0x2039070003070046160400c0781007000c038803d80340f044140c0410410212209085d010300b0303228140100c1c00b01d041000400440f20801d611690000081c616100a0f402a4014210452058880690440041441c3e00c00c451040e07400a0240005884100c203100d81d100c0d82e198070382e1540c02041c00200720300c18140211405a06180041800400c035100038002c5815160852080760722910f040c84080303540081601c81d2004411400194801115480c498440d000300c034441e0503001d210541e0061032180405050800004006501402600e00c1c0c8a5110101e100008048881c6200d33440400c0c00c10a420748450003240c00c08071840010641c1c1c805158001300e0b003859600254a04216500d05e114080c0c0810543c1400c0c61502400d101000401a24160310722020011906001030345407003c15804130031800440004a5449440348450a010303842400207513031450800000c501f488514a5840288501e0641c0864141d1a41c40c2007101c0c0e000301e80c11050303501031039000100c04190300384001c40c050045 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 512292715 1250 512291465 512291473
    0x40617070e012111210708060901060f090c030b1905031516270902180904230a02060309011a0103020a0906200609251419080f 56
    0x1810504540d03155050300f1003108029502041100220001090580c07150300c0320090340c01c500303414003141c0f0192004602000700182c06213400c520007008140710091b1400d44043d521640d4030046080d01f41c902510a010b1202c80c0d8120400000160358070030040f04045203408616803d4000000d030030382070021a440300303aa803a40002c1041b4501001080000000d00f40d1040d41d41c640506410240c2803010038660034410310300d6154042c40400210b00864280500900c0e2702e041c0c0b10354040000350060800c07801514041d0610001c249018541148299071210f8400d480e0050b001002a20f0418030210114900c5420401c0c0010303503c40340914851200304000280300442462969140f0142501e1303541458810424920307810f90011024003500c240b41407041a81d0700c403c1040b5020507880d5241c03003030750050b00b06002e16201c02143d81e80c2d00116244107421400e180c403040d1103d03a110b0740b203444200c1840b0120304e400c5041041e0308240b400d08090302d1b074940c25603502d5001c0c100300b1013003512040c50b00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 512293965 1250 512292715 512292719
    0x20c0d0807050114100815010b090f060d0e06090c0603130c0b0a0509010315180c0c060c020106060f020f030a1b050f010c020114060906010305131217010e07140904061707 75
    0x101e0010384400906d00400104403078098050720840200040c0640020b040700002d02414588403c0454240c3d4440500a5035a625040d64503000034801c0c0b0074125240c0c010640850008840010105104680100407601d551100c4000100242480b0811039500c1880c0800003030600a0f130003d84422500e9449045d40d0307071400f1000600310f0760190205130120700e04020503c60915030f03c440004ca900d4503180080d012026107410b50340c0d451400380041c0801d09010100d00541c3d8190020300440b00755456074060740b910410166221040d002e500007841d801840380041c0244203800e00a10600d00032145020340c0135503240c8a0924034820f100d000340f40c1d100d400c8401025824858210054030450b030f502d200e07050460000303a1610000d001141010344410126075a101c1503928000301e01c1e4407800c0c10b0680e071030311100900f0512032107044281d0b00c83c0500000440c22440940c83d8415601a030700d400c015a01000001c1da0358101100c13094200d903594901180340f40707843c03866010001c3d500c001081424 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 512295215 1250 512293965 512293981
    0x17160c0639080a0504030206041806060c0506131a040308090622021002070e010312020705060f071b0f06030501170106053109080c0105060103020a020c0d0807050114 73
    0x10849000d003084203600031110107540c030098896010040e07441120142d65100488044850340500e03000070354000070000e4006030903412012181c007580040c040c1400229078507041910014480034020b401a0021000150083c583c1034003140341520915000010b046018031481c802c80040754102c010800c002d0600000100800c02150303c50600040401c0d180d080c80c0d0603400d60090301304001d00030010850602c3c1d40f640240a42c40242903084444440b40d0394a0420246601250f02c1080140c01210000318407070810400701c50b0760321007001540d40740148070b50790380d107402e18151103448803d8603002e4042200b40301d03959590020403c030342e404a0503504202c0c010840601450b000352007607140c43c0c8108069111500311070050804084031b60500300380400c111502d6007101c001c5200240c50546800d040215140180149400070b10080281c1d40d14000150100d00c1045461409030f44a15004502440d000320381c0c82c006481141120700f00901ca0780c80900395036900241108840d08041003200c15 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 512296465 1250 512295215 512295257
    0x2101030602070218060f04021c020309071e05090f0601020109140f060f040c150c081215090c030c211612020a081803070c03080d1817160c06 62
    0x4d240c00b8143c4d40020304001d00029010018440700c113001e81e802203a101c0b100c0b10545d41610400085070f005560b00e1800c4000301d52510314500074286480d180041821400d05070007030100507110050140e0502d5101c071085100d400344028000703811592503100041c002442d4540241c10910108014880c0c0c2c1c0b04203e4480c01c00703100070400121050344c542000042a00d01081b58125240840080144428418100c602150fa01c00240c1a01d1002458250780e400383c030178240c49a103814401a8550001000308450040140d0710842d11180910110710b0b1503c54034010420f0f100858122904c03205840b040c0000054129200c04019480b1072030502c1c0c031600003101c0c445242c60302004604d001190344000d00020b8018000300303003d10043e041002e028200700200c84050b9001003251015960300e18000505902144010342254207103120f9081c8000010404421035601601405206029140b0b2010541114a00900404403092040301150105c0c0038040602900c1c0e45420090107036820032541 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 512297715 1250 512296465 512296489
    0xb15060304020f06030405070807031a01211502070615150c05030703080408040314060702010f0905030708030403140a0f1808150c2505120a050f21010306020702 71
    0x181504004120043c1e850030b00b01507001c407044856035280e40b03036414190310700ba48603000060b1a2089840100902008881217010007010106500640ea00c400c8045503020003040e101d070106109004520014a8203411003009020601d80103052030065210013007a02c0504101410110321590140320003603030310805048148141c00c00f50904606a940c481d607070312941e007000c0c0030000080085020000b084048400071504a000c4414840c1d00d07000644e19030300b003591078001540c039100a010300d100f001d000c0e1030000b41d0070030041c40c1400800d440710841584000d104078100080c04da51444810014000761a5907100b0350b80700c0030180702c1d40e200035040054010034100c0504001c50200001c0400051250354144044a800041c0d10b810a11920798041c621800400980c02640c6800c003804104501d1001402102102ca00b40c91022140d40d481c8200050f820025604110388010714010038001c1c919925502c00c03440c080303920b00042c00d101c180203800c01c4a580f030300081c2c104150b1620b002c0300700c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 512298965 1250 512297715 512297719
    0x5030106031502210f061806010c06110d092619120b0306070f020712080909070c06021206120f1018020a0611211b01020d090b15 57
    0x14150942c0c482031200c0d41d0b02c60ba1248002d80015880001e0382148000c2c0000801c01d500e088064100402031031036008007202d4050003201c0c0e5030a403e411840640586001e114107845003c048001902c0f100054035440c21035081c560400c100c40b2082c40d1035813094041340c44c040c143da8400c100c001e17a100d000072079000c5001005403201340240340005090700c1d03003160303240c64034242840346428140c1d0902c003816005000ca5490b000ba541000007103a0441c000582c1c2580385c4d426950690344401003c48540342895018007944070034080c80401e414003100c0380741c108038241820b88200c0c510340d0f58542a41e00854502000701314403020300143c0d0819618a180c0c800b00c0c1070142184000c0b03904200e60700c100074900080c0498a5000041540403030841a4000f960003400b030800703107501c6050180607480c031401c07030b404140716008054481e80b0440030820212420410f50f1883d00581c1007100103c501c41c802000d40556081000003450b00d101e10503000040c2c8076800004040c9407000c0c0b401c10155402070303168 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 512300215 1250 512298965 512298971
    0x1e040e18011e1a040f1b32041a09041b020d031a03010515010e06120103030804060204090e0601050102011b020a020d051c03391d04061e050301 63
    0x80b05065810003401407a015008000510b4880040781d6000050582242e030b400c14503000c088006030707500e5000385000454084505070321200b80c46044441c108000045030040080346241440d91504000d20b2038040074054460f170406440313586000c030004511444240e8080d0000e40780b45281828003030308424130340182c42c183c90032465020103074942d1107481078001056600e00391141c000f04140e05d0403000c00d01c0130740200300034500380d49c1c0007a0041c801d07800c00b40800e8407003c40c8003e901c4e000c0126644100c4c0003005030126441c41c0d40955040801510445226400f40804940741083e403040d030f181c030030540000303007550b5240038006401c48104c1b41d801006030313040d0040d0190490300014204092541039551108603001801c00500305a10303100b08480301000000801103c5034903400204501e0114440b58078a82c02400c01c05030100c0c0003000300ba280f503054a1050f11618003c01361030020030701c04130324811500a11030010b0100c034407903042001118007114401100c0704240e5000c00c09010280c0c020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 512301465 1250 512300215 512300231
    0x1d060c0d1505011e02030c0f031305061903090302150a05100b1819031703010303080a0501180519050c121008070b0a03110d060e0601020c060f1e040e1801 68
    0x30440103003210416132640ca40707800000320038400c100f1161050190420b980d07440c017001c801e198aa40c400060b03050f00e80c1210794040b4091601b10304840c0e83c0f500205061401200401054001c0d0440000540c1540203030070380c04441450381c8200c148a41c540c04000074941c40c107a911a103401103683c0007610407650a200c5e840300c507441c0c0311058000c20700c101c40406511043d0282d0309002074058000501410be81401e4056034401d00020b503041e04c0c480d4841c0d59071692885d0642e41101e01c24801c0b10390b5580314504110140013180c3c001504003c0900703010100d003401e100c2c081d094070310980760442c0c0741400003501c5282981001d8200c1e082038a15130100c64091900544c15a94035280c0030b014008640098180d4841c2e0103030b8007100c1c0f10000e510f10b075030f1103140d105403600041c0201c0c814042e99505801c0000e25035032011070401a49013000b00110704148482083c011560401c0c0c064040c420034034618904c01c196007001500080c010502401610310b072482e0582c03450440c803005124680e042c0001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 512302715 1250 512301465 512301467
    0x105041e0809060403030e010809160e0a090c032f0f01050f040305010e030424120203060406050a090c0f0c1a0a141303110309131d060c0d150501 64
    0x50500030300100280d480514090420310032520880480943c00000050f0000070140c1041c0b00a9200e8001d0300ca90445941d099039080c1c850080c0a131080000c50a85400d00c01008104101504181d400030000b40d12001039940e008000ca40f0342042d180e400001e5442c80c103e010b484500f03400b828580c0700c900060400b28001c200b42402696400d410b01402003012400407c2d001d09903001190403000034000e0345500c0204a40f03c0c0c0c030901810660040040040d100ba02b0314485106118009a4624004400441c0140029000640714507403003600c589001916680706004030000d000a1500020504c25201000e01511810707807005050040c440303c427001084c58140401040c8e60040405c032103503034494800350002c02d8440358003001c100300f0009109210b200d030254041c00714825100e0a60748158610758581c0c0317010703d00b000e035400f0034681c4000d15140b00a0308140e4040c00d01d200341c5d142c0403040303014881c2030440460303005903032100108120041d942107028030030a034200402054205424080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 512303965 1250 512302715 512302733
    0x70302370605040809030a0f170c19022d0a05240309012c1209130e010e0727090b0a020309280c0812040e13020a090501030b09010504 59
    0x4005007007656190002020302c00b1010480d00f40c504002c0540d8194149842c1018000d0501031055414088009207a040108a0001c0b52141001d48004244000702001d5440c2030b0002020100e130003454074905020002039103003101c102c48400d080300c0b03059100200144040001164081c07403040c00f0902c0d000c5402d103000b20001c9540003501c0e214543e07a40e941c0c41d00c240940107140309070038448070750786c640100c44165825000e007a1040805a640d01c41c0e56042040040c000c0d005140d511140d0b2003407601403c100e0354840a00b0143c0500007242c4103044000f420309050240e48404a00007049070b0720098003011405001120304802404c1246d6036040e12400d20404009096101203580000401e0345510b0812004054215040304581c0081c1c0e4000a00410780003000100c400f0424440d01140415021070444110b21101c0300040c10545040c4140ca89400f0140c8240e10b588a2100c00c0400368540d400e209000d052460400b1030070b94518a4001daa01d04002c0c005541d41c0d03d410103010014920034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 512305215 1250 512303965 512304073
    0x40c030b0418030c150b090c030103110306040507120f120c02010f14070f061d0309010f02010501080d0513090501060302070c090b0f09150904060b030f0304120b0a11070302 76
    0x443d00d0b04982480f030343d5900200402109141d0040d1f501080028aa41807001141a2481525030340c80c407110890a0650f01c940c2902c00400341e0700141c109000c0c0d03004407101350000c40d0103615086200300d2283c03030320340c6012042062880040d40d00c03d01001556004080c0d150034000b00e10f80405040e542c541e04523814010701c1c50040481011481040500c20943c114084010b40b01c9010101c0c0160b240c1c415039689c0c85410780e180401c003103a490210490041c49064100c0c1c0c6060302802800d452040100c5140d40919214a20300e000414085015000342c455a40a4070540d107005a98590318207104140f401c45074403030100d650030300040c00c183e41c9900d411210b51803029501000903403035a2020040e00c15510340059042850300080000703029a83d013060200007020740a84850401a5030102e4903071060b0300510301407441002d15600007560302c00910351b20030008440094500e44101c9050380340e90120350160016030211022010413441c817103284888140301070003a40e1030182c078107942507440319003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 512306465 1250 512305215 512305223
    0xa12031209020607140a02150403030203030612031b0304030302161503111608030618010b030c09211b041b0c05190507080d030504030903140c040c030b0418030c 71
    0x4028000031500c61100340c88191750300004c6980720410669045581e568810300c1680700e0302074100c9540d0130351200c008503415250164003a52566a80c0014410345403e150305014240c8001c0100759031b031401400c47c031202d184181c400b40d90f865182d800c000b854180c100c03002d000d002d50f481b6020004402010364030400d09011f418003003021071003546803c80e5405881c90b0301c4818841000e40000700004140114480e5400b11207407000c4400003a80d0741c41c001424016141c0315102003020600c0d441c03c68000e0104404010f100d01c41e64005003041c031500350804400f241260744600c420f030300480507004a250024009803010090390640c60159013188545880350f8050244006800c001e2180520a030405d01c880c0c0e0a880d4413041d00b1385044c40e62004540320b11185800f500303101c011118407070301501c5d020b15010750f5540403e07400d5451700700c42c46540c507490407150300c125181c0c509261a140601d41c3d641c140c0c0d440001d4804014018001a1402491003000000d012840400040e070418900d040d21500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 512307715 1250 512306465 512306471
    0x13180203010518091f060602070b03010501140d3c0504030e061e041403060702061e060105091009050a0b03060d1e0602220506090916120e010504020a120312 69
    0x200e03002141000d4210400c09030102081760084956800b541041003220141d90071144101d0b80c50000d42e60720b000a0003003600261000f640c1003000c609410141980c00700703a0100003a483d8000254090041d40700500ca18403000b0407140b03400c064502c00100140806002040c0310501c2d0540d030003842e00484d182e98510402c00801e241c01440c1c05500c4030260b48898000890f80d8070b4403146403c0c00b2802017007225201c1c0c07044400007015148003148250140c4d541482c41c0c8200b8281c0300c0d10b941d11140003400581040828049600d56548450b01e881040520342c0b10580743e2404d100c14010040c429412072481c00400300140f0045803a00c0070001800394000c0d1444212030707031030400d0092006117034101030001c600100d020003c8442d1705014201112540d10040710003a911014490140240304004e580a820000040c41030800c2c800b002c40441054a03020700c908900420503c11607940a0205555070341d26810081141800e03004800500002050050f0300c0c0c5503558000c00100d007038481c11000c01d403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 512308965 1250 512307715 512307721
    0xb070f0309240c111009081c050406061a030c0705070e01060503011e180c0e0a08060f06060708071b030209071d0f0f0d0f0813180203010518 62
    0x442a80701a14a0394815501c40d615454030082100c0403800240c00d0541624104200389801d024462421009540101500c111115000b400d001014101400d582c2000c040080020183d0000c154541c401d03c5000000f8160819080c09421a01030b07800c01c50038409000388441d00c0040180c00d503580407080f002c0380755070307001e403442c0c0300d41448019400910b20301150000810751903000800745059810f004070340030420710314006400c40ba030300611030b01501d03114007940f0082c602d245070800105010079040c00c1d01d41c4140c21001c1001400207900100503900310605014009600304001c541118003110b08608000040d00c0710041c80c0f182040007070812883c0d420940c0184040048200215001484040f040c03401c2a0064030302c1c030b11f03a043c284405207113154400c0d00c1d1078140b0b65002004030281c101c05021900600f44a01c6032030b680c00c1034410b140c0d40e215500000340e6a000802d86c0c904040d411000c0c051038012401182e036450004404018010b00c010700268560003003280310900c0380703143d03281207407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 512310215 1250 512308965 512308967
    0x6012102070c1706061e060a17070309050f0312012736030203041406070813050117040b04020d03050904090605060a09020301030b0106030e0f030408061801090b070f 73
    0x200c11680300402e05420103000003010b03a41d03003202c81c20441c4440d0030303900c06030b036424108501c001c841d000f1815240141e0750b4014031814408042c21030903401d82420000315902c22654111120200c0701640029210300300c18040202c02e00000c054144888011030601d980400c80000010050140402003205103d01010340c1c01845103881d006200103000f040303100071201401044100b11042d10580a080200074030a803100135011280f02601540a103003800e0514440a40806420b503442d0f5001c3c40c1231240c0b00116003c00b00609004440610354500c0c1441d09001516800d102540800510590401c10000c541d64504081c2d0043e070440d1310b29640c0c941d61400790341c0c034050094807039000f91401d10602d04004007980124001c01c412511750703c1c40ca949514407400da200074000200880281c0300100031250290f001000015042c03c15240c40c003d10840300352442c0c110364800c1c15039600c28001d2103131019940c0c3c030720404160020000d0180d2402d60710b0f2202030800182c103a2080080b015038102e205 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 512311465 1250 512310215 512310217
    0x1c0305090709090510090317060607021815060f040f150c110411130609091514030f030a090e010b040308180118030501020309010b030a1e02010c0c06050705120306012102 75
    0x44070f20200c0400083c286c03410001d04824a202c40c0e048a6103a20f000b08070303103240280940728125402001184c11200b00110314034501c4028007640c04401d600c0e240b900c1c00b83d80f00ea01030140d80c1d124201c4180c440d842e1400001e468152a800b032041002c40e2010340911030b5028a4402c1455004035104034840aa14040340003000390418011880c41d0209210a408100d000e00340219151030b90783c0150030f44c031101203d08545640d18800c103041310896003004610101c9000340003a0000400707a65480d440c204d155402d643c0010311001c002850401c0c140304012400d00040d01600000f102242000c0c00c41d42d80c00b041d0700c01da08005411180500083c01c5a038411407000c007403802c842200025280c0d40b4540103000c1d400c1521040469400d204564000381030020300c4443c95500119200d0020140c03800d001300640403602d0a904002e103115800000c01c3c040840f2800602e01d580c0c40c540d80c2d41680c140b580c1403c81e1b036a0041c04141042042c403c00c2d80e0310100107101c0340340c1c5080408000080c0c010800007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 512312715 1250 512311465 512311483
    0x140c0712061b0f1116140103060807062007080a0b10140a140a0906080a0215190c030e091305060f0f070e0301020408011103061f02030d0c201c03050907090905 70
    0x85082481001c640820b42c12041e10046c482a2401d210041c3c588000030340702c50310350080341c00041c031941010340d101d032446000070010348010303094511643c0c48003620341c00c041107584161103000c040c1e0103104110070a4060000200004080101116414400070f20360320050b200b100c24003120508204c0562351045082c02c0207004001782044000d03a1a0001c85d191025820141d10a4030072407a2410000c141404135049880764860868188810350300644504100d140c0940c2007220100240078640c0f200103c030b44c014103221440d5960480685092450110010201e011100c070180900c50442c03119200c01e0707001100d40c1070640d810312040020a009010b00c0e032250809609041e100c0303214030701000045004050546060880041d884907480e07101407160695030040e07000700300d0050103440c81e6000004c0c2e03051610f0314014203070551b82c1384200e032807400031040d059801400271219580001c080c60140e01c1c00c941014406858400005500c54600388600841b098941400e181048020712171b0b16a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 512313965 1250 512312715 512312743
    0x903020c12010c09050405060a0603020c03040b0d0b2e0806240a14070804120609080304051b0109031a10030803010e090c0a15140c0712061b0f11 64
    0x116a00d0078101a4041c19440c11840c001c99501d0901007128109130081c1c0e40b00e0b45000d030010740a81e14000046000f90301903c24081c49010911011496885a00003003100c1035580c0c0700443d03020404000c100e4640b0700d0502e01d800b2200040403c4078a05d0440c003840c850014103043c0140141c0d03414020903c45858069640c0740807150421a400c0d500b039000c05882d95680640e02d81300d40148100199200340b20700700d00130f823032950240802c01010744204000c011046c824400440c042c41c6075541ca200c0c6030000c1d00d0840701e0380c020031412845002c0d01d2a00c0402040300f40380401046103581c42e1406100fa001d449030740303030b0360031000021002d8000300021801981c0c0140b244c1d549603500c841c80441c3c80416500b5122a0180042d100300c00c0c540b41e101401643e4102d9003400700e0820038032058414080f060b0344d0141c3da6009025160422406015045c000d0070480c500c200c904400c1e1800c281155101918086203d04000215003001e82c0000200c0c0003800ba400c06800da02d2690702c0380c83c82c1c4205111481 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 512315215 1250 512313965 512313979
    0x30201020c030c0f0609031c0b0402070f0303050609060109180203041103030a2304061b0501060806100e01052b060b04090305190201050c0f07031b06060806160e01030903020c 77
    0x529443c1c000580c850168070100c144c40b0030b03455520b82d09881c5e00c00c104100c14a10b0b00070540f411740c0011a445181a000b00a10040c940720301d0750740b18511400d11503c00d034082540c071400c00100d03007407450765540e00c003c0919001c0e0a01d0b040c00c61104070380d9441d07441a40d20a0f030110001d410040c50410a40c1c0462005049075124469604002c00c0c00b04d02c4a0021044402208024603c01030441642c2c02c3d101c0c40d450b40704541c0f402c0b41e009a00c1c000a0320342640c0941d2580800503c400040c8010303801000c0e022103c641860510f1083ca820344010390046000b1100c0b1285003428154010803441c038114441800d00c1c0440142c1030450182100045099020380780401c075604050b000030040c1b40701652503036031100e01c0c0c02002043e401c0319811603801400810800160641c2c41ca400002e08a4a100e0705001a64004402c00d0100410000104640340c0c1d6861a0030702141d80c041100c181d00030b00c03440c0e1112085851507001040d42000e1a40141819141c06405c02050f0007400046111307600907040d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 512316465 1250 512315215 512315227
    0x80f0304050313140607060c0e09090d02120f07082a01050a0c050903060c0306150c010603020f090907050607111c02090a06050d0f060e0a050c09160c0609030201020c03 74
    0x10307940b81c1d80300c220961001d079509000054a1800180b82e1a03184030000c1c00039060503402e0722147e001e0702d4030301005402c111001800c0c010315a82c080800780a00781c0d90006058078040ca40010380340103642c2c62030701800c01082c0b0000b80f03030500d131740b0499520503800003049413905420740d0100140300b80c48244104900c080100c0424120b41544a54416460b6000c1440800700e40d0030251034a100e01c40360785805070003000025548040c0c5000035500900e0160040b00b6816002070b64101d590490303c0312200030f94480c0d00810030761401c1c82c00922074030021500029542048000a0303078401c01c5208031030182c2804551a01407154500c0031031440c1a01030011270f22203100c1524060070740e0200804038422a0440046651100b4a21500f029550058581c40150740e2540740c103100f070070210f10203c4040740c44d030450407102c00c000d002c104641c1d88210020b1030340900c007104100703144d4001041503052801c00711f668105294002468040c1c11b0300f0010000e8441d1045c10100d000e4414035040c0d4000e84000504 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 512317715 1250 512316465 512316473
    0x11b08070201020607050c100e0f010c02070e06090f01060807020c150706050a06060c020d1b0b0417160303030b042405040b030703050303061201093305041e080f0304 73
    0x904005100364284d410701c1e695110151050700880b0700822656108101c8403a001c030065100c0701020307501d10b0483c4c00341407886800500350b4801358400001a04904020083c081051001641259044566550514010510b075130160414400c1c901002002801304103940d00a00c01409003a6014000301500e1480151060440e0710000c02110f4091600300001d00c00c20302031044c001036510580e90000c202405400f0401c107069085820744154000441790b1403000c81400a0b58014114074032420380751460171000d1a5141c0000c000300b0f00d280c0002e00840c40c80c00c01c000545040d6585801d0010328801000e0100b00141441c0c900d04c0c030130540102c004002008401220360403500110390503c10010a41c060588440c0d49120061a0343e100b400451054609903000b64502d0408a00020f040348c83c5448405540c8150005006640c0c84200307005200c484031546030100750084401400141040c0da210105450307c44c000281c4003403042003881c10056008203c49211140d40c1c00c41d0345a00700380c14 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 512318965 1250 512317715 512317717
    0x9040b011404110301062d21050919050f06090303090d0507050304060311070b1e010e061003110f0705010605012309090a020d09030c0506070903020d0809011b08 71
    0x40401110702403500004510389400355104282d009044581180d00c0e045045c1d540e115441c18a0541110031242d000c554010b0b40040f1480740a550f403090b22201450450040345418121903020a0342010200440b084000a00380758500e0a800c41d516516414100a42401826454541240580014004002400006103000d01d461500f80c503609105418182e449100f2514020401c2d0024401000880e01070342c829900703a0380c400034080c504529030b55400d154072800c44490615a0405001c0c9001401c032030501c601421003006018424181140005c2040301e21140c0d800815442c0c030756401142907140b082d10302c6031250b8501d49440347e000b882c0090107440305000b03143c00070f49004a041d00d40c1d01155200310341d884000d54410f11b000314a8081c804032290003481d2840035a020403080b480c4400c284580d212140c0640d50342011500c40f8581142000390140c015001c10105000034400b507941c002c40140341c2944a0810f603901c003d64001a120516820000c25046110840765818000010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 512320215 1250 512318965 512318969
    0xb060909010c020c06030a06080f370609110a06020c0411030106050a0e1507080304060606030c0e0d020414040b18030711040203070905040213090506060a0c120c0209040b01 76
    0x881210403a614028040d0880d00305206400050780141e84110703190600d03c0007980c00000c0710ba004100c43c1e449140d540e10344510400805816440b020044980001200c41004e01d02e0501d4840c1d595404100c54198540c400c0e0800608100d644040070030810054140050721104044c054a4815582d081c002c0d4880400055060189040c8a150000701c00d081007181e06943c990b89505017011000c80080b228514807001058011104c5444000d8008072000900021442440056502d16183c500001522034651004051604008614101582104203a8000c22003a283d9015180e843e00000d40030303224501d4500310480c400406e0000b0701101d03640091103507102c50704000480c4920360040382d0324441c00390050b18000c488520b021052801d5002907402220702d00e0020303041070312480040c01302d84c00011071200081002c20104010040c1d0701a00d640428100c80d003500b020200800178229000001009110b0200c2001c0c40c0e890a011781c0100c4520341d0081d00002541c60640707000b100c158003c1c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 512321465 1250 512320215 512320219
    0x151c1b0c030311070201021e03130b0910020a030818030915030906010e10050108151909060608010e0f0c042c0c1303030e0a030218270a0206030a090605040b06 70
    0x112105041002c007500807207050b05e41c1a4020120341000344c042d20b0681611112508035400100b140075188000811002e0183c031045100c1c1c1e46d2201c80000300113400c030112041e181590071010074a00440d0704280d03d117074050f030800811006515048406802c600c41c0707040003648008968074030540c2d03240720303800341d44074040c1d803c00c03901583d0700ca00d040003030420200c801c035a40c000c1000081c0501e510a00d4007503000b5180800d0040342020240c00141c490418909041244854041c10840541c40c0d004500c0108a6410110b006504107811000c035000b0081c0508a007008a50201d0035a0301d43e80200c2d4018105400420450201070401c0d40c0307500c000c1c1388900c9a100f0000041041c520156046851010318800c02c86101807035036030b0070385070300c88080d982c1ca6000700540800030141e10b42c2c44002200d0507490081c40300320320b481c2c0e12000f0305080700132000700590120343c403041180d18002001c2c0004da804449003a265a110f50041d4060429594014012800c020501c010032200803002030142c0f1003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 512322715 1250 512321465 512321471
    0xa030c0302013213050306130c1a040b0702010c08030a050f010e01050607030e0a0b070f120c0c0b070f06061d09030a0504031b1d070e151c1b0c0303 65
    0xf02d1100310031540c200140365001d03031800743e00e0340c031800300100007000c0c8070039600a13644890350303201c3c0042d040501c00c60b00c1e1a800511680e0701020081e028980d00050005000140f03502450724640c00c3d428080c0e4080c8100c0344000141c15025603004400b40f0010640c060280755407442c01341100c2c40070f01001d548000458985000215a0000300d0788400d0582c0c41c041e0015080200c1910304803452800881c455400020b051400b003548600600100611750044600d91098100c134548540501c0d140c05102040004040a0760b0026041740a030031304852039100c509444054608242d0320b40540d480e00102070a15140700001e00b081560502c2003124051158030300199515200c0c243c40384a401c101e000041c90400007400001d860b540d46842d2a0882e444a1100701c0e15540002d42c1c21506c1e41e0700b000ba0b0340400080189450340240c41c030dd4003c5c4252904d40d113800c03448007440d0403402541028400c045204c12603012100c000d50116100710480d800c402c15102942402605da40b05284007600080c1c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 512323965 1250 512322715 512322737
    0x1314161203021c0e010509131a0f0a050f01050a020f010f090203061612021c1409060c0403030203040312030912050a1202030103051915020409060513150905090c0a030c030201 77
    0x1180d009450f484082d5196601204520401180d8640c001c501d0103130311010505038000c0000e0640314103503000042d070f100c025100610070304104820303108880c4184103111030030040c0802e0311f0703540320380070400001e013403094403012090f4040c0c0c10000700c0c0f481006a50710f00782500130480801e4118902d064000d07420740d0442d4070f03054000e500c0750002d103540b44046071000c8400e156544055004003900c254244600242d00c40541d402d01c2616002c50000c084100d080c400d100401e40240805900800980c02c454641032850368060740300c0c02284809042c10703101d070030001003d6000341c000d1103010f540030712080c0b4036450f00c1e5400b41881e08800c000034000f603441000c0d102c11000510881e41a80d4128004000c400c0d1118a001c200400c0749004980d20a01814170b11084d0031a40058005001581c001003a07050900003030006802e9564002d03528503080095550443c000c4541020075105c0c860030100346541ca038000d031441c1903005040c440e0420141c0c0c0740002404901003201060340c1c400d0340c54141c825 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 512325215 1250 512323965 512323993
    0x8010b18040f140c091e0c160206040905090f0303280b19030605010510021002070203030f0c0601050f0d0305030f09030c16080d0513210b13020909010203131416120302 74
    0x80c4032490404074921b00c00c000b00e801c40703828201510100c0400c5042d189600104d50104100f60000e50100c0c1071981c0304c0040c082c2c036900c144600f13001c1400410045085180c90294690601034030240030800c08100c035481140018550000300da0444058058241401314208070040d205503840281c50f441c0c6044008240c0380340c110030042e2002c001340c1c005c0500d035241d840c0c000001d5101e40404c81e0700d84405c0041540c41e40340c89015000d505a941c014006541c0f610090217031718031440c00594840c140c40b46074100040c0c5c0040c00e070386d000214140c0d048080c0d5101e034842480d5114041c1c250300248a881140c0c0911015540700005036400c52050b10001c50010b20207032224000d071491a2803004c20100107200d220740115072810a04d085048410382e100c80703031f221000110010740d10081501c020410790015070602c1178807150400048002140303103140690f01ca4882600520000b880d00f8108007681101c48410803400801602104410000c15554050800142c1d9041300480150090307a0940001d9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 512326465 1250 512325215 512325241
    0xf040e180c041b08150301110a08010906030b130314030c04140d0221010f06090203070e010e1e010e1201050103020108010b1207050906070b040c050a08010b18040f140c09 75
    0x710056242c1030030740f10600c0c141a00d6061005202500d01841c007000c3c1000c943d001d028404d80c4980600d031603543d0703200f6281c00a1050a050300014001c03410101c0c1000000c0045030406d40c01084c0c0c0c00704030b43c0d98202c0c0c60115900c0710140216005008040705000c0d0503282c0c2c1300144105c60b400701c40d80c10000f20003024040c4044000a0107540142904020b00c0b40c904034281900c2d070002041c0000408480c0c00001004a8050f0703005103501e980e0110412a501d504445a441013a0f42420107545840803d000501c21040b8030640c0502c084d040001e001040c3d016280115800000524240c10715212213000c9d4020507091009034001680440001204011041114040040f59041a05603900d900303003524998403450806810060400034100403a4500035664041c03441200c40300015032521f400c100410b845a0403034400782e49040340340c01035a640c480e204500c100e151450a15551394900300800c11100307000d00075009065104080d01c001c10003064062103950129900c400c01e4840c01d00300382c0c032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 512327715 1250 512326465 512326481
    0x311010c022d070b0d06030c060302090a0b0f130e040b01050d05060a0504020f0d0605011505040e060409030c020d0606080d080103052e020d05040203070e0f04080f040e180c04 77
    0x20b10795010300718a160003403140c428014140100c04030f0342101d503a0303201403c50303920000305a40407541d210014410869101041c0000f4145840d00b54103000d1002c0016842c0800e40c4904c292081002840389041d540020170707100d040d00000e5008424550b2821150f07055141110300300c504c0d281050000c01c003850201201481e01d90000010441c559403609140c00500000e002a68480d00e8244070f0f40c40380d500c10400301d090034411100400c0340d52500030516201482243d403101400b03014030007400200c401c40e00c00c5074064411100410a03a505003816101c603403840d00080d400907500411941481140d802050445841c182240c010341691001103400440a00000700182c004c01030714041a510104540e240b0720a9406c809203180107681d41d07000320707030000d11300c0c560a945490810027989400d121501c010244010b64001c00d01e08072049948414004000928001010071546001d010410596010f49401b80d9003080604006010f0035101c440c800e4403609902c254a103000e00340c1450701800031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 512328965 1250 512327715 512327743
    0xc0a06062c2502010c020714030d030506040609151a030c1204020f030d020c0a0b210a1e240b0a0c08090d03080708010e131101120501030311010c02 65
    0xc0d10081041c0042019400505109112000c0c0b403000d10090103149070030304400c0b400d5000080c0211140902034100506a40b0408061282d640c135004240c40110b8410002c0c01c4034079000440d9614480094003c165981101e00350503e4035403210300c0390058000242c15283e00d909444450007040e89030b9249888120368101c01c000c01446454503810a5440c8207402130710003010303012000504401300f07140280014403000140d1084002c070b00a410056552005440314550140ca005039010390030341c6034009510f46113202c82122000845c6407400d0340c0700712078000d03448001e41000710b81d640c0380d00301504d0400113040b80007201e6094108441d00010124003101c41c10b104060601101c010295041111410203840c1c1c0c19080290552594511255056951290703c50003540d04107030a008009110580100d0107102c01e105c00c0c84050041a02803616140e40808a04500000c120040b680707119600071418141e818400040b0030150040b10103d10000e005001b000f87c0461554102ea031410700b60f132149 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 512330215 1250 512328965 512329019
    0x303070809060d0905010f060602010e2104080a050d0905030309010804110a050603010b2101030f020d14010e1c031404170f12061305040827060c0a0606 67
    0x2100203061400035114070a00140100d0804150703024600c1911400c2200f01c4080c0d550b2001000b0320f805500c80c00b0b004e400c2a00c000c01400c030000a1450792040300041d891070b102c0c0f500c2400281c4000f444100c40282c180c42c000c0d19691011403034030aa071030b02c0b416540800308204080100d01c0c0d080000550300710401c1650b4101e001c3d1140d803a0103017074200350340c1d05542103505e588021919844101c000c40c0240140ca0685070380b40000c2d04048848000310a5003020361b00c503500100f010030300400c103c544042e0121240c0c0640d51480c40c024904a5000c807028029500300400b04c0f0f582d0f400072400c01450001420107002039048280124212504111700c2900141028003050128a00d24003a50564a0500d00103290140440b03030802e580e040140c6181400203454201b05807410144203080103400c0105090081d810659a070035641d024564007072141d11000405042c1758416410600d848800180c84544c1d5692034164154a80405003419980c050800c0300015071503070103040030761130248203485903 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 512331465 1250 512330215 512330227
    0x70c03080a0302040501031d0d11030c0a2105130306020d02160506090c0102030406020d0311130308030712050601080f0603100c0207031a07050301030f060f0c090e1605031317030103050604031b020303 88
    0x10340e0951800391010300984000d0050201b0cc000401182c0350f8a03002d40d0510744a11405e03201c0450385c014601401c0f042050070b009002c0b0071f8000d4200340064030b40c006c0f070160301c44500481000080c01244a41d01180718002070480511002080007809002040156811001e0f9180166528400c80c8142001640604003d03041c0310710980c44803d0b0b2641d50900c1c180740c1001c509548a5161917500140c0e024000002030003102303600601c5480e4035504040041c801481d03e0b000103804102d00806120348050408000380e000d681c148241e40c28241003000c00c100005100744003e5070f8243e1ba0000321744422100b0781070758200e94400c0c801c40c800c503000e5942270f02e0341c1c0c25a0380c1c030036100c04c0d4450204c0300b480d10713000288035104441c061020240003565034100401d25010b103002540c07901620310718000024814202c42d0a07881030481e9031103650108105400310062401e09511010b07111003a828500c00300001c0200040400d03103074010313030217076a0b4804050a440b00c0d0111013000c1210096160b8010020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 512332715 1250 512331465 512331467
    0x1e07021215070c051c0906022104060e0d0c060806030f010b030a0320060a09061a0a03020f0f0303070813050901060807080a0b0d030306081b010507020402070c03080a0302040501031d0d 81
    0x8038820184074600f0350ba00c012600340005a600c1105d078200001c550132140070b0000550420140d20680403e455006118214030803031241e80c4035a024940403c4400e1507500c00c1501d071820156082640480101034955440718020035004090310841c0c406c1c0207048404400e4401400b4140082c0001000b0340503058442ea0b00780c0b0aa582d10795030192070801101411011003042c040307944600405c002c04941451a40b81c401c1c00c55108814918031034040c0d170140a0192103801003401580c3c2d0544242c0840c40c0f00400085810050f00e00c3d0a038507100c0050032800b04a42306010b404c07044a4400552400d603102c10030440300850034019000002d1440000809040c824024070b42c002005c0d100002d001071001000c281d00e0103190a00703602103511040200551310040022010000d000b500c01044c42c541200000d2191082d80b401a200f150041604804e00a0744411003000350380c0a000569900302c0040701401a4109114450100e0700c0c00c2c9101d950000b180303451058900904010384141c2488440c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 512333965 1250 512332715 512332727
    0x100f050f0409120201090c0f18050a0605060a2006040203190f06090302030705060109180f0204020c2406010203091c0f080406110c0a080307171e0702121507 69
    0x1984550150311101c0860118403290040300b80980a80c0c00415024400e0601c0c99180301d041d0710231a50202c03800410411326100310803281040700003da0221711910389030030040150116400160b4000400983c00442a40004c00d00d624585a08140d100300c0808658080e140c0808640203901504040e05281400c4d00808801440e1840744810082000d40358581f0012152a517408501681c0001800780510104100c558010070404900703101036003001b000300000198140e00141001e49001d0000110350b1030750140c40c1040b4000c0212948822480b0107d14858070920715080a0f40803840401c81c1ea500c044112031403240c014052104080e17900944148805502130150340143c9203845503c001040c0704000c02c02001d0903520302100078254280c0d1410b154007041490312503041640c0c10080500b02100f9241c1c080e4010304054000350480e6200845481841c0400c4d4410601810504646500034040c0520500070350b41948801c3c4181c0089680340c2c0012082c8620021180000710b0291042d5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 512335215 1250 512333965 512333989
    0x30804080304150603080a02010506030a0507150c060507090518070804170702090a0c1d0306010603020f1207030c09061701180608010504050f012301090f0605121005100f05 76
    0x120f5050380c050041e2084003183c0c05030300200e4030391400046100005909001d010781201013100076001d1044c10303603920303991540d4520548201c11044400e50700c0203401401e868485c250880e030144000e140c0b940c001004405180202e0788542a55914913045154818049115410a8807044860b4071145c45c2c140444030141d0000300e840904000000044c0c44800c211400340b42d5501010510441400004d419a010310450603075440e40e40800c1103050707800055290449015040040c0d54a2900d88140010f01c0780e031402482100c0c800f01400f40c8a98103600840045265982c0d603210591240800c40d014000c840c0c240760360040140061002e00c03091500d80420034504600094425a2911490300f903c20480301a107090300441501e9110440038010315031f15410b1188811124042c80ba802203102c00b06005000301356a8032a000c00702c41c10b550340103201600006003e481241684c2090640d030358038490113009101e0405010030f448c681180610000d482e01c0803090300700c884c107020904c28008004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 512336465 1250 512335215 512335223
    0xf0311090c071b091a0a1403010b0a06110d0306150f031b0908010605010804020d11010c0218070207080f0709020306180c0706140709090b1908071e03030804080304 72
    0x1084108002103c03407101120a94080c81d18040381850502c0705011a050103441032040d64088151410302d0741c400c3c885d10161a17465005102d40b20220022030f005100c0c10100302e400107400348001c118590000002071004101c0000c4625403c2c14420880550717101c0d01c25a9030000400c2d02010901d40182410071003000640b400003984c10303511b285440c40515000304940820303040401803203000303c01e010340302c05010300b824005034500b890ba0100c0d10354035000c0009819040ea143c0e546000381c0c403540301c8a0b45030b80c0051860500c0c045400f00011030354425205840940b040e410300203505140450324580803039078980500b42d4240b070554154040d500c0204502d5006200e504603400f0018402d40003030003000d20100b02610f418641c03a0031022905414010880c1a240100b04480198007001150550308012000b1440c5051840400c082d8003003038102c40d484a0502402107151200022850111000344200c0c010410440084844010b298000500000d80e032000040118070fa280c01103801500c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 512337715 1250 512336465 512336467
    0x121b0109050a11180c220f051807090b0c010b0901151205040308011203050f0408030a0906031a1201020c0d0f02070b1c05090708030c06010e01140907030e0a1e0b010f0311090c 77
    0x100c030704002001042500312440c200314281f010b0000d03007001c40d003100143c00ea11300408a64103003c030014044000354414031030141c00000b05089848029005801e02402c06072290889503141c1c40304880300003041c03655000040c2c00d14604000d201d101e0107018002e58050325070380300c1a42000d8180e0300c00d504000041d024008100705c0010421240c00c020001026501302550721060b40c00c000501d081203a0307100030b04160401c05403411120045440301c803078003030440b965030400480180c1180640038035502051b650003001441d010158000c40100c180d030b2a250700b5030303e6035a143d00314000d15006451115095200d2070700b10048100c845d52042d5041421001100c48955540492600d180e0040303044000740e0300400c3c0100051043c0a000d030740980041003030b001040e0030100100b0403091004240f04201600d07240140300e000c00a00071100c9054020346101e4217118103c000c81a01c4004100c11600450701c40c0000420484894407030098a40c07200d800c0711042d41d040108004101c01924010007180 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 512338965 1250 512337715 512337757
    0x100b09060f0906270c0c0f060c0d0c0e030d03050603100c0e0f1903050d080615070308041e0501050402100e010f0323091605030f121b0109050a11180c 66
    0x24004000038440c810140c210395950902c40b00d490306280007d901041070368000010b1103100104a000d80301409001c12002071011004403084680710310740401c551301406032413666151541d05400031032007018150100c071625a0404039100480c1c00103030702c3e0000681002c0c1e016039145800b01401c660b050008000410050380b03140740640307992040d07004803a954454a03450380c1c05a0010502940318400715141a000c11000040620910401d90001e0400000d035000800f00401c000e0f03d480310544d03424245220b4419403900900070141a1800d078451154030408107403581c0b084108540a95040e507a2906a081011094020340640c0c1e080c01c82d01400080b448030f00800c149407052054800c00002c00400d01c1d00740e0034200781002900818004d400001031561080d800003000706410418455481c0c0e42c82c0419105110440071500c0b100f415401c11000d913003800800194410f00320b00030100d02d04503403c00d000b0046503d05100c0785140040c1800002545810141c018000341500706001c500383c04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 512340215 1250 512338965 512339029
    0xd030e030a080a0c03030506011e121d0a030305010b04050609062115010e0a3002030f01090c1d0109051f170f0111120403020708100b09060f0906 64
    0x43c01ca402e03903e000034207040300382050507458040d46130842420f0030001042e0800c0c004030031700c40604403803900500400c41c0d03420282e0f20440d0710850010841042d0b0703170380c08540c03110215122140d8100075000682488008580407441e101150700b1264001c0000c0d10b022020f030140100c41d040801140035650005490890440c044500244030b45c81c0c649400b502d00c00301c08009042e11066544145c024032404105204000084010043c1c1c048912a100d0060441c08a103001442c01a00000d4060051100da00090b1505420543d1541d03c105400c141280e02d07000b403000b48840e40085008a1070b59440100201c1c20180e000369002080c5603281c00796219407918400d88404240c1c04120034010041c002504c4031814010034421020401c005d2004025400203002036008070380c25100003114070404602018000c0084074010318202d0140c4040c05900f008240041c990300300e44c50b0280e4410b030001002032a0402e114020000014070401c3c0ca612001e051203039140810008244220352161000c90403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 512341465 1250 512340215 512340217
    0x30902060705010204180f0902030a140f030c0d03051303050f0703030b0909060601020f19020405060f030607050408071a0307080712020408210a081f0902030a050a0b0f0d030e030a08 80
    0x901601100d06010f17200c2c0d00c2c000c90407287c00c580500c4025103000c400c00010390b0041925114203410102d07201c0c02212459080341040281c1e0940340e810300c00080e005401b110041608440d414082d14104019034a04000c083c1c040740e0510001e00043c000c1000a00307090318903014110b0b83c1e010380b400148106c9400d012405451040d545400250700c0441081815a41000311740c0341101c04601600400c0560304050b200b9844c2c0f43d00081c4034945400010703040761540604101040c800604031030081c2401030b4080e00b103034001d015100041c001e04030b0114060790702402044400d003a4414a610b903580d034500032510060040d00e12010816046142a00c072990381c0003400c05400140064000c12141d400380b840d048030841c111300005407040c0b200c4401960442d00c06503202c5007130032440c40d84040d000510015185940c0080000714404010301c60020505d80c0414403545901408000d041c04036070030494040f440424642d030040700296014000b910ad000311000111000e42103461003c3c1e80d0340d83c0c140f1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 512342715 1250 512341465 512341469
    0x18090506031c02030415020312280b03010b0303120a06080a030504090c12060b0405010306090e1504082713060b0306120a0c03060c090f0302090610180b030105240a030902060705010204 81
    0x592000c10300b1a09c00d070200380700c907420842600fa0130030200c10018400d241204d11481808113207a480f582e401f8541c07002c1d00440b2035440c0042c1a01d0713454240821b20741240c42d05a4003080c84501e0300f10082545c1c1304c0022401006a0035807201428103260181c8403003d040ca00784030200700700c1e5034040c0d82c5407840680a1030300605500d11119032281e0811000400f243c49951100034200d0400102d40d104100119030750001207490a03c1001913a1581040d100c00d00c6680a050010b028404101e0103a280d52540c80c4c90718081100e0a55035a00c094840d0300a9030005d00582c0f07041041080410380900d082d48060030b002c4250f200782e4603045174584610741040010b030300c00d0f05c000d5196081c40c3d841651000345600505622420089a40c0c1103801103200c41c0f00052802e0300a118003141c2586403400780c501600c51040408100d150b03152562201880c540085c464103004124201942204412980ea0910b02481c1c000a650810004880c202d001c0e104c2e012042e82c1004040014202141c428001000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 512343965 1250 512342715 512342717
    0x9081b011401090c0f080c04050f010c0c1511010b030606040c0923030105070c0b040f06060306020c210903060c0f0705070f051c0b15060f0a18090506031c02030415 72
    0x981120042018180c075490205205c00c100e255000c01504804200503182a100140c403882c541c580103030300503502035000550181801c805d80314006200c0501d1035401300c151246035180200d40c55161526420303203641400507685500190001103007402c0070b500c0040c1078180f503d0078440b11956000d240c088001840c000e1542041ca5034800c12141c142401060f401400318600f003041e0480340d0f01ca0303858074180504010b1100542d48010802d11403581c001e08090b50304101c0840d65102040e4106a0741e03c507600074108001ca2650010300b410710020107542099002501800c910b035034290f00c04105602041040100240503c5182c010800030440040600380c81c2001e1000c1608000400690004141c0c0180100e0951003201c000a800c2d40030650b004110b01e001061700380c3c20480041c5c680e01401110305004800456413482d03043d0711401d05124402014203e842e02a115000c210580710700702d030705941561182c50304610400c3d0192442980019900c160382c101a190910074035036400d00d0708040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 512345215 1250 512343965 512343971
    0xf06031f05040b1501050706020a030603150b04050a050105031005091006060819060b121e0a090606050406030b04021005160b061306080c04200a110f0109081b01140109 74
    0x2081240d4040d0140c0c100c0c0421141350340c55807002c0c000130484d03c104040181002e030003140041d60036000b40c02c40000b03558003115030000201c4a0700980002d004018546103d5810705010913910100c03032090505a82c405800b41c00511403042281c000351001401e500c81d244603001183c110b01582d440780304082c003421b640d034003d1400d00700a40d0b8810288003148100e21442c20700c0420103000c600044a0044070300b40f034406000e6803549030031710040d0310155042a424000c0300410054594503444602c40d58804c2004024240d2170384244012610107000041c00220b5030008580540b400481403003202c456403070045d00c1c29494a041c5050340d5140c26040720603641800c24132001e032801203100b0305036003110b84040180350b181806281d9a4500b00c4002c0e4010303943d40101541c44100200380300300d1030f182500748a43e95196268018071304880c2c2040c2150728080c190440541e81410b0042d031034002d4102400e00c2c1008501ea0011003284c001e2000e010307081d96134250141921010306000c50003042190000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 512346465 1250 512345215 512345221
    0x1030b300f0c0303090d02013006060516020616060608060103020f061207050c03130b070302160303080604020f0c0a0506190b030613081201090204081209090f06031f05 74
    0x258035000340c01c4440e1103150410203030425a40c0b00003080d600d05080c01c403000c11544525000688540c100b151084000307a40c0050700b803050f05008103601e5030b000944841000707800da03108402c80d2180a084070703001020044040f42409441c11710090039840c4907a08a6030810035075076403000c04079032040e8405001500008010020743c82c0c6a040d0884512068480610f0140504025412500c0007040c1d0000e00c90045402c01850000300160f40300c2c1d043c15010b4595080d2102486100381e004160114014840d2140c01c009442c603042941040b07960646a515030383c1c8a6100b0030001c0c0d0800282c40038051014000301c4420001001800c001e0b80c040c501810040c01c0084c88400ca01c900c00c0801d00e0a43d040c60003038819508d0010710650f00101c8111241003107080b80c9410340007440780042019920000c400003203842100c43d8002e008407040681165050307440c80b14031440d14054499030743d0f4003600010018070321003110102140d21050040a40b0010014070100c55041080001000243c503038075410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 512347715 1250 512346465 512346559
    0xd0b06181302040e06010c23010603110105190c030228060f020c0a0b10030f0302030c0f0c13020a090504020a050417010212240d1421040501030b 64
    0x240c1400340c1c1051109501d041d0901d0440460000c0c09444c290400c80c2c1800c1c01c500384140c0051000040309404c0c0b0b807079800021552500d00ac3e06c603c0c00180c51904e48190703c88659805141120b901e0419250315903181c119a04003542d00b000b01c84002e6056000702d0401c18005217020b0f0103181e400076444401c03905600103081c200c0c21541c1c160a42c510442c810450160b550302c0004822020310341c065440c100702d9640858085000b030701c0e580010005030b44030030392108058000c00644800302600c4119100e090000c070886030396074400402d10380c0002032052034000e40c1020b9002840c059007a410303d03040040c0d4900211381240d104035040c200140300401d05015a4011542e0700b00280796400083d030a156414201783c041e002d0151200043c0d50716401140c500550b03c0f058005020300c002c11108122030242030201c00c90001114113030050250140c00c4001c0741c0211190701c405840c000541d801d09050000540003000d8445502c1d500ca400868404510040d04034410f50404074038078041003850104032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 512348965 1250 512347715 512347729
    0x3050a0e0a050a33050a1e080402091339030b010e18010c030b0a0603150303050d06080f010b0f06070305030a050703060314160602030f0d020d0b0618 66
    0x184180700c0c1e10141c030100069511043c40c90155040884c8291a10340b40314994080c500e00142d80307140d003100c0c004c5101041c1da080b0028003804070181c1c484441f001030000f2210a001c14030003004011912490104015041c1010a02c1d80640000c0850084504948460b00d55403140705180c80d04460300c003d02c0e03441d4006941c40d480303403010010a403255142507030303106100c942c0d0500480c102203184500160302d1030074154a030707155000b0302c07002000074088103040180504058070f8501d01030319400780001405407080c82111104452031507848402800d69408842c180c2c051b1800f0806103131030b0b00000c120804140400003100d030015000180c500001401c1c450011504010a4450b5005114100210303420004896000d00e008100060a40d5030200580050800c1c1c0c201034070074000d000b10840d06140004000301c1c2401c0100442440710780e81c20341240c0d81d1081a04015022409014081282c1e80c25005801d00301100c603c041001d0b0090b4001c1840c5400041c026294601d4101444001c1e0030109 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 512350215 1250 512348965 512348987
    0x6041103040b0421020601210c1d06150a030f020904060b0c160509040f06090605071d0f0d02010302130b2101050607081b0a0b01080109031d010e090405160303050a 72
    0x1c8180302551136511010352500e805100c0c584002002100741d40c07508225882c0c144130b880c0d1290034517070502d032204c100b44125101600b0b020421403042000c10250b1a00c51548020441c05a51192900d02840401ca01420003410700c0c2d200c1503024032004e1116070b6a400b404000e41300c03e507011612804200701040c9840ca400c0d0364001210a656420320594a404001035885a000807a1806c411850b10b044001494985000380115182c001805400e560102a60320003c2c942c280b040e10500c14003003000a961001181194056002a0408010750094010704500c401d8403400f900081c0d900d00f00300c0750580c030030106c04a0042050403414451821011428003400b03054074054201405596440346520a16150041011b404100041c00d40c1c0c04100107000319910189118180d41d440c043c0f18060009480203e0201c4d002d5289401d07011000304800b00d084005039120508004010103000c2c0b08140544103503201c0c081d550569903022034012000c80211320990703940703513520038000009107146038030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 512351465 1250 512350215 512350253
    0xa12032a1b0f12030c06141602070501020c042c060f070f0f03020d020d1e0b01021906090c170c012006010b09031609090b061503070806041103040b04 66
    0x5400140308030340c25140b4841c141c82207801d210707903040300505083d140c41100e000d00418150911075503920340c160009100d07024460359040c082111000d003074241d896400c0c81c0100c2e80141c0c00304880302c0d0107150540250700b0800318400b003054010410700790441e09450b00241d0404030b81c07069080c01054110282c20359846941440d25a162880d604401007400c190300710908201600410241242da070690304440208000c041c0800c4094090303a61840c1e44c0f01900301c407110040c44e020341c0d001954004150000074241c0d07043c516200c175240ea41c90300e0090485000036103010f1030031407000c00d003026821510100c410700e070070003041214900400105a25850390840103900c030403010441700a01c1c001601ca064a041e940001d868424240120380303031030509005601e100d280f00c0c10000d0160710661000ba02c6034002c0383c0c20b545564424003801851802000c0ba1044a642080029a00e910501d4941d4010100a01c00325504c002c5020450f4560000c1d5025250f80c00c8030010710007004440044501e9403948 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 512352715 1250 512351465 512351513
    0x80d080f04030206060f04060e070c12180b0a020703050703030e09101508090c2205060913080706060509160f110307110307120b090106140a12032a 65
    0x740d64002d444000c0501014007a25100d51601c0c0c45a88540105001d0890000319810318a41040c0050041700d407905c040e2010b000c40c02e01a48078501c580d904011010503554907402e2585898104c110369481075070014114096a54080002441408010000c60080da1000c40b2a891042000b00703460000e003015401c000e826108210400e400200c6d0352808001d82421410391f80d41560300c84c00d1103243e0614035400781d100002c084d1030141300c075103500d04160381c03200800480d0703a95014440c180c901510a14104e01030b0910640004001c0001041a00c4c400c10000c200c8503540c00115030408402c0d00e524820309a000c0002007502c0d0300407111040c041091400b004020b025000d4285c581c41088006006030001e62038410b00b82d1020401d4000074200c490410040c2462030901005480d0191035100340d95003813900004a60100800305216031000030080f07a07000d0304e000400c2e480d550701e103601103040c07089401c9000d510729141410a2200c52200d0344840714460203140c4003491031500d04c2c04071402da030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 512353965 1250 512352715 512352721
    0x1b06100f060f08010b0310051002100e0114040b09010e01020a0c02030d080720120c030403030f020303060334060504090b0603011d0c0c0a060603032012090d020307080d080f 76
    0x540180078504440d082c0e41c42e10350342d07140c150107002c6540e441e411040d0800d9182e270841d110389034005409000c0b000303402c004009184100350101e0a8070700500107003103030900035004500840c0406280340d80102d005400051504800300140c5d0a80e006a035100300828441c0c0e000d101581014081051001c11514007001503141122000c2d2032441e000c110302e135006c500c040c003070411820308102d462301030321041c241d2940740d0104960f000d80c1c0b41d0040c041100010048161004204e000200740ca0044000601604992030024014030a144840c0b080c440d40003407440304103040541f5010b1500c00380c070940c4d13110b0f0381c5c503405c0210f104103943c0139040413030149004000401181c20400da5401c888210600349414a44681c51b40750600c0c0145801031002d80206da28020402206030301c0340040341c1c8640c40349080051749180c01090708015101d1046960401d0080140c004c03400001440d0308180248100003060a40c1c0209240c00070a4010010940c0a5a4286126038020a07003d40c0411804541e144c645 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 512355215 1250 512353965 512353967
    0x507020d1e030b0307032009010305150a1404120806030a0f110d0c0806060918030316020304090f020408011d0a0605150607081b0c0f01051b06100f060f 67
    0x420105101455010756401d00e0140c40b07a0842d90003000b00500310340442e17850342000e4003904500e11002031000f1051490070304c3c40c1019001c1a0407a81c008024103411101c854400607448401044004802d0740e61038446d01804a10781840d0181c5d00234a5031089504403001d010340112070203045188280d1000c50460000fa4409104607000c0394400010041140f2031000728508101d440001000441403c10100b0360200001340c452140000315100c120a0300c0d00c0c400b5080e007468a142c1d440030780e0000c00000d25a440c0c0320f02120790012a80c0304407440d05503a4140807044aa00606140403da0005800c201203c0240a940d440b401803022148a0101d280c41c015a80e90541c4401007200761500001028180e8030309400100900140007503544510600c2c0100465011200981210303040c454043c403250300c0043c1d004408000a0681410210100010f6039280c010b1101014941103070150380e5403072402446a130780560108810907401034102038442010703440315040002042321510090340b170304d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 512356465 1250 512355215 512355227
    0x80f030a110309090414010507030204060e0402090a030b15150a0221130b071e02031b04110c0a0203070905090706051803010e030307030f050606030c0901020a05060405060a0507020d 80
    0x4900e904141101804420226080d406801209944110641c1c20401407106056480ca00740000b24002c0181c1d40c1c98400980481c00f45015040c0000c4618410100b5800d01d03038000c0a0b0804028144503174680d80e982d5003142048121002056007400351404c0d80d40c3c0c145010060a00d0441041a13401c10b80e64120003540c031100546d650004401c03410481180c410301304101c6103160020b000d000c2c6942e4a845c21075285900c1160200d0340100742c0644500605000c54010340301c01e5008020700411407504144070300c0c4441480030141e100740c0e900310060000d8030140080c42c0700c4850b20041d11a0315500d00405007841d20507804940c172075081404010417000041155800ea82c0c0303504180e6150307284c03040c035500003210075840c1c142c040d885c08840c1000360740000301540c491f5086035005c0c00160041c1140c2c0b4140d950542e0055044201030020034111128400600f042c07030818411139005003d69184e0a00e030002c1524141c400b03400200031300148121a0107020750005040c00204a1000200700040034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 512357715 1250 512356465 512356477
    0x81e010f052a180108070c0506070302040609050301020c0d23031003060e0d08161103070b060a06052104060e030d0204050414060f090901020d020d0e100b09040305070609020d1b080f03 81
    0x401c2103c0000406d150f001d030a842d00c00c25003210807030714039203010704001e0300130f601501800004c10402c68000907603140c140210340004c40c041000d062035400c4131100b41c61019020307410703003042c202481d103103c40700c0900d501039407103151908140001a403850030614100c070038540940380b05401c84c51003000480d4202d80031507013003109080900f41d0031546d07006c2160103c05406040c607440c08002038100c284910b01c03d0305406104115209000c1941da001c05451a00c07e011010f032541a00f401d028044112040b540e643c01801034002282c0c09684050f02800d640c400c5904014543e8041000d000342e0401e0300c60854140d1061200000e00c0c1442d400044136044100f05c0c0d00d1148002c5400200390410a40581d0100c00ba1864203646660880452001500d0b1407100045244907494400503891340c1d900031070000c2c9401800605140e22181c80840300c6a101500585203603440710500401030721407003490010607014040d02c1615544050f0040c4a501c156842450740343d0007260031410244002c0b0480310 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 512358965 1250 512357715 512357717
    0x30f1f060f140d0f03030b0f01051e0f04151206120209010b0a03140702070501020c0607110907090e0c03010501081f090c09090608030c0610081e010f052a1801 70
    0x642ca07064540000c0d0300700780345000144000050320442003099007503041900403800480c0d103944c0c04103500d00112014043d0301003250b034103100e101521588c0d45081006001001c140700526240076143c400c2000002e85182d0344000282d00c0341d0100070400b046205900282245410b20880e008182d0009000408180201e14030350100207201c4110034082c0d402040b0000010502e466580f0b081040651511050320807240907001d054610507081c6031080844120302d5004d0340c2c201d55a04100c0030300030780d490000d014409200c40040003280f04021494018811158051507594a41c105400100b082c1005085180c03400e40511550782c1d10001300c2c40c02c40070390380c5000d000240315600300c80494003a10a60b0000710010b06d400004580c0e03540101c000c102c501c8130172007103034042d4566040d54140d0000b580701c0c65407103404c485845400e031682c840d1500e00b41e800000010401d2020441c40300100d0346d0030f40e410242a4680504000c0d00d50b20350000060003913055540328104030300564481e00f41d03e15412024 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 512360215 1250 512358965 512358989
    0x4170304140616060e010614150a0c030219050106090b01110705010e040b040f0903030c09061718010515010207140303040e060a0312020a0204060f08031c0b030f1f060f 74
    0x3419040d0300c160300c030f00903542000090105a4080d0612802040207000e41c00040c00c0c1e00c031801000e4100301b80541041002c00340503a1070810490401c5443d016518030440441c007524103114980b80480450700300e20390240000040740d5103421210001c07a980045640e043c844407003104d9000ca280881d21304c088903000c2c2400b445001880002034000c0280c480140e070301c14606800d12442c82043d902c0b00000301d10949081100443e080410745512903648a22000544c80f600003c180c1c03a000d0b803141d40c02048008504c500c104041070150303b502d00480d40c4541c020786807241400d00e50303410400800100005a05030049000c903c0119032244990301800354007203158008541b040d1120000320340250341164001c3c00100c81414025241c5085010691107281080800b0070261131708502d81c0110b691400c0154540500401840501124001906410760355028600000d8500340000035140b11050041c2070006900041070032701c200e40000c00c0b90411301c2c003c014089201101100380079100120548 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 512361465 1250 512360215 512360227
    0x705070b0c0c030705010f050c0306030a030e0d080406020a11010f021005180304063603120909150509150d021203130303090905090f0c10020a08040308041703041406 73
    0x101407107100c0c90010390002c2c0302c0011680c091010640c0042103d01b0394840910068071a42c035412428002a6420350781604120801c000081c001c848081c00c810000d480403050141d982c40e86a0160082d500250241c0c10400da04000c200280000d0703c21f0329401d0900d402401c0380c0700002541c13084000491030f11a6a9040400d28081608103010001070303010044981d99903d5140003841800c0908203403a2420324004120a00516001c00d007403424480c0c0710b0340b24424a0f6071120303152503042e1905ca5007442245d180c003041802c500e00501c80e505144010340701c03c007032400051104549009061030f10704202c0084548650b40c48494203094150100c54031200720000d526110700b988121414101c801814800020806400c80401812204183e004000700d644183d04a5140d06601620142d5034020340c01c07030b00445c41c10601c0b0146c010f0092048880091166440151541c8140c04c240d07120310001c202082400035150303056a074600d1400185050030300d0140c0d006051015404220300c22003012a60b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 512362715 1250 512361465 512361481
    0x203030109091406090c1207050603040305090f04060b0901020f0102070c151206060903021008092d0a080702031c020c040f020c0a1505070504030c0302040b0604080f070e06090705070b 81
    0x160400500d82206a480c141031505c0642ea8070600076101d213000b9000d46040c118140d0707020a200c0e048440251036580b460f1b445540803201d41e400610010340c0962021805071a9849910400d00600504900e0300d50700c0c60b24100181c41d0604540040c2b4280c1c0c0108210340c0003a455050040c02c45000c800800c00e0401c0d03019040d5602c41d19036080d200c100703180c2500028110b5010404401b02da0003611010048120510101c0c0c100108650130044e59018820f44c21900e05c6030b030f84600991000b907040d6413038454980c0c0c0c1c0c2410302d4903091095408400106135402580383c00d02554a41c00c02c00c00580410f9000c04002070344030043e81d05001d204a54880b011a0100450b80449045910f0b40c3d0a89682251926007010800d0388100700e034460320b14041c00500514050b000311000c0d40c0d04420080c025500e103600700400760a003071103200c2e00088140000945900100450600d0216440180102e5170800c030780400ba80e0001050340c0c0c0308102e09024040e09580200858114540006800c010755982c906 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 512363965 1250 512362715 512362733
    0xd0c0b07140d080f0c070b16141201050a080105010f0e040c030b040f051b010e120a12080405060a0605010e100c050709020c0c030c0f01081b120a1407020303010909 72
    0x78125140c1d002e03403845000d0141d40038180360721406450340b000d01240c42e9503950903014055140000c0000040c64040340d843c05502d9480c92141c88a840c00d00d1600d40b1060ba1060960440c41040c0d28400c02100140700c00c0c904403810700003414403403008210f03540c9032400c2c58804108074070400020103082ea0220702405142d014840c090340c2c00c49080c00c81810321340b800d001c040c0302050080c5d0f840e001e4400021265130418642070750440b01607441416440650040040035600110340c0c85082c4546a00200010320b1450301800000c0e25848000c0700e840c0900b4014102072000b0015089245022818002680c000243c0a8045001d54801c41003e443e410700762446024944040c1c00c51080100c00180981a038001380b0182c0d20f042c05881300300946501307043d1f61340403204005c1c2c0e001d8603100b0340c2c0d0115441207032840d6000150000600b40542c5e004848490369100d00e1040c00310801460410942000d907010303101c810300001c281c04a5500d8030702d4000751a800103009540c0b40585820001050111841d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 512365215 1250 512363965 512363993
    0x60423030105010b031e060120010615030e07060201140f0c090909030903010f18030c08040e07020d030513030e190315090b070504360911010e0d0c0b07 67
    0x64020001540c44d425a0361854008507010400801c04400b03003070007040e070a05a18024441a101c0202942000300d014804000c2250040515940c0d11070004604040380c066103015000f6440c00900c052181c80610700700821500710708296814076003405031a03060003803003951100c6080b03054a0291200340c544070031441003990455012103204141b041c900c5c00130000300540e40045000f0000310003c0d9907410192008503c41ca440c90307082e0100e100229029022140c0c07954401c0c0b41e81c0c1e2500b5221400c1100151065030745000590110141d80003183e018030035590004881d9808111040d900d5030010908080043e24600612940c010000046c10250201000e5540200591882401c0070311a0b001810b40d0725003a903402070340300d002c0b86070f1134042c1046509640c4a40400700d06000c000c00012100c60002e0f600881d000030100301100b401e42c040c4070b212540313441004103a50203518040010062991099000d216903c0201d4a41c0001c0c81e21150308102e5040b0149207480d102642044c100c00c015030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 512366465 1250 512365215 512365219
    0x3c0c0504050301090b0f1b040e04030306030c180c09150f030b04060e090706030e03160c05090a0e1506060d1e0501150228030c02030703020312042102060423 69
    0x103076043c000c201e0803a0134640f01303400031114071941d540c68481c51210700e1f101c054140c90781c6404000a020015912484552290190038041075007541c1c0e596501c081d0005a00c184c2d10201201900c000712010341c000c0c81803040c0c56150205a42d03007005402005c07000074008800034410000020800d82e4040e42144060000060080002e20f64412000390301000888540b002c50080c0000411202e01a2113a24244d080340001181820100d04015902551404080d95400916000003415035501107500e440781c045403c0201e0070300031800c0c800d494441c141c900c0184a11b0101c04001d11a25090141c130350341004102c0c04500340380942c001034199121a2007501050b8146000440c1410100043c455440003aa0890b003181d0000c4106403200303181d6034010003031120364140341070100e0304c15109424501d00041c182c0e40c10303590369800a450040f010301c04010b00d45010404000d40d1a0b07a035900800b44252500e00009060076a000502a01c143d016001510b81e1403da4030b4506481e11311030701408040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 512367715 1250 512366465 512366471
    0x140f01021609090501110a0f1119060b03010b0406030305030a020d11040308070c060804080301090b0619020d0e091009020f0d2318070308031b0301093c0c0504050301 73
    0x5500000380030f8103014006588541c20075079211038070340003e001c42e1140341450f6500d60b030000c0304e00300484a01510401d012660b2054200c501c001406003c50000c2e4207108110004241c2418401d140c2510f18a40040e442240b82180810100b50406d0440c2da21221010340140e55016020001d4010315800120310800308001c03c000c030030840c030742c00282000b5014000803400030307030368805c1260f195800b15001881720a041c0010400030902d5001440301520040a140c10501300140c42c584440c54034007040c0062b40711903188202117420480b00b5640f000c040d0380040b00303854084442d80c07200703416201d0f0203126540024003100040076a07040c0c1d004241c0e059000e20450b400d2600302c4064002512041c1d0361208032001043ca5075410110850403c21210f001d050090702c1c50b01c40c151280c0000b030580c7d000030607000810390a2181c0350003c50181441280005011144610111001c4031200041078099852030316007122050f0340603500401400850040b81d0802c0c16081110700b4080e56100035007542c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 512368965 1250 512367715 512367719
    0x90806130204060e33030613060b040b0d0b09010b0d0c0e0a061d062404030c06020f0a062301092a120203040809060301030309031b140f010216 63
    0x40500000c21045008403030610915465914a0b00303601800d80300350700c2c150004054081d0003000c14038000390010050020701101c40c514004603061003070848000003806259a841c4082040c60b100711011214295001c103c541054000300b4003400101c4006001c01e03000800090503094250801e8181442c05800418504d19524001080c10218042d02d5007441010001625111551203482e080381c88017201102207648603501d500f40e142002e454141c00c941640e80c44c3d501c1c12480c5490518105000301c04590301d9155041c2400c240501384c101034115001140d2003400c0321400114003c407036412400000301030180100d546030000c80c40d144903828401c01000018039418951000d51031602102410021216007100c105030340a0b01f11008000c1402c0f200e65011102155011f95845482040614600441343c0006001a082644110006440e09105000701b20a9a000380e0041c4c4c0110301ca101c546090210351400c801080e10424011110080d81c20150f038401c22105410300a011700b0344908503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 512370215 1250 512368965 512368981
    0xb0a0206090601060c0f1b1a0706151d0910110a02060f01032012010f020703090608060306010905040813060207050a060206090304050d0f1a01140603041104020a090806 74
    0x910200c4581e0310318010400000394041c0100d0440030302d103038040e609207034444903035560070382c0c004a04403480400703500c00102140740d440e01d60780103540b40c2c1e044000315260902c502c3e00400f070b5843c1001c0b584400a0501080000340c01700c95079081850308203c03940d1540e640d80c1f09014a444064903441d0201781c182084000000c005e80005c00c6840115030a60340c0c640c0d580000ba040da0320083c88018a403001c21302c00c09000f52000f0803101c255120043c4141c10380e0521100050035500340c3c6803207c0c1095400034181d010190007000e554014116814505145d180810000391034540510980001d00c0c2c40300700040410100708210741500044900c444a0580c44060007951003401e4003440780074581d01c03207001c240c0b94000a140d51240340e92a008502d03040c00d007024418082440c00007281c1e035000c4502820005030700c0f8603803000d1441138804030948d40d6141425403401d094141690500442d010410322000c990864400c3e8904942a00e0260b5a5035a0407030032074020030654004241400341409100c510 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 512371465 1250 512370215 512370223
    0xa0207020a0b0a0c11040e1608061008150a0f090b01050301050a33180219090303080a090309170c09100f060c061b03050601020124050411040b0a02 65
    0x1250003615100345540c0c4a0028038400e12070110710a001c9481c0ca0202000031703100c0703450f025500c0c8000e000818034802844030107141601060001524404421040c40000020401258858215000c2c0010700e45010034254540486000f040104075403940020392109040c1c202c200000c0d0440c0c0200144c2444d410000350240b820f0240901c01c1d4203050200d8841c02c0c3c14002c1e003d400360f00080444a851079402c02590350202110200200c800e0b0600001e15455141d548590904a030000541d40d80c08095180101c038440b1a41e05081c0f100b6650b061020079404030000340d005900c15400108081242070580d5075030980e61041e280c907175070045203800d1130350f001c100c614000f4000d44641101d52583d1020311501c603214051900700c581040002c0100c10303c110383c0b2070111030007402e0000c2c0c500e44a07000720031444000c803070f01c00c0030035155014400c41c0e5070709116020040e07818211184190415038885080a000752240b0b07440f498446050043c50310b9103608a6000744412001240c0c0c0d184150070203921 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 512372715 1250 512371465 512371477
    0x615120203070602060105010e0f28030b1b030127110706060e0903190c1e11030a05060112021f030903140f04060503041112100608011503030c1a0a02 66
    0x3030182c2400040c510303000081d054113868050711051740000c02c00d0103020144071401216a8001100c280c09003103a030500c10700e048609500c100700c030b541074110f0602c02c0c08540085c01c1035925142c8013130510f2440d00040150303819503103d1114102111524170040e6403ca5070800c01c6210307589084005c4a0581d24000103141840c81404140001995140b0815000004550b108040d80003040100c5c0500e804140c400c481c0040d90420107450b8a003034a9844052220003480700ba600e2030460700c3c000340b20080c01400c001c41c00460003800172815907036481d920ba14040c8103441c0846020402c080c02c5645900c000e02038140d032402c18645413082c030328000700504008003040d404079409802d2114800d61030320407140142c0072042890300d0a40b0340001100e03103074402002503880000880740e83c250f5a8074070400c0c807c0c1644210040030480841030042d8112406c5034842010303603141280b07102c1130020045d0404126501404c007220107140a09020903030300081c17200414962204820040794441580c09044 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 512373965 1250 512372715 512372719
    0x20c2b020706090302030c150409050a140112150507020f0a05031213050a020637030c0c0203150622020a0f0804240204180e1011030a0906151202 64
    0x200729503681c0040d0b80740015808040d4240d08802c81c0d048184c102441e99081a507030401c480352030213541300302400407218213803080729901c3d45445605407416203104089000d04001c100720440c030700c4181d4507198140d15034618a03101a40f05d10020708054020302410303041011580a80d6901e01c0c00e45481520b0742c1c030288840154203554008a0006505400300303045c0c082d40480100315035150358007001490b801c4155900364403042c41c541c6031528445a10076840614440013042c0e604043c3d540e001e020b5034801c21803241000306110149015940001d14a1102e810100000c80d49465150115294481212401000c005035849520041d1580d900800e202c5030079568002010261241c2202d5070401501d0140030401090111804c6c0110806201090b1240010061406039a98080850102c1c01a1105045c1d036442c1c2442c2032451f41840356421000b072070700c0308004d80c0c2d21240c81e0176403500025120004c602c0c1e03113086442c101f00c081da0090120780000750102c0040d0342d60300005050343c4074180d03080f4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 512375215 1250 512373965 512373973
    0x1b06022710020a080d0f02130e0f070e03150a0209190e130308150d020901060f030509060628050a151e0815131401080f0705030c04020c2b02 62
    0x1c411a00c00700b803040382c01d9800502d05241c844409100c00191190080c2d03e1640b550070020a40d6030b0175100d5604000b082c0c1c50340c1b51b00c60340c0780580c3c01480c9650700400305000e001d80b1420218003560080384104045440807a245145e841c3c14102e10001d015043c0d52641003c03012070348940e004015222102201c0f03400003007003040d5540000c001240c156441d0004c01188108002c40d070034280d40b50081090303550180010a024041d5000107581079400e03840781c03001c030f08112010301055625004556102c00c616004000c18248640444d0740220300d0348202d40344a500c400d05965203220b0303444842c02001c0080c01c3c55072480d160603652030207420441302007010076a610601503916442260070802480c980d246d1044a13664040c100031044440303a00180d0050240300d24040003100d5120740000c03030b958480951041e6042c141c09030f04d411001074240da6039a001290410450b0380024520b661040190340c0540c0710140c500c2d83c6460710411900f546900b40200342c1000d0100e401b08100781e198040c550840d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 512376465 1250 512375215 512375239
    0x50a080105062403010e09030c01050106051b0307020d1e08071101030b0d120f051c0608010c02070e010515070515090706180509041a070504080705101b060227 70
    0x3120071025204981c00440c90600c0100000b06c100f44065600501120a5a2800341848c440e03a0848900f600302c2d5004ca600031548900d10460340a0002c038501c50400298039100c21500020b50313007001290004c01c0107101810301504107841c104110b40c0d90307511541954031034106107800c91508011300c1c000e0307000900d8501c01c8034183c0b41c0f10b204030502540104400d80b010a41020407503c804500c003616081c080204011058010349680c03c20702c22030078440c0002c1e507500f4424410b007582c29030001d08086501c15030083c402d108000d900d060444504031070f0a02d520003034640d00d00340e90180a01c0500306020b000402d0002d503a410712154410042031040e00d00050300e819041e160720308a50b01d140c50500c0c1d8008180030301c0c144052a250018040d285150900e007405030007400d10701044a145000a101150802800f00208000009031400300c1d00040d80100300c40006240440004120f0442403103002e80400340b290b01da04641491000d00500718040c00e903c130056050b80783c808035490050f0309039052 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 512377715 1250 512376465 512376499
    0x3050f0a020a0c120201020d08010e040204050408131d130503040e22080a0801080708031206041401270203010b0313030c05100b0315010b030606070314042408041713050a08010506 79
    0x5050790701d01c241c0c48bc3c05071119000e1200800005108460303c003006c00c410141000c0d0b40301d0341001071440e00000401044000480c0c020701c080a0980018801c0c2d81100d040002c40c08030680c0c0680f606540310b0801544c54200214141101a080d89a071030300382c1906c80c2c244050080189030021403a201c881003039136034030307421a5103400601ca50312144d00240642c4518880314000b0030b8110360005d2020030b100e0b10100000e0510082a401095032510320500c04551900d42c9041e041d030109001c81c01c50466151224441c05d07840001c0c9803c42c18000c9686040801d40580c2e60350a006400000311100744c0b44601945004141104040d44240b09a0000150b62920003a40c181030b1607c44030100d081d80c0b03459040c02000d0300324280803814031201514454041c60510003a00051540c0e140c440301c5804102005071201480694440170042601c04100c046545206032248140b200c02c100e980d02d00c5100310f040f10100003a00520b034040f10321140003030003501c1500414060003088078030704002409010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 512378965 1250 512377715 512377727
    0x5160f090c020d0909020904140f0f0f070804030507031101110309010f09020319052109100e0901050105031902030408130806040c0306020d0603021f0e030a03050f0a020a0c120201020d 81
    0x12100f0001252100140503410b401c0e00904400400a4404116015000d100500d5400c00b00d40c0c00700c400b8450010401e84140300c040c0f43d500030112590303a03440b43c00c02800c02880e5810081000c0c052040c0080e0a00415209094000720711101000030484010f0304145200254800d0320b03059550360a143c85407000144610070070090903030043c0207144462090700f84040a0f144640300355118002c88640c800200c00207011000303040444000544e07215400c4041198540c44a2903140401110021041854441c0803041d0b0544a003420400d4880d40c1d2020b1107003007480501c030020009800401400104500b880c00f0700046c3c0e080c40c5058039101d440b80304903941d4410440700649000c0518104001141c01e03640205203500d1200408100c890700c0303402080e0113010528607000603ca03003c000440e00c42c2d1148030f4042e0401d00310301410b00c040940e180105213000300820b0000340400012984165402041032101e0746600c041c2c01100c6d950790b400e02c4000501210410b0f4054011036060700d05140c4280 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 512380215 1250 512378965 512378983
    0x70b060907021b0f04060b030114152508041e09061502060c0f09060403150c030203010627031b140105040f0303180b18030f120301050d05160f090c02 66
    0x36142e000c0751201c3d01000302030072180c00e880390083d5654001185c449141001103020b0301c18040c00700c2101c082e03041404025002c0c9082070681c60403d00040c02c42c40324034500070f142440c01c42e0520782007054600303141c030040c41507620411030702c003540c50031304019031010103040121254100100302c09545d644280c000301d401d00040d5801a000400084c0810282c01c01400184000c66841420320007813034080ba800340d100d0303001540c00d91412902e030b5005d9201c81c0204135240d410b5160070360541d454020302400e800c14098454000103010020030780101407800c480e10041d500440c84510f540001000040040403500078608000c45035122112720754000d000310340c00c60301302000c814550f40c61a00c00300c5408040403117000d41030001d4103000454100401c040c0070b0b4151403001c0310a852261a041518081c01003250010a412000c11505141c10030010707a41141e0064901c198451074601e0404d090448200540381403403114603000c41c5805a00150405541907070508110640c45910b00ba0b944030191 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 512381465 1250 512380215 512380243
    0x30105010620030715060302120c010e13201c1103012606090106050a08060402060304240c020303040b07170c0a020a0807110102070608042d08070b06090702 69
    0x1050503482c1c0592451540d00d0b5080d4000540307044c0340840c0d03512555030b10006907080d00182c9404041c0705505e00a980300041c1d000c100c1c000c060206c50040044c0290302070011641c4941c803080070300c2d07861000c5a000302c5119001075030305c8080089034001c60302c0f41d5000701d00c2407807040580040c429071f43e0540340724040040321002601c03400c5030319152071590000c00c814101e0000c41c2c0480001280f900c42002154005d20100c07002203042c40c2001c003400b0540341203901a65803980020184005030300ca540403241c0040d0040c112180f02c00e00a2030581040c0b00c5a0301003003502d80381910310045542e0120240d4082d911560303d02006840710681150714007030001e00480d540e2103c0d404a51400c80100040c0261442801940c03200c40c140d0300c4522890700f20300c2040e1001e07062000203204542e41071007084c0181145042001c01ca00b05500c600c000d00d015014480b2000c5480d46030030190100016a82c14602e5004d01450340e1044140f41083d03448c841505c0b0b940c000e200b8000851515800405c0c0d00800d4100307 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 512382715 1250 512381465 512381477
    0x3042a081b0a032103052a070503040b07032303070215060103060807060c0506090106080a080f040b0309030910050c2d010c17060316092c07060e0301050106 69
    0x1c56154101da144981c01660710407003008001000a0058000504001c03051052494650181d840501034400003040d107840314600102c06140705001d21102c0381040c00e00c4000c81d44034081e03850038914520442d00440072000d0701090031000c05900140f80c900100d01d00f0b40b451061180940c0310005800140c40d00380140e00a501c2c030200120215880c507034442c2052501050b0302e95924102c40c20515260826000541c01d11940d100f4002c08001d1250882c10030002086050b2500b070042d034403403140d100003c005810002c2e6000d80d01d440602920050401c00544694030b043c2002813582d80d6024003c45401005400c44401c1c0a90041007580c00c4007400784068800900740c03c08003184680241207429041041c80182d0061440912403880305803455154240c418281c1202c48000c400c0007029103100f0350145100c88611060200100c08449800303501080c52050152044415030240049107130169400038140b40c5028001010301c1110500d448081e41c0d41c0420301030500f603a50034000c0d0000305003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 512383965 1250 512382715 512382733
    0xc16081902010516020f060c01020c0c0307030b041b080105190b0a05090127090b1e010510080a0f140105010f1404050f030321070906030203040c1806090203042a08 72
    0x440284c4060680e2004004205810440c0d0014805410200244001e42e5022410070180c413000c003d200c40900301180105201031071961244da80100050000700759100e444633040c8c07134807112095000600b41c0c0d00000d10040c60310741d04804c500078042281d100494100322204040c0c1c00c1c005d008509032000504140c1c280d82c20080710829164030904005644255240c082410241c148a08203465125400120303031420a00d0380100080704104a2040e000c0d0500c00400042e994609030340c00381c00d014100390102d0382c1c40c01031200007410038420744144142088071140010003840d90b180d05844090300c62400032200003034101d64134103260000e030075100000c200c18001e03454000300c180b0140a005044a1408480c10684002c0e08250801469640e1840382031003080d5401082c54000343c00c00b45800c42c00c600d0981c60b084e0a422580c495031103805aa400c920064242542099001e0304540a05540e00d05041c50315203071110b081c281000b0015400c8042491154203c640001101e980f80d0042006030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 512385215 1250 512383965 512383987
    0x80a0b0a26030d020904050c040b03070309030e120a200f060702031e030a020d032306190303080114010c0305030c030705190804050d09120b0a020c160819020105 71
    0xc49030090040d621846a001001c14480400041540e030811400c0940c0755407038107090005841c0c0280410340c804206000c10b110901480081d00d43c8440d01b8034000c6284509400c040d40d0801441e0316080d08a9400d40032000c0c002000145403003154491402141e01000540a04941d0340301071344801d601511a1040389990716003200500343e420b00080035180da0303a0190101c00412115400600ba258002060324900c2540600c105504801541030511a240401503100c2141445034104040500000040750701500e03040c01250711007001c414250011522401d0140080800741726801d42841e80b1030940b10654420042c41410552541743d040c29034543c810a40c0f9a07400080280041101c144200d030120700080c0c210b480029000e440ba46040e06040c00c101e41010060700d6500300707000003078000b0011224244401040329030089202c90071501c1d01c84013000684600040c900c0188a40258040c2240880e50320501700c81d0702d00202c4c2c11009110002d141505030040340640810400c2c02006011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 512386465 1250 512385215 512385239
    0x30415180f14030304050706030e0312041e060c050702210303071d0d0b0703050612030d020c101a1009230414040308061c0c120f050a12080a0b0a 64
    0xa100300612500702c91020541480e60708202d500303941e607a0280380200f1010b905031050309480c8541c03001075454555044584140c0c0540500001d0882e10b010404160711404200c4003882d00707034011403c1c01400f441c4000105143c010310070581c4100841081002030610b59451541c00880d0035002c0c60555540314005d43d010110702568156070b00c00848141100c1d90343c003101d0310b007a91007501c2030221401c00c1301000b021248014009809848011904c00105200005940c07550301030040150303854880c200c0581c20005e200315440d8001d410948038070070400e030340120b07000c040c1420303101c0604521209000300c954540e507102d198103c1c44a4070076000541e01e03052044098920213030011650b14032884a035141c0c250120703000d50004515034140300c003510b820b011590042d103d003890f58403002d019480b2111b004a42d88140c64490001003070790000c1110744407002003c04d402005581000d40316060002c0b00300c0509442c540083d0302080008c060b20600c0c07040c0032041070064400d05016007411418404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 512387715 1250 512386465 512386493
    0x9150f0411030a081201090606020102090109030b0603010f0504140d08040c1a0712020d020d09080c060310080d09051906020c2107140a05090f07031503150203041518 73
    0xb6000d4800c05a000c11401c2c4002c100320002510300300d105601d8a482c0e00c04642080d0440707401c590040000580c0e5a03840a50b00c01688d07002144a8112f4582c40c0000303006100c00070100c240582000108005c3c058040e144032084032000055600031810400c044a240ca4216001003428000c032000b401083d0b85c3c01d042030b02c1e06aa140c0c0b030b2454003d264131386030360745c0c00200c01c003600580c421a4134400c02075061011064210362810070864042c209549562103c0036809094028030000c00085d02c44291020420020a00d49090f18912088840d00a0400c01503005450058500c14103105014102424080c00c40e4a142e02411421820408100301d001454903046241880741c4254019804180300220062448042c50450b50f4800402c3c0903540c0c0c07480d40a00e1080a122040113003980e4882c04182d400305040c54000b440e407140f0b48190301c0100103504003600750300d00b10001c1c08161105170f0003540118060151600003200462200c070541302201b10258042900b1403001000512140c49414 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 512388965 1250 512387715 512387719
    0x40218070509060d050406060e060a0e060604031403190c0b0604050720070614131701021c021b1f021b0609071d24030a020301060e09150f0411 63
    0x314005007000060f0f095000390800c10035180c0c4e10340c203000401865214020041061079402d100714036109000804160071031003030009903002400000c02550ba03550494014561040a03520091817803a58035030780c2d81018940c80041b10301d10f00c000320305500480250154a5005003000c03000d40e5890140000340a001e0901401d00070704000d0301044130031107081043d00e64044802081c005140c480c00802904801c0401c00c80014100200201050f500d01c00700207031000102070000c583c0124401c40e0081c400c0d6460030790114018035001d000201140c0017080030725640e1003860740768100c00c441ca81d145c14565142c040c00020342e04040b0030700c4169070017610440d66010a19130650700e00202c0c0d1030521900300ca0030003060308185401d00035204000b04106054044418100031480d20158805881940074501211070003207600c4240d5556081041166040e0301a009002e016658060005904020754080410340180e4920b00c0300030398044002c500c113010a0b00d11181d50f417602d8480d00d43c0d01104410303440e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 512390215 1250 512388965 512388967
    0x150209040f1e0f0504110d0f140309040b180f0604151811030f01211202010603050714180402030f06010308090406060e03031207020f0d260402180705 66
    0x369100000d20941d00803103040d00b500c0344904182220001150b4100030f02205407071903c0103020218686c0d0340000412042070312903034005002820101c9034100043d00c000e181800b46000e4203940c020100150607040b2055400307011260000d030800c031008174001c1403100342030b5110001441c1d03042c80900c055007040d8040d0001031555070400c0240c03910f1005030001640c103810815100c1d541c860b94800c1c51812090325500c00c0c11400d00150003003403902c0600c140c1c0e09072000711800f0001a00b280a00c548180d50110070101740340b440740e4010380a44400e1200f03850600806000003080910004c03c2c03a0380500c010460820005d0701e2120540300300c00648181d805108941da503060012003046400e01860240c61810f0725060000200015a0080e401040802c1083c0c030540402d070300e00109550840203030301120007259450200c1240b4002842d000c42c0c6442c03082182c050800c9403c10004051820141e204d000b10044001c80401d10680960f0001d4008034010440d00b03458100f00c01c5680c0041940c40c0203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 512391465 1250 512390215 512390231
    0x10f0819020705010605031b1804051002040e060109150905090a0f060303020610050301020406140d0902031b010215090706210c11010510050f0d0303060f08030318060415020904 78
    0x30104036088400101c859a5560409200c140f80c204401c00d0b01c1c5440da0b102000321042400415000003070482c071101020360041c0400e040103001e000c1030b074002d0440300c0210b4540b030340c44100c0c00c01c408058450601207081143c0c00300d00c0707062000c40046c5902c52a1a282c00e43d924100c107000400750010b11000041e6034400b800e0f6580c0c001400b4a0700118025402080d803410003804000080c1050b038480c5100368030411040110b00e0300b003c032528480e03c10200352900c03024209103500107001e2170f1038001c0d814052540a07042c0310044242c512800c040030f81c04c6a04541d0001e0003645900004e9425004a612080080000c00d11034500c04c0b50340101c0080c034000701030b800408841514401504d100104000403c030607c1c6040c244551540039440d05020600300d45810040380710705031225041802070400803012410f00d8040c1d0072400090410b1540e030404031342d0340d600c0c040d102d80003524210000d60403e00544800c2d50009101800b4680040601c113120381003603c00c1c2e00941c803400c2000d42180e110500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 512392715 1250 512391465 512391511
    0x8010204080610080d02060a0c05071205030a0e060114090c040f06050d0b01050a0c0308090a020a08010504140a0302060a1505210601061d0603180313150e010f08 71
    0x40c00040018900602003410149000c20414030b40e900304440741e41c48403510032981c650004529800142d9120b0011f00650003602c101c0320351050b43c0c0041c0c0004020610840c4003644013004511400892008015102c580036101c1d854000070701c102c04c803004440d17000c0050f0345048600260021307a0524164605036940c5640c012400e040d034080360200b40003145041c2c0032000c40c0983c0d01601400d19203036140c85003d98000c2d12544c0052070140400c4141c1d0002a050f0204000c0c01d45141d07001070a41c1c00c5a540c45d406280604811101141c04012a0352070781600400042c040e41440da05402510b504c0d90707815809002070650260381e84a034460f0000000302c584030404483d1800d0a403035285040c10500003e00f034a003a0040e4400000c010320501c100002202040c035041c0c20000807a00f450352620307031802541e06242c20301707200b41003800000303168a11000032982000031121181072210000c0410070041e1211518041e4081c003060b541c402c0340020314403801000d944100f80a9060310318118246d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 512393965 1250 512392715 512392717
    0x3070c0b0f060108070c0510090201021e060a0f0204061b051c02031e090604030f05070e010f0e1b03041101030e0712030809030307090302011b0206030a060320100c0c080102 76
    0xc18400324522031007480002e591010030f895100b0407901b49040900c1c601da1b5002da40300d11004030f5400140d41d030300c0b60f9411603100340f0038a400400a01d54000c0b1508004070800d0f01c43d4070a64111450034500458003c00c0a818000e440440b00f86446034a2240d0003a041c01002c01d10f0b01d01c1c21107160040c160380c1100d50319000c104a040c1c5030b1a074000d640b503030b90350010703255011452402400d24180c24480085159500da08890541c0d40c0040491508803041c5001440c000181c0c0103040035011500000c036039242c034a144202180d04806188031681c440100702d80d006d9804806001c1c424074100005404143e800105080c2c480c410f260008044210456503410110b15400001100d5000c10303103001031503840015181c20411940265166042ca032030090064456844002e0500c1603810561813604d95035103002d080c2d1a0007404c0d081d540e00c0c1c1107a038040244501d01003102d400b250034620501c0749100040d54211a0380c050301540c07a4070b100b5581502d140c2c2c15200b04a0340000b0110003c0796041080c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 512395215 1250 512393965 512393971
    0x91801020307110c03011416091d1e090c0108040503090a0b09010908010605030d0804140604030c02010306140d1b0801090605180a030203041e0506120402040606210203070c0b 77
    0x542c60401c81a0982c503e80d040070a00c50b01c4d10f102c1e81c10040f491000b1140c01640540107031181d040081c491542d810151540269070384940801c01455203410501c544043c00d10f0703c229041d00ca034081122511110302e246540039141d02d071665100070320b40390165000c1c80c2029001400b42041300d00382481d0000091144101d500480040d400100e181003065130050040c0d40503000b101e00a01a40742444080781d81c0d1840701800d4020400307800080b400f482085200c11b04104100003d6940030301d06410082e0401c405200300302c1c0045d1900c440001d54981108030325964410081150800042a40f100424125035108544803441040e00000f0946400d03c501d4481d248121004a82c92801c0c00e0030601c24024403207909035035000540c811b00040c0d404000c5509480c001000030181551840440b040b401050300200e41110000030101d0341104c40c28881c511030752080b10240300442d2034160807038004100c0342c500300303a0350414414500004c0c041d03000345510030514070705541c04114544451072295025 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 512396465 1250 512395215 512395217
    0xc02062a1b01030c090b131e080a0f060e12280e0f030c03160806060f1008090a0c080609060c0a020d052101291c0e07030206030a020d0506100905091801020307 70
    0x229404010140b80c0c2e1a95096983c45026070b5000c0c5494041270300e0312008003003002405c400901594034100704c0706034400d07400300d01080201c0b22004040c1084444662010046081d0300d140800c280e880d8009806608104810341d64428029800600601c0424640d10010355418062100300d00b420f528104403c0b9060340d0141c000340d0049240c004401e0500b0009490f85029500b4002e50280540f00d4000d054000c484518161031259200484a410007031403610040040c01d81c000c002605040004405004014036400e41c1c03225190801c20707800314070980d0b00e92405a00000c036051020740c0910090071444018800c0aa08030b4500746000e450810240c020310080004000c81310514070410580121561403482098039141303c5481800c1e00c071000d07451001c045030329000000c2c5c00200901092000f1a030240c20f03181c403030501e002090081d4100d0307103528510740d181c0400500545001442900900715079240c161450f4184020300c03401cbd400080c1400d01c1030034104e4000b0349520091000354402d01c0070b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 512397715 1250 512396465 512396497
    0x311060910061d07080c04030c030821010e1314100c021029010528030e0703020d06020a0504120f11090f0f070c02062a1b01030c090b 59
    0x200c0d072480440b051504034036030021486041a001035802d1610076000300e0282400036003661200c90858042c821500700a1120a40360400010041c2540203000d040c0051058169134080c05180c92021764002d02c1141015142031011500c81c00500d00351248060092202c0085600d10b080b80c0392508141181102085955030b440c0e07010250b05000c045400c02504070113114139444c07440c00303180025001c0305a00345000c00760070801e4140c0c0a402140d1303d0000d1400407104051020024410380c40c80640107001003410541403010506010038a4825603a005100c403190b4211500c0e844000d40041c0f92a10030b00508000100791002c200009010941c070401742d034400e10740c8602c0d1500080ca02c0c103419602510003002400703070b50550034000d40d5014003d0130303480c2d4940d500c0300c104079007181c901e020294001c1000290050440f150ba01c01d000c500f403c00086005200b800362500e9a80c0707003d040f21001c1c0c0032250034003000c103601c66000305050300d96524049211541700c030f20308602e950008034941c0074120 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 512398965 1250 512397715 512397733
    0x62e08030406090617010605090d120c020a120305160311070803031f150309052d120313110a03021003050712020f04180f020f0403050c0d12080403110609 68
    0x79000203484007921041ca4010243d5801e0300e0342540417941801080305011001c00c1c003103804e8403403212018206800a210520f11420880050f04c0084a1074099003c2c1060002c04980d603145162540405070341503139050316001520701160b040748074010048040000002614803000341c02c1008501520485007c0e540d241000e405010301c100c4052144500b00884503810091007680d011000340c00405404c4c0415103246515006080192a8824078085c99a154400281c1c140d41c80900842000f004202c40000941c2c08050045000c111503900c02035186100e400c0000780654480100c010300a0f01005025441e40c0c00150103007004296000001d43c0d2360204120349911000b0030340380c0300c1106001c6290008400d03044220384628025036111071024840c89100025650050300d916241c40380c01c5403210325140107018164400d00c81940c0720b00c1400000c0e141403a1525039000c1069000e403030f08204240034001590245e100600070340c24044c4504221030306140511016104200c4000a00509030b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 512400215 1250 512398965 512398967
    0x30a0605030307051b010804032705040606090515070f080703020106090f020a0e0108010f140d0c03082119050601030b04090303060807090917091c050304140909062e08030406 77
    0x4440e0184603042050247c14030011070b80094411407100c006209103000ca921002e0b00c1c14524034540d0140790000d203800c80000e14a54001e01140a0315011582040008072711115040e082c0580e01e006084401c1e602496400680174000410a4602c00c2c000070520303540e9150501d00300c4950281c0c000142c2d40014400e03040d141d0200220301d180009080490a55060080324400d1035194007991030406048043c1c01030507607402c040454076035800140001d20740d85a2615042a40000f0800d003100440f010707000e8914101072842d28403071042d14001c194003c03450b02d50789010700b00c05042e0794180342d6207401c2d4040a803941c0c0920340c41c003030003030703c011864902d010703480c9282003910b50020500b80d2400040d5400a0040c91220704030000003040951180003079000500822450254510701484144d0100100709003c0007030011601d624002100d160a1f12082c01500601102c41e0310035900400000303403402050403403c214140e40111000c5548001100d40d01d07164031950441c003420b030300100d4208402 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 512401465 1250 512400215 512400253
    0x5130c0c0503280203030f1f0302091f0b19141204060902150702010503011505041502010e1603080d050703021e0d0e0a0b1501030f0203070f02071502030a05030a060503030705 77
    0x607903132000b1842c5150505600315598409000c1d039201c4408000400d100a940d0091500a1a00141508510b0416850400d0b01c840c0081642c0448140c00c840040d41140c60000d4400303905003001f502004010305003040301c07000140044aa042e04c41440403200c088102403007103100740e1280c840010b910040d4010840030380d011161140ca100c404000d0500141d0744002560304444081d8800ca08030200544191803a0080760803091b4042021035410003001c0d81504429000c0603d20242d41038a501d071900e00d00303443d443c2d00019004240401201d4441c0f04150302c0650300c14290714005041094081c030255035801e100c20284c1040c40042214030401c01c9a01c00c0c1f0800e9840340c0c000b401200d5413545c07807400c00e5100500106074460514000ca81d2a4040e400205900506032001c550381e1501c003c015140e040c5001c0040014402c850b008141005001192200580d4a070025402c142c1500000c032103c0e8001440342d0b0001e80c90301030024141d1410009000340300c2c8184054045000400076280c00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 512402715 1250 512401465 512401537
    0x907240206060a061211040e0c0d0b060a050a052a0708100e072601050a06150804151805060a1d011103010e041406042a05130c0c0503 59
    0x118400c084010032406411100f01070718205c42600100700760010172007010807070285501054114406200f000160140600149000303c0c00b0841044000c1c92041809014001c11090f42c000c508108544000c0034014006804241741400886a000e922600c001e4200185c03204000c3d003c0c1c0c803040043c010008140032400700380c00a0f08041005541610001c2e40c1c812a0b40710f40501d0741d0307a0700441d011941100200d007040d102594000c0c0800d04122110b00c00030f268500c19000c542240102030a2054400c1e400340d4001c1c1d410240041c000032100c13800c40001d04001c212261f10321410002e0400103541800254400c401005002a01810012003000b807800e0811040025914003185001000f010409403415038040f050030030560b6442e0315162001503a0380321030081a205005c200810007004070340b400c010b0006d02e01e00002040340b28294a80e02007185c06050382c4948a142500c038098803d82c44805511000c1c5840018201c164032007074250b5000b00031101e40c035500c0c116074820110101d00301c900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 512403965 1250 512402715 512402719
    0x100e010c030b3a0f030f02030c07150509030114062b1514090a1b050d0b090114090a1e0b040212010204090e010b040605030703031403090724020606 65
    0x100003060b03140019212202c0c0345103407502030741c25401030944243e80484804084060203c44048150600386140e850702018012000a0b145003040f452051000c829115001c1c007ea0007400118149500c4183c09250104014100002802145441d0f9402d001d81000c015103101441454202003080c00994102682d01288240501c6008515050384c107200459480c0c1280001c0764504840d01c681014151039610010005146801c0c80924000454110402485002c0c044e03040060980304d290078100c503101d013941c000310805069000c40e20020300d45502a0034800000751950610301e000e44042410b907a1505d217a4000b00341c2100300900311200101c501e1650102e90750403a100c0d0380740603806c0c2c0010320080c0a200aa484902500703002d4056801a0107140410302c000403e04800701c1c024960012258856410001c0016032428082030040a4a2300350303039540d0b03820603c80324100c60366001421411552044003000140c031000300c1c0f420198690407007040756030f000c00c1c007200034681000505024 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 512405215 1250 512403965 512403971
    0x70807060b1203030406050c0d06031506090e10020705031303030f020706051e0c0c040f09060501141f170f0405010f1103061c020603040606030515011202060c0f100e010c03 76
    0x82d000b00300100380ca5100c2d5100c034000c50103640c1c11505105c68064034811202c0c65040c880088200314510f1100e41c50606443e808004040c0c0c1d4800c0306080d920283e152244c0c51700032003a40c40919a15800400801d402201100e14046030f4140713004203042264070550000798400c00c01101c1c4c5605010440080000c2d01e0244d003000c44000b10101244030400c1301070400400050002c440c030205104214404100410400ca480325407083d1202400342000b007100e03c18900300000c598030f0030707203a0705511102021b4070481501e45403019007651407038024202c0d410f112040144400741240d00b4401480b03441d1102980a90741000c0c5041400d681003582c204030079508200c2c001c44525071600c15282e00010032100030030607141e281007100d80c0020800d4007071b4100c0e200204100c00d00c0341d50b42088048030b21803005c98800c00d01040003561099000c3c051078003044030180c60000035283c039102600b240064801a83c0b9240080301a0b6450000380035548000d0f2a00d034501a14104020f204600c07142ca0750b03060034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 512406465 1250 512405215 512405239
    0xd0203101203052a07090c0212070b010e040813030606170f1f0e0105090c0f010f0503010e061807020f01050726070905090103210c08030f0a11070807060b 68
    0x250407070144c00440103031411055503082558a41c40c1e50540c01c803403124280d40355030b511068840c0185c080e00321400007521038050403415104110040351540d5800c00b45218540e400c02d070301310740300c40806030003a00c2c1100103201c03410701003110381518801980b1070640092a18607041e07002c07141c10916a8021b4054100450042070a1400b25080b00c1686455080749030b000003004000000344206e402130a9190320b04010070007008000658103d403041f045500c0b004405641c0d00444d180c1031400554000035106200401101014019030f90b0020001014200552280301049a103060121213150044c0d01c4a280c2051a1800384110781d00f1902078030700160345841c1010021104981014032140c800300c004c000520791480752180c180900001844107590b5607407400d0200c040ba0245961103443c0400914078a5081e018481001625510511450031540c4150030410a900d00a050031221a268403450801c4000c40004045440c42074010607190140e9041800888401c1e00c01e05003c2ca80e21301ca0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 512407715 1250 512406465 512406467
    0x203130f050607030c050f0d0e0a0e100905060a12060f061a07020603060301061508100e0709031103010b061b0f03030114090405160905040516060504090e0309060d0203101203 77
    0x3c071848950503081090303802e072140c50a41c1c58010503109880550003518440140030354003030a05505811308482c61020b56454422000310030303400b994400c00c00041c188082089005c160801c1d50700007402010301807a6035441c4100100c000503c0da046170a0795990b407148091100512858000c0c005458883c0000c00c0220b041a5481c400c401001c0d00c55003001c80000c2280c1c1d02500000003031b1920b1141c5620425982d00064410320b02a10811203856190300040740f07120810324510b00c105000d035140d4103480d24646070058040c5803c481d564042d502c400c061840f9880c1c100062070607154070600646040b078061039450800207141c03003003000b40e0010001000340c09052041c0101d06001104e00340c6194440349410b618003130100d4005d040e089859140003640d1896a804188030714015000c0da43d0210f0181c2c0b500c807e0484038003400021134014081485242140d40c8440c1c4c402180b07070f0131649400c140400181c035a42000364080031140d0004100b108100007008680024421034807a09860125550 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 512408965 1250 512407715 512407717
    0x20d02030f31060603140105041a0f0105280f090b0916030509070e1504050703050412051c1a0f150706022a070608090a0503030a05070c05030a0203130f0506 69
    0x40a4020b2840d0480c0d140140700351940684002d503401031901c01c0301c0c60502d1030140600b200f2982505c150700800b8143d000441340e101184e00c00c60056065644507800d2004200041c8001680d10580c59401d41d440d5280c01c40d0160781078050324075070900c0303520141f40c01140d4050b284030200303281c003807010070042c031840b40d00044aa80900d505410040342075610500190f19003e00c5034003a000c641c4100b02403001064032418000406082503800784a682d071100015000c0d1030041e500101f110b48000b1030394a01d14466005011802d101c2c200c03501049440c1c483c41c2040d1243d0400c0d04e00001402225071440f46050409000381c0902a94801a800901070015603540035041002e090a500001c40c0604141005042d11149120859508100b082080325a40ea000240203075804070b039481000c15118000080c10040f0a0340c410011480d641d0b44640b44405000c010344494107200c8070707288003030004009102034507000149a00843e01c4d40a4803521101c000d903540d10440509010403014045a20f0f07482c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 512410071 1106 512408965 512409031
    0x305010906080a02010807050405150301050907021203220c09020309060c090d1e050a0803040308010e061018050901290f040e0910020d02030f 63
    0x40e2030340301140c60a000304000c50b44903416503c015885042c141e680102c1c1450f005041956801c0400e504007002c50003403a03020340120050210342001420f0951001c4548020b0450444c0b8446881ca14400030b0050344000b0030710860040941c080b4020703040580c2c0d10580c000d41c034946d1145014000d4005548005081c010300001c43c1140c1c440c04180d035040e84005215800f124429640c1e20442a44400074681645800d0380d44c2000c10350030b2003e820754034000d81401d503807890645802003144005800401c7d400c0041d00502902c5d486815408000e10b50504003581030744510800c005400466a005036807001c030400001c22084d200c2c050f01d1500c0244d12031341e44d0801e00c000250f10120700620300d00b0040601c0a01040006c182070408054000300c02400780c0300030301d10b00740b031031400d80c1e20200800c00041d0b000401c0c030508200321069168000c00305030780f601c5594030740b181101c0384644407 = true := by decide +kernel

theorem cover : BRFrame.Cov 512230215 512410071 := by
  have h0 := BRFrame.cov_init 512230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 512230215 ≤ n) (h2 : n < 512410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
