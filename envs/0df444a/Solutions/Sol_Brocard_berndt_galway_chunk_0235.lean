-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0235
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:38:50.044176+00:00
-- url     : https://prove2.me/submissions/c6f10d0f-2222-4282-8f9f-201c6d6c9178

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 42086335 ≤ n < 42266191 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 42087585 1250 42086335 42086347
    0x20604031217040507030b06010908010e0f010b030111030a0b041404060209092d0c041e05030712080403031202041203032408030412060608010608210a08060904020d05060a02 77
    0x948410040342c000c00e038480c914010000002d801040c0c0b2403e40e0b50007880305099031140310049401248a4200101d19840d080c65900c405100040c0082100840c1009115800c01e04040c142a80c519800502c4a00414404100491202d0300460003624029100060345c80c4071482150341c1040c2074030b0984640703a0003d400c01c000c3c103101d07882c070b0b034020b035075100c5000341003042c15074511510401040740d6030034408007010503880d0403100203c8006009000250a110464103014050350403a0300c2064801e109440000030f44255880e524120310f50003e00d440c3c142861a00c01f0f4403842c4040744030303904030340d0b08100203c0c550008190a440741406990006100100c0508901c9101c1180b005001c4441201404200c1c03404008121001c0c0e0b04e44001c020803004540c5411800b511140d00141825406e000001c1a01400094810380204102d00c4406003107840440300c090a201c1c42c8040000200241c0000d416810170b5400290032500c05050078884280355101c3d241802e1084d6171144649400141d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 42088835 1250 42087585 42087587
    0x607050a031e0e06040302010c030c050303100501080901060605030c030403050702090103200d1106070c0305070b0a020714010c06020f09090703020c2a04050403200d0908060709030305160206040312 87
    0x81d56400150340c10300f82010540000050702c1400740e444024104480c920048080500c81e80844810f1603205003129100d0909410710030f00c4240c5e60265900280c203071000600856014013179901141c40c142c540c0ba1540d210640c00e52800d0307000410648c18480b04001d5100142c403a41200c80c02035020b5186a105148200003541d80ca40e181011648251102800b10020031402001c0c05400035044484680c0d8204c545000c0f800050b8070742c4040d1a9003c1d180000501c2c2e03c5d00d00081c03885601540c01e40e4103031500c44103496100f407082c24513980000c080050360320000702c455004014240181042078201807140d40003410298080755200002038000c560716202d02000c01000c0080001c00c80142d0325074000c41504484031400c03454039841181c60350080f4042c98001d404094000700741002039201c1d140c1800369a07a4070344095403000c000407401d240010300000d0101d031403401066036035644499249552804c5865402c010300800007809400e00c0b06006986140c01040190301c21000307109034a403c0c0314 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 42090085 1250 42088835 42088877
    0x141509060a0e01210609050a0e0601061b17091801060c020f010309140d030f0618110c060705070c0603050106051603050c0f070302120106030209010306021806030a05090c0f0d110607050a03 83
    0x440c09860380e0a14a009d00c0c240c00100b24076055450600c0d01c10001c032101445191007803124480a44298a0301c400044026505001410142400d580174404c02410806500b8144024410440000c02590800c030047c5046401140390060500d00480c8603150390300c0e10020183d0000d103a10b09039202140300c554013901405288a00c4294031010072010b07113000c4541d00c240e0300d9051895001d580d142c3c03a00c0b65031b02c040f9040c2c981321900b4808640562030100385c094501e13030080e0010b450300c0c50b1140f0002152807180c01054140c864607607510703082c040c80280b200726400340320104605005c000d21450040d02c0b01048500700c100e06050003801c1041c80c42c0148101e4419020721000701da4107102090015844a49220b81182d511078001a51041d101c0246840d41d454450481e500c880c2c00000e1108a0350a908454010740d40f10701a55140c900c8442001200017414a0072070f00940018246002b04513045640000c0c0c0201804492074180b843c3c2c2c0315414188a10422804a001c0c20140e0407150340c001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 42091335 1250 42090085 42090091
    0x90e0708060115230403050d080105060a09060e030705030f0c19050a06121103040c0503010c031a120f030a0f0207080c0303041502010f0501141509060a0e0121060905 73
    0x4006010700e075040c4007000c0d04403000e801e4420709001c1c1d11101c0080c0c1401c0507402041c001402022251159103a03c0c0840d11460079031004000a1401000130030341e450700c3c2003107450060954442650b010700d010410b441d481c1009101e254180281200011507442c2440b41d110700c0c0495602a0600300c1080c0b0400880c600c41d050080000c0d40c04403030901c02601c81c99200c0c815503003942400500c1c2010304030303103101a0a090201e5485140c010045c4810462480828010741d0b40480c001d201c603208002c1c0c1241250020f41818001f41501e900400c11410310344003450a0345a204159480c84440c0d80d20985941d01108820001948550845045660620180001c0d0002c1c00c0030381508403000c0b001a0744c2e030146010b199200d05241e128078031440e000354040740f092181ca4805000350b695031041101104104130b106401004000300107001c1d4800e100898000e14030041c040b6040203070034441160440c500b881e4050602c000c601c01340c4642c001c4a03140411700842c410700810341c02c1c2012400c0741558806 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 42092585 1250 42091335 42091349
    0x70605010b03071101060e06090c0c0f030304020411090a03080f09030604050c0907020708060c030a02120403020c01020d0c020108042d08030703110903100e03090604030605010e0106080103020d0609060902040501090e07 96
    0x5041c004501c1f0110580e4104000321000b24480e1903070040c0600c03510600748980710a105413102c450074200084051441540200c03400c01c41c0460a00307503085988500c0c08020340c82268244144005100700d030190115242c036003101c504219000300400e2070b000007541c054403980d00400600c1e02134034000c141e15601c1211480030f07041d0f10703140021b803e54400c0301400c0801c040c040400090300450032036050b00c0143e45440400580f6007414203029450b40c2c002c4e41028010b0060500704050741d03008500c2102d9131541079603001480e81e141d8942d940191120711941454440030400007689407040d02e82c031807646029040c260380d00e00f03114201804a40c0c1d0041c00303031011007040c03190101310341e808030307100781e000c4800d071070101d865100f001c4c0450441c400c1c5440164800700119000c0203000b815480309060303800c80075807110a6621442d013518014400d01c002540024641d500c5c038001841c0c1c3d001031104078450140811002c00d107500103015281c00340c000d001a29518144541c800c0d1042202000506130303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 42093835 1250 42092585 42092591
    0x7180905070e150a17010f020306030c0d02040e0a030809060702060f0f060a0b0a0302070501110405150708040b03010b1c09050c0f0a08060103051507030219030f02070605010b03071101 81
    0x2039845548036030040c0b158880e51021100020f462401410f20f02e0b51194006100c003040c81e440360f0400c1c8066001d0301d40290700350301e000118203c4410601c212405881d00600034886e005400301044905100454100e8125480361100749024608001060059220707445a007401d1404440580c900400204020b003194480414001003404000005400c55400b45a0b590507558510208114548507030005400c060002000c83c0c0b042d516038040d10714030703100304001d00c00d8080c0045030041c2c500603402403d0380019500e11076039545238210003c03ca074902c50741109040035900e10070492190801da1200144001c0089c901718041c81e034030034859501040c45c0041100314511f44425030b86c0c04400105a010b1a1400010740150780e614007a40010450b8501b03d5a00c1c1da1603150181e12858511103041059080e10b0105500c030b4040e00941e90702d03080400f15649a0301c2c00c6a8200c0240c990300d50a803440603402c00c444000b2030301900800d800380c00d00300c08051340ca0515810081c044056003030b402069903d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 42095085 1250 42093835 42093851
    0x1c0f0203180d0e12150c03090c090103080904020a120e0a17070c14010207051201020703020c0114030403050d02272404090209041103070c11010309030806010f050c0f0718 75
    0xd00500d003141110b0b801d1341e280b5107003044054010324010081020544040541040200818078040154130030603030441a5038521100c5014040e00407001c0c04020700c100c4040c0300303003040b90409038050000031445180a1184000c9030482c0c1d070480346092941855604a00040000e1041c600150510600704614031440d284254554140c010254080e0071b005441d03000c0144501c0c0c0c0308203e4940940b5004000342908150069424000e40c0302c42400c5000d4098540000140e40c0281c0b00340909402a801c20b61641e41d0742e5404466650100d00d0403041c880c0e0038015101c01034000c02004008690040340e401c04441e2035410408070150403040c03001e0004c0c514840a0040d981542030320215540ba01016840300103e0001401600e182c04034100c03030040100401007903d81c0070300612800c9000d40b0381d01d281d01d040f06004405035043d02c0c1014000c00c103070300d0115100354403c4080f0041e101007890014103040c2400d200c1c07820008448851a580d5009007400d01c00104031000e00340002c0d00014081108d10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 42096335 1250 42095085 42095087
    0x803120f0c09040903030b060a170105030d1704170a0507030e030606100c02130504080409060806060105030103140a050f010b0f060702091303030b0a32151c0f0203180d 74
    0xb00c112005280601e0301e600c00101014001c1e000010540030051545807103190442008251444121300106c0c06500b11340001252300300803a4162810065645101010504521004045202510844869100d104c0503040340020700050a044400c5541b446d81e103003840d00f00100b40d03010b80c260562098104805200850b07448100d03034502e030802402c010906160900026500003a60702c14100707044e0034001000200002c00004009941e4a16010460760380c6442000350b9458049801c1408500301300014004198944408031605081134100c07041032406507a12400c240e51102c0f80d0302d481c3e4403017910440f0780c50104680da29441d400d9603242d040c2020303030300042c2ea1540702501490308034440c2d4000d1010306200b608601d000c444080c00c603902044e41c3d0100005a803e006030740800140e0005180408a08051001c080c0301c04000c200d54280c0c2d1701454009100d500c803003440d1034000c0141ca00c161000580b40a0748401009040c001a100d1514407003282c1d02058002001c1d1698110025510510b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 42097585 1250 42096335 42096337
    0x31409070806070f03020903010501030303091e0320030c0d08180c06040b130803210c090d121b0c05010f09030c060807030e010e070302040b031203060f0a0f0803120f0c 74
    0x200c81581307894440d90f080404150001e01c1040c03012034240d400c21001000745905a04807003441c5200d160a1040f0a03a00029003641c505090b0b4014001107002030001c072546248440703e5401070f6100c2c01c1d81e1501c9000403d480c42c0529400c031600106a08408012411030155420480366041ca40a0180780840f14001000340c4a60b0041c9141c0580100e0703260348596140354500e0260010000300c03540c5000c10100510a00403441544810118100003d6002000c003026a040349001400100f10b01d2060b0b52200340c42000207010708100138040554000e8060b03448222015034dc0114600300400c5d041500040c00010015801d50920400c20010000115141c0c0442c0447d002ca28200300e042e1100b86e0120090500040d07070000c0d070760904500c08601a000710b1014110780c8220380400c04401010241350b200d0304400290310010a00788005012804e054042003440e810080c4002c1c00503450382d48212040106412101e0150300c00f18440d003000e40d0700d03001660082600d200da0710407440c120704a0307003107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 42098835 1250 42097585 42097591
    0xc050901091802060c0708030d14070c020f0f0112020706051b070206160c05040c0302090f0406060c0206031003020301050c0408100204030b010501050c070906120312020405030309060c0a050d031409070806 90
    0x981400122455049001d06c0071b40060302404068a0b40c90400f00001c60140142c2d1a10240002241c00410001e07030140850103d00e80d03003c0c199151402c08502001460390300190018180210680d884620864a1009002003072140a0006080c1000f000ca0f0300440105180b052200004111400144c2e80c0c500555145130a010840680c501082c5050040e518450f44040e410508040c0040211501900078015241d801d40f03d948240c044602040141c40b5144586400728046a030342c0409820708800842c1c0c8140000c0d0703e82c0341c5681d80e501081c01c48208440d115410100420180302005040c8400d22620b40c2400c1c2c150704280c15a111010700c034106102382414040001003080700d460040c0580c1c401414401410041295030342d0481c1190404540120f00003400300081e1481c524a520a940544c0d00280c011400c01102100340302c01684240c021903898440c84035081c00040003040300000f65280c0d0f5a000c10480343c81c5014200295002d45101c4246e0003c02060040d0b0b1000182654 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 42100085 1250 42098835 42098839
    0xa0803070b01091404080309010b03010207060c0305060d0b15060c0304060306031205040305032a0a12020705031b010309050a0c080c040e0606011e03091407031a0906061009050d0c050901091802 85
    0x151f84c0c1c0300c062941d401480004016501540003140c0b1000b40826540802e51075542d58806002c90f6540c2010042c5840032130600804a814290215003042c15010f402030644074003404042c40d041d600c0d84500d01e5034000b82d02540c0042d03261401403007000551003041c0300506940c20818107003811585d070541c40e80150000000e210392002d0640b54944012100c4001010414064800a10560601c2d2a1644c0250303181341c0036128092000601e81000100901a0706004e0511401084084011000b5142d0b0107815504d6118050800c004204038614030401840038100504c000e40407902848280d508008030010700303030030100421010781d07001500e0b603698078000304e402004030045400941c02400d5000c00a854404c5801200c0c03200d610000340300c030a507030048184900740d89030180f0003040120105c6203c1c4c01500000041021410251703022101000c0303600707054204980700c1010400d05184480c0070340e01c138070100d4404c11060803c1c0d614580076015446060096001e184090f5808188503103000f4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 42101335 1250 42100085 42100087
    0x6080601090b07060614030d05090f01020705060f04090c050f07110406120b0604140106020a0f020307090f09031805030c09040807060603050a0c0501020105070f030e0c0a0803070b0109140408 84
    0x14096a104420800142160301c51054543c010303400c1c10b40052201307000b0100d854440d420041c42c03502d00000d84616416065543e145840d0424040c071074400c7d600704a00341540714114020440e0341d2101c000e0841540c111100303e4a843c9440c6402c0283c4103480750050920104000c0d103035410059034200c4000607040a60441c0312442070000c600100080c0c1e021b0141300c620103101c002048012a00301e4064801280e0521030b01845510403134514000703225540c090703404044c4850014111342c2c80d04051500040540b66030540e0b54420809490041c049515072590b02d02c6d0620030075800c8103010a4441392480c07825000c4c0c2c14240426544d410365035215104e03011035070020b8100100f21381128640c0741c1c444000e004040c0d8034a090ba03a1039030225021203441c0a05540480c66510508c0394902c100d00c43e40e5240e2550004c9001503000b043c0c3e00420202030b004460810b61107455101d20600186502c10040d6507402e0a4204464440d5060300300455442c00d1001c240012851801415005500b0030751036 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 42102585 1250 42101335 42101341
    0x91a0a050f040b180a0c06030204080606060306060405120c030d0309050d1d040207060905010c0206010f0b090d0f140106032105030903030105060f16060b09090102160303050a091502180a0b040608 86
    0x910f29011120170000d000d5031010b02c000c1603040d1b050f001303070080f5000101101c80c0e03a01c903801000000d001c1245c085800a40c00d00003040313a407401507504880d0254010548603030000d00004030f803c182c404128507000c60b80f168180420010b080240b050448501d113485510494060080c40e01040020580b510031134010450070144109036100300501a4800020008e65800d910007a46420b0240718041141000d2031000950540a0301110761900b401800702d0010b80070340c1d40d2140345148142d81034526184c084281d0000840034414540907600824440c0c0145803200088459107010071400d500b00300051080c04044c3e2000400c1d61b0541c3c2044035075507146e0500c05501e032010b0186400b00b40f82c100b819640070b4107028881e4001d0421240968100d1003503660401d049080c1c4c0702c2c110b00c3d81c000c9401680308101103403190740200e030040f0410b940401c00c19640d03124441c07940394100031043e1043e40040c140b4940d20003601c038568240000d48400e08654900b140c14501801248134450a0040301000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 42103835 1250 42102585 42102631
    0x209010f08150301141005010c030210020703030207240e0114011401050c03040603020a0e0904080909060a05120f0f12072006040803070606050118090e01091a0a050f040b 75
    0x203440c0b8070071800b8008010a101710300d00341100e080306644400e0318480851000ca03640d4441c0ca0301e40fa00b680c16400401004404076611002540081002c0d420140d090100b05e0004054002190100c400440c9042e40741c0700c4004000204d03119403d0f00b420a0b031402e440001503449851145044404000d0100b054000f44401a6124440c1d1844c1c011b441c0000a0081006078069000e040c00300c1540e61100c039504100d1091140d2031000755800303407607040d05109541551811500c034960101c0c01900c062032060b5524041041900401110074940e007100c0c02c04510280c082041140d909809001084500980301040080d0300c501c51000c0d205142d00840c02c40301022081002a070910050080350b9900d81d6411030311707100d03008084200c88007410601c0004207503208031041d003040034010081034042c42c0350000310002442101d0105501d552070742c0503180401c081c82880c1100340c46c6800030b901c4500d0007152510803280003c000510140309036042c0000300e2070300107081b07034001c1104604c003c0d20107807140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 42105085 1250 42103835 42103861
    0x50112020f040b0d0308180d05040e18010c020a03080901050403090501050c01020405211b0306010510020c040515100c030e01050304020d02120d0909050618040f08030408040f090209010f08 83
    0xd00f41d04068001c240b0710406a004506a10625100304024001d106260304641c55016108180000820500003403200c0c403504051150400200f6045a2588400908150946844040c00c00240e0402d212134424075401c000d80b994000101700c001c04c040e1509680150140d09035006060400c1400304220214800c2541100c0161200074040c00d043d16411592101014083c46281028026484800c8000072a007100903411703840200688907c0e8240014880e6450842da903610441c80381084032591a1241e11515001d034000030a480548062081480942c03d10b50341c261041000c4061845c02090b886650021100c009103421940c0e074070380780005001d00c05100c0c4040d40c801c130300000c4011140000205640e2900b01034882c1d441c1c0c26075460b151402c403442114031a804c05035800029980c420404107840e07003c0e10441583d103003904103480b0030820703400440307041324403c1c40002c045c0061900306489030001d00394080c0552901c1c44400000b00900c4985202100740038130840410030a1414107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 42106335 1250 42105085 42105101
    0x7080f0f0a0305090d1a0402040b0414070503070c17040501020106050d120c0c08030a0c0605071803080a03020f04140405010504020412140f010f0615081e0702190501020904050a050112020f04 84
    0x1500195015006c690300d0341c10700d05e0694040744610300e444c0c1131031a0740c20140030b4070542030030914113800c0a68640e441511282d10080038001081001c0444400142d440c1001c000b13080e021980b120707103a50170400060b0850320260045880703044504881c0f00003494110031600f5016042c40c1603080301665241c42480840342d80c002c2d500300e000220700c0d0104a43d000c2242001d00c1e01a100c10300c010707243c4d0070381943d0f08080e0074141081040d03c0c00050011071b07840c1005200c200801d103001460030030b074a545903000e41c011750001200d16401c400c1c8c2211034a800d0040341d02500d000c8804500c1e2502c0c080821314000c0b000d9100810b41100c401150318911024040d40d10300d42c48410080c48040c1700080c2c900010a658058a00c03a028125410f1003681e1240e14aa44180e50b0b00c070580c2540c1c50510f15605010304020306980442c0b00789a42c2c1c40001007403030301409443e071007840050b82300c007400d400300010340c0c0c00103010801280c42e00004103c0088170ba0007625015030113843c000c8000720382c00d0205000c2d1100c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 42107585 1250 42106335 42106343
    0x30c130b03040b04020406090203010510051b010c08010f08011109370929060c010902061308010e0c0a060e010e0d120206090316240e07080f0f0a0305090d 68
    0x700401c003e128482418920480c406c5400700111611007a40200b00d0000313004480e044003414100340c10150142c40101022040900741000c442d00c00428142900c40c20102080002e2902e40108000012a84c1e620003502d20b01c40240324901aa40c2c01034045d015800500d0321884070781903804034034013081a15602c040807400c100b4410b45808442106120380a22940e511245400854158440060f00c0c00414041107100704640341d00500810880b40c10450740f0002c555680c00b041d80046c0e4a0800070076282030b02d80300700e0003020720300180d1074219800c1201103040c03038220b0b00b010038056580c2c0c100182039501c1401c0880260869000403200e0007008c10b42182c000b41d5060b204401e103c1c10820a0072291029800c6600c596101c0c1c001c0c0303071030340900c21841c51000700b0480d041c00010b00d0109102c2070f00c3c1c40201c5c40050451103108010035100d002c500c101c1e89800848051042174000d01c4111410014403000304408480340170440d5882e420346102071300700303c0046404645c41d521013264400c40d07900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 42108835 1250 42107585 42107587
    0x18060f070c0905220b0c03041505040501050402010e010c0201080a0e07090f1a01170402040b0d0206030a050405070b040e010b090f060a1e031b080a0f09050a020906010212030c130b 79
    0x40350140c80040c103054401038504c1c6102c00032a090382c081e101c000c41c92581c1c0044003c05d107455000b00c210850708003501c00c82c0c44007607143d000c1d8a01d00061180e03500c51801800040390500380741c000034203406200841c060410124801d040b0150340c00500c0e41d41c110990300f1000409030007055000303081142d0b50308010100d81c00c2200248421020381c104070361101d0111b11103044403072071000564405070401001c55003500e45000040151a1660000004040213040e0103010041c5a00086007a4403c5aa4040c415910810b000c00d1060401581000d886805040d40c40c05050020154a4107014840d100c0b108000058122140e100c54003885582c81c0c010b4141a01e968060714080c041c0c2c3c1c00b000c105417400c0d4038449281412031107800307000d109a103007a50f010140c40480e10200d075203110040c141d2500c60b4441211158907407481c401d54035094000e202030142d62115104000880501510072030444d4815242503903103400c0032040382d0300a8451082d040d03441030200c0c8409140c40b059031224001000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 42110085 1250 42108835 42108839
    0x5060417091804060b03190507060509090411010507080301030f050f0d0507060504020406082a04020a09060806041e020c070e04210c0602030a02040905090a0b0a020901050408030403030c03021218060f070c 90
    0x144422503803051f00e1241e800e9074120b41c0c46107402c40c0c1038083c0007010b41e801201c076030209010640031001ca201518062608500d08003440e00c03803441c10350080c2c9c411591321112640c01401d018050001c11900c0e8030107400b0304a0348500710b07001041030058841c050b000b166140b010604550b610303481000107101d00405c0d1103188c01c828180e07100c0c400902594002c0784103542c42000c5039140510848004034020345541c8111400c1242c00c880c49280100030f10340191350f07040030b100d9500c881320303070090b0410741c0000240e038486817000440c0c10580b465200d002c50160315818400081c0c8000d074038000c0720f59400001c1d1a5042c4549c001c03250003200c1c50300904a03520000902150a0607500200300361070940c40709000588a031380c1707542d607116171400e8083d104004240c040380e48641e8940042001400516200381015103d8206c542198019030048000c14480184001015014400e40c0501913030400054189548e001e0108002110010301c6031103100009900ea0180a80c94143c079a05500500401c81d101d07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 42111335 1250 42110085 42110113
    0xb0a0602010e0d03060302010203122806090b01030917030405070b071514160f0507051c08130b01030807021f0207080f0f070504111605060417091804060b03 69
    0x2072110b1250b03420f409100384220000c4e0080c02984100c90341a40154034080804420b21285100600f040c1403041030070222040c0034840200402010380c541c00d000484a10301031410080311010f208890605060090000c0844c4640301c9010800402041d07840e80c0366034034070b8200d041400c6604104205500440e00c04180140f0601020340902c4c214800c00130081402032441c003200c0e0464903034084041c0c070000280344501c60009184485a1414102d043c9020755848a091005c181001410840310340d4004a0711a032000701c05400801e44601d40f800c9000c0c0f611111101c2e40140030140c51208005107100854541030041a166403450300f0306408512021002501c0e001180305045a034030440c3c2c002d0900c01008101d08002201c0c12008280321890402804094804424101e42080c0113000c501d0070513488071070b9007404038845c102030042850030303113000c1c0d04400300340c0c4480351408814400141c0c0c50700ca04180319048401c040501816642d00e242000c040c1c503c2d0412b05425001e403078a400608 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 42112585 1250 42111335 42111341
    0x1809020d0b0109060b0c030d091b0314010f1112190504050604050705011806031e0207120207080109081813020d09021302030603071206090c0e06011106042003010b0a060201 76
    0x43c0da2081d50034071906644225040e100d0207041d0352003806801c2002000c1e02d1001c81c0d44030f080c18511a11600340f0f1640d05030f006400c0300c1055030041c0d810710801c1c1313141003500d2000e101e500c0d904000003100b00403c1c255000d62031040d01403202002c401600b280c01080c1c00b01104146d441e0881d10b338100c00c0c40589041d1800580714801650f0865591094900200700c079801140022103002507100e00040d03162070404220081c0564074039005803d2441071486940d801e460000308001802901c04040c42486040001e140c80b0440d80803254903450203041d0f400068500341181d100c40d0f003010440300e8000e04000001d140400410446107114030001d1491148015600714500300d900840c0c00080c02c0302003c6905041e8402200c0156150300030600a0200414250000c10074601454000a0001c003a43e01ca40b504217003074000e003441d0540302c4100145982e102807003c07a070180d070340050001400d05503200c1d0203070f02c100082c1c03c0c0720702c100c9071020440b5242540b01c400340c3c1d90000c0c031210380c05076104806802 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 42113835 1250 42112585 42112589
    0x405032203060f0501030b0c070206040306020d06050901140a0b030a02090a0e070311030c0304080309100c0306170f120a050f13030204050c12070e1f08101d011809020d0b01 76
    0x40b8605040c84500c100503244149412070342c100c20a0340b4a540c80703041051039a0f200035070480e0700503000e0001101190052029008042600200180e502d00341800c203c01d03920164042c41802680f64200d41483d01c884086030115010250361a40b80d494407038154001c2d01036112070755008140328200040d01c0c012502014020035040c0c80402c4a07000c8648050440e100c1100c690620020800200300014805001180e20000b840d0545881480007800030080d01e41036410400041e490f000c0601c18124412040d01096048a000702468503154600d41e8884c410589883d0101c10080361100005004074201d5007080580811555a01046125514000880c3c00168011440d120000d428010711004946008030782c00c0b000d022550380d0308170484900d0110101c00b50403c050b0844092408400304210040d08104d441d80205480e10081001200d20f50b40e0113415040000c21135520701c66000c0c8111415502988102c010741040b01401d070010349141d0100940151090b00c580090104c10010581 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 42115085 1250 42113835 42113843
    0x3030c090f0b09100201060b0d05040501060e06031c14040609170d05040902070303060504050702061803180603130b1f15050901030e01140903070302010b090f010303080405032203 79
    0x2525484141c420307068580c502407092042c0c4104880026407405a5043c0752107420b620021031604d840307003c4c0c07000c10b42002900c0c181003030302c3c2c00901c42000b07000e01482c400303803062541d01c203024030703010000990380c0d80200000079411400d41c40400005100e03a606c510b00140208085a58a41e10700b001858213549124a001000f01d02c8900006090041504840c607012552030707506260078203c495009601001089080c90345c0e031080040c183d02c89004240c45000c0300c2d0007420365071400c04083d195242c20528049030a410030003075601c3c2c80040c048008a02d0380c041e2916622aa07034681b8012042e240510058a03100c040381c00c000004101071040c0b01c865500c502c101010759512280b201807010303148006030105101303100d40d11180d4840d610800c0c440490b003002003000b06d40e00368010024003003511111043c0d080081c001c0c0516409014400c0e83c03210a440034005441d001840c201007210600004042090000214091080800562346c030803580c1d5184462132003005011456003600d42c0700c202c07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 42116335 1250 42115085 42115097
    0x13060c0e0301060b030c030c030c0403020a0b040311040905060109111c0b0102190b0a05090c09070206070e030f0703030f0915020a030801080c090402010302090105070b010909051908070201050a140703030c 90
    0x816011300007000e9a00a031018441316046440c1c203143c0d4100e0390002012006d100b101071000001680d03551690030b0040c008607030b549a803241141001041c2d02200305030280940e040000c03200c0003c900040407411185101400540340c50399030020ba80c9032080c0305131a8110340c5511642c031903600c0568049005003000b602140c50007030104411144c0d0b90309544000c4c00720100d200008810100c03d401c21079000c441d070420f65010364006000078092080c15501000140c0c424010000b04a8111060240c40a0120010302c0d070041d0100742140c1d108c0507404020104007400920200d403d0180034050042c0540c0900e504103003003011360007941d85200300ca0a0b40050241d2000040c030000202d0022074440340a4817542c2035542d59001035000c0d40c421242c2d58104003041041202260f80510540c1c0a401c40640108492440e81402860440300c608014210501c1d040d9a200041050044800050342802d0850326a112a10f0907585542d07c1203603419060b0340041c1020130160306a00c59140480079440392 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 42117585 1250 42116335 42116339
    0x4080d030c020d020703031d1e101103070807020a03020a06020c0108060402030112030e06041503050108010605060909070c08070f0303020a09081c03110d020c030406020d020a1a13060c0e030106 85
    0x120f0355032040c040d5000244c0c110403014004688982c809800b180b16030340c0c4051101a07014041815400c40c89040c00a1020710b030000c0120b480d004203144c0c42c0c2c00d03180c5018111a945404500c0d164441c000c0c3c010105000050000f0441d21000701140040d5002070518458560340c15002e9150101d8448181c0022542c074001850380c03800d0301c00e490585a4084032640ea03560a940c0075624040541c0f00694040400e00000031140c0403024508202415554081019450b09402a0a44c1c540e83c000e140f0909003848980856100c1d0400150700244501c1d0000050310341d800c10901512829901401e02940002c801040c0354064000300303000c004541c3c0340104141e662180540314061403132001d00c1b603003000350404001c5110780c0000942106c0348011914200040b08a00100d03800070010907a2604045800c0040f00d405001c0301c400100d0034000381036842c551b941d90b107018a20040312480540d00c50f10101c0c2d455411040350180007640300104209043c8610b0300a480d400070a001c0c94861b42c20b0040c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 42118835 1250 42117585 42117587
    0x90f02030411060d090c06020f100516050d0f060902071b060806040b01030b1e0a0b093d0909060b1204140a1a0a0e010c020a0204020c07090204080d030c 67
    0x31a8480ea41002500c41114001400c10200360301c06040c0310062900c41c020400410400140800204100d4000f0400004003074110f0f818403010b42c01e542000e81c503150401c0420b40411210301403290030707032902a54460171600c500300103084082000d07003076618114000c90000d0040d03005002e1035007d041010740c80b1401c1c00500c0141c018038068600001d00c4800403030b183d8100b03904024411030050402040180b00d91021402e1000581821500c09a040051102e40d041529803140608022803002d40380c0031440c40030800c030540400030030f20754100000318038960600001840304c900390034039a800300b80c54034640f00030101301403070041030592441d04e603000418000100c22182409410001d102d21341d0781e26240c14414a070401000c121034002c5a20a01c0001c3c44001d008000074400e00000160341812034103502202d01444003405160314018541e00b42a03000035510034001c0e412603001d681c3e0001c003102613003403172090b41c40111401e001043c040742c038003008611510b844c6810b40e0100604000303814 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 42120085 1250 42118835 42118837
    0x6060513120f0215070204050408040e0606041d0c0c011803120c0917150109140f06210106090c0905030d030b06030a11120f06030610060f110a080a0801090f02 70
    0x600410100e040000b450060512054082c4c1908030078000a08000c480c1d004502036900848049518440007e0140010f0389403103400b6800c82c3e41034882d10b0902e42003407001004401c210300700d4518190b8020005022000c544100c6403042c503090006e001d070080c0250200700b01e0140503000c401041000c11540452040341c404c0c551503010641d00d25800030b1034481c14804910001c0d820850740d0042d45021495601d45001841c02410240c000203010214010b13005000503015090006200000061020344c1e0b0b100d02d50103490542c50080d0480400701c48104900501840e404200301c2c2d81000090055150080c58a204a0354241c00751521030300e1040044085036040c400003039100000f030000c12510100c6901c8031442d6000e80c080c2a2928901400010401c18100c03415030000c141e5104200c880c1c1014030003e0342000420601640381c0d400e100c405030403040c000701c81404011101300c404600752410488007d0540e0411002c0760b440854000042035008240603c0803602c2c00e140d21120364100300e03c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 42121335 1250 42120085 42120119
    0x1e13020309030d09020f0306070c03030e010218010f1e021e060603060403050a09030b01090902180108030a0e010c0f06060314030f040e09030909010b211909080d06060513 75
    0xd1440e19880c0d00e0844004d041003041640c201220100040250301e0400009005640710703104c96511001900d0001d0030303541c040020903901e900500040f0160030100c11000180502404d2445400184071021600444243d00c40c0320807103800b116002c1c01940104001803040341e1243c05032000380b0300004490741c81505844064040d030050b000500400d104101510710450949808440180da94440000100080e04180000d031b82d11030034a01140fa0140e1005092030340b07444041541d6242200c1207448c0d002d0b60380c18509105040941365020382c862651002100d0740080c4c005081000c508008008003800d010856003400b8403902d6003400000081521030165400030b80529190404241d407003000e50281c40c03201a44070034064482c3d141c0d00c0e42d00050103880300c0400183c443c8078080d2400f0f040c2501020b0030301824244000c0c070526200c1416901400e446111000c1178244e4a8503103610244039158850030340d2450044003198075540702008142c0b80b00d0010000e4609074941c1c0c0d00d41a40c2c0303420 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 42122585 1250 42121335 42121351
    0x1b0806030a12140c0610120b06090907030204050c0a02010c08010e0c0a110604060c020d03060509040206070c15020c10170a15050301090b09120301051809010207021e130203 76
    0x10754406002611945980340c0c0b494240c40c0c5400d0101c002c0a010000341c100703d0800b803440c0c0148041207010344003913902c00300400101d4540b42804100b40c43e08605070030094090b902030303a0001c00050441030b081025030003e55020700104410301d0401c139280319135002854401d0040d428a00c0c1600c0a901c0391800505030346042c4902442502c812001d5070241d400b503c400710901c05005203c2440b07540501c02e1610582c064031020480c1c2c1d2102a009041070003e03901d070710526160000c280034030707110aa000f030b038881e034169030250b56500c45052288541285500510440c10142044c0c1c2803154081383d140420a000d8914901d4001654010742d003070b9160f110702c0321030701c902040012072a4019401070201800b5000002c0400303510385000c2802c0d41c44042003a142d0300a00c02c00c2c408403400c1000000c41c1131400600880c01d5504150010b05440c41c099401026a40143c0114007450402e504403800355500502d056600c0782d010040c03140c1ca006044c150761040106919424240d1102c0c02124401d200c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 42123835 1250 42122585 42122593
    0x2040e060f01091715010b030f07090f03020d05030919080601050406180b15040f0e01050a0b090d08040e010e04050c0409050705190902071a0112050c060d0e01050a1b080603 76
    0x1404c1144407503481402040506201c0c0c10885c002138505020414080c0c41c40312034042e900d00d06030b50b04400c1214040d000c7d608005481c07004015028040a4400031380e603040303403807000e2000070b8205a403a40c001c00c0d170b03420307404080400305e00000c01102400204903161502503980c240e83c0c6000b0030044031120b20840c0317007034030100100d44050b507080d501140c86640003c00c1070012000000a85080340c0042d0010300c1d00400c981414840403408002d00d41c01004c00b191303408101420040c00340300d94040e05102c0350140030521104410042c15500382e8000d000f51890544c2c666a4943c2e8198550a096a0966060241d0b40c503040040c14940140030204d60004001c1c50a545024241b040404022035401081040807501090b100c055000401046000e2020030080990001c41c8414800041e445400c03808000341d0980b001035400304241080f40d80403a80b80ea110700c40c0440c00405444090a15211946080100840c0d400f065002502c200c0c1042140001035240310b405a9001106a80c0c06c2e5150340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 42125085 1250 42123835 42123839
    0x70b0901050a0509061e09010306120213020a0908010c0201091203050609060907020705030604060903030513050601060318230c060918090307020a06080702060a09081b010e0a0602040e060f0109 85
    0x10103940100301801c000b521142c5068220317142500301c0d40d01642d0b00003e900c0001006407e641c2d00d0301030840a45026640d45140c55100d40c00074401384030f00004203041c0c640200f203000445018103c824000c00001c00280440c14030346070000c5c001c5c101c00408484111044810401c041d20030300c0381e01d05c0340030003802c07003c12521240100200004011f0203502184210740000c10f043c5c40600006000d54411030001c10310810700d1402805030f810042c0388841c1044e02e03100580c046038000030702d40d0441d0341c0c6090000e805080c0c0d5408100740c4803072010245c15424422080f84101c2c8447c3c40b407200e01c032114020b480c54111800104081407040311191603000030302007401c000310b41c5543d4005401c10800c104407842c059a0b54003041c00c3c030782d5035482100818110020001600c0d018841d480d40080250320421080c5100d940304501402030000303840b009040d00780900d52010003540040742d07503041c0c5070498100f007141d880c3c0031002c5d5200740144492520918080b40b814103056100e401003a205841d10120a4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 42126335 1250 42125085 42125087
    0x304031b080a03030b1903141b0303030411012609070905010602030a030b060d05090303100e101202010c02030106150210060303081614031302010e01080412050a14030f0702070b0901050a 82
    0x990720718107030343c40380500051b104d1808030303106040c0040d882102c1e048003000c81001c00c10b040c80c1c40001c034035949026901c8522103560303021084a0740703da803000c481e207845200c810040301e600d104840860a02c0c030b4a42403440c2949040c400040c1300f415003008032500d107600e50406005030313803080c42040e016910501400c4d085e01d001b90000d070220039002c1d001c00c7c20100c0e2049900103503401520410050b4100106000341072034012002e4004d07103080001c64034581811400b281c500e0886200f1350030500d5a8500b103a0441e0b125440c08840250010000d009a503110542030a1108510017110058480c03c140d50013508907034091001265050345503015241e5684031403903c0001c1b694100804c100c3ca081d00010380008c0c0350040d601505822811240052082c40090121b440300322696050110040400000802010040751541d10501e009600d500441038280c0700c00d440a01318001c1a03101104010300706440000e0707203202e2100c90b82100c208580e50940d40d60544a02452980052800c0008000301 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 42127585 1250 42126335 42126341
    0x120304111e10050f1201090902031204031a07030f05070905030705030a0f08090d1407030303050a050420010210090b0610110304091a030f150619030f0602070209090304031b080a0303 80
    0x280c160b03051300e103141503002000040d00d120242c2145d00c08a5030360a0302c60541c24104810030340190103020541c6824150b44854101032201c140060300e419808002070100361080d040f80d0080408040c05100e44d0030f0000c0d000d0b10104150186500900c50303180300260328135000942d103201507081810100c1e0801c1d1910350100b035a020b41d6074160402e000010740c000240d51000d2251145d402100584102401c518004058030005000024414282400c1c0404200751000444030622402c40c00004171801c0401070703090101d8141514140c929041c50301c01032140c0000349078440c01d0201d42012241c100d40c1401d03681c06124020f407180c1580140300030f1010080e203074040380b0002500b01c074036101c1c14061800079140407009a003805060f007084114450070542c21b01038a41044085854140680d480f0361100e250000703500c005042e504c5556079071801c2c004140e046803040c130f401804415946c0381448800e660b070340c41403000b12004400151403048840c8071020703500c16180604090654802140c900f02e0103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 42128835 1250 42127585 42127597
    0x3020906091306050303030f01030501050a06150305040204150b0301240522051002012f0711040b04050f07020f03040e0613060801021303020307090509030714120304111e1005 77
    0x10043c0e8490010441e40d800f00044e62244a21481c02c0c4415811494480c0c2540c0300900700950031410b080042c0460180c51500d480c01c14424900042c40d03170340d240001809000c455112014148ac409804070390802d02030010343c103a5200312000c84c480d00d407000c2044c201490074603280002403414400e0401e441c3ea9800e40c5500a1540101c40c4c41c01921040014000e4000851351400760390758801c008100010302c200006c148009510030b031144500001d08201510500c88010500c900b42c016000c4103a0f0f455000c0c010055014204111914000300e0400402500396101d101603c140024480c89410002c100d070180c45554200554a40300e502c14089140c8152071071180c510b031115400304803000e0074070203007600840481c1890000383c030b0b60052508001d501d4201c0604070f0b0602c002c00841004c0042200c0003103034400500025118000f01180c14171300c48030000031a00c54000148424864030070b031030020440045401c1110b0070381149441500e02d070000b0301d140d0400d55031160008000d01a2018083c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 42130085 1250 42128835 42128869
    0xe010308031009140619050303040911040b0c060402010215010503100203060409062901091511030c0703081e0702010206070e030a020a1203090f060813030512070815010302090609 79
    0x212650b2101d030540213580030001c50a20000400d4104011807070800b071421100c00742200c01000f032505010100c1c3e200c0c89603014102c000380d280d01c80300d021100b0700c0c01100d00038400e0100b0240c545c0c2150580700c0d1519000e0320164018442c81c1111640324481c006c0d510f0485500030000e202e94440101d0f0341020350401080c0c07641c8242d440120300082012800f807806010903c0880107550800308501a0304032003034884060410985c084c06001821074640a49031085050801090248410307038a1403070b6129182452003070b4055040c000003041a410050a8098084141420600c05484003241c240c0500b60f40070740180d010f28041503016000384021510320f04d001e816250301e005103801050303400c10300f5402446036074925002c0805065114000c90301500070700c040b00300404d252410040c1503200203020048002c0322101c8400805008108030755002200c00d4270342d03d01d441d0444029003020003c0310b10b0702c00c0500d09242400d140d813183c800c41d81c11443c01030810742400c01c2c04d01070200220b28084981c1c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 42131335 1250 42130085 42130111
    0x3040e0408210103032a0b04110d061a01030e15041b0b09100906020706050313061e0e030a0909020c1006080607020708060c0304020607050705090a0e010e070e01030803 74
    0x1c000d8007180c0e50810b149002011011029451490003d1207444005502200011030103401080c0102c00c860145180340c00030314054250300e4a0030300c81d02d002d40301c069003030f40303c22056039410811080b60040d85800081c0a03540030341240c030b0001501a142c003050310f45055003052100315500e94003080c0d2150000e000744aa40c0c0c0b01c10b244468481b07140e001c1e80040f042c03030f40046513010032444d248000c030519548514200d42424942107002e07590b0a9203020b030b0710501c003000c000562000c01034201070044580040040c040044004041030f0800c9011050350030180c20260402d900e0000001151203400c0c03581e50f0107a040c0c0c604620180250008004424076004800301a0045543e6001d000d01074460f08010f040a07040128000e1315081e03c541c032100c0c1d5038000d04208281d100c80c460030f41c1da00a805990295030307002c1c98a855424540c1a8115580c8944144140010b140790340c2e025000101c440e85c000c0041c50341600d04d8030382d580c000740300d800c01e455074010040c0000b0b928000030710b403c820760002d91 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 42132585 1250 42131335 42131347
    0x3070f150e030c031c0b030601050d08070609112e0f050d060b03010509090a0b070e040e0105010602070915080a030e010c05030a12050106110a0311070b030405010204031a0903040e0408 81
    0xca003141c2c4800f0390964513500c0460051815410100c400e600082204010040c2c0007254011a8a440051041c2845428452a100240160b85e002c03140c600380e0000c8104a007080354a009854110804c00d1076000e94120088040040401d89145008400c1107030501040020082c0c11100c61010a2800042000030300c0314070001040d0340168400340c101f9800c6141c40b5030500c0c00344149000024400801e03507000c080404042010404034982100c040d113412410840410085009006c908064500c01c0d0300c0c00c13000081c004d40c00304200341950700000090001740c41d48600d072510300d0b101c0d0041101a800414580001078000d46102662a0301130511040c9558691610780c2560411040704e000b24500154401f000759062003a94050111070500c442a00d03488003041d5a162818140142401002d108840d0f541108114000040600180090792440c0528005000c0d4201d4802141d42820100301020038030700b00c1034110703c501034401c002d504084c5064290340f400180078005540c0301108200c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 42133835 1250 42132585 42132611
    0x20906180108060108060903070807020f0a03080c06010e0c130b0c01060e150a050409080a03090804050d11030c10020a08071502040b0901020d0203030601090b090a05030105040302160803070f15 85
    0x9114001c14000010f04110340c0341c4041c46040a8005144841c0ea800c00c00410303000407000005d880b80d298046e50300c01c54030543d02003c101001c00c0b41c2c1000c0d040040c0450401c103030000018119050381c7d146101c21000f5100c40c20341d082280202a0a10180804030200f40f0000c104500a41440595000007181c059510103506880420a6594414804587c072240f0040d08082070480001d00041d6000c010000350741c0c80d00b010a000d11a042c40c201030300c541400d0181301e030b18002e0350064000241101680582450038000c074603024004180a80101001c0400702e00d4070840d403400f1548547c0181101f0341d11941c0f2122150b200500840c3e50000154030f04030150f00324800b13070018100c45107210395113049038000645054540a003200c2154000c00c1001143d9a00c07500e448201c41c20f62100989803c174401c0003500c002e41c80d0708195019031900041006255000440417000107481380710b8041151a00c410a0722441180300c040d01c0340941100365070000d098008488619044194000352903052001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 42135085 1250 42133835 42133879
    0x16050307020607050d0807020d0519020c090a1401080a0201170705040306050f010303020115081b0102030906120f010602031204080a0e0904080406090504050105100c0312020d090309060305040c03020906 89
    0x80182d5085e880210281030413074100e00e1040c0c2200c00fa00007000ea40319081070007880c61107004180e410700b00400300d100556500030006413040400c010110b080300d01e0441c0c01c030740042422035807401c00c0a140034000118200041401e28241d40c06079645c604985209076500e401c000007605070b80800c0320070400000850314500c82d0b1070240f94401c20b0404030754914100242900c80c03011301000810080881084104d00c0003809841003010200c144120804080041c0d0541c015103400a802000002d089215410070f911400d2050100c440601d0a698840100b01d030b803409900075822900071084e011602080d00d20001d411342c4055840e000b01d000d4176860116000410590713003165400d00218050003015004070000d00a4081a1010050f130f40c90a40090b408080c0926206e0a1087c4000054140361062440417902ca82c2407074155500c0700005c60041c010400f00b44190005444100003141207486030198a0203507401c9140c00364801d042d03408012039001c0c0901000d91020090032a010381001c841 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 42136335 1250 42135085 42135097
    0x1e0f0603020a0311031e0a090b010b130e010b12040c090c0e03010513030e0d0302011401030f06050708010302060d0f0e0d0305040c0503030c03041e05040e030306010201060e0c160503070206 83
    0xd500981c44001e80c0d1000350583d244100101901e8005000300460043d00104c100c1d014055091240d40700c0d2203075030344d0030014810ba0304050a92406e48001143c402d0000000300402d80007580480c2c441c03551151100100741c400e000b01319540400300410031720060040106900540100078040b0b0b140c2d81e600240c81165100241907000c1825042203202e145400e216882c1d2001202100000401c50342e54014803000a0005143c4243d018240b19001d040c0b007580468001c4010640000d05540c4a0030511400000c05500700e03030080c10302d000030310483e21501c00581241d40c0130301101c1c107000b030341c00009010341004011010030b59945d0344201112201084400056a2075441c001449c2c24075003442c0c00f2240c05d90300868040d5104000b0b02c1e040c240004100d0701111205030300c4c11401300003a00000c1001080d03501c0694060704000342d07660388803004001076000300001d070003c0001e00d944420304d403685882202d6078050144240000c210082010740441c41403446032094a25160720356000403a10b402503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 42137585 1250 42136335 42136337
    0x2011214070e04020a0903031107050a0f08060702010606050a21060f05030105090307020d0210020f150702100902030d0509010306050d0b090706110606010c03050c07030b0921041e0f06 81
    0x60041c455081d800150104006030103950561802006410190491480d40300040c10040f03145d00c02005100c042c030000c03000c1d01c0001e29a001031690745036040c002c52040e010f103040c203002d0540030485c1140144501400c4031016100d9500300040840c007511000d006020f10340701d521034041141c2400c11680300e40c402401c10300c0a210080d50500d010705084030702c010300d0014a40e00130404180565194401946000d90407150a5200b00301c00d60102e0034100400a025124072944002601e80c001700c5038820b10505190342281c034400c0d100305070b81069501e4601c01035056048001000c1c52184218000c14940a060401054007a81c1e0070200307050807078807041510310348806800d1195070310052000c84018201480d10040708500030311250388a5001410040c140083c1c03a40780b904240c0990252505040a4410707681e00c00da80341041084c1e400c0458000d80c135400340301100501c850141c86a030000385200d00e00141050304211403850083c150100c41041c4800310003000501d5203914181c00702070921 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 42138835 1250 42137585 42137621
    0x403200129010203032e030b0717070e010903031d0904060905010506100e06090d0203060a060302040e030406020a080a091205010906060f03020d060b1315050f0604030c0909020112 79
    0x2101e0705a800840e00c080d03045400410500c6081c0e03801a01e00b810b080f0f6403108495200d40c1d0824a015076a195900c000e0000f0b01c03044c10042c00740e811602c070550800f0f038a258981030350350308401220907042241802d40411030030601480030920965001c03211540c0103020703810656180e00094824002110110307012a147c0240384104542802a690440c00680c0d00c040000e405403805403034864001001c0c0c1c0280310105400080b50b071081c038000342d0300350041d056030701d9420404140405070909000a0380924148100410b008070000112000ca42e4980d0150951011300d039503587c0907030300c00c170b80690400103120404980c000c0d60f040d9a610451281000240d90b005030714041c0c3c16104154040c80e14606d840d001000980c4600d1141d00103680d05c80400250400c1c0c0301c00164071200b0b0300741a1080e8501e010000074011030a138081070166041100d1540d490003110042045911035400300a02d0b50148032020400344a181d0807040d041031050400740141401e440d080e030101c845000362070303800c520 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 42140085 1250 42138835 42138881
    0x30203160804050312090616110409080919060c0b0a141303031505060901080901060e0118060506070f020904080702190e060103091e06060b0c030403030f02060f04032001 75
    0x50100017800b001303882c1e0160385003054540750008000c3d010b4040c008440c1c3e10216213440422107052120450030a005000b009211481c0c1081d880540090003010b0042e180302e612030504001c40c401d40f100712011a42d824100c0c1010b550390f4204008041c4c500ba609503294010103421910b0008580e1240240707070041c1c041d2429038100203013614040550710300c0144100501740300940341d28089030403000c42030a0240080d11250081c500604141d803007604820618000482e480003404402640c03040340300d00a1282c0740d2074804100c1103119500d001024055225020340060914141003980f00b4080c076480c609095082d004107441107500300d0107100d0448052418000d600880300b841c2c3d003001e028a02009001451381da00315080b4a51240300200300c0041ca42c80040003613680000019044441c6210784031030741c1c410420381d40c1c1c020303000880c003088081084912451000854074030034449146482c0b61511607880541d12815000c0c450003ca60b00c003002401b0a4000340034504e280ca21410f01039003004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 42141335 1250 42140085 42140089
    0x90207140a030c03180312030c05091908070803030c07060c1e02070306110306010801090515061303050118080403020402030a020d090c08070501110c040203091c03090b0c0703120903020316080405 86
    0x445445c1903150310004900f003880031800c42d210101e0040c801c2d0600145d000403910301030354a8000c01d40d0300c6034010401c00c0c5802107020034402d074000311050503044600301c40e05c44040e69100d0008031042d14100009001620102c2d0a58116001d8a141420516046e020310000c4206c1400d8596803500540d0280c03e0410802204e4403401409074200c0310f910b411402c123000020700036501849659544c0d62114007003006c0c0d500c3c8074039003000070b0300c001c0010b07a640340064030080c034007020b40c8002e80b00c9500c6c104450b33a265440c022040081c81d0b0110b0481e182a04690800c0004e40001c7c283e004403590900151031040d03028030a54184501400f0050300031031404031140c0c80c02d141d036080a81045031405010440d0000001c1d04000088200c80150700c983d20342c980305161008030602c100038440309030008046582c059100482c69070181660410a41d128a0322120b03034450088018001806d407030b82081002c1d890781c098503025101e441524a03160314001c0132681d9038480d82c4107a80c4040c00284c204058 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 42142585 1250 42141335 42141347
    0xd081603020c0d030b010905030d03090b09030906041a040306060801020d06091e05040215070b0703050c0717071401020f090f030601030201020a0f0302120a0306140904020a090207140a030c03 84
    0x5018545001e518201480046a8560000d44500402e054550030f00201070313030007856064080d00b006800c5540b10019004010007400e500d0380c040e03841c01c4131240415001c01010085607064900900f00c10324043c541041a11400d00303058503500104003e000c0480001c0460054000808589001503214072030040c0280403199258095643c051a00d29280003803540f1100d242e50610107144001069a00ca00100b43c2000c100000034502c0d580004510042003008040d40b4003418659804000e542c0d0355030113004442c840d5582c0509014020b100d00008102c02e14014582244130b03900602003040311030401d03420381c0c00c03060060102030381c04181e20500f8201002080c01805c0c045006003915403550300080d444212000e00507102c42c0200000c1d805240c0204141c8594142548041e9680c6074110002001000c039400342c072035108610ba400841c00d1030a454614041c41e0000d01c0e05e02d40600c0d1448010003580902c1003102d601c40d01c00a0b210900310203010b4114402d001c0c1c0c07506001e0960502d170040007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 42143835 1250 42142585 42142621
    0x804060b13020d142401020a020303030c03070f090501020a1e020a090c030c080402090c0a0512010602070f060c151a04021801140415050306010c0501090f1506080c1507050d08 77
    0x2200c1821820015148806444880c6030841031741c3c002541407107500103e0030b0500c001c801030b4041c44004240464400e280703004601c03403002691000030340d00c00210100c03140e10541c801c090042c0d03c2180c4400200b10360306414102c0c483c8100c000702d95290b2960200350717298910303400b25003000d944907000004c0a0300b600079001c40d1111071500c240d0914240d800509000000b800055180a0203c0c0d440290fa01800441c0d0310103481909c04107840da5070f84002981c500c054020036080c10907620380004c03c1401580e0030135031a0350000300351a820082084400080101d660b40124083ea542d02401403030f00c40748000d1044009520010740f500c81c0d180c0015080c44030096a041141034104002c01681540030780c1010380415919003255681c664200480e04201c0c1c19a01828651800c0144010480d40e08000214180304090441414504201700720445400e482411081c1e00030015004075450601e10041358103211140c26030420352551540e518000000040c01d0100311030105022000845103480c0407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 42145085 1250 42143835 42143861
    0x4030e0d051b03010b0d140c06070305090d030e06040603050a110a08010306020906090406090903080c1809130b0c030414030703051c09050105090c130b0108070804060b13020d 77
    0x8100c84041da201d40d9200c5400d492031040a003500c20802a9942c207400450b04030a004000212102840c200321020112880d030151562041c0c41e8000058101642aa001641c15803246c3c3d00341501c450900070000b0f45c1d142d0850800c0300401080c45240d4407407000e44003819603940d00081d50b140960082d012214500d0102c0a03000061042440c4154040d83c5036041d40c0d8040400341c2c41d0035052000c281c440c0100d00c00e0503070044c200a00410150b0666110003200c40c003d9032801e106468070407c074540c1d4403034102d400008400700d08980b02d0605000c802c558001a4003a06c141c02c4212030780b11000d84c144c0640c0d107440320300000800d1006012404e801c140100203114060340c50300c410795030080e00c1c0c2d2003040d0f00407141c0005414038007070440d16640608d400c0c580000c0203210301d141006d000c1e03441c0d03084054054030896014502c2c0901520f50300c2802c0c603c0d60181c40d40131b1107071614031099075134920040c0100ca203640c580c0469000e0340c031846841010b02950301700140e11104400c0d45c81040d2104088111 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 42146335 1250 42145085 42145099
    0xc011508070b03071b050d11010c0305010b0405100c0203030c0a02130515120102120108030a031103100e060a15020606040e030903060103030e0301090c120506010b03070f032c0604030e 81
    0x200c2200350302c01c1107a8102d2003d090002007440d264024030401c0d804044054041d004804c0c0782a48650003c4046100510303580c0200000ba030003940c25012918203020303916400344207104c00c0c0b1050402d003080345c44449950401a045031030742d0740080d01c0e5038888050809150011040c031001c508041140d201c0c040000307801844245400c0f594401070080c030200e014400d10b91006e160b10b14041c29412104aa913a001481c1072546c0c40c0c203c01d55a0fa0700c41101100064034141040102c204050250782c041ca220703045051202c1d10700254907410150181150758000038030710001601e03d506600d0201c100315140c025081c0c0c0d01d000c004000481d0180300080420350002c010608442c0e0340814658150713941801e000282450301da022900520074104014004400c601000c0f490798050050110103a1041046617110b070b80706c0c03081408502090b5005400b060399240802c0006010b90002c9001c200881c100000c1c1c21000f010103044010b00c0b4521107901d070000014001803680c02121203554403400d440c95 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 42147585 1250 42146335 42146339
    0x9040803040308100308120f01051503010905040204020903070905010612270501110c0c03070501050703140304150203010e040615050f01050c010209091e0702070605030402060306040e030c01150807 87
    0x1092080c440240000c0801540400241080c42203c0d401005581c00901c0a501c60007400c0481d05401000e8481241e000c1d840d400020b40b03458030403106041c2a071401e5415085900c0c04d00c80601910000d04101d17841074090148400c01c3c0c40402c040e40040c94194400325095250210103402d03200b0904212128a042a130640501d00010440c10004070401d81108100600c50401d41d006110200d6801242071001442c550b00f00e0000840b4000f00800301c0c1541e02c443d0b541c0005444c20f214581c0001c0100d0000c0303060110500840c0c0c0550740c42400741c40e144c0c0075824452142c204907030090300b00c404a100e0399030501091000a20483c45801e0300c020085100900b48070004402c0e00420318141c0c100400020215403074202901941c01a0101400b020380b80c5c10031010090074403039400e060541e400300c80000151420310000741002111029101c09256845640034071449030300041485400940b668549600c1220400050a81c24005000050000d686420000a000c0d841d880507505a02c04001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 42148835 1250 42147585 42147593
    0xf01050105070f0201050702010e03010e010b03060f100608040302030d060b07030e0d0213020c210c060a050c071202160308031605040302100e0a1212030b011d1003140a0c0e0904 78
    0x83c100ca0150242401070700c460551004a07140d40800400d1034055080080345805680d05410400c0c40201c00c40550703890743c0c2da1030040c00382d464040356106902c0c1005070040108901516001b6007040c0a44192031030512540d03d40002e59402e58400c0094180000d4550185a80041a407001c0c06003181c04400140741034000615441c079041c2c00400c806d50000f0802400d80d002c104020201004510070031420320023003620402da1b005508250703242e018290010b000c00419201d058810007000b10800d00f884900c1d00c0703d02c0072420110f41541075100310310f800c4580921990070100110311400b1030b00d80c1c81c034209422040b03400c4010ba400007801018041440103a49111102303d0076a00b91510107000307007649001990106c0194071045002105401c018280a002c02c3c1000c01e0b401241c60074440c4503064030044501c42ca07a01c40011030003600318542c400e2480e0814a00008003590314000c60707054403d0154180728602502d411b0320541c0e03103a405d07600300d03a0801c941c083d44180032115620700b03282c907482d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 42150085 1250 42148835 42148853
    0x203030a063309090509030904050f010e0408070c0803130f06020a0c140a18050609060a050906010809010204050604060509090a021e0a0212030f070306050f0604090b04061d0f0105010507 82
    0x22191003040c034809041c04502d40b04071005801024159010b014506092890a4813940400380c00c50255042400240e40e4020210511341224248402c11030b0640e2182ca80841340e4200d80411580d041a2400000c3c1ca00710810141c0801c0b01011a840c441c0391401f00e1001c0744c81559070102040d504091050408a040f002d405000c0703580050380911414844800030340c5280740358204403100c51901c80000001c01c01e0f50320040c8244001d8548540d83d8403a0002c001254441b8400e40e9401444200080d0791944241007035504151400d00141c1800e84510004155400c01d400c540c0c00550302007007402c2c0c2da00d0300c511044c0e002261000110303d042a8074510100454040c005181c02040014485079010320800600340030100c0702400d40e443c1e0174036100c00421040269002c400090030b050010600e0720748444035182c00710004081c1880d007840c2040c101c0c0a800e03040b0702980c0c02a40ea040c0001c80340c4030303548103071520a607490301207000740b60800291004010681000c0d04000c814005100000c0a40c3c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 42151335 1250 42150085 42150149
    0x2090a080f0709110406260f010f050904020f04020a020a0c0b0904050a0606050403080a020c03060a1407030501050619020f0604061b0201021303080708090d0803070e0d02100c030c050304060203030a06 88
    0x300d0044800e0361601000f078004031f486200720b564440041c0c100303c1c400d5031040f1614182e9840103080d8181544d12801c01011000c107440c01fa40c4551800c0c2400010320703040e0700411131018903005848200c00319480e403403d4500c0035401708240c540c0000b581241c0d0300c1c08d4400c49078459a4540100249410f00000804600960200811441000641801c200d00030410880c929200400300d4038140340c1000810040c10034828070f00e200c80ea0304004518030714060b0280f50f060392400b801c21410411f1a039412421124079050300700550140381e080c0300e031120040c043d0521642c06030700c1c0481d1130078112503249100101340031001c04592042c0311004149940a900c070044030f41110310107845030300a042c1100d5038800c0e01003647d032040a150300b000821440d40003951050050743ca4005101c9141002d21102d501c1542c4002d500061844049103040d001d200090720650107883c005000d00702030b503203091856010750000d03c0540e002100700302c21710140d4040c500c080c00314014440c03024100310781c40100e80f104103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 42152585 1250 42151335 42151337
    0x2100527070e1006030b0f030c060f0408010e01090b060306130b071202070309030506010b0906040306020c01020f0c0307020406150f0e0f030703030509040f020c0601030f0602090a080f0709110406 86
    0x29030508082031000300010300c082d01906061840c507060880303548065140c148202c8022900b0100b2020092400c01e811111800380a0098140500b0f01410840c40d0f0780000203031406080184008160241c1c00d118010200320100700000e1b05042c181441c04d064503005201c4c520a911107001c000500181211040041f64042208401c6484619041d103032139a04003409050b407071000c5603503428964002d40d44412240154203460b000c0c0d0f01c07022450340c00d2007102140c0360004e00c2000200000783c0385a0090000e48200400182054201056590981d014410406165002003007000640c0f425204040052003581300340040000c203a400680040d00e009010030501840240c02d07035041c0c43c0c68200601140004040c0c1d80a00c4e1a0324001d084e03900b00d0003105018500e01003400c0b20741c0d40203208440d441c2d81e00706e00504590b8a9035540d1a0f0400f90860101c0d0026000e00002c94a5120f0706040b1001d0800d0070050044952560320b4270389824034581c00041c2c3c141c1011806881080c0343c004a5054841d5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 42153835 1250 42152585 42152641
    0x2070b01050a1509090908160503030708010b032a040b04030b180102040e0604090507030803010f210c1a0702060d05191a040c0504050a0602030a021e0312040f050f0d021005 76
    0x5040c48078060180d00015415024800c230311208000300400118441d00407a107900401d641c855901c60ba0314041190a01300c0b81305121304400c144121003824210f05c1101c0e410040c540b07038030380b211050705400940c030450382602c1c2d0130300348200303c80810007840c55016484001c50400c1e14002e0b00810600000d8092806180d4407101041030000034410000a03540050440f42d907540c0d208004032064407039200380f40414074900350f1001c0c6050600140d030040e80e04949000c580c1414620b580c00f12030411007042891103420412a4016205e6801900740801c15003030000d002d24045140441c0781003145882104145465007820303400c00400c8c2120b16000003603d001480c0c5c0321410307050350648500d421440c0e200c4100c513400114180d000001701031250710755094840000c1080074507110007803400c0c1441002d400500c09500c0384004003403020360281c01841000030381d0702182c40d41400c0202c44509946690451740c0b4030080c40e50100030407404503008440030170440c80d054541520700a54003424030820301c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 42155085 1250 42153835 42153851
    0x7051c05030c03060d0b010612060f03050304050909100e03070b0702010c090b03070923030d080103030903110a0b0a020d0206010611060402060c0a0210030e10020f160606080102070b01050a150909 86
    0x100e09400e0504158452418a55543c507000f01401b62740b0303800c0952650038106203000c280010b0030080002100d9000d40154289810401008a0580010440103052081140000c00d406450144c140034181c000c0103143d407801d4a040c4440303c03000007003401d4256030400540300880c99028960204031408522015126110f400c401c40e074088a5038008541a01401800f82804507441c8100500103012401c68034840d01c860800c4e901c802c000d10000d004985200c1080000c00c5500516001400004020070b100d0b0ba00d4400565140c1c00410f40350006a1007108142c90311901080700c2405800743d800e0001c028241180480d55861000300000c1c01006d021030b51000c001c0e402c002c2d28500c3c81d402072861150045410004004018465079000c00f4807407007003520601141842102c181c0d00100c00d1461070300c1c0131120000410780c055082110940d0f61000c00282d206c0e420710103052001d21aa21411942d4500400c0003001314441e084201c45854104484000c0c030380066107101110309291021802c84 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 42156335 1250 42155085 42155089
    0x1005031b011107180b03190809040b090103060e0d02010e0d030f0f05040503071101170106030b030a0b070210150e1303050708040612050f0411060c0a0c090207051c05030c0306 77
    0x42c580180c00c140d100342c10000c1030080d07190754920340040c602001005080554004c02d50b4680f00c014a030108807480f04034480108540720000c09030300c5d03c042c001240128800e00483d0500100b6807050f28050f0740c5014900c030f00042488a1180850070788024407114880900c01625410b03a2241441490303640d240031003450000e904940511040400d04100030310780f40c14441e49990104070704403104d40400c0380b1b280b841e42c0646d0802203c0c1c500f00404411b561700f0940154000d006940085606106641002000650401e409485400c10768058090002e031841c080b070503548801d010f203828031408181401010514450107a0055252181c542c0f240845e00301500c00e48981c40d400703002d0090000b00404c00580145940c80e800110401c10006591196950000d042c13043e28010880107401548001e240b80885c00390041004d12400d840d40c0c5010f0387e6401566800700e51007400d04a40100e15141404014000d41c0010050705020641a6149030030003405840014048040c1640210100b0425 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 42157585 1250 42156335 42156347
    0x50601081612060b090a061706040c03090203010903050d0605031903080601050706020c07050a0e1003080a050d0212070206061503060d1a0702010b04060803090616050f061306051005031b01 83
    0xc032041c601c04000342522000d00442170781c40341e400c280c01043d000d900000c0780c0b0b202c1c03a00c1c03c48046100c00c030a215900c4500401c0042e0110060311001c041d150380104c005a030707080c07150f481c01911a4072035a5603420120302082c103944040d07121503c6504068071806250160078050740b01587d140ca0040d101c0d65a620040c0c2c0c5078010ba5a0180c0314510110340396848040000701c6c0c00c1070318011030700350b244150f50320003005190f42c0c00c4500d2910403031021410030008411a0241c010718019040c05030030203035040c1e400c8040340c0041c40a071903007140c843c050001d00e90301405210341084003500c403c858600c4211a03c40c403403202400450090322f0360034000081c402c100c601e140c88503401084c103002a08103140000d000c2d200756244144694a0441e0010f03407140000101e8550501c0504054100001040030b40d0451801100c155094014020340101039041401818802c0c481ca410391038410116003061421140010f1a0001c600c1c00e4080600c160707940010f0940030400311954540f0001e000100407282c0d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 42158835 1250 42157585 42157607
    0x10501030603050c09130510061a030402010f030b0f0d0b0118090803180a080403080c0c01020d02150402120d0914010801050a030b1008031b15060109030f05010e070b0c0c0102010506010816 83
    0x5a40235408008403110001d822840c01ca0300087c1100b10ba00f0b40100746045980700c19117000340032504142000c007490303019030810808500010300c0e40211040c41408586000c500f8072044542c40b40c400300602401035510800c070b14030001e00008000d0351001d60b9a200c0caa10000e48044a52480c00d8240d48400104004010725103900c4101c0c0d545071a5649010181c0e50000c410307050342401024070b682c00551000600c0300c10112641c0c000c1100e40c1074100c0c0d07001000d0004c0c0090ba0810342c0c1c1c0a1240f40b040e4100200c4a01c50001c1d40c030104501d10303100d00f03400768403110301c60541086040c0c07004025540e554110007060303c2d08804e40c0f00301c07074685a5802460310120f40c80101c0500010078412501040c4c00c2e601108001d01000352403001d8000c1662006001b0121801b0b4003043c1d40180a00200324201003904ac200c0c03107140000f500420711030400d0724105850b44804102c41e0006900002440d0611500c03402d2002800248003a0500e0710019010120042c004008042040b680d4076142d40300d0065125 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 42160085 1250 42158835 42158843
    0x31003060c1e1107061d0604080d0807030b060403020f03010b04050f010515040b0a08071107030c0303110a05062202040e07091401060f05070206041d010509010501030603050c0913 79
    0x8031840304944040d00d4024030000c4444640768103660030015502034078400c4103068550010780622400c02d175050310712031030b928000012040c0c1410040b103a915010001c3c000f0348540f00003815003d0002c0c0d1b0084c06c2e0380700141a807042500700740300c280030b58440c03e01b80c03130699504071186da40e02248240402d004000c814030465103d818001881202c08a112100741030b15030035517103140806407a191203502071050344101c5800d45010401c940710240315103200c540105e020310f4680807a45800820520300ba005400a803200781c10108100100340d00988103002d100401c50144c0540b80c40d540b503154541030f00904429094060742d08680c0810b4820001c102025401071040000d078400501080e525900c41c01030344921031505080d09403103801455080d048800581d6000300e41d020880003120f103500f20000c101c1e0040b0041c00302103001450311500c02509003034400d498140d98501810058201010b90001d03060501d40b00c1d05001184010481d0810650182c80c0307072105448891062042464040b0050 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 42161335 1250 42160085 42160091
    0xa050a0b04111f020601051002060a05040c0305060a0c03060f03020f0d030905030703051f0b090412140f0a030c03180807080705070b030f0604060e060409031e0509120c0d020603100306 81
    0x8040b030806803103d5100c540d08690a0740e880d84244464184111401030150348500c0c005102001c81d5001641d00ca4885c07421110101e41d20b5039540c0c500705c02581c004003402c3c0c403004240b41440e4188100c0000304417074001440510b14540200b4003d00c92170400a005090144400d000d16000e1210300700144005003c840d241603603030400e2078544401c0006815021030762140941482c901340120030b0540d01c005d0980103541c8441e640c0d00103040c00c10103000d041c00300707108072000c1c5c8920610152400000c00c2410a603206801000103040302c040c1c800c900c0074145070500b120111004241c1212415900c4a0403694400d03050078141ca01c0d016804006040c1d1150b44404205400404041d500890340004d0429103611000c0402066030464041c6502002031031001a04603e403d80119118500a041110740c1c035010780124030342c4010380300d004001f0400006201c10b00d402c02d8450b64400000e0107018009804407480090010300d00c0b400b002c1c1c42030101102082c80001c94908407402140e12000c10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 42162585 1250 42161335 42161359
    0x3030c0c01053601270203060c070c060c0f020a030308010303110609070b07080d061e0906050d03080612061005011d09010303030e28020a06031404080d0902061c0c020a050a0b0411 79
    0x54403014a00500c107e000e8041d0202040a00c10b091041d41c0c001c1780d20100f80d103412800e00b442124005203481003599025424107616002d41ca4080052014600070382e00c44120750b0660031701514040800c070414826030311541c20008410700109054054910503010325130340d11001d081c442d03018069124429000352410300000b0b9582e84120909000b00740040f078460005549908050407220b40c0c0c03251981081125041e070300040d10500e071340d50b4000f02c010a0103007254050101d951130008200d6294504010420f414045581c01c00f51544100d07440541c8a0b03140e07020306021131044072062000400b8503440720500040f5070001d00c8091410070000d406000d6903890020400038407000000140d028560086000c50841c0c801c1c007408201000003e0308200d10340742d40d600c0401c1548015491001a07a40307403410801a550321b40202181e41040e000b441803440020230400807030398004600c0c8195401190071500054012641064464000700f681c2025510b07818032030805020700f035400c0e9014083d1544 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 42163835 1250 42162585 42162641
    0x41d0601020a02040e0705190603060501110705010305071416061a1f0c14070303030c0509030c0d0c09021c050a0e0d0f021002040b0d0501150e090406020c03030c0c01053601 76
    0x236400844419035402d100f00c0d0380d641e0065a044990a90464240d00a0b00041c40954001c3d001aa0002031515100307000c0e603265610300c19560008080503503e6041ca864a0043c00f03130034044d0540c0d01c20724940b408001d40500c000280d11101311a514200d99480c0b42d12012043d0041c0d503254401d5400403400e1000c100b0780f907a003648841840c00201c01007031410703c107800b8140c494015905980e00190013000305100d600100425809065800c4611040b4001c001c542c002440c0054041481c1c186041d000229000104600b542c200510f81304403980b501c080c800054400150078200c030750307440c10310300342000654504904100441400c11140f0740006000108040d4450003003400c1010058200320745d9880b4589206248007240b1607000241c9400c80646041c94810710044d0450720070000107282441c00b00e842821070f003084500c04181e40004c90804804039007030052940c40000365051420042060305125021010001c06800064103041103a1000c03000354404182d034400720104641c0300e220144 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 42165085 1250 42163835 42163879
    0x3051504091202070905070f050c010e01020d150e04020a050603130501090b01050102011407120c0309020307031a0a0207030203160204090b01091b09140105090d0611041d0601020a02040e0705 84
    0xb0318001031040c400005000c0100b40700d20b501550041e42c409070b000804841c1214103805c5020460040d5680f0081034040050034401003a0842908038045a9401e600c00c61001140d000d90082c07441030240002c100c0142c4d150b480b00d405a0b5405c5a006441e900e07545064001c4101400b0010300035881e0141e11002c0c407500302200c504841091b070090140d0028030b00b241d190001c054450f10302080e10004280810441a040840341e5401880d00090a03440e540002c1d02c2c0c001c0a6009075900000c5515803650b0741c0900030002e0344540102c200758607002d929a03001790b4038030410380c8522149080708491401c5598a4105582c00c2d43c018400504550311100721800400754400054480390b130f14101740c16814081d8142800b1202b0030510074140103c2c1100540d22a4410710307440790b002e01c1c071401e8500041d0003031050f0202d404040d1103440e2240c0c1000c0e004841c14884803070340e04070301055004010707440e1f0340021040e10040d8140d8000c120385850b0700d0110316100c140c5c3c0101c0c0d40000c1c0d0a505500815680b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 42166335 1250 42165085 42165113
    0x20a03050f130309030809030102070501020f030405070f0b0403060b0a150e13060303020601090f021210050a0b07020916020708100219170a0c020309040908071709100305150409 78
    0x40c009820607103074850b11100c006544500200030844141c01000420b01850103003c0064018002600d0b0808a0ba5003a003242e00a2504111038000803040c0420301004000310400fa01c0c8610003040740300e08100c41450940150f101c01410769480d04e204000d80d40b21614440011302c0c0c03c103e1541140b00e050000750481c43c00300800c034050540401c4000e010400c1d400742c8000c40360581c0142200e6420603c41c14041c00d802e04822524503020411070352081d007502c0c0000d02c0f0340c4c07801c030407140b40f41c1c00c0c00104a0f00014a03848500c1802d414400c0741c0c0547c0e507800601d0741091610315450614801800140d05140060740140258000c0301010318215003160004c1102482d1b25680103840071004000343c803009000100249060340880004144d00e081d5030201450408900442e414504800300003170990310040c0c0d04072915480401c0802c2001512189041c4407610b40c0c075590309050081c400f003020b44c0d0120002d141095110030203d40a804529007044d407541006d0414031008240e81800c0054403004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 42167585 1250 42166335 42166351
    0x40c0c0303050a2c030702030607050307090602060c090f03070305010c03151505031f03020d0f0b16050f0f0708030c07050f010b010905152701020c03030405030c101101020a0305 78
    0x1100009981030001e2060324288130300720490311015121030340420469448440021403e100821110340035960420400e8460000707540c40581e40c2c54002e2004140729120f60000c4150340c04101440107410b140803e071514104266171000d00303941e038500000d25100d1690703c05481075180c4503990740c40700d40c0740e003008400301c00d203040058819a40700c43d14840c051a400c1c040b0001081840440d001c03001042c1d400c03800c07440c0b1800f81c2c05069129000645007054020702103039140d460403c3d1000b0080b50102490b0b01c03481004d1541c06100f02c2500251040c80f850310014600e64000032000c0040100704152044140c0100703229499282142c1d81440320751000344e06554610542d22009a143e4050045034000741c8103035500400945400b05220703440c40f00d8505080204018050b0000d041c0d202205080010b001e00c02060200480100290800c52058000c60090300100014080780e28000b5841c0700300841551311600110841d102250710400e00840e1003000d50000a00c005080d82c140c00440c011019 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 42168835 1250 42167585 42167591
    0xf0501060509040b09042a08010608011b02061303050d0f020409020a1103040b1207050712020c040605030307020114030907080a080a120506030607080910150e070203030f0112020d02040c0c0303 85
    0x2221300b0011625011140202001000303201d20a06500400d8020540d01c40020810a00743d01e4450107030030755000390400322a030b030354903031500c91030a0002e440800365202c240064005801c0024841c5891a80300b84058184400028041c01d050540d1784906c061b41010781046480340c1d103c126035800b039448500000c00041d8130890a60480e0008030803902100c40c1e0a00e007625104100c0007194051800034a0721050200030701596000c40c20380301750401000d0b0705502a0444086103001c100440e02e20b82c00084c085c1e4020302500c0c0051340c000801c4505001080509038480d81d071319428510303000440d0031840003806000c280c1d0b02048040310282000c0341054031440c054a88001012003101e80844030709901da0701c80700101d01864040c001c001d4101c2810ba003600e10050b000240d035400c0d51580c41229031150b0494008100d900301ca940c0641c0c00c5101032000e14510f0410b52080030501006004203035000845041c1c1204556980d4110780d40c0903405030041c81801c0d2000c00141c07a55220030070517004607003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 42170085 1250 42168835 42168851
    0x180212030c06070309031b030324060e060304020411040e01080d03050403140304050c120d0e0904020108011e03020a090f05060d0b0a02130314010903180302010f0f030f050106050904 80
    0x4410785151800180092400e5610200f00310090440c0a1055040c80f42c0c112512614113a0020350f00c040c50f000752000f00b01c0950041c86000e031035001d84404140480d0104d000c0c030010b40e000390b0300035021108548140e103a46550000900401e44d4041c02c201800e4000b03000258208104d203154101c0b50f607074060316200020340320142d040d50130403131740240080c400001d00c003074140d5603101644d001402242103450201d500070100b200e40042c5c0d45658000d81c0250303005414a5880354809140c1030b015500403089051650010b0588001800b800009021044d61158249110a4408000c54008180100e0380e6640c00c401c0c0002c05006d0003204803903082500184241c24040201030405510145503c0d103540c88101010003500080000c0b0640901102e0010100d110750130ba032032000d00340800000c1c14252500c2d000d09880d282002e01c00d04107182d403504201503a000134000c0822034040c140b01c100b1030590320048001b807030340c9194030501600d05000031031f0096124015105241c0c00340c1e1304103c402 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 42171335 1250 42170085 42170119
    0x8040e0a090c0e0402090403031a0a080708100908030f04020102101103040308180d08061c0503040f0e190b010e0310050402030d030207050606150c2406150702040507050408011802 79
    0x70101300c0780a0740010040b4081400644030b03500807404081d2101c3da00f400312001100146945205600001e0250300000040c04a4081480501c54064801074100800d403500e0391020811f0000602e90708002540b900082c0940e40203000d41c014802c00c045003042a0310a84c0c811080707540054405500003000080000c4d4185050801440c0018005008201c00400b80700e0440342d034080205840d401c024079034103d6030a000100700d00302249200310040d40e126400d000c0103080307103d82913012144190103401400310705940c1c00c0c001c1c0c005030340c0504d0129952030b12600603a41c82402441c1d50790075200d80c610940c082049580298011842103058400d20642c92004400780c4c000d42c8000380207600f051021404520300342c01001c158050100309581401405404141001d0303488483c2d4042d840c84c01c4107441d64140982c02c19500a1040f90540f0341c4400034044138446026410307000b07000d80d43e00c00105214500175801c3c2c90003031004500901c08115080281d204c40004801c040f030061421015041c105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 42172585 1250 42171335 42171359
    0x303090b070819050402040e0a05010204150c15020306030327040507080709050108180703050d0906020706090b07020a0816090b030114070f17072105040209070c08040e0a090c 77
    0x35400303410303103440794444034640d01d0000c1c0130240049074055a559400101c40c0c41c1071016984960040c400140c445140c000c004081081440d5a1001c01c50610400e00004405a1981c10b006064000050b01c0740c0e10750380841d14622a00c854000e06da036020707258a00c0301b040840d500e80700c0701c6d0668062249403218501a101c0080a8580d40c0206006080500c0154841d44425500920050350348203c203680410f2103007020f00f560016203003500006051611150425a082c0050420b4401800b070329140101c0102a120203000d6007001c580009050f409656a8102030000350800d0015503003a0020070402c02003241c29489410b206c00c5c28956070030340c6c901c0c0620518210404c7d42c00703607000c2c4c2d035907400040780c004111164100a110407000980ca0394803100156610038540d44d1541c0d02070743d071040ca6142e0207114001c0a441e045082c4810000142c0700c0006282e004023081c217000c4403121903031070190840d02450f000303c07001117001c008100010a1030381041c00d4150060308607860302d030745502440c008 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 42173835 1250 42172585 42172591
    0xa0c02100903090b1309090f03020d0504080604060515030709050a0b0405060a0504050601050706061401080109150902030c0409050411011e05040605090f0904030e040c020f0c100302160303090b0708 87
    0x40f03071801004000141048005102c1c00183d040c00548a42e00e43c0314420448000304400e551509415a00303008058040040030145c0c0440d05000307050134a030040e15940d400c0700801c01042c098407003000c1005c0322031040503081c5001c00242500d00707070350302d8141a1000300030841780c00140702d04003840640c1702e00345403147e640140707070140c1414040b81c00c110521002d000003500c45810000c080041c280840d402d48151005402400682441040322400040441d41c06800000002e45030070410b4044c850101409401c9621940c00940c40c0e0355820051050b600895001402c094105010441000340c0b255401c2d40b0342000742c883c4100018400c8242e00020002101907020600400c4107100040c0140060040000c1c000d202d040c150300d845020070540c0d202582c044003c100000c0b90900c1c20318050040d40c01d0348a0904c02010000303503110201e0307501c00d003081603503020704040343c40c0c0881103101c1e40484403001015240c0201800c428a00103000382031941c0245c54901c02400030231001e038420400580 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 42175085 1250 42173835 42173837
    0x708070e060d05091204120204110a020a020f061b01020309010513030207060e1507060e010e06100b0309010212090304090e0c010906030e0a0209090c040b190b18090a0c02100903 78
    0x401c1010422142c401800d014140720100e10031610b41d40d0200c2461001440a081801c0410b10350355072a10502c000e40e1007009803124a0501030264014455001600a4109404a40c8054410110004181148100e0510340300d40d45e0766401b00070030504150011809807030750100802103540d400010018400e90048010b005800481041110030701c142e42c21000c8107001006820100403841007618030307074801c1d28120784843c0c0b00c09254408460a20580d140108460003501951615006a112101d00341c0102c080448010010501640003517040e110503081092003a6040c3c2403c0050940d203800501c1120449418005035408406c1c02064002d518034041e10740c2100343d4103220007034001d00000b85803501d051083e400d0320000b41e40c800f5003182c041d01108015020001c13012045c00306543c0031590080c004c04e5003490152002080c1030540c030032101070303000058640f558100010044450069150750091901003031101540103540301403000411a021510741c80061003204090700c28456000e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 42176335 1250 42175085 42175087
    0xa0308030f0901181202060f0402060d020d150305060603060c0a0e041a0a0f0611010203010521100c3b04020a0c05030f04030210051c020a0e0907080708070e06 70
    0x15092a60404001d40c000da90310001103443c4214222a4018011019095a1000441d00b09401580d0184001038004500f049910072624154001c240188a05405400540d81c0000c11000501c440d500c942c0b14411110f04031400141e9030309000c4d9031203500303540291181c0a840089801e40040d5000c50f6807041d420703200c8200030500001000010b1940581c62000f50030790340a0041c440d0756815020009d800c130182c401500300c1c100070b0014140c542d0010500700d56841000140580e642d001044202140a82c40001d40c088640709000c0c113102902c050042c60a0803c0b403403a144030b0300141581c015031000844012644040e0400b121003c1100e00b540c004010380042411941c02c081c1c004102d0b500941c1449001c090044d44c032145981c0c06039149404403c0d02040c03d0046107000013642c4140f4946190450034221213140c480011181842d0100995a000440d04040c5002e48408941110700418800b110301c4c100c40060414281155104009100c50380094100da01480c04103200000c060302c05 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 42177585 1250 42176335 42176341
    0x10804050712030c050d030c0201050603010b0d02090a0b03060c040305011103040f14030f0409051b070209240d0503070201031b020a0305031512070801050c0f0315040b061908060a030803 82
    0x10b007950914600b05404000c50031070071801007a410041007500b81e080b564001485254520000e0071114082c000314803d07414200180c4c1a5a508894004101e8040300d5050031502c81c07100b0350004080500d0181d40600500c01046500010040504200d9020b2030081c03000ca40980e880d0b00c00303448202c1d0000c050312400740d10000800d118001e0741145d040001704076494504046050182a0480c1c1d05c5004030315121000c1081054488806095901d40c44182070300300699680001c429240090046080c0483c510704202d2044c10079100403014140a802d0b0313030040406041654a0790300a41060b40031a090450810204008500403103070403c46501500c103c0320f203941d04071031603440900a0790307151842e07030302c581003a9580c102e80e490041d4500d4020042070385800140f03801c4d51402448544200004d0041a001203000b07030890764410041e4401d0494070b000078000400408040d0070154115001244050100e10740740c0200c4008072041d104c003682a0356000401400401d28003004018542c00e1000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 42178835 1250 42177585 42177599
    0x14010f05012f160f0302030c120c0910050604090b01080610020304050402070602040801060f150f02100e010207050d03020301171c0305090f0607090e010608060312031b0c0f06060108040507 83
    0x182e45045007140107840441c81540c00f105058000c40d00304902c1c0064000c000c0045107420404203a040c031080e14240e011022903072078580c50b000c28014071405500c200002683d5070400d142d006010300002840c4076210394407010382c200200030700c0c500c59011503400000305465142219401000d48515402546098102030600c4042e401c210011240540c0038003010550542c20300031240604400c14210312220315266051401e004642c0108041c4a030311003840c58056800b00700c5a2070004a000d0210751542d01da04224028450150098024000c040e003042d41c1a07895001581201d003c141070102c15408291016200c8800d030000c5a03800c1200307150340c450789010b40c000c558006800029070f00c4140300500014100303c03048451800103000420140100c0c180c0211b01c50240c0862301d8041d00314a01040030903906c03010640e030940d1100c00400040c030300f15449800854001d4800c205035464030405655196940c80d40c081c4490240620780004809500c19440c1d50320403908071000301140792610344 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 42180085 1250 42178835 42178907
    0x20109020904031b020a03052b0905010806130f1d0c030303010e0c091003020316031406040906060f0b0c060108011811010201060506030708040c060806030307060b0a0914010f0501 79
    0x15004d0000184880a43d000d6503413501201c005500903c0130344042d00c0813400340f911407409030940341e070403405e40e901c00e60140703a020107035070203884007801c2030310706078980d5000a0701ca100d0951050703201c1400c04602071030110b803070340001b0074400d02040c5100c1d00c0c00380001459202c20b442034129416500c00e0004004004c1080c0c50b8581000d40e900e00c0f01e14000021010035401d000b910100004240c000041c0254a01c000a50703003445821880c0030894221002c400d00413aa8001c0c010501c1140c41d07401c8481800340340e034424001444400304035600c4654440d08020071b9042200500401d01800c000000e00d148e040c050894010140b5240100c0700b00c8a680789005c074035000c40c10354115980c0e55404101d545a10000318007405032a115041d15182c00c0c9030002900c40b450b0410801c01480c4018048940c0740001583d10312a07108102003018284200442d2510070194881e030741940c201b09801c070a043d886c09506045e82c24049a11790b05907210b030015505411a00c0c0f80e058181000101580c51140c884 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 42181335 1250 42180085 42180107
    0x14090601111504060b090f010611060402100804031101051905010911040303050a030209031e19020907050d0b090103030c0b13030c0b06010e0d050c030705030115060e01090305060c0d0c02010902090403 88
    0x2010005d0200160b50220fa0904011104c0440d0340c001d65005002864018591403c0610100024201850550b01068012450351550350030720008002080405000d00c100001c0e24103404001c20040c517000440016008000b885203a0316480c002c000300d00b440340c0b409a003000d214036030061481c1c01d1850360b04980650155504408040e400c0c00820003075a401e20904c0700202e0945c50203008204080c0d40982002c00300010517191250310310740500180c50710f0660643c440994103041d600d900f410161400540580441286e00c000d0000003c07003015080400b6188150191001303400e999111000318500c4242403101a000c00e035203ca0302c1d070000d90413082e20b5074400418500074020070000c90110b400e030942054211000d4000603121452810f0802200008040c201c00030300040414104107a204083e0b8021001002100710b4080c500e41d0060382c00b84000c640c4002201d04518000c0e000309a5a0444914084017a003000010003005205018060440e6002081c0081c50780305c603501500c0c1e01e2480 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 42182585 1250 42181335 42181343
    0x100c050a02091b030f040311030a0801090e01020c06190606020f0a022b05010902040b01020102040609030f020a05120102030a06060c080a0807120c0503041704030512070203010207060614090601111504 88
    0x3c8080c20410264180140d03008425148940800c2d04207854090043c0c00080d06007200b9174001d1020800b840c1c1e1080d2224116250b1a4001502d40301d8083d01034003902c42c50b10415403902c200c00920084086058030604450340004081054076141d200898494203284c880b00043d520903814180549000002072080e403d048a08514210500038090202d050661003034807141d5580c03902d2401e5003014010f000c0d8200007440218500360a11001a05000d801e00001d00401a500d0704c2c1400c540700d0340c0344200074003401060f0807d15415038050358041d500880da54a81c240c204940055514065294040c01e6540310415509185030800308551040c0014503900070490000c441002540403440780003811050f541d00e050340c9140c581082a060078260703101604840d4104410800704502244041e203942070001450361300c010030700009019010300314000e007000d03140c20750003e40080c4c80380451305040019240308100759503450055400d000091076105c807541000c1714400c03102d40742c491243c0e4840d1103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 42183835 1250 42182585 42182611
    0x304060302030c091017090613200604030b1603020a0806090912221a0a0f020a02041401031a040503030604240306020a0809070602030702010c03030b030f010b100c050a0209 76
    0x10480020201c17070143c1502d0012031046c60210b502030486924195022041c07200810103805c007480c25241541030103102512055410702c804040380d003240300540390b0303502c014003051315584c032824128034109061b01d404400508200c9010103184c001d0007a250b8120158440c08816070b118802c1c0903540c40d00a1200802d4020700d551560404500009454a004040480c0c1030b030201c02e0462440c80030498000250300301048128000c042981400c590803184540303800045030414443c181e1403c009000000c1d8810f0410740900f107200007140d50340c1d048900403044480880401120b07201c02071003e0708d0150094008100283d041e0400f9081a041c42044850690112600444802c4090010340040700d03001d80004007070440550004281d504800d01502a14a0038500395000c2d5491042d55402414842d03083e0841044c10301aa000310141d40002d0700740c40903180300148190082039101440761080b0048502030945520856007407881940c05402040c24040c1030302000031071a0020725401d46515 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 42185085 1250 42183835 42183847
    0x2030a02030109230c030604081e0315130b01090e0711060c09030f0609030403032f15012702070204021b0c01080a090305090111030d0903080f090105090304060302030c 74
    0x1c1c00d00c10884481e008440001407800404030000e10821a01c011a0842c2d11014100340c6a0340d000c520140c02c0b650105155a803602d424815104944541c840c1c40c541590110400c100c07040c401502034901003088a4040d1141d0b00909400c040703401e0915283d002034110141805902d85440079103410120078100b0708030000081c54032500e800c2045526202014000c10f507200e09046c2002031298129000014100700c1c90b001101568070f001d1448044c1c01c01c511000c004451541c0c01506101c0141203d280c86e160882490b40701c0d40c1c90300e1050300201c4002c1103400024000781c852070b011f200c0c0b84030816041c040d13181500b00c0c100650040e0905903030140d400c00450380c440d200701c81c2d0b4204481c4a1000362030381000c0c00300058540000105120500c60500c184803000992040440d01d034030009007050300359801d081440526502508119101c1d60b0301e810b80120030b040d0440710591082c5429030100c506651000c19003401d0790300640e080400ca0b070091005000e564021b40203154444166545507007410 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 42186335 1250 42185085 42185089
    0x30c0302070b0a1d0d03080a020306010912050105070905040c0212070c0b070f1115070f0c090203100e01090902030c0d14010f1a0109030b13020a0305031902071e030f02030a02 77
    0x241c01040c80c00c0100e0b044c000c4007280c80400e12400d0110100884208502c2020b646000e011041c0041401c030140b40c0c00070000d4100c0e0b010780c400c42c0c003030401a101c0d010703480c42c14034065000789419030b01c2c01c022840e00000052030b441c0c84d005000f805c81c0c06501404680920b80056402500403000440325400400b03408240c0240341d4000d058110702900c0050b500b54807505044010718182c4900da4050340101303480302d0381091803800300e07900ca41d8014160f0f41c4407542800c0810180e121908005840c500000a0007006040310100d0070580e44540002141c0703903039074910b500032684c03c11802905500f10b0500980c0f00c1c540500301e0b80f8000d016051031070280d60001696030840d10995010000b02e685e130051212840981104d00415038001c0c00c0403117042d4150388030113414007002040c0c0d11110291900d0300c0c01710748598001600455200084a840302104603410001042006100c0018400c01000103001511442103800e6540140046032995040d61136161105942100a076003520820014400603 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 42187585 1250 42186335 42186337
    0xe1003110a030b1f050702090403020f060a0b040e03070c03170f13030b150d0605070c0b04060515030a031b02060c0d080109060b070201021005150a03050619020a0507030c0302070b 79
    0x100050b50000303074a20a45041188240801030300c0c0128412034964500f240f0f8126045664182c5c04aa007948103a95500c1c0403481d00c00c1d40c07400b081003401354800b441031502441c1c01c0f0700c0404108440c14058509650703549540d901030440d001c0c2035a100404200045100665855800b90b03c9000042c600368000f07201101c50361201011101c5100d80d114100b0504c03090100d1150404030300941d030a00014020001501018080350250078269034402142456010f070b10034130340703131030f4400d1841d0102c1c905070034914000c0004032076000150042c20700307407502480c1c04034040e6242d0707a2540360b5100808642c101d003c00f41c4000d580490b04030204222500e50801c080150f003d9403800c42e950588a036040800b91b90580b43c60342e10481f087c840c140310720001070f86c01165a4004040501d0002490b41d00e4241e00004908000002078025202c0703a40030050180100315140f040d80d190845413a207100b1a021203049100d61101000098024030504000921820344104000d0191040710880c030703100c0c2d01c58225 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 42188835 1250 42187585 42187597
    0x180406151d01030309050609130c230c0d05090d030c020a030b01030b0601020708030901050406050702040b0409030507050d020628060b0a03060501020c030309010f110f0d03020c16060e100311 84
    0xc503203401c40100201580140c0e4907016003401c0c0c07a00d0341400f280c40041011062280002500c01d5143c050724004140f00c0d8045681181240044100400065100c008181d02500c80005580280031100f10f4280c010300481e01260300141c44501e1384d03065902d0440390700e1408038081764007810940d400004501d400e50b066000e14040c180d038012508000001a25090a55111400c240c00900402c00c5136a08041510200c40040c1001a0366508610016005000350b408580c0d01030301d040d181805055100d000350640030310580490b0410710002e1801e80e610101112404400c03e12440020103021074058a1030b0901204003020800176282d03980d0408075080300411a00082d80c8190800c09076904000c4107200e540c007640590314090352840000c18401001c1808014480013040542c040305081100d68501618001915040d6102d418000c01035805480d240403d482142d201c105000400c208803030450740d440e228001c884c15010b003030042045e8086010014186e984035096440707040e1200900ea = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 42190085 1250 42188835 42188879
    0xc0f0d030204051002060c0415030e01020705032104080d02073906170105150f040305030a080f060f01110c0901031a0108060705031f08032718040615 66
    0x41c0b5035090405101aa80d1324407202000c56100c0014042e0781c020440484065503088000c41c4250211035200758060007500800b1681e0351b2000a44100740007012002d4100881318010100f01028a0340210143c0300080e075001e80014010071118495600310340c01860524803039000e20280001d075070710f1a600042c462303103100703844d40d401d4030407028103e02d1a040402500981c03c04008948542c0c0c02d060307411405001c2c850190340c02891180340c0c14554001c0d00d2040f400d56184941da00c3c0c9a20380b454981d0442096203011500b03a4000c12009404101442c1c842d41d0060700c08006601c0b0000111031302c1c0071650880c080c0380036865070b04d18543c070380344011800b0798040c224110f142190b0008514103514164095200b6030405014803094590050469410480360121000030744445964410b68081503440003a151000040d510078480da5150a020102400d40400302c20315000c6040c48000454828010b0203c03d59200050001d8010b07800542c078030300c4c0006c54404464441d034150885181c42d80d1165 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 42191335 1250 42190085 42190087
    0x260901090c090911090c090a140109050a060215060604120311060901060627091a0f01020705060a0809030d0603051b0409080405040e0f07062606010903080c0f0d0302 73
    0x10600001c02040c400500560740704201c1d4000fa915081c00842158146038441c003618408180c0703c40344641038482d0304200800a04c009a50740290141001c03140c14603034085103280e0300c005180e250481c490011519190003034440801002c04080101d58004c00300d5900c020213010205000074a901c140e03103064030a481c0c40480d000d0807080300c0c0c0f610000910544840e818200e0a01c00203030b220040500e80910082c1803002420010045441602c2d246c020343c2da0a03251a58941600c150070082d0002118140c640d2070300941ca9034012611806a400307031541000c2c04008940390140f10f0300b803050703008642e1000e40382488082090441070724059801611168080b58106107410841d8104031200b400440d010000e640f07e580d1000103074000c038440c0d544035582c0d803840100c24010a1102d0900c2d50501000c3d90b60698031264050254480d80700d20708415980f00003002d032070742c000a101600a01d4141c4032400ca86155640e606150352042040c41c446000d402003429020104002e241c80c8801ea545002d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 42192585 1250 42191335 42191351
    0x90c09010c080f0a020709020403020307050915030307060c18080304060e03010e0105041208010b040f2c090d140c030d2301180f05061807020c0604030f0605060604030c0501260901 79
    0x3d02c2e11b1520f4100c1c0b2074480c410441000140e80009092040303072800e96070b1448603510031551400c0031200320f483c103030140000200e190801c000b40e4000e22408010b40c50b2000325403801101007003000e41d24010540713582d05c104410b11465028903040d42e00e2078401000840c0204004c450b1509440e4180e07002c803170780244d52071010342968000e5500ca014107100d40381c03d4103252810256030454049449003004181001812039004003503610120340c02d0b81c40d001c1c18041400e1101c401e41c0d44804071503501d00041c0403034140784000c0b00408101c4e25140102002542031141034078401c4000e004400c0045040300305500940400242500c4040c004d000c98510840603030903641144080e01c07202c035803d1511624040c1040a45da0723030340203202000c01c000140242c0c0703640e41341c0040e4a012140007206511610200f800410001030043e00e9640500c201d80a00c010f4441400b4040907009500000b0201944082c091200c2e52040c944e401c1281079040701d1070964400140b20180c1c0002c02c0d00d402c132035030351901d003c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 42193835 1250 42192585 42192587
    0x17010605030106050111070b030a020f1317010c0804020609030f15060102010b090613050a11040311030706030905030a030c0203161202011505010507170909101a0702090c09010c080f0a 81
    0x9543c000302403e08058200000801c0c0c800e84600c1580111040c0a0010000c9910101c0640c1a00ca01003060081d203540d525298902c070074400060300c2184c41115260391091100b00c018000e43c004a81c290b00c9151080d140c3c6d07800c10001d46c1001d01e00c86d030507218280001039186400c201d101106140c8505082072030604c1c400081c00d441100300c280b40528a40704c18001e142d00c0700c2c041d0601c49000008c002459440c2c000742e0b031020f4081c015100f01004030104000c024800448180c40202d40100d0440c0c541980e11b020940990b95050303009001504244000050103000c2c0d0014440900300d803040d00e151a82d5080b0700c1d00e908074201c400380e840c2ca40d08001508815024403440300030340500c11844419502e4100003c0042c851a00c0051000a61010690641c8584000da4130b0340d980c000c02144503440c04074006200d03848284585181d244100c1031507166004180110b4441c5a00903204248a42d07403100038096603400610f80f181007001001401c00400c8104020709514111003000316680d00000038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 42195085 1250 42193835 42193841
    0x7080103110d1e051f0209010318080301050d03020109020301181a15010509030703060f050405120322020f0909010219020c060405090910020f0a170601020a0318170106050301 77
    0x3920314040d1064022a40c08a0742c010008079180f80d0482000740f081542d0301d41a4103058070034202c1c0c084007032420500c4400c1d004c150060b1000242c01c1e6001c1081c0000010000015100c0311406051410104014411800c0c0320704048a04d034024000030960903040d070302290031a01a00d00503544042e00c001c142c0d0410200d12450040c82d080c1b1f60b0420b200d8140129500601c041d662202814800f00250150198906210400003150070020401801c066121510301414040317508482c00d026401c1542ca00344001d80c242c2e0f002c0c9030102c16074420400c200e0070848951780b1604060381d10803020030103034260341e4480001903c1508094009038a0303440e102e81079001c10b000a694401950050000070686496410641b801c03100304903100700160712040c80c69807c1040e44180c43d01c0c1c042c0005011440c103003004000f0075003500b0340d030303201030a0014006101c0b1140c20151340d0310380181c2126641a000c01e20850310342c1d8000a81a5042814950b581c00510305087c0303800c40c10385075035111a410040ba1400384 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 42196335 1250 42195085 42195113
    0x608070201020a020601060e120f060702070806040305090904020a05040c1d030f06060d060e0a030908060105060307080f0a022209050105100801090e0a0f08190e030d030b150307080103 81
    0x40020b509055030311078069240c1405001e400100074201e66211401d5035941c9da0324000c030040d4003d03115840a01c40300541c0b01d4000300d6507a00584140000001c09010004400e84610b42540d00c10f42000202000c200f440c2d403014200341c0e80f1104405011815a03518441c3c009503401d02c0d2159045600c1c403603900c42071101021842031003500720000d080302d001e20105a05a000307074111144c0351500b010b40b5214000340402095110984a03a507102c20415070003004900680d494002100e00903070765041000028441116584001140503021a016061909140d500640c140f0800750500b1107036007201d808140c02081400c00400c3e80b060400002141e4411306014100696110a50303440c0c10b400031701141010310400650300e81da00e40340d45803214188140c05101c1ea1203a0710000160940c11300301e0803600910142903440ea000041c0a04030340c01101038015155028000d8469000450f2068004141e0203002e0b039049081d0203488071120403104000c6218202c0b5444214003541141800d000c102204 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 42197585 1250 42196335 42196337
    0x150f0711040e07050925020709150f030204022805120109020304081b160303080711011e02070201030b150703020d02010c09051c050610061803020d0204020a05070807050601060807 79
    0x1a96030b10440302042550540340d068903040030a0300e84964403660004858015400343c2a50280f4201c99640403641c801120b040d05424044017007004040110040148691803020707001c49410401801c050b00a40344104500e40e44083c0c4051260903001d40459601003100003c2001560b070001d00d1114800f240035110105085045103807694032202030b4410000c281d0039008a4500e0503001c00000c10a607500110b44041e0300000960700e2801400740d990544030725000c1410480c0e443c207580350511030208140c10b568240c4042d64409200c80e8000d5004000981c1090340703840031000b143c1c80c0c107c20071104c0030509100d81d0382e41c54141002414854941020011a4148201c910aa640c000401e60a940302100c241646980840d00c8200c0105030312002000b40c0980ca08102020340392101c4101100c1460b207c0e0300742c02140303c0c0f0b1030034001c0a03804000d50040d003000c0c0d4200542001da000e40300e010300600f0080d1070039075540c8450f0010740003010101d5040e4805070041c841641c0c000c212542100382 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 42198835 1250 42197585 42197591
    0x40b34090b030108030a050702060408010c0203030f090a1a150d050c010314070c0b0c09030d0305040302010c090e15010504170c03010f05010803030601031e0c030b0307060c03050f0306150f071104 86
    0x1007084c1d4a0300ca02c50f402ca02c904103c4082401c900750340d156000c680041000200810441c62071110194807030300211400b00700c0013507a07400211031307103004155102926406000b50007018944000a000305101809803980c2801c2c403200603650341c4a440c03d00b06154000d5006280d154410000102940e102c1c1002000c031440480c103104c984c0d41c000c04c4089949a100c0d00380d038035036911804076404d540100c000450b418410003461212042d0581d0207180600d000754000e100415020f07000341d5801c8010300c143e0665401010002706c1c3c1c00108003001c1d48035401450010b00d01507403002104560304004020075030a420004404c0f07000c0c43c01b4854103500e10ba464606012079894185840d40743d00000700b40506040d220300130322741d14180c00b02c07540307000300310245080000001c40d46d4010010596107845a009100e01030f40800c03000e0160751040034150f45079549618000c1008400d240d0750f0030140c4004d07080707543c01c0140003c404505000d8007031a048903000e50340380c82550802415104810103114000c0d45 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 42200085 1250 42198835 42198839
    0x405060106050a051b0c06121006020c0d060f1401061107080601140d020409060f0603142811130b0310060506041401050405120105040203060a050906040b34090b0301 73
    0x2400500f9150725100030895070ba14001e06480d0b040c1006d405c1420b00d03a00081c0001c2c2490304411001d8014010f8003030401c1aa006920f8407000d0340d4400314003d800780d0003039a0301c3c0e2040c0011341d40d8100a40d030340468074000c01c00854003080e5036040d2900703030010b001040010300700b82c00309201040008000c018860040041d9450311410140040011010500404035014034506549668001c4800240d200030104410550000700b100100080e001c00c4500c00742550b00c40c04241c0c000151100b488022580f403070304e640341100f10382964030074a0300d003100d20404078851a501d65135030303692009566085242c08640800300404250410480c072410001031490703c074051145803560001d541c2580c034a5282914081100001070f21140212f5010580c80503106080c50401401900204d01480c07090f0210b80158590301080e2060b81c7d42100d054031143d201c000083d000c60100809a500400d07948901d03100180c41da81c2055900301030b0440d007020345581140b03804540341c1c800d801e0310080c00c07421002400c0d54 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 42201335 1250 42200085 42200087
    0x11a07080406111006031203020a020115031b06020606150901090803030a020409060e07020a11060c070311091e1302040b04050f060909070e0c070303061805010f0b040305031207110111030405060106050a 89
    0x405000b951f0201940072039003050040c000d511403001c029150f03500d083c08580d01c0c54100414414281c2281528a010320f00255003400064460302401009000000700240d400c5002400c0e0040380d80303c1c1c1002000e02002920040c01c1c0001d5004540d54000542d540303040036140310a45660b07510420301280d510b030802418030b0b40821420780c641c1d401032016044000400004030640103030b5113800aa402142d80002c1001103204441c5840c0000f40c07410324040d40ca40e1504515448100700c0002c40260040004e0001103c10292000c043d10040000608021540c040340483d10116031609900c05510180004c2c4d285c0030384080d501c0285100240b0b105410455116054000504154008a0049108010140a42c01c0b40c80a852844c0e61441500c00c441004005084284221303000701071500b42c08249010500c0444083c0c0c0c0e04200118544180420301c00c0c03804600508880421200709c2410340550350a010f40141500d002007041c2d101c0c00d15041240c200081a4814400c0c400304010195140f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 42202585 1250 42201335 42201353
    0xc09060e0606070b060a081906050703020301050109060305040512040305010203070305010806060f01113d1103040206090f12010605040b19031202070801050711010b040c0503011a0708040611100603 87
    0xf60380c00b419003d103a441d12800320b84a9961358111107280d020320f007520071901041e05e04005030203016800600a50312010003d5040344400c0c0200c0340003a980343c0041c0300f640d0194000703680240c822002c030760300048408001a026001600110f403103075000030030b00000795810300035a405041c045015080506084c00040c4008240001060500940c142e9001840d03009100c0300010003001031040751000c1c48a608541007902403a01111130305902900000c2070407442c4a4100082104683d151854a842d02081059004420761550001000086155035101c0d1880010030450040c00443c000d07050204210540d003608003400c0c090202205d981d0000000c841d08402100e40090380700c0003151040200f00e00b01801c5400071001c941c01c14007407081a80d0b0080e0b508028451880013002241028810002921024000c1c1000908203100610141d89100403181e002115181c04500d03042d030300c0e07a40b49101e420a5000c800414007002520103001c100b4041e00909407505d40c01007080074119900c100f09 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 42203835 1250 42202585 42202597
    0x3030e1f050301120c030203010203040305070506010b040501020d0e190306021801080606040902070305070b1303090501080f010e0604140a020a09080f0307060c0302070605130212030c0307150204030c030c09060e0606 95
    0x41040c640113528188412040c0480140d500680250343c4d9280c079040240c12a403203450202d5061281000000c0d0380c2c40b01d01c0a5034165075050707011f80703481c080d64013040b52081c0071000c44680c400d982e80c0040d442d00f000d20008000075031143c0d40243c1c0f03400000d1850211507280c0f805003030502008804000f00c1d50f031040121015103910791001071b110b0095040442d028001c04500800040f411810302040583e004503c82046100c0d030341e5103107040c1d02e44004540c5410709031a031000000001c0c0043c420900000c040030350161000d000010500c070120481807080d40f0030340e40c14024507030000300344491580c0a00500f0180854000615042c3d502d01001e07552031140300c2d4080c01d01a5180380c0451418484d404649040740c0040c0705009904200c102c91b80600c00c4610200d204121307034600e5440921020041e151000d400b4000b440c10a9140c5e00c0d011540341c02103201c00c8405a0810000c000101c103500c8141c061405160284030781e03820328282c41c2c1211810741048505d54090340c10000b441c0c1d030b145c0441d24 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 42205085 1250 42203835 42203849
    0x3010603020d0803041b080304051507030c23010603080310241b0614090d0801050a0501080903040b030108300f090307030b01150206060f0d021014030103030e1f050301 74
    0x303a039585e81d0074010f1a0340403546c034650b0710000c3c109001400300c000102410607100120360108400f2500641104117120708000100401e00c90644540412164401140620901c4140070081c110b450202030841e1030795001281c1104d40441840500c1d24041c001101904805450245501300c1120009110f080e602c50070f400c000292001509007140700f040f50800503440349003030003000d99510080d00030314021075018406102c1d0a6489440750b00c10200c503812107030090880d081040c10180119800039000341101d001e40710421001507001d000c40c008600030010000a403180e0b03480b9000c50be18104003001d02c42c003564a1004001090348049007221071501010441942d00c02d44c0d000844d06002d140d90000c3c0001407110000100b407800780c0078101c1c01500036401c3d81c8141e070b903507810048280c02e20745102e500604040c000000509000725041c06041c40c07400c2003c40705001505500f4aa4030981048001403030440c01000581001807600b160b040340400d40f801e4080460800034070303034013051040350 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 42206335 1250 42205085 42205087
    0x604080309010204080304060801141f050a020a0b070305040201090602070f0e07021f150b070f020d050a12020309130b01210902131406100e0402091f09030501050603010603020d08 79
    0x485081c1d09504880051803400241c03500c4540d2290003a20b843d2091040040704181d03c1052003542c0380a400201400781d4490700c101d08400c1005049510390040e00d901d800f548035181e0040041a40109214800e403100d0340e020945141a100040c64450341d503021009541c45220309101d0600e900c5140020b8601001011300155111b00d000c03440c00c3c03000c2140101a046036040341054000d540c2100c48140009c0445006103035440300a641184640034000c0c00c60483d0520f0100145064400c07154003501480403505007500c0c58480d603640080c021001c0c000f40e0300008802400d400d0a000442c5030000340c8000708000c000b10780020b001d4810f01200e081d80560841210018081035074406020705401a000a002c448605208002802003000b81003558103004005069490140b0526000d4402580c44542c14004e00e014030010390400c3d695a036124004806010021001501c3d40380c01c512503594112825185007400c5003181e03405060385c0c1c000d9042c002c00b070007da240c140100009583c031100b45 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 42207585 1250 42206335 42206341
    0x9020105070f03080106230409020313021206060f060c0a020f01120e0604110409032c1005030709060305010b27040203100e0106030b0f040509100e100b090105010206040803 76
    0x100d4803482403120040800c607400300e08000f0715600c00805416038405448003c0714548010b24030100d030015400a50181c40c0c00c0105000b0f00321035801540e004002043d64562507070807176000542d19070015204490702c1c0d204504005851801c0400034144e00d100703455491401300c08050a41d101d80d0b032018040e00540465185a5503a442148080b40b404418801040f01240b4031720410b44a09050741d06441c05000070007090550325042c41030340003035541038031a035600040503070000312f40518111008100d01c807008d11340344454580c0c240280036441507a83e1345030b507440c000c080502440c180707810050415180100600000c20b0a604031030a1801900b14142d5070b40c0c480d600040002c006440d13454000e40040240145100c1300020360303040c2e90101180000307507a00c4803001c800321040f030082c1030f902101c0507050b01514105940440c0c0c20000c80e1058810b1480851444d20950380750780000102e603404031a030410448954032514080d0181222590155494880000d66070000540007401800000000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 42208835 1250 42207585 42207587
    0x30c020111010501060201060815070e011202040f0b03010608090a0201050307030f02071b0609091b05090102010209040501030b09010c03140a020a0216060305010f1202030706050c070902030c0c070509090c04090201 94
    0x1141c64014103903009200c070b9038680034005d01a280b18400c2600500c00d001a41c0c503000103038400e0a1042d0303201d58680880ca8900401113620f14000c61f0880c0141d5405c1001080c151822510000541402440c207650780d4588580100f0341900140b40201a42055881c580140e9120b41142d40181980c9000b240704840180840001e2041c00b10084c012400ca6082c2840c41c0d80c1001070390203c50310b503140c0190b5107940d0880c03042556100902c3c4242c012a4107941001107000300050a4030560620005080c68000400b28040f5030b002e070001d84144441000700025a20b09028104140344189001d006003074100310800444a80581002286600030a58402452081120101c484c4500ba034803071006a54a41c0640248003e0140362400307480c4080101d440400082d1420010f94040c1c018a4038614121003103401c2e80240c1c0c0d030a41c1a00a82c48006413109103030024600074554484c4841c1c0c0d4800c2d01c1601490441c499208034000c401880800103580008960000000020744002ca540c0d01a480 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 42210085 1250 42208835 42208847
    0x5120d2106030f02030f030325110609010b030d0507020904020603060316060810090902210c041a0901060c02010801032603070804020a0b1303080f070606080a05060a020313030c0201 80
    0x1801110480c5007900001c144400441c003290224001d40983d0072089113044002d0f1240300494919422500d07603001c1001011442000303010030034103071030a014070500440905003444001da0310301c5802c0c0c1d112101d02c006480d05222105440c080750403c1072070104103030f022680c405c500030801f0f44120800304c0003034600e803810300800c1600248000d600e40d01548409000c3d00042d0142e4025240005a580114120034035200d00411075800619028000c50031100300a5400c080710650240c80c001c07a00c1c50302c500c5e01d841c040c030100b606405851403c620350340f2050040c240d20507804402040050719000d40982d07042041281529000145024210314034050b649040703401491801a030b50740081003250441d4403401a60050b40300320741c54100c181d40c3c0e42010040380201c5290460f003401c443e20030400a4107090040003008440116941054040d8a0b400100e480d25404207003160040805030741001001c0c0009a80429601011415401c3c87d00c06400310540702e4500800b403061001012082d0fa000b50 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 42211335 1250 42210085 42210137
    0x6030506010602031201141804030e09090a03021c0516030203071b05040e0a0302030313050109020315180604150b03012d0b01020a020315061804080406080105120d 72
    0x14044800c2965510300095403603021000607181d02d01100008680796101c220060040d480013000d070307955580c0c0c490b0b68103107000000c1e01c1203040c0624104428601e448410328203200f88002d201034028000d05040103030400045031002e260501820142042c2c81d0b40140c140c85045840243d26800484a40b8041e4a507105040c806030400240300743d541c00f0009205602c5058440589044c010f521441001541d980c0f500c05000300940c2003440091481c1916044807226180110b0011035034180310f4010900340009040740b00c46c400040010083c1c00304002c4120700c641071155000700250b24090b210790345e400d014542031148041d26200b540045a03400d400040d00d80307030140400044c1c200c0c0414a00c5104682401e0440118100a8003102c0342d07002140c02c400d904d07005409000d040c2d1444c0803220440034000d284551004d6000640c10745220094107083c440c520800d170581d9aa400c021010b07010f110140e004920420320341500041360603000c5021340c12441c007030518818072040b000c42041808580 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 42212585 1250 42211335 42211343
    0x7090f05061e06040b1204060f020c0709050907180207110307060f18090e0f21040308032a03040c150c060b13020f1305060301030507030f0303110301032a0f17010603 73
    0xc2504c8601e1308000321207c0c011803003030701d007040040791500f0b88034241d0081101c514001d0f00141401c100e00055030b000b60b584440d41d03200303171601c041c0c030b8540f00707000f80a104d5603402041c4c2c0d0100c0c04004014028403c2c1e108507804900400c4464980b40000b84034000050100c0e04200886a003a007201c03030041030102c01351045030300a000e000e0203800e9142c1c1d503213a00049442c09114419400d501d100143c80c1204445546070310003417420342952601d110542c400380200e81c1c0c158001124100003041c0b20482d410b1350f00b04582980d40c2c0c0c03c0c07074280007044208036003100b4203110b4051114059140c0010011401035031100b00400c401170a400051130400c50003040729502400014581e20500241d401804040e030011040105140c84406218160009000042041d8010b60050001c10110703100000f01c0b500c6807030085029100040e80801c250030a07801204c000d0304100d60b0950901d524540304801c030300c403480a0b00459251100241c8145840d00c00c00040009100307101c00012801e4220001840d00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 42213835 1250 42212585 42212587
    0x4110a030b1501090902130302040207141e07081203040b060102070f15020f0d1403130f080301050102010c020c0a0618080706050c061f03030e060d0e07090f05061e06040b 75
    0x3821618481a030b50750000e000a03c2d400001c590000c07035200f510560031109299a006900350ba0920000b54040c0c84261814030f0403008202c0c0c2c202007040300d03440c18034201060040106c0b05454043ca400e21070703081440705401c180000c01d80b0503041d1050340da0058106a8440403030b2200750042c0d003080903603040180442034011010032185001400a820341c80954219044a08030083d803e44444030b400d98500008d045504c5d0b0f2259a45980203950001c0b02200e800240c3e5402c0d58518100300150041104c4140c2e0120041009607020b03c1030305054070580c00500941010000001c3c004134113802103070140001c076080c40c1d11556002d49000050159101242e000c3c94607550701400720b4100166480d16889071000146d40000b000c140c0c2d10f05403111600d02255642180e80c25a58070300060314240e0400411f010000b40f4a049003e46010031403800b001c0c11605040c5402c0d2016240c01088a41e0110300b0b020074410143c483c90f45403400e280184c0f401981008080000074410321031076010b0601c40070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 42215085 1250 42213835 42213841
    0x50a02070b0a0c0f020a08090d230a02010e0306130209070309080f0316050406050f0d090602070311010507050c0606090711030403050d0e010c050d030902150d0501090b0a0e04110a030b 81
    0x2d840c1d4803800c40304900340c580100c281e21201c02240d440e100342000130007120f402e008000c128106500d21024403485a4100408038800104070101800300304080501603020841032019540c2000c80c417041e1841c250702070419031400100441808103c504001e00828106000803001c511961162811551203c01e840e56450411440c1c4815001a04d00c02d07200030a2030580310055006104030b03403c890650b1035950801c0650f50340100c1039009840e22200c1c0741d0712100d0303c01c001003907840100b00c0d883c07198864410000a03215100c2c03c4030741c001d0542091103020080010390000016109900c580c0c1200d54500c41c2d51070741d4040350301480103140ca403600c1c88045004020000089421241420190f490070110110f10f001103a0750755500d640030300f0580020b408103070518800d40010180c64000b43c4031650714801030001050300c0d480012150078680e5250010302150260340165080800110380501d400c50130400a10003114000d00020800403d1903c214056100d641c0c030310004640210031041545 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 42216335 1250 42215085 42215101
    0xe1002010213090f060b1e0c07031401091a1003080906040f030506040b0702010c080403030510050909070608060609061219090803060f03010504051c0306080607030b10090e04020103050a02070b 85
    0x2180135071101c800d2504201006c20708140d00025100001c40003003041d030744800e02c160b82150607880380000002c0790041a0003c4003203a0800c95410081102c60300014251a8508108082c9040300c82100d01003801c00c001c0c0121000e0301480042520b80100ca610394400320180020a1845242d000340911100d1003400010b0180c0030940c00d120b9401610900e41070b50f50500200e080300d840740f034204003107110b41c40490301080c032a510041d840403071100044840c42d180e000040540300f08070381000f070940c40403405004003a88805010740085090b1043740c14151984000340c81c82c040d80400c8040f10120700001400035500c90000d214105a00004100c80c08503804c20441d1613204031100d40c000c903074101c02104079060512604e4030840d004030140c898038091070301090200c024010744404240c0c980b0f40124082d8414464640110503984001540402110a109016003405031704420300a12250400c0800d14103941d4030740c0b2503424a400580c5541d950050b100900075000060240e204c0305003084100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 42217585 1250 42216335 42216341
    0x903040312030b06070b04140f030d0605180403140403060f0c26010b030619080c090112030504090207030302040902030f01140f0a051504051804061109010e100201021309 75
    0xd2806915504514581004140d0075607000e9007420380c202c0002c00440011400d000300140c0c12a00c181c0400850038030314010285040081a10200c3c0c82c0c100103203030b003070841c242c2c03040c0340003018241c50352050f03071320a18100f1220101c02440034040c0003c0307121094440703d40c4402c46014590140041115405144d09140180000303140c0801240803100d540e40e140710012140a0300e59402004001d01c1e030b0078640d036503001e90000780c00c607600f04545043e0359850715486181d05020340104801021500040400c1240c5100c06a02c01030030303172154400440c00720750310100b154240c0e240a080585e840c801d600d022002481140c3c8684000c0c0d10210901c020459944190303070403074a40071012081c84411004120718444800d02c2507600c2060241c04110074104401a00c8140002441c220700340740d0b80398049003148010140b00000c4041040c100010004688240c0040882c0e503102030303007007401c6140080d00c0f400280d034400e4420301c030034460040c88034400d404803004541072a1880116940e20800d08000e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 42218835 1250 42217585 42217589
    0x90303090b1008150408090d03030609020d0506030d050702030d0f18090c02010c02010b030304090f0906020703090317040521012d06090c050306010c0c03020301050f0412030c05030612010e0105090304 88
    0x580541013441030312140003c03c4034002e6811020152a2144040421100010000c001c40c14541c54040004a14040e80b002d00301c0740c46128400300e80e91400e90101030411581500c44403c4c840c0c1405030710056100003412003500515801c090001101003c41505c8102c048038280078006004000400c07040c0b031720340200b014054290001e001b500d0a80d44280c0c262040c440b0f9403074051380148410852050b444d00020640a5041c8000803900170b1500c405090368040c01040d4040344000d4810010032071400151010b84661420705410681800001800d540d2081411042c100154110401400302903201080007015020320302082c4510907240e15040c49803079401c81281b07240010019104c242030041103034550840d43d850349181d0310300005507420302140009940c9410154008001038509204242c0541080b52034916207141910300303880b2030000c9080e000d04042c14041074402142e009000c0d030ba08068100c3c0d50103519100c0b09034260040800e428210255800c02c4107201108070040300400c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 42220085 1250 42218835 42218849
    0x41a09040c0c0203010533060910020303010303180506030708040602130f080f03040e010e18010e03090405090109050a020139050f15070e04140f011502070b0d090303090b10 76
    0x903541e07c0c14100346407070342c1008658481107040300c01c6499130000720300c0c0340c3c50050050010382010a0280401c1c0c008035900302c1000503910010052080c9600800c03d1300541d00c1454507075100d14240320100e420f900010344540140001500801e04001c0703d074040e92030525940c0c0b03005c00525230714902c41d1580c1c1d00b10312518002e0301509450746002c00303000c0201c0b02954400c452822159280c46152109101c2c000c000d83d130300351007001d03072001007800030701803c4604034000b001551500c86d2101008111795000c0c12401403a0b140c05d103803200003400820720300b030842c0d024204000406401e0230a4240c500c151b803003000303400d90104c4900e4003200c40e04000703800719405082192004c845042d0110f5880403081074801c90340c40480300003100f00c2d01c50000c0515025020340040f50040ca5003032681c10310001601c401c1140310f20300006000080c3304100c194a4951544000c102d500d1030710740b4280340d034400c4c0b1150b042841d072a2141e0409241c069000703100c00d643d0203a2040304502d04421640300e00344c22402a07823 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 42221335 1250 42220085 42220091
    0x9111e0f0f0c0c0a090b0904020d020a05030319020c011b03030c2003030103050f2109150a0c1101030b0d0303090f0206030115020f06042307090609060509010801020a05041a09040c0c020301 83
    0x1c03417001c403180b291001c400c901400c010b026445d039030208039440d121150100c2e0300400701440840d4689050003d0304603410b45c0000144281c0b40c0329006030a00c10041c400604201c0359041299643c4000c100c02c81506426081c0010f85c02990402111103041d22074000e1704001c400c59511442200000046040701d006100742c0c0d003108400445691540e0540c1580021200c0c086503848000b42890000e05070004000c00c01c4074180450104040355801005114021070304039500c40c2c09000c20180f601002e408246010414000081c0000e91420400e080160400d1303510709841c41000621500105040e400400032a160b43c0e44107640380d018000c821801d40140500103280640b10750010b41d55004640c4440d208458080e443d245840801c00c01e03102d61258031a004001681c01c0300c511400d8050a4500070100b251800e00042c00243d81060f848200c85a01c104101c850031607200c800e50713065a8144c080c0b03c0440c0c2000c08a0075072405a901c2031603102d440e01da1450000d03508400e035861000d10a070300034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 42222585 1250 42221335 42221339
    0x304120c0f050a03170712080609130b0106030c030e070306290a0608090c040911010f050906030105220f050105040b010305040b07031805060c0409111e0f0f0c0c0a 72
    0x80c24481d1491180c603800480700801070000a0556000315a0074012071403003414034085494410000b041924000c0108050006002c42400c000402c1580200c0f07490b51084216601e0340d548010301c00c14030645040560381d0b010f5082d0240b207604000300c0c2641200485810304c2e00d0341445401800c485000f1450b000c480103031a4842142403915115a00008100e0010382c1d26000c0280e0350704500519151850040c62040500c59841c0d10800e01d100c1e01131b0006014010401c00054000080503680d030050050034000c1c0703d0a6038844084905517407068803142000080308103111000c110417108451858244000040800140d501040c12140c0c01ca40a000d0000d00c0b07001074080311026200035081c00750000024400a00a8000fa03581007030000d030051001e4141d40f00c45003004001c0d5000790424500040800242d0014081c1a428810082c441441c0ae00c10850540781c48240612003038054101003920681d50396104150b138103d0b440d4990442c0d44e03051007594282c0311541e00807180d106a200340c40c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 42223835 1250 42222585 42222599
    0x102190f03030b04020c0a0c030302010b0109050d0f050a052a060a080402041d07030305030f0108060c0301060c081201080d08070e010c0609050c0402070b090f1606080601020f0304120c 81
    0x1595040505282000d11648046016042ca407200540083d002c10403020058010031190307a1460141040c04138450035450b000382500c01490382039040216032101849255a4400400c86080c0d00404000c0851641d20780182020f0411202a20a01406601940116031101c11020140100c001e42c17800e5001402004064050f0b06941c90001703969100080050405a00900240011a4190030181a11342045207400d21941003240003e0010050041005a04130424051700204001d480e00e4a00490f143d441404148501020850007800075024014040202c80340d40d98a880703508038542c3c50304800c81c0e50341c2d030000410700000c40c0c100026095900c40e204a8940000581d9028514180d80d100e100181070210000d035010701480a100700141e40c0c9100400145105900c81011442c018200038101401007400c440140c11480145855040c0d080280003502c0041c00c02e0700580d201c0d100104c0c5412907490404900d0305c000580130038891008011040700324811a00e0b01012525200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 42225085 1250 42223835 42223873
    0xd2a0f050d0305041a070207051c03090909020102031e0c01050f040b0a0c0203030a0902040b06070f0b070801030f0209041e080409060506040b0a0c081c051005010503041208060105040b0f090102 85
    0x40245c4508030740070f40000300c084140e035460342001d001c1c41200d840c180c946000402094180103e200078002d030300d44000030942c10490800090040d44820805500c0341e80000c0d4580c41450003050100320070014640e0091141816122a5115036001f00420b1500e0380540c185502e050301d055600303c004c0b40000703864003010300030001d111405901650035511005012009408c81c0c890032a070107510350111241c03e840300c00c0030303140e01c9014003c2c2081700c4c80a0b0a08070020400580000200705000b00140046228042c4c0041e003603505544e4103c003a034440c2803200b01c0700c031081c814606015882496405004101d005041030303400f6000204040e50f41d40d0f080240c50310443c409e20300352200c2400b8039184103004042858840b400380351080e240a00d00402e2a80c0e2101c1600c09000566071030081c480540b07898403d007005810b003820076a10310308060301c07a01d10408040c01160708000344040000d0040e4400d20540d03001306800c115603910f5134410002000c407070300160541401803151540b51001e03450494 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 42226335 1250 42225085 42225091
    0x1060201050402012d050f040803030c040f0e1506030408041511010c0912140c0306070923060910021914060603061902160f060b010905040605030d2a0f050d0305 71
    0x5100f456034500034500a50301904036104244c08941f042c0300c001551801400190300c108625690180c0e03460401d0794000480c0455045400800702103400c0200d040081401c1c10035017041251401d0f126070710340c944415180308581090701a2540c1101c5000400c0e0088030003403030940d024009100c0b4034041e00085400c12428400c0701e056420400c250004152807840c2381c81010049030a1758844078400c00440d1034400251030711000a5591a02007140203a100c0070700401030001c00d40b047c4044040f01c00620540030b51107000d80f2490a0040c1c03007840900070458806001003950000b48150110f09004080c00f001860010f1a80103103000107400d0303c2c02190302485600326861420100c0350842e6910000e4004400108500074200200b20108954080f0b101d44c00c0e1003424003258a01d94400010726110b070560040303010f603040c400705000c0750703902044450403c0c01525115a003958041202c0345240446240a5502d0800080da0811b10250a081006407030003a0304440c00a9040b5400310101c079012 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 42227585 1250 42226335 42226397
    0x102030912010213030305031009050115050a0e030d0309050c0d051207050a081201030515010302010e100504031b050a080604080304021203090405010b09030d0201020c030f03060d08030106020105040201 89
    0x40056034003501e04409000018018003000604107070100e240c42c40d0007841c540060b40450300100800211440c0f076011140509031311070060025502d0218003140e400c50032886a0140709010400507000303885501100700206005045540c0106500e601900a102c41c070820364683c0108020340c41c0301d051558803010415400350042c4461024100e2108254100420072a2940250641e01003c95420b101a06ca4070031000c08c20003181d4510720b00720345028030b0140380382d2100818100401c0541e80040c0c01140d040c4040d603c0c410191858402103400784107a40005040045400c3c1070960158002061016903c0544041e0403072034441d000c143d45c45504840c0200b107004108006001070510030441c90080750f5030340440e81001084000a4103803070003604080002c51010440c00c1d800c3c60100b00c09411382c001400214540b214511800d03850348684d60042103a42000000702c0c0b90350f1505602c40460345c0d00310a51300c0c0c6a58451708000d01a05090300c050f030024070141400f00840f8400c1e0341029140c4e4003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 42228835 1250 42227585 42227587
    0xd110d150b040512031207080f01052e0504090207050a030f020a0b190b04020d0509010b0d0203070e090a02120a02040f06051c0305090d030e12010c0f1803080a120b0f010203 76
    0x83c00082094010b100e50700c4001d18007050106280b4a029060310500480c001d032074481d010f20b404c03580c4400c6c0c0d40b0142c0c001e902c9810f040105040c2c400341c40e00000d584400207006454505481d85d81030b03803d44507540c41071103014400114182030000200358009076034841c0d40c981240a060a80499990040000141c0116080c1d400301e03038512008045901c03418240f800200b140c4010a0004041341c001a00c03d82580740c48108010020310b0a10440c0d03c1c20b00d01325821944248182c0201e940d84426029400200c0885004030345524001c0004030720440d4010308200e46640200f502545070152140101d008900b0400e12100905183c0030785c3d07058800151516050809100040301d0070490184c0641c24800e00b0001441c15444225501c2c01580c001d45429260980102c1840740c040010200c11450340d14101c90310b60308507070000500041000529051040810881d01a242c081495100810300c0400154080009400c20084140d101c900c080802060741e800c800d1210209100034643d0050f00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 42230085 1250 42228835 42228839
    0x60c03070c0c0f090506040c0201020a020a020609040e0a03090f0f15080402010c061112060f0d02090c0904090b06190602060c0a09050a03030509090702010204050102061b0d110d150b04 81
    0x300c188807040d0040e0142c1e00110416076120304980c1e030b46606803c0844842c0d2144c0030081c060820b8002d4603450700051000314a40030380072130000d403200151400207100d0000017030240100d507502d80008007a02d40b00e41c180d0b0062810b51501030118100c41c1f080402c4008400c02c000343d04280400201c0485548220342c0041c05074141c4100e812100041080f410300030803c0048010656900c10a00ca1103002c0c28190b590742800c9081d060340340300040200f449403096030941d0401740c4600154080703003a03041c0c03500012034031a0b482e10003480c014102c4040d00585040c40000c284041075a2041c002c80064840c40103002e040c1c41c0000031800301d8029040540d101c0008030312074400740802000342c000140b52840960380c40e5800541c03122296801500000c00118014101d440c101d000036801002030f000071481d0a24120000c1e4940030000c011441d107040d07203d1b014903119040d07070865000e01042e2900704500312030700d0605040b42c0c03c0b0026802201e40790900610114441d000020284e4121002c1181040c1c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 42231335 1250 42230085 42230087
    0x1e042c070b04060c060e0a030e03100b130504050f030d0b0a1715090123010503070608040f0308060f1c0512040303050405040b12030c101b0f0e03070f0303081602060c0307 75
    0x1300390940101c410f250782d0340e4200d10780d2401b4000741503030320b1007036a520b1031600d1b0100c1098645103800c190841d1303441ca021b02c46100750b038840c00c00304600740705e001010a01d41e4480c106182021584181c14145003c001446005102c0c240e1020444c0c00c0708446101890740c951a40800000030760984546c2c59001c030b400070380b00212141c03000c4d51101c0b41d0000440c00b05035420240030f4101c01030013500d1070090b07681d005001364901407051034044d003841d107050f42107440e19845066038810307601d40140134042404080740d00c1d40c40d03039003660f100102c025181da0884225004885640c182001054509004001d048251921120215021603825075100c0b821700781000e00300401450f042e00c0007a800720714409442a141ca040c03020f840381c0e103514805401604000e22890041e00d404044d40401003018910340d904164112482da1509040d0b0320f81100c0e28030402c4042868400280c002c0b04491108540000404d41c1c0302d0101c0780b2604510000d244100342d000c1e000d0380d03500010746d00200f0306423007440014449 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 42232585 1250 42231335 42231347
    0x50703050d051803070c0906060305190e0a02040218040b01020c030c04110c010608030d06061803060213051504080f010608070501110a060c03060303021b0603061e042c070b0406 78
    0x40b000340d40f062880b014002e2038491556004200c100d82c2501d44100c100a207400511030f0782e00034903542c20107009614011142c0040d40b902c89110b580103540e140d184018004c0200005403003103038083d104542e18490001044802c6d03070700c141030612a500b8804140303035070751010a40040c03000c0003600415540340c842e010000900500003088000b0340003403044880c108824004c0c040244501d4000e99034464040000710151942600400244569801225a0200401030301c0007200d801c44d80040e01d840c00d28400c1942d81d44540c1c0300702c1c0d0100016a6903138441070042d005004943d020011554200ca00c3c02d103160983c0c03158440d2a1050300054001c22503540a03c0084111113861350035241c038040305907181c1d002c68188032016000665a0035082c41055010055588840d0340d8085002202200a0000d0668440180242c1c0180101c0e442045450701030030440010120003001803007c5c0c1c80b0b142e64400b54601c401140c0503c04801c20b0069000440819040e041d103aa02441519090404d00d0965070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 42233835 1250 42232585 42232591
    0x140412050c04050a0204030512130e0603030d060339050f031903030606110619020a05040905040614010509040503030c090a051807260411030c0307120203010c050703050d05 76
    0x46020300d65852507039554520505105180c955001a1161300710308001d4038102c0b22150f4140d9603001042484507411396890442d0403210764810030700166a0300e41c040790840c05410440040b050402d00d0101c200250b80000140b0341c00340c504c80381404826011304060f04207000601b071051a484203414001818401080c0359161005000c88161424030b12401e00801c8241e40300707030002a074902042c490703143d0015041e4941c03c221802481c481c2000b090144c84048040200070034150300181c2c54140d2405030342560028102400200a00e11b014200007003d002c684458666001c4c0400c004920f40c80c014024034040ca811130001d500310360320006c9143c415032058080660200400c000007801e07a0b22a070400d03d060f0a2540c118006040581002e000d500c85161888012280780c1450440c000104450b503a0254000030341500c48801000481e0405000c5400d150301400340c104081030750b900a20b26016884c0c402e600811100350088001c43e400d005160000340011b204110340c8010b41203640010b60 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 42235085 1250 42233835 42233843
    0xf03020904170c0d02010b01030b01050313110a0305010f0e031603080705040f1217041202060d06080f06010812070f060504060b0a060c0605130201050f0309030d0624140412 76
    0x304180c40072000b041982040e28044000e5100b000c510b850a42c2c28050070303c6a44080c2400c3c01a10311520010b80a8040140100300403401c0f0014003051101c81004d80703030303140c1d000303000c56403207075100c3c10018060300307803220156000750400f251000740f0007000048070204400da0201e50310400280c2d4040700c00450281140e000c000b014000840d85825803100300c00102000e400d51060016140781c404194440030300030480580f03080c0010812158000400700d0700c42d034110b4070160b50323030f80201d00d080c002d001c6034114034010b109011002e07103880e000188503816142c000003151a142c4030011a1555481072840003030120008441c2c900002e0815000250054172410000c1240102c403c080fa030404d41a501c1140000c00500030002406034610809400000035030940c5401401500003070050304c03c06440003200302c000400030300b65020500c161020220346030020721040d41d5818503a00320b46001240180400000311076156110701460a80c0c84860009040074240361510744540901410703120f00361 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 42236335 1250 42235085 42235103
    0x30f160e1b040b120604060f1401120c0f02070b0a090b0703110129030105090312090a050708071805070c120c06050a060e01050a030305070b070c0206120f060301060f03020904 77
    0x5481c1180722070140014080114046481d001001e030301008100c80540414091490100c0c10700203800c4502e803440680740d6180031100382500e90b0004031010311441820f030b041c652401441c40707000e80e80140c41c0600020f066013111881921500c20000303e200e00900b031808100c145034100030030140c1f00b000d802c40c030b0b0003414690702c4860141d41550a41e2151a444042483e211801104110103114120080702054000300f0a034500007c02c00e80c2ca1050704a401d492843d44d10000d840c48104200c0c03010601e6000e8283c6118950710900581d40300764501524005070688a0b41001d07140c1c461192510a0506546d202000311aa403621030118840f0060142007049241d41c00021403250b020f2580a0140c08a0000b00140b610788100d221000682100f0f20810007660300f0000701e80d200b41a01d00075600021b4107822a110410181c409000018000b9000340c0c0c0480d00c1e0004001d004412441101c1d10054100c0704e41c0d030082014222075030740c003139620302c02c00c42c80041c005410302c150383c26800b07031141242d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 42237585 1250 42236335 42236371
    0x60c0a120b060f070311011d03180f03100203060108130b040b040611180316030305030c130906030303020702120c01021e03090a0810060501140f030601090b0315030f160e 75
    0x201c0c0c0650300c46813040c0e0120344004010114208248030704c1c009000e07003000b5030f0010b010780510705440341309000c0c1c440d00c000c00480c1c0000d00f503641d00f40e0354201800010100c0b41c542180c1000f0502a400485c0c1e201e0210349620001140e81034406c40240c142c6600010843c91030f9699650032941d403002500507101c03a80d5402c0020407441ca24002402400980c0d0344404510740e080c4201864641c903417100716410000319a041000941010a903504118048800740d218448281c6030b0341d0034980d0361301421030541060400014550160300800720795009a55021000c0c8070034418560307031060038004030b0050348201138214000100002000b21a9081001d580c5003c0c1c891000442c501c10b80d0704140d1103030b0005a14480080c400d0f11481e802844282490100001d04240d09005402802c0c00308101450000c0084d4060303100d030300a4405808a00d420540b42d04209402c3c41d0410101036990f4060700c1544a0070f01c0c40a03001411420910341c040f041103865003004092a10b00c5005480b002450404c00c9030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 42238835 1250 42237585 42237607
    0xf0203070201060512210d090503030126010b010504140303041706071707020a0602070206070f030810050a03080a0e1906050a030b061303080c0c090906040302060c0a120b06 76
    0x154011103480d800030820b20300f07110070811034404051030408664010140b56020070030707990140040d1070403078643c10f8451081401001c043c010013100108540000800400c0400c400c101e01041501000c00450404074a01503041c00c96080f8220302c0c1c04a2424002000301d8031f42c0c2c1056240703095019082e40c0c00c0035628244440a41c034000000302e4580c203d1020070803140d5000c440200460859225489141850301010b074035882600800703041d40f031f0002058030540d2103490407600502c1d800300d0f40e550300e5109130a004101090503600180e1144d854000001c40d0303d0030206a4041e039400c44030540c03600442190907620150905030a5070052200785015841c0d50309008090002e001c0c0761a1150b98103461140101114034407070f40284581814801c00380b60703400e000e070894180da40c486041c070795a541000009190290300700d0101d0b03006400e0000c00c1001c800100e1803d00503442a02100c12580b2600b00d07045060098803c800006182e05090b440000c14035000040e20b0800a0f0102e890481d010355 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 42240085 1250 42238835 42238837
    0x30714030105070215010b0a110d0f020d03090b0a09061103010801020c010b010311030612030c0f0c040e07030213020d091401020a0806010e06040915051c060b15070b04060f02 77
    0x1112050268042202241504080c0201640b107a0640301074080e002c080840a20710441c10300030b5020031280450301061090040140c80c03004021030048403441000320f007004042802d0150040014002e64403810140d42c0240549085654080b41e01a141d942e200e5003080140302c140c1d825035403152101940100451068010b501a0112000150b6994400c0f0000c5003500c1d02d58202c0d82c10189012011050285244281c9800c50b004135007003034900d40008200c03403440c080c80c1107180d09130240041005034418006140c1c000440140c6082c82055082d101b0780da2540c12501c0083e420014a00d01f150100d41e90768010000c0d198507000000e0b00395005d44035204034072411401d440c0703240c1d40020341c08550f42c0c00400c4550b010f44240381040590310b00c00085061f5028501c505001d8a03112003d40b041c001c92414035801400000d0101c04c00e481920015400500318440e003600c06a01d005201982c50070a80755440070440c0c611031140c50800c407a5070340f80181030b0042081c0c502c9a65101680d400040e940 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 42241335 1250 42240085 42240089
    0x30402030307060606121802010909020a0201090501180c090204060519020708070303030501030b0604060302030d05070204110a020303040c0909050a0314070b01030b0601020f0a0209010e04020d050312191401090f0b0307 96
    0x186e2007102d0b1000314400b0001702c40c4a1040d0100c0444031005410050380d000c1d00803c1a18a50040580c41c5c01914405902510031298020500d50070a482c100c0c0c0404150300c2080c2503401104980d2040355256841c0040344260301803d00010410802420b00307000019440254000d28811542c4082d504c0c50a6418003131f01d07030002c500190b2904010828001100e12107038204904a80070082c00386540d001958508103c591902441004900ca8095685550042030450b0104601c184e5442040e64025200d0380111030072120038502000204a10b86107205400c2800e0b40000180a1034003141c40a5a27810302181c0c038181e004200300308050004400903001402588260031405440c104100064188000d03c415544240d01c42c40101300581c0d02c1e48201c50451307043c0c0d0240b603100e86890010030300d03080c859000500540b00005203001101414481d0b20721410820070364240040c1c800c1804015280f072116200200c68542005000445540d07005510b11a40603000150822002c0701080c1010450303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 42242585 1250 42241335 42241337
    0x206010311090601020c0103110c0a06050406140103050307030305270a03031b050301030807020301020f0a0c0c17100509010b030a0f050106061b0303020a121a3102030402030307060606 81
    0x4004004001ca08212011034400460b440e50503403400d0b10000f5520300c02010100d0415441e001071400c60103620702120401907480068031100001c500303082c000780c01c09550440300d0524050200620341c0c4c000e46400e068030b038840091850071100da2421400340038041c0c5904140300b0a401d8521520641c0244034003580b1901c005070504607a00e00307018013115020007810b0350019100030f502610591182c1202d06580e40111865180c2c81d81d0b001107030081c0201d2803541004003002a440c54040d8000111b0342c082c81c0300b69485a180390729000b58041c03903a072030914012103921488110324015450303001154049000d100004014189100003860000700d9403007a1000d451000c03040c41407040c01c0c001c00f0090961410074203a141812207420000080404014082550115803c03941d14801da40806440511601c01d018036480c07850501c1e90010059003c5101d0100349000d60b44440d440380d40600c0c80518410404001d550114071b40002e50f00003070040343d06010403c000342c0042c010780301d800c01410b09 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 42243835 1250 42242585 42242593
    0x3051c06060e090c040b0702060f070204020f0d050c0712080402012a0c0503010506061c0603020603010e060102010c0c1101030c12020406020313060908060c0702130e2503050712020a0308040602 85
    0x840b428820129406072a00da00b80000300804e024926603030003115040d50381500c4c00c540e41d1100d410482014010303810025445800050169504c2481c03401601c940c202d07002c0d04100c3e40c2c4415440b0043d40c4a800801422203041354250301030380340503104eaa03a000f4010b04024500c0a10504000350f400c03030481045000002452168003401a8181e41c44007408080e07000304030750700307041c000200306010b28500b07483c000408090040d6028003a800010043da400381c00c150712540c6840306110700322002c9038100e0040d0b2030700e0000c0c8082803052002580303040d0880141d0100c00410001100640001c80b003040a010b101000700401030084d02c0244010943d5501454494066241d820202080f90740300c041048010042031100c010b000c1001c54201d900b0710140ca1303880009101248114440c00ea8080d04140360403508007002030042601c030403c107001c4054003c3c84400c1c0c5003c41c0c02400500004c1e04d00d6000c0c0da41440710712880920b4140380341c0000d0a0755030307441e582e039240404c03607006410010040e00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 42245085 1250 42243835 42243857
    0x302030709050a0503120304080c01060305100b030a0c050411040b070501090201020f030c03180f1305010503100e0c060c0312040f020108010609030b0f060a080d0302180301060303090303051c0606 86
    0x40d10207115000b0303160840f59404128a0702c0002607883c0c02440442600c0c10740000420200400501220450705c02d1000a100d00d5589040c0241c5500b196030b450410541003000c0c0009610303020403080850780d0300c601c5c1c40d807600b4100700a010041980801a420011007000041a01a40b503005032000511500010a1b01c1c0c2c0303244002802c1001125484185500622066007440b0002c020341c0d03840c0905044a00c5505a058001065403100183c129080424564030040c2081e0b56000300b810317034105400f25440740700110410700450f5121000d00c40990480201c01c0c1640c90701c2e02c024507200341d46100b240d0810492030220380e111942640c1c00c403030b00808018144210750304040d050340140303c141015410b40d41fa40e00e840e917040400424603c03602e60458000f903187e031341d4000c982000d81702c4002201c0081080f81d2014009601489150328407601c181001065490140102c030141c9030b16541d004d445a1642da002d5500b90418000e02e5550031098041842c04013243c8220b0b03008080d84e80e01d51270606 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 42246335 1250 42245085 42245087
    0x20f072304060e04030c03020c060c06090c01020c01020a0f0503040518040312020906070f030c15060e010504020406050a051b1606031b200f010f0203100602010501061d120d03020307 80
    0x15480c18411402507081000402900180440c260b80c03064060030310b180520001e1904904000b0305989c010307842040820300e1064100c0004902d0310600d400400c030356841d041c1074016a03441c520926000d0069200c800c40c41d00003000281c0000340148100210380c2030540710700000740d040042442c02d6030300182140c104010b16500c42c440c0100c00212000441c603004c405008540184246400644614401d01098040600c50362113207a14540065841ea030080d0601080400f50406100b02d5002c40b42100001c1400d1501b88211002c55940e5110070789480d00f0100305544503040700f0002c08110310100200000140140614a00c0340d002c900d000820702d0a00001a0448901074070500d00d01ca03010b00d00306601c41d0060440c40c0400d0410507007c03c414a207040c0300f40b800e824200142225400c105500400c0c00351500a1400344080002c2c82203100d84500040b8200d4000344201000145824141c40c1c2e1000c10360170205607144041c00400391108010441d41c68469640c021100103980001041049 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 42247585 1250 42246335 42246389
    0x10207050d02100507120b010c0f0308010f0b090310050702030403080705010c14070203070b0903010b0a090b0f1e0607030903060207030f0e0301020711090901090218010f0609050d12020f07 83
    0x9583c240e5041045081540740101106108601d001003103035507402c00c1e4942d038001c038551610741c2c0c1c1c03201164244504c00d02d8000c040f901d003803040010150600c98007048400d084801d42c1c0c041e40001d4010648558442341e094040c2001810080641c0030400010001c9000800107010035801440041011003049c40000c0c00a03034281c40d100741c20b000c00d2103181c00698011504100b01e0340308501550311070119000007801030080840c904d0b40503440b0407001515034116001501c4901003101c3d50740005091100b4460b80d62580175503051035071006070b81c0d012340b480c00501030f0170b01502a10b844001c00c1e8a076503849040364800c14056010806d2003280c0820b02c0e911189149058034240d00950a04802da03a44a40080e0761901c0c09116140c4080080c40d503d02c00d40c0110704583d0020540d160003003001da16206a2074080c000c9590341c10040d1030204015010b80c4100040b0740c2c02400086922081d61642244c1c05000d4072034004600803040178401c0c0c1e2a00704102c8014011040d070324800101c3c8003841303801c0703 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 42248835 1250 42247585 42247603
    0x3030210020304050d030b0a0b040306050103050f03030601080f130f11190b0403020405060409020316080f0a120e03210d0e010606050307050d06030b010312020c0103151a0c010207050d02 82
    0x1039034010020040001c80c0460b07840e043c800e10b400d020544012410002e1200700050b04000c05814020800006008403901b28504880c001c106a5001d075000c81656501d0380300481d02240880c607210007080001441810159008003540c00d00100442541e9039598400b1600009481218500002054500d4481209401003c610009030038062802205520a003d10300c40603110b6a910400a91030b80c071541c100860159004091391171090103048405103040c6180200d80d003520482240c1e0200307010010303098101a03001250121018004d02d4200c03035001840041c00d41500035584083c1d00d4003440e10360b80140f400350901c01620b500c2c8a03c904000c40d205001c07140b81681c10000d04100d82c0b5002812240c00c10810b14016503914100b10000d40544042d6100a00d4061301100002c00d100c0068003d12810f05181d003590741c01d16160004405644911604030701c0002038000230040724a020400f81d076032000080165091480030f510241c03c9030802201078440307400140c240c44082e03606002c0d4000d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 42250085 1250 42248835 42248863
    0x519020a03080a0b060c0a06020406140903031902010b090709060f0507120c020102030f0f070c0915150306090e0304050301060602030421020103020f0a09030c050301020a0c060515060f04030302 85
    0xc500d403800e880040ca5198042c0c48020420b0340d4000c41d900984442c4201e944a400b17103c1203422000c0e652816800a40c080d10130100001d203800e00103510303094000c0031a00d0307030328004005604107400e68400c810010016000d20080d9940c0e69802c5405841d04140300e4403d50042e115541140c1c81c01c407003d8020303c40504e1480c2000b00030054000040e80b118203140700e080c81864400c40031125440141e107148200001c1e4102e0040206262a40c1017130040144071140c824805655810303914540380c0250b4a0400b00684a40305860040c001006d40b030008000300803c41c580890703031590325a08401154440418031810303030400a01401941800d0143d02c1c02000c0c1840150724003481c1600035400c4040300305581d0300e2609a40c8002065a00c03039015904511003802080d03a072030707000090103000354030144011a914268800c00248600d410b100b640d08070304181d01c07921498807155964900a0100070009a40c11050303421184468540c0c50150040d41c2c01c0404041d85c0e2070660401a24050000e108070b4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 42251335 1250 42250085 42250093
    0x3050603010e030304060c140c0601050f0f03030702280602010f140420030307080309030901020d050c07031506090903170a05040c03081305040c02070302041a0117041a0403051902 79
    0x42d04070300002003200c2d841030b000070001031082040d01044401e000c40f02e02260310020086500310f601c0001091076412a1400ca41d000c25101c01d03607060104288980704c41650542090240c0c070013508040104135101d8400ca010710102d91910303580074100c1c000036048040141c1d03540c480f500038038171103114809034000f16207404103ea03d8256905210740d90300590224a170344149490344070a031410010744600c03545c8082815281e28102d45a50380d60b0b004a203030300f07005200f40e040c01d05440f4041ea040301c1d801c1035404003410340340b42561034090b00c5064500704c8004595541a00240a02003449550010ba00c00d5591145005104e18910118500506101071451401b0280400074407002c041d4011254440411a01c541c0c420f040d406014000d035105a4001e81170a030382e203030380b03942c0401c0310300949101700c40c20041603600c4484064100d0b4868401804a0a00c41550b007410185451031544248207580e24942d004a4070503a00781e000098404801055001c254481c02c02c60007508101c02c02803600c028 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 42252585 1250 42251335 42251351
    0x60f060c020a09050405070b180301020a083702070311071511070e070e1305070e0a080c060304080702030a06020d0504020a060203211f08100b0109120213090f0b070305060301 77
    0x14039280d0a46100751005240c002602d0000d030b0800721009e503003a46008000711b45078081034102500c1e1400403141414442c91103c848030103184a1624808000c008042048104a810301014003d5015660a506100c01d03009400c5030b00808114080160122041181c890421400060300103080c88170041900d070840d40c010b0245c00350001d500c42e404130283c0751a4800d480c0c810045a29000c15202c00900181040204404c6642280170300d03502c05003c1d1758812240c0d60340e40000b41c40389a1606035985c0540108046404107141002501040d80020251180803120340d42e072004076409803000c605626200c40c00c010662419100030401030100380081c601e480300c021181c05801c0300c98005042121b240c08041050140a04080900508585a07800c200c40d22200c0300382e514003581d11030380100d900b440428401948100c40500171110010441d0072a00d003e6400c000460f80c400080f020031503034650206000c00c429020160003e1301071401142d007800c107050010250b45d07000380041c0c081c0e8101140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 42253835 1250 42252585 42252593
    0x20d06020912070e0f1005030d08070806120a08091203040e06040c080c1c0e1510090e071203021c110607020606150f04030b07020d080f0c0307030c0201060f060c020a090504 76
    0xc915171102c10640410160740c0c4511b0340c520480785c2070b0407080d003505c260401962040d070041c400c1400f642e041d403200d03609aa5a1410032000580ea41019149900414501000120b441014090180d4024a440c580c01d10920500385590000d9111604030320b825000e102c0642450f100d0860405e0051a00b001c03517180129140c4418032440d0725a42d242c41c011813a182034106258080009013410805645201d080080014480d400a9441244111100c90005400481481407903802880403001d429031a1503d003182c2e019051429054095018101c0c0d01c1d000522000074042121150b521104500c0c2a05214188ae000005010ba01550301140a01100307945480ca805080d00f0360f109440e0780c0325240e040000c0a401550b100514000c19801032058054002c111120ba0000e0f641e20050640e43d030780554003042030185c0e8411062001000481c85d02e6110f41c02c00e110440c035078000801c81c103954400484141c4482c0d80031600003000c00082030214505102400002c00403506d060101c2d0a003911 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 42255085 1250 42253835 42253859
    0x212310b04030320151909110d241a040603021f0909051006020d02071a0c0703020604120203060c030114060a0e030f010501090e011109010c0f060203090307030f020307050622020d0602091207 84
    0x400740d44201c80002d01040ac210701c24900d60340700204244210701a01800400c0c6019003007205030611448038401e005542c034145440f42d00c04407034005000306404801e0351166101e2000b01d1040790100710045402094030811405054050160107980e203102e149020700080c1011000368050045401035801002914141c1883e2402c1240411010380d03038804641015240030707155400213400c81c03804200082c1c0540c10840240d4130768002e034103079101d95071951a0080f0340c0c4000d000703e160308421500907401d581407490142040068a04042d00c1c0c203c03486000a140c40400c005801080e915600180013412450080c41488032181c002803103410b02010580b01036000b80c002c1c030b9040000099840341804410303400d980d8048e0300140708645d2030800b001066100c3c0d01158090307011440d890310b40300c00315100100f11498030b43c200d80501202c3e2185400341c01c505408480c20b110480c140710103400560342d201c0144a030f030b51040c00010303903400d000301c1030040036003d14004c0c800d1600070600810611940720 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 42256335 1250 42255085 42255113
    0xc050a0c080307030e0601091a010f02060a051914060301060807050d0206031e040309030c0e0118110904020a030902090108030a0f08070212310b04030320151909 71
    0x1034041e90700e9585044003100104580078805000b8400c59000141c16140e80d03000e03c0302c1810400c05c500c0078014442c0152841c1031195030280041c0d1080c40011511502da9202075000342400820003102c584d60000c40003622000071001060213082401d20410340390900c01c18004004000141030030b80e25003400101a4680c000e03001e03006902c00400101c5402d030b14035003499040c02c421070140090a003410000c0006a01340000c440c02c80824074082284146410791b9812100d004688007440c00c1c01d850b40801812546001c003091450034490254569201d0020f0190640280d900050080315401080034290040e800844550010001c03400c0f443da000c10242c0700c001c203e040450b040d0b01c454000f24508504010954001c0c0d1010031109903256802d908044401c900310482491403015000e100e0182136035211b48030710b080b810081040000e000351441c1440300072201d41525186c00c984915410719006240f07950740b002c50003007003044100e00c4506402ca44213200c1d1007046040039a83d64440c40e4a0a2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 42257585 1250 42256335 42256343
    0xe040507170406061505041d0f0105041812180e0915100506071a0601211503020a09060f0911041202120d03020c010c05090a09050402060c0319030c050a0c 68
    0x6140000c0c107200f00340d00241c0003440c828450310700a0b814004010226080340c02081d10036112210420a82c880b0340d1020f6004080c2018207464507487c1804100041a10644100f40c1040248507140841c107180405030565501d41c5030084200c2c5400f03c04034041c101d0743c1102080258820500038220000605040c5a02c40c07200d01230314645410b81e071130310b02a8450388050fa209000103000010001e204808a000c070788150691055502c4900c01540d1008450358014032001c2d40074543d03081c00392550061405505e11060000240e078680e008a032010480341c20542d445504c41108101562090803010024107a0b070504103d03010400031422054411845100922410742c0000c0f015540c60240200350050030314115455200702c0341c03001c0c0180d00700140c1f00b46103501e44101050114000d404451107448028240113000382004a910000c1c80090002e070381200c42801074240c0355104000401c0703510a0400510003400703540000034150760340407a500c003c0003404e010381c2036030b19003003090560740c01c0d40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 42258835 1250 42257585 42257627
    0x1060308030f040f0606080102070204051e07080c04050904050c03070f06050d020d020f07030c030f020a0b04060507020f0307060e060105010504080615060d020a080613020a0212160f03030c0e040507 87
    0x3076044c0420424410400500041e00e0f000000425000541c000d001052003681e09000300e0b516441d103003c1070b2030b001101070700d540d0f0048d0000d580944101c51096001881c1240c031805c1075120404070707036421011101101d8079444a0303012107542c6000c0111000a200c0041130903031a90620390000c0080c0604805000c1c0d098021510829400c00c07078050324101b01051841d50b480d620b003420010701e01103803a2810b4011030804c4156164040c13021402e2801b10750041c1e00c0035502d03207480d80c2d410002e00700144070804600900031072145030071043c001000b01c0c6000707140100d10461040c40c51400c1030811781c03025040c05010030041003007030310110702a43e002c0103400c46d0300c13101c80c1c2400200740c0d00c0c4541c0b00c0c146419803001400b80c80c980e070440b00c20340c000c100035101c2110f0300302c2915150040b0f108943c040382c05641b200c1001c060299140d8010040d4401070815400b4036450340d0340702a14080e90040440119171110344001101c1d5001e0b410a8602d1000c5505002c1418244d101401191940410a0400719 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 42260085 1250 42258835 42258841
    0x5070801062106020409050421030605010f0522030b01060801050402090d0b041a010902041a030c0403021509030a080d0b0a060906050d02070f0303050f0a14010b0306010c1a100801060308030f 84
    0x3c110340c150b130014200c04905011a18161074180c0c041145003141c01c821845405070131402500c01e20415041e60f406855400314055403c00540f11600003288420541103c210100c820801c04903010700190300c224038114855041c44d0015000b0241600081d000c1da106210901850b50340140503c45203030050301001140d00c960401510740340080c41010041c0c049180006207514040e8010001c644c00b03038111703180c114801604008035200681c1e8825075010300340800d001624003031400007a00c2984803c45071074211325502080c00c2505003542520041c8001c603010502d1882030096441c0200c04540c940c290310309080014081d00d00d00c0c0541010000080740b50302001c202581224801c075005950795814801602e030041c0a440216a001d0b0300c1480301c4041614a0840d005441508808006414041c0c0c00c00d815400a0f410050015040285a00c1e00d10041074005a00c014402500808080c20f468a602c8125421400e580801641d03032400d801080460303200c4081d80d81200c40034002c1c81c1c90b52 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 42261335 1250 42260085 42260093
    0x90d05030f040501380301090b0c0a12090303050402120303190c12020414010917030703030f110c01050103020f030a050c0f0d0206040603020301260a0f0501020c010e0a050708010621 80
    0x824516103c0c02210452540501685103031040f00d010b85c0a602d68064030203c044051600781e030943c0400500c00342800c404034a80d42a6603004c1d00e40c000c3c0e90320385000c005045010980c2515540f450643c0440c0d9078006000c1541090340c03010b905144118011407441c1442c160203515039050b0341004d803e00c2d50310700c2c0d00100f00d8800c03e802c4075090511181503494a803101d0310104030144040c2144d0200705c00342c1c8002032081c6200c0d101b4114040c1e55001d54181200360310150b000d40308101c0f241000550300c005400000f12420040c000140c84000000750940c10b510500c054a82000e200b94841d6128008803030003e000010405e030401429600462034045000215283c8040620025030003100400c0c08200141c1c154040d60484105e10045190180c008844a00020301b40881c1c3c42240c10900031140420b40129140080320b1061000606d840450440c080c2150b5100001c2e000da5000424107509101c410031911001e81b041d10000c010300c0e49420480c140070030b2505003072900e1007441891b240c180 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 42262585 1250 42261335 42261341
    0x1403040602070b061e120f0f060f01050405010303020703030f0507061b030b01080c0714070e160e0a0302010c020f0d050303010f031415040b1312030204050315010506040b0702030106031403030708090d05030f040501 94
    0x90100d10122411105025000d40d1100c20071940c5d01c02507103852b000050545020f00540f8104c07074154000d8542c60342182c4045941854444054050003407c0047d10f0016031284602c2030441442c407202200c2d240c7c00c0707030b00a06550b032458200d4108204801031041601c800d004644016500c41e00030884050035602450404000d50b00075040a24110104140c00e40191030340401507030f45940d13035241e41c1c4010341001451451400040d00180e00f4240e250b0050600010003501c80c81c0090183d000250541e40c1c2c80d1556000f608402600d00d075580040042200040401c0d04007600e01002d030050340744580ba00c1c0b188400c0140040c1820140201040e61260550404a0364036003041681c2d04c40d0006d1000036010354000d1041d18064031445200c4403440410b100502e0586000a01061a080c40c00707405440d650006d50040e82e05540e1000f001000030312412070300d51081c0341440916146d181031940505046402807200b01e80ea0450000c1c0140958406e088980c000c0c02e90550b003407242c0b1581030841c01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 42263835 1250 42262585 42262603
    0xd030e0306040b0601081003050a03050c100c02030a02010606170403140f03090703020a06051e180a0f050f0307030c0504020a03061e030c060f020c0609011403040602070b061e12 78
    0x10700a00c402c2c0402d006460f05010301c00c0c102a2a02e1986894a100c4820b002e8082d100140558001d041c1c81c0001901c074000902d817110005089401640398503030b00e1400c85902a2165001d640000b0702d40301c2c996028002c0c80018900c0d401c0c0104000c51200c000c100309600103100800708240404c21603d18512441500c103500c0d0445982d6899183c184030303290343c811702404260711801e4401d000240e8148034008076172030f500400c404d096009103066480c040a400181c28182c001e080d001800300e060b2500c4000c00004c110645000340103e10300420b00100000c821103e50298014240a0002c2040214140d0841c1e00a0780c0040c2e90b44207804040300109280d0f041011500d040d8041a95000032804044054900984d240d80c0c22940d901c0c815908010017191540240e08480c00c00e01d95440d0107005440307100c406050a106540b04003510312915401183d04030b51269011607040144104d000b665540424250794006c00751440d1014524414200140f04d80302d1010003d0101c0d002c9828016401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 42265085 1250 42263835 42263839
    0x50c160807030c15020904060e041a190905011e0204051c030915080403120e07050d080c0607050c1504020f040203040507030804091a030a080906211e060a0b090d030e 73
    0xc00698013107aa60181d4080c00b1018811800c01901088140004c0390b86802642d1000041c1c00c01042e40418016900e4020019001c0c00300d4428580e80c00c0d403550094103200c6119900000d4034041a40078208a4446000c07804200792040c0300500180d00c414450103555408203520050400a83c03030121101800c036001040c121003c60b01c0e1061703d40d08900ea80780242d109865443c402d03001d01d01014110b60304070164850550028008004900700312a01d4100700c0d0203000b602e0310700100c2201c2c07585006810759403c000500b00142d02d40305a84240704507a0a1082290485644e041c680c0001c0c1800450700303a818810344c0d0010200742000001c01c5002c0045611000a60f1540c1d13031015018001c1103280030710b0501038548200410303103280c04596801500e501c03803c19410b00d0303482070038003a00340c000340041c1c04201c03140c0c041c0d4101800e00000707980c846c0085240c041c500113000605040840b0300506200c1c0103510403482030000440007030036203030080000d03100003601c620f09040448260032070300300700d0f6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 42266191 1106 42265085 42265103
    0xf0603010504090618030c0506070815060912010501030503031506041a07051e03030610030b01090302060d0f140103120c030503040b0a060512010e01050c160807030c 73
    0x710300f0b10f00421002403440440c080745031440b01900d00a6000c03505482c440801c010b810042c1c21b60181c030501d000c2d1300c60b0809480181c1d048000d00180c92140401003041c54060b20740c98021195000031100030300c642e5a5a08049440b50300c00d0300c4590f803405a40b540c4818504009049400f00c89106400304a071013264000255290048001101e4a0181c9160f03015610703074001104a60f0b0407000095583c83c20030504019100031801d6522091506014503003250341e8201c4040300131241c0540d56190756a000705844401040302c07000a15201c1e252410315180400002001c2c0c2c1038905c9440b0800b44011a941c0c26980354408100080008008000080014880c202d5a03a0042001d24020441d540c0f5a000580241c0e03100c8540d2400769520300b2040b100381d00034001e2607003041e0007800305c520f0002024124803515042c8100584090800150081014490341080000c0c2e038100c1c0e224 = true := by decide +kernel

theorem cover : BRFrame.Cov 42086335 42266191 := by
  have h0 := BRFrame.cov_init 42086335
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42086335 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 42086335 ≤ n) (h2 : n < 42266191) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
