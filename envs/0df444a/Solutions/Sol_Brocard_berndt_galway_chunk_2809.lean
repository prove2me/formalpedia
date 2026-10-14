-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2809
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:48:44.573674+00:00
-- url     : https://prove2.me/submissions/9bebe80a-e43f-4b19-9e07-627b979d6b91

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 505035971 ≤ n < 505215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 505037221 1250 505035971 505035997
    0x706090509150108040b090703080c03030906181f06150c0201030b0111150402120607090303200d0f02031e071502070503160606050d0f1208010b09040905030f 70
    0x1410403040c80c0c000141c40e0003104902c050700903008540002080c14000400c06003e4042140204020380000c009103070045800c4000c02c0d40b51410419080c0d00c07584140c3d6149003a2203941c0114511310b21184445001c1148000101180340d0030706030180300c80032000c00d43da14050740c0f501d00240da1110f0512100d1620a90f43d00d58583c0e40d801d1001400304c03144062418100102c003044c1420010700050f140c0600d0501442048041e42d481c800200d494098078407103c0f20f070040f10b041c03000c52038105600d079003600c1c425124800c01c10003215000d8200400308119085a40c001d0550300d002078000e92130384100548900c166490310500744684289905034048a4517403860010b1400184502a5500000011402015031070007180380ca525aa038000c4a0f041c1c0c00d1800c1c50385d5504100241940a50000c00c0301910402c20320341141403084403a00e18440949aa00042c2c3c840809a4440c08109040c1d410703500580d410402d81e0000d10008159225003181c492008100c5110444040d0707014205601c03c0741 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 505038471 1250 505037221 505037237
    0x711010915110d020309030a020402030a180f050705030303060a050118050402040b0a021018120e040c170604060509280612030f030b03030f0309011530020a06050307020f0706 77
    0x4507440c80d081402a000007117400610034807040d40e50110711034140640480c1c0158407611031030f10240003480c401e22204c110041c1e8500707007000c02c105100560700c142c1c000c0301a600c1c61a918001e2603107070700c4105d0303941c3d41c411902c24091100d5802040e1941c1e071040c031410485c8032542c407074000c20100d0f8001d4002c004258008074482c001c071a4100811005490564014429041c0008840c1040d904c1540000c0c0101c1c0d124101d69070041c850400682c030300b030006000303100c40c1c0485000600720280a0140200d1000c420380001c049003010301441003141e0014140e03013003580e203050050340f01c681541c86050640b5041e021008882c482806248064030351001c48803448222032401800c2942c000741074805240c1445204491a640401902c540c0803005000e5030f52a44c4416040d8014411000042600e100c40c400215040c1082180c050712200d14500440e82c9240104d101561000e064200a5200c008c55000f44842c2d031040703019541105590044640d204940c407413007400c01506410a02c0050310030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 505039721 1250 505038471 505038497
    0x207031e1a09150907090c0c0506070f1110022502090106080c09190509071e030504030908010c030606392f03010f050f070e0f040903111b0102030711010915 69
    0x203841074480403070807822320500e103000942c1c4064880c0d0004110703206204001d0310a52080d402824404c0824000d40191030b1045600c0c030200c0000c1d003000108404038000d00f0091810081c00a241c45401e980050031602c00d61320380340040394220802040d07070074007500c144aa000c40340c40c0d89903008010960b5040111081e41044240700b01160f00400a03020080701d040e54001032035080034200220042031030040380380d80d00e13403c041d10007900d070390720180e085c1d80f800380303904c8c1032980c035902480070703034215946642c0980d840307a94268032050150350607103c00b24203518002d000b0321042c000d9208140b156010f548182c550300090140b04aa4041920801c0ca050032000c04900d001c0c441e02c1d580a240e03203c20005400c1032400d04041200c001e1811003840b680e510b017180283c0d5142c0101c001900c0050080c08606080d2038002c003088618860000c0c5449403288000c038005c040b01100e805190180e0040d401d10119494003450240ca00b903c403810f0003c4100d022808046c111490300100c0e031a82c650980c0034180e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 505040971 1250 505039721 505039739
    0xb061303060204050f0f0a1a040f030602120c0a0e040b04110c03030106022802010c031403191d03031b0720011106060a060c030e04020a0207031e1a09150907 69
    0x45c2d0180910410b029160a1410f07910100f074002070344c01800725540344d800724455014251250346c1003c40f000d112808000104a070030380003007460510380d03490ad17581501c0e1030880440d11b0261804800c0410301040503221241082ea00881c0c403203c0051001c61200314a13a5100c03041e80c0042c222400c1600000014455a40c041101c0314000d0848003c003c1d0191040001c07504818150764000d0420081c804c185080c180705290059403a00207404a607680d00f02000c0110814029404440005007805800c10b00c40c00e102420030300590703042d8042d40c51640c940d0700000042450101c884c2c021a01804404049100710b1135403448080d03120356480c28962400000b500c0002c6105041c550341e44500e0400c01d16489a1460400712a400d0074024082c54461605450b80030301e2880142d0403910216204e4401980082c00700202c900401e038420a40c00c11041000c40080c0741d2030702500360001c01d1a107403090094a001664800500300c1079500388444441c0000422506654171200d6502c030103028405405 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 505042221 1250 505040971 505040989
    0x3130e0103121809020903010e010501060305060109080619021b010509030a090b031b030a0906090507030c0b0406080103020f06070210081807061d0d0213060602010b010f02100b06130306020405 85
    0x307000c0c10a1030103c81082001d144142c141e01413548201c0c0c011904580300c1d10250040c0b5014030001009002035030316003000400501c07003100e0481c0040d13075000001411010106d03c50b03000b401d20303001550a40b4207202c1031002035484030b955031464840105108031582000e205640c000c402100c0038582d20380440b1001001100705130840fa10350b010400508c204d8014902c2440c0f10301c2584180103484e60b882840c80310090400340e41c0900014105601c00c000c2010101e0100b0640c0d2040600c4a0740b0b944800122120707002d40d0240310003299403c00140098075101c00320403880760300204260300c0c00d0041e03070100b08200b800040102c00728464100344034006640c07540080f44491520010300311585030880041c880d41541210003805c00043c0c1000802c1c1d254122414042074000d0a48081020801c4481703009252501c1a172005529181031a0315542c440d07854500c2004280d4001c000f000305540ea002c1c01000a09112580f01504005d60000c60325510100d0004502651005888034a00000e2003030f600 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 505043471 1250 505042221 505042253
    0x7170c03070b12011a030403031a030321090601030519020604090c11100b031e0307170a0e01080c09010809210d0b0a0518070c02090406050403030c08040b010603020c03130e0103 78
    0x1d403d005640101742030700c20079290700c581c01d803401042180b401800c155481280070501d030307094040003908005031000c0306240003004121031026645a616038004641700e03c0c0c217000040441c0c0001e440d000044410594944007640010241d40c81d2a81d500307035440403141d0102c6103602040d841c00302e80d20054414031980001a88021041c08a442207500080d2030741a61040110041003c950480d84100304100f940c0460f80e01c05030300c2515546034045001640c1100001000091440c22440520b510640c2e080e80640d6500e1a0a41020b000d50010745e5905001003c2c0d103028883e910344841c1c1c0550201180e10340d11300d9400c000780d0b04d0225801050640b41d611091502841c1d03034481c100559155a203a4045800142d040244241c403441012100c0100120002c0d6002042c001481b00b403049a500190042d4440d4408104850220ad011f54074080c080714080c010114481c01001658026002400c0e895080d100b52441c04000312403445a0140640041804c212088010300030000d00820b001218 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 505044721 1250 505043471 505043489
    0x3071809150812070c0b070524070e180a0c030207080d020301180c02070b0304051614040f0e0303010b0703020a0b070e100e1f020111270306040c120602070204020c0120070507170c03070b1201 84
    0x705603c332264020410090403d2141560310544048418030a07810f4400160340102d510f641c8074000d03600d40d0042d4000380100240050844600a081d001a1103140644031003500540600d034a04801206250001070007503540d400740c100303c0e0400154074030245014014454002002000d40000c1c00211034040340d1342400fa500e0325a8076010070f107001040e2811100e84e54607655035071445150480c18030790140300040101309890203010203a500315404000b00721080e5102c6201025660007228120354a000194003c80d0b02403000c1e0110b040610000158507480c00085a000707038040586200c1d5120450304952400e00100451540260740a10704407020100c00030f04242c20141c4880f61503007114860f00c0c4141120516410030402d07203806440815400500031520b985500c005980a1304821810303070710728850742d20720310015a5001e05580e84941c0000040014904211119181c450310002c510034a03c20340541401c0ea035010005140034000e058481f64231203c01d405144c26480040c0c114000d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 505045971 1250 505044721 505044739
    0xd02070311010509031e1539071b15020a06060f0609090f0f09050c0a150905062d040303170c03071809150812070c0b070524070e 57
    0x503a0002102d0480300c416846e80155140c000240a2800480b9200300804040d1a810040d801103a16403248a0404403032010304103e100f0b00d0000c4110b1003100707158400380f5041c807a06001c00c10510300a5100c81c101d0403140c945030388802c81d907420744a0922251300140e00103c5403408000c0a17020701c00081c44100c41c0b41044504086001d0610b0b074480c000c1c010b4042d0384850365100d8482d142c00c11481c01c80c0c01c00042029200b44c0c10881c2d02c9100e505456405914810000142c00369008501c1401b840d10f40d80b8500d010f8203003810030025900c101c00309001c400400746040c2c110303850004021030340030308260f12070340d21031440ca0040e00c00d40c5007461a99a101203001042059205c20084a900200c40c0c5010074032074420718800d80f504101a040341c0f080e075117080c4e11164109041090002a11000412a070410f410401e1415640c03080150003044081c1030746013000031450f41030103010424424820350703440a83c080c5401500c990324412a51440556400b8003a480f03810009840c00f0381000d0f5480d0b40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 505047221 1250 505045971 505045987
    0xe0a0c0e040515010c06020d06060917070e06010c02030120040e0c030705030c07050f100629041403070b03151203071a1503100204060801060516030c140d020703110105 74
    0x18070041808101d05021502c0d485004028061f41158a42202c0d8141085017580318100101090454001d2140d4210780c404003203c01a40090920210741d0054840000d594441d401100c1804008200300c1e05592120507a4065142c04094065140c3d1f28401e16030f100c51414410041c5080082c1a50705800c3c0c0400511410680c040100d0340d108400e203243c1c0c2e64a101a103046450401c1c00d18510700355000c0c031807224801603d42d070000c01c11100f9010740c00d0b6044900882880d01940c0b204d1702000010801c00040040030703034802904502d280c00034155207880d076544080c0030303c945c800c490300000e00e524885c048940e450010a101200f03a400c0c40110b0a141d0540e42d002c070345041007409400c002040e0310014000300c1e000c65041c160880c024007601d10702c072841e8a0090182d0014061400032491120000c502c403072090003929004840350410180000064600380c1d009003403198150b450b2506144c80041c800e07810454590310542aa00420001e865402d10002c01000c03142880d04202040184071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 505048471 1250 505047221 505047241
    0x9050a18080301061b02040e100e010e0304170316030203070c15080a09020f1503040b011d0403111002040b0a021605030c0108090c040612030801050303030f19060e0a0c0e0405 77
    0xa040d608a07040c040908051640c4101340e02e841d031710f0021340c414107003005901c0710400411050200701040409110b00c1e0503c4210314240d65803540395041701da000f4842000510008400960b400b10020240c9142281110303420300034000c132010941c00b60b0720000f03400c1c00700000240300b603008020f04d004030007810000c210001c1000b000a000140760301c2c1c5441d0b0740419550f4002c1c1500c0907800081211800c10784503031003080300303030003c44045d25480150000012101d501b00340340341280002090440156440b6642610131b20144e442c03901d020312030b820301d100114840b07100400140203000300450f128100580001d2400340f030904800e040817102402000036440001d40300b0782d0241c1c2420440100d41e184400e1515064240e11a05d9000b414640005540c43c040b12500503198060782d50501e03542e03214001e0582e644803e881d00025100f802c00021810281c5407046416051104000b241300d03942c4402146400c50280c0e41014181d59400349010001d4100303143e03c0c4d8499003030340c0901a130b1400a0703203a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 505049721 1250 505048471 505048477
    0xd051c0f0f09060302070317071d0f01020a02100207120b15030703110609060d020706050702061f1716030804140319061d070b0702040b12060c2209050a1808 69
    0xf20080c1034010610340f0406001c1e480039510380100410610302460490002840c1c407085501c50031800603500054403090501d41c0742d80d4000781040e0000c04406041d0350a100310460a0b0b51002e003140030f00d080c0483e01c440607080f902042400303100d54070002d05001484810344400c18043e00e100340d00008040000078455154140c0f484030440d88a6211440680030070f01138860791045030a0706100040a4040140b10b81c0800e009800942c2210100d5899582c1c44180018450703078240000c80507401004100901081d19080310a010140d4040d50382141e141101d012140c1c00c1200c16100128052004051a6001e4200c5043c01c0700105411903407445400107200324101e01800d015211400504008e0409046d070b55442c40403012030f03c9456880041c9050b035001900200c1c820307801d0545a801a290480c2115007441204003e4551501ca000001c130441d40540615407490140b9405140e691812050703200051111020114091601e441c200c0c086031078414150f012482002e02d0440401c20311015 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 505050971 1250 505049721 505049729
    0xe0f0a090201170c0f0c071a03013218040203010c0203161104020c0f06062103090f040b2d06030c0412110607051e03090f0f0d051c0f0f09 61
    0xa00f80301d45074980c0303103003031403158000200a41000041c00b403030340000042ca510480d0100504416542030700a5407400701c1c0700078810300c0c01e244455105070711545480030032000300a00640241680344260004140ea08030001e002510520680c0c08000540c2004e0098460600031480a186424540d4252207e0081c4036203010f8030100444044107980e440341e504a50340817081c102110028200d01204c5c1daa01c03101218a10f000c0c04540820a0b20001ca00b00c401c440200752002950500807002c0501442c1001c030100c02c1d0313000f526000101802c1d04c0c0d000c0d900d02900458030b0603400d440c03040d02011006018000209014150400405c400484548292000e580e45202d072250412690f06001040d01c490942c802d030301ca1400981c00c0100a0300061424803003400001d0051104c4118900f607440b4021802d11542040b290b41d00c5100c2881c1842d074182010380c0041c048140b4107580e8840f686000c4404013484907901c29481c1000b034640e04803954080b444403924214540b100c80840003031201c90a40300b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 505052221 1250 505050971 505051007
    0x3020c07050a091a0631171b0f010f051303080d020408120a020627030f091e011b0f0609081c0204051f0c0b07030606030c0309020904020918070e0f0a090201 69
    0x140e110307041061240319001020b1074405c01c1c40b01201c840d031041e200c414503580300c104000102c0d0392365820300344100c44880e240030584913000d68144030b44065036560300c03801c000c450051b05404e0102c0000c9a19000d0110701410250050725141084005450602c41c82d40c40e0302d03044001d0082080e9240c0c0010391035403161859080d81c1c194821001c288401c28114150f82941380408519503200900c58005804080c80465044000d094042d02803801d100c010013a40d0300140c04902142d00b88120091903640c0c1c9481513640c4c2500b003500d40caa240848031403080450b2003c0700000d8a020f80320414000d54003000d0308030401c514085ca07010000e0054111084038010f003c040708034902045004084003580705822501d5001640707080d01c1c00400800d010b0043d000407d140654015425100c1e2065403c89540508880b40c4d6480b290200a0203400003000c02403209a03100c002e4000d014140060402044180030f018070034100041004a0300700c00030f00f882c0c80b16141c40301580150b03038400d080d9214042c40003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 505053471 1250 505052221 505052287
    0x130803030c091011030f091809210c10051501081012140102031f1a0d020d020906070501091e02010806092a030a11030c070303020c07050a091a06 64
    0x40010f441302144140b104810f4040801c40728402d881080003803001d07807411100c2002400c0e024080c0d9160b03040599070189268000c12080c1700100c1440d900888511606030014103240d250068245050f68a00e5040c44080d141d0003440b1000354064000c605103002428020b80318600303c0140c0b006c41001d8454205101c1d0744c001c40c002840405499055a034030a54000d641d2482c0824003004800500c0e041c044045030340341070000d010b94a0301100c0c00c0300088110268500054041908041d4111084004a81d03500304a000180d0342c4031002410b0f000d125030000b1540c10800e092059408544070a0303004a4180000d02c540144c3e807103078415a000c102150b0106058450b200c07c00d400c48039020f031110030390301c0021607c3c01c01030800018507c2494030345030511400d101008641450300068403001042d20082c00840c0000380030360090440150740d0011184025034850029191141c150700c141e4180341d441c0c8141600780340c80010400300c108192001740c54614100ca8511003075a07412030b0420501412 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 505054721 1250 505053471 505053499
    0x9180212070201270309030c0308270d02220501060f1b08040b03130206030910110702030607050a02010f14010513050907180e120a09090b030a06111e130803030c09 72
    0x2d614091b014542140740741141d6626481e104409501c0288040381448280c60540c0c41c1c0b84141201485660b805880703181c1e182442d031b080c07080031100d001204006400c5906618030b0850b40d40b01d100d0080016607178003020700c02c81030310180dc600e02c1c941410b030301800c2a100f2800420290b00881d0704580d240324855590303a071145000c0300140095a030080d40301000005100840100049405a03d207150030108082908090442000d00c584c8134004c0d01600150000303070405014801510748036440f40004140c0306065884003085030180c0c031907841001050b0740140210300700040c00089a00044004100da400c1c10a070003959907507140701d4649121000340491518000769007000340c4001016046403c4c50262070100100d6403ca0714000000801d44600040d2550b29409000c4464201401901c40480e298440348040d00100300d00c0c8203c0300041180e084079210b02d10b2208910800708102c00d8a4102e0301d504601c1c11100307580000b4495000b4818021a10401c40854010b042c003100c07450300b13803501 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 505055971 1250 505054721 505054727
    0xc0909010b040b04030b07050d09050c0a06110d0503180109061b0810090e0307060501090605090c0f090405130f050a0201020d020705030304090f06080312060316030f0b07091802120702012703 84
    0x5549c1d180c160b0079040c142c4c0707007040000020f50501d02550842d40c000c815a00c4043c12101c041d8100000040343d80420207000300140a440256080314400141e20401660403030182e082d502014011200c0b103542e441c030b000002030901140301045c000ca10700a040c0b0706102c040c0074003240c0d80340100c54840c0c0c1d455900751483d007410821580303002c0c1e00c17050a010f41c3da584c03d2104010300080c82040e0080107044000b8042c010064120f5003019901c69149003040d078104144801808010b098200c0018240c9251012031a0140c0c3e104286100d14010400c18040c0d00c002403c2529400000c070942d48031880a000613980071041c0c409490504400203082020882d0000140c40c80e64806401404005056210b80c5035016250f07114000640c01c0390071000400300c6403240e800440c4005442d08401400c52000124400b480382c1d04518030f1324111500d10b46504410b8074001c1e181c200d4440507070340099025021400044003961101d200c0c0020015058602c14070940c0440c02038145140c4c0e0b190503070310b008040c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 505057221 1250 505055971 505055977
    0x60807110c0f0631050303040305060a02071b1401021b030d0c06061d150306061018230108091c11070b04030c05011d1c060b04050c0909010b040b04030b0705 69
    0x11301c44904414010515440c080c903070700101c040c01c010340024800414141000011242280d52000080506503100740449000750004941142c501c1da02d45220400c0048071944000039110040392502480c10f402e0001e4901140141c44048039007650490781541c0da80852403010007400c40c14240c0c40100145403075002010a0b40101007503100d00d000510a0340c01c00c0000301c0c41455910204036641c006401051b03a54503040b00c49650054003c4940211117101e445a80c0808160360307041ca5501362550410340d00c2640741005030724a98900181201c00e07681c40200144c20680c1c0e0f1001e44612140703007008041c80e45241e03000c0b5044c03000f40c10b40c074a4419000c210810040050030f01d000d440340d1f22803401c98501d000b2231182c203002603e00e030042604c0303c080d00f03051440e14000410140c11900303c15400211155a01070950707034644d903402041903603111800303143e200c1c9904c2145255103281003010400400d0068020000c44a020300050014640000c100d5080e01c4e00300105080541c0e03101030032507040c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 505058471 1250 505057221 505057237
    0x12030209010c061d060708010308031306090c03080a03061a0d1104090c05030117010c1220030f01050405011a0306010302090d1b0f150c0602070f0c0b0301060807110c0f06 75
    0x903240c803413803c403603d44614031040013000100550301c603512190720840d0101c1083c0005040300700208082905209696030503400e0034864603020607102c07400d49a400890025a01c160b400d45070000f25010001d52510848015010311283d0000c150a65034003460b05000f41c40c05803501503a114803112070680e0005c05d840080075080b40c14003402c1d4400342d0042c0950020312510701c40200c14404503040c26018050036000f40960b560f003a914881b5100005e01400b036030320f484d80c0c0020340001404105c00b0200010340c850507202d000407805500d40024041200d00c1640000302d4801c040010908003908041221741001d403d28015864002560000d1450b02c840480200034542d102d919034249040000d80c041120041107400040a940b8002800341d28170004102c000200c2080a950000720b50f580a0095680a0400c41441c44242d50765a85460003e4002240401002c0300400c843e690004c2e1031644241540352032000c200c100c10b0081d40d1a16030014081c4940200c1501f80207d403070f517905482982d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 505059721 1250 505058471 505058483
    0x12150212090a050c04020711010f03020c010c0206060a1505030a0e0c120f101505011413120c050102070302010503060913080310050a15020307030f0e1005210412030209010c 76
    0x181c00c000100300d40d41c0641071011615402840c2901d00a480d01d8400d88094580100c0b1000364420030380c0044540c24407001c10801072650078000c0c400c503800248038480702e40a2a4008064a080001c01c010110302e10781e10204400c540c0704146d804c0f10ba07101081c0c036003050654070f02080000c0c4103003680382041d03203a4030780300e8100c80b013801c9090160800146240f00004100e0542c0d190310780c0084a0000e94400310507014581d003940c4001c02c859441942003284180c0c100d0b00d12424000c0c4564240500d90143e4130280312550181010414025400c0e1303080c000308000d0004103105440c690001e011408001d1210b4444c070584000125558200803214003c59405000282c1c2c918000a84000c1540e650186a020b69030300c803000704060090170100303280c00149030029421701e511554105c8420728141000e034108070940c4080f02d09920384180b01d14428410351100b60b2140d80c0c840040b0300548001540c803901c4c3c260072050001054085c83c0d84550f0400c40c0c540135989504810041e00e850018940007090 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 505060971 1250 505059721 505059757
    0xb0a0c0f02040f060306050619061119050304032d060b04021e0c1002090315100b070507092d0209030a0b0a020705070605070c060f2015060109121502 66
    0x2a090444e4072480c19684945401c010307603182c040034400d03030003080849500451403252080c08018050b0340c050a50000c00022034001000c0314041d03000e291034000d0101da40c1e51020400740108a14008040522a0500c1c4800b00c0000c150038043c1001103840005072800b640c1e40405c1d001c0e074445404a4448010045585d040300000c0000300290f94031a403070302903160080c03501a100040d0603000b10b41000d603000703006010540312100c86515000d0301901c040c940c0c1c00181130000d41141500003400c0007600690250003114a800c0c0c520040d9180240c3c400413140031200c40807072503004902d2625841040350340041c3c480079080c000c00e10300303842104050101158982086440140d6800070851180700b00144c580265403070f04262010b0040c1d0f440107044840d4803209204561003001090090301c1d0302d2a00c0800d064642540c007120040d103070f042e1050b907000700d882200e60078500d00107035810180c207280051059292440201c5070301001c07000200990b0220300074500030030680e010346081c40c281f000700c0c1e10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 505062221 1250 505060971 505060991
    0x9070519020a05010612150b04090c030318060f02150a0621020a09020906030406020f1e090a0b04080709020d110418050c040e1302181e0604060b0a0c0f0204 69
    0x5aa034080490443e107030340c244580881c18607642507407146c03840d41c012988400a480000010060074040100f55000380e601d01d0001c0c080380300c21035900b0003103029441e0304c07203071564450895080e04c1064002e041803100c0101100352040c0d00243c814012240d1318034901d55034550701c40c1c11016210b00d038001062494001e2001e052201111050000d09208540c070040b900c1d03403003c0035070980c02240140c990181d828000580461032940042c074001c48a1003000d0314054441030030b60390060718020100b864160101d40030304c05003044241540902513010b161030030b151502e240140d55501a00603051a25004241d101003424150800d0000c24a004901510b468035010075025200c600c08e45101781a00304800700760b1540c018002c403000d4030007040c02c0c400d503690780c010040714807624084100e81094070754000e00440e805507a8180e000f246803404101000082091420101d8005003c4501c201e14150013040081c400e0012035111401c00d0402c2c04040d800c60500000015000c00003940181c20070352004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 505063471 1250 505062221 505062223
    0x20105070b072321072c0306010f0e0906040b180f0f15070305011d062e0f021501030f080d0c0e1f090311060d06030b06030c010c0b060907051902 64
    0x50b100320b03c1c402c2d00007054444504140490130550f002c1000c17801d015060090040b00218000c10f0000c081e0b02e20041464141c040391520310268054696408003050520640c64000d003c075070090003a800401142c1025142c42800349400f41014040c0a41264a240d60203024032000461100c254280c411500c515004503071503044400d410320401444400050500f402445280c0c1680c44400143e990258a10141410420003408250340020010100320b039141001442e050200384c2081c8401e04064080c1d4081d0001840540c00d100350341100b00c1c04000d040044241a0459801141c603100500c0c1d203041080c1c6074402c2e0807840d070340c060034000344101c440e401c2002684219000e4550600600c06134019040096402550100040b18010100049919031315207683ca428010320b410728290503006018100d401c02d510440e4a003a241d4200441441d0030300004503100d00a080440c1c848100e036480008000340101424403c04880d0007150040d0f120740c1c15169140095160720325100c20201001e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 505064721 1250 505063471 505063477
    0x70b28060b0310080a03020a061d010e07030c080a11134703030a0e0613080a1209180f090c060c1103120d0f020f1615020403020105070b0723 62
    0x1190045240f101c00061030480043e151310700d1501680600310101032565101d02a220450a2110000c038600c20581401401e21480c260341004000804a0b44c0c9185051003100527603070f220500d15040301e0700c40700200340c40315041d01140c03404551401c81040d48100d04002002100c5401c00b0304640350b05440b01c0100000940e031800d240da055844041d560160418110100c0f803082540c142c4c0007071251400441c080c0e1182855002c008104034208030000c510200c40c0b40c0a6480030541c0d40c00392000805201040700c01050000a61420712411400c0401c5015088070300c48500d55800d583d03120602a4100756030001c6141d503803000e003050035150341c0c0600901d00158200c0c2130700e00814402603e100d038a00010b510311101c4482d81503d00f411485030004000313005200c01940c2c1c181d000c100c1581c0800500c2e004060302c0464124a017030301c09050401070070504024070341d01c12581c4100004c2c000b503038004068842c1c06a0040c92280699900306c1c084031a42420754510201d003d0888074400844800000303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 505065971 1250 505064721 505064731
    0x8090319141005011d09010b030d0201090c090203010b0906030a150e07020d030e06060f0111030a02150c070b0103120c0606090c14040510140f0c16080102070b28060b03 74
    0x11075100d00c03080040303002101d0f000c3c0b2a1544a55141094684850f00c00110542c0000c0c0c68000140304c0c4c44460101b403c6c01751028003900141d545461100811100445010103401400c504508544c1030000356501845411070040c4a9103000c03000440c1c006a64111030190a0544050409190f844c0303032491080070280e4220300940503040d440700ca410b100e0f1003a00d014010b258020811516014140314142400740b01c0c050401c501c03080c2d20b82040c2c03c10001066022041c1d4000d0405800741922610b0501c800b4100c40041c01d000c20051001c19041416030781541c1e01b00c103005800c103001160030744208044c41e80061002d4144100013030b40040740c0e8881000c1203107607240c81c812032214042412080c40740d801203c1d4004405407a180c0c0e003074404c0c2c1e298014003451a008500d8a00c04840c04465508a50304403052a842007400400040c59580c0c034000405d5018000c0d400c0c81801d9072110740618000340300100340c61818241c0101502c01c11907102541c0001c1d0401c01c8010344440311501c5603801115 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 505067221 1250 505065971 505065973
    0xc0c073f020d12051e0406080906070c08032508060405060420090f0a090608070e070f0e0a091503200105031504061502030703080718030809031914 65
    0x114081400c05504685455004020300444111595210000040c54082200304030050045101c0e1500c2c11041024040e409155951541e1074000d0080c4140300081207984030360800c0c3c05002d501504103140d0702c030140d4444e142a88035035800d9040ca4024004280f0b12424440800040f20610b0300249843e0081c5020b8805100075510001880151034012400140f900c4000d680c66040300241800303410044401040500c2c1448030b90002044d022054000c9804241c2d1403008002c400310800c40f080061814a200c46c0d0a0b00e0300107809044c1c8200400440140586039070680710681c2d50f0103d001c0940000e1000b0040c111054251010700815400103c40700c006c40d5400400c1076040b41c600c0040c0c0c01c0169262461076568040c8051524182c0b43d45540098030313002e02280c050000030081c10321342226801584c039888541402415800d010b4420340c00d0091001c1c1c01075040c01600d0480040d039400541c0280e44012410109140860f82d208813507204c040b0000100400904469010304260104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 505068471 1250 505067221 505067309
    0x30b0a1701050705041503090c03171206031b270702100f09080304020130020a0e01030e190512031f1e03110d0506010303020c0406080c090c0c07 64
    0x10058607507119501840011500c2d00c00b01403030082c4260081c400c400c0c80780c65010702751039403692105108051180300001e0018081a500201c0c80d00d02c402c264000c008034010460b1a40e0050500141210030f42c3c128003a21007003503900303044030080781c018440f03a10071014050249480e500003511034004082c81d251180c03c0000c641e0182607035000d14841c854110b103800d0b14544881d401564001054190081e0031400c1300c000040007070b8460034810f03100005800269544002100013841d540d0001d900700d041c14070f0011032404a0b1400900b00104001301e030b011040003102400c243c0c1ca8a00010804102d5800010800a601c1800f90040c00024415022981001e40b03500c46142d0380d1a0510389000302408016040002c5042d06801700a0400040c0c03208084080c90f88030a81028426041075003d68803100c0c01d8006400d140c8154802010318078050203c0c0d10203070001443c048806800c0120b0a40049050312100030248a40d000a202d0138070181c4805500d800304c00605a81920241e518105030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 505069721 1250 505068471 505068481
    0xf06020415090f261b0108060405040507030611091908070506030910021b01020d0507080a0c0824100804020102010f0606121508030a090906090b150307030b0a170105 73
    0x207410002c1070361608400c410403035007490038000c0c4141104680081c000350119482080900510202070307000b0304040c030a451040680009081d01c500030306120700503032803c0704210114070301240307a03002d903980320f1008521404038019180e41c90181c00c1030070358032080d0348043e45c8a00302581c009100700d880d8181550350442d41d034400c0010f9404100d0301010740d5042485940d411102035030051100c21001c549030440c440804003070340c2c01c81e0090b00b98468140c0e0340b40c00707103c0090707000141c16900c000316a0003030107402c8020b00020419000070305020700c0e081c241603c80c00c00b4241c00d880c90034a200b010b441880d46552081c40100600700c15241a80954a40340348400d241d895030040324103440031070321070200042004130302c00000d0544403410b100d80303150000003042c039001c00c0c0014114081184d54500c80603080c030b0800d4003125401d0348801030807460201145600d44940b071041c3c62408409040c1d43e10f0743d50300103080d0b002e84544103c840c0d2004e40d4150208144e595000782c0100030200380004c10440c0e0315 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 505070971 1250 505069721 505069727
    0xf090105040f03140d060b0c0f0d02071e08010905030d18030e0f0102120a030603140303011401050708040b0409051f03051009110a060c021f0503040209130f06020415 73
    0xc2601d018001d10800040703000800c0c003403052220883e5070040c071036241a900c0550b400c01c0310000d40149284a100059400340f4040c1082000340ca203180601034180401d280d840a56544003034407e02055131022580c02c100303d103000e45a0801030241d00700a010045052070140d8896122012400220345081000f8555069410342948000e5040c1c9984446500260403c60018000303100d040c118820030310504c0c42200301402412502c2013549021682505500d1315105070001c1c0c0c4003201850703001b4801003024254072840140070302000c0c03d01070345d00d2260b0f0034640340354450768010b001c00300e20016001030103100710b5014a2090000c080344000340000700850101010851002a10541c48005d01a03130509103030744200b812521681d0b4440c42c1c800d1002c00f007903080f90140d00030390104c1d00c244401d0040d4106102c170030442c003504844000d804800311601500b01c1c04080c202900481d0403d0009008d00c3c0300149040c02a5040344c1080c418070030f1841c05d1030107540305014a40c401400b1040910035180 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 505072221 1250 505070971 505070981
    0x19063c03020f090a09063e0d0c0c050106120b06060702012c030105010f0603061a0a0c1a040f06062c040c0e04030914012105070203040f08060f0901 65
    0x90300502c201d09203610b040c10032a03012409051400d00641d05d04002000402e24411288000f1000c40c150004d0b00303c4900d600c0e03640701c1c00c41701c2c40c8215a40344026650810706004039a40103184240003d0111600e401c106e910030600c0070010400e40c0780402c0420590001003d91401a2040398424040d40c2e03240e09001c1503010b003104c0207010a44100604c851186601c0c0b41d10740401350a200300220385145000607003918404e074081100c10350407203030500c60140c0c50302546019018110036112107510220403050759124001c000010803411000070300400c01e1006402d50f13800070540750141c150170a400c2a65000d1f001202c1180d4441c581400001c0484000140b182000c01c100c0c40c2c2801202c1d0503060310945200100102c410304aa24804a036800084446900442c0a0740d201c480e171a09242c5800d501112400d411414004104001384206034812081d030361340340150f07101060720380b5540c03026031540c011a0841112009580c0e000300702104002040b038442e4252442d0704481c2c0d16040e840d503007261 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 505073471 1250 505072221 505072223
    0x13030c150905010e240703110f01021303110a0e071d040501050a060507021c03211a01030207060b04020d0b0301110a08060d030905040f020909160819063c03 69
    0x10713011810716042c61810140c05140d008110040c441034004403c014401680040d00460100da05d41c5a074400c030030810009040c410705d45000131890041e201c6a030f942aa0300c5448001c1c4035510640c4140016151200faa1000784180c907101080c03406e264001501c00150240710b040c0519400d88100da50780742c94041c0904030b070030140840b4091414480200c03180c0e48075540503038004141c0c0e0b0341100036030380c580080d0000b18001c2d0359044880402c5950f14521214842200b001c65091101c2000e0b014140503229099401c2400c0041c0d9440e003901e4090040c00c08082c5043d4881d1011442404400b60307600007010780d090403002042003094010310103100e8007400e081b06000030220b400040d8503003490010700a00342d002e4100365000640c1c07800003030142e400c464400780d0201e80100b090816400c0448510390030074030400c4c110490b443c0b491801010080001d0455000301c5101d03039084028480d59200d0360281c0511842103003902c074080581000b0503501501085445c030304451690503001d00c44915000d40e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 505074721 1250 505073471 505073477
    0xc020606180c0c03090d0b061503040210050c0c03060106200613140708010203010b1216142209021b060712020a0e04090b0402150c0a0204090813030c15090501 70
    0x207840300b1a82c01c50359003000c014a00385100030413003001030b580c6400e509440e080c8204012009482c1030000d0200c00c5204000480d4411000c0c01444010384c5d40c0c155000b95a0098a0500d0f00c800303070041400c0c50400304150503501805004000304155500c0010783c1d51140300750301c0e0316035606202900f640e6204030807284c0e1000008494079401c00100c156200f100d50300b015900311102c00752074940c205e08a900130f0380100c50611000620201e0002c03138180083d4003480c0c07403854610034000054054806441d402c8001400d0324000b0715460710000b5540808000201107154000075601c0f02d20600082d80b240d1940c616510411010120000307002030010311515940d0340b003005c2c271006046820080d4025030780384018000203035000030098545102d0992014090000a041070429005001c1ca08484a00c03840e201502040104413010000401e14490b541c15180080c0251080c00e0194480c0558140740c0003040000000000f4440c3c1e0074003101c00c0d2070b00206503030780807508902e0039690a01c41d84030b0503000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 505075971 1250 505074721 505074769
    0x3080606040320060f03130c05010309030f0804050f0a08070b0108010e100903030f05091006050604060504120c08060c0310080c1003050601120f091a010522090606090c020606 77
    0x111106103000003c001c8007420941c10500829958200c2c2d4008a842542903c8010011014050a014000020b040c01c1c00d04000502a03618010b0000012545401c00c0c0000c210104040260400c010042140c1100c16280c02505503d8110a079903c0420299240300c58400040b4160b0018803802913841c0c12072000700a581c080f48601c03405015a84010344c103141d0b0300d0010000082960289910825a1b1406048082c0e00c121101c000c42d0303015002540922424003040c040c05802c9812541a20425440d0414000340d900e854403000190350030a5411b03000b140d080c400c5000582d03014500a008814501802c15151000310340d440071100b55881d840b02c00c9503401384005000341d0013590031900600d000c540b000040c11703014098a108805d04840d1941d941f0b00e0000b404800720101c481c400c40d02803000c8043d4580000a8a640900310b900c0041101ca10f4840c2d81c002c010b98800d00c0c100341d000f4070902c04940d903200d00e20000c00504000c4405405907000203401c40c139121400c001143c0e040425601 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 505077221 1250 505075971 505076003
    0xc08010b0325050903070f030201021b0a1707050a0603090b090a030c111c050d021506101b060e07090c0503040c0608060102030f0d0e07150215190513030806060403 72
    0x60141030451407081400803c000011542c0c07814401b81010303103140c0c901c40307001908d07510009103800d0482d48003542d004c03190000d0307100b20303982c844c60f080c2210040c0843c0501e4128147c4054186100c50344400e0340910f28103800101c6640540018540c14011121100d55643d480002074544032100c7c0000c0001d22440c4400b00007861584007842d039004080c000c04c0c01c03410050500029134900c0b0100759182e074001e010000030543c0c100030114024608035070804035402c1902c0400c51103604446200184a94071010402c050300c20000c0324981e0f508641c052000480e114001d58603034209009080a29007040c4603000c071039000e0b000300c0b4029a80120704640192600c039027240c602001401072411400304001c2e000810728404054004072026180009809000720030880c9465040d50217210300d1503244034401c0010350086400c140d509600c40d0040150382e00e8003070001c00ca0300c020083c00c6c51240f80206000004070003110410344d5510a0300d4624035a2034410800a0600403440000c00040c40380350492 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 505078471 1250 505077221 505077271
    0x3050d050304051011040308030a14060102160308030a0209030307030c0611090108271509011506050d020d0b1f020d0504080a0f02060f0304050609070b2502150d0c08010b03 76
    0x140c074003d285c00d06410301c3e482c1d80e5404169031098a03005074464640c506003198604a50301150400406d00041c691700100745204c120503803031480064445203001c80090103021194040b190021001401d4999a00382464040c0c00d104031203a0540b4280d11308103007043c15544000485050031016102c0f403030550341341c1d0000d400e001080c080003500c4403102c241e0f00d0110f0301f040059a10f444a80c000d107081a1414410260071562001511300c00300060b1082000300b213400000701d801c5a41901009a61107040040c4d1030081d02001c00c0d0243c220b09407071032250951303580013001610064554299100e04130014401c41e0203001c0c9000d00c2449401034442c21001500380c0c801c0001a034801360810f800c0038030000016149400440741540e2070f0300000c080000c0f4020610a05001e01038881d241820841001c500302ca600c050a80c04002c0d48940c84817840c00d55460a65000c2c10b540c84118850380c440b50b900c4080042c00410321100d0100305100b0020407440302d5401980d1080465500c02d078009014501c6403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 505079721 1250 505078471 505078481
    0x100f180f0b070c030b180609070e0f18100f0b01020c10030c02150c0415140d0504020f0a090606030f0905060601260a09030807111c200703050d0503040510 68
    0x84503941c94401c0000001007001c4c8070144640c0c6c2e500c4412000d01a01080f407410b0400090100701e141c1c20411060101010142d0020340004d50343c60f154a8603900d5132005200e0100c036100c41f1109220780c500c1d003000c4d004943c0103825014a0b00c60140510132010006a0f80e50320042008c030340c03102c0d04040c044021803180d44503500c42da20074030495050000d4000c0c1d9140780001030b0340c07100c050200014180044441d1b07803051400d90883e4940018480d165204007030f541d000784944070240980b19404941507542e0604220300c440f80040244c000365940e00c080303100401252250341c000c04c0c100041c41200000b540b1542e1412a0450301070301c625900c4100449104860802900e2050041625a014081c40c05181ca100380c281840008965a003801c2c007500d180340050643e801c10020040c02c2241d0900803d8131425034520310900e0f04c9843c000e15080d525001505080e284040c00010980f18403640001c82008490140040e02c00d140f400c3c08084600384011107014040794400000c80d01104525800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 505080971 1250 505079721 505079723
    0xb0a0819120e1c020a0503060c07170909090106060809150c2d070201020712020d1202010e03160c060c03050f030702030412030329010c0209090705100f180f0b07 71
    0x60390040d190040000c48000302e0781905002d1a122200303d00840c10800705290240c84100e008110794a0540b15000140c419500b00030040400382002e2159203e03c5000d540500300c005010501c64600400450300a05561043e000000d20795004104644e8000c01c103400221540c0000508a40d00d08260091950102d405a0045140b400042200c0750040c5800000f451001d40b020b559003603640002403410f042c1b90041c406204020720f21030300594500f560700318103aa00104031100300c03250f42c7c1c040e80100040020702101d80400070301041a640a00510700c11030f8400d0040c4402d2039141c0108a88400540d0001070104504100072484842c3e2980550791020151040b6460140c1340e4030500c1c1a011480c0f41180482c0d1155206030320440c02c450381038180082c86003a8044d0504280c002001c94000c2040a4010000d040129481c25800d01100e400350030040c2005c548070034030f414010020914002a400014172405081640005a03904607007100c03640900300440030704100c802c100315848428 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 505082221 1250 505080971 505080977
    0xc060a0c0303090c0b0a0512070525060906020f0903070801110a2a031e03090803010b090a0f0b040501170106021e0f0709021305010507020a06030b030307060207060b0a081912 77
    0x30300245c2002c480e0002c20240300c403580d40c55210580201e54a40b44407015020f1420f0050900203000d01c1038a08806000056541c0790701240c51045080540007490ba0b01c1d005404140009000707400352281c4401480c41d004d0a8049441c11559105041c0c2202e9074200c0c2210f400b64104488100c1510a2505103407010141900c2c1c0c00c1810040d50503030107001040003ca0208500c042c0245040740c0c00f00600891625508081c001440c1c5030341e882d80d461205000c0c2c10400000450300d0030440d141e04030b088005d0840701303104003d01921040140070720b800c18403074240001c0342c0140f07002001011000c0c0754101e49031074004101c0800e840000078103107492400c0000762889002054503124904100b041c1c01040c80520040c1d5502000900383e07d2942c0700d07040a4184080ac0001600503111000100c0c22101ea502d4001200f11500d4006401c42c418030740c000d400d090010405106200c0303107034008041c12108590341c0c030542e640c44035495240c2c1001c840401202154400c60f80208401e400c000314112551301d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 505083471 1250 505082221 505082243
    0x60504020102120705010c1416232b050c07030b04171314010f0e060c03040b0c0601061b0503031801150e01091505031c030207021c050c060a0c030309 66
    0x1070311000098204c600305a605a440702c0b01c04003c141c02849010b92150460801c42c900b45628000400a01490b40c0051100408100c1c5900442e50002100a40c100300d80a80c1ea803001504540300b400b8a105a001c40325051015010b03000b6401801100c041044d88400b0301036441c655143c0c0c038161000140140c8491010f0601000041d50840051201860540282107120b060650000340521440c0b0000c0c140f041561000c00c00302d401c681c02c006e41660448190f503640c140c0c8441e41d400c40c0581d0340702440d603450104141401600c0420514140c640c2503030b80600c000341b1107505016a00030640050600d03001000031a50804030f1240f40035640706001c001088a998001c1c0b0344685452582c418000030b20004010b10800001c1d010f2b001c1440142c00454403040c0c2054000380e11198bd20230701075001501c0c481401c41850081d01504c05080c5c0041000302044680800b807002000d4089045600d40901c1180206c07030718000f0165501e845d15a954480d2344112a0740c190f00404100605941c0b8035041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 505084721 1250 505083471 505083493
    0x1050904090b100b09060d09170c031b03120105062110140a062a0b010b0c25090b031203010603090c080d0f050f0903070801020408101404060504020102 67
    0xe02800e401c1a11404110485142081c0303401d000040f15044508102020041c000081d510001510844154820b00003603415240c6410032042030001003034141d0000100e45510341000c040003501803410030800171040d903102e0070f003425124416441820040450345005000324100030020308403c0790118450300c107a00e440d0200350711010040720303202a41040e8080501000503801c0a1290025080e03695240790350030038a0191129070302103084040c0c6042d075681c01e403e60b800c400310000515001541d48000d56109c03029000b00d0b9200e040300000d207100c1c13462280040c0c0d00300c040300400e20056612480ca49420200050f014112504c800c0754144120094108103c0c0c0010056000380344544000412441c0c510780a04c80c00c6181d4050790058000f180007080c010340294594140b14501d1801c80c0ea02c40300100015018000d040c4201e815116140000c518064154000c1058605400894105801c9084010142e803556072100e02c150020802040000340d070781e080941c0061050068888601503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 505085971 1250 505084721 505084729
    0x20303150d240c1706040c021002030703090b0106050c0c040b060409061409180a0f0c031218150c02060c070e0c03060f120d0c0c080a0303020c06060306091209010509 73
    0x782840481d80b410751020410030b510300c00d4180f9000d0508181d203980e1141955854810001405a402075840700d2983c45418420f100540c02d500c403441003107480c5c2c18103410040060404c08400c841d602c540c000041021030041c01600d14001500c00181240c00c10102408090040c0040e0550482418480420407088038005c080c05003039000c240e044103428003420850190400340140701591094801184070050101c2c400300c080b0740043d41c0030240200c900e00200d42c40700c20390002c2c004e40c241d40700c03440361185c0c480d034603001600440e800d44100d503448040c00607111055000400c04510301c5103200c4018241a006405601a104c4c1680d442c2d41d81c0d20385e203a609100031108a46803100010410500b80382c10751800301041408e851100b140072080491a5584c8008104001441010100903080102c40a11705010b443c4500075124200424640038010f900402c41947c080e000380300000301c6071304000a0243c4208020b074000c1c41c118540107040f0341e5592001c2d9400b130400c0030802c400102500c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 505087221 1250 505085971 505085993
    0x9030307030203030603010f0b060d020901050f0301062006010501170604060b041215090f020d0c05120f07080606100807090b04060f11010b13021303140607140a020303150d 76
    0x100a401466407407074401704050131281c19041d16650980b43c01c00c416450748440003560b884034108040181d58910103001a1404d000c4ca16903c0350350400040040b804503070080c44c28840c0001004000640e07003103c244552110000d029103400604681c10081c00f902200340080e401180242001170b1281d01c1381c1c81c0d00c190341c0c8980c02041c1410000e42415080042003441c0401c140e8a0714000c010340100e566030003101c0012460b02034850940300d8003400c184944001c641d00107000040c0102c0000c2c1140c400d01ea00d039005522800141d0107a1000001c2c0d101d0b002c100c1c14404c1d0310043c082e0f000410844010349040d04081c000b20200404100d01140c80403202004001030a400e4949070701c900d00d005d0000b46410b20480005c05a80d04081d001011502c0c0c040000c0e0801210b12000760711800d0381c5440003041c040b070350700240074074806001042c6401e00c0031a520b8012040756903511034012a00064007070600ca280ca007180142c0c41000068501c0394003042d4a841114010b0030500c000c8003985904007505 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 505088471 1250 505087221 505087223
    0x5010807030c0e01080606040e0f01051612020f0906072f1527010c05060a0506030f0609150604090210030e0f01090807140a080309011b080c0a0c030509030307 70
    0x80d010010500c140121191514010440140902000c2d814248059219180542994003e0313480e190014400f44060110b86080e44005000304058980001c40190220307203041b190700420108115140b1031010790086400d00003100e00c0207840d00c076841007405484d80c84080c054a91081260103450741040b620514800500c9100c10701001e1074100040024601422500c049407000402442c485903030300c241141100c60003480c4a000d0000d1000050790755039104100101540035810070030161550b250300003401410283e00f1184207001420185036101d13410b580c05c00c0203500c210082c65101c1c02c15060941c3c0000083d0000c1003601095004c00c1d44a52042483c0e00800d45501032070b159035008200546914440000a0120000e240c80d0314900344204000a048040c00e0442c0345d20036070041040301350455100c50225036910389201d00358000c000300414030542e258640d400c83c030707060702c6100e40744d02407040d60f119189040030f1030a080c1c2d5041c01c41c0304100c050140038040c4160558050024002c80303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 505089721 1250 505088471 505088473
    0x406120c0312030c02190c33020d090e0c040b0c0f010f0605150d0b1c030201060b090901170f0f0d0201060b0307020a080d0b0a0b07020f0f03030a0309020f0301050108 73
    0x40741180307040a1251019940d00c0105440c00c214a5180d80d4001b802800819152124000071280750400349001c0700e40d80c20054080c52003407030041c442c4501d4081046038022400c55100b00c0e6400b040c040740c84418000003440006c110070800d0080607194208950410a401d4110f0304c2c107603a40b041401d864005d0791001d00190091144110030b0182801030400032000490100402820007000545040c0807074100886e1520101c3c0807203100351145d00c0301500020050905040b4541100c4904a03190803541c101c0c010350030b0010000300c01200a00b0307a0f940780c00c01010070885a0a095010b80e4075074000089200620402c406070f80307644014045840d03d00340b0580a05070b0041e80d4800079095495991110403203c1e410005c100076141d01107620702541d5403143e02240c0d00e40c0034107200030242c1013456884d07030b010191030400100f56201000a040ca90300c2501ca41804408520130006810740d101c103005e800d60400c1142040701c40c0b00b94011048036200a055510091902c0d0209007150400d070802126 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 505090971 1250 505089721 505089743
    0x72a12080a021903020423060a0f050909100f06031a010f0e04140a1503050a11030f06090604030815030a0b0709090f020a02011103090c040c121401050109080d021b040612 75
    0x440261035100b11f4100136140b9a1072078854600707010035014810540c4d59802c00112020fa040e0140c800c41c2180e40400c0014030303410741401e00c00340c00c1c0d124407414818280c1c10b04443c0400500c1900034044d811000600002003001c980781d00d00152001d580010f0200208400e10902141c0c84d5100d104030840400c020102c0b10542c82c013400e42c4d80440b51000d2140b13180340341000c010000118001401d41d40d00c0d90200314071181c60300341e00c0802c0c41c2c20101c0f5050700090044108001c030450f0300040395071246000b40c1e1003124a03124000d500010074801c0c0d80e29605500b25020520108004290b130b0307a0005132516008010326583c250f07600460741a680c0c1200c190b5000112840101c0e13090090000c0e40e07101c454481e00d0b41c1130141c0341d03583e56529010344500513520f4071311140380f09010704c1c050000d44594500078800d8500d81d503005012090240a0580801d040c140045284080001c1010030003035103030010722001d196112100d0380304d070103200b4250f4056100c090116000203000c40034418544200c080c030300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 505092221 1250 505090971 505090979
    0x60e0f06010e0102280516060c110d11091b07030314160801030b04020607021201020a141c0506030c0a06020703060f110405120a020603072a12080a0219030204 70
    0x140c0b031000d01241198070074100303450714011030710000f5400c40013041407444100c07a0b0310f030441c1001304441c482c0400260700840000c00030b40060400040310720881421807c0344d0541c00b084030100e4101c00203002c40c00e044414000a01380004000c7c1c021301c42556040d40040941e40b255a9503200480403000603845800320300304842420300c12a0400008450320b040b10f0b400700001001144144406042c0c00300a50201d010354407404121003565401070003001c070185108000e54040c0d40102c03800d400140400004000c03600c003100603601c9409003079141071a103400c07482242d805402c019042c81d40c103000341403051007244e82d4900610002e001a8018007081e178514100706080b2002032003a40303211030900c54110328200c0f280b4201c0301a44c2c0112021290803400c940850315140e82410001e400180c000180b01c4541d8008082c1a484a40c1100380c1034501c2c2c4011102518807005203008101807030121000390f0f0b850140750660340c0800400c000600381340c0624130700445040007040c040c0119a000038184 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 505093471 1250 505092221 505092227
    0xa0507060e0a1a03063318090106020c0402130509010e18030405101d0d08040f08011e0917070804050901051c060515030303040501141e070f03060e0f0601 68
    0x140500803581c1c82e0b0303040c8101441541d04c401014107201c1c1840d11140c1d82c101500306a4042ca100b0103200b582c070600c1d540d2800c035485600240c1090003d0024209021252526a84c41da050700d4095010701454000d100512019402c141c196510f0a00300d044c0101300d6485c0c49107054028540c481041815080000c00910301c0d5101c2c0c0b80e00010743d0001c21052140f9104c0040321943c08a041c079060341d0411038070480710f54914009241c9907000120a524406102025004d40f043e00d000ca41001c1c10785588007009030803958419050f14801340c54000c4c003d6a4001540301e2040d03d40100207007854800500414030481d0311140085590030800718050050b401d000c020b00c1d0251200303584005081440d0003501447d500c855030000d055a84482c0083c400805007107403100500d4010b01121346038103007442c00c03601808005518041070000c140c005400f02030192400e44603014070f030740340401c0c03619401c1c0c0c12100c42d004100c514080c55164203002581d030050342c840038859810b0140101050400744001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 505094721 1250 505093471 505093489
    0x30305010518070f171e060a0f03020906041d06090c0901050102060a271515030f0f0227060f12030f07170c03040311091e07020a0507060e 61
    0x80c9000e100c00b64401900c0e450300c000865040510340c1411560b00d0070603001260100c108401e408115982070003403000250510b00502000d00d60b100d42c000c4d0541c1c0340310602c03110a07030703a100300c0030b003803001041c20005400c2030b121240e0003480107000425050021001900510400010070304194098400c00614150510050005990459940c550b551400380000c1d40c07148042c0c070100c000c95440c100d12500f0184806c0564060740c0401d00300c940400c050400d04a910408900b6040c0c2c503040654090100d01c148942da01503d44c000a824048039540d00c03800c00c201e117000c1c0100c0c5c1202103501c0301003424986881901c280707003e0044882c02443d00c1401c1c40710760040002c00c0c9014445e02941d4544440e40401502c05e04491108080c1d11030955050000720a10b480440e00c103c460006091102200040000c0050301d0285c82a2050142c41c481030203428501210304130480724400d1040031420f43e4020031550041d01e244110307003501c1180d803102c1d0704086050384440e010925220032807030749007001c1c690 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 505095971 1250 505094721 505094729
    0x3050d08090d02030a0c080d14070f09080304150804080421140d0914010c020a0305070e1608043801050f0418110d0c0621050403020c06030a0b06030a020703030501 72
    0x44c5051200640740940850240c1e0802420b006e400305040e6803a00ca16030103911b40d104c0c550700041c41810711a001034004010f04a401000a000040124480400100720f4085405101e0241e000d10f4041e80c04552802001c1c104440e081c504210000c0c2c142072060010390711a00c501140321315500c40b880c0406411807944000381482d00000c05000b2010b0b00040400c04580742c0044840c43d403208040125161546100002e41c0000390b8580403050260000d080c106482e001c54402600d615140c82181cbc41c10400380000001450300341c00140003070f4104001c1c46154140441110005001003100560840c1a040d0011078983d00c1004010510b00381210f0030005100b40c804004040c3c02007102c000034074241d04040c00c4007000c424010319035110340c40031240c00340e0040c809a003050740300e100040c04090341c00c62001c49002485c0c5a850506880d104407070241c0c2d4035400601d0501460003d1100e29080104645146a6980c1d40b68190703440c0c420013036205070440e010050340c80c0c45515001d021940b041e08 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 505097221 1250 505095971 505095973
    0x41b030c15020d091703090301110306010306050d150209060702030a0b0a0b1c02060912030301080706140307022a030d090509100f09050a021b160902091509040603050d08090d02 78
    0x250803881c3c0754000c2c0200c001d40b4100107040c000300e00750180580c59031181d4500d540c0c040d841c2c040810003210500303014500400c400d82c0d060020750740d500308101511a05120150255450702240b6900c003095034020f20354241c02520b120f041281e9600060b0500035207440c1074480702040d104201e144402440703443c07007038101240c5281c607c0c0078030360340840d2003220404024002e1000281042c0b241e83c9520403020705098201c22244d0f41c1d030f100d186158495010b0721a4a0124098080562826043ca02070302d1069a45e80e00524500031541254038544040002101026180b030901590680742802030a08a2005e03460f944011490441881701403000141172245c2250016400d0014018452030901100d80c3c0030f0011404c1e45600c42d0340b43c024490f03582c030fa00c0354681c111014020401c000c94000c074040101e401459283e5901d1781c42030103034484d030542e650303100030500680309072180040301500c0c82941c0074000081898681e9941c0d803600903080014000b103644102044121141001032a2280660384 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 505098471 1250 505097221 505097233
    0x1020315060a05040303120603020613060f0c031d0a0308030109020c0601050d0816080f161a07020c011107090e0724020a03050d140103200301050103021305041b030c1502 75
    0x104002e003c0e024038000282040800000c4041c42e441c035800c4040510b800030566a607511a0101c0d0501140080c4111004103d40503074540041e4010b500002c90140c068079680116185803854106107144c09100c3d81c0d00c24503118011000c2002c04010f903010300840000140d0b0351142d1032a581c60034030160b004500c81c61403400d00d4000900d444041d07809101c41d4500755180c0c0549454a100705025000008100031b102181d69041144808401a44240981d10408441200314032002d06050b0407114400076a00500c91181554030032010b02d8a90440e91068401094031404003009694400c41900000ea20908040c030050b4038100e90a080c4005140c1c3c15180c3c0d0340841000f0b5101c000c000005030900c1008910100c1e1900b10307030410751400201345d20103000c560b10307403800c8421080c87c105000c1c40b0b60700f600728000440c03d0520800e0705a9030020302e0000700710903680d183c1003d888010422210181102d14104520480c2c40c0c180014512031000e10744403501b0515038404045d0b0b400e4920b811940a070b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 505099721 1250 505098471 505098487
    0xc0307080d0e030a050f0d0818070e150913170c121e0a031401050a1a03090a0b07020a030210051612060b0703030501050a050301061505030411120102031506 69
    0x2140c034229810790802e808001e14050019080c620401c401410718041e07074508400d00d040200351408000041d40b41e4012a446a00d41100d660329000b0a00d10654441c45d02401049a9841c0d80c5510400c0341044005041d12440407070440b1800380c550801d032a0194448200f004480f9101802003500d62a00038240035008800700d9440144810b04407511000041400d9208040706007040b00088000104c1e0340c946860b0030080c000e214209220008858010000c078151911360070501c100c407140d4100032407002004508030b0f450341c0701800c0c4800c02c2c85100c5c980400100c010559a216207820f8024028601240c20007a09007161300d410314104601d400c1c1000b501e4410b0801a10f2280424641036955034a1000080001c0840307800c544801c5401049000c10180e142d000603040c0c407010349401c0310070740c1d0b28002c0c9400c1c2d601c58014810603051114502a165110b2409190700600580486004400c40000700c0c03c0303440c0f50071803502165000000c0224003032241e204406d51078004d48501d8500410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 505100971 1250 505099721 505099723
    0xb0d060506041d15060a030b0c03060a050a06050d021308060403050c0606271b041202011b0b01031e02040501180e07030209060d050f01050a15060311040504090609050a0c080c030708 80
    0x13000380c0050502c210402203140c030b0311000154409140d000d040c5940d5420200304800403500201c1d50719115220b00c00c0d01054038203082034503c04a4042d9210f5500b032441c10781401c0e02940264202c1e003030104c0b00c00b000088590b010003070107009038001d4492aa8402c10f42000900701a0000d002d140a1000d0f40783c0e140d401a0740756a00070300000300c501498207907183c2c0c2900403e9004010742040c640c2c1804500814410950f0004690643c802d0306d80480880c44200403e029010000c000303000440365800400c003040022510005100e400e10200d040d0070507030b500040444d2420381140a95485000c10940c000c442803090400b507220010043c03c425145d82e00003074101c0e0000f40300c54051880020b01504102c81004000c41281c0004000e214030300d0722500030303001070080d41800140741e1601000062910b010384140314001c08a402c4d02d900e440d080c01e0500c0050304501744101d81a81d40c515542010440c103208400100348600080c2136245d250180c00361a03c0c0707078070400c01d102ea0080c2d4020030031408 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 505102221 1250 505100971 505100983
    0x130e0c1305010305150301050a1a0909030a08100e0103030f0e0303190e1305092b0c03030c090b16020924100318030908010606030506031b03010b0d060506041d 70
    0x582443c000c00c040d500c105140301c4014400d055a905503003441c060101207003540e0040c5c09400003040094207012100010000c074500203507a4003074203410401032020507a102760038660340060602c02948289940b00c104a4600300240d0081d0001928140c011195682c003143c143d841341c004030001c41c00c04001d605c4808c51345000120020600201d1141182640c88800308000704050802d0104020b14119030f18a8032011a942c3da10804c505900000d10142d45410404c45030200c1903032104141c4503281e030142c000380001d11000051180040c0002400b00840c0000c204a5021482c00080c19090744141f1254903005880304034980c024030b0b01c5504000c0304100407441c1990482d05080400c8100d9419401055409110b000c603083c40b0b0180780916810107d0f49041340c865000801520783d03240c004030119141510b0923541a000030020300b1545582c0c00280e075005100038000280c1410503c000382c0200740c0580100c4855447d40c04100b42c07854944104000301c8180303106070309250811040b658880c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 505103471 1250 505102221 505102229
    0x14030c0906190617060405070f11031b010c0215060f09041505071d150f07110907030e06010b13030f080c1e01150605042306130e0c13 59
    0x641050001d80d035561007a4100000000400d010314141e0744505000740154015900241e6666502d00401c5550400784101d901c00c480544d110249410380c28801c50301108800600c0d500c520013408030b00e03185000e241182d1000c000400001610b000c4030440a420328950315220306111182000300001a01c5840000c001c00108454102d10b950302d03880c03c1c82c144a0308584000e0320519000270403031050741111001001042035860000011410300400444086031003180c0c0b412a0103120303540020003200041d280c2c40384612001c420500c000c00200e120032074100c3e8100e000135190705240ca8001740c20701002d800341480c06060740c50044c000d00904640d00e00d6220007001201150403071014015503800343c031844800700c402d4840c03011103420107030741c60280407055040a5280961160318400200c2d25030f411140700d61140c07418585084000c01703840a090703141224500001003031707c0465030348600800c2540f030244550f11035103050142c1c0c01c51040005229411012007007040a800c8080401b2060231a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 505104721 1250 505103471 505103479
    0x1713081c021902040e0303091f0c050906070201171005040c030209330301030c030606140114030a15030807060e062229150f0604090b060705030307050d0614030c 71
    0x90b10403440424020036580f424070040f800040301f400f015035408030340745541000401e03458064180e02c2d00c140c030480d03601c0425080030841c2042009404d05042c8040c02c0e43c9401410035803004804599800e80140d022101e4000c04045404240480c0c0b0705482554251001443c00b14102480e03103011600620000c003801200c6034030402c1d034115800c1a0401ea440900c24900710603201d5a50f45803802148a60f40000c0350307083e09009020984110070030016080d81416501c03850804080000701c2c0540c0d00141100b116641c4900c0e0029821146805090055224010441e07583c48141854012030f240c400651111b40c10403c14042002c003114192582c000c4200410014010185440b0303407043d8a00f80c2c4080c201c0c04400f00400c009110000d19031240b4903c3c81004080f04142017005007401a0740f901c207a00c084184014045010300f640180d00c4e850001e0701282ca0401242c40d41c07031071600b00316481030000c0c0d000210720701070300380c1d501500b8005c00901c4100d0401c0808940082c3e111500d8600027402 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 505105971 1250 505104721 505104763
    0x61609030f0615090c090b120a410604050103030203040306051e04050d020d0e011d03070914161e0e0307180207051203041e1713081c02 60
    0x144202da0340800c44400000c00754042c03282d40d44400c44040c003c3d2075410408180f21b0a0002031004062084070700b4654100c1080d050350b542c05041c030b0300600d614841c0802010000503440c809058011032802c04400300203521001c103440505611801100401e400d01583c20100100000b030703000002d82d400d03694032000104444c2c0c0c420490754401c8505805070000e211440c030500090004c00300d00990700030b200d030b801d560290f02c003010113070b078040e2406051398001b50440c4911564004124140000254000e06841001e5503640e00b81c81920341f08c120246503515007005000307102c0030300284180d850382981400542401482144c00c941c40c4034000840521410300e9520000e5030302803140c0ea0280a208030707200240c0240103c4d6000940000368121224400e01407440d48004c04001075a210f903600c041c150458400d0400000305a403c1580c0803103a07203038041c14880003800b00078080c0025590f0301d21103a50041c904550b03240f8001542006e800b002044500c0b00c4010ba40c0412180078481c885005544 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 505107221 1250 505105971 505105973
    0x1e24050d0f08270306090c09071206050603010b0c0708060106020307080918040b0901060b0310140604090204090203041101030b030c0f01170103120e1804031407050f0a0302061609030f 81
    0x90600c18007400104810603c1075012540400d0341c51640944001e07030455803076999801900b070313603000c1c001325003603012000100148180c2c2c0320340c458416410700c2500c04039519a030b4102041864000780c102d914620380211740700708142400c010548c0107140440040c0419450a0070203034a034420607001400420000500c0c0020ba181d0075290403810840405c81c070340310b151a040007602e9040c113a9000b40c443d42040b0300003841d1228030013500d00603051a12240c2c0e005142c1144248080c46005940c0d4110000f4000003c01c00390030320160000300803400c40540c0c2c80c90145072008000f000c00c06003905140c034042000780c0350b071170015088400140a0b43d00340c402544100042e6040030303000d01400c41c4003000704004000c1258480401c0f07049101d6840301b01d0780c034816100300140e0900c851481c0d0b1401006100280c0031034810a846c1041210b8080300619021a50b2103480c2031100d0b2544c40d4000b944120804010558100001030b4002c2c0600803109022408040060a8020340e200c060894a05852a90 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 505108471 1250 505107221 505107233
    0x18061303020d1a0406380922060c141c1e0f0e070503070e1b0403080a020604120504140909100203010f0312020a0b0112061e24050d0f 59
    0x2020007a081000c8120780307445e180801c050015514011040d5044041083c1ca1806000c402c1001c1080e0884143d20183c158003032001c02c5000411414500d20101240c4000c00a601c1d0328204040c01958080354001c00c528014040200980c40c0c0b000800081115029030a6041c1c4e000c091a0454000401e88a09202c9201c0c0e080c5103000610030b880f4501007000300c2c11481c651010b40689a20000c1e5a1141e030340e44101071b00e0b003000344075210160600c400018030342d083e8901074645d01c40305500c4442c28917440391030b03000b440e8224108400169015409000611140c0d00307250704142c0403890f1940ca000c1c28207019803107416420490500900141c004142a50001e004c400c0180c1c0210104540325070b96480e80600c00800d1707100c107840b100c1c00f500c610b0b80314520210b15051459004441c0c0b41c040e074a8005440001318810105640850b560180c0b480b0115a4003030f40c001c01d128a4601142503280394100800340f000001c1c441846c044400402c0045032252800034003aa078220300102c186d5a0035081c24 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 505109721 1250 505108471 505108493
    0xf0306020a02010b0907050c16030b0402090403260a0b03060103150908071a0f0903090109051c0606032301020c07092d1d011802130e01020301080318061303020d 71
    0x640e01c50845820400359680c00700140448d4401c4e0012542d10610300c1d90104048180307404050051a40d040000d005070500c1d1130a160044c0c0300b0300c0c0c000c00b10310801e8405448541002c1c158805a000c0005200007030f2400c0c0a09400d2440032000351286526654464112511030b8020444942e1a174008000b03211f084800c3d903904507001850007042008541c905c000c41242141d80034060345030035000c50320540c00002541c19020b030685179078011794204010030584240c080c410090741c0712005840c00001c0d03900d008503001076101e01c180c2980255000b440703456801d511511046540c1c410300c100039130f13400001f5070281190034070040000d80704070b100d804146040003000301c51070f0307031003407602c0700400500c158080785203e0704e814541c6032002c0100c900b490a075001c032841c600c003820003113000344054030f4500610000f40204000000700d2401d020786090a98000347d00c9420a078001050400f118101c0c19044118114200c900624140102c140003014290a000c040d00034881c8042e10400c0008034414 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 505110971 1250 505109721 505109741
    0x210c02030f0f190c081206060403060c020a0204050702150114010302070f05030904050106081303080c0c150609070c050601140310020f0d0b09130b2d1f0f0306020a0201 74
    0x4240d40d0400300d902c0b032186621100000708803031640d00d2000f04880c0f0070501001007170b5002803114a800035440d035065a002d00503003940c0d4441020000040001e1491040070b04080740b03074001d480c01c90001c3c010041151402080c005c25034100030395004800d0316113528103055800075203007018030741c0308407004a009008006005003400300d000d0440060002c004050050403c089805011582e00c03070b01e0880e40700e81c041d10814180710b009401070001034000c0c032649500082c01c205403410206280903941c9429000b081c0003941e01c40c0003042c808039041c20b1900d80d60210440c04c2c51440b140c010ba0390b02d50340d02d07814460b03100d00d05240d81b20200f0664043c02175401d1800030810940d1110844d0018148950201c448003e030b0798901028200203060107801c480c03103903001060300e0b02890700b15114030388200700003000c40000c0e000084110303441000c12100066031407180b1104d5000d80c6011140704180a0610003030107071034440040100100e082101500040c1c0340d100102584030a02c2c80070503800745c0700b0015 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 505112221 1250 505110971 505110997
    0x1110050106020a152408071505090405070c02130b090915070c03020703020907080f0604090203060c0706060510020c10080f1b0c010501080c15030f07080c251101210c0203 75
    0x40c10300f1766850080415050340c0c62903081c3c0f084983c1e00d8041c0489400e100d10340c02c01191046c031264059151a0340180c1e8000118105024460920760007d03d1060a00c12a80502c0384e0720420186141061408141c0c41440c200c0103024094032070600141c0010018009010030111618070f00800d84240494402958007600e001c2d45800d0444002c0c158910845562000b0100f0b00000381030f501d09400303501c1c810350700603000d40040d0300e40c102805d010f60300071401551096241e0000240d41c2c0c582010741140a01c0a501030040842d6110401081062460308141040f840a080c0004100e83e86003054000040c80920500c016500440c90010f00440c0100c00840d440e0800010b0a0440418402132080013140c1c0c01541208150041c1c0c020302007070f16410187c604640014440c9401032082e250001002082c80b41010140354000070307640c10480706500100c48118200741040300300210883c05040034241040000300d80d030840350014401114090b0500e85850b51044014001d20413210310a000300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 505113471 1250 505112221 505112261
    0x402210f012901020606090a05090109020a0b0a020c0d0c0e04110d060504050d110601090e03130f140d1203111306091a090907030b04020d020403031110050106020a15 73
    0xe1203190420b410100d00484005900e08403180d190b2003c100240f1491000300f00380f0a603102c2c4a4400f0041000401d1686d19644e41e042860160382c90300c8002004111400800b5903441c0c1030b0000900341034460070b829005101c0b81c055000090040365580d010b072071104071150300e50380c0e40d07003005860b4503c8005c00d1a0000c0019031308205009503600000c1c801c90080c401c41e00d884102201c1202c0100c10364500380d8458020000512001000e034010307003200300000080300d0030318900340b481030b10315240c5034070400700700ba01440100310044007018890800d00c801c45800980010769180d600072444000c0b40c1e5010155280c004031910301081c1d040e240d1401d00e11000c07402098807450007509446a501075035100c1080207025031031541e01403040390030400700a030040032982c861003c241c1c040c101d503012040d407140c0c083c440c7c0c079152600e520107840250b019a590307590050311816840c1c00c10b080c001c02411800c0c10b000c01880500d400144252426a00083d40441000b6100b550802003c203071041e464241607003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 505114721 1250 505113471 505113491
    0x30a0218151210051605090d050304050a080f0601141315080d0f1202072303070803070309060e06010605180a2637060b030a15140402210f01 62
    0x5034022000f85908020480c50700c1300651413112020b0a860b140000300204412170b9681041869040002d216008590800e5110b01c0003443d80344503500101015440074020024071030040000341e0041c1020350b0408048041d41c0c0100d0050909030303480c021440d072106440191012070707101d0203000307290110a490104408401c0103058006020900c0001001c0f1a4a44c141c00024821240603591000c00301d8010301005690400054410041c1f592a000178000b400c04201107070011481001c09580008111160b0300e04013040740d407030208940890348103030014441c83d5000000ca070b9402d000c04400c02030580300c0b90f001600b10080b82e00078041c404641461200601403003080030000611031802e454598000d00680d0f54030521075050b041e2411108031030030300301000d4120b5042c2c5580c0140f80104000307140c0804030389088581030080b100c070200d4040507171003001d6611401001190f090180c0301c25082c9900018411480e49460a210712005100c480d40c1402c1000210b910f101d050009101000c02 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 505115971 1250 505114721 505114723
    0x51303030519030b100f02030c01050a092f0909030f070c0e16020304060e0409050a030e1504080304180e070b030105040b040b031f150b030103060605030a02181512 72
    0x802c24807540b40c414010b101684440c0a8002c541c180d1402600140c0c80491026046406c01207074100c203819408100032001458030b0078041d062143c140301c030001c03c1c0110389203860300012070b403010304001496540f4440000f451005d45840c40d20f5800310380001e002c0c0c0341c02440b03e041d840b590b145e020701060000380406c1000a80c1c85041d085480b030b03002545095881029042000200b16440c0005070070030042032000ca801100c907184c002001030310000e0a10513581c0c43c2d03407600c00c981e00150080b0b441c40d9104441407910006038210b03014540683e83c1400d02d410482d40d564011400bc8809040c001c9054060f83c1c582c81e40400c407000c044500b16510310b60b4400c41714409034070a02525000701d007844128507450500f030282010300035000d401440149450044494030080c1c402d02d0306d4020b03807944264a161000d94111001809082c8403043c1c1e294510b15058040740c92540c00710f8060f07000004a040036941c1c26065101800030214440701580d554034101c0d002017103401c2c40550001ca500030300040510 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 505117221 1250 505115971 505115977
    0x1807050405101707020a17070c120b0f0c040f0b16050d0503040c051c02010c0521090103061e061409040f060602010c08010e06120a0f3801090203070513030305 70
    0x1448040c01e24542d142c0000c02c0380c64021605015280c002030b08001890140b1060041c20003a0040182003d103a4441922b0b580c2106841310660b16200701c00c1c24885903c01e02c0703807100d4004100c01001c901e41443c1c4481a0301d20034051260a00700503020826211844d0016111041c443c0c4c01819a05035010700540071f425508252810b542880f00d841010440b0308089040982450003110600000700031907004480b15400d22a046916000d800300380703900400d00c05030301800800b1030001192901165400102201e041d6803182124a2070034084100708000c000c050b0703081da0b0552511400c80e80a00301c0300c042d02d20503141101c0d00946410111152044035600400550f0303480c1c0e000380200407040d0400c0701c3c052028040e040c1e03084d1007440841c02514101226040050103c2d0036245164255200c0d01408103078218159000c0c03000750920171000700c0754148004ca01510031444030355203080005140c000343d014011000d40703076800030118400a00441c113486c0185581002c4002d59030300e0b803030000e207aa0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 505118471 1250 505117221 505117247
    0x10031a0d110607230304032d060504121101050103020d03050702010908060910061e170a1b090b060c1506010e0310150f0501020a0b06190f060801050103020306180705040510 76
    0x1c0380401d01e41088040111b41c00c40e1f403c00055074602121820b2004414080c08800c0904011100e25100148050061502c964000e0042c02801c2543d80c07001340074161440461711090f403621005000590340d064540c0c03041501803130310903103030700385840113a60144040c0c01031a0144162020000b022000240c0c0c503d00b82c00c2e0580c18440b16991365208044046206420b0b1103001c0c240f6828030030542000040300c00c03280100d080364101e50b16911074002a000c2d01248504040c984213050158002c01d014005503920142c410390302e414201c140b03690700e4441c51111000d841ea8285d02080306c60384100445003007124001d007500d45031500501400300500c065105001008400140040d15004d4240580201c1d501038000c3d0004001903a140e0440400040009500c020000e50001c08c141880344020050402c40110b002102d04101c0d002d4541201648001d0406004000700300b4951200c04035908003220103082206640c8072100306458034016500400e401807004240c1100751544100c900c40c4c49 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 505119721 1250 505118471 505118513
    0x9090a090201120204030f02010e06041703040312020c1c17042309090334053403080a02010b03010203130c0f03030206041502040b0d0b10031a0d110607 67
    0x20f80615118100b03a00542c0b002602d43c5249045c2000554007030f032a5116042c0004005924040e2207a070f9000004025008100c400d170302c041414070800c94428030071408000c480c001462602036582c001080c030900510b0b58042c03295000c0c2080200a940d06205a10b0040e001c0d1650301c89444044004c1811100034a1900749480ca1307004080608019079021b010720700b0ba030b0107186030514103d40d9880c0145000d07140d54442c85805580464000d44220151101d44110081c28030190141801640b0411000c04802c128640c07007552001403000004140880e94850096500c40e000c290041c0d0060000804442e0513500010800c2107424203643e80100030b41c0b080c3d801c0030350700d51503075155a00200280802005607001202050200d603a030642001e5135800c2030009460b0686646080d000381d08006c44c040b400f1611800038082520384a8541010345000b854200081d03480d094074007d2440041c01c1da2401048005080e0081c000032840b481a03c40016004079a01c2520b89042c3c0750314603000d542c000358 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 505120971 1250 505119721 505119737
    0xf0c08030106080a1a090a0b03070806010e0709090203010f180f060902041706041505061906090303110a12050901020327040513080a14040e09010b01020f03040515030c09090a090201 80
    0xc000c80a40f962490b17602c082c0c4005c0d842d507a40020320008015060190f90f15110710080001e41d09001c0055601900c00c602c0800c4480c00e24080184c0390314030390741010071400e005000501c848041603160328100c96154005541107842c42141500402c2e076400826412400e001e40410042504e8005000303c0c1e00f1000800031019000445980b40c20081c0e90092036140999007207814400c1e01d801064210f2170051843d003108044101e5550403895a40c401c0001c60a811810014560800310701c02d18920400b02a040c0348080390340d50004400340c00c2031801030020200341005264400c20646100303034002c41901c1c05402e960300c0c1c040008058640804d20542c1040002074045400e004082c52403a030205240341802c00803481510604450800c00c20043c1d0180000510010480101400f90309007000008522a8040009041510340c0e44111901d600811007080140c03074040184d000c00e010114032946030349607884162024421703521000e41c0114802e0a0202c0c003d241d0f4001d403c0c8a201340ca465507 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 505122221 1250 505120971 505120991
    0x1506180b091f080f0d0216030807030c051207060b0a050418140a02150a090e090a06151205030a080a0902091305100615021e0d0f0c08030106080a 64
    0x5403500034034059009102080422440e1502419107071441d010b501044420549441c000c52070542c0d0f140c00d2928076880045c400c8921501409025907003403005424030f450383e007551526035140c411900000c041101c00255103080c85414803040b903d440d15280481d944090508055019002d9031181501c540f1603101d00007118505841400c0300200400180498034106848507140c2c41c00314203101c03115001314650400107a4500ca04103810240300000142c95103007800000b44505030541002d00c01c078042c2000d03c92980790000d030541e00e40386e01227030110312841c0310f44500103540119030160404103444445c10702000320200c0505841500c03a42d407900c2d036564131840f10003a10138607840039401c000f8100c041040d4407085024903000c1d40c003d800b15056103c019180304100c51995000315846680d520740d031a0b03150ba050100102c03850440c1e01b80140c0b40264002c194481d004c2044a0060040000108030b9144c0242e12020303c064100b103549031290307500c40f40501442c1c41140c00240c01c51a01d00b0040c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 505123471 1250 505122221 505122269
    0xe090f0f1e070917151b0919030b090109051c021509010504030f080411010e06070b0114101110051b04080705090702030a080103081308010f0207060b030a030e13091506 74
    0x203506050b41002080383c640702c0380c24520886d00c00844c0e01003600800c1040c5252500c030201441c85150003d030258041d60b00d50304108481d16009171040c19640d040c404502c0100b080061100782500800400d540c04040c1100c0503880d200001075821811401101004000f82041d400b452140d03000f078031151217044408100f100c0c42042240c00610171264a102201954410120105d4211007e80f0003460301c81a5201d01c54045000d0380102031800318100b0b02500d500f80705801e21010005402c0200e9480313001c41ca10b82d1201000140495016918400a5a14080b8080c1a000059103001b200d43d51900c0b11000b607101c00039805494020503010f00400d40315407000bc11549205460307035440e615a42159902100343d801000100b5038a0514480460b600500b0301c141c05200d03030a00070040c5d03a28110f160000540d03c2a0b070038144039400c2250b04034040394100d01c407100781c803804441480d84801c181c0c0c003100042142034409441e403000302007411004e03c01503026509940740740e88103070081080305400d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 505124721 1250 505123471 505123483
    0x1a03011506050304060207080c061006020705010302070308010b030a0b1e031e1c030f0e03030f060a030b0c03060415090b030708031e07170f04060e090f0f1e070917 72
    0x101c03001880410005010554640c0507001d0680701d165000e241004000d01c00745828420356203440f03402c00d000400c2181c00d8040090500070102800c05504005580e180901030003414030601008010003c002410848140d201001c0600001c1c80084407211422100120042d1141c4560092064000340c50f8209182000045154010001401101c000c41c4c030300f00a02ca2070b04214024075440705100d03c0310724018041c1c821483e1350200210f4513450300303840e0a0510400901814001e0790800000d2012a801901c1c0340e601c442d01080b9140d0b2a2200f0001c180203040300d00024244002400005c504152241c200520801084040b103007030540b100c9055407288500c1c15010a014103164280c03581e641c0d410050403182c0d00550320041d01d46020030b0404003640c4401540f51030150005401d00c012034201840c409507200640f400c950b58038103d00201c41e030303000c05400f08083c040088001410320160300004141070303070200002500d5040c00500680000240c0c0605045080300712001c5403048000100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 505125971 1250 505124721 505124729
    0x121d0d020f0409060e060910060b0918191a130507020d0c0c030614010501080c0f1c090215030117030304050a12090b0a0e04110310140a03061a030115 66
    0x86440c0501c081010040140743e0b60700102c0c0c60b141c807800000840e001c207000f0140310b0ba100d04041c0000c100da10903400c0483e2456000088070b008240078416840d00c9a06c1084155400d190300c100098903840130702080586420b044003040742c00c0128120029003e800041c03111001030712840b0400580ca04440181d40f0103c81c0c18005902410350203007498401c0150070200e90103105003404194076522240142c8180b204888440072581c00108000d5a02c148010b6102070040100c0c0c1c101300e5a00158000c40c414001c00000c00c02c02c440306024003140c2903000740e0056a008107840e031444d40400040d640b9802c00d10412101c8400003a40d0350020340003000300d82c45a54030502408010305e1036554910324a58049104081240c807030008901d1110100050070b210301d40340c40309003500d001c00007003006031080a208180c10720300620034014400f0303801c0c04440c103075002444081d805502d500d000c1425140b4584c4058031440c01c15403c040103c0417a001c1c6100c5840a0b00203004410040380108008421441 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 505127221 1250 505125971 505125979
    0xa03122706020a170408030105120604051b0f3111030a050705190810060309030f0e040e0304090f0614060a0302090105121608070f2a121d0d02 63
    0x103840c00100780354001d005603c81400d00c110f504104403400c88402100319002c6810842c000b00600851070650320072002601c1c0c0b88010403081c0350a0761065201d885c0034158485400a50300340203038664a80000c43c00020016100070000e0502c141d201081e52010394051141d058035009200404885001d451280c1c0b01d000500752654036116501c0b40240001800442040014002913560845401e20618020b07041d0b501da081c0d9040440c01403484e2045588444281480d021076500066000401e501000440341015462180c085c00031030f015007030700740c07129180c2e000000340840d4504840c1c0c080c2000c0c50441c4020007501d500e13503e0a03140701c09080c42143c1c0c441c13000d01102003d58480c0c0c005002c09d11044c0750840c2020f20f000d02760010315000351560102180c0c6641c0c0b007642140e020420341d5200c1c0280c90003110b0100030b914050b2800007001c0d005d200d05034650080114110802d40c1c195070080c1c0c46101e96051604401d0000e060500c0c845000c0142e108441d150f40b9240762860007250f0658000b4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 505128471 1250 505127221 505127291
    0x6030703080304060207170a11060709120f021f030b0f18040f02030a0602070228050609040e0625050a020c0105160209070203090117100e180a0312 65
    0x41c450020035000140b00b02d0b00300c0d40811040e00003481c2004100c00d200500708059131110140750024100c0c461004803002540d201a080020340c2c3d034042d00e0311088501e5407685608194203400c20442c3c0c012515006500901c1c1e260607100301a002042010004440e564200041f079824010032072500841078509078800d401042c00400b09545110780d68020748074a590103405c02040c1e006c2410489505803c0e181c240c0d02140e40e41c150f040081041c03202a50f561070303090f000300b403d44994890100901071140036000200f02d0011540317840e44440004521001111058640703042d1540e92041054400c0102c08080d00c1c00089050194082d03038441c00180e005450200714031001154150800c580002c0c112212054100c01740e15030240c0140039452550185658000c01c100140030800e0a0201803c80e001c01410404040125540030050b40c0c401c40710340c02161600200311a81010701514041a4021100f000f801c064102131b44080d00d81600324203001d60090b440d60700c0c42c030b040c846100409055002c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 505129721 1250 505128471 505128473
    0x41d0402010c0b0c120f4c081b0a0e093003090c03121e13121b1211060a0c0c0b12071b111207061107090504021e030c0d0303140a0506030703 62
    0x1010744030150b1500f0703a80c4d80c91340c500c0594900102754500380f806881c518010b0425080c01001c0740c020b0301d07096814203160304003004420f40c1c890400041542c0c0810242204c103198000e40407207076024a05084182d103906150202548070414075860174400d01c02d44182d406800c900100390360a288411420041c90303540b11856a034542e20105000070610000745c0c01103184110400480074083c050040a40440c00c0c0440746006080c550700441400b4429585840001c1e42c00c401c031100c01d01c0155022512a010b504040d40d812000850040200410160124070306075900d024000c0300e40903030401400b40d1180c81d000c0d266a41c1c0100d550142c4c000106155011540740030400b4050507001d030070b042030071010307880203030a1a40390781000b000079601c00c504d0b0760502d8007008460007034000c81400304241d00f050b900080341004200315170441c400d6030a00589240c1d03802d2043c4000c1500140c01c100d070040003440d008004041805203208440c4582c070100c1c0c1c26281c40d1180078441c50015006120301070031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 505130971 1250 505129721 505129831
    0x17150c03131104140633071b030f050616090b0c07030b0a0204080c0609030a03080a0e030403030f021e03220f060203041d0402010c0b0c120f 62
    0x1007000d82d61982c420703a44207156100d6208468101c0c81d200c600c50740604104041182c1c0c00318040d4a4240400480c044000c610680c1e00201e0951004000d042d64070700491900d1642c140c800504030128000301c6c003000080c0700760340360042c28942c81081542c000c0d5440d0b610b03040c0040d1119140383c0000e884540e0a0002a200c0310007080d00782c034100203c41d01d00e0b54995400d01d103400100c0d412401d00b85c020400b00a004001c210b2040d41032401c0f60040d0405201c039001c00da4405c0a614003404100380f01c004039803808403d40c01800d02c40c1110f0140e9071360325203030304000d8510100c0c0e940007001481210241420921220b2240040c140c1c030700059807a2a011502000e4540100d070031401c0010b4514000042c070124000c0705800034419600555103442c0b501c8183d507440890608480c440303429060070480140c1e48500d00301c100f5030f030000d820038136511601b80750805070045807409803854080f02e040c4080c054fd0b8440c0071b803184181908401e01c000c1e00621a02203107070266110501c5d0b03e107882824000d003507 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 505132221 1250 505130971 505131001
    0x312030911150c01090c05131b0e0a080109050d14120f0a0212040c0305060f070806011b050a0311060603011a0f04140403090906050906030a0f030e0a17150c03 70
    0x41800c2c80c41c01e001d0468120342c01c68050f00b400b241c1d85c448a420403caa070a0100c00c038031001c800c240c4100b0540d0300904401d034170f90950011901c20003000038001700f041e50f1907654280140c0100002002041200e103440e0781c1d0b904501e01903c0200304403107212404041e0090498442c4a10b07680b820009031a84400e401c5240d02c0504610b054079001d0242c0c1542c00d0b0030826851156000c0e0b00103419185ca982003403810503001903c40c03100603035004100422103030821821a0000070a10300020180b540c0351006100300c0b40c1c21b900501e58001c10940c0000e06511401039072907600b0752401d4074880e0302c4290406089034890100000c00b22680d02c07034161940750070300d0706048164025002045680c0420071408404030210360841c082030f41c851060112407098420030001e0202910003d40908128000a03900c03000e14600419602d00d0484403820035108414203c4c400d800900445021516400700c03181c1007108003841d14052040c03a183c001103881015805000b2920240900e1640d107594000800366a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 505133471 1250 505132221 505132249
    0x50117060406120c090c0e0a12031e030b03070b0405130b0402041d04050114070503160e030609031b0705090c0a090e190c0806061c0608030a0305010312030911 70
    0x1e0781d1414001118010401c83e6070351184180e800d902c0b0241048518002c58252070403107401c00c407440c080d8001c00e407100203103101170740c55015541c10301c1030751343ca801c4841506e221a803420036021f07040c0d00000d294040c3c020020300c01084040c2d461154440445061500440c42000d9108288040e001700b0740c10598440c034685400944003514080d181e60070f4a8041034805000e0310618200420441404020320030041c09150300c01c49426035080641c0000c040740000b80041006800b154040c2c0c406a001e0041e0403170a00f805403d6485e01d240c85102e0070707140d412158045401405c40c12050840001c0402ca410583d82c1c000e1542c049600c5548000d1840d070400315000701408640c2130007284012140100c0d5101d00c44860034213141c050b17440801c1003a5112040340034140300795041481441e68940701078400800190311031a0a04090441d604c0142080e548401c3e1240400a0110b90079503040c0c0000741600d0154042010705d608500c421800c9406010010b003021080e45c0e890300c07091820b034610200003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 505134721 1250 505133471 505133479
    0xd080f0a0917040f03020117130809010507170c0d03150303050a0525060b0607050a020603090a080409020a030e0703080a050307051b2d0703020405041a071101110405011706 76
    0x710040c009144070342c0c8507804c16030041c903918808004541c3e01510340d0f164290541d1145159040c9107051000c84907018900800d0103c0103d0a00d889900c16005e0f10b010b04c4d003200c040a54070400d0201c020890380400b034002a903000c3e02d412004014000d0150a00b16994900482003040c030350f46088407150000340e0600c04010040010b048000d98501c0c41054240c000403040200425501e0200101e61940c0750040c002c200030311000000c22000309040c2c40d09a0159411940c030b50714140103609081c0f42880061811501140104105905074040c000f89140c03900c08000c440c0040c0392055481ea11403000416001c030401103900b02500c140069070700080c5a0401130b040c00d03000d00c0c11144d06000700854200350307880b241a01d00500c002f142c41c0c0b11450494020710020241403080300b61607061901000c0c1c09941c85401040c1004001503101d1490b40c88001505241d00b841a4001d1a4109040034840c580d820f04145040d02c0b500c0104072411103038140c40740c55403a511650002400362000349841c0d40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 505135971 1250 505134721 505134743
    0x3250518060706020c1e010f0504120305190c170703180807050c060a1809020906271c0c0501080f180703200112020405030a02120102091009080d080f0a09 68
    0x1445004024000c8406c6003541d1510815504054003421030700c0300814608181c0c140800e0002243c03041d011401d52201914000c075581c2e4400244210302651040190b101500d000800c81107217130302c05032601241d031f0703140605044c54548200441c1503451610094a030700403503100183c00180c91a0043c00d0f60751041c0e0640340424000c03000115250400c0410002144880601c3c0c51203d000744904400703807860000440c1080c41308004600035004058068003414005017000040911a051100c08101c0080402c0c49503840c15804100c003000701c80303044440d0005920040342c03079070054066920440c4180700c40070355642c0741c036151000ca105900d00360005000c0c0d0000880801d0f0050f20401001000c0040b07e5810400f101c001017013005050b032405440c0d40b05000a2000f0355010a0701140c840d01201c0b8040da61038080c005900920480d083c1e40e6020782c400c481030080d580c0000ca81412903201e407081d6420200c02202c1507c01402c01c8421040c000c82d4a400200c0f1181150300c034042640c010401100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 505137221 1250 505135971 505135987
    0x3090108060f220b0d030e100918020c030903061e0f06010503040f110a080102180604050d02101205010801150806060907260f100f080604030807140325051806070602 73
    0x845d021062106800240102240d070035281442c001005040302c951902080071031404e05e6816503245007540a41c49503400003651035268104009a40c80c0450045c25500b481c149100300004012125000d08001030f8580c00080e0911051080a4400c41068540501e035031307980d98440380341d0b00c402c100854010314a00c0c0803204940b181481741c000b410501b0001079603440f0811200741c00c0c082e44d8521902c54041004240141c3c0c54162121114f03d0307068900213100c2d2150036043c1c80e001400c900c80b1091929050000070459015000038180880e4a20045880350b140e14109d9250007041380c03070f41d03040103141002c580c00c540b207400a0b001030452a103007240c1170300416007440c0708001c0c00c0d1107a0041c0d00442c030911011b00c0b1440d030300740014201014400803180c600080076807183d41c011301c003809010001c4002a10386000e02520b0030b40e5060550380e55503078944500c804888900360b07080c28400c000760f02d40090b000c0d80940c0840e50410500c0d041c4001c62612481003002961200000b121120f80a0100d08 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 505138471 1250 505137221 505137229
    0x70b06060d0905010b041505010c060f02190306030b0a0b0f19050402130305010608060403020616120c0f0201110412060209300d090e060105031008030a0203090108060f220b 76
    0x120036144100b0002c60717000c488208000c00c0e109075010280644949032000c20940e0780042820b40025402203020520911a04a0f6002406441810300920490301035800d0301650580c002d000341d86c420f040030034181e150f004041c011107071301181203508500001d5442000b07140102e408510401224550f00009480b440494140d030003d094500c003249440b6002d2040110070b0040101500289000300034514007520000c1d510080600300c4814070322034804a0051503c200740310940c00070185400c0c0071460701c10310000d1010586602001c019441c000e01c0340c6102042000b140c003200c260700c0d00001e11480d07070b032210b40003503010b00400b90f40800d01d800d404603840e40b034458000c50402d00b00b5102c420104c234081983d040a170b4160300c034410085000401d1000210b101081500f03d0000e1030031940701e40e00c081c0c450042481035000104180720100e1030355142a4000003c0c4a05030003a40c42020720303103c4400703002d1207030602c086155011400f68041c2600b81d04640402080202490020030700c060088041 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 505139721 1250 505138471 505138481
    0xa020a140a05090702120d060b0a1205090d050a031a04090f021c02090a05090f061008100b030607270806010923160c080319060515070b06060d 63
    0x5426995401540303600c1460a070305600e008200548a0b125107203014a0700035202ca42c200c1200401e2540810102003540d20740d40024090504500704584d6040a940302070f00c409451000c2110480c01e040003d07214880c0031511101d00c854a440d8a8100382032b0300800c0c1d010f02203103207000303542e000c3e84460b0a0542c0d8030750060003030003801200c0407603640440f401070003a840c503c5a008001c000f07200040f41c2c010385440f1040c039402050501c00145035240d44010504201d88412a4095071081c801031110041c01400c0704811aa81d02e4100d5201c4078906003030310306480f0746d4007d50b40d02d6007110700040c1d050343c0a941001d041c070800104034440500076500c10445505940c10242a5a0001d030040c40742646520610118906005030301081d10b8814020700c2d41d0080013020202124107121a40c81c1e1980a83c0d2043c00f0705038028082512427400c2039207507030001005100d00c1709550400c50001303181e041c454120000d40c02c000c0801d501c0d1a41c0d507205c10803681f9024250980224081282c400402203d01c11 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 505140971 1250 505139721 505139729
    0x202d13021e0414010f1205060d0501140a06050a050901090b04020c070b120c0306033a020609102304020105070b13030915020304051e09011215020f070f050a020a 71
    0x2207940c44905020f510a03540040305a00350501082180d40500c02d6001300d81081d2000c003034036010910b03030b4441d008078401d0034904000601d590b0801e2001c040007100a080d0910a004a0804001d140c0c0e6441c10002071280c103103e45600200d2040061011a100da04400c24101020b4000741c9800c0d610f0128a00d4140e595200341d0300d501c40401e282a5032120380b05055000543e1103401030a5041c0321002070b81700ca0060240d1010030351508500300c507403201d500351500099110445000840d03204c01002c5d4a5100480e400006402102c1d000701a01006115031b10650b5104041030ba890607200700c4040910b000900117074103110084c00711a000401040f20184900807107030120085e69454a005801700072103810214038004d0002c0c1e0b01e01855030000c1038a08980c8211180c0394450050145480e84403244102c0941040c1d0800c0003090482c0b291042d1854181f0800c601901c44110150742c9089024810780b0720100c20f810418400032600400780b03202c1103405030081d5005070700b050340082c03443c0350540c1c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 505142221 1250 505140971 505141027
    0x40303140a2904110a0f0f0305250207090213030303140702061305030d02030106030c180b27060c010b01020d09030f0311030c0609071502030301030206070803090703202d1302 77
    0x103c3c806c83c3e503801450410b8042d003d0509002e14282030702920700b5552015030300700c03490160300303080d5030003034030030404400100301e0711104640d14612075180340d0842e2801e01054000ca810f000314003090a2607001501e00c10352281d0f01901c0107032502c0d0040c1c490108072a0090b02c0c18030050100888031440c500c010343c001c14079030700c0c00144c5800346000a4461014010000350891000e001042003542440c01c40d950512010303040809031810980203001c00100d518510380040b80401c4002194205612407542400309800300c0300c05d034a50361011104200f00340001003100070102c8100c800603018030050350f036401c104810fa074109200000304515007a401c84014540fa888003d040007014210400800c4000c00362001d5461503044d80c0100341c06102c1d10f000145840d030000b000521307045007400458041c5500c04892090b0010280501d80424180f0b207446211705170000d03890300111264400320101c0070003950b0141000f60711307004002106045580d9000389580170000710b402c809011101443d2140400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 505143471 1250 505142221 505142237
    0x1003060605030a030c0b06010203163f26070320040806010509070309050f1b090103020d031d0d0510060605032a0909040303140a2904110a 61
    0x1040420a030350007644a9402504181c1820001c42e6100c0041c0c03814541208039240140c44180c0100d15510840c114110007494085c0c00ca0100603541712200900c0d0b440745030008407100c6048075807500c0d000c600281d80340d4500300056615068060f040000d40410060b403045404601421120b00e2508211400b00000750b44072a9007403411401c803000415000c90400742030070305051030506035640303c0600074075100b007511200180f43d0700c2c841c2d044091089d40c0202a1607d200419103142c3d80c400c2100f101024581415460303010a00784403400c207048036001031a4140c140401d84050b100c00c6803d00d94034103184c00540464807940c44502c0c001d501c4c01d12506c024090000301005003822940e80c2d0304941c0800c20f040042c008415100e54082c42c030741001242102c44014100c01c2030b00607201c1d000001e9000380c082c2d0200011306406038405107003882c07911034420b181e50350801c240044a0410000c0584881101340248514808406010b11080d01504c00610b60340c1460200c03d41360410b02105001070219 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 505144721 1250 505143471 505143473
    0x10b030f0115052b0207140613030503060418080a020708060c130308030901060f27060f0b090a0531110301180213030501020a091d0109020c12031003 66
    0x2450245004200303042a101004940e0b40c002072440c8110359940150b04520ba038403402c2002ca031540ca0783c02c0a990282150b07030311068646511346e00b8082c0c0e510a21405103400080c04042601c0d501070410394141c0d140b42ca180c0d6003000f008010702c070f62800c044150211100090015816100030650700305207070000c150191801500c5490203400400e482c0203041c05120059901f11040d2065003600c2e80100c0c11034072030b6034141060703004007410b03842148196105200081d07412a9145c3c030401c12000c0440d110602c600002d00b03402a00d04900c115a1488408202080310940050180080d0940113105550442d920400580204030b030030301c0d640c031100400c00003840c1160300c841c0210f91401400c0b01845915040d0504a03220b0105102c1c140e5031003072018100c0316000303450381129082c01110300c0b82000e03240c4031700f81a03001390040c2c907040001c07801808022428014000328902c1c040944400081240c1c20614445d0180d00030120008541c4240d80342203206032400c1c4040c5124007800310103112081c1c55 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 505145971 1250 505144721 505144741
    0xa0603150b0c03070609020d1208072c10021905010b210d20060405060702010e03091c020409050706120609060e0619050d08070501141303030b0a0509010b03 69
    0x1680e446100740000411110a8100c008402e4408058002034000b801c040e40b0300201e90300c0112200300814425120010910298002c047c2c0ba00800c000d544602c0343c1c001c042e40111419501110500d41c006101c08004001d02e804080800050f50074070650b10b44000e440a442d001103111a02210503944409401c6603600308011f81c86001070080070101c42c07202c070011000341ca0320f1000c03034042c00704500a880d0100d0701060803114206550341100319480341c0b502d07050842e1145c02c2a07421070015403c25000058446000040e100049030041c00040c0291060141c20686668901d041fa0442e03200d081c0000030620920207840201042c1c0c80ea5104108007041c040201d80e00fa130440260b42d03143c000c05024080762400d40f1503000388140c4442c00e4100d08804c0441c04030a055001c25405031040e501c80c01040200c0003d0083d0300d1241c8000c0c000c4240411008a441c44120703982c0c5400196a0000b0000c240700b6000901030400250442d00d600b9290004545204400d03000445010340010500c181604 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 505147221 1250 505145971 505146011
    0x111030a030506100e09011509050d08070506091b0108040203120f0703030b0a0e0c090a0e01120b010509070503061908060a0b030606041a12430501020601090507020109020a0603 78
    0x10f0721780b610000200a403000606449010b001e050300e9030400341400821680501e40f0382c0040c101c020720204c4d00403d1490031440303e9205400880d0b00d030142602003100b03020001503040300540e51681c2c0c507290000c0240115543c0200134410faa252040640758412500a20002d2001c2d02c0c200c044590703503208500b001b07030544a007541820301850b8959030421030903c0d102100e82c0c2040c80c0180c1c465840e0102c0002900342d1240c1d4000501100315040006200800440d142410724826110801140c0c2e90b07104009950310200d6006011440410001e03093b403a02c2d0301e0880d0380a0506094990154842240c01e00d0501c04480d400d1840d50b840c11007100c149000c01040f80c1c03010040741d0522500802140b4900b4108500c94014020a8000130700810590148814000f014144030051088a6041c040d02103159040070360808942d102031110000c01c0210014009880e0181c00510080e40703818100c2d401400020003c004655a40c82c5100060f5100d40d02034000b001c050b0b0303020130500300c0982e0b0758117000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 505148471 1250 505147221 505147249
    0x1031406040b0106052107020c13020c060a021b19021221090607050a110f010f050a180314011e020403051905011e020a03140f060405060111030a030506 67
    0x94002000c01c400a07201240d03030380c19200e0390314166490b2002c41c0c02c00c02c00c4e2001d00b4003201d031034400c00d410000d0099000400000440302240c019240d0101c20310008224130030074042d000789800a030005440c01c50766030000c100c05e910bc90120004004812620f42c1060300315403030791002108190b0b81006500e4000f0311009003800c4030000d89280001d030034410024680300000010000e4000c00c07011032591324541135984031a003003001e46400680b149082c4c0307098209014410700c00c07a1350842844842d441200e0b80c40315a102c0361036081c5841c0a210050364104611000102001d004000200c002000b807542c00b000034580c070f000030944c0c0c0c450380401c2c6841c070401d034505101c0510601003040071800000f10b010110f1440c50604154041c1410f1580c09040342c1c0340c4803180c01c52240240741c85860b40d90b008040c00d26003070794200b00b030461400090488a0701605d941001e040540f0100e110b82c6000d5200c580c00541c14106110b1742c06400005a0541d0000700c070340e0f00404d40c0c950030407409007000102c00c0c0c028 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 505149721 1250 505148471 505148473
    0x7090b0a0b0417120301150f1e0206010f120215091f0c060c0201181502090312130602190b060103140a0906050c0424091d06010210060b041526010314 66
    0x540c101455001880203115581042142030070300c0c142c0e418060304e5842c0007558048070740440c4109d031820295543c0001e00c00e41e503000303500140024248001c800c8a08030a5401440c400d0343c00404035560500d03802441120384d200c0003051030013030140601108030000403441d0b2910b00c7c180341036041c0801114500b0700300c1402c2d64103107400c90401843d140d0407200256404503581c04052010405034000303004050040e0303018490303440081e24607184403020303140c00303d051000c0c210202e0310307042c1c22030301d0303080910280214035400320b0540c0c00100b42c0c0c046594001c80602d0000384604070340d51004104402520048080c43d0381e0105002800704601816900034420002245494580100303040386580a00c001106c00b241d410840101d24400c41c1250001c0c000806801d038030141c0606c10580329502030b01c2c0c59004d48a8010003108460503801540100d450710180c1605003403401516002d10780c40e0041130700402051554144040f801038800c1103480080030b244401030340c194641894085042c40d842046 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 505150971 1250 505149721 505149727
    0x5070e041e020d0615020a02030d030e0303130501020d050712060f03080a0c1b0f380a0e0402031008011409100b01050c0604061b0c020307090b0a0b041712 68
    0x14290701e10104040c4800036500c0140d44003030440340b9030014440c1d0381101305c82d2140e1800c030440990340040c0051800380210191400c18013010310686c2245c0090400c401a5042400003545d02e15110303281c6070007607000303000240c40d08a081241404865084a500d00070034075080d984002c0b003440d07204190103003000a00c0704140605544804442e03000e91440311003044200d1600204010b842e401c000e21109050101032140e5440390040b8800e03030b0890280da1081c908010301100c0d62400403280f205410300910100e003030329181000c55025507020300020014000c168951a80ca511984003c600c00c0300481d01845446007480e000f24292800306e0055500100c2e000c090203004000400c2030760518041910008801c40c90900507681c3d07004806580c3e440303001d04410013003405031642280894256401d210040109001d5081c0c4020103480c00103501a84009028080103036941d1140b1941d076001440304180a40e541c60158865000c0d420160107244121040c0e840c81208004441d4110780400200381 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 505152221 1250 505150971 505150991
    0x3060f140103020616020307140f0f0906010324030501150b0702151309020c01021207020d050a03020f04080f0f0709020702100819060f05010825110705030304030605070e04 76
    0x40c91900602010f80301e40c00009070f4090b180204001150a181d0141c1074401c084da643c9071160303400150b41c00e4540a400000c0060301240780c0017096141400000388202115243d0200440c0100706140c80c01141e0b401c002404d0702d211050700141c2000750b10500012882e100382a8800c030400c0b070307968000540910f0502100006a42c1d0480b08880000100445921610b41100c1c40003c509254000d07000c0920000791244043d01c1900108007000380c1110080082d207852108980d142c400020b0b1030000f039403c1c80007464a40c82a001450304444843d202e81c101030f00e48844605000b42d41c549001980c1c0260100302c0810340c01d01c403403802840c9129046041040b0307a00801d039160440040f500c20003080c900025074078a01002c401c0b9080c0d03443e0307074200080b42c0c846502c68004078160180e40e000c00c1d1408009402668288103c803692114100080341c1a141d80c0310036942040c2114030741140f4080d131038000c515a101007029100550090001140c1c3e41060780000c5c0c1050348810f1079500940c10700341040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 505153471 1250 505152221 505152251
    0xe0108060105060d1404031e111902150a0305180a03020709050402010203070c030b070e03010e031b150702030d060b0901020c01050d0b120105010815040309030b040303091b03060f 79
    0x1030440b201500c01d0b40d9128106200301000b03007506001510024080c0d820b01c000c0c51352042251380c12680030f40c0e140c800c0071500c01c0142d450320f031050303404821688071b000140c0030580b41c004d125548502c09800c180c00099a40d54090f001d0304070580b1000001e503107208000030380110701500d052810035000a401c010416440003500d0340801d001d80000d031a2218082002c591003041240d50a40c1c10480c0c48031255100c0c90450005e0500342d54110005048000a0400d4039040c80b486400203c2c010080d07282849103503210300781c2d00b03841e06000a0f5000c0d42c580d90580c00c03417201c48103210b41d03060360255540c0ca481c11041411140240c000c0704040c241800b1f900310a0f600056000300070b000900306252207001c0342a00da00640342034441690017200f00c200182d00440c1c1500300e40c0c1605d40c24415661264405141c02c0c0b0341d10030841d00900002d460030010408580c0c1207116641143c0245400f040b05400340c1c0300c0381804d107044690b0000141d0000c43c1002800030521500b4012460240b040c00303220101d0b4455 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 505154721 1250 505153471 505153483
    0x2010612050c0d11130e011512110d050a05030d110901171009090b01050f04090803040f020d02060429130b130509010b07170405090106080406090b19060e0108 70
    0x105000f00c0c0c000b640315060080795560f42e154104014a4800355554005580c80503006056006003070350700b029a040011f00c6c241964809a9035040400c110b840459140c0d6039010b4070300400030b0b803c20500401440880c0c0c0a019041000340030703200441d600d000d004000000c0760303610b4004510051042c00b22062681e0310140448440b4409500800b8640301c4100a0030f2510841d800080500d1a00400c10304000748016040c1c1201c1080b0761008681150005100c141c5200090040c40b03068100b000030001380c03101c050300103e03500250501460a072a540803501e2940203803c14442c1e61640341d0441c488c000030612000c001d48100c10b4850800d4000d80308000000001d000351a101c00010a40c00041c01c00d0002030001000009e00c05181c03540d440c82080c030306070f0101c1801e55401c17800c0c5190790903000b00e803011141224030203010341e80640c2c6030a9003110221400b9000319210303912109a0400b0a482500703260040c3c0300c41c0c801424223500c414030344049400c2035207d201401040001003041c0c410102ea1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 505155971 1250 505154721 505154743
    0x9071409060a0f121b03030f0f18030b090606010c030e1c020a030c0e0702150103120507060f02030619030507050d05030f031003201302091206160201061205 69
    0x25440c00c1d03151240051007203059600200c000c224103203400120320a40d0703401200a580a506100805c03514140945003182586c080603010840110001e0010b511a04540044103d145803024100d086049441c5200046a0068442002c0c481c00c0c0420650240460380d041982401d00e1101c812a0703940152159010400c09445040c0d448030003254140c00180c154071055009100741203441c3c44e4a04005180003a0003405508105c89002868103070000480e000d440001d064103000581c61580c642c42c0c80303001ca0280c1c00c10810300780903403030005110f40a090390901c4011005a10380c502207080c48502d0450307211603590b24000d0401040480c0e408141c05054a805645000c60780f10381e41001d910758898040c154020b0f220000070002212038042d5004181d0b84552203030741d41c1a40c038070401511054107480242c1d1081418580230583d144540c0140b480d210080d00c041521401800e11a0600c1c2040327540aa2554540d4004280c8960a12600700070344021201ca0300c606084e911100c1e80c550b00001c0e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 505157221 1250 505155971 505155979
    0x402090601030f0e0706020105060306010f09150305010216030f031103130314030a090c0b190309020406050303040f05090108030a05070602030c25020405010e1315020c0703080c06090714 82
    0xc1222a480380c0c100200c40c02c10b009007403050501070031481c2e56070161417003444019403810011840d82e182c0440c65904880c0e180105143c0d46003040c16031001007604c1d035000704081381d010000000089084c00a004c0a44502400c004003490314200500f5220300036034290100343c904010b04c400002b500c010703250003044e50502024962258a070985488000034981c006209011013040005005a08130030b40c2c980c450350709410020350382d4040c1000340c060202020581140c10800380c41d5940700c1c4c1d000c1001d15000810104807030360f903440444c4c00c662094002d00100c1c84a8402448581420900640102107602c0258603106641078010810300602500900c40c03600007011a880803180b60540f02011082541c040307090018030b04100c0da1100041040740100d00740000004c0380c0e078100f101544606041107140c4a00d1074107a0b242c0910280b10030440148545c2030002c05020003041106c68003a600c0707550103950f82c001d4802035074941600104014120b9008540038008480b00c1c214440b5120320a0f2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 505158471 1250 505157221 505157239
    0x3090c010807020d050c1e07090c0201090f02191502010c1e0c0206030415051009180c0b0f0d05130c170c01031802280504090f080a050d18030f0f080402 67
    0x1b40400382414442c610244c1c0411140c2d40440d44504003140307074011240b5800d81003004c602d0454050b0f003a290228800b602d4030319032800c000701500b0442c2c820070300d140085880a030b82c0e5840340c0040440d4143c0715003040044c0e648444040701e441c0c00000350000200040031500382b00d1107154000340034500103c0001c0c0160008000f090410814025100c8407441c2c0c00f00a10840c5800511019164400d03c00c1c200034605204007480246000141c28145a03040703203019011500b041e003940e1540c1c0c0302403095044154104441c441c240700398464240580c66072403898044985600f081020349203d5005040c0c0c091140318174001ea09000500340910600a0030045aa080644494a804114094042d40000007000000b0003190300d55200581a4250484003001c15242c10522085409219004200c00c13680c80040d030215440341e02070500d8900350b00e0081d1412a0801c81e400503120a00070090b903841020340b0311010184c00c900805a02c082c10328241e101c8441c410f2005004001c0600080d005120038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 505159721 1250 505158471 505158487
    0x30c0611100216110d0209010302011128021f08062b03080a0e010209060403020d08040f0b09130b090a0b190e010806160804031b1703090c010807020d05 67
    0x41c40000c48490542004648410f40200f00c44099100c0341000c0f544885016010403151070000d04640c80c454011701920320607030031517005403115012040104103c0c460403a610f04500c03884d0151850408561544034a1442188107005d040007542e401d81503002d1450310946005a80029881ea1040c0201c0350344100261004c0416050511a214580c00da008010340c1c0083c550002d50550158400031420000c0c1002c05a00354200c1c0280101f0a51100080000308094a800d20f00364000c54003031800d003880c1c036588000c104500c0350240d101000b00140880c0c480b00d580782420310b00d0703219082400f0a2041a000b800040c40c41d000042c4007805041e500c40031148640c685226110025001207034007140f903522081080410b0f0030074400d010041c440e207000902d410700181241d000c5d803542074840807000d88403942c00303480001c1e555008415414421807001c004c51207404941f03106d40e0212a0040d41c9080140c4014206010012220706101c50407060101c0c542e400581c1c800c1c032400a00e8015115111 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 505160971 1250 505159721 505159723
    0x6080c100c02031b061309020a0806010216030303050c0c1501030312060510050c011b111c08131a1305010e010b0303091908160f06030908040b0306031c050a0e0a030c0611 75
    0xb0340d105a941c40c0c006d910000c02c2088a0358000c010310281521019103558400004981c2c0e2030103411000004655001d0820029011350819500f02c62400055400c12108185080c074103111200c036045200095030040060681200004050ba41c0c011000d11010342080085048940c0d003140a004210000403009411503003940410b01600da0114803010040a00a0043c001090708039518072038011212004402201c0b00d08040c0e401c10750b911000c0311640c2d4904074500c50356118109a0755136106000c464180c1070483c195070301c511800450110000315a06045013194a420b00c00e050700c1e854a6640f41d400d5900200751201088106c8210500d408082c0d210003408401d03030f010072913078400c3c450900c0d0340f02c04207185601a624501d11070071140f81d5640c4103c060b00d10101c80074210403410403040c440c1d803061000565000d030018003180c00307114460285e500482884c07403002e00000c0300410107440d69540900c00c00324a83d403c6603210f03040b604586076510b180d07569100d00014429101b8070320ba5811705c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 505162221 1250 505160971 505160977
    0xa14010b0306040303051f1503050702190503041a0a02070e090a02120604032c0f0f090f061f12020705070308030106210507020a11011206080c100c02031b06 69
    0x400601612060704140c90083d011b00300a9850a1044854840f420129400c4440c40000c651545d813800e4484908900c0c10340c01004081c12881c114041c0c5003140114011404103804810320a8000f15134a528021350070110108504007060220130410040e03d50380d500240200954031941910103107604d403803090919203070040c00d000390030900c0d4400400300100d001c01d1481c8224040c0e103034500d0700c0039021440b41103820f25403c4005a90001400c2c1441420401c0c0d411400100180a003101c40c00e030140080d0010004850441c0041e1606041240b642050340003180445a40c0d0700407003200742d03c4000030709a81c254410041d00345a002c00c04074184035081000100031768000c0030840d504d50b1104001001d0303401412800e0760588042c01070b64071740c0301340d03104043c800c0105130700cc0c049040c0320740d4402c62614506442d050411021001c020b1003130740c85110358001440c58400410300c00c4400c03001d00009480c212080c6050011104039080940c07400300b030610211403180c81903507522a441c030018800340 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 505163471 1250 505162221 505162241
    0xc041104120804030524040308190f0203040c05040204270204050a03030210230f040312051602370f06090f0209100f0b1b011112180a1401 61
    0x9a1040440c80522028200a0050361700a0054400b030440f002140d4000403806941c0d25000aa10000a00881d2081c100c1135004514400c00d04800e0440400b000e0542d80e80d26120084160b002050108104060300603400624041e20113504091624402c03480032482541508076001a812a182c9400c80c05d038122400350034001c005000c450380b6820002e5403094881c0001d038810303180400c24415880001909540c80c00d100c40c10700c80e680d4461400e000d00b410050030450a1102861440718129120701031700c4d02c40e01d144000d2203c0c2d0170780050001e00d0f0a882031401c1d490380d5061a8036401882d150181640305408104900b402d0002c03625042000a500d55005401240f600c00301e0001c0144d00300050420034000c6484141a4a0300c804000003811548112008040d50a07420018022034030003a00000004090a801a00c0082400c03825505a001c041c0000c00700080c4000120324222002e642102c00b60040c1e580720420504650340ea6441000c014001d00d146425614402c4801d402c070341030013 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 505164721 1250 505163471 505163489
    0xa050603010305060f101206020703020114070206072a0201030b0d15021b150f06030a021504030308071107360b0108070e09061219030e0a05040e0c041104 68
    0x303981c0d0303820f00030b031501016120040142d0f054004504215003525002c802c2e10308171000701b1400f03440c0c0e40d24400207601003581107096540345d1000d0b004904600d00558400c40c5c09801401e81032400100040c4108000e00c1603101d1452030140c18001d4503804008184076a50a00700010200841d100040e0048140c41000384198650004102e01d6080c0750043c0c11059141410128000c0002e0b41c01030311407035001c1206c800318500c03d00003118071580e6208940c218034041c00359500046d507500403600045540751075070603141000504008040d0300084280e4070037140d15003c104180300c070a110380c8440b82c5210b1004c10405008003c00c1740d03d4500c92242c0310014040b085a00c03000c4401129014104010015010505d441d0000300c4c800d008803500b55000000070b0003503006556080c00c00151072642401b000c41031060600c411018001e01e160011224066215544250706440402c002c2c0138103078002c2800755040011840741e03443d0010b44805400350440b00851b8100050b00c2e08005409075512140b08 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 505165971 1250 505164721 505164727
    0x14030717130501090308070b0c04050a06020a1a0f070f03060b0307172a0d060308070b090706020a0c0e060d0203010f0c0201141b030408070501090c061e1d0a0506 71
    0x500912a00146000e07440242000411595480107445100c035600c40035100e040b0800c404c80008540b0400607501606080007581469144d0002c00e019030302c2500030002680c49a0305d070700240300c1d406818101110540032180442d2421f0f65980410600c0a001a81440b1009401c0da04c0076010340c01c8032020700b8030440015160b281901000781088103c0c00760b1101203801a021401083d403501040c0000b0306810703203041141d41111b065a5150b40200b02c1d00d003005a48590100000e04a81d0082c030101d4040ca41041c00c0342007102605080c00101e5101005541c000c840303200004598003068011100c0c40e980d546200e13a254404945001c114400003545540303040742606803420564840040c421140d8000c000e020b82101034240d500c0015601400c1984d40c5981480c400c8022500869005104120407814200c0a0781c4207402c1d1500c0c0c9204480c2d03181d698106201003a84a1400e12506080c0074400c6811044030328050600d10740307503881c5c60320099843e01c2c03191a622001d151400600f40a00311a075 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 505167221 1250 505165971 505166003
    0x30e13200a081f060507060b0d0f020306010b19050d0e0d0f02010b0307051f090f080c090a050709061d1201020c0c06181c0819031512140307 62
    0x20039921500d00940400c011202003074030207800c034440b004803559584007100140d0a114041e81e0f0f0f9000080c040710348948410b407801c02601c0d894103580d4450b110340188000c8d00090300c109810803030160002444240c0a02501502840f10014544440d50034100340350b982076014400300242440d00003003459807040c0c1c40074001c1586d01c416411903020f40d581c000c1102c0c0311008105a1118510f100380c5a0100188001c0215420f201c24100040070071410300010069603420f08070a25840f40d401142550883c2c4955112414180030345079001d085a078003000310f85009000980700f5501c3d801480c1c02c0066000e5075055a446806100e40d00940080c0405040b036060721815020b94882c1080002034002d004e1003090710704007082a110144c8090705a4506882c412051141000043d02054007407840b03a00d1000103e24203600801b1502c1c3c04514075040c4a2400b040901076410325602501840307031031802000f50303220000d81c005900d64040312020350103400140c0c85146001e4500060151038502000755 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 505168471 1250 505167221 505167281
    0x3021b150405061302012102040806040501090615050607060c03060b0d02041410050409050709050409060b0a05061306031a0406060207140414070c0501060e010f1809030e13 76
    0x81d110310301c5070003118959070f1050b003190a15020050002e0108644500c1d41c21340d00803412171209080b00d01c4a006040a076a02101803410005590940d41655104e44220511130240640045c3d4440030032182001c525000200e071641c8904000900a284d40f54016040180b0035000880103000c0144060b450706e40152000c7c000354454880c15440340e0302e88001c607909081010305c0114110098445a051501d400240c2c005000010f1446d01007040400002c951a40d6078410030304024050030001a40d04070703107000e2019469150704034602c9030b2014042d141c0100040c250000503030f5130038940410105040968901c0740038001018aa1007410285c01054050717001989a04407088240b48008803500399080c0421030300441090201c20b0701e10000a110240288004613045128000005019a8909104507610700a81166001043e071000400c0313000c0e00305107031403c104520070702000b180040b9030340640719948407135050b030240c00049424411040e5984c0420491200c030f8910040c1d10181c0d21100b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 505169721 1250 505168471 505168513
    0x6030709090b0a0e060616080a090e07030b0f040207060612080c1b0f0f1c0b0a0c02011b180e07080f09010212011412252403021b 57
    0x81203542c0c50031000c082c0c41e03e07140c60640100c500b1840c070041c0c01c0d03c0e41c1e41402041da002a55060f80100c1c0e0120450010307080d94028050689240e03184d150b00c1d4103040c949094460050038040c00c2609020160404d5a610b224401c0644007c84d001a80d840c0b440c0ba000c00940310a5000410002040c9207920500010783c0092a16030007807401c0d6000440070490560041142120041d0001c00d024008d40003402c00d00904555907800803c80000c08203c44503409018620030022220401100b092102078056800345a20b40f203a42e0009000640d161101c4d8041e00180c1501e081c03c20201551502ca481400100751000d08880048016103190114010b80004030a07160001e00c54520000501070350810320a440c05120000b6004045034a0a194502240000e500c0c5aa000b55045c0140094010030800c0d001d09031704980702800ca600300700c9292000b0b98801d501050072030804011004055a100c54404c600c0213080c10b005841d100b180c1c0000d04030280d400c190808521405082c0b141802c000f0000d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 505170971 1250 505169721 505169729
    0x70305060108031809040602040308031005010e01020c060f030a150609030209061c12030209120a4101061203120e12090d1a070807021b010503070c0203010b06030709 73
    0x444055036601c40b05507543e8840e241520039600342c1000074240f586000c50780640c02c18003412015003030a4490310342c041242d1060707030507003ca21030302101044596085450030b000a00c09001601d0250648000f2a40c1031045483c41d0300910350010000704030709410741c40101012290150814441d44405001d4003d11240c04240e201d10f1420740003036014501203224410b440c030066051900c0d41a2507440d09080da904011440c2850307000c1c0840d800d1070307d42540706010322070480c0041c05180b1242c20180f590030781d8690762401340020a41c0881c90300d5564545000380181e0840301c03502c4010202d04060040850303803c40340e2803101302c2980000b4194815101449540c0c3c1c28000c016100d00780940580d15050038000e40c0309043d0500007165545004008119854002c0003914128440400714110100003291a4004a440c040038480050350400400a60f92030416400b0726155045001070424000108103070304000506404004548082d0800301c3d914034003802c070546034148007101070105070761401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 505172221 1250 505170971 505170973
    0x270302010f090c2108130e09030c0616111b011e09050d080408010e0322030309030212031b01020910030902090402042301090c112e1d070305 62
    0x21100605848034030850b01840d074001d582c180c03400d16001880400c030780340c60740e8000441d0f02e02c44120003142c0e407800105644200e100d11340e65024201000c1d888031140c045c20036886ca0f80305001c040e01344500054801d030811a0709185540301020040c00f241d0184155131484218090404800c440030014400400d8441c02600c401511010780c185500244980407003d00000f4070450040049041240c4030303011240c003c040d4181b9194862031420309540700301400340b01d070f90710015240101e421a024180e05200c0d803507020403e881e1031514003c201c0121400068410360000d0b4180034000410011560b4075400ca0f41c0c48810380e016201c01d18000c1d088201c2c0c036801050403a8a070103482e8464400d0510311603008007000a40c1d00c0301e400340802003000d03001030054110300014030440750301d000c10076a000b403812030000709100e084010001c1804032130f2507038107031198040140100845000000710175030030126504820b00030484e5950201800f04241d034030802c0815008000030982000c2210384c00d07079020344 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 505173471 1250 505172221 505172231
    0x809121f2a0305010518060904080c1239060105040518010f150f1a03070e0a0b0409150e0406050c090d15050108030c030412050c040c050c010c02120706090627030201 73
    0x2d03031b056580d007140c48690000020000030001039920016214254010084a001c0b0700038441400700f65200c510703502850000c40e42e000002d0314200524405103500d0800106401c40ca1500d0250b403103506014040c40f86840307000140f041001e407103155080242170f800a218200440312994010080b01031a1150280b80311b001044004403640740504481041500d40c180c841d1020800c04517405c068408410040c503006a14100d660b03200d440d4000d806444c0140303070b80324645107440c000c40e0000107590001c1c0c10828000c0050406001460740d000b030f04001c012642d0340c1c41014140d6240305072114964040b560340c4042007407000420749140ca0302110001006583d0b01c03550520354030f02a1069910403640104401d1000f211002410030384c640c03048044580c0800c18034001010350b2054400c0b031002580210300550f140c0001d0040c5c0b01400c1050001c1c012642d05080d0740c0c8050b11403100041d21841e1280100f40070410903504c0800c0a0000020284c5100b11118142c07210b8060000e0030341c01036080c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 505174721 1250 505173471 505173499
    0x80409140a2304020d0f0c060318030f051b010f06050910050a0302012712020f0d02010e0f03101b11150708041e0809121f2a03050105 59
    0x648030740a18a484011019090700c1c000ca420510650b000740101c1c0c00940019600c0001900700b0ba40071a40b9118034900051181000001011544e119800450341030700440300c00c01003504030500700e20410161414a41e9050120090101403040c034007206c03440e41ca407401101407964150300410544504803854142512607d459000011a90082c1c0d07074003444900c2c0401c01036000b00c481060010304890540188060180111081f004c80e034801c00042ea00203500d8400c42c0703402c0b0080601284115540b5246650301e80000309008109212640150b8071008084c980c2d540c2048151621410702c0d00078002040b186400001802041000c0e901003200c860815202510100c0c80605c64419402030081682d111081154050300250040d1a6500c4400c807880c00701e000242c070803400320702581c1000d41d500b001e6400d020100d6900062007034141c02081411420b000b002c813590009100002000c80d001c08007031154020600c42090b100b200044902202c520182c054210324100d039000c4492101034000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 505175971 1250 505174721 505174741
    0x1e020d060b0f091012091b06020a030906030c020712260f0906130302030a0507060f050405130b03011b0c200f01031a0d05030c0c01030e0304030b06060708040914 71
    0x24402024001c0038041c04040d034203051403413020b41c41e0421460031045a0703000d825a0401c4511b0400d0645808820718006e040100d54860050014078192005144540c0e507518000c00035042c6011701c0d420141c64170001c0e000140b007049500054000303c501c100701c0181510b0400741d843d81a444041071101122221000c4480741c2040e02c0c800611817420500d448000c0341001525440900e4843d0001c40284012026071020084400903070710800c01025030b581884009001c081600340b80b02e04101c010441802a2b4941c909a100c4a80c154500032444000703180000e07000d00004400005100207410040c1070803030340041c070625454050405c0c440c0c0400c100720415503030341ea60b26200e600442020f4102e10743c2e51080e445200c4c00410300c03030300070804020040040ca00c2000208184c501c0da0000c50b06400c824410300070301e0554442400c04000701b00c468074055480340144e10000d4000212240080d129841e08400c6030780607684a400e050340e940e21280d41c14004c1c5800803001001c83c2a060004680e005e03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 505177221 1250 505175971 505175977
    0x9071e080c01092d0f0603020903011506090513020d0c091e1a03091002040803120105031b190803210703050705031902040b0c0106050102210307121e020d060b 70
    0x2140350900c502115111308810302421410302100c260328507107074000420b40443e01d074030005000170307540250391070144400b0182902c034030190407041e105151004203e07454018103a1401c888041e200051403281c7c0c1c410640003800740032080da41d1035003050842214141d008001d135017550070400342e480d0065248009071201c3c080e54001c945000086075004144404040061a440b04440d800c40e40414101c0c1e0307d00081ea001a404549960300200f00200100e890120703075809071078250010710b80700b500106a04050048040d5460240240140c2e0040d007091031101a0007410b01c1c0011265181c1c1c1c8180c0c180b1100e03030400d0f100b204000301c44020400301d502c00e0041900401c400c1d9140c41c00d680b0b443e400045500408160803582a50030000000d04002c9040030300990448040006080c03840e1600190402c1c0111804011100400725002c42c010345040c280c0e90040c0492a2100c0c04e1020782d04031400402c00c81211011034452003104410349821600200b800429070541409196034036241140540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 505178471 1250 505177221 505177229
    0x207021c0302071212050d020d0606090f08030306150a02160810050a0e070510030e060f15010c0807060924050a0b030c01121802060f0d05012c09071e080c0109 70
    0x810111001d100170f803081002e48500b100c007d600600d4a01e20b00100d10407103156178000400700e640c00d0020014140e88032410001070001001940c55440e1110000c0c1c0d00c407441c0b903600800c4075070105803400024401c00c60030350030114031b1030414805901c1d03480f0681d0300d1a0721070880080c142050001583c001c65401074106c4007070b81e1001001414180010031507512854201c1004150340d6a25200d045041001100c0c01130b014014408018100400c664000d110300ca00a5818404c42001540000e941c80049880451700310600140b2541350745041c45420940607460702c0c0303012064405400c07140c52a40301d540581a1800d080184042c8441891380347c0110b8002170740031848078154141281540c0e00070701e0b241c3c0f02070180f0555184995001501c99041541c4200050001046101e41003e070362040034050f00c1c00d0811407a0340400111007103025000c14141000c103044407008a210b096041080c10003030318004404203202d2009807514a01c0805610484d6401d01c69002001d480794000e0301c2c144292 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 505179721 1250 505178471 505178483
    0x100c0302180d03020f07060507120309170904110d0c120509033106120c02030304020d080a09030b0a0903080105150a2106090f0506121c02010207021c03020712 70
    0x10000104216100502c05000d900f5406a0301448445110522041c0081c1c01c503a11040e4484156060440440c600840194241842d043c24003001c41d818120340190940d9948045941e1402d0002150140048900380d007021071000c1908518a21190040c0302030101e582d80f49204040c50111101c00d441056805a403e900100b05c0410001c848101e0300d0b0041501c802107190442d4a0402019500b072294005000121104403100480d0b0003802202e412074234920095045060503000a01c5120700000d0062494400140441e4801d01881c01c132002103401281c145e03d60314000e0754070000b901c203141d82140014a40b90010500f4507150300d0802131165148541414200f65550503038a00e07401080c985a80300c0c0320700b0305220f0100c15026600190200340000305860030f81c0751140c426100301600581c03251141c8180c0a16100b0b000402d503070180f01d403070380c0c00e40e2030394049909900900c62000302942104e4612542900c00c07045007281550319101c0d03400c6401c0f891b500e09221403401c0c101c080051032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 505180971 1250 505179721 505179757
    0x70905040b0d0221060106030204150e190905010815040f062a0207150e1003020a03090f120912030807031a0603090601091a1c030c1202100c0302 64
    0xa181880d40c0590001e0401070100490055581c001445030812060b01c010420030318011100000e40c2404010700400903410706609013401d040d8185240c0d00c1d040404400c01c502c008058407180d456035080f0346180c4007196107a2407140c9581800d00900000d020340c1c41c00d4811001c4050001c2c80c268280d601c05d940091404000070101d80d514406040079003070700c00c40220901d0004a842d00b801810a2007111260020701c0001c1c80c0c610300543d40c45040542c0000d2080e40e800d02240b0703445412400c0c03141c0469150040c0d031116180000d500920088071b025101103200000c45042000c4040c40e03d24005481c0c8030070031541d94032580c10401744c10300c140003800503203041e0229003818001d8012020b8800103011643d038001c440c001094540e0401c803092403d41d03001a00410100303100e0f11032400341e804211a0811060790741c1001c02c000003c0090030b040d4008070450904241403048001d1500540d10480303400b241c14451400070758940c2112442c0e07404030724180104584034001e2007203482000a461071a04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 505182221 1250 505180971 505180979
    0x5010f1208180d1410050a1a0d080f0705070305060108060709090e1c020a120503060d0b0912120a0c030204180b040e0d110708030408150403020c040f0b090604050709 73
    0x10b0390141c641103a03a00407102d84448400604000070b10700143e95410020f108400070902d005c000c1e100c1c05004400070074074100740e142903514004d2100490300025600d03a4101a21443c000820344280741542c202e007030002c602d040c100980440c803042100d000d603040301c5640c0d803282c4030300d525104241e40c080081080e5440400108a00ea00403850440b24030b010381b00480303003500f0603200300a2074000d01c6c0c1c0180c022070f4a0004001007c00d00c0b1322001c58a01d072130f074107619001011070410040c803c8040c091200c0c1000003044510100841441d040074602050744490791011908001303242600c200c4070060800b503509115502c40d2013a9401c642c1034171248880c0d0340208003100c00404180d40e900303400640700c00966600000c1009031080c0d8440c40d03070fa0100302d05a202c0600b41081d0454001034a1904104010000c00d40001160720b017950b0210b20801c4103440c0c602d0142c2c0b42021030001140c00c141891040310040c0d4a56114949040c0e05403a44d0a0555829081108561080b144400400e05d6080240 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 505183471 1250 505182221 505182247
    0x150109020903062d0403030b03160b1c150b310e0406021201080c030c0108040c05090709330f0804081602060c01020901030e06090c130615020105010f1208 68
    0x700000011000e9902e0281381c181404000c803016008292a10070b45820303400c081002280700a00f00403244000d038184102a5031900c2011104607411034481138003094151590709c610b6140d0f445140c1e071032003903607940000360458000380c264226048a40303a19940001d880e1490700241042102141c60250422800c00402036000c6d000b601c0d030075824440d40b038903050f641909902030400310004109940c00407040514101c100d01c000c604100c505010b02001944c0c001d80c003c140c5004455840346680c0d10700d012100261180d0015100c0c155050040d40c0c01c0e0700d048001d0b81c4210f1000880b0b010100310361800e031000c0c00300d0000c010002d0780b0000010082520000500784401c044d0fa0010ba0058040d000100c06412150005880ea540003d5500c21580c162040c0f0100700c51240240a452400310f000342d86900c03181e82210702650a410841142c0d203403541c8401c01070900440f0141c0a0603241c10b00a001f041c0074010fa40008a1000c00415220500020602e081d81d00c25002072a10004031104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 505184721 1250 505183471 505183501
    0x6080a09110909100e0106030b1504022107020705010c1a061c0503041806080d032301031103300f040e070f090f05090103120908010e15010902090306 66
    0x40e5900d00d45141c61801c69900c00c2c007000e0103401036200030310507101e00e000d080303040f500d8645e65005140c2c03500c141000000c40503002a5400103140c134558400c1c1116001240181c842c501c84100000600b00404200b50844640316000b0507080d800c88440c40c1e04d820040d107542103140d20250851035200039441484491107040360b4099409805035008940340355409003444440c1d81d04484d550008a4140f20840780d042800789a0309000c801030104614110071a038942d42c610307601200300341c1c403451424050a0300000984071105030142182da40d40c4c2d00d08106804280000c4d40394440d000d028603100d900c1d950361140525540d50b004a03c1080245500000040d074000100201c0d422001d00c0005401589014075612415090700c81c02003204550383c2c001d0030a0400d070480103808803005405e0100ea16400d42d500e0542e81d01c10b004120a01c04031728280c86200c81030384202101d40c02e2000079031040901044400314903240001144250f44c88064800c141e028003400030b60903600510000b17211031804844 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 505185971 1250 505184721 505184723
    0x209040603021c050c0a1d0405250303111b01031d0a06060e070908070e0618070f110604050a020907120f060513090302071e0f0311010207080706080a09 67
    0x3a80540e40d5011401103030303058a5006007241c500300101c050060900000e10622002c82d00445003d06222150032004800d1101170315510341d0800040800800b00a00c0d0740c10103408032581d01800d01c180144003030003060300003180094002c0f0074070702840d24001031441c04074a20320200442ca022034070044006103056844030481c06500c650002c104d8400303100340907042d4002c400c0814501d08065103600000703005801c10b001c2014080c4104440c3c0780200c1da5400351000c8200c4408076445240004111412452100001b4000e806c18480990380110b8074031313103035101b503220910305140d10240c40c0d880ea90b045a024000781c00c02c962010040c034011030318590100c4103080c03c0c10b10082c940340b00000c449070103041c091966603507101801246080880d5485180418005002800d4207a40c002e40341c682602c2454241000210031303864464072400541c02170104d20340c3c058003940da42d0030031038061341800d2410f5025001b001804102240c000c1054425a4500e403070381345030341c1c8802e00c00340d00505079414 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 505187221 1250 505185971 505185979
    0x3020a0e1e150f100e090a0f020f0d050606070c031205072910030f02060c0a140609070f030510050601270513021207110102070c0303080916080d030f0b0303030f250806040209 77
    0x2248c82d103500135030b10240006031100d100c035a44458404044804441010740b070248030341e105214190006812440030025179902510204841042030001c0d00c0d10f00071014010982142040701c0c500c2030411422100e1403266510010384503403100403516800c5a8540000751940f403030002140058100351004081c2c0305108406c80d000d80300709448240d1207503007844085005400c003406000c004001000940090040044580610f500d0740c2c2c0e4895942e0441c04680400c10307240c0c00000c1c0b190380250381014030700c07402e42c02514512a11143c56019205a805080c2c40303080c00c031307100d01800f524a200741c510380c89403088101e2041d259441d09540568200851050765900ac210030701c00581d01c070300b51308001e6210b034480c00c1d05800c1c1107569a00f4102c40b18400703085820410350030800c018000500302c85400340d50400060440312610180058104c040c030458042c40008280009485c1141c04c0a200b21080034040143d042c04408801c00010705061202c00220000003144031842d1030b40c001c242082c0020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 505188471 1250 505187221 505187231
    0xa030602091801080d020705010810060c030e0604080d03050c07020d021309050a06090302060942070507030f030b0609040b1f051b010603020a0e1e150f100e090a 71
    0x2981102c1c604400342c0010603190040b6501404080c1c04101040150070242010600b5182140443c40542500c1c404c807410410081c1120003031600421111000800c05400650b07225122481c81c0e584031405c110030400203241c1400903001c1b5000c0419125120360040072055400aa03400300b102c9505a40d210501050b40c0305da200b000110204450851039226a00110303110906080107420080010a0000e40e6008200c8030000c081507082c2c840441546120b416040c0d16172648016450004001c0c40600380c48a0800c1c005a40e0f0407001801c2864800c2d41e07000c01c1c003041c0c2c0c1000c6065840809996400c6642848101d15038038154010b1505004007501d0f015140d0503801c000c1203500258441c910100b4000249102c0c140a600c1802e281e08001c0c0f002804034514650100341e60782c0580c421001d054909501003644c8003800c0021361000003095800700c04034240100d070114a0041c0941440c450b141c071103502140360512651407410904581c580702404180d000c20302c02070090040c40305003110b6581c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 505189721 1250 505188471 505188499
    0xd0506060c0a0609031202030f0c180913120f02060622020304030c200603060405090c1e03011a010c1205040b0414030705010c0b07110a080f03190b0a03060209 70
    0x820202000c01d000f4400443c12070201d00f8080e00c461959600405014010010011506201c1c02e105030025106040d503555084c039002d07500001007168050691201c80d030010300900c0c0103104051204e290280955038042c4210000035246a000040d070038000d0b801060005140d860422800600050f141c1c80c620180810882004c040b0385c0110313400c40108549240080c1842642242c0140500a10301c031400e001c1d1400c000240240001461540304d40e48400000b040d030034007440401c0ca4428054040110740e10303035402201e083c100c890340a0b070003580307810b211000951240c03603205003d04040c0c540301103c8565489044c4203e055548010078058100000030f0004000303c01000103000c41c00d6a07040c1000749208250601541da0f000318108042404c0035808651000d48058101c80700d410000311700003005070020700340444004090804c02c40494142c00c40900705000b188079866001c0246402001281c40030100c40b0805100b5401886140d07040c40003a0459009140c104c900070800031710640701c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 505190971 1250 505189721 505189723
    0x1090902210a12050c0c01030b0607020d02040207080c0616030b0108060d02041416020f03180108040c03060c030e1614190b0403061d0109020105090d030e0d14210d0506060c 76
    0x2d903002d510009040040c0c03080020b1428130132440841e40034602030002007279104c0040d00d98050a034000c0e108a620b1120541155500d46c100c0f08040c0c0e000340d00e0b544610003101e4090301c407502101c84680c525400840212094402d208601c00a00140c454455589880d0300303112003402011400c036002a40d440a0020f450780300700e041441040130440d860075211010100038103045580c4c00e01c580d0b0ba070061080f00300d06410303401c041f610040203181882c442c0e5924181003001980c0c0d948041e182c1e504c6c11700740428050303046d00700e07001c0005c1c2041116100340c0c0c40d68502e0401c0c07086200710b0f01008041c5070082c0580c5060412041454410b9000d2541a5110210b618481d03025600803100303140da941881000c03034001c2c5c28044007004010020800e011258001070503902c59101741c280301d4ac0581b900e5504042c042c480c0e4545050010703002400200c01894101e41e4694004c401404511500f002c0c407850780300035080c41d6049003229114a041500903c5040081c1c0781c090f010390307404cd0f01800482100c10f4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 505192221 1250 505190971 505190993
    0x1302041a0102071e14031905060609011e050603090c030f061806010b070f0303020c01020a1106010503030a020316050f0a08180904020607020132090901090902210a 72
    0x38149029603803420400002a107004450307444840562000320702c0036412803403509120210307034007040d4800e03401c9000b1000a00348106800c415a00e6200100000b0502500064107442a4002d4a03403890591301c0f903800d01c03024040c040800d06035144030082800103080c0134019540105d60722007242e2004520780006420040010a80500d680c01901002003001e401d27204a0540c580180242c500703541005007003000c40c81804400780140043c100d1070307800c240c400c0d4125121400410000c47d1070384a10f050041c000c9002800070480c92040300c001151614001c0121003450700341e50015850310048036074100321b0f151004025a00341c06403103001299600f0600c034800080b4841e01c0b08683c1c0e0b0b400c03246107585020140c007009000c1d220440400c00140c8446c1c04940d280ea4090900400045150059030382e20300e007038548820401040742240280710151800340401001c00c8806054581e01c0303c130f1b900201c84000788080c1d44800203202141c2c80300c1c054240c454a901d4841d0075501c240005440d0069519 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 505193471 1250 505192221 505192241
    0xa081f1109240a11010f02070b0c0a05070c0e06100e0616261306080402010f1805041107020126010308182205061002100b030c1c0b010b0c1203130204 66
    0x1181303900c816940180c2071040034451030581c4030860074910b83e134664212401004054408001c4e00069809147d40a0b03000d81e10840c1e4002101c42200e034584c0180c031951502a18024000c6410007121504540954010446401c001e041e880c1460a40c00c180c0d12141c600f180d044e140c2142d11995041e4a1000361354802500600c8074416988a0901c44401c1000a055001c08108482c10040c400141e070f00583c074210241c458038106107050065640e00354440c01c5544429842482c1c400c1d030407202841305d800740c22154000d80359a841c401408808a001d5603800c01083c501109000044c000180d1080141503031a1015500103614503510003c41c4242c0707040c0c680d800c8151140405212400704030b009483d4042e00590310800902d880c13080203581d400ea00e1200580c4261140c0e43c00805403030411104105040040c0124140341c100e56000000307903090307001070b01c04039070b003000100c1e09860810031210082d01490052103034510f400300e00c0450760406421401c00104280001002d80e655006029580c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 505194721 1250 505193471 505193477
    0x60a2d060509070306031e02130e010f0515100305011a0c0304030c0605030103060c0507030c02210307061d03030138120f060f0f09150a081f1109240a 66
    0x41c00d47c204400c0545201c141084007040c1a51407500686a00c00c41d600000d00002003c43c03107840e40451a80981400075988021520b403100300050160707981400100d4203020307248410041441c82c0200c041e10801d0042c00044030140c030303518803d180808010300c07030b81e043c1006030303401e042d01d0f03a031a40b02010240c0c0c006000a03c001c401030042c0406c2d8442c002060303125081580c6411130696010b090320003540c0000e4450440c11010070a100040441200c05960580c1a41d541c0c0710340c0c0c60300d140200003410340740c1b1405031100c450141c0c18400008407030581d1400c440400c1c440600c50b000c80f0180c0640411310b22270368000c0f070440e5044c000d25405445071040480c80a10b5929010a8864412030010821480f405a1780190702e21030301c900200c404d001c80c081e20004040d60782c004400c9482081186810780020701d6002c00542c110000c240300f0240c40c40a00076030100d1040b001300030243c0710050040504140200401c2500b8a05030706002c00b2a2666844d10000321780340e07800c0d4116500000491804 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 505195971 1250 505194721 505194731
    0x140c03040614280b18060a080a0f050606030105010317030903120106050901110d2f030318210d0518070605072a120f0c1403060a2d0605090703 63
    0x400ca80402d00030724403001d0f1400c100340f10103c40003918008803511200c000c0d00800c0301284c0c45031640e40b1b418006c0c04d901d20485043c110586401c00a080d5080400d0311103003d000003140d881e140602a060403280c012100c828a00d0b414420031010341e0018003082d856110410480c10b10712155881e5034000d0040e6101c0c1034035100d86900150201001418802242c3c00c44200c0b442d88942005500b851079020b5020705008040854207100a110041e8540c14107120210402107141d294602e0344e40041c0c0e00e02c0c25180200c0788050907102c8103801580814030038078140703d80c80381400103030702c4668011584d14020510703400585125003441a00d821460008000080440a2045400c0d40803480601c0b02100701d1450301ca040c0c183e80d055414051119540340c8064014280a02498200c1e0700e150810408019150756011400d0481a4044a64001c2c000c910001e46002814821090307185080d82c1019815020f008441c0e1025624201c689c600300c2e521400070030070361100c1c4205882078082d0381340024 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 505197221 1250 505195971 505196011
    0x504030e040e012a020c03012f120a0207050a02090a020a0906020601080d051309060e07081501091e170102030a060503030f2a0f07050103050a140c03040614 69
    0xd9900b0404104010b03030500c0c03828203a03100a403040c00b6036074212030341c01d1300103c0042c0012400c01402c000c0d52035140d03007880701d0426062641200041880c074010f80f19a40207801c1007042519000c1c0d9110300c10749403030000c0000c0e21000351b42c0041072128481c4050b0b849560550340050b10b0075900b82e4810341c0b060790200e008281241c00a03900009020540000d00c00740d0b02d04440c030b13581e0b100f01c3c440e050104032000c02c16801810882040750003a04c0c1c00e410601030310b0340741c0403400303940b8404139960800a1040004610011000c0c0071a88005e5010303959000a203051000c541410100c808103500c40b07074821140081c1c0042c0720004817014015000005d83d80303040010524080e94180d41285101e03400401500840039640c604035a06005e45c20425070240c00b01d01c1c44000640791044403445a40035280700c5090302000071440b1001d503007003600c08004a44072005c66908864500307201d02c4151040c000859400304001d00a180e205126210108501d0641c00c090402144103890041c0d1348890040d03508 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 505198471 1250 505197221 505197229
    0x114091806100215060d050c0607030221070201050d05090709020a0c0209331306180c14070201050304020f06071b0e0c030105010c06061a1c05070206190905010504030e 74
    0x1040c61410b51000b00707800c1c0d5400307007408140c2e54090710b018451803071220380b08100305041c41b49204d41c4400070304050b290051400e02a44a15005022280040320850759080550390141907420054040c0d58003400c2000c0d0700c07100001400081e000021500c94190700141143c404d000402180d407841d603032a10300111070b105000c0403d102421840e9090064481142c550b03610568280600340e520024540b668448000300b184c414019005203002c600f0b02c10701140340002c590780c0301082208003200b00326038201c460084401d5108201c85007174007582000204007540c4a6000341d0740243c001040d002d55012004002080742d4001c000460b0302c0401000001c002d00015818030004015a210105a03031034507124081c41413105002e13003814090743d00c1701c4c141031104591105024201e0784c2c00c6142c1d2500007802e0503209400691050301c1d0000c02406e4a4110303941c60003018040c3d0440d400400c595200e264462448844003109150840ea0f51180880450300900034640224080d4482d104c15032104001c0c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 505199721 1250 505198471 505198489
    0x2307031205130b2d070c120c05100509120f040e0a0b2121090a080304051009150f0c0c030803040317060f130e010614040b0d110114091806 61
    0x115400254004d03049007440c02c044920051103a100359403c0180d84a803002d070b800301e0a50401a044107c80004c000f1000d80020b00b12250901078411070340000f1000d045201a544220b480205603080100520400c41c2d2280182240e90007500e883c508054480750801d02d10041191701d542070b10703121605038003981410070340054401482c100144d40002000030644d50b0344111002d249039408000c02c0c1070031424154059a510030b4004102200f00e5944140345c43e034a41045c0079803031040c404c04003141003450140040ac803c89101c031804c002c0c003901c051025035007040410101c4050252031103101c0000ba590394144800740d4444c484c915243d043c07905006088018410200d0b60701c0030140180000399440004000c807040c0215944140042c0050414001d0151110483d407150700b8410080b840c030f603d80684801c50101035904010540c00c24040005008142102411000031040700c03c50f1035100d4851443c5072082141842d1420107100c002c030758003d1440000d0444080500300740004c0346041c5840c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 505200971 1250 505199721 505199731
    0x20a090602070608060616020d0309050a0609031a13020a03150b060c03030a11090303070f02090603030708180d0c06020a06050c27040b0409080307030501062307031205130b 76
    0x2d00402d410101d01a2440300003134162845608040703070740e03407400ea1911840f13130020b0f9002d8014000c60407a0f1a02400c0021a0700840303106440b1010040303001d52107480d1441c220303a0010755481c0211041c4c118030000c4000904a0601205ca00c450140940c0780c400180c03006501c203001b20007098000c40351ba00e0488100380c2c4407501c104801c001030900e402c00082a04d801c05403c01c000240545d440e0410394039841050050f5405000104581043c0100c0c02c1901d081c0f5802514801d20f95502d031740c10951a441421402802c080b01800800d1706900011424035100a0192000401d10000d458211104005900100040e403214404104100b560300400b600302001c9a221410f01c98900d11650320122042441002c142c1400302b02410790343e40303421401c01101c01510801012445041c28029540211003140101e81407200029400344100b40107401a14181c07580c0c11910202e00c0c120090741d0018400b6410400075000c100d080c40010303c6803502074480302014048906092402c6a000140244 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 505202221 1250 505200971 505200973
    0xd170907060905040507181502010f0c0804030c150f0204090b030708070b1e1308150708010e040f120e040b060408030d090f0c0b030a27120e0d0501020a090602 70
    0x4040003902d801c0303030910050352011540400c69642d241400c81e100b10800800d4494590040000038022000c980c05001c030701c0c40f0358000d01075404400d000e2004d032802c11403603000080c81100041c012a00c100740c410402403043e1132060802c0c01c1c180d5080d094810031804a070000b9030002d0100050100789c400c0038194030003a000341800d02d140c0b00c0c6058540c2c00038450207100641c0010039410760582c0c14010309484117510b240d95259800064030403007c07011400b80f40c406200c1d41d824054002644882c2600c106a10364890800360b080c8959000140c00243c000c444026a0311100340000b0b42100c40c4a1400e0b289a60302200f5184540030081a00c2e8250381e800e0041e5000c02c07081c02100000700480302c50b002c07a082d0100742d42c0319074074041080720f100c0d65001e08071007207030b42d0045080180c020043d80144e140c10000e0080341e200320a4180c40c0206000b9420100010040b00b00010f60b80c0c5000c1215507030b0074104010030700482070105407a506511822622658001130000803a900030711100c0141c4020702c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 505203471 1250 505202221 505202233
    0x40617060a180209120a020108010b120a0c1e03150b070507120309030f03050307090b090d02090a02132d060206070c11060d0e010609050c0a0503090703050d1709 71
    0x8010070503520340741c0a400e0000750803151600ca501d03069011940c550001401400ca1284040903494603400c0018080b03000410120002446141440a8414512907150b980b0070b00e80340c0a00c1d1500621035500c0e910203015001102d004801c0d210f8614007203086044c0c43c0880c0c550700d90ba03006009d440c4180c0204107000c400b4080a0003181c800101402980d008101c1c030f1248101900781620107190603400140b03503020381ca581108141e480805140210400d8503035a611a44031500b483d65401f4103100300d50440000703040769000d45050768841c1e401100f0000010326103011484000e9520400d90020140c0e0072000149003c415014414201d041d0071205100324101d00f450802510782e00007030810400c1100a040040c14441242c510701e094001c02000c0306c1d43c03000e034880d40c0d9010f80400006440154039000c400a1009064040c42d0700c2142214005846d0400d04c44054580b5000941035003420b1103421400b100094040001d1400ba6032913495800442e1806035280240080003003055445030480 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 505204721 1250 505203471 505203481
    0x301061a040e090a050715020f01020702060d200307022821090801151d07050d200d02090a06030b0616140d0f02010c020c1c020315040602040617 64
    0x141056a00340c0e00b2404004142c1d40340c900c820f5250075003040b001750507402059000500e48a807848461007540f2680c00b50b81d01c3d49802e4a0b542d00302d0040e000b0294110104000444000c02c90354024107001d1411611700010a510172418800b80c0c10440b000c001690241d0300300034294840d03042c02e00c02e400b00d07817400304030070840d56490090008105001c0006481d501c0e40d40b0000c0e41c0180303425806444030314000c20211010803c680200b0342c4500c9100e4409121071201e00e0300c4500c1441c0e06d48600504d444680c03500000401000043c804a40702d100302a00342e0a4034011034081070014254804c1c0810096125004d400400c0922012540400b003414907024008803603850700f9050740c00b800703c1000a8840c400640c00c0040700d450318400e0640381d81c0102c1640700c84990700402e91190214440e80200309203003080c6410382c2d40307110b0340c18655030114081c0d50701c245195104a0030038460344003500f5103003000c2d9480880038070044103490441c0c0150b000715082c80b96503841000c0d2162180c50350152038450030303c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 505205971 1250 505204721 505204769
    0x20114060d12120f0507110d08011703070606030605010515120601180905040507030302011a0306010512031201030b01030b0601090b18010e03070e1609031a06040f0207060b030106 79
    0x420070061014200401800b040c2d400741e100340e0600703058020280440c0c2c00c10000d800082100300c42e43c40120300c0440aa5021010002d170300c107840080368032525030070f90a1030a42401d100c0c440b0881381c1584001c0004a0000784035020722030003144100c901142550402d0100724034074107071000007a400f4406002110100e803c1c4042c107504041c081c2000c3d0030800c003003000f00c40d00c0e4019070000c2000b50b00304001c0c80200140095280b088900941c02000b02445200003841c501801c40d001a90560101d030050190349084181c0c02000810039044138604105035103c0308801000764816101120800010001d01c2200001c00d41d01000c00d1800410b198246450b0300c1080c000d07005070030141c0c0000001580241d004040d58032072260000c088a07000c030342ea50080300d408003027154900e004141d41d03480190071a01400d071120549500c80c13010740b1140b0100380301c001070a900414182d805901c64042050000305840204107403805400e01082c0c0d0114201810f09598041d401404035292080004600c044 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 505207221 1250 505205971 505205989
    0x10020a0203070b070302190503060108150d020105130e01081605030102120406020313021c020f1f11070906061220090d06060504020309010e0d18172b02011406 70
    0x3e48510304050700d86981200302c009000310140340001d000b01701c0c1f805580d0303038200c00030350720442d004d0361010b525a0b99aa0500c02d0b07805d49031007403508281c071814100c00560080c0c01411007551800900680d641c0d80c1c40d900f4200480030780c0002a51707009400c102080d115182d505001914040d03000b54070303085908030040880000180007904040c4d0200100b024000422020980c298000b84000c00c1c0070128001e540c075400c005a412442081140700d4044181810018840c4a405203048004084280d2605550140080c2102070150040000c00b20740c0c8685c1d03100d03100107010365940b0b04220141016082d82192020003840a10a011108000d01d14520341c0403662a035000340c80301c00c41007503180341ca0700180046400c030650140c0040108090140158000e6520920300c000303d4840450300001a1585140b00d240c00640300c10485040c840c25110110400c44c4092117411221010003a41d07284d55868000080c055026100398201e40b4500e509000340f20f030481003010b000c000c50a180b0300050540c2c07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 505208471 1250 505207221 505207223
    0x5040506060d031b050601060914031c09080d051b0c0919200d0c050408060609040c030506040b0a05010f2106140a2009010c030e030c060408030c10020a020307 70
    0x1c40b011400d000c0620079412a60315943c0745140c103086a00340e240090b04c0b00d40c00d009082c0054254000001d00d401c1d014001241d0000c042c0c003034555500305c002c445039081000005207007440401000041c800d141013100c0c4400040c1a95a19100e015040d0a803102400302d9a0f510410f5100d0403002c08540c0d1150074040c1c04c1200c084420308500304501005025041c1203520607020b52100740c448a1540b1424010900020303243c50810061b4150b103002c0ea03082c0114056450b00358084000510f10303041410341030b600203005100048003117550795507032131418900b10350403a500c1001c1c1040c4000c60415024503809003188000400c84903003482d42099024403403034110041c500c641404807040c48000d5000100411042804c4c009925040c05038030082c00d503103465660100d0750714200d8042c10461800340d40030801e0581d0390241d40c5c80c15450803220180c82180040d85401180c100040c0c0341c0d54080240001e04125020b5070b118860b581819081c5074000ca00711098038010001454821f0340032007160707109 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 505209721 1250 505208471 505208479
    0x30402030627010e010e070b19032d020a032007030c2126040b010b091f02070614070c030b1305070e040b060109030206030115050904022101090504050606 68
    0x41c030081000711201c21007008950352154605011104560410f401c05211b281c0850122050180c0d9200580351500c178038501c5400d6400b000c007942038158408d402c40000440700612407806422140381d481440b1203031034070518141d5800030701c0540b021340600400404180b01c1c1c04070100f003607041111510300d2013804801030030001404420170030001d80702074100c5407641081c40380000400100740a006203003003220150000303601100b00d070201040c2c000c01620039540044070034031591030640402c9441d04950201c80c0e1040b8186581070800c40e6501d4000002c00c61a4010302c0510f103000350140c85200784c0d04480052070b41c200700c40d1001c82c14407580d0008484e8010588031495450312461800d003004130900030f2050140c42000900b42c201d0040c254005ea0040c1d900282e03036199200156414021071000942150092004000c00d41c840d5441d14842802414042c4c0b0700040040080e00300d0b405049581141110310109900138005002c810b070141c407000c10200040c0c10700351a1103660f500c000b826030f841 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 505210971 1250 505209721 505209751
    0x10030b011701060f0e07090b090d02100e1e0a0e0f040f0f0c120c0501111b01051b07030c05060309030403110a0803030a06060210061d0408091504060f050304020306 72
    0x7440d00709601c102c000b44502c9110445494a0384003829070000240e55000002c2d68001012450002c03260848034014002400b041500310580e0921620142080c01c4806005912110640b0764032030b079001000103805240c1705803080b0024000c001c091840ca4000700d4410740d03003c0800001d0b104a091558005801c000780052030703042e610b0300d62007030490200000d0120301850340000f007103003001204811070744c0302d440d03038050b0181c440004460046070451a219039034040c0c20000034142141501e48074208041c5040f0f480c1910018485104a4942c00e10f4100b6a0214108205220b00710402d1030190908866940c59400c00c07099407a40ca004c0ca00001d400d0000001100300c9695811a8010040122109580d220301d02086400002d140710b10071318015000e00141c0e0011001140f0a520603501910030721000e03d0200d458081004c480140101d13800a400c1201c46040e0390b544503403101068811b00b1850f80e940c204000284103844581d030070801c4c440d040c0107202c01070713501081866005100b50980c40d8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 505212221 1250 505210971 505211009
    0x80a050a0f021f0806040507030504021f03020c01110408010507050405090c09130504080306040e0304050d2d1b0b0715241202030f0703260702060d02030f10030b01 72
    0x40080500400b90010408000c00926a078000444a110b01001c40c1c04020f548d0f550031043d0203075082210001d62141394282d155540040c1e80c10007c0081c0110714006060910032840c1600711b44003503000509656021404008104090242c2e55004000340b522604107807030003002c62510080a04050144000458050300c26201c085440c1080700019000b44940c0c10182040b010075841035a03204d0003941040440701060000104580803600c000c1c1c0302c10042001503c0b800d40d0140c040d55900c244030342c3d189003841111051800e0724951800343c0c0342d2010031044030409c410703410030660102c0403c6109000c0c00010031001a0005a0348100c2c0e0008150410701c86002e90a0651591500500c00078800011800320004000ea52840d4801c3c3d040b101c1c201c079500b1509988000500c4002c190007458a649210030000b81e50365401c1c074221464603030900001d6400107a02c0c2c1c0080c030b15800c0320f42e408801c0040c00d502d0404c110340c11010328954030081e40d05544a08140300b005000302940e0800943c4454 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 505213471 1250 505212221 505212229
    0x3051c1401030209060a0303020c060a0c0c031a0f01050a0308030a021e0409180b0601030905160b030601030c0f08070509061c0b040b060a08010311181807080a050a0f02 74
    0x119808561a0800503864800000d40e144242804141c1c002c200341000660301d03042940c0002c05680d0941c0041003002e80d40810404903038800000d81e0100004405458009285d90004201461007410308485101200e5801c0c000801c004080e001c558034850010407641d01c401c00c6550a4a030094403281d40da940e001c080310702a01c1640d603c1caa400e22a14101e40c16100400d0180051310002c0c00305111407203002c91040c00c00d0368640005002e0141080110380990300a5002d009124460340c10b680d40100c4030303125102c2910083e40900d4000600008121071507901d07100340306405c3c80500789802d01218000f0001d104e100002c20030f03420300400048254882c1c0d166010781e0b89044d00500300f181143c4113184000040c050018940d4080d9050030031111580c64000c1c00e40304202825900c0e103400380c0c699115081d080c81108125a0000420740c40c402d490004441c6443c40303002c5a11503030600210007101d80703140c02800d40c040c0d045074208890341b8000035400304a03401025000b02246400718000c1c0001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 505214721 1250 505213471 505213507
    0x20606450901090629100c1a010303090f15111915060512030d0209130501150f02060108251d040614070905040f060812040f0906120305 60
    0x81242488404101c011401500044680340c407070801070021151844241c5c21504000c000030160b4007682c600443d950400303c84c4240c0000481ca03008142e070040c4e84560703090340440b07440441c07103070350f0300340140240740e004402e40d0006d050609240450925103022580e01210b042951030800001d030300f070b240c425881000500390100101380c0c010032400c00c51170880640c03051032403411030003400c112000915241041994160700b0544000d103140c020b505039444000c0d4401c2001e01d42c481141d510a9000c3c3c2da151103058040d010036041c0010501c10040701038016400521450304640c00070f40117014000e400705150081d074481c5564200d54010b98441d05001a2640d045030580200c5a54510700c820300e00c0381618007940c01043c0c20828240b0218052031400801c440240200b5240d06040020307042030790001140c142d03280c00000f141d94403808403d0030000c0703211200481013404101401507500f080400c07030042001c42010009a4034101c04c46a45c15180d60002d000d00c03201264049040170034180c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 505215827 1106 505214721 505214839
    0x6020c1002070e0406021606020c2104050d020a09020a0801050112150308030402041b1d01020a0203071a070b10090b0d02090a110903150403020606 65
    0x3e420b500260048418544c2005500d032884094825024503520460f4056564107a4247c401c1ca003c446030881d0561509941124140c9071012007140c00302c40068034815a00081800001c48054065020101041c00000d00c52003580d440551207060391400d13202c1c80002e000701c5005c001203030964040c11400719011003050002c542107101859120b44000c0c00032500d84c5145242d06442030f122804103010407800d02c00f2090100c0342800ca25003552080c4001d11070320030107400003941c0e020940319404410b81c0007680c04507a06420f1040b5014260008020080b40c02c020407040d018070803500c56008400e141060b4030001d807070884400b64100703030003d109070709940312400980010812400000e95103102003203071210b01d450a11000402020f00d518019291400d82400307414808010711952146084d05020306503110a00e110080382138510400b1000c9030311500120100b0040599 = true := by decide +kernel

theorem cover : BRFrame.Cov 505035971 505215827 := by
  have h0 := BRFrame.cov_init 505035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 505035971 ≤ n) (h2 : n < 505215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
