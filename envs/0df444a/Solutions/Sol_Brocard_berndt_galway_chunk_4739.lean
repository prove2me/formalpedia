-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4739
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:34:51.349682+00:00
-- url     : https://prove2.me/submissions/43875661-e442-468c-8c92-749078446d35

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 852158273 ≤ n < 852338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 852159523 1250 852158273 852158291
    0x409140a0e011406061e0c0d1206121b080307121701080d0f05130b04030203062412031201031b06020a052503080301080307021302121f1205070302151c 67
    0xc1c0b480501b000801c0c400c5c0e0707a1701c13480d5010310302d902c54914410410008000342c240325031200203407066a04480c0207152840307041c03000c3c0e590403140f8035030414040e2412101c04ea00040c00d030810b00042c80710030310034250821b0307100da07060001c3d20400140e0142502c0298010050101c0c01001500f00c60f030000c0703070034a41c140410f0500b003204c00d44960102e81c0c030502506100002d00d18001c50103031064078800c60554555a45608001c000081c1c0154000c80500314501c0030301c40c80c100144018400003642082c1c074540807e005c41707681801001e078812100c21201e501c401502c00c10545101c1e016245510140c0a180d9041e110540d60f0848100401202000c4022540c00000c68024900041d503022480c0ca4503503030b45000740c584a820002080e03005100f50401800790b4601c510860300d00e50300c0c07211584c0c141c1c0c8804415252a50388941003807540320303c01b280030a0008424410062403841140100280d60941c81809a504000803542c040362606004903405402d103a2058130403d54215030005200305 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 852160773 1250 852159523 852159547
    0x6110a14240405010506060a0c06050c0906120106032d0c091d0114060705060411130e06041103070509130303090602120a110a0203090d02060409140a0e01140606 71
    0x14000d40700081d80c104203244001e00710440c000c41ca20aa000d03c0c020040796a4210034000c00381314540003400050811048180005c2040d485150810220202181000740d540086510390340b01e1035585a4054142004004039a03141c094807a55103007255000e4039210000c5028505c071441c1900a030442c0f51074882d4003480e03501c140e001c00014400c9015101d0f03144100085c0c41d003035690a00802000d008000d076000a2810a8000c80e042d880e8048000d1140daa10b07510761007500540f46124507405214034058200242c7c0a00481c80410b01e10406415281840d181125200850740c0002e4001d4028078000c000c1079907241c10080d0f0200860342c0441c0c00c0061407408a005010001000b00b03d07034070200746110501c2210001c680716018050080190b007030107003a600c80ca0f005071040d40006078004c0000b40000d0514140d52451280b01501c121f042c103840b402e40c0d500b80d40104424040002d0b0107010044e4085141c00b03160405e40c4118000c105c04030110740113a14506004080704e006000002d0724445520f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 852162023 1250 852160773 852160783
    0x90109090b06150f162f012f070306020408101401031a040302010b0406260f06070c03030209060409140c03010b030a1119090503100b03060604090507180b0a06110a14 73
    0x1076030043d60301211b8a80f8444800c0303182c90404481c02d81c0c002c2507401c2661940100c08041d2400c000c5030100001404201c034580b04008004088840341c040c03000300200092040c0050406071070080d016041741d404a1060800700e482d10f9070888e1208000000400c040740301680c6c00f000a803050315403510280d44500301640903169841a0315000740c500480004c1c3d102d002c240012681400c1c980c010760443c0c2c030b908001d941d00720a460800d1550400c50114410324040c10b0b10f5002d1510a00380541480000400074030300c1c0d005680304049142e207405184920303030140213040d580201044489030855050520180041c0001080c4000155884a44d081490101000c0d220b031401400c10340041c07001400e100405a1440d441003d000b4801ca9401d07030744080e214003801a0600e000b40c01050719545d24420071000d0705c2d500b04107460070300070300c1000300d4007510f48240c041070b6030070b102408900e2041c0340c2c060000780280c9031311a101704407805561081000000c80e220f4182c5410100200203808031983c050300700 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 852163273 1250 852162023 852162067
    0xf010e250b070813121529030703020a031202070f1401030209061204051b2b0303110307020303011d0c031f0b0705061909080f031005090109090b06150f 67
    0xc01888140001e91402c94250748106501c1030b000551689a01c4551b08182c502540e6920100c41a42068003c8220215400e402e01c000050454045941e6034010030303810500c0e42c0003603681061200310416203c0e0100216030007040c20401d8403030380302c0c6402e20060304030540207a007904064001850101076a180400e80300300142403c542e031028200380c0350031940d583c3d4950318980007840707440700c1582c18542070b1404803807480701c641c400441550060b0305803410700460320b0403418591340d44a01401454140040c52082c00d440d00299520b5050a5024415540031641a00e00700701741ca08000c40d000e501c1c02603c0c2c0002009040029104041c0d03044e520100040e0072031000014040740e020140000051540d02802c0c0e85030481c48543c0d100c000280c01e8075034110024101c02006c201c40850100303420000d40e071048a190300380c0305d8142c64070001108010300781d00681150781c0302d0307101070103101e5010290398201808507800712400c1e10015244650703016101c0781448000c4040f400040c50110101c10681c6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 852164523 1250 852163273 852163297
    0x206010b070327080a0201080a02090303041412060f040308090607140307030906110711040605150309011404140105182d07030f0b0c03070e06031302030f010e250b0708 74
    0x43ea0791200900d035901d54059030181e0024584001040100c41c092080710f08481003d006145054100848040c1c003544540d0a0340d00481280050355483e1070620682d409108908042034050500d428001d1400c0c0014017042c1e001d400040038000c0030781c3c104d006001c006040d00400c98595880207001c0c0c0007020800b00c0503102d039080c01c0b02c548160300090300412a45100b8401d581030000d039042403000300c42d030900842c0e070090004240d1000c48082e942c0a142d001c49120004110308110700310ba01c40011302a2001ca82c00d9040201d6541d03420420b0182e2984100484c030708845480d4140744040ea0ac0c1c80c0654150103016006c01c0c044040f845600c000c12101282d0403c81d95065500e15010f02c402c0e045c0c9005a030540b44142c0803549044643c82140e010b020184c0c0d5107164020840c1c2041070030780c4042e00c02e006000c0540c05040050701d0501054284943c01c100019000c480300600c50300380403e505a080b0a07030841c442c406006440c210000e403d455500c00d2954446901d07103440f203098804e240d04185 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 852165773 1250 852164523 852164597
    0xa0209070509010f020a0203191704120303111201060f050c032d0705100b0d0b1e070c0b042009100f0b0307050315041b02010b100206010b0703 63
    0x100d03090700711008140c111400c0c1d0340e02900c0c1c441030000701d07151000d4841c02035264101e071012402007003035415000c903402c0c01124600c0c1d201c00100035641e00b6521540c482c54410040d1000e480501d0b41501c680c01d40c1e011800e0b032407841e1902d862900005a0414020700c0140500c0b408034014543c41134040e101c03811f80e018102e95a8840401e036810484a04218120300001c1015034010740c140c070791084d284a55408401416080a01d40194001e001200740d5a5040003a0002c0400031801c90500c260145c403041c2c034584c0d1001109003031107451281c0145a81e00b070028820000c40024101c11a9940c8160003108041049071f1030030101c2d0a04801c2000c1c980d11200180c14400070340e6000c2540400c480600301c8407d07a07aa9030307005c41c0c50f00303000480e90000031460900008800401800040c0780e20a030080001403400440410706074085000074050006031365410480501d82170500040c1000c03521800140660340c500901c55041c0c0c4200040102000506075110110340c4103807100c071903003140c0543c20304 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 852167023 1250 852165773 852165781
    0xf0b16150e070503060105030f030a0e03030d0609050402150f070201120605150406110c0607080a020708161404060e0c0711090103030507060f090c1208041205030c1506060a110a0209 80
    0x255881c9001c0c00f0b198424090003000040e50301d03000814560004000010f10700b04507200405441e030181340004550940420002902050841d10521b4040c0c0190f4000248a0400303006100b00c51184090f11803400b102000440c00446448040c2c0314541e9092901081c40340451084501800e00c5038001908044008a84100540340a001d442600c120f40d40303808010950380c0150f582c464103858041e800140410100d0086040807009180720b59180c0100c0d840d01c1d41c0c0d00c10300c61038081c06011a000901d40300d2404e000685d03491b915611492011501445981d0610401480100b4041d000000030140081c03180100450300512a03200e00b4014031900b80c560703482c00c0103010340d401440f08850551906a408400c00c45910410308143e41000307110100b01d0521081c04042c9030544001d45245d6414800021018400c41f02030141e00d100328080c58503002d40081603440e1a175107048401c0d05034910001c00c25980ca407407050740c01c1c001c058a020030b0045040400c8500302a0b40d240d01941055100d0100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 852168273 1250 852167023 852167051
    0x121020d030809060c0711011b0c060210060611030a20030c0a1101031b0503092a09101a0d1803110715120b011e090504060f0b1615 58
    0x6070300c140000e0080e41d19985e104081c20655108500340107003400204c007030848084d44076000c0481e0f120f500d40401c02ca01c803825101c04482c20855800100117901c4414680000000d43c09403200420725424400e5105440b0540d180d01d074002c5c0400d01d01000051343c1407045080f0042d06000d203200c18402500c3e5103203c000c00182d16064546010303a800346013010030007003d512038860209440e0000b40400200c10001208490950002e400345020b8440e0b01c0d4050185040c003613141c0381c41d8800c0605150071001c141c2c103014900c3c900810304000040e401034100500743e038602e541c0b62081c015140903540c40b0f00b02e03c8170b0001000301d0100f0b07141d41180c04840008058002d68110016042107027143c10040d40c1d0f0103c18000f0001403c80c500044103540a1040034000390044001c1c90814101000f80241e40a06c1c14443da04031100d0100103540c036a01080f46d4146803040402a0203840c4011081c1820203c00381c81c2881010328609080320406840c106010708a603040c0707051505208180301c000319451f10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 852169523 1250 852168273 852168287
    0x50d02060909010f0518011d071e020c10090503060a1e0c110c030c0f040207110612010314012304060b190509090313051011100507020f070602060121020d03 69
    0x6083c024407440352401c0403204841c01090489000c901c0d80003414100c14071034103c18202038100810f02400780122b0305d1210300000104003e01142e0f0041c424400c0301810400349000c0044202d05001c002c01082c8840e8801250099110701e00b4200840d00100001181740025070354140302c6811458103009540032588040b04003a6060500f040314400101101050340320088408042d0b41714829520800581c20180c001d4806980900781610800c16540c0c003207100e980c030804945100a08000040c81000b99070b0341000708810040d00200b11000014650b001210220038011003a440030340d001504100711307a000007451074005000e00e500d808440c90b518050080c1801000d224811510000d00c49610010030780b541d01c0d5061540d11019880c06042c0964242d079840110104030781c03015041c0d040c3d2003c0100e0342060442d00320015551608000c0281024900742034400180c00c85841040860350014295056418026028606883d002e034131002010a07014000d410441d40d00d4010149508a44 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 852170773 1250 852169523 852169529
    0xe0a06030b04051302010c290127140a0915020f0703120c0e01050f220512011a0d2d0623040b09070f031202060601081603020d18050f2401050d02060909010f 69
    0x42c0310b40180000701e03c0100740e50440300b1044000303084bc0e00244002c001a0170048846004582104155440c01e041d0b50aa0380320501001c0c400500203000d5013003581c440310421420581c0002000350301c0c0307041c400070f020484e502081810404d022a0f508181c1c03110b501180c030009a100d0705e400e02161181e2a20481d200c0b248a058860001c50b4080040c0950600810a840c14580007407100c007230844040007994800342d402030b1905150310b940400c02d00d40441c5010341150000c1d2090b0a12201464208191030120017000c0050349140c0c2c0c50304000f12607000d5180c0250740104210002e80d2940f02491401003035900112044031007070000070034840d04401c0910408100c0d03007512441e55175400103440c8a4019a585e074420511024a031840d0b91003503000c1c181c40780d003106000c2100322207107000715860310344480291041d4000410180c5400720800030000c1a030202a003448584003040855180940148901401040c02d0141d6804540c3d40008031842410001d10b07070700e425616000410441f0300c3c140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 852172023 1250 852170773 852170819
    0x103080301060c14011e230103021e210c0402070f02040b030f0313030b060a061b030302070c15090e190509030403080a050307020c0102070b0f07030e0a06030b04051302010c2901 78
    0x50459685040394400c0a4440c207d2181107507540d910311f134240080c0d000e204074079011521041d88040625550041c1003c107120350204013002808088a036a400c0c82c000d2014244035601c1084041c000440189082010380e4045400003034210400c40480d0070510804240e52090000040e44842002d160f40c060050300c3c040c0700d004400355a000144240038640d13015180101d141440381d402e546204d12400000c280c8686405414482c1c940e031682c10f00303161500848201188950b400105075131001d0180c0050110754001d001a00741040e034010203000700903030740c1d80c82c80c1c880700011007401041080394001c541c44841503656500c4010010501d410964420b0014040c0e450300401c9503100107004010b90f020961402d29140012400c00c0055000107001c80c1400101d2701400e00c40e03550001880010f2400351400302e2243c11120411084076001844078003041440d254801c00341c0da021400208240d80244d007882640143c01400454500035614498141203590004c200c1d0a074144181001100d00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 852173273 1250 852172023 852172031
    0x905070b0a0c05160e190e0d0504061206270603020d030507030f050a2f07090213090603052d030a021c030207120503060f0312030103030905090103080301060c14011e 73
    0x51409004d08000c0d441022203d1208101040c14000603c11440031031003203007000035440302d642c2d15140c1090040700030000440d5011030204038068001141e45091482e883c01006040e00b0000c0c03a0420f1950202c0c2038100c03103d100040c822410007170744140059900117141c1c00355480340340b400404035842454214001115202114001c0d030040099030804ca0310b0340c0340c3d0102d8151a0303400c9034608a400d4420b03120380700383c0b1064943c00e074020b00000010780103082c1e0140c1c2e680c600001c100e0703030f50390b00354043c140c40352910380c082002c5040400d0540800910f040c41d0400805007649280840c0701e40310411080340000205900c40e59000140784034803e2003812082603180142005608900032080d0140604420b0300b460b08103648034500543d808080280344440a0b590803000c0f078a810301c10b510301030205000100500500d40c004920724000c041c00c5030004842e41c11503480f09900d000603c40c07c000d001160280c00100802140c1c1c51791004c501c28000c2185181503001100e11004003e02e19110501e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 852174523 1250 852173273 852173293
    0x90310060305070e0106080703020304060902060c102f03091f0903090504050421020708011418030a050a12020409090302010903080a06080c21032a0c0f040905070b0a0c05 75
    0xd0203103e45e040307038060b0301c2d40b142541e00e1802c1500030b0b500003882110020390f84c050920059032031001800c4007441c00e60040c110445080404800c8a1401e0401602844405500100c008d0700220a03600030a10240c410740340d13110b00d0400d80c68002c400c2c006940600300c0c0032044414880300c1d401054268060b82c1c0e01100203607500144030071210b0070b46002e0002010700c241c0d04c03c18072051028003d140c00c540304544c0c1c0d4603500c8070f0032400c480064900c840c1d600c25a1082c40941071a01092888448500016500d0145403400c041c00c940328008150052125a1390005d000040f01d606840003403095120610200301d1030f02c0c00038000d05070403a0403400714030a000880d522800070300c03506d03043e500458000c184c0e00034a00100240d411213807442d1080350348281c60791840c80900303001401c0060f204891240c2c5084c1c01c0c85035000456204810708100e0341c014043c100e40d83d910050510780f03400301541c0001c0d00302c0040c10b2040c1441c4050304a4203901c00c001540d0203030980c0c401001d051441c0203005403144501 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 852175773 1250 852174523 852174539
    0xf06091e0b0105040e010b1308030f0c07050a0b25060c030c0807090f090e010f0c090e010803030702060705070317090c1e130e07090c0e0a0e090703060f0209031006030507 75
    0x11354084c8400310020000144500010301000340380f11107045a0f00e140d403641d902d008500d0b550100c140140e021401142c0954001400c02400003c1d1400700c03000e851181c100f150313049a90060b85007401490541101440d484180049038602c0346421420502c44c4040c00d03d8003501514107610403c00050030280000c20052140341c401c000e9500503680c4c088050b140c01e10b40d4001c0c1103031034041c0900707540c0c45d2000054005076100f4070342201c420780c95442242d17107008010a1804016070020015800800c100192950b0201700941d101d80c2606059884403d44d00f000c8603505c0c000803040307186803d050148403007004001a40380385020701722103809001c591290f0243c0e80d8145c1100054220f0040d00048882c2c4103030b50401e003080e201150072078103501d55407468001540c0545540c440843e0045040444a0501030341d0500908194040311041c1c2c1403500c0003550b280b00d10310002c0e2041d43e68a8440742100c210707404a90480c84000c00b180e01b009201003009000701468402158144039003000020606 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 852177023 1250 852175773 852175777
    0x10091d040c0e1306050a06050402130806070c0309150527090a0905030f090f1f020c0915130609021b0c030a020109120501110f031e190f06091e0b0105 66
    0x2032a2a81843c00700041e50f61000a4030f4050055840540ca8000120305621284050300c04e880600d80d0814a80d03140410301e40c208100689414100042e1350600380c08a03411107100d40440d00c100c850030503078000d9084c00b01c90074025400001030b081c0642c03107421300140e900d04101601510031074400030b99880d00c0044100b00e07142c002d00107240d90810300c20011a99001c0024000c0000003a000701c01400300c440000d034900c42180c0820701d8680c8281c8400a01588c10041495034202c16142e040e064100407907010000e00c00d078600d1500c41c0d000101c00b41102d00e402c0d008003009000030b04066444100c15084c100d80c016082c0d0b0440218410039200c002d140c500080da191031246c06840b021401420a401e02c9176010f408801504c00d036494400c03040c14144410000c0207000100f2152a407281010103841c161480354100041c0090701020a021503140e0140b01078242c444088000a04140c170b20428002420140d404803141a10b420b6200c0035885010440d00305c681c1144000300b103210030303110041d500c034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 852178273 1250 852177023 852177031
    0x120c123f1e0e04180b100501080f0109021809090d0e060a0e1225090b0a23030a05010507091701020f030117010207020d08130b0c030910091d040c0e 65
    0x801400c80614494000c00250a100001400120b203201512110608004e2103003c211002da501c90100250a920ba0104202070902460302c0320b49030034514a141500c0006000d042c182a40c0003c1c440c003c00d2640c00c1403040752502600b041030310b10b001a0121303210600d03441c180f00440c00350495401035140103021601b031600d1644030f59590419030820700801c02402980e141c0148600c100c41407000000d40c41c2c90300740080590140c4070180c20410072a083c0c032103d5201d0b03401403c0c0014107110364800341c49450003440861620300e84c10002a00024900482844060165442d02007409801d0303a01074078036415500e41060000c1494032410f080c900702e115200210450a07000c0c070040c411000d1510b05010340c06042c2e0009400e05282e45c00050589450701d104940100d80001c0d80b070041011964484010080d4002c1e8a00780041049100d482e03200d010440d80c0303d4140045c0d5665158040d00319240a4610b40c1e814100f0050340031a10007020701f060340c064030041c40007100040c82c00c0c2d100203007500c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 852179523 1250 852178273 852178307
    0x1508030301090606020f19050304030812060a0b130b0904021e0301090b0109150804020d0515010515070f02061b030703030b0a09180609060612110a120c123f 69
    0x2460741f2641000307a1201446078101c03031a0008100c00400b055890025068900c0309100a0209040140c01c00c107250180e0b52151040200078407211208070f410101c40402c03540070502403aa1030400b800028000d00c01c0444001107258600829424540d00002550503a07007115400c02c0501404401034409400340d20642011500b25030342e511542e0711035442e4641080c80903000d01c420103100e958080c00c4c6115140404104a400d2004200c0c0d07250400e141d0f401c000141161a14121050b1180c101003000d00602900541c1c000036803140700c80b00665034001d070384454002e40382c440e500e614008018000d50483d2602c2032607041b0002c06c000c0c02500c01e2081611485954124108080c0c1d070b5900940b1030b4034001d8810f00d60700c10000880005000d941004980b240c00c10044010036001080440380340341c3c010041014003e507503100024004400c0d40241e641c400f03c0d01d00424450f25202e14054200500d1845032000c6c41c10b010306191007044240b548041c03440340e1031091740d52400200c501c8058906035103a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 852180773 1250 852179523 852179533
    0x60c04030c1a0d05090606030705150a1803120c150209090609040302010615020f240613153206030a020702150c0f0d0c02150d1508030301090606020f 66
    0x7001140b4502042c0078280701c154810b0030018211860780883e4002c0322402d0094100300e003000101d1500b84a0800640342c12103507a041c1c000454501ca055000e00c19a0320140081906412092540740440200450f80040e50703076054000410001c1403030074601b10484a128090450003100c0302d003402a1080c1c404003400007252592002c013009400d000c082c2c0b090307040d55640c0b100411300000e0f44204001e400c240f81c0060189548044003945042580550030b0420000c85c6001150004810355407038010408850043c1000100c5100b400207229041000070500e42c9584001307416202071620303150310741120228042480c00f070144440c10890498000707510607001c100184201203964040d04c0348a00141441c800380c00b460b50b45d0603055010100400c45d0340d000c00035400714050300300800c029410083ca00001843c1d0702d80c2c0403a00c81552402c0c25107864202140e41440902c0580c4406403550010030b0b00510315035038055041d1264000c1c010200141d007403050114429000107040840110400002d00d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 852182023 1250 852180773 852180779
    0x1150602030721051201030b090d02030310050d15051023130e03070b090a0b011e0603020d1b03150602120301051e100801060e0a06050703080613060b0408060c04030c 73
    0x510003040d03d6500c08103000003030004400c4a0382040125000c1c51103501da0840500340700300d2407480c14418040282c1194020820004941e91070000305040b95003e503060540f46080c1e00d4040340e80044d0164180323055140400b0071100320100c0c140b81007113907241c140c0c0c460002c000c0341c20582240100d6448a411100a084442225419a21004580203001b003500d007003445590700c015075480300395110700d40c1380e04c04903411040c172a00900240c0108446120f004418181c2c00c00d120594115202d40003d00d40d01168544c201c142035000308440000303068902c005000d8840018004002040070840d030390109034401f03e08540002441d0302610707510161142542c1c03900301007044003035031008420a001d110407001c007800d45401442410480c0d0302d0b11104541d60502500034030f174407060b1580c0741c80380f00007110420115030448111008290580b88c6550b095403003e004c14900b00c41c009141a82620f01900014800c0c0c40c1800b8005503800b070001d81d0001d444000d07c0904c03a0003139000251101550031020 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 852183273 1250 852182023 852182063
    0x3050c0d051002040e0414150f04110414071103030c0403150b0a0b0d0f050c03070c020a17101a03070e090109081b0607031509180b0108011506020307 66
    0x4050200c0c401c5007114000340e16450418140d811035809181a800c40100740010080c24034007250341080040c0007030220b002c0210021604c2d41e0054010050f00c0841800b040a0008aa40380065120094418006003201c0703940c0920f10ba0044034500009680c56066034591100030040b20b008000030b0004509050035510b4980d5020708003408800500d03640e06800307000c1c0d2118a003d0008144891000d51a0620150305005580d201c411100745146800308101d122180902900d030058910728115052203064808200c0d01d0f80940c00511076000e4040803400103450016010030300c4807400b80c0c140141401d41742c40b020300c85607070101c070f6615400c0038006006544039407032101d522041c8100045900e6842d600c9580081e48800103181d07600d544074200c085003060403c00d498100442e441c081051400c481a6072a001e00d25024010315151904009880050100c4c00b01810070382080780a029540d494406074001c1c0115400185030341d104c0c2600140c800d00100950320040c3e005004101801d040c13100c6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 852184523 1250 852183273 852183289
    0x30912050d14010e01030201110d0906080a09063219020c031c02072a0509070c02031c03061706010315110a02151b0f0f090d0309060f0903050c 63
    0x10303544240d5841c04420040c002c1e4035242c600074220440e00b80004d506500004010410355108503040d9800584110542d82e03000301035208503a042c0c505039407140c890110100103460142e8001e010682410400d1a039030b0078071000c503c5501071243c040a1070080541080301c4c1c48404803407810703444041505080e0750180d41c0c1c0042c016031203050140c03803510200350000965868a042e00788030680d400310343e4004003c102094648480c0300c0b14104031107180c03001080103500409000b2240160729510200b0809401910b40d040010390080596034203440c0900701c10020304842c00c0100000e41403400010700c07401e150401c9284c1d069004044d000350b07804c64564a6480307910105c45100640e80d0282c0881c01c049041c05040700409650141120040040781c000e01c00744013801881c0a0610030040d50030510780d02085032511040646a180c5459210007410b840e80180d4010365040700c0d180f4020f004041e8007020113001e442003516000b204a088075030880314264136010040160b4030568400000d0324010130 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 852185773 1250 852184523 852184537
    0x9011703090a1401141620040c03050604060905040305160c170105091b0d14010b0402031008280b040c0b0c0d030506100c030f090815060f0103091205 66
    0x2128075100600010920469459110900040e0644095080380d83d002d48581d000d800350185031414000090124642815100c800500030800e05407980240e0741e203103840034006840103100f00681101c045008d800350404640880c480c92034410042031070720540c825a4000e907050303a10759060500b0590f050280c602c0e03201040d1001e00000380005180d10352805c0d81c036503450f41c403000460b0a040072010319213040503d0201c4804270400c840d1041064682d0802d107000146c1081510b59400c09806023540148807440d05680c005000004000301e02040c40800d00c00c4030200e900f241e2486d14441141d2218543c0748000c281107442404442010414840d066600316010b00f0300808855903801040301e00b03501c501c5212000d0740080483d0840103030940f0810703078000c2054640c83c2e02034109400082c09103c0d2080c0080600c509041c0c003509072842800f03040f002c1e04059048600001c1c408203c034000b08021150316100c2e103070301340007030089511900034144c5882e41710360b50624a5498000607102504400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 852187023 1250 852185773 852185819
    0x603030206011a1c0f0e010e0c040c030209040c0e1e010e04090311010f0b12030705031e0d02040b130b070c05040507110a061b0207140f010507020405090c0109080c0901 74
    0x201c10000044d402c8101248901c9000600090181e41d00301800b00380d0303500310244055a450101903a100301804662120310700000c80740011a000034100c240c0013405104100c2d0b4100f854000c00020302500850b4142d41168203c4484005140c1030040058441d015001c031400213280c104c42d403c80b0304060300581011440307414103000046075a01c0c143d003111000300d551707501c13551030b00032084da1400c03d800301c03282d8512020059841c1800c5521034035a01d00c9001c0481511003440340e0419400d05400c0140d40d003000520400b955038540c0d038481081944c1186080114038407240c44c4c00180d048407030048030b081c00c2d0700405001b469460034082000418000340910b0600400006082c100750050190408a80c40307040c0c0002c2d032907400301c80625008001c000b0803041d0361042400380300000b10303096000e644480850302c14500c001c3c103d00489070f07406260002908031b42080d003070000000d0b021400560503202a42d907000300c0e66941e24080d64801c0d1440c0c02c61b420499460043c02a01d00d1f00060503652034003d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 852188273 1250 852187023 852187027
    0x601121e050d030f0c05040b07020904110901060507110a080a020907090b120f070e330a02150a060501091e2705090601030b0f060111010c0f120603030206011a 70
    0x507031655820000e20840a01c006a56621007204c2d44405206841203060a444c001c1e003058141007110f40c00d4412018081d2240da4800005401c10a08040d1a9010b0101330018040ca503980c1e10060041c0d00880d00495060f842c3d01c0f4080704908021000b4401c41e46090020107040c03032187c09010390b4500107000b400401121810103d41c1c01c0c0343c0340c003c01200d440070000c410349152440c44030f907090101403c864100300141404802e543d50703c081540c4000545050b000c2c461f450301080092454003105207048010000c100e5043c070640206041ea03030309091000c00130103656480c5450040307541a0007480e010031740c2d80e4070504c082c40c10810581c4841092900e9940115184c03031030700790394550f407500e10020541c080d5105d9542203164058140c100000c42c00503c0e44d5410b6a0f14540205001000107400c842004005040d42c0c3c442d45800d4a40165071008002c0840e450b50000c243d00184078120012842c901a0420f020409203e0081103d8050303018042c50b03428441c110b44000e1607001040d04035001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 852189523 1250 852188273 852188333
    0xc021209280803041d071e020a0b0f040302010b0904050618010902031b1008040f17090d0b070f0c212109020a080102180405060a09060312030e060112 66
    0x20311101030103000b40000650315036203000c0c0c890141071844240d0460341c000841c180200c15401003403040d03080400000c03110000d1401380c0c04034604200804040d001c107490f5802e01581e0030380308000070b00480c003e034007c1c0402b01c4420180524403100b0382d0020515400740340050400d12030800c010f4404200d00001107015071071900041e21780000d078041d0040d034010314101c240c2c840c508a0014082940c00d0309141d1400d03d42520380d01c0388400c40f15005041159480c03034000d040c0a03040210380d02d960700104071300510341c07813801d15440c140c00464101300401c01c0c00002080300c6006025540a1551180c80440210b500169441100940c08416030900c94241d0821068120221707041c1c0f91840704402c0000d12400300c2c010454009100da0100500d64070402248020000c4028040014070301901c2c04100c1c0d882e14404120000b1285c0c0c4440b000c00d142003004000c010244044020007000c0d59030a1009400c0700114a8583c08280314510340b6180c18445000014204840c1c07200e102202c4c1b02000c1d200740 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 852190773 1250 852189523 852189589
    0x6070f030b180a180c05060904020d020c060414010212010918020d12021002091f050409060909060e010204062015130314032e05060a0f030c021209 65
    0x800d0800040500c2030030100f140d40411031084030100c0d0000804c0c0c084041080d04e8611111820f4000c03540101c900180c000007503200d640440d40b0740e840c8050704564598840320502e855050503034081754840c0e041021a0135070b5005009035080d6920341d846090309a4a050b1510008001c502081050403000340c070541c0141c1c0c0da0384c404142003802043d8030170300c01020300e070002e06000d01131350107400540c414043da465944030406450105100c1c08042ca51210915000780ca490140340d1020508904260000c2100201a0000c003030203481003000740024120406014242d000e240650000200c01240b840200108011100040300e0030506403481c0e003407900941c4100c00c0c0c0c111060150b1600c807580d00c008241e40040072411041c1034540301800c0d418911181100301c180100061414000c408003c2442c8400000290091400038651a5690a01e2401829611145201e100403a240500340ca0505002050088400c7c0041c100c45181c5083c1c07c003005009041a6074010450441400c2e180b261343c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 852192023 1250 852190773 852190789
    0x3040c09020c0625081609080111270f06031b0412030206130302030409020d0e0d02010b1e090106110307060c081b0405030a060b062118010504030206070f030b 70
    0x300103a0702500f070b1850110107144a501801201140c1c001c4003824070740001d80c2c045002500600b001e0400c504100300043c04888856654019100079460070702c46071b403468072100c0104000c2d0307090f50000341c10215004800c4d03034062454184c15040b096866103944180b810100841d40700c001940e2000c08400c0c0c0e0300ea20902c0b40c105400c25013003600b01001d41c07010b040d01009429880420120400304482c5280d5000f5264081c41c440d84185640118544980c881581c0041c800100040206d800385a000c5200a01a10041c1200e6000d03403131540064000c4480c01114a420000141510285034a010011542180650100e0a0a0000b4410350300026054003c411100086c1d0b40e1b41c04403424501140120b40300312014a072916101004104965180030801c02440c07030304248006101e07140f440c082000341c42402d00340212104190315000604010610342ca00900070103000900384502c9030042800c0f40c009450190159010030b000401b1503114520f060155182481e0109480800e440410860 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 852193273 1250 852192023 852192037
    0x31709030403030e060c070e06060705010e010c030b15030408250c150c0506040b0a090b0a0f060501030c0e1e0d140d02150703091109090115050306071403040c0902 72
    0x5030400201001807550065684100390021581540303005660110140d540c41603100e83d01007000a14005101c2e5600c04007a640c006400074000d010403607142c10514001c1c001d040d00b070004207117482091041810307c116407a004074601000146903403255101c2c00c920740c02c80d060146a4099a580444185c13000007684086d881c0700c2c0000c403000c2070038010b0307407030040700c1c0740b501e030001c10000c070080b1800b0a0000406581243e04036084010315284d0074003510143c00005000381c02030114406011036014540d101c0b103803c1e045d0500c20001c5a4031040110140c465141c074580001d41c404c14100a00c0c41c0007120729510044114028007590b01550200301601b45d0040140c071b15000b400006940c8410901c03955030b01c00114030107004080351400e0710002c4000c6c06000c8800301507403000400108030030248000e030084c40c0140080920f1a00124050103011082e40b03801c44c440c010782000607142800a0f119000702d0030743d21010072000d151013181c5a0341d00f004101303a0307200e0031201000625070610310040000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 852194523 1250 852193273 852193291
    0xb0d020a03030e04110c0a0209041406041a061014031005090a0213090203040b0c03070e09010f06230a140d050a0204050a06080f0601120905100510050a0506070b040317 74
    0xc064a01001c004c1221021042002007200c00c0003590400140071401243e403580c12174000400b0b403a42e04102d0119503503154014000d214410600c800d0100c1000710010443d0f61030074241980d40e5040600070000c202049180c00b0402a848507654211100003840d809184180000041a5100d002695694090b144902c00d545e0000395404070300da40285910240292503000d5241d810700303589940c04940000d00303126000b0f5000c404101307141d104100d65031908078000c0031000903513164850342c00010443d00c550030105840304020006040000340600a00540c482a107080020720841074036013444016090008c64806c03c03020181c8403403841064003404018034016190741c2050180000c2e5140d5400802c280040d800412000000100e04554000828a8410545c214049818024140c058002130031409610000c40424180b60b1109200d5402e600550780d400e0380c1d5505200c0383c449140140b81d00458200b0500010904007081c4a401a00c40c2c501050300641c20720220185410a5506500f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 852195773 1250 852194523 852194537
    0x210050c0a090b090d0204020313050a05030307080f13110d0c0e07030b180105010e1c0614070e0105030f1b0d060602210304020d050304150801050406060f020703060b0d020a0303 78
    0x400d169201c0c1401003d8000303032810310318041a0900150904100002c002e00c11900000052100a1107072002c40001c0c0d40041101e1400c1e8092800c0703030302c80c0c00840d10711001903400000501c061201c4040d55000781c03014505031085101c9511102e60940d050301086800c0031840107101d002400145016008183d0100e00d8030503030804410080a413952110000c0c4510503942ca107003a02d898510017941110002d00702902c0d09070050700410400d40407059080088086d41d038600040c440c4075046900050300d8072200811558030007100742c0311070170044e007402e0010f4414170000d8110410402c120703800010040c410f59050400b16807600f80c9900002078010038685584c0c0402020303804007c1305107024009507007101c14800e03080000b0b000d40002030003c2c0c46070440b124400140042030040750007130b050703182e00d040c00c244400d54080c142c0030080c4142070140c0d2510a000071020310a036000c0f02c1c2d0801c1a4041c041e4240b41d5203681010b44040c885050388045092416070040e0344140d85500194440d40700c540c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 852197023 1250 852195773 852195787
    0x60b150a0c15060e150f0904030201090615080c0d080405030a030c0b0f0c0d1a101d0d050c060703020f030403030f020c030c4510170a060504030210050c 67
    0x1078488404040740440c0b55041140030302109203000c61069104001040100d12040c20f40c0c0003030307014184240259045a14407003444103140c2c0c1908854107040c01075209100540d084480e46410410a11841080350003581184002d0303d41030407482c05040c06208440c0c140740d12600042d0800c6041e01089000c40c0c5105076030001c103d010445181d000c1d0840490000611340001c0c030a6a40c440c91039454056561803603081074555401c46555824000603128608101340d052000e0045071980100e8a03050500700c03130340707605442d1005140401c69442006008003851007018402146c01c02c1000310198082d8042460300084100046c00085010f5030700c00c030006111100c00f13410101701d40801400b0ba040015002010384034000c6e072000e541000c140090502d404145e06521000d020744c00034804040703602a000300100f00f542d20900070030742c1c5403016060300c3c1c1c1c4500c2400c9882c58450300300c941c0d070020072090303011540591000b40e01c81c0c0203005880d40c1c0b240440c460011141c045981a88460010500c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 852198273 1250 852197023 852197033
    0x5070f08060a0608063412202215020d080f0609011a0c1b0a05092203051b0d0e15030417090303070602040303080c03040f060b150a0c 59
    0x4142c01c5066500100082400c05109644821004014148482106404034041407a2200440c1100110528880090013a480c018607540350480003816840c140100400560074001d12404074502c0300104a00e000045250b40004a40072030044a084140d020000f03440c0e01c42040c284464041a4043e103c25411000098051180905480c05000070002081000e0700e0302120303141075980c1c0300070491400113241c0c82c000c5070f841491000c80b035030b000340d80010803440b000410717190100d1000c0350000c01d400d48440501c07184500c1154210701300c11040400c1d0703038000821004038030003e00910f0010300d482681d00d02c0148440a1110415031503001d0290651001e602c591b409400d55811110302c1d2211429007040240d81c00701800c090a68100d41d1540c0100706011401ca0b00d10314405000d0381c2d120041c80c01c105002390002d00c020380c003242c07001e4002561002c9034421280710710390107095145454019103441009200f8015090741181d500c020f0b404040103648094901003015a8600c1092035041c41c02e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 852199523 1250 852198273 852198283
    0x160303140307022a0a03030e030f0105060a0621020a080f01050901060522080604080703110106051c111e01020c18071407081b16030b0610050705070f08 67
    0x11151008103100b8820a242d020840b103030344401c8511040c44c00700c5101001e1202011900c0100d610180b000800010150000310300c040702d5500b24282e03011141841042c500341c59044a00c282e21008908041c00290f0142e22003026190b0030b00d02c81d0100110780b440d00812a404050000041100c0b0420008030780c18840b049070241c0070030b0b00c4206255140500103891406410080e10001003540c040540720014049504020481842198071a041905040409a01103c2e0540c005020064405400b501c1401218211140500070048071500101e9000a5180c140812200201040303a405120b41d1840d00f030240c0c04d06410a80080848020000782c6000c905000107802a40c03060090b9406a070003500d2103a108000e400d02041d840c26680d20380560f44100c0b00020001c501c0404c4804085540e0803840001c216540221000c00f0407280418101911500c4001d162039109000204281415141c0e0007549802d810200e040550507500c40d401c040e560f4000c4880304007010307010022140300b000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 852200773 1250 852199523 852199547
    0x90c090a110426010e1b040209041404050d0801080a062d06051c0b06091902210f16030e0703080c010e074502070c0302091f120204020408160303 64
    0xc0200b0800100320440364a8114032030740070040410030000e115241e00d1f607804481c03002000600c00c00905466100f0301983e10340594040e01c5520a80749240c4045018a0065050311908402010148400e179a050003411064032100703004d1600700124003401d12443d0700038038000750042022868500f880c09000111000b9403021150a001c5107560003c0740c507a01c00c983d00701c030b0b0075a103924581d5501071f403403c03202013042d02c00503c442c8000707128000b01011030240c0f66a021691341002c0c4c42d80746d0236503082000c0c0d01038403982e119211840404460302d00076403000440012400a842078140d4903110460b49801000d03d094040e5100c2e0a5940d44100900ca007002500c6040c40e901720103a1001c5000d08a104003608c200e0385004c154449003c0350070156145a60306080d40070655685010340741234031842c0350740c0c401240907212003404189882e454050101d90f102d1510040750b540ca240c4030801d290079240701001d0744c2081e402c01010554000600107280c0d54007503481028030300352962800400700d4081d04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 852202023 1250 852200773 852200849
    0x2d10030b0904120504080d09030c050d150e0708070314060702060103080a0e011205010b0d0c0302091c110901230d1205030703150f030614090c090a1104 67
    0x8594449946040307a49410a400049621004014200c02e0340d07288a00d402c40d000b544980140700c0c45d00c50b0301c958000c0582c1d01c1703503100c41d080f1075441040c01546246850001c10885c0040ba1184200315240d01c90000020031404840043c4c0d510201d003400d01040303410640b9501710090b814900d14004104007904050144000c14046d0b14544840240d0f0192810500c1005141c112076000c50784243e01d28044410007000070007065070f5a9a4880c12075004842c4150503900b0088401c09003800f07403080c0c0e01c0c000303005403815078414000075010b01109090b000489003a05541040c0c2156210304108601034030f50010440f4030101000001d1142c80c500388000303841960b12584400001c2c40404200e24411101d06110b92a6121801e056028001950070004001d800c2080050020b450440e41d00440703000d05810881c0d4520031840c0e032015981296003448a50150418200a080c42c1e103459030b10207400b00000502e14410540602c8651166001000c03007001e41250f10342000182000280121f118 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 852203273 1250 852202023 852202031
    0xb030102091302090d23150601020a0b1005090115080f07080115050c0a030201090c0b09130209210d17040506011401271701020304030f052a01020406030e0a0515062d1003 75
    0x5e023000035980e652003000100560707000004a4503000c0700078008000f40400414070b00c130560311101004c0c0c109624100700c0c1c00107848500800d0b001c40f20110418002c416607aa1001c85a00b40051034544e9280e882c683d100f000010040200641c105008c0300395618030a5001142811443c18009a60710f02e54002e80200c07201003009110300e50310200c6400c040107248001603141c0140134009000d5419401d140c2d140e404024205610585000c034020404c400c807916041c2e0170307603910928101c035480c0c12a801081580f001c401032218801e14402d01249010500d000600d220b4445810290328100031303d604000300515109221160294401040c40102c81c0021819440d103074a004007040c40418502e02400000038540712540c60104100107001b21400e8011110640c0c50640d0b8003e520a1050344006460804c40b031030800c101013020310364940c10000426058900d9a07803800200005405194413100c0b200d40310452544243da03600e9034035511080000c00c1a0680103002c100403000b41450b041506d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 852204523 1250 852203273 852203281
    0x714220308040e0906090d200f1c050a0c080d0915150b07031b08090d03090558060e010b04020306010c0b0402030a08030f0403030b030102091302090d2315 68
    0x10000b07d007541c11981780b802c030740d500000482c60040001840c12401d424000c007601603503900c1000a0084021b01041211a04408109006ca07160700422142c0400542c0142c00d070004280204003400c0b0f1116840c00000d0002100d56600040441c0c2c01503e504180d10b03002600c809000561010005010201941e4a4003e81381d030014003011030609407810000451380c15800740440b100680d9406140503145041c1d400c00f40c02c3c054400c45c03443c412140b0401c4003007102e156036a2920103030b1030b1000c4100c2d803250300800c480038065800c1c40c0655079a0b0b03c44541d42419010001201c034660101d5014400016000c43c00511440c2543c0080307481d0343c0641d004001b40310207070340e2101c0b0095401d074000d00944a161540d100013410314506900284c024500031040c81442500c0c0032031180614030a07103081020200b1701041c18284d01a030700400b84c3c03004000c9080d035000902c0350010586204002c0c0808042d61440d41c491080440641c480406034400b0300c02e80450794030401c600300c01c3c9004454615864030b4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 852205773 1250 852204523 852204541
    0x90611011e020d09050f0102090f0d050304031205070203010f020909061f030207030212040e010f080703080906071406090c0420030402101e0807090603050714220308040e0906 77
    0x480100032a0242d0000b100c21200810754469420340303600c41c0540e0382e100c2004c500325001c0c1d0007820869200b85803090703960005180c003c0e601040c06501c68044e505181c80c50301c44004c1032400100010a10104010300d80060741d0a10a03414054030704900181c40da01040b00f480001c40006101da80101e07103c0f6000002e043c0c40401d0300145c041a0321300540d4602c180e190480c02c040c100344080082031000714020841604901050b4140d030343e0403818000055582440503558506880060a0040302b00310072003446c00c103400103000c0c0074011802c0e002005054502103240002c01c40d031161458002e8034041005e4070301405014402d8102c04051149517a50501074100c2c0c0c400644000e10035440c0031020f90304030340160110000318004002c0f640403a40e400e0740140040030101e0301c030340c00191545404134529000b84521030281e406a030700c420107011102c080101660150000e0100e51583d01c4001e46180d501c00810310107184075441c1d0580b1180307441d4910150800191584800390460810411910 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 852207023 1250 852205773 852205811
    0x50a0509070905060f0607060501060809030307120b010905131a0f010909091a101d01141002030c011a0a0f080613020609120609210403020103020d0b0a0609061101 72
    0x50094030b00081c0c3c1e40ca4200010344000140042641c02c1007000c03d514042c802a9400a41220352a803142030b1181c2e62900c4003916444115402804280c0d120340c905d075030b000380303910801d860360040c1070a0a001d82ca60000a400c0e46102260521040c0c8814800424105201c0224038a010031b892809181c0b070f1030000a410700b222401458410380d540c3c004102031003406501e004407601503010710300d494100012440114010381c02125410010070b8014120003001454050481e14840c0f2204002280d1104120381d84052b440d1039002c521042c4031026002c2c1c021b1051002140e411041507096244a0342807011600244e070001042100d911020808020045401944081c0e080c2281c05500032510008a00f405600410780d040f4559121428008000284541c09251a00c1c11117120300008103217040c51040c100d50709180304106100400041d4080c0e000b4061050b8040d10114003030b00103201180080200c0da11410002ea50044100111504200111640e11100c0020702c204c031a213010b0a4959 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 852208273 1250 852207023 852207029
    0x2030a02070b03100906060908010605011d090403170a0c180b1c060e0c03071706010e1302190203040512010608030301030f03030902030a20030102161e08120109050a050907 76
    0x2010000001000120404108006049654020804181c81f58001041d882c01c3e4001c102c00b561034003034007084960140c00c03d41020788043c01c01c4150005082c06105d403034000940102c4c20311010745102d01c1695440800984a4030a200340000e610705030b4200106031615002001e5a80b8050600900c03e00085d00112140008402c01c000301c0e00a4030003c0000820965204880740c41e005d03002d011603140c1c1c0f00011070080c009552400e091103d485801d141d60709050b075000380031608102d0000e1076401e040000c140c05240030b003401814602c0d00a00d1918811280309900010b80000800340890300d06202000d290300520402008024200300c442c0c0e6a901c011700028040300c2c41200c202082512030b0704082d0141c0d81c060103894071034840b480e06080300d000501c040c860303181c91051411005e080520a6844034802d0034180407098015484048079080b2151040308199030100141c07010580741c0c1c0082c140c04450080c0441990325000010003191005000a40958202401d02103848400518882a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 852209523 1250 852208273 852208289
    0x1b0503060328060c08010e070f0f030c0302070c080c09070809070b09060408030a030501090b01110a17071713060f20010b0a0602011407030b150f07021f0e0102030a0207 74
    0x3444400c0510310b00e0b00e050b031400040009052a0210094076440000b10381220101540164541c0b00c14100756060402200c80400046010141c0b901c0c0510030741014880070841d040040c42c1401a4580c11802c039095006100158000c0300c1b0f004081c2012008294003261501e407150740d03824007140580c5c0354207140c070030003c080c3e4011882004640c0d452040305c0080009000302c981d00d45840001401038034091040e840d141e40b800e8a20310081d40100d01c1450f40b10000c101820705081280e0303968448000020407400042d0b410301150002603840b0840000101c01c60522030b446000004c0b840340c20060307d402120403c8002000001002d8020030348054680c01c070403503031480a40038500d00303006004410039258030143d004e100040c2103030107600420045031410386030441696100e109400703175a00c40e04c0203500130354a9203c44000c46003144c080d00201b003196000500d840441d40016541c9902c003c09400e10340c003140055401c07950400c4000c020344200780055401c02282c0f01d03001c0d4840c2603500c20542 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 852210773 1250 852209523 852209563
    0x160501090c0b0c0a110301021b01140c0c070506070c0803070318140a03140f0118030908030c21071a0604050f01030b150a030210032003090a060e0307060608011b05030603 75
    0x540c1d8083d01a1190008025127031064540103030070717140c081c005c001e082c5203111009001148402d1107034012980c0040c40d07400100581460801444059409640300f601c052021800204c1c0d44501800100580c5001350f8030102442c0143c00d01014090142d84414011141d1510081c500e8541c092181c0032650003a0b07100303114a8945100500308014400c41c0711855180c100c014111000a4200c80000f40c0240c0e5854091030300c0f105940d9a91252130404401c0c1c0e07104020303d0401c403440480e03a061a404400f1500d082074003070ba0f07810035529005142000c0341c0750503100b000107a05041c40f036540d0180055a00800951468464000c8000041c20342c1a4211404074069001d0b203400380048003d650107001c00c141983c40420050040c610300c507060820100d090724848a0018a0003030360702480848020300316006107582e481d802003150100400e040d0005200c1000891014800c0c140104034000c0003051241540210b14010140890b009007486000d20510546440000c2c0b08140013130241c1f01c00d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 852212023 1250 852210773 852210803
    0x204020d0b040903030e0f03031015170f070e0616081b0a08070b010e010b042304020a02070e060102030421170304031107050904080d11160501090c0b0c0a 68
    0x6000740c9080c000050b04a400c0c11911010154142d000036080300306d41080e03c0f00307910783c0c101d02034403840292018001b0709142a0305201d0107040a054a40c100c5807400d24680ca0043c01458814030201110500d900c084200100300304030340c000013410745808040f01d00d00e15102d0303a2154000072104006000d04840c2c0d0106507440c0c0d030b00b1948500264907a0b00001ca4403207400600e0700403030660001c64103d41c69886080000307412416060418113940545103681d0a050600c18295480c642000d521403c00201202a8041c0d48861004000c603038040c1c3e0190141500f02101c5002c5c008018240c181198400c000400c49585d404007a804211030b0510b0405030800d660401d83c040d0354164443c503001490000030702c020190040440780c1c2e01030344001901c0d01c1507559010802410b10480c2c018107070000800400400c6400703030784200500c03006102c40d00d0403c1c1c0801000ca050140440382111141e644149610034003272094107540041041409c03203407500b0344151002d5120603013050010144042e4440031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 852213273 1250 852212023 852212047
    0x60c0703350a140c0f03040302180105180907050a0605070302070f062007090c271409041a130b01050d0c030201110a0803270d0e0d02030c030f0f2404020402 69
    0x15120015030800f00d62658005e241724079241c1c0d01c0f511040348071700d9210400070b8100488010f501d0403124020b000081040c60140540ea0b0f44200801c004854026408003041075590342d06048003411f1144da42c2034840d1407510307000c1d14010741030704180356074088034004000781c943c080001036070040c0c0c5c5c1e45950308021605070001d24021040e0400c9040341e045c98411500036501055615441c0a120100c40810f000f20303510150001c41c174056a000d4002071070302c10301c00741000540c55070414400d220b40c200c2521410031300300000b60b090700c82c0680d200000c0210018010120841f902500c030840d044541921f42c0d9444a4008219200090522142c40e40030740b072001e000d2000c20001e82c0c000042943e03a203000508080c0f80e4003a110751508a21740c1e840c011520400014140b10503d800b030301e4180f01300504404100003e0154101240d141c405e8a440e0083c52320301707019800c070359840c000c010440501041c403101d040c0b8040b40c442604020303030040d9403c4e1a48090307070034540054069500580e180300d00a40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 852214523 1250 852213273 852213277
    0x806150708130b0c07170604080309391206010e071107062613060b03030c0f030304020907050c060a11090301021602030c041e0506060c0703350a14 65
    0x102c030003102c104100004410761514024400501001d0584465545503201107108000b0321100035030303a5220800040004407043c009581021100d01242c02c0c0e14a42880049034034880074002c4100d10707820b41c40c60305109070022303c00c03148403044800452420107441c00503503520341440354248036041f1b200891003940c012300380f00a007140342c030040d1340c5140d0b1030702800303088094902d043c5004407040301d911003824401c0c412000d0040d03000c03040b8194203990396150440505942e05140d40c0c580400c000d40c1035481000c011307600485412070301035900c1c6c1c0780c0350040144244004122a0521034104807008951303001068107a8440d8201d100041d8400054103814058000c0e44c1505825600c002000404002d04801440c4610f2084084a0040b0600d81c20f101c00d6079010380d0319156a1309822540c01b076041c2d6503008a80d10081c003514250400361300041d503a02d046c405910a84400d1015021510f40e940148101501c50911007604a50541115409201403240c100c1070400c0200c500d00ca40f517400f40c1002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 852215773 1250 852214523 852214537
    0x30a06080d0e09070e090402040f020c0706080a0b060403170c122206031a0d050102090d0f15050f18120a02010c020f0138060a090608070806150708 65
    0x400c682081070201c501802c98100809018414402100094150b40c410b2000d17440e08440038104004c240c685034244130243c500c101031010b18075001d0008004c10354042000700000c081d0340c0c0d9a9203c0741002031080f4100c800172101035005e070340c04110500111317003a89500121070842d440f2407a0f60b10f189070880c1d804e100680070b050350800c40014108140c511150038029101f010110b501203004da46110540482d030b070341d508030951207081030401d111600d0501c103190300780c03070068002509c0c0800e2140000e40751442c0c44021030b1249149401c90050103140000164062481942000141011030740403690307150041c0304915140c04100402035000c1d0903c410003022030100c0042d40c6540ad000b1020f0702070860300c03410300b0042c4034022484015101c14003a80c2266170081419130005124040340210a115041c00d2040e20745201800600303d4607080010a07440c4007030350703079014a01d040c280018030429000d0801c8041101301418081c1c940d4600042d800340c0845003004035518406403400024a00401c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 852217023 1250 852215773 852215789
    0x15200706060b0a0f0e010201050906060111100501030303061e031e0f0209040605091603150509030403050a0f031d0f0906040e01050109060e060909030301050906010507051b04060b04060c08030a06 86
    0x700b5009032441d00100f04130600a0315403a41c441c2d500000c40120708845e0110b66101d00c50b44810049105540901d2522104064110654250350413110450080d178001780d108400282d40c0d807508100e096103201303c04200c02d05021080e1003403441d5403030700c002c0c1180c1c1c3c206082d4100e802025102c2000003240747d602c1c01c2ea502600c3c0f0580c81c503160030100018241241c11800c6800b44211a49055013070074401c00c140e0390721030f003024400503058031104001c01000f45242e22074070041102101045042280349005803150102c10300b01019032500501d03480300b020010040314404c2410600d69503e206a10000b03032025600080703180d90742c40009001c0c0c06660700290042d4606800815007468a8100d00d00341c0d601400725030350030703150481400000003040702e21000a40040c00148441e02c0c0c02002e15400c55414500103040c490161206400c0c04031503004100e902e149405001420301f0107003e444000c00740c68410500f014541400501000284800289080f100100040350b585040d0f100f6006041c1b21 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 852218273 1250 852217023 852217027
    0x402040905100e07050c1504140a0f050c04050112030804030513030506011518061d041a030c060a0504090915020c070e0f040f02060a0c120c15200706060b 68
    0x340510042c1c11101e01803448100088000200e1040c010b10490344400801001084800040d40c000400c5120140044402e41c0e081d02030707182651001c10580c64118090b1924085142d4146800d0b450480f061110900941c2030000401c04800221001c054864141c01c1c0403407a07550341c0c0703000c503250b1107240510320400c020184084284000000c00b1810384030003480030660008201c60035a02c06c03070840340c0306ca4440074070310060040c244102400142d00981c0314100481c071041d00005000d54030b59a0080f940c9050162240b03005180800030407804101c251816481c10300400401080c034811805080307038064071501001d040003520118a86000401e040454407401c1441c0c1c641d403612910b00c510f9078400070308408200c3e500400c0c6000346c0115030021104408030150780c01c2c0b144a4101e0140e48040c4060495034074041040c1c6820b0748000300a03543e07031100010283c0341c000b410003000d0b8040390941e8504440c4440c031b5222060314108201300001d80f45d86441180c54004081c04245d04180341e01000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 852219523 1250 852218273 852218281
    0x90905190e0708070b04240c05011a01180503061614040f082506030c1e0801061206080c0d1e0b04020a050d0f03030b040209120601150908060103060b0402040905 71
    0x7000c150322050701d44550036526180e0303032441044000c1c011800380641540c40c0d00c08480c503000714514184c5203000039081801c40c0e80c046844d050b08561405000c010403003986292192103680c88800782080040d541400040c03182030001081e42c0e4003008101c0715104942085440312a801900141a1311140314cc0c1c059540b43c8030382900c00d101940d071040303a0051041601c0d4100c03a0300c40100d1540502690380c41c603801c503843c028044000d403002c840074006000703158442d008801324591192100d905d080e101d44000c1e51500038000c0c007807200d4014120380c10b0314004051201450200e54624550000c480c891000150b41c01c0c5080f1142e0300500016040c1100300c0e50404024200241d00e1169000f100c2400e45507503108180024040104002840481e658001c440000d001e54440d420410014000506009c028004510f80d090480d144851651140300104901f145001354406503480c3e51514600c0585880c030241d9a0b400180001409d0719151a01c1400035211641030f03070020402060306200c82c0c10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 852220773 1250 852219523 852219551
    0xa05060424080f120915070615170a11040b030c0901140301150501080a110d060603141602062d0c13050f0f01031a0409030206240109090519 62
    0x292032140c42d0003070140c5074440381c1c803c00c04144929400d0580303d8140c40c0003044000c200b40c1076204040540214014007000002c07510070300c81d460220010701840944030f414082c000e81000a8034040840720380c880181840001e404c100c08500c08901aa0040303070b01c0900c1800a81040113044405c0d4000681000006544800361b4615002c854158001c00a0540d103400e01d40c00b82c2414080d6501044e03140010071084040b992145c2c00030001c000b1541d042440000201054032030b181d000d980000d03210124084070019880c3c48580000d054210440300c3c803e02d40000c0d498800040c540030710342a141090741600502c80c480404088840740e9840c00c0e51800064007201500f28038015802c501183d9004901d504100f000d580d26070200603c413402020520004501038100c40c0b518401e0040c002e420750b00540c42e68094400114860380141c403492910a44031811001c08217149092050381818045490b40c200e00070300f0650700b41c0d071408101c0ba0360b41c0310480c0b00f64031203032600f4109915183c04410205 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 852222023 1250 852220773 852220841
    0x501090b130302092706040c1e0305010e0d08060402030105090c0c030f07030c0302060601030525020312161d0d02010c060e160f0905010b1813112109060a050604 71
    0x1002c00c00c080750100301510100ea13030380d000032140288448440601030044a0300c01103801c0413090303034a100d22710396a102d5450b05c1c2500c1c034081c42c0450690210401200054100001d60b070700c40c005680c00c5003198500310000b182d400d0041c2400032403800025003014101028001c4401250141c1d0003d81c2e034100030714000382001c28110060f401401081c0205002e90b04c8ae000c0c490145d40d0360342ca110b6040c2444071280710303044c0b00b00c0100000d51004006902c0300c0e111485071a442054a47d81d288404024035501814417441d071307850b007110404802c00d01c3e42c281d0340708a08005000e40a20f030491100100c2e1510344001d1041d0381c0c003910176200d019400c0718818043e42d100b0040d0740101c0007081b003140d41c82e0480d5059031028000d0440c050f40510000c46800d0640d28a07606080d00141107408140000000740304440e924100f040c14400d000070241030180440d5503800442c14210000200340c03400300b00880e2164000703010440079685540c00720706180d4030340e002840000300300c482c0c0d4608040a100215549 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 852223273 1250 852222023 852222061
    0x806090c0d02062223010e10050c011506110703080304120c0605040b060102010e0304050a0b0703031506081b0307020d0815030d020c09090712030305040c090e01090b060a0501090b13030209 83
    0x4406150007075a0351342d885d500040344084d81030b1544041c0180180802140ca00c00030007040170081c090001c42002c8000340103400c80070f8400500242c4143c10500300802c4800c01120510050380480300402c001a902d10849038099003142c42c480d000c240203041290403448404010308131a00300410700080c4041c084072580110360980080020315503484500343c5174022446050f6010700f01040401c9194858401040058401d1a00240d88805c00c824001030241c2504031000040080b82001000e0072400100c510ba08004160319041d454100c800a6813440d0403c0710780104213038803020950010182c0c40b070044c0640010159a03070101c0d03100000756a5500e07014007620031041d000200baa0650045000d030107a030769824942c0100c0c0003540b0141c001e0000500200c80c1b8105001000800e102244520300a410510001184006036400d140420807030103855148580d4118404000f50707130b00220140c080300d5030410844d4880e0f54200c50265040c0070740d80040d4010244400300714a100701c0111401433 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 852224523 1250 852223273 852223289
    0xa0e0a0b0118060516050d09030b0c120a0b0112111201050d05060601110c0901060804060c1e03201303020a0b0c06040305251b0806090c0d020622 64
    0x40e0940440044422951038216400e80e103000305014419648144010522413401c0f1550410000e00c4e50740d032034600354105000900044c1d0302c540910400101e041480d0300f04e00001e0a0030305001070b2584400c155203026000822160f40c0380b0860205902405600d21103540940081040c202401080340065000103900400940b55000100c1c852070424000c0e0b240640000003051943c3d5100015909048031540030565885030b102e00008a9852000240c060a0282d8885400781420320b000000c2d03030a1070390b07e45c05020381c0303042d0040d008845024005183c4030b145404030303000714004908510700480300c07501222854001410306020315005070501c100ca2094800070081680c6080c4d041050041441000c8540c1101011a010038130480140a4015084815450384a19800d1451802d520740c1c000300d510320b101d69a01110403140c421070078002d11890018111078581680040d84412102c9402031142192101c0d00d810b649075441030701e0030665446030f1112214155000c84a22485503c0303500c00c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 852225773 1250 852224523 852224531
    0x9021902070b03070c210306031e0f0b0c07060f020306150309030d020318030d0b0901060e060d0903090b0c15160507300e0301150303090e0a0204050a0e0a 68
    0x40a100180300c80449080ca602c1c1030a64540390700441e0b01d905502010707604a001004c200145945058a0124000c11038900280032491898002c0b41d50008007188502028131901400c00300310020815070300180e2200240c0c81c0c554964146420700d014030703800a0440da20340b440b1440011260b81c02540100c0c81150814640d1111452603200c610003155406079a8205000c06042802039401035a001200300d225035007070304103006a103480c64201101030401d058885e06481f11600700702a20a0140500b0328024200000000c041a02c1c0d1040221040d5519581c144081c2818030030080c1402920798011056590aa40c001c4283c0c0c1d40c0e9800304c44120782c01c59501060802c2e00c41402c1100c4042c10f912031078100191a00c1e081500c613a10301440b500034880c144281004101440800ca500c4000c2d11070754280d4442609142c21524400103190807480e0048040c4042900041d41104443c2c221900c2e102d20f81e0750041d200042c0c09264040ba03004407219001061030031110010341c0c40b5802d0384e08100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 852227023 1250 852225773 852225817
    0x70e0402180403020d03050c0d0f2c0307030c0203031209160803090d0f03090509010612060b25110a03080415090f0504151a031b0a120b18010902 64
    0x1c81c030780c081e10000c0c00740e03101200003203030a800303a00095030003d010006941801800e4603104185d403030044155000903540c1442030400c41c0e900b045000b20b1456407441110304805191100da81e0302c107201d0050b06100c0c0c40c05800c2c0841d1341c00c004891801c816000c0041d4142804171380503070f0398030044420b40d14848400c48003184803800017007510030f400001400210994099101c80c0104d07102c68206070300700f02c0030780310108060f1038840040d0b000f40566a030b07500145107000301040881c0d8607a00020440c1e842084944c0c24101d0042101d0311100045151180800c0e0a14004203021032000e410742e080403420000006001c2c03040060710842c2c460215a5000b81c0e50800105d480c204280208042194500d405008908055114080e02030745201d0509140c2d48400203080d051400c801c000c200401c1c0081007140d120011141260300e030f54000403490600204c000040c0c50640420400c03d081c03952400c1100709556000c504643c60611440c0c2d010fa81d5031501c22a90107540140c0c06040003001a01040d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 852228273 1250 852227023 852227059
    0x2070c270203070903030806010215010b04140d0209150d0605010306050402010e040c090e090c030a21090f3003081f0f0b0d1518180f0b06040e070e0402 67
    0x89100300601e030f81314141c1c942180d41c103542050020740b40604504c0780800c045c24410041c8402800703450b00640b9151214508042d4918115440f851030340034802e108101401a2501c0240e142c00c0341e5500c140b402c0303560900c40816407104480002405540c10310b00001b080c88119404540154005c4e6074078210341803883c1c1844107981001d6581c10004810b840c0402c09147e8248480350000d001c2c3e01601c01020070400003d1070072540560540c1c0c2580400d031600400e54044000418000030750038a4903100703142c20910114002d140c03180e02800100000c0b043d0400100101c070343c50481d40644c41c1c4148030210305000300005012a006030b001d1021b150146800603400a13080d0880c0c00704a4029440e80c10030035603941c16040380710280310940e10b030f81c02442c1c180f02c0469400302030618108c0c4505070704920030040b400d41c0d206030a00704e26911030400010100b4006051441655040310b006800754980c035002c00c005106490380e41d04c0300c0c0144280072900141011165005078000c4a81d10141d403120000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 852229523 1250 852228273 852228277
    0x513050103081c021e0d060603060806182e05010806090309130603021206040302010b011e0302161401020a030506030114070f0c080a0e03010c020a020102120d02070c2702 75
    0x503020ba0400c1c403d4001160580d99500104001e00c5005414800c015128912516002c2002d000c0d00d20046042d000c241d00031700c14600240080e24045c40a6840c1c01040d076115200600340e9491501c4016408180300d00422a44054114422144880358001e80c0386070740011904000903605801c0c400002003100d0300141450140315090050740c40c01091070200f1030155510440c0302d0341c907511044c0003c0507a84132a403516148081ca0050700c1203240c607190003403c440249511034180246003c251050342c08684140084400d182401a600c1031203020f8080030150303010009124031024400d000003410190040c18040c0041d890900c201d84500d401c140c203807103c4801d034000c0c141c1e103030001a2000384509017450108249080078254203c158440c03202c2a440b400d40480400ca03850000ba516040911440c501c059142c4040d00c0f494401c0d0740001e480f2880b07402c040002c19404100b007410120342e079044640d00e660181c000030810741c0d126001201c010703404828000c29101590000c8540c001802 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 852230773 1250 852229523 852229529
    0x2180a030309170f070311120d0210050720010f0f020304080d02070215070507050a120203060c0d0f06080c01090f0b09040f020f03040c0302030c040e030d09210905130501 75
    0x35048629420405580500c0da41443c1e88003007807060901000d8007040c1803140c034001d180258400c0911038005401e1028018824a8040140e440440511940c40d8041046454400c2c0d07000c0101c0c1e01d480d191001c51b08241300c0c4810b442c03001c546208a8150074015406142c41e0944c540c0144011003100c0e68400481c0400c0318090b019480c10480c003a82003940303900070500580b000b8240c1c92400803928807061181c1044004488581c01000c0501c558a06070907500002d1041c124042100d51456011030b482d42c1d40600201c40c01600407403201a2034440d46c2000b0001d0100d5601001160f40d00d60149903039842d00e00c1c0090108100e158041b81c1180604400d00c04d40b071310705001a14114090080c04004c02c18084180e100a6091205c4002041000000e41c06640610300046a90742940101420700486050252289107014000d40321614048140c07550000341074000505c80300b150400d101e00d04050500c5445046a20100e40c19180d000b200322000c3d10710a0300c1800001114003d21070481c0d0f4280 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 852232023 1250 852230773 852230777
    0xe1b0f090607140627060a11040f06030b030c040b01210b030d03150e1303110a06020304050c04060e070c140708010603030206010906050402040e040206071103100c0e090105100503040c0b0d02180a0303 88
    0x2800040b4a0810ba40140ba88d4104282d00140b920707603144d0b0825070100d202e40010000035150200c954091404110009640d07004540400400c2015000601049296000321400354041c88001c015110181c1c02044038917409019501d00d2004007800500800d217031000c503c020300340d0ba4000f0079110903020340380d885400041d40000005009071001d41e25025000352103801c9100d1810010000b50b1140083c502882c442d40c003c00c034901501c404c110560344941c1010031884414003c2104040d4001140195141c000029294600c00590441e0920b8002e80244000d9800c0c11000401c16900140c07450480781d001e101049540d403540204401e031300c118800c845084010707101107009450010f004080700351241074000e81c0d1040fa800800e0510401c01c0440320190380e5200740d99a42c80d0000c00082591404a4101d4403d605103800994090303190740c00340e008c010300400080d04103c131820402000c0d101c80b410464540080500d8480658444c4a100f00c00342010040b856031030030002c5068041e26899 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 852233273 1250 852232023 852232033
    0xe06010b0a180b040f06021b091317190f020a0b0a0b030a02150a02100e1c020f0102030f100e1b18040e070e1b0f090607140627 56
    0x4080700701c42d4800200c08411810040d032a0004004408100510042c002071417009907480c6050000382c00c107200076082c60202a081c0c4049000c682e940303031509a01040d1181c1001e00302d211820f048031142c1c040310180000c90b0001480703032003500090181040c05003095441182403411a441203071280c0074203e00030301c3d0050b00750128500c444560080100c0c0c0c2c3c80501101c070310720059000500c1d01c0c004214442160341c0e002800c40d45503541880381c465182c10044041c464210100c0c0456036683ca101c007001e80703050341500500c9402d0300c24072602001e002440e009540b203040105100010070004d5400070003045281100040021030905030910a144003074089822a1034002100056408403020820084d048943c1d84000c1d900d51080500c07403007541c0001c060107401c00c41d108101e00070243c42ca4000070200c0030380c0c0310764080100c111b802c08071078040300c01d48601103800401c01600407408010f01c00c0ca00d8070224544500f000517540e100d003120051204e2603c15010824101340b11810300440c05400c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 852234523 1250 852233273 852233287
    0x12020306061c0b1e0f01030b090a030e0907090b04150906030c080f19140901111903090f12030c140901020c010516062406020c01050301090b0f030304060e040e06010b 73
    0x34003d03c0543c003160b040704e51581001c500100f10510001111a0110002a0700060080c0500c0031032450340448240d00400c0c550503140c030003a00301d01d22022114400c100c0c65001a500610411161000b060314000d0700351141d45071700401d0101c48181c030381c4400192040000198152007405180144140398031210303016120180006041c1c2c4000305241da1150700c10440c58400000307445850041c400e0103940c40c10604200c244c4a00750360701800d00c089110f81c140401c8403e01200301c0c1300e00c2e60b0040da0030002220302031454080c079044820600a08492010045180510f805030844001408d00c0d035503142c00e0041d14170101c4400e0190004280c01a401145d04480f60350160740107104804825001901c40303045c55981a0907511000c4801e09403560801503d550300760303043c0b2404050805400900744c03210a000000381280014400d20b2001ca442d4041074070300361a01c7c0a10074007071030040c003a683e455031a4100a001c02c0b10410703c01d8003442c5070526035040c124001c2081416503c0300c401c142c1c50659 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 852235773 1250 852234523 852234533
    0x6031801140c1801030605090901060603140705030c031305160302100305150d15020a0f11030a0f0804030323010f0803040b0a050a02030423040608062e05090112020306061c 76
    0x70900f2840c0c1410b07a145804102c0f42d40b540b02d981c0c81038007888008a4914140103005054a034282c958110b20607511081c01541900401901c0d408043c405080303881755a8014560070350841d060003d01140208807084813415020450710307040c0d0b030080e6216021201800000c9040324400c07100310789103040d41035a601951400016400f60039000f01044900070710305126801c01c903030040041d400412000641d94003003940194440f42c01a00d544090350811214400c043c02043c01045440200701400c1c00042c1054080d6120030071901004c031041508400c1104680e40940080c0a0304001d20b00c4224002529200041102c0c15142d022031400e00344840c0728405e5a068000380c40340403d50005000105284142e0102c05a460b00c1850802500d4190034060104aa4241e0403698150b0012801c201c83c51b4941e1030480740300e02d0001540c3c142040f4400200d400c10b1381d16004035901603030510000401c440c07083c090b4038005008406070b81d01134485004110704000044c2d081b280f21b802c0482500c012030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 852237023 1250 852235773 852235807
    0xc0b190203070c0b090d0b0108011b020f030a03092108060a08071413200301031704030f02010e0111161a070c0e090c040c0512010f120b0c0906031801140c 68
    0x800301806d00e002c00820ba585004024400740c200600320382d500c243e806a80d00c1102034460072a1801c0c0081c0404902c6078510946030710601d2001e205250300c62013403208004c400150070380c02ca04640949074020003928001800c810b030540320b540c4030300221400131030080070100b2444120341e5803111080c030a55444c014802030342501e030394181e103480c0e03981c01410514200d0490241d0050348a03201c0d5559605500d040c0708099141c1e4004c141c1d40c03005207c107000007607a8081d03e400305502401d080201c280f04000480340c41c2c07110080c40c02c440c001c469031700081d0442425080142e401400d000307481c0d401641d01c2007107607015260000d005c50b581c20008006201c41082c03107a411844560941ea598141c034804603068030310001d40b806c0012800540c1504074104044c54501500b0300110304c448903840d10143d583c41a500b100094940c2c412800032561518420048455100e00070b00002c0d202c3c501480c520a04080c06096100b195003031038016024034082c040450310a100080603903007030004d00310b0250030324 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 852238273 1250 852237023 852237037
    0xd050a031a030a0f0302010c030614310b0a151e03021207051c060f0902130306052a0c060403120f09061e0203062b0c0b190203070c0b 59
    0x208202008a100ca8805000344000c86024a000303020001c298175009007102d00131054201003500e04a0107002c016484d040c415100c03c4112298070309880d016503110700035640d2506405004c244010203040030600c0d074111018521003190000c050071380e0f4403400e0351017030500396680000514030b081c00c00100e90300180030f11000e41c0501c0c00600b404200c1304040e80492090320344101160010914a03104547d0216666911403000340a018462070403000500d0300800d40a8403062036000f00d41c5400b80f81503c17000c80011608042c0a00c804d040046e842c1d03843d15078203204210032a00f05140b507182004444101e801707564503c070080c1583d5589407012a1032441188010a90030307101c44951107001d5981c01020540c9008010004032080f103030003401c030700b03059046050788a2070041c010400c040d60303110541e0000000c06034401c100301c41c9060844407003050b0b490700241606005400030492810301c0e40030382881c0300f9400c00382200102d444001c0e640e9020300c41c001414281e4205084c0f00140103e4007170280 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 852239523 1250 852238273 852238301
    0x6120b07080c040b0a0203040f090c080103110f03070905060108130507050120011a010201062106110405030d0c5109030210060504020702090103120924020d020d050a03 74
    0x811352151001a90f660100381c8010059001081c203100c0101703d405101c0041128030740801080102600180c01544148006031803440069044001034691501030482c00000a0641d0a541d1301d443c1c1c600010f00054404500150070680000c0c10250300c50310309403585400000030300040f4035003001120b102c600c80d00100341141300c1216600400340c0902039000066181c0c09094111540131000a08599542d40320088000303d101069011100d03003041c10000b103070032180110f8200f102040142c203910441c0e00c100d070103100c0c0003c2840e40c0356010b5001c01c00f031485050b851420340c0000200902c3e904c04010003d20322002d0300b070700f84610710b490702c20b080341c030600310b842c01003907080d80000c2e1411030311981810303005600408900480441148104130103082c0c119421401c0014a4000c01c690140500000342910495103942071254000c3ea0070400030241d5000d200c0600b0400c07816110b0540d000400d9502511611000e130401c03500226000100321460f039140c41c01d04044c002d04401500d461500c1c424 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 852240773 1250 852239523 852239527
    0x31b03091722031a060102240a060e040503040f0f03120516050d0f02060c181207121a09070b03060f0f12010e150705090409020315091006120b07080c 66
    0x4a8038040302c1d030407000f5800b0b0740005030343c9032001c0003039180310310010f1084c2d0454100001d0391400010540f60201d9118001a80d50a550350f00e0114000800803a00321001c1041a81c040004004000009206460700207007902000b55440c00004240c20031800010402d062041e0f0340008544a039000e0240e0400c903490300100340d0350b10b841c2c09040c034444018290000300f400b040c501480d50108103c540006032650f59600c1d000121070040e815003076000713138144034002d0310075051401c44d81003010320f000c1c04208813a044c02c20303010b00e030145d01190520280055401d2000001d80d1618010584401311038aa006052455079804100440c010740601ca0760303030101c40035510b014541c442040305480200d180c40005007040d81203950b81e00d440b0f803413464490043e003400d08010a555002050782d041140946000c200144030384002401d10014012411000e49640304209200800081e00d0701c011030a04000c000492302c4542d400c0b0b0101c07035408003400300b40901000c60180c4d4401ca00e100d620075032944d0134034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 852242023 1250 852240773 852240817
    0xf030b06010e0d021201050612060f070e01050712051b0f060c0f0412050102090307050a0f030b0c0c100603030908010b0105090909031605010f1406090415020c030406031b030917 78
    0x24110001035018245d80c0c1c6d900ca042050300e0030301c07020580c40c0036234181c000c02c41e80ca0040302d10a51020000c01c40020004681210813040c3d0103942a036131010f52105101c0102a681e034001441600702c0b502e603101070303c0c0d480000244a1004150354281400c1180a007909070354060740d420385540311821405c42c4d03a50400002664400204030140c21901c550000369407400d0741d1003054a1702c1000e070001c070700ca045a20010082400d401c00350070308407039100c4903107135041d9034448490019000303520400035a030003400800071030382c15241e0146056038482e4981413445510343c80401c3c200e84403000b00d00d02248003081408176500c1c11482d5154081021800c4038988840d886c1d0240c007000c0030241c100c2e1180e454210900c0e506250340201400c0003445000c5046900e4040001001e03410013a0000d423003030040d00c035075100d0045250102e40100e802c91045035510340e41d0340030003401807205540725889440016101d500d824071a0080c100880e8010000812211103000344c040309074801454080208400b101d61 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 852243273 1250 852242023 852242029
    0x30a0c0b0c120a050405031e180306130b06010c060603030e0a0f2d0b04060c05010b0d120c02030c030d050c0c0303090303071205120112020301140f150d02120d090f030b06010e0d02 79
    0x400a1201e214401070b11740e0910300c0062701e9070180740880c5101c2e0300076008000000300700c03440020400341c010800000580f01c944c0182c48000381042d01a06080c10150301100f415080b21988854400079284040720350f580d50003003c00504c10307005204c505280540101c0075002105458064902480e0800912558610381c0c2c0d0310560040d0301090104000a2031007050100a10031941c2aa1003136503640b445002c256101c1d9008805c0c42c03004410310821140a03000d54804000046040001030220b65001400840241098011130001c50b4503100b81d60301c1c00e0480c10040203a44032220090b00950908905589421900f801805503100f000003d11000034250701426803d8003e05561012092041190040c5402d6440c40b92494240d1282c400a22901180210703000d64005440f0940307100054207031001079041e0601e0309001c0c0d4002c050340401100c3d284041080c015210041c0c985e603c00d6541d640034042c2c010601d00c00a0010240000020402e5008141c98001c1d050014140307401100b0039400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 852244523 1250 852243273 852243307
    0xf07020c10030e012a050a142a060a0e1f051807031b140a150302040801020304051c020613060c14160b01171f020c030a0c0b0c120a05040503 62
    0x881c0d607410315028a107400e0105035848001c45c003a12460030601d0007404c06009084200c1503c200f060400001034904540c03070245800500840c441d01c40d8909600d94442c80130340e01c11007558141a0a4689600c00c03484103000202c0c81405040c4003400301c2c5084210803818020075008000f00356003041d090555600c440c05220031405103100c1e4120302c05a80002c01784500d404a50740007109510845643c1da0301d1590741461040c2100c8908140c0c00c1640c041240440c003074000c540c01120298004010b2000b04840440c8210b030210320486c0340b106040b000c0e01c0072070750ba10701074850b0a06820400c0e1003401180b06600001c0800805081c0172003400000b62448a4683c4600500c00c074100c103030b102c3e100801c5030070b490145c01051001c000150482034462510703100c80860700d00140410382d2494040000e0f401d90159200f01100100341e0b0b848a6800c48081c0100180314000c603904240c06002800c2003240d8400e5905403181a40845580d948105646009020141c0300341d0b00c40c03006100e28106104000030b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 852245773 1250 852244523 852244541
    0x18060d0c0806251b110d2105070b040b15090403080403030b010e0609060c07030219030303051308072603091e010605220f05040c0302090f07020c10030e01 68
    0x20090256243c030342ca4404840ba680301c40102e01c880c10f0140c0e0341d01c4560002c0760700190394003a580104028250329214015080d40100316410182c9112030344144445c00d10f03465001c1e03d407040c20882e880e5a0900841c0e070351107001d100a24002c501c3c004100401d1031603c0c425404001c18071f4416030101c43d000013131a803640499089000861100410080541c10f01902ea0711800c20b003000c8016200b003100182c0e007801602c001d14040c800c089486901d044040003008000c58001e401c00d4010980081e0814206080303000c150042800c0101284404c1075485921050981003a512820f044940d6114007411081e000340c000e0034983c1d0300c1c03c1000e080714480114000d8150b48001d01c5109460241c0c0011000d01748540c0c00d4503454070500b000380d0785810540803c0c0910b020000000c80c160f00c40341a00601c10ba19500101c0c0b45080200000c000d010406102581d0080701c0038001503588080c4500070b03010845150006070403210b20400c0c54107004c10f20282c60000d504000c205d502c2c440c1c40301030031580084 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 852247023 1250 852245773 852245789
    0x2a141318091a090d17130510020a1701080a08030604020904020c060a06052103030121081804060b091e1216030308010501020313121a151c0218060d0c 66
    0x2c0103020030780740c0800071071000600c41d0501c0560340500c40e403480d0150000800c03002070105d6000000c41000418010400c1c0e00700200421501c80d442d14100910700302e030456034401405980000800c0b12407001030243c0400c0e500c510b000745990f90300d07000d00c030180d08038148150f04a80c0038840859241c105110b02803090b0000f04000400903e0001009040303d2507004c1ca4000d400c001c2e0507002250800300c1182d040d10b0328450f00702d4801d2160800341c1c210088540780900400d00206550407810707240b418400003603500311003d1180644400340c402c6548901c3c01d04940c00300007000782100c03240d100e8903000181c690003030050710000c4540c4109810602040e9600d40d0000080710700703208041e00843d225026202c20f200450800b50007045900c001c140078041e43c41400c4020b2000b00c01c1025002040140e180d40c200c449520782004800e1100018165401a200300442403422110038140d11030000125002003014100c50701c40c0f5451824a403001d0030035a00440c17410041c0c03010420600448004004d14 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 852248273 1250 852247023 852247073
    0x6090c0112061503140a09030203070204022107080702160b12040302071a0d060e060105041e050607060b0f0415120611070302070303030c0c17030a2a14131809 70
    0x1605c4191241c080c000c00306011030f46425030386004240e000003921400c0798143d80043e55110107004c03083e40c9189018240217040403c0003003145150b0b0102001d40555015000c07906242080503100342c1c070171854000d40c20003040502c100c009181c0b076030a00c0c503003241c002c0c016112003a4586e250b00420018403445065000310010302c000e600035143c03140200905600311f9001143c1001400200140304a10070344c040c4042c0b14a580d9130708043c0611410080c280140b206582e47c4071803510070302405042c02145d1140c443c0e601c070b05c50203062a01070100f1000c440075103901890705040703044e0f89d05504818182c40701d641d201004918103110400802e0110b01980040454600d03614004090320107912803a03003000903040100d000070b40f100d4140c500001000151b070b51a0340e0360301030309001865410120320428140d11345154840c80d814050380342c1400b045d69440050808490076591603c95261960b000041d1000104448010805016a500c4409101040300c111b20b8484003007442c2c0b18895000410b0030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 852249523 1250 852248273 852248291
    0x80d020c09010f030f0b0a020f070b04140718020a030905100e1e030a0f170a0b190315110706060605030f1f0e091009050703120206090c0112061503 65
    0x8501c00d610300425440c2c402510031825982d07040180003544034014030405010006c82d80c14031203601507c51400d001c10040da00c9892070b0405e040781900c103039416034070b0040c074801003405c4880100350501a254440c0003400d6030500301429100a40c0b01840103801c0503550b80341d41c00000c5041c07050f20008031f054800450040340c4e400f6031906040302283c044240801605503a04820b102000740c404000e0a07050640c0568200d94042e9602d48a4213a1081e0001e180e9080111010081d070000d441d410303060f1080ba0b1080d6944a041b0036000040c040030740402da03011491408081c180c1c111141d0821103181c200d0030560607540b0700c015100740781c11100c041440441080340d442140f04005521031002d0310452817500c5001c590b102c10740c407107014142d002c086040010768041c00401403103090002c1d1140421040c455414100c1d02d494150004450750390240041049403840016698090056080a00414240303440192006085850700f40c2459450300300025050b8040d9405010030800d0b40c46c04074040c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 852250773 1250 852249523 852249529
    0x20070e010b03161805041401080c04020703080f0c160803060103050a060b030a0f111615140114010228031e05040e041721151003090c080d020c 63
    0x541600041c10040d001c2c4100061182030700311004050b6000e09058620100880d62240340c1500341c0c0082e9000341c2001003140c40981ca071403e850407290f001c0c2c15034040c1c00f04c040802042c0e1292150140028082c5404124191420480356801c051b14001c21481d10070f08002d00390810040301400d0703500d03e10210401402e540c06003c2c2e5944403860883c100707d96410420a000d2501001c0c0c81514010307650403242104020030b51049440042e0711072280d0b01c6070580c045490350030182c11811901907140c04903841c401d4401d400340c01c2ca0305408040701b0030142e0800b80c00c001100e18201443d41148a60f00880141460700c00015503901e4962413800c0244900b8180038200048402070000d07600701d07501c60744208550001c15034094400c002c549021986907402c1c020030001c0c00c2202040c44183c001018050903030500104411514002e2403084503580300c03043d40751004141d00c1015003180741d110041d03482c144a580605407140c0300ba0f010b48c4159403030302c0d400c0780340c07030304440114000d41d04c06003540c01030349 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 852252023 1250 852250773 852250799
    0x50709060e01143901090501141003020904060902060d05071803170715060e1e100b0912011b3c020a0f0c03020405070e010c080a2007 59
    0x45002e00b4010002880240b00107000c0c03186049503400b80100426460360004ca90030306028590340c1e041d104001003041820036009012000040f101d0750701c0c15403070701d40b10420500c8262081070f01c0820003408c2131840c0c00340080c0c01d100800c100c031010b070388148260069881c0c070f000e011040251800020146030465014042410911856001c252030000400001d0b1004204106401503010b00a8071003140d46004501c004250100f81a01810f04401042a42c051210248035281240c0c0440d160000070700e2545e4010419034a2686500910300180056461540240031104001d40700010303060500300b025084030813103200c0921180c445c40001c40896480021a480751703400120907a12101411003101034007810310b42041d60716160800f105441c074028007081a1180c0c0020b002c05400700c0615201003103000b02d0204074070540c40d200100d41102d105d40583e0791010010384403002d03150080d403103a200d580c0218031002c0401084060b1503001d40c0035240d4a6010a6141c002000154100b039444078500b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 852253273 1250 852252023 852252047
    0x80601050304050c011404050a0e0601020c0d050a020f010c060c0314090c01080f09030f0d0e010f02030403080f0402130c030506040e210f040b040311031c050d02090d0605070906 78
    0x200038014000843d0340400c085040160900303003000303102014002e401c10340c05079500c4907a21003a1020001103c0e1050000284101e500f40c4c00e88030510241e40800c0b040f5045400e000d8020741c4140300751300050600f810350b0100b030700741414941c094010681c0c2d0b80d025198504402000a0b46130340d141800c290301c2000c4070350440d4141c0301414580f0080b9000820940008220030510b02e10380001c148015001e0040380e40c000201c0c040b03d035960940742949009000c03550101c1d6259840c14a00402c008030b0361094034002c55041e95807104980307905a03c1d0482d9080a80140c0c0d00042c1420030105c02001c41c0b04643d900101600c000c6001d291038020082181c00d80d140c080050740140c0c482400000201120f01580c00100781c20644520107c50008418065030f0840399203124000b03004028031800f5410141241e104404840c0d40c0442060302c034590604880f07021020074000c0c051414000071540203880242c0000d000031000405a48410040e12030036201040420784424040c8141c591014809e048 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 852254523 1250 852253273 852253277
    0x10206010b090d0213090c0f150306031101182c090d0f0f050c0105040b2e05061804020d020c1c0203250b01030c060e041107140a17070201080601 64
    0x52001c00000b08481d2030106100a1090003051103060500c00c1780c1c0c0c4108070894000c01340b031210036250001c140030903ea03402003162a0403501852620b583c828041d01d419207074042404604a0f10350300c019101038000d00c5810101c0410002d012945004a0400003d2581c04007440d40b4088800413017241c071b85201a040007801e40201c00c0e40d9044070381004030480c000c003071460f100910706c42c4c00f0300c211064000c1c00c1908040303500300414403061290700741c5154000e0301d61019140401080204044445d010503843c4030b08550940f0040101d450220054100070100c0030042071200e003490005412644450290981c240e07012903400740b0940c04110700c582c0d845110811044d0103141020217940c90003009003071000c02c00420010001c00110b04800c00e4480e40c00760b00042956180e26200400400d64055800050b8207403d04103071a141c14002c00300c01041a031109032401825403140c120980350107103800b0701d42c032a400c0b0790400128003114101c5411031510f203064607407617648001040c20a0141000341 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 852255773 1250 852254523 852254527
    0xd060f1508011b0509011106070c021c0f1101051e0301091506090504051b0c010f0c170609041b120203010b06120f0613022d0a09150e060703020c010206010b 69
    0x480150400b41c081600f00f00b070309000c0c0d1501d01010049814031403095600c4254003a081c140b144039608407101410141c03084880810401c08840c1983c10100410720280a87e20001c1c80000071400e6089a054800010301d041c618003c0c00444891041170200081d4402c27004c000b00400075041d0910a00e80311803c40344c041a043d0b0b25004004003800d055028207840799507502c000c9551560303125448282941008915621028003c1040d8028a40103054401060414045442207072180300c1c004500d6000c0140500217444400c28000b01d001c000304112180524002250464011483d254004084c840c04811203200381e131052509541e81424510301849042c0b1100c482c4e8607492a14079809040000c04002e80d554240008060b054158814056a0b01c009000b00004101200c40910b4502c0080041d82020b805502904144108850f8200090811001b03121f00c420b0204028006030081c9468148034501030300099441c1d01c9101c0880241e804201505560b58041c0038060041c100071544034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 852257023 1250 852255773 852255791
    0x240e060103051605030c0d060b0904060509091e28030908060f04080c1002030c040e06060a0512070212041710060f050114040909050703051c120504020d060f150801 72
    0x302c08040f40580b15030500030f0100c0054004860b400a13180c0c0b01e25003110a00c4443c1e43c0c1d07081500b15901c03081a060007141401030102c1c0030300f04481c416020720182ca0003803202d00044142139003929204100b180c007600030384c01c0301040141280e80500070302c0140f10700321140828510f80940801116840f0220301d03000791041015040c00144490703401900510500e0365000d842404a0600c20341000c1e05c0c0301c3d00d02c0032050000010303254003d8011303901d1000c0d1030304007916082c00b000814017958030403400146082151078416085100c01640190080c011200085005001c5004540041d00481d507940a2602940500241085140401d581c42c403003c00c221410000c420030504260f00071305052100507103100d880701048030212002404030308001c0122103100c1c81c0087d11a90103200545462080b20041028034464142502c03411030141c4640c1464841c1c2d41031800501401482030b1303804000700300d62402058440c0900050010003000003d05046031100f90070f054541d640140c4c025030300d410540 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 852258273 1250 852257023 852257041
    0xd0507180e0112081b07050f1e12030715051519050126010b07030f05030f1504110316081003020a0e091207061a011b031101240e06010305 61
    0xd40c15207040b00e80443e84414a41080c031090b00c11098070380036501c0318107200050400081049020f44108403840300415480300204407091203001001407902941d5104500c42c0d10340300740c01e040307070b509201d00781e03410220326441e0711141c00117030141000207544880400840500c81c40c0404014081114290200c9080b40804400314655000e1036042c03042030000708641041e0341d012100300d159904d090103d2583c545410041c107400040c000c90100d820690080c1d81c06002d2030941f485440d10040600a0b9030381d02c500c1c0f049003000c2d04e0040780c0042d40c8001c00c005030313000e9000540c421200701c415060304041840c0010500c800c000c1c01c04d45240c83e0200280016038030191820111b0b18007219103512600d0b81c0d120309091500c0449110750541780002c0010400004d504828100c3c1c54262100301280c006c10010b40300107290310321044101c100e9450210010b070085c41c80341d03214001c0000009000c683e85441e0083c2c8045c0135030308070051440140402054103203040b00c0341d02c07040030700c5c040c44030742881141 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 852259523 1250 852258273 852258299
    0x503040f050313080c041a090a020f0d020f0316080105031510050306011710060f0603090f0204020d020c010e010c0504051e0d080d0b01030e03180a08030d050718 71
    0x50400030600416000e00c0010000d039000c080016500c0340405a07034080c20359481c000100c050380078a0070200001c0030041d003480000100d5502074150726407643c3c4d801c000c030001e5201822040c603e10f8280300d400b10b0076200d0304c05003550148820503150341b41044600c0b207035000341c50b40000d420001c50318010b1249880219815481008020404500e5100c0c8903c0c4d0840030001e400030b98051160300000507410b5400402c03001502603c3c01510050b40102d201141950310340d00550418081c642d42c104460391090744401c0006024441a00c619004c584c0001e0036030744980c41806015801007180710328140300784500c00c00298040020842402070780c00c068424022882144d110381b080260340580403300400c008480c101c0213002025200151034003841c150000601c0c16825450609641d070254001d215000185060200035400d25800c03030444007980c0d8040d04501c0e00308084000008080108002070029080443d00100c0e00d490f0100300240f0700752442440440d5510b0080c01000445a2104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 852260773 1250 852259523 852259531
    0x10050a0302090402250c08010c0f05071103060a02190507020d02190b0705011d031309050a0906020706020c12130b07141b0a06021f020703091d011a0a0503 68
    0x280540c9418202d40010002e0056007024110040004060b84c0f107800d002c13101040040c40f0351b0b080081c140d2502c03c12406c03256024101030109031146c0b5120803050058001e08656840791405655007490f0801090500d40705441c9105441d0300850110307080c40b41b80800d103000c46998a8840d04010f95500003900ca0422810040d00400c518250401d1506070f00440101902108215a035034201034680700e8000c20200e0045101d01d80e00e001d41d031000d40c3c404821180948465140c841815081ca000c00c0014040036000350022580c031303040381f0001401030024010480c0154070068075255001800790400103a0825080110400c020300188040c0c0258008103550442c40a81c0d22404e05103025910340c1e5000700702c044940700b05491118100c4010444607143c410694202d0b00c000e5441b801a40d0b039040006940d1403040b680621111120b500d68041c00d1898083d15000420b266278103441610018070040d25401c1d552007000501c001d0f80104100410f55121b40105440d15001140c014000c0c08054 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 852262023 1250 852260773 852260777
    0x3060901021c0b010306080618010f1a3322030213020c01020d06080c1201050903070222110d051e160905090702031206030609060c0a0c0618020f10050a 67
    0x1041c3c0402c692180c0e2100740541448401c03901c0504101203401c0b9504240c8441414075801c20070080c2100d80079000355810045254040000407038500100480c49003041c61500781d40365031242012600300341c0400001825810500c180c1e85140a010300088000980a0307007404e8212a4004c00058035501c801e40401c1010030401a100e41c10412100d029114419500c1d00580c00c10310040b80007a00499461a1114100e13400700322000300504071f44c20b84008607402c02ca103400501c182409401c00c01415042c0b28042d1030010040d0400500d00c8003150b0710201c55204031013001c100c01100028500c125600100e403800500c41407000d103031000001060083c102468001484500c1c1c1c80940100d06950180070010007400b000e00c0c1883c4000e40c0c94100080d58038846406202282542c20f01103440e9010f003e05030b0107410150b40e1001c0008031588000302c0b00d410060614108404160284229180c101081c140214002500c0c0100640c807182000f480b82b180b030301041d9800159030020202c6065541038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 852263273 1250 852262023 852262031
    0x26011a0a0519170f1f0f050411060d0207020904080903060705091005221e090e070b090112060e1e090606010e010905090a020a09080d0507030e2b0203060901021c 71
    0x350741e0b110b05100c800e030b22044162103441100c402d1410600007101c8042e118220030007140341c0c20086c0718152a0140d4018081e403013241844003880c20104003e054620498201602d04150380e4041040c581044a058940d03020110304032519180c10310200c0c2d003003041807501034204200745c0700280c0740e40c98900c140c50900900151013101e11128075900918468200e002c070455a61b610100400c10708084041d250340c2803000008100d001151040201c4003d0b00300042c103450342008d031103004a9000c0520503061111595400e4131102c460300402c0003601044954002e80c0c2464141441026851020501c50b04011801c00946207c006030440d400340d001d20300b041c050205a001a60ba604450300a00e030025100350800c024051150000c220803d00c0c1c3e500d550700a0f5885a0a90715515004524000a01d0400c0a4008644503c155214074a4018015100140f60000b8808400d01e0035038200600c9684030104d00c258030b030500c02c06600c11540c50081d8500081c0c0154800f00d207502001e2078900d1a03076 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 852264523 1250 852263273 852263309
    0x12040308090906041103070c0b1008070905062b0b13080a1d0301020a030e0c0109030c0b0a0302120f0a0b0102160e0a23012103050426011a0a0519 64
    0x650342140d030780f17904901412a84c0741040580202142e61608094906488481c08110028010054041220301300000391541a040181400c05488094100340c6e101c071400302d051100624003414003c522041050b09400d004291501540c1c00308000c0007101c0c944451141d40c00890850b03001ca41200e40c291810700c40e0f42c850718151070079030160303e2441901580301140c1d4481071030b0585d00011207000068100d9105001007001101d01000b030f404000d0030740800340e01c02c200c0e0710404005841c2e0b40c2d000c4d060250514200100004150b40d007107400e44a070a40320705c14001d50441c54444c800b00d01600b0b102912549803201201044904175100b40521382c14402d0028100c101c1d50350006d44d00c444e9900d403181d00070080048540301400280035049121440d4400c0c4000da1b20741255420141c0d62644400e03052034504a100940011a2004110100700034440f14051031800c0c4103540600c04044041458915240c0a22220100d6500038070701404d003201e003001e00420003e201c04100c400c0d00c0b2000b440300030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 852265773 1250 852264523 852264529
    0x1051602010201090b070201091109060a0b1309112d090114160f030f08070807030207050118050102130515070f2d0b0f06010e27041412040308090906 66
    0x44c13420003402c50b0003210244018590b042d0040a565400340600c8401342c40c0000811925040940d041036018211180422601c4000800380c0940350021060303201140e0f42c4d003a640f00703440c0484680c2e01c1188002a01200b044095418145207000c000429415840c0b030011000b80b6200c0d42d50200c2c140081142c2c80440ba11081084940500284220060b001010b1901801d000400c1000b10042400300000c2c250300752140340c8540c8030300b55681d142c01c032946801c0070a400961211500383c03099520b409041ba0102d110114200c20503100d0b800040c0e4920000e404101001550b80025204002600d01c10340d00101c168140c031409c07a0070040ba0180980c15160058010034440745820301580c400e041c6140210703020221140e05409180c00003281c3c0da038207a10112004003203a529003c9005890807216074205920340c540001110104090100c040c1840c40b018120200c0e000c8500d0f4441100b04045c0940c188481c2c00441c4e10802214200340c20360b0384000041c000c0030003082c00b502c00b440000da0305607 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 852267023 1250 852265773 852265781
    0x216230402090f060d050901050112080304061802030d170a02040308031506190c0b0a0902090f0a33080a0c030f0521030a0501050a050a18020d0e030a09080a0201051602010201 77
    0x440141402d68078031100c503012011b40801c40f690000e0f9480d00340002044c90080b089600d1851703200c41d1091441da03ca90380c5400614003440c0380ea01007103005404100584080050f00c41010f4070b910783c03101c0c0c10381803042c483d00c0c80c1c4010903041210b4010702080002800300781c141ca4010140042000d034250510010503860300550146a010f080c024200c06800d40c1c0000403000d1460095205003440d591303d01414050320020314009400002d6500020f280c80503c0100030780180340090f010443c49450107054031600e10411925070512402110404a05245d40e6100014141800a0444080107882d0102c440090b48005881c00c1070701103490701003013024006041c1c003c00703410305040001c0e60107009410383c1e0021111900000d04d040d001041030706c1c08500e14801c860f8020000300e0303030301d0401400c1c01c040303111590703c1c2e00466024460020074030781e98080c180f0b110845034001c40e1143e03001c95004004070400e078007903503486e04950a00000345c1d81c007008807849100e4210002e58021041d1004034010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 852268273 1250 852267023 852267049
    0x1b0408150c0903031207080a020906090d03210c08010e010b0f0a0e18061305190b2e08070f020a0206070519081306020c0306060d021f021623040209 65
    0x180000100e042da82e13041454114086c0d4510390340c4221507a03811483d48200e01c6008401e6512000031300c098291442c0003015425818464034007003150325556405210b8060644460700455a21071166805080d4011310450050402220200702549012044a458031032004038540710348000669130900340c06420442034a5801030540c5030200d181800300d0003100e10542d641845541c0b500400041d642030341c081d090040303000b00e241d07459003030700c01d91120010700c4845001e540005104413800010342100c00c205254020764030201004901940c0010001c650040c03451083c40440994803a560b036000814400c695819140e00b03517560b100b81002850016500c1d036500c0c9080c036100c13150081010301001b410550781d4140041001e90303250401680c490b46d0110700303940c1591000001600d1703031402c85c10b031140d268000340060600500245018013503c291100d4100941c0c00010000131440c44400d081c8014410491000b400da40d129240001000c0d0f4001900d12850f008101ca40c1c0d1641c800030342400c6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 852269523 1250 852268273 852268279
    0x250603110c030711100c11130905010f050402040b06031506070611130609060e2b050f0d021501030201021e010b1215070302030f0426121b0408150c09 66
    0x158009441c0c0050f13520240328000380151140c480294000303014003244103407a5405404500110000010b0040190424543c84100c3e5158800c00700405d02c00c0c45110211040c03402c0104140c9041d00601055504141c0040d0048400b003003001040d6410281c0c00301080f0342100c105030754100b14140000503105601350b54196500003d0700c1c0008000b41030504003201c000d42c07200d1100a40e1248144c9090321810081ea800003ca410380e2031550a1201200a40039040381c0d2080c0c0a10a80d16100c3c64080310700310000e82035201c1c2080c0d02c0c0450701044103040f0891400d08403074084d030569000035110400c0c400c40b094150516941d04e4440b0308290403000d81188094401d4804a505c401c5403640c41101c0e1641e008101d828201003111035100b4002c5a100d00b0b8030b5214601d00c0c0e1525a1007001c0d8040595819841501e10200c140c50356040d50002c14a0f404031070001c40e014200114a1a4502c403180c21a074807642c8200000c1280030404201010124518180d00e01d07199100d4070b001034144250200782e94 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 852270773 1250 852269523 852269527
    0xb01120c030902030c03010c140f1908040b010e130602090a0e07021e071217040e0406020c0c0a030201140c0708100c12061d0c1b0708250603110c03 65
    0x3a00c50385030740494a000d0086007120b04030500302040c0750072105186406000107108003100140c0c50801c1c8001c0102c0c0b8400004c5901d4a8803e070421468500c2601c01d290000706500140700174040d4203801e0902401d01c07c0e070410f86034144124000e0000409000003000300c0c0c2c001c035030f0760702990322040d07660010714010a0b00b900701c1c9400a0025194a480180034900c000503510300d40c10306ca000280c407001e5038071482001c0340540a40e140d40303c0b5494414242d00d1361000400002c2062412850704500441c03180c500561112300842c082420321104d074038000d01070000c12104101613a4403610a044454031107234110f90740c1101c18091424080a41c100b208a4400d04001504070b070220b600581000c40940e0780c070342800740155007003801e0321040d00ca000149200c00002c500c0100c01d4a0f8250382040c0c0f03010b40c246c54003550380060850041610701144d141d802548003007124400900000340415001064104c203261600b5001d0100c2c803080c003a580402d079840d4600d1b034120f19407000301c1b000b15003400c003200e03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 852272023 1250 852270773 852270791
    0xb0f13020c0111210c0c0d2606031b0a030f080705010c080f0c0a1b03020a0c05150f0a110307060506040b0f2d04020d02030103020f01050c100b0112 65
    0x1806940040100941d6610380240f0b009034501d10b81c01d4031180e2070304402c941000c20b81d00070007820030034000d002a504000c080124800c40241044040c1150b8400d0f242c03861002c05802000c42c1c0c08030b214a0220b10310b042c242c10030150755004a000f04800403d81c07000c02001080c040410017552181e04020030b0b0701d1074807010100303112005000c0c02d645441031009100925200e0411940d401054070054000d001010100b02d03e805103101038050350070389190405a0804080c444180401c070840141c01503003006103604184210141d80c440900b1080d1806002c0c0007a0074003000c028803c6040c070000c14031020030003e84c568491640341b1009010b10088030380303484e4039043c040010709041d46d6540c41540380003091461402c080202c0070302c202000b060524210034502980d24414001001c0300c280320790110301051140c1d81c40c8003900950200c8100140c9035815441408445114200054180081880087c850100004001803105441c0c107000c40c10000750801600c0640c5103042010255007013513012 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 852273273 1250 852272023 852272059
    0x60f030402090a11040b0d02120708160201050108190203010e0105071d09010b191e0302130e010b1c0f1d100b01021015050306010e0609090c01080a0b0f 67
    0x5103004500894a0302215140c801500702258084000f0144070941800100840719071100500700c20401c440c805450700c99100350526520030115280408100c0308000e0100d00300d50200b190501c4035507400200410350620314000d5548401c400895079000c10a00d6082c1151003e4014241e5003003070344001d0200742014180548802a0500500401c09401a10309101d14102d00100d0480311036210252030085102c1000c0c040344021a4030000380600350312001b161421040740b000c070743c0d0000d540c0146c0b0b0f60728801300f81100c150b103a80808d028015140050000d00a20011103c1c0ca03e003003100f1290390201040450060001c88030143e858a02e4005980704400b04c104911480003400b1083d900603584041c4488200c50500305a1381c0107922161000e103014005034004080c8941d01050401469034503000686411003d030072107620210b0902c180001c5091410007650401080300c00b40044040c132000007400c0c8600200310783c82c80b5403200f460365410703103a070549180328682c0540b2032a9a60305203200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 852274523 1250 852273273 852273277
    0x3140a05040302120a08060f0d020a090e25060c03210212070c0c0e071205041203050601080103170f070818030601090204180506031e070305070510020d0f020c060f 72
    0x42d00036004800125508840e007070b0444404140356114403446d602c407001800040000a040c90743c20018120130030000d0f035070b05901000200348000010a00541d1041ca0307908204003200d184000c00d48501c40c0d4204101548155001c0d0f03a200e2070101f091241609080302c005005500b41c0315001c0c00c00c600d441c0c00c52000d07002089401c05107201c40c0050f0301c0e0004110b90042c81c41501a02541800c20309100c2000c0f0500a03035000034607440c06611036025410050100c42c02914100d6882d03107009241c0700442c4e01401015030002c07090a04200700e40c955143c0424060f852080b0600d04180050100080c3d00c80d00c00303903909190400a1180c413601007a28008161000c400103d01c04c2c40b8039800054420250300031903040c1c540715003010b10031407d02103625000d0032028014075031600501d80d10895030000c0e0301440c6040359146004202c0c4501d541803542c2081c07610340065000e03400c0030301d040101d103400082c1048000c0311450021034083d40b00000728203141e001050158030090002e04840d00b4415000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 852275773 1250 852274523 852274531
    0x120907230d0f0804030b250f081f0515041d0609070c0303110c0303100e1315020d020c030d06060f080420060d060603060b090123120f04060e01062403140a05 69
    0x30500340704603001320b0235201c006c44459450000b65480340011500704440501d02d04c40c80d80e0014214000b83c072000013540407002066000c01c0024046000c1044140b0b0411000e4403c00c980502c05003800d02c0c401007039406200034091f07401e02c010982d10204040c0f19074400e00c2c420028401840c1c4590180c0e1409480c0d034815142000c009445900104615400c0484e1030301601c0009a06c03110445c0076036a03100b40050300000d9624840d070034480d0514640d0240014030002203494040e6a49160071800b5000302ca115070000300400036501c161404c001e401181d1150082e0b08401603114035608001201002512080e0751038200b480403403140c11401c8a07400900540e441c2d51000d0140c0d82d01c480516806008030691680040c0080d8400c42405090b2802035620849185c0128603182c40e6014400d5003000941e004022400c212081009001c1b05200d8042500040c200a10000c0d24103480010b55075800c4400484400c0c5081824540c41d0203a0301c542c1044011403000c01d41842d084549a004001c216 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 852277023 1250 852275773 852275821
    0x3050d0509010e0a2612040924030f06090501020d0e030307091e0608060a0306140411060304151107020d051b150f0d02120907230d0f0804030b 63
    0x211a1810b6031500d4080c40c4107a400300180c2c070302c22500c903506100c440305c0c43c0358052009015082e0100002c0412600610140064450109040c189906081c5044050003450a450b12a01c541400040d20307d80485441039049200410340340c1e003505143d4024401c424140031002e180c41d488602c000c0c4044007031072050319a9111025040c3e0766041d070111103510b051006900c1812204144104c0c0d000b00a010707000300b0040c0c0200303003058072941d44000325032150b840580072000b04420003080050a03041501c000f4806d4a10354103506041c1d5a092551440148070070445480d90700d41010900070800780c6803059002804996281201d08120303840c2d61201c03110300240e034000c40c03001e8000c2c20a00305400154080c9003090f03141c0404190144020380084502660080e020803a00407060b1280003200d011740c10040c00382008520f09500742d0041d554103104030047c0c0d10300010860081c0d541c20f007da0341d016042081030f4130f2041986405001ca101d0381d000180304440010900c107a00c4220440e50411410304 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 852278273 1250 852277023 852277037
    0xd0308160309080d05071403190c050c0d080a0b131505040c0912030903020d03030b0906040e0a0204090f020d030504030b0601051314030a1e0303060b07020306041b03050d050901 78
    0x3011401d964103080007800c0b50b81c04014440c54401181e0101e41e01140d985800040112001c44419a0f07900607140c01e4000aa41941c40e004040310340b18050085480d810503d2401c40078143c1191501d5103240c1030014040e4400c0060310901054100c4002200c0040a000c40008841d0705440104902c1e4100b044017074807490007241070f041901c990130225402d621400ba0aa1810850126016502d01b0840401c9180c04001005071603006c2c0565416200b03850105103a488c8100f88160701000424183c442e900304503201e42049404500c070300d40c40d901070f280861110010300b0111011900d08100940215000c00d592041c19031000180007524481c0103c040961909401126540942980c3c0c110400107a00c0030400070528140318406804041c0c15102c0e905201e031600d860b041e2490322014040c2c01214003400816a00d0f1140202030900d034800c89090105a0b008a6030301c03080100700600703031410a200040072551125400c802180e00100b1100f058050020040c01c2e81c1210188501003242 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 852279523 1250 852278273 852278311
    0x7051207030b1005060306060304030203040905040b0f090601060914030304170f070e041208040f05011d0d02070b031810050a0209010314090a03030b06250b010b0f0d0207020604050d0308 82
    0x21480b600040304c40c0145030070b007107403180f104219281d071021300201c040d032004110008082001d80156031050380104401c071601c0c80d140780c40c080d014400a00e0404583c12400061210b030b5006110201501c0c0e01c80c2c1c030103078464000804203181d88642c0e003200c941142c110324892100c000015290790002a100c040c0c030038565603040c00d156240d10903130300213202c140035007680010148038202d9158841e005e44414a406012030300c07003a00719032100d52041410310801e0744075400d60b58104546401041144000c20319540741403072900705800b000d010f1101ca0003412204c0c3e5501c00d01000803200840b0030b2417080040d4104004c03907000030750101038264046410f1103420b40443c50b460b60901c0c8102c2804018020500090750308900402c01e074039006611040602c0786032101c1c0d00382403881c01d040e02800405244003d107400c0c580380e5070398142c0c003404c400d034010004100d0300100c92080c1c80480d4000103001d6140d400d94400103016021300d0300001e811503030103414242895804049107010307242d483c0d032030450765032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 852280773 1250 852279523 852279541
    0xa050703331d041e05030d1e0f0b0906010c08190c0b0a02030f13080706050619030524060d15060b0c0d09080705030c0d020613172401090e07051207030b 67
    0x1524138043c0c06a003041c00f40500340c0010350001141c951a0062007059031001c000800115032a008003003254541e1180c15041038145040c400380c002c4424280030603884010394485003a4811000140d50300481e00c80c2c0c1ca46e11900070000b07441d00d554050b500c030182d0306c0d10000d40e07030003504100c80c0b51110100c0400442d070501c00440c1803014a50308a4409864520f560300c40e200a01000782c50160402812801d00a0003204d421801002d51300c5180945030340d401800e40d9140303000c2c5102c1c00100703101146003031028594038002405049540481049901c112160095000300050361200c01d6850001031002c0203050080f0b00c0140c4049161030b00c0c986581c03180707149070b655404d900500d90554000d02c01d030001c914201c400e009803030f440140741901d0241307012060700c4555504e5208041c0c010b415248003056a405001007032408a504803d44c1010f500d00c901700d618850180300f01140540c2d039069219400000b400381c44003500000c0c040080070b1950030b07429580c40509220a46641c221500841c800072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 852282023 1250 852280773 852280823
    0x130908211b090907031a0a120203010b0a051c0302030c0303070801080d110d03022511120303070c1e0204060b04150311031b04030c06080a050703331d04 67
    0x207a000e000f4403400d640d40d80003500240000c030f40e0107460151581585106982e405005400740c0307002c01180109040c1407040c5400d5600d085080c600c00d10303590f07100307000503255174030f60300e8035041c908000201001d15410181d046100d912440d006501000040000150300030b280681201e45200407683d00c2e8241650807190103000505404a5070030100140c0003840c801e802a0020b1800441a0071545040c07504004c403000380308900700d4907513034900c06510b204c0c40c0a0106041d55148503000c0c1d8554600744100410724603041d00c1c000c0c08440704203400800d058040042d405540d038007910402019480305c0d50803216800074401c0040784034048200e20381c420321a008400600102c1041682981c886c4410103a40120303000403001c011109001c000f010840700c9103680000e000300d0b101c06a040c100403c901040c2c40b0001c005009040c10300c00d80300e0b282c2e000c40c81d00f40c010500f01c402407447e400fa80803280d000c0c2c1030300e079100b19508600084c04845203824901c00c40d00031485000383c42d04103000308601c55000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 852283273 1250 852282023 852282037
    0xf070b070908030715050910060f060305070c050a0b040c050306040b010314070503060112170a0909061a1e040b0a021c0e030d0f1715030714130908211b 67
    0x4140b4091031500017882541145406c0504001500c141e400d400348801c04031511a408910004031039002040855010300c5010340042c4581b80c0b081d0b03541640d44030700740c2d24000000010a080d000000040501c020032411401510000b8160781a03420a030500103841c00e401c0c0800d5a113000c40758520551400300240e5401180d40140290141da8a4500304a00180310000251a060315040458500c1c21600d4000c0070000c502d0b0b19403044031424200684211901a00100e060045e510b041840028114098074041880301e440300312030b0300904c12405d51501456012410020f0b01040000d106500410043c0d10424241a12880440c03c603404031042100001016050742101c00c220031200e20034502910b141d8a1401c3c2003a988290909050003000300302e8026000c004040c0d101d52403450b007404007030010b042e0411050041d2101c4800030300741c400014515003026640d560003200304140303c000d0b41c1080700c034400c0310516a5016107140340c2e0074400301c3d41d06426406a00d02d11204848030000c3d04c01c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 852284523 1250 852283273 852283283
    0x1213030204091214160f021504080609060a29030709020a20010b010c140109021c20060306060c0118080318030316050a031b020f1204050d0f080f070b0709080307 71
    0x5285d00700e494202d114401d503001070303801403102d030041a9070050300d0004000410408004001618145200d04e042810180818000c00d00740514451043c0200e15903000b8004030191944180d2101c1c0c001920700161944804a044c2c00072402c03002c1c041d000303801c0b104214441904103032600701000c0325908880e40c0c2d1407424003041c8080380e0440822642400003020011000000607600750540000301010180031170062041d000156110821081080c0070b104048114103200364504050000b8496020042c80c00d07000e40703004220031040b00c0c001d400900d00690b0740c8001d6401811641480c0c3c40d580d004036045101c200300049450900709000085a100c1e11952020040010100c1d41c100e505600c281d00b43c03010107032282034028001c0745c030349450b28141e020b68000348855180c248059081441340b01e0200030201702488100a01e4940d04080c00c0c255500020203500401107162066080c080d4150038051a140451040100481814102d0144503a5110650000e40c0d61340c20716640d114002006007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 852285773 1250 852284523 852284557
    0x3031d0604051c0c080a0b011d07140c031e0c01060602030a021b0f032a1804170c070305010207060b0f18041113090c171213030204091214 61
    0x203078403282604840e200134820301400c954640d80701c44c003614202d0707105029a0f602d40c280700100076035808000181d01741554294495442d20f820040684030417101a01d8840500001940e500342c3c00060045810306841300c101c0c802404103802c10b110098004400303445032580f07040c80100f4202d00020076501c00313000b0b55000300762a0705a00e8540c6915001d03400042c0c0c00c00c14014248825503810b0241440c0540302040040e1030032120805110f041411116150140e111080000401200500241d030700982040e024044d000d40c45640044c41c1c42107603803500311401011400b004012040d0000c0030824000e40d400d00c1030402020411103c1c84000c0003013540607a4510f100c58803501c150412503480350041c0284051440780e2800301d06e0200c9a001004051583c07081d20408205902003448050000400000c0c00c0600340b00301240c3c0d40d00f52103c200c1d0010400f090622910407003400309805140d0203803040c080c0025902d001082c00c070080e0044804502a600b45c840141028070a460302203400c0c104d409 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 852287023 1250 852285773 852285799
    0x501030b0a0f0209130506010311040501050d0216021807030608010203070c14101104050901090b010503060d14070906170a020307140a0b031003030f0302120105040b030c040603031d060405 83
    0x7070003040c03120700042e4000d409019484103075581c40b042410341c0f000842c003c191440c00000040c1101c6501241e5524501d081c0814407869034400190391660030401401607680b00c08c900c002801c80122030b0020350010090001130000088040490b0007400652010321003035031038505e02070a0f4041115048000b950142c088004a0900c954a90079a03900d1810380e02e219030b0084120042d24040038400c0c0603c00005410030070340c101070243c1c600502d03c1950800c01c100c2c0140000b401c42c03001030450303441001e190003080c0500920961580c0c0541a0341d0840728901c0c0d8403184040600203c1c450050741d0400420754a1070802d0202d042104c4c10740c010040c28002d400d00300288010321a0708541d540005092801187c040c108000860052000c0d020084107145185001454130810f080031804140c0140904100c503840d07044130074107454049401003141200d4002292810f1820251141d100e402c14200005041e003102c00c0720038901403209103075042210001401614829846220b400039407001101c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 852288273 1250 852287023 852287041
    0x1c050c010f05070b150114190e06040e0708040c060c0c090509010e123a090f05030706090203120c120a0318050d030507030605031f0f0c110c040501030b 67
    0x3640c2228032070400c941480c2c643c3e202c000c484c02e02190314409060700020760385078560308040071b01d036030b90f01c1d41d11b020303141030485860814485403401d004402d02400c034544058a950f03100030358000d041c6c0e5861000246c546608003d14010041d42d003900c146941040100e11940b0940100180d00e80000044c2d0003e45002c20b042c009041c010406410395582e02203102c41903070144a890040d0078404545501c402c2c0c0c0440c040403403080080314001000003010400d50070124004d01c0815407171071420004040f402418807070940c3c100c2c1c030002011404001122810010a54403800805001307904490004181d0503803950f06118444242a0507841103070005010602c4000034041d003c400d25002c60340b000f10b4030816440704050082141d8981245000d5021964180b0800e41d00404624003441050b280c680402e850744629100c494400c9440504a050269a078000340c0c18403450120030018001880c3c8001c00141c003640c24041103000b0000000c04078078090080c14141c80d042100c21400f52650111 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 852289523 1250 852288273 852288287
    0x4150804110a0303020f1e070623031f230d0f0c15080c04050607060c0207322704030e0a03150b0a030305090f04020910020c1c050c01 59
    0x111025600c0e096411025101d01460b600114070a400410301d0949050b10181401030709041d075140c2d2401503d450242840008402003210701c06d052443e80614110b03030120000d0000c203066232880038000140607502c41c210564800154044c0c0c00d0804041e1282220b004155400300313000c980c40c044a040d07800c249010841900602c1c400d0501e40040b8159035600001d180d882d40c0180003101e0413a20308203000781c022610950080e081c00d0313487d1509081400150042c00303a00d502801c0c45640c1c83d94850514001c00442018041c1c0304020100c45d41107018002d20303030306005046070b1004401c0c4103095490500ca485940a54105940e035001415040a004202c0c07400070310940801140440d100c856445000c60302d00914040d1040030000000290a00281c0d4080c40d10203008140d400010030220f5400401e41d070307511000b1100c06d00c000310140d001402a0240700d03022588644400d021207080c0d138001685c00035000096030180181c25000044109420030030300090316a40010701c88001a41c41004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 852290773 1250 852289523 852289531
    0x180c090515130e0705070203070806040206041503020904060306060515030411042f0406030606020d1d0105040503030d0b04050106171513050f04031b2609030d02030703090902041508 80
    0x69181141c07542c400e84003c00b0341064582d00045034000604105600342400040042c2880c0e07002800302d03080503400729a50784120300c60043c0103000e07403d0269541d403080c0c044803482c0c1c400420606c00c094503400c1c100c0040c4594442d05102e44645240c81a2003080201620f2040f50007400d202a10341078101884058049402c902900d080c403c0e8242e410000c1492201a0404154030a1a115414a81c0180c100c443c250064000d641c403491105030115442111240c0e609070500000c100c001c190310040e5054003540d0092a410700010403d600d00017502d42c00b032098107100b12010700c55a44d03a0f000948040240400103414154030b4000034115001800d0130181d914800f401604005060844583c00c80e601980c0c00f5501c1d013050000c2c80141584515000c071050104074484d400d464103552440c81c00030300e001e5069030301000d0f00b100d60b0035030016000b85c55050340042c0c241c520464214600a482c0c0d03101e4030044022900501c00171880803070610965040e40c00910f000800c04101c80c20a4603d000010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 852292023 1250 852290773 852290797
    0x1816060503041421070b060909031b280516080d0c0c09020706020909060415030620120708090c0a05090406090203010f0e0c040c0e0d050f0601180c090515 68
    0x40d032181c4040151650051312070820450464490b4010716008411240180100e4401d14800c1e0500250000200071160b084010207000e0268a01c41500d03642450030365000600d1110250f000e030300c1c160101c0e01021041d40d2080060f1016409094400d00010945000710000c40d80808051160710b07004055044501d070041426120040e51f41c1110400e0341e00000044030440e40100d00045c01f405d02c840c185030000e808031001e100c140b6000511943c2c4512a100240041c1e072520504680f582d0003070080380743c0e050944410b82e5105440c801c1c0040c100e0003550140006200880000e00c000004500c0b2040400000c04c25807400c1d150400f0003440301e10280c0306130703200c0fa90380c0b0150740182e4003440349540300d00411501054214802c1c045c6402c1c290448100381c020303414800c06018155014001c64004202114004410441360502c10b00d0602d42080c620725500c2210b001040310320883d61148515400b40c401400100460b25003282e8035103041c4982c80e040310416040a01710403591014048400f003d03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 852293273 1250 852292023 852292033
    0x1627051002150406020a0806041e020a031404030e15091e031e010c03140c03160c0b0a060f29090111010519050f1003062318160605030414 61
    0x42c0030702d12005400ea4040b10103a40c001407180005411070200c5074030050843c3c04010241316813540d8044084541220008913a0025500080030300941c030034501040c1c198402a01d41c541860090050715100303400d00d10480d040c002c0c0c191001d41d9101282d04030a4080c124003488180c182c82c0c01207002000c06007603894004c10444041002200c810408141d03078203000400d0b5504030003001350071104500840c02006e5121810041c6070a5150100c90b000344040443d4070300a0036980b4111a440f61404c2c0040840c0465401e00c003104100390041313410340ba000803080c0401540c551070541760450650315607280001c0c80039070b1402208bc40d001b40050f074506040a1800e114040c100d0750844104450141c164004040f0341c400e5400319110780765101018501d18480c2d420700f11241c205031880ea1000902460300c0d6204220000c40c2146a4500040c103140d50f0009401c0108200011104559041c0d0062052030455000a55018088012a11030351951851602c550325019040404894210403a2207a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 852294523 1250 852293273 852293293
    0x30f1308031c0608160b0d0603020607060b130c0c02090606040503030c1006060e01081308190e0f0105181309052a060306130e010b091627051002 64
    0x8140000e0030419440580889007003803402d0160b00300d5603144c01807080359001c401c03000f429030140c6099900362044090b80d0743c6c4030b00c0d49840d4038018010079000290030440100703441040206e160414600c42208642c15a0380281c8204500229101000384e1000202c045400b1800b42c10008040741d0402005001e462a0030340b10004680745034041c603000703159503204041072106074805100790340c0501071b82d141141414102e2070009000c0d0201508103c500c641200c0c4a80030424860100c0b4003142c04070030f0501f0004000400901400300002c001802201c04400358489076110b803049441788240c50400c000011041010b10030240311402075400e00d50760740c00310390012070350030000c98603540d00d2842e055503084032400300090206400e1505070b0207140c05105003d1a40e440d14010000d80c030cc140310020b5580e00c04405c95000d41425942c16800038004414400a101c1030010b109010030341b5183e031905014803802c40002c0d50b851041050b0b07a0708014030306125034034104421040e0420356204031400180 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 852295773 1250 852294523 852294539
    0x30206030711010c2606010c08030a0603060c0815012d050c01181406090c0603040f061b03110c0703020907020a1209150e0a03032016140a08030f13 65
    0x201c52040303600803941c1c81503070188400e9408100201344203400c005c00a28104400007910040e014000202210305c04800940302c50380d6584a9001141c010b0341c00d224124030035034003522041007600c0d400c0c02c000c2c154400040315402483d4000c0c5410400c0d412040344020f604d4050120b00d03010320483c0805c801003143c805900c40900540c40d50241d516280c043c60342c5686000c050f402072110741c402d0303507030031201c00c00118a4001c10301103000740c8141d80155490b038617450b02c100c041f45043c20051189240c4040264440d00c0c6000040c510703501074801300128245003100340307403500030000390700c0da258820001440181000c2c4802d5801540c240120b0381002e03495541e40510000900300100021141030080110102c200e1686078002103a042821840341c201c408101c1c0e8041e180406414804440841b4060070841c81c4000c1451031000140c40340c44081c020047c00e0b42180d4401d034608000c104030394162500d0180034181c1110780703103001540707010200d5000c0c2806402004080210034544000028400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 852297023 1250 852295773 852295781
    0xc0c060c020c1302251104180b0a06050306090a08031b04030210050910030221100b0c100f0507090e1009051e151c081b0d030501050105031003020603071101 69
    0x44401c420250312051054940300038101d040b03018404c80c40c6140d45c0d02011543c000080c2400036410755000c0382403190700302c5440d10b1580d294030082107640c9100401840c0200b90340b02109888003102503881c45d48400310080e5841e011020060034040c03041020480780b0507841d06035049504108059414140c0d69000504032401c81d000c90808140c00007120a001d1811440e0030301900c8140c141103040440120701101203010841981190101e20350201d860641c1001da0603005008801c003050b03850807000441c50300c54460b280000030080c1003040f00314601425010b45442084665100c81d1218901550000001c2000d024612b41451004020452a1160140e184140514452801014010380c88079500c0c40004004a001240900c51040c0941d12031140030400f0b1005804416054040e040c81a510702c40c858046c0c03001801e9190f2600c0004002c01c0243d0415800e4a080245a036a040191420321084030f41801016a001040c0300514111014541049151911001c01e80200032154211 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 852298273 1250 852297023 852297049
    0xd14270a0806091014070507031206081609110a2601030308060117060105090607030915020f070608010b0d02070f06112a1506030a0b100e0a0c0c060c020c 68
    0x20b030840d200300811a0010130041002d401d03140c070108000c401d1704c01411034000000d00044100040080d13070724203040c4900561003070200c6c00c0c04104031440d80c6644032507a44900000f4065200b540503400141d080c030611401041c2e107444188540740c580d003948112034074000e451010b402282418204444030504240c00c0340039611a4481e1480c2e800d054001528190300c040d40d22558180c4041046156640308082d900030442c1598025240c5000b40b07415511041785411200440c55401d000d19030f02c40d400140c0c1038000c20840240e988182d00c40b40116681e1100340646a48010100450b2007502d150340d0081c440c1500800000c6056045941c41c4000d40d45400252504140c1c0410400d40000d00d001141101c2202c00c212403070340008005a0a40300d104100c1c00070b1b00c42c090400050540c3d1170500c5444002030384110044921305d000740c250344846245020301d0001c40980800074098074020f2040d14418403690312400070302c801541c0e0b014003512040149504600613401e04203500d44508003c4401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 852299523 1250 852298273 852298289
    0x601020709020a0f031d0c22020f03040303050c03012919020601081002040e06120a170c061315110d09061a04020a0507080a02011116050d14270a 64
    0x1584c103001e0008040d42c0c1c910071000b070728000c1d582210035610300000b80300f81000c2c015a80500e05030941d011010005480088402546000007542c070710b00c0c00c00c40700861195202c1d450400c0f05448040340311146000902403044400c00d42c1240031800044000400243c60040d00c91034541001c03900412950310368030701c440015034000c100600c4411000d112501e10300c400c002e403c40c20302d0710b81420000545000781181d4080e20519400e1941244103000d51001a030b00015648481403608140d0652984001107070074a500440c401b06401145039044400c005400054801814040b115004000c01c1c1e405001010007204100324000154540660100d20340103100c001801040c001104500e9044100400d100d01e1040150288490708202912419500244c515850340d001500c10b80c010140f0144c03000e2481008121aa40084103060b4481100e101d02d090b11889102e005003030310b0614506801c000b00036000c0c0000e44116080700c0c40400d1441d04020130000140130000070850820713007034100e400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 852300773 1250 852299523 852299537
    0x702060c0d0f0f050a0c1b0e010618030812070207081f150503030708180303030414010b04060602060a090507030206070b0f0c180607020d0b1602101b03050601020709020a 75
    0x4001e80c10a0012040400c28200041c0b14002003070010810312a000310107050000c80b0303500f1428001c10f0040800040706040c1251070312601c46101c41d1010800f4450f04001940d0107090f442c41070851118441100d5200c3d035124204800390100b140001c500030607500840c460340c0d50010701404100024180440d03540d0103902c0351011034264030146d501480e80d041c804001d2550070482a14000125541150080035440c1c450020306240c210f1640400580c55141c8400b00030300c010305c0764606600a4600c9c0910003040481c03100300038001a555540305000c0980c10105c0003d0555070250403c2006c04d205005072203610b51643e000070305a4010910176180d2140320001c100d86030800f42000c54000911881e21814400f0801c1c0100e0301000304c0350828082d941c08901c0d04219102c0ca403100b405035511154145451910b01c98004100300a452500018410700492004a00c003d201d94810007085002400381012041415405040b01600142c114070a4810000c0c10740c51920192110a0306036030340361 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 852302023 1250 852300773 852300793
    0x2010e2205070e010905090105060307050403050f0303061f080606030c0705070e06091003050d0c110405090a200a151b1104060b03060102100507050f12090714031e01020702060c 78
    0xc02c40f03400d0b00062414000592018045642c490100504442c1c2c01c48400c4c0c2e0f00c0d591104201c1e018003c41c3d10003031040c440c02900850024012014511416080e541c401d403500c4900802001d1800759202107003c5120000801d0300c40c24900005c5901820f400c25503480e240407aa40d0b1450310b841303540400d03059070a40060005600d0320302d00b0180c1068071280e854403c0780c1180c0f1550348450000a810061125403514001008280304500b010a04001d01c10080391038010174041e107070080d01c1c0086400c04d2400e50700e0f8200f1800116210001500500740c035944c2401d00040340c0d80f20b09010f10130014400c1069025062058014100400030311071245c032490b00e60f1724000d00c400d45004c0d4102c810011418010085503907030000b60650b070b00040031004101c0f034484880039915446200070760f00b408840018200c0040100c41c070024005d40c09c010490380010381d505109008034007011134ac02c0e8541c104c007004500c00814048003542520a08000604d024425800150f040d40202010107403500081018 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 852303273 1250 852302023 852302027
    0x515090714040f03060b030d0912020a0914092a01031e060b1b01051603020702150a05040612050121050c09040f02010e011e0309110d0c08120c030702010e220507 71
    0x20540e0510a47c0109000102ca140141c0450183d015001d285254440c0003015541c802000c0320081c00c05403001c01000074940606481110b04442880040c412074480740b034200610a6090001c2e0890500c942484030144011009011456501041c15060b2651903405450521030040280103020310207540b64198500d100380100d5450b06044079900d407001b0044100441041e11039605410300d00107a5a00c003a10000e40e01c1d1f04005103c48030341c0c0000c61841d4046070407400503c00d0f10b03ca81c9540d4284d501300c5a030102a650700b4040d84421802c8180d8030101c660070f0103134444109102d14242c681c0c0202c1c0340c010425051003105e0584601c078441d14000250b581200740b07100748c08000c0ca400703090710034180303060840400c070107800504250355043e0900030300045045c801c545643c010610060360081d410481c00048141c0240b00f50344c052071f076500c44d542c805c00b000c542e10000650084e500f002c12540054900c124204a034036080b243c200b24035110941102380a000c40c52050a0002c1c00781804480 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 852304523 1250 852303273 852303281
    0x10f060b070210091412100501260604210504091e0c05030402010c1202010b180f060105040f090b04020c030a350a0203060409120201090302060601030515090714040f0306 75
    0x1031030081c071030b03408001e00511705084044444401d00b070751070038000c080010750503141801d80f40170205042d01d458000710303500c40540d040380b804540384003400340d80070905404907071154420348005041c0e1000c1c1e041585400381c1d40e541c4c00103000b154140541440e031382d01101010b03210043c41c55840064103d00f0018108054481c07411000043d140441c1540f40507800030b82628802040a03106803d618160202c46100350084201c1d0100980310440002d0320364060a0072031416030711b940450103d18001000342d4415010b0b201200e49569014a480303140403c2480208043c0c24401d0700550204910007002104200600944195503201001711b500e940304245085000111101c07106a07810031512484041c0041a4000d000c0800042ea40c0e202c44001500411950b040180604182e50f903110301180c06500014030750b80240c003502c7d669070b9883c004604841046800341c0580182e04d04a004509100c003500780e0120103800c040030309803001c0c511001503401a600c4000403d00710302c0207200704003e5000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 852305773 1250 852304523 852304549
    0x160312061401081821040f1d0a201b0d090506070b15040905031335070308030a021b01060b250804090614010c1211010f060b0702 57
    0x70004901c1d20071903000820300c10380a810241a038600e000e4554224a0034018142100c140c0d1007412052140c01c0740c1c0c9691500b081c8180d4401110702c2c1400102e00c0318102151420b0a404010b25550342d64120b01000240703042c141078840e031040b1880280d01c0e584508024000760003480b44003010092001400c1e450501107085074400c000d9141c000704016205c0c1d01c03c1c2c0301900c0d84000300492540e02c2c0349512280b20400e19185030f009003132449400078410040014410b021840b1949050749450308224520b02e0301c800071810076803906d421500f402c0610b442c81c4070750140c403040980f40c4460341d940359000a03030020740e00410312540c00180759400c07241c28035450341902207000003805054a040c3e04650240203860212000749203020040c0d0301045a810350280041d4050041901e840d2100d03040e030000d00c2c0d01e02410580e000204840480b541c001d800000c4113581c04481e50f004c041c0340c50411107000302d9261100340e8a64a0304801c0c410f81485005910140610f94040c03070b15040140100240084444 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 852307023 1250 852305773 852305789
    0x15390a0b061e130903020102090a0906062307060e0f06040309140a03150e16030c0f21080f0708040e0403090b041a09010c02180103060f020c0316050316031206 70
    0xb001c1c80c0941d00c4a4407000c0c2030051806001500ca01d2a08059002e88a000c203080d031301050b00203000c6000b00440e403181042e100d85039240e0024803120081076040013401c403051000f24809100460000f0401c1c0c100c443c2c4e01d41d5000c15540d001012424681c40c2020546040340420703a2500305004400e15060350441e941d004030760200003586583c80d084085051707900c064900b0b5843e039040c0c0d03945d8132040005408032040360942103082941d905017402c031101e580c001e0400c50310702c880c0f0000301c3c000e50500d4400b2449028030100303d00c005540c6c0d030090795846810f4a00c036403002880080003007101c1c03901510003400c8001c1c40c4001031405140c0184a001540c00c015240c000c1800188641012404848040e8900701c485c00e40d65800e44e030042e44d003804903410096100c102c0103911098201d041000da0704807485031400340015812148140c0c183d0051700d080300c60b240d1007409281070540d842030035841014054401d580c9809251071504521743c0440c60140d002c14911600584559007a12a0784002c0190b4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 852308273 1250 852307023 852307069
    0x60504050c0f010e0603100308070b091b130c030b04060f0f0b0f0a0c020f09010602030c07060509010e0108060a030f0c0602061e01120201090b0406090515390a0b06 72
    0x3120011307151044c4d528100b03010f620040009903514118288070740c051a001003c4984031100e07440c2860707221000f03c82d4012140200004c0c03c01c0080c1140240b091882e000780281c1c0c00100c4003400e4001022090461020182c664141d041036450b01e20420000d0031150740c002c0455800d00580d03c0e090303030941c3d00c1850741c0101044a4010071a014041d50030390003081c90700c015005490300002c0e404120000c0103d9014844200010b80e083e0000700800b0036549450139190b50580d91102034840d40152400c1302d01085207507880e084c640d0710408446038404401070001502c15169245c00140f4440c1c09000c83d00c080c03080205010080c2c040080c01da1000d80d020583c09180d04401c0c400c1003040c811b01c180c080700c404c540c140700d0440e03000d2403003c40035084070f40084d03403529502c100c0104000810b11038280a9000a100020b64403400404c4032040907502d404e00c080f102c0d05001c00074600c800580d5170748110784810007100300d428040c8020560140500d4000c89a414150200302450013041da40300703641460 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 852309523 1250 852308273 852308299
    0xc0302120403033f060509090a03050a12150806040b0a0515090717070201230f13080c0d090f1d16091706182a0a08030304060504050c 59
    0x8000007441500111066040351070719100f042c540b6006124003d4104048080414021113090354010000c0311800ca40d0300c41107890744a05551201c0404002074000f990402c414601c05000d4030040b5085071106a0004910000c20711856103d402070300420102c0c0c00040c00c1c0810300c400c1c40c0c0f020f50025520b050400442c2070102107540c1000c810074410b03008562035400111100c0c0111100610944500741c214601e10700403100074000c10002d140076510800004440a49004001c0d04912601283c0d44901c82ca03240d029400803008410139040340c604504001d9200000c1e01882000c0140c81681c0f50800c1403800d10000803041c0f4510f401c5168030034103101d228844106400c840c180c106070f03103110804807100710100031100b603085908168400005da8181c1c159000001031041d21400e510403498858a81202c2002d850308030303000548658410700300e54100f04d0804007491342208e8200912a89249a82c2c80002c1e003550002c0f03805445841d0342d4400c201c2800130501540201c40f20407181c040440d00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 852310773 1250 852309523 852309527
    0x21091a0c0a03050c0f0d0e010e031620100f0807030c020a020907030e0a110306090604050607300507090510052a010e030c07060f0f030e07090c0c030212040303 70
    0x900700c603020405880f01c2c080307120a14108100c4449820303900640360303180320380314020001d0010725100760381c95860070300d101c9140c08000c0180e50303d045451400a50000e0103855080302c6c00c4102c0101090001c10060000c0e00303603151144580d034450b190b00c3e01081280d21020161080000500340c0013450f052200380c0c00300316808559580c0060341100c030700700b49803a01202103008181141908919110b062160000d11018440034803e1300011070868081e43e41d80c0e2034041d212102a500140a40d00510101c1c0c40705000f920b03803d003001c030b100d140642c003040b8194400e21462980b01e82c00800c0c541e16000d0088580d4070100340405080281c401e0100d05044c480010190701c1145496051031105410b40350f02d400c40844034481104405009000e88003c5852042d225408030129059500c01d4940000360640a580318080c0030901c0e40b11094003c0742204180c01500440c101e00395680907011000c00c07805070754401d800c540c0ca007541e155220800c0d0751801900c0e12a00300388170f5010b1107040c00300f0000a6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 852312023 1250 852310773 852310777
    0x80d08150f061c0906060b25020906060a0c0204090308041104060e0703020d0e0303092404080f0a11060106050a09060306080307110d0611031005010503060d110121091a0c 75
    0x200303180043c928280f01d480202c0008151400c00107040e00d04180c4000360202001c0c1c058580070745400c542250800e200b019a104440031101c0c02500711401e4000140c0340d01e03045015011620f500e041940304420141d0000c4e04440494004801092a44051206014081084400c480400d9404101844c104601c0d0b48080c0001403642c400c168000991100703099482d0071409403240c02800722500c85c145001c03020b0b100c40162104010090000e0560041130000300700d0305005030b0700f00200b0fa00d00008000ca00342d0a900415040d010700c00440c40406400904000440c002e02a65542c1c42d15900480c1006102a61507481034080604103c0140320054000c011a005264041c49800f00e0304d0183c0c011901008001001800036803500e4055040505542e009501c204900d000034a4400d40b035200640c0c690101343c0e81140c000011030f01007000107a2440508640e90320504000480344950100c1418803844e11108000c2d80c0e407104c41c2c203c1088030711410315440300c11440c2c500c101450501c03406c0c0914 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 852313273 1250 852312023 852312037
    0x1030504031d010c05070b03010e09070f0317160c0806070309020a1e0b1306090609060c0f06060b0c03070c09111c0209090a1b08010b12060307080d08150f06 69
    0x15209650000000e41c4c0500303401d601c86a4000103403801c559a8101c0e1a000390400d2040004031000000002c02c040d501150041c00d5a42c10340504010a003191500c8140c1118180d84841d01d00341080301d40c45880188414104d903502ca9500d020040e0b0414416038280354020784000149400c010700d560050b0b40388000c1105540d540034201c00103c086d00711808540b0303079960040502110020703c41441551000e110400d43e1411f442ea030031b0107940e0710b4003111214018821940050964946100050070f0034164a16035806203102049240c6c4403180714030907074042201150f499200103401e104020042c4000802421125010440301c1c0341c8201c3d0b49840e1145880c20901d070762400c015a5450b80701d03503040d1202c080020305000150f2801c50b1018004110950540104860314400150032074810041c0e2030580b803142d1951410b0200c0c000b080b003103c80000d45456814082c000c0003042c8890104084101d60f02541d581c41e045090000c0c0e03403c903034800c011001c0e01612258100f010a0f03110072080b1490 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 852314523 1250 852313273 852313307
    0x7061d070e150d111f110327150a0f1704020f01080a200a021c142b0b0a080705010f0c060b0d061d0604120302160804030f110103050403 60
    0x2401e20304e01e40300d440c030407540705696409102d0980120002040b401c14680214072074640301c113020f9000032169680c0c0110041ca040c09001041005084900300048070f103070030806000741d038811025059a0541da080f100c07001d030018003030540407002543e10020000e81e41003e8001018582025008510a44d2110102c01c1c14000d901c40410b44070421030b4070002e8007510340443d0104d0401c030704805c1e45e41c1d03621280b10b0b00b006103d0030f03030a20482555020380c0c00740d511790741e1a0003012240750303807855a40703801082596040d01502c110203040e8010a071030b03820000f005a040091030b0650b1208020000b1034503007214866510031102070215036000303000003000d4061400c02030114101c23031030090b01410001d01d5040d048480c00150f1000c01c106904070b06100140034125030607580c96003050a0391958100d60182038200303045140c060702402a03000703101e420410783d441203801196449007807582d809544200e4a20810030312903018403620010061191600b445c0c00c0c0701600301901d0040103100b00241c4110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 852315773 1250 852314523 852314539
    0x17070608040f05010c020d031a1e010309080c030403021f08010b25050c1c020d120e03070803090a0509040b1b04080114090105060105030106170c07061d070e15 70
    0xc10311242c8540041d001da40035009002d514030000001351262500500b10000c02d05020003107071a00c6040f8800003c580004d40a8a0713540b00e0b608500c00c1d01d0601d4800c0c0d0f4181541c65540c40085440080241134140e0810000e5075651b2640c0f05221010500603c0e44081c09100e007920040c03140d009c0c4465046072400703541e40c1e84030403030703904044004104401c01410b4640d403102c141c81040070101b074104032900c0458200700c03006091941e14000915840b0002d5100c9104203080e4001900c0450a01e40401d0070716120140c0469131010a2a0032070031f8012050315400803030300d51058030f8145070200181c0300540f482c541c00d08081e95440540300014016000718200c0308410309003220041c0a50b4000c100d500003d11210000c0c110351002500d05458144403542040f000440c00c0d4000d0307003107074100d0307000796100d01c0b81d2601c40c1d090403a6098041c200c484030007401c0040301c022511901541207407100d1030205040c218008402c05141803034980c002c1c042810b00008000c80b55052005046c130b818010b0f2a490 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 852317023 1250 852315773 852315781
    0x131e2a03180501142208070503040e010e0a0515010c02060702040b0a0906050a0f0617091906140a06030201120c12020c06090d08090a03140d2417070608 67
    0x50060100e0302a070000322804101440c080c4030054104480c0c4129060503d10b2540310f0740030350854000351100350307400f075011034594a00051845000304565406401a82d00385500e0b0b960120070301d80d080c3c0c0803203c20b409100038131002e91180c0c42066002600210380c00c0c080d0105000180c541c0207103410280c4118000300d001801e40d1584c1c0c0002e814004021310b210300d0f164884110b80c006001d540203260280d0030111001c9140b680010f6480107990190712050010004060704a502c1c00008000221a0140340a12000e4150701d400b004509403084001081d0700102c03802c1c402e140c6000402036240242001800c20260341c02100d8028030081003000031580000c03c040c00e48103140200a4801ca40b4400030311854a0003011a205015500c1c0005542c2c401c0c1c0c103090100d40d400e03030a0342c00c8405600040d00e1000081c0c003406090442005c0e04c80c6103800c00d001002004102c0b01c1803502103a16045803a001c0c2d01c4c4a184c901c0540142002c1211481107519910742c541c3ea4590f24000c500c00c0c40b014402003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 852318273 1250 852317023 852317027
    0x6151d100f1e02010509121c09050708061e3601290102010c141903110d06030c150c1b0b0f0909180c130209131e2a 51
    0x100000c94000520000310310842c024000e001c01c8903214250701a0369040d100c1c880300341080760219103039150020005500280100004c20600b41d085800f84100d0314001a0084140000c92082c0b003100002c040c400c9180b0441c100c01500140030440c184145030481b140c030103040c40710000340b0607040350141d0000f560841c45401840480c60111303041545032441c401502c50035644111245c4207900902000304241300c141d0b6603040d225010350302d07400144aa1400c07000d00010302190040a45030203d01c0d80c04021200300340e640031408090296442e49418070034402600200c0c0020406900c07107020310710400c14010400b00c07102d0b2004050111541905003c80c4c00c40c030641c806081c0d101d103010b40d0b94054261205a9034010040d00740160382c206c0000d040040c4001144882481050143c0084442c1004121021000702c40014400ea030074018032001c2e1711505032184080c1c8161000081c5400b000090815100c0820741001145050400060258181d01d16200a625044a0503104081072801c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 852319523 1250 852318273 852318287
    0x31911030403081812031906050306012d03030c020301050f090c060315100207060f0309172101140a15051204140a08043201050d0f06151d100f 63
    0x3100074071611000c4580b5001d80401036004003408030301c031f0025101d0b401d080016106180f0506a01d600a803004000c0c2e1050310800d4520084005a10107008903e20a0311407412a160001e4000500c66030010045082c2440b40907048240b0205800040c98103510751070751191040c151070301541c408404a001d0104185d5290190000100603d01824010714025a140240d1160100284e01c0c503200c07485042c020f1180c00c0c5c065070400724800c140306114116901d543c0c841746880f01d4210038181d441c1c0750361186104a60191400170004020302d40501e0401c401c1000c26003018400e040d01c842d800d0070480e002030880312950b04240e4a406075030388500704034004454206001029001d1002ea000401c000c070801403042d81c0e6400c0240142d0048402c040c80030742d40c000482b100904044240380101c2d0b00500103400b204503c01030108c0c2c61055054500d05440a40d0310400e071400c0015508a11107802c204504000c078506211080450801c00c0003445440281c03408005009800d07410044071445851 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 852320773 1250 852319523 852319561
    0xf090203030f130e0411042703020708160b191e09150203191103130f050f010c05030403171902250308041404060e090303191103040308 60
    0x205581e190421481892201d80c003000f0080700405103041c010400030212104c0a0060f90004074583d9288a8401440001c14103d4450f10011101034007101c42441200d031401040c9100f039025040b05880d0000080c90020701c0d046c542b451007900f8800b80300322512141514400284807500400c441380410007590f4801c42c9400c035400b801880f00340401102c0e0060000c40882c2c00007030520301310015107c41280c4a005004001c2e40d04d00740138541d2402c0d01d01c40d80000ca225074490b029245880c0420b07514030100d49042d0301c14030800074440001c011618150380486039030a400e00380308a0032102a0b03140f07500e030711450000034414940d181c4a603001400c074809030791862103407401d40350742d400344c40c0e03000b940c1c030050100300e466404000000c010f19451821060350032254842450b070304140c202800e909401000b40405500580d541e80c0010746440943d0400740601c640201a40e620308101c6c18458607241c45003000017190341860301d510908120780c0c045a0307000b034040c80d101c410f54407013030320303080f002e40c0848 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 852322023 1250 852320773 852320779
    0x3250f08121615090c0f06050a0305061f0c12020309130e0a0f14060c0a0507140f060403110606010e0d020906040905120d0b1c0f05030415050414010915030f0902 71
    0x304662848030b0700e580445084d900680002d08401d03694092050024824018240091800e100c0700e591140290840ca4011b003004102111920540341c40100040d01016500c001901545404052210303040e541c2007004181c0c17019500e0f101c1800b0100e09034030700b448401034055541f030007406901401030240b40c124903070010000c64445407605042501403000d03000e0150074020794004c01d442c00f20715000c50b15440d107540c480368105001a01ea04140301c0f203410120249019102c1c030500c5c0b001e014001c06118502c00e44032007115041054500e49130050040405051005969a080c0709039148210341c02036031b5040780c88401507075500d03000c28042d00421800030454810300d6000c0c10f0844807040903140000080d0410480440b4217010003c9004102840fa5050b00a000000c3c02140076181c2d1080e1480c047c03030132a4a0300c2c1d550305c000355018100b217200c800002c00118003801222400380615440103000d103402c1d803119007449090300c15040c00751703500f0051603621903076401c003011150400c0540f10340003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 852323273 1250 852322023 852322043
    0x80102030c090f10321b0c090f060409030201090f0308011a03060901030b07020115030b0702240c0f0c0f0a020f03161e05031b01090e1902031503250f081216 69
    0x10200c6c61035a111886000c103440e0060801c00f44560400c010b006120744071183d61503034140c0700c0f942404000c00a0301c405500710b540300c12400e00810250303060110900c4c03280c1c1e01c0c0390a13589880364071510500907561900e142e403c00c00900c4196074030b403101241940c0e040710b015410358079090b00580c0140121541c6c0700003c64803540c00030a000a045095210b80300715001e4820754106540780c6008224110500d95680310303400c011499600c0028040c0c40c022190306460b0b850001c1000c0094179059041d404408294000b920401c11402c3c09607040e000c03c0000d800814620107118803004400c00075000b000750301c4120103041d9000b1400010305100405002d410303503011907101d84060040745c0c0a200201c0c00700380701c00c40005004001d40308840c800c0028020051070b1441c51003072207001c2c0d88042e0140d200b0076500e615214555500b400a001c84c0810582c0d04110891041c0903400318074010b900c1418440c0605c04100881c0700003040c04001459041c115139a6140f00c0603812400d652204006480071000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 852324523 1250 852323273 852323287
    0x3020a150612060c02161a360f040507120c120c0314060303041212050d0e0f0c0901050d02010c05070f0e040c080c1305090106080102030c090f1032 65
    0x1030b8483e06a000c0b00e5403c1c0ca000340400040030150b0403087c4074410881000800280d411001c14024280b0742c0303510802980c0001300d0001711540262003d090705580764102002186e24038000880160204042e5418080d0349000400500061740e00700e2503038407080e11545440001d0340305102c28403018200003410071180b42c00d02c100400501c901d039561614414480c011031401c8c900003042d01c007155000203c4c4c6200710b030550390711003c503101c0310b0445080c00300511980380e001c0750a00a6024080d851801858090500c03a040e600c9e160851110f503010720440703001072100e41c40b00d903002c603601078080c00c0401c0315110518006c1c0c60407480b58054100300c00c07400c0010480031910b0503282e0240b4020f40c4031642490300d0300d030140d0b01c4262000619134000004a0740d0301e0030740c0b0a0340000c3e03805483c400000811035a504982401c0e03134070417144481d0312500041c0540e030501c3c00b51543c450201e4150391072010101d5201c8003800d500f401d1880d0442842c5500100008414203110a024680743c00c00180d440d002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 852325773 1250 852324523 852324533
    0x50909041406190b06040509010b0c07080d170a090b2d04050c0a0f0807140d02031f151203050c0304030f0c05090916060302090301060305070b130602060403020a150612 74
    0x1040620750f226030b40c180030f524400e81c44e0410a50f400d852004000e188240d11f8000c405906902155000840d0300515a0010754400240166142c09040c0c0e10f90f00010030408545c03104141d00102907050641c44c01c003014002c144c4c01c0c102d047d842030500c02c0c03c0c1b8029404805903c40d2094a91156900400ca40100002c0090108100a19003429109040845c0c0c0f07074020514844418060350711158082d01b402c0165810314100d42a04030005805070407922000d4022909004852002d0ac04003c09001207034940b9a00c1d100e030b004219035011000c42a1410306292a0b5440c1d1050b10113000c010003c280b51002c244140100c80042d43e00600c5810310f141d061410003401c016500ca514400d9030510000b80c1c4201020980b100d40380c40c81e0840c801e0442c01d04601780c00a4100180a5415640e61000800055003c0001c0c2011701030b05040640c88054004500d038101c00d85401050454108206100001e6000a2000540c030307803028210141c490403c008000509840d40401030a026800025080c01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 852327023 1250 852325773 852325801
    0x60305010605011b0f021512150a1e030b060609030706032003391611010507020901120f0804090209040f060b0f03041719080108010c050909041406 65
    0x303002030304d464020039403406400e09140320064014009000702940c1c0001032405001c0312500c8600036800600740413513404101d040000c01c51b000403000c0c403152180042480c0c144000801041e843c0c0b03d024060360f00c03040b640f60081c45440010112b40c03803200842c80540da8407090b201d08910180889030125500c042c002d0103440307984050f842034052100c00411021915040342e00c161111811513041c3c02102200b0b4410780340d8041c0c1c8a00a40c807002d10010440108801800c40c0750103400850001c04040c01d00d1001180704600d0b85050080410100700142ca4416a040c1119010001c0783e40000079418600345854180000800440b400200072800d01030341c1d400fa00d04100f0640c0c00b003204400410254044580d540640f24901c4018802c0f5001288120019130384140314412245076035480c40c085480e035803c1550b0070710034007240d03120413a082940070f840940104420700090004001007100908288220144280510005400a428040110044c175400a4030004680b43c43c134140d942c001a030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 852328273 1250 852327023 852327029
    0x8030c0a202205010501050304080f03070e092a040f060c0303140c030103060e0705060f070f020409031e09230f031f0f0b150717120a05090123060a090603050106 71
    0x1e500d00303c0007181c5540300d602a01d02c40c6502580e114a08001c0d0315101c001500000c0002040060400c1240b0190b1504211f4501500489100783c4130380d16480c016090407400c0c1c0c011020681c03010301082101d02403410461085900b1420301400d078454600341240501704440816900c4150300f014000790f402c031000110304907400781c0e10421110400b02030380c0c1d89032031191003610341c409024041000241541c1e4010301403a0700c59200c4102c1e0455680c08141600c442e000154081041c031500c40a800403107128000c402250752509419882c24071411101d80c40601024009001d2603081045c00d54841c003c030000c0f5854000c084441100034400c2c5c0c40050389810712000290390600b45c3c820346161407402004c074559070041245601091888016205406ca800c0640d408501607100000c152031600c01032070000d5001d07140207601d10740403014805550b030290030003110340c2c500000c4e40c050b4401d50138082d4201d450840c1015240d00c0d510000313810b07900e8540150700814131b044000020048154005411 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 852329523 1250 852328273 852328339
    0xb070e0603250c1a061302071a060f13020405010f18031212020c010603030f030c20011d0d03140f071d0301020d0b030607080606070b0621010b010908030c0a20 70
    0x492001b0503c40410380c0180c82005141040d59a464400480900f141c150700c1103018140042c1e802d900c10026034450040c03060000a0b82e400581840296071080000c0c42501003803c0c030b1800010f07900c000310556501d900c00589101c0d41503100e5079240d445080500031205424a00b07644524080c140305008101600c0120081001c905503104040c1c02401540450141521502010070485800460340c085001c07048506540e00c1e41603a180700c0e0746000c2c0d041c9260485009021403000140701030202c0302030382e1402a00d24890fa0030401c0c0054640d4000740d02c04079602c1c00c0300f0301c0f202510707050909180b180074042d45940085220100741c0c110398001101190200d04464440c0c4603040c0c140d41c0300c207042e10901d4001e1820003480c404681000200c94010f0400741c4440010b40c1850007410700f2051001213048181d4480c0c022003460360307120181c00050044e0070083c0d03182903000307100990b8a403150304004140711814000c1c00410403041240ea0711409002d844082d5100700300360b080025825800400d41c0e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 852330773 1250 852329523 852329539
    0x5070303032a0e0120030d11041a041d010302100507030e04110c01060905060109061d0303070c091401050319020a080f030a090f0501140f160b070e0603250c1a06 71
    0x17039000000750907002918580d101a514010107500c1e00c0e00642040d8a005000c0601040002038030a580c0048c465118200c0400700e4171f07103081c60301c0045414040c20720401c14141000050002d80d840c8009421008914149240d0361111031500b0b0710305020400d08260302901e0300c030511a13400c81c00802400b003101c2c1705008104075a1180b000360f0031200180e41650000d02a0b80d01070201500841a010310a550707244d02c9030502c400403000a146a0101c0c10407a4040c2d44e0500c00c00001206000320f44402150680010780c1c1d42c14400441d60703848040440b0442d2510179606807096484282c40300c070113400d03090103481002004107181030344d030380c031040c000c3c400140060300024000414481d03002c16210305941e00150307280b00b60360000301030b0820072005043d000e003003042c40c02c404612011180020300c9810110428980700308042c24459013184800d000e80402c100704580380c540b00d2407403031144e141942a41e040c0864550101c86940748260018038286120015101d000b4040c1c402900c1a001210814 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 852332023 1250 852330773 852330797
    0x2205010b0112021303021c240b10140f0f0d0504050f0f0705060a140706061a0901080103060207032c041d0a0b0601050d0f0e0d08010305070303032a0e01 67
    0x300d110301d05480d1000340040c0001d100520380b60052141c202009924a100c0c01d5403074030388603034200c014071110323151903090800c100410020740070702013080100320b81d2445d0306e0015160181c00502c00c0c440c0d10150980c00107200c820960400c0540d070300c100c0d01c1100c05031150b011f10b10080003010141d609903014410706081603000080003610703048807107120000c0c0c90500c2c5443c040c071030305070010750b00d450909c50390801c254440d6180f03001800b03059001e60f00204049150000c103411141059603803d081d1b4038204004207899800c6104d250459911040060360b6103942d040407500180750244c01c000b07a0450415004160354a01d0745640c5400080320100f040c5070450124090781c20700f11030350280c6600003992050201d140c601c01c086c3c1c410010305003249000c80400c1708000301d503400018400b80e07650300e42c0c0d0315078030140c10401c00c203940105040054465041d030712410303594070303840c440101050b0b2100002d44d8189000303241c00d004d0041d1a0450303000300c01100c80180c5800f074104c0415000401ca40d41c00c0b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 852333273 1250 852332023 852332057
    0x409020d0605040603020102210927010603020f0f16020607080712030216110d020603010f0819110d0812040c0509060d120c050304051504050907110709052205010b01 73
    0x820105c0354140c000b0059084c81c40820000745002e44200c052804051003a02d1294480b2034803002c4416291141c20104460ba034400e41e4406410303001841014414041c101d1806040c408540400300d420a19580f0303180070204c0012142051180250800f2001c900041000044005811743c28880e141180700c010a004040f0100c1c025000310351036040c0e018000c04082941100c44031607207034010704819065070941d004104203501c01c0c4d101c0031100e00c03013403420098a64184034150158000035101200c2080319101c00368601d0b401c40314288103403d807404c10410450882e00300e03100902404006006480c10b8104040c0b110940c0c8100750080440c07000240d503900d40741c540d4840496000038405480707401c0740012128004c20250448042c401004003041c1036580b0005492251141a0401d0365581044d06010800c0350280c410420b1200184070b80400b07000125084050f1005020005600d52714040c035064111b503084c16891001101407442000d02006400c0a520f004085e2100c203d160080800d07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 852334523 1250 852333273 852333281
    0x3070510050408090d05100519200901051308060c04031401090c1701060314070503010b240f07020d1203060b0f03040b09010b03070909030f0809060f0606040b0409020d060504 77
    0x402000c0b024200a4850700389032031104400d4040c00741b13048600c0700c4191040a401c40d2000d4031442d02441b40724003d810070106502840401d03141c00300210040200340b00c0d055600380102c101403410b00c4004030380d914440c26003568920042000c00101c500504080245500be54400c1c0425680d0326669019981e595805002c1c0104450b803000aa041e41c500d001340507545150b0a02e0099007a54031008004081200c41c130510304801d07824030190502c1c0303107841e00b05421140d19201c503e002e905101000a9608034120400f048200840c40340340d62407644074503c038511b00c03c0c900000d611098545e240c0c0300f408441c900c40364040c821618100110703915042020110700800c00c42c07503a990130404c00a00040c00c02c2d12400c0d007100c810400480e19907003200c000703410001c0a801c903001e11a6a104881c040c15441141c0200341d0401d800d00c2046402c00302c5c0c0700c40d224140100421243e04420000c2102c58458504560082004000d2251255200c45124000e0761002034080c03419818850003089900d0f003482 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 852335773 1250 852334523 852334531
    0x903030201050f06060a0f020f030d05150906010c03120b1503150a0f05010c061d2a09060d02150d1d1605151c02070605070c031407050715020307051005 67
    0x60300d401d01a0182c0200c8030071111f24030f04411030054a1707446401040810141040881808020415190141144810305c09a0f81d986101e008a2010302601da60000036030b022140d00762502c0c10183e4402c01c0d8140c00303490032800003908190007034020400040400051030140001c2034600da034400c0b05004104030601180200302008000c0401000250f0103240c06140040c031510003c1428100715481c00c0d074202282a08104a4210100c854515128001c012401c00303a040c2031515440032000c082107a42000900c8c06000d03c00d0001d1075025036444082e0300c005068544995030392004003800b580e014000c0d83c3c003544101c1401150840a240011801502d07130092904100441031501007081101210aa00301441c0a810458580310701c0343c41c101c01840c074607e45005a500c2041d441e290701103d10003081c2400f00900795101d100040e0b0f00c44254130145151554051f241c46050424505054056128440c5000c0030304044c41c240d9000700c0501030642c001d105541c1410390940b0f1890507940202c07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 852337023 1250 852335773 852335779
    0x30403032705060d2316260a0509100515120604051507140d021c14150301020d0e0601170706020c0405070e0d030c02092d070c050a030903030201050f06 67
    0x44240d0510b481194000c035802c0f424465003400307452032140d90140456041d650210a00c070414007020300d044d0087d5410110f1154481d8020030714100320f140c60f81d42d590140240c2d003c26107644c0030070240001040075541458140c8410041400c1022481124048291140c0e002d040c404d006111180004603010348903c4e008805400c1008080c1b10006204800900c0c000070301c440d03c4030035404000360b0f101400c0310700d046440050781c404c2000d230700030440c58241c1940f15055091426001d4080714410f40d42d500f004000020000c40f2150b500003034064058030002c402c80f0b51810307010090198001805504845031010760102e06600e0f80e100b107482c3e1006000d13070740c05039118604046490405901140d4800598980008240040340010704110b00249064000484442d0340e40194a42030a00070b410400f1000060b1a02502030040e184d83c82c20449031158400780d10700015580d82c0946480400c45070301400340d5001c40b0903494080c0042045002c15401580b17032000140002250402c0e65008241c01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 852338129 1106 852337023 852337027
    0x80604082203080a360312051201140d0c140102070501020d12090c3803060f13060315020a14030402220e03040303270506 54
    0x3034201d4500c62090500802c00510250200d8a41ea40a0b0401e0322a100d41040380000103140e00c000b445140302e12000310080c410503518040705076885150300002c03407031900c001120341d4041e5105e14418000c65400601000584180745100160300600c2c02e280d851040c0e44002e11102c0560000940b1040c012920f021580c0500181c1c001d05001e1000700410003c282005022081c0c6c0d038805030029603550021400e0041602c4100c1c0900040000b016034030f400110240301c01c24030b10402903580422214403603105540517003141e01540005124583c0441d0b41c0041100c2003042c2c4501016255444000100050f01c581c003402903003a84020042c7c403660100d502501c0e01c54000354401e03003c5002c204100041e55420382101c52183e0f504130312b40c640810312880d41300400c4841a910810701c40440c000040540c841c180040c24001da03081c400300c1a2003201c03501a0301d150343c02459800001 = true := by decide +kernel

theorem cover : BRFrame.Cov 852158273 852338129 := by
  have h0 := BRFrame.cov_init 852158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 852158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 852158273 ≤ n) (h2 : n < 852338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
