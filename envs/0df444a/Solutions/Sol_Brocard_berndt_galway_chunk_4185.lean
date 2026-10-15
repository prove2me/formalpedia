-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4185
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:48:44.61389+00:00
-- url     : https://prove2.me/submissions/4b1ef610-8cb3-4795-9cfa-148334690f9b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 752517985 ≤ n < 752697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 752519235 1250 752517985 752517989
    0x11a01021203060103020a050f03070302180306100302093304140c0306010c020612071d04060b0f0a0201060305061806010510051e300a0203070504060807201501 71
    0x40d90700c6895040314440701081a6036002c0b209080043c0c4408042034140c03810300c600c0c031310340702040000010030641a0705075024001c004004a1703900d90b45c004181c14180d0350b007015900000d1080851000700014175051200ca40e00003000380301c8459201910100d072444c035a00e84200c09052035118042e5565050500c40d50346c1d900c80326031101900d4208030707210300380310710001c1c2c5828100240080440255110401211030105162840e00001d2034500001840d4903451540e199440a85281d135860b00e00e040c0c0038030800e440405420a00d40004070179030580726804105444155501c4900010100750240000c1d44550f00b100b2410700c90704000382030f40d41403210580259114254080d00f50b0a680c1c0c0c49010785100c0700441c2c01c1300510001c0e1043c0024203006e0701d805251014024200c1c911182e000029442c0300307007030580e6901090f85035103000e0703c140e0000b100c5100015100340820411644600c265a40290701e41c14605481406c0d031114009680c41072095124991115203504448072841c9034841c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 752520485 1250 752519235 752519237
    0x2041214011422561e0f180a030e090709080712030306090b0609060703050d0c030504030e010c020307090222080a0c0b04033908011a01 60
    0x4044030401c00002d201031806803c007507a40c000b80c51154a6100d00c6441150066000b14a19802101036034448264061455145849110340c407100a041c2070b00102081101c1c036071808042d0540c51840601c4d49203400240001d030300b1180200c00481390346981c808603020304807100c0f0284c1c0600d040c49030740703140106a81108442c0d9004003101d1001c00c2d400080c0d6850400c0441d180540b40e1100901110014210303041520716002d1041d002807410f50440c90411070303510988090000650b5020310b00201c2e1600c0a801c0d40010003002003044c42d140c92001840c0b014071034189a0708052008210100301c44031300120b42d0110740d0710300a100c185a004011541c5880007480c000d2010318450740829142d010380d00c903440c1c00a8001c5160758601c00e080d6540c01e00031025842c42c521103680c0d0019541c0d00c0b1600002a0340d1400325150103d42250000200d5041e29084004080301c402c0d8001d050410850348c4052448a10169000c1682c0e50b4036070400d200284240000499480d50418041c2848210a01c010b4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 752521735 1250 752520485 752520491
    0x40b010306212001050714010e011103011a090f01140c060c0904060803090f1306052716090e06010c1a04050c0d1515030c0603020a1e0806130f0204121401 68
    0x58010b17a408402c441010781c0c0140881d400413800c80d401030161488440e181c0b01542044c4419203403480c200c0c06141221009001031140002c540b0035400944543c405403500301c003103072907072040b80c2d4021344c1d00411018075942c0842c50140d4030101541000815604c0041c1d00d00c0010380c2a88600d410b00031100034007480b80284d8070300301400001452481d00480207d00600e0000f00c41444001d0300d6028800400000e02a555000a070404050102c0c0140241441c81c01d031000118450f070343c13111140f660004060b00e402184c14100281c1c031948040061904d410070020101c49000203103400ca10000c003500b130a85254480c1018074007a820701007000380950003510340f02c0c504400314070100d18044080610305000540d502400c281450411002e400c00340602101d480002103455055001349460201c580d50000001e4801250b181c0f17821003113400300700184080c404500705150135004070065603020380c00000c80900301565001643c00a900c40380300d02c10060342680511070017443d80c050b54003440b0020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 752522985 1250 752521735 752521793
    0xc27031002040b090103050c09120622050316170f0d0506012a081603020307120203040f1707051903020301052a030a091b140d08030105040b01030621 66
    0x3e1954020a482a410943c4810104865045110480344078140281143d03600d501514110b5070f48070000e071031400c45216070000e03004400030a003810a160743e50040c051468014034544000d95142c4804080d140340700100c4030180c0401d0100000c04c2603419040c400f030b80b140b8200b800103044410007440d06052198184000164021081318224401054a501445802e0604094900f401466001c3c640c0800c610744000616400102401401d40314040040120000f0740040f80c8070b014a1189030501074031440c0a2049070442d02a840148c18441d0483d0100c940e9100069121059600c110b08070a44101d414070540c202030089980c407079000003549051440381700c1a040700785e400856813290fa81010020400e1103069803c882d0300b40750883c0806400ca00b0030f0b469442210703954482d982050300301103003038201d41c1807010110001c2c64100c074400b42141c0c41d100c18080a004158170450415540300000315100c807840b001111000401100d910104940c0d15001c10000401810080c01c90000c981c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 752524235 1250 752522985 752522999
    0x160b040201270b0c0f010504080301051002070b090d11030a031809150b070305130e01052d010e0f0604090209010318150f020c010504060b1e01020c090c2703100204 72
    0xb40904940c2003103900e0390341c0d018541d40e150130418043d101010355420300c018002800030800184d4180d032000c84204107045050360081c0d13524640c510903c9007240091096028a1620348180b0480c94014944002c01000800000741045420b6100b2400315168400c4007441c000540c80341ca01030804c005041100781c4640da80c400c0384000e18403680408080000d081c9041521860989014a109203a0071840c0ca03150f042d003603241442401914098a0505490568007018076515604048201e01410100759424011120030002c00b026a03045400345511001588030f550045c0002c0000c218016190a1650001015240340805101403010b441102001161000c9016819007846940c0003070170036180c0020314068001e04c1c0b40d0600315482d14080005000f295080b0389044641140c645400c004c0194418200e9540301d404076005034801c2c1c000c02d02c00e0403c000c20a0b0448240d168840c10181c03000c0000f081d060074034400500015103031006607941c0c00c0402100450850204040d8142800c140c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 752525485 1250 752524235 752524307
    0x6040902030a0f1704060504031b0b09090a230105040b09091e1606180e43020d020609060118090c080105011d0c032a160b040201 57
    0x10040c203030100940f803c2c400c000400071040c0207580f403111030355200c0b80e480001402c250800e00c01520000c1840c26440ca03080c80304100c2c1016a6070b01001582001904000d0200e0318030018105107110365103908407103603121207414120401d440b80242022035070520061009803500c21410038007501000e428070046080c0840d83c0009100505250715032204111340551a001c85005e016200c458003560106480d43c0c00581000b40310081302e0012102503641d03421499852084500c800b121003080000c404900c200803500c141d0030400e10700c0c01c8800500e4401c07062201c8240c010076016034403001d4000f198503014010705900040c540b010703002541c900401940148410310351001c409030341c2d03d900010803258110203406000c000000704040d60b103c030f600c007410b0110034103607041113039140303000501e8030030404100d80c410401000000314404030b60120b0003007032000380c9200d5082001480302c0440071a1141040d443c1c54060880b000c0d55050074000500189404501321407055030341a1844501d542204c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 752526735 1250 752525485 752525503
    0x8010608120a1403040804031b0303020c0d030c0b010803091e0a05040c020a05060a1d0111160c0b031303030c080f0106051e03010909020a21060b0f1002060f0604090203 74
    0x7050280d61489080c1c422100e582081c450f41e0110b52001c07041c041840800f0f0f0180c000d0ba840340fa07914030392582004540d03440408900c0001e00690100c070510010b800c00008200125119041c442420b9039507a0301c0700300d034034030036004001d6035030010903884003034500100300c0c41071403400403400581c040403a03000c52920303c1540945405903489030344240140d4400c00c100386205822005448c110b040402030500900002400e10000da07924940b04807c00c0710600c150301c5001c0c01e480910f0700d01941020b400300c42c003041c41400e4a40c0402c1a200103480361f91000150320580320070b1003401700702400f8074010b41210304241d490420400720b10100401d810100e040078ec156401317418031980f29006555015a840c0f080c046141c0c0c50f0501200000d580c0d041600038140c3e0510854159810707544880c03400901d110001e00c440c05400e0403628800c0031600c15841150b200700e000c2d101074424600b02003c103d122042100301001640510300f04003440312021041504a0001c45081c44400780c1c0e43c0011341d48154032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 752527985 1250 752526735 752526763
    0x15050a08030c0120250b150108011406031b0c07030c0303170c16060b0a120213020c0601120f0204090809011d010e0105030a0b031906050703151206060306061e08010608 74
    0x30303220750108903c0a00f070703051800d64006d81d00c00c180d190449100600c442110100d0380851b00e000c001142c0c682115000d94012180a025903042d59030300148a0381e5444076107603610746402c0800c500760a0410500140c4069406000d01003410b45c40c1d440e00500c08059082d4500c00c11403a03030203202201e0303105401c803005001d00807181d00c920343d000d0800d407008010585206502000b907003400103648500d0140540c5060080321107202d203075005110300b4207070301c00d40c108079003682c1125006100600364408419419070280c3c80c400c021140d2540031804039421344206480c2da01d008211b016103581e00c5030708284aa110541c021240360b9210300040c1c0000704094409050000c088001820841d10764403569220200900b1038420f81c807060801030030984001c900342c540c1402c082c00112000d021340984124031503035445003c0c40780e1808590a403e03401c18202292007580742c46000001c204203000d12400342c003000c00314100340c10005036040882801d903488540b080e41044030400c5080c8012801e20700210f68 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 752529235 1250 752527985 752528017
    0x70614040e091f0f0516020a1e0c03060509010516090b1809010b120f04050a0206090103020d050106080a060e060901050103240312110a110415050a08030c0120 70
    0xc078108242800d600d02c50322001d0080c1c0305075218500100b50021031044d00196404c00081d1140b02c100c41181d00218001000343e03200080a00024070114161441d20821407144035181d000d80d510907840031050f520a650043c0c40320306001c1c500100b0702c00d07580c12150100c501c616002001c9004ac002c5104d611503050500c0000c160f8007510350651281e01c1401000500c81480703581c46442a50082d00700e0050386001e00c00b0303a40003900b40c40d00950450300941d000303402000140102c1d403c005141e4004624541015000c0c003403440e01007030328002c06001e040140c652242034540715601c02c040b540182c2c804809c5510307400138045aa210f100b00c4034107690b03082ca0042150040c04000081d24441c1d005c00038090b01484000005100c031500e00d07402e010380d10b5503884e0006401168296a00c4844d00c001074081c0c0b0007525220303490f00e4140e11138145c01c107140103000c000760750368000201808100d41c090682e40d0800610410800802e100c0c1c000c4000c4c045160f4a90982ca10720440a14055000001d28402c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 752530485 1250 752529235 752529241
    0xa060e09070b220f090b062b0207020603180d030903050d0506010903080d091a0f16020106092f030f0412031b1101140114012003030117070614040e 65
    0x10f4070594445801007160740e451030481d55904280c0b42c4490340d1080360f03100f0b458901918034502d088402c0f0703140c80f03c0340307044a0781e902c07556400000d41c0c2503e18800e490311942000380400680307840d030103140f20714224401c00b40950341c8001c0c500e040417070300ca00b0a0201460500c080300081d420034241c0c1c07005c1311100030008455890000588103040c80c2d4102801000303011031950400d0026030800246544a5100c400d810460b07500380100c8840c0130f030340f40090550392500040c02c1505914000c20f0b000704901c00400c072a41d50381e560700c044a0345003c070f1448074422070349580050060310907200d4000e080002c48915514090201d140c0d07415000d40300401031030301d10981d520356911030b410280290480c03420302d2107500901c0d01d01409083d1881c0081d00385e9420b05269060000704110001e04903061503100080c1004050b0044952040c01d0b040f4411000010f007015200e2101000914003810301804104160210341c9041480d065050f8040c0302080f500c3e6040300c124100c1d58003074408850700c10640740d42a407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 752531735 1250 752530485 752530507
    0x80d0b04182d12020c040606050f07020f040203090304030b0c04060e01080c070b010b030105180405030405061303080a0c1a010302030d050c03120709050406080a080f071e0305030a060e09070b 84
    0x400800c042250b000041030981040c82440710180e151107026408550514918005020603201c40d44a840003260050040003014903503c4000c2010342d100502154051020000280c201c2e04140c0c2d104640e40c0c004501030040082c1180c4040c0c002d031040c20803504052600500034544001540c140d410405080007040b031b154101419562442d501007064680c960715580c2c452010b030401d1052901c40c02e010500300e01a600070b003c046000d581c2000c090b5281909100070b0240541c8100070380040440d546000101103400f601c0a0814004603030380d02542410309041086102070015007107806441c0d440010070041c0e030001003000c0e034101a4100310391500c035404515400e5005101c100306944021108210202d070f8003d6607541038800440e0108200c4e521560200d940b2001c40c0c5004103883d07020030450345400403d1000d40700c10b91080e80c1000c0103415580da5440b00882400045000c2000842807001414282c0901c41c040d1030041345c1031842d40b408490040e982c030640d10510000200c0000c0c88425a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 752532985 1250 752531735 752531783
    0x3060103060b1305010621020a021e0a02060c0d0e06180d0201170f042d0609060608070f1508064204030b010f18020d060909080d0b0418 60
    0x1043c00040100920f6966400140c000701d0b640704520000b012172174400022550a00c01d88150140c0e550061280e0030003c1a17100c213090040700340b003540744035054000d0011390310480205000420800940480c2c009560041c01703401e265040b051084009120400070382404181c003040400c130850b00c01001d030b081e600042e14408803400b42e90b5460103040e02000480d400c08082c890281e4461314202500354050390540507a10a944c00d46541110802036240119000d45c010740030180c012140080c01d1550f60305940c1c80c04200d588031100c40100d80608024010a41c0a016210382a034107120b07200d031420100258000e0140f01c0e0100c003001014a0280c00380410360a8091a004611300c1100c11942c42d440d015440c1d0400e10080f81d1822160002084c40540110b0500c2261200c0948804459050022402a411001c0110621940d448001076803041c94092401400c1c01000000c1d520481e20103040140d42c0c1898038170380241e00f040b07030f001044035031a442809041d4200039108890b4090f80b041d6226 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 752534235 1250 752532985 752533009
    0x806090712122c0108060a0503120f0415020601030c0501090311041a060f1b0705090f090f01151d06060306040228090e091519020721140903060103060b 67
    0x94480b09114280202c920007240e66031098244c940c003400380e94040410010b02c407c0c3c001c458040d00a02c450011080e040d0001c0e00c11404100344090402d0b4075272105000b140c00c070704000301c01a481035004105201070645484040c00d400c0c60141c88030380c15500c801d603518004480490283c1c0c3d50b03000c0c034204802c4182c0443c07540c4600400c1255603401e01143c10580360028081c07080f00220285450076081400104941100c01c00761248004c1d56802c2d400181d0748100810300780b102e006488401b00c14901c20301c40ea00002100d211011034050400c00e841494250102c0c00c000c074280d1385d20030702c40c060b555541900d50000c070488015039070b18240c281c2c1100300d1800615000300003a29041400400d0340006400040c2c0c2e419010b0262030756100100c00c1d9640440c004c01108414074107010900880094948005844003c0703005450400a903540808410009910310616084403d04403089580700c14002d003000380d018040c0c2d0070082840300081d21440188001400c140da00d4806d441d80752166150182 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 752535485 1250 752534235 752534267
    0x8040f0c0b090109170c01081e091005160206010b0c1504150b0d110621070915030c021002070f080d0f0506012f1603050106080609071212 61
    0xe5561404504038540000b034181c1c1c0400c03200c2c9004100140c840c00c400c0c4144240d41c2c01030081e000340c1c500542e02c914024000402000f0344070050410380c48000c102500450b01807004100b904180241c00040716800307003a207018000c01240c40210142c2c002003a40c10354480e1000240d40c0c119009600785800c120754114034680005204100c10300410f02d40c02c0034000061041440801c0c5150100400c465002c90020300704203000d070003188281402d002030306121011003940881c1c0d098001c0184100d420440d80000050941c1805200703403c2122800c00f60603486040510101d425000040c0d2070390b10801901100720fa000c81c1c500c0502c81d2a03814485001d0300107410759500c0e0030fa5402030003d03050308039110428500348400304185510458032401c109241c0004240031042c0041c5c00400040c00440001851203049403207007080b00c41d5820a001140700d00700001d205840d11410600300503000b00518819044020b04201d052101d400c4070a07120750001051010340300e02c40041c0d58100000036001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 752536735 1250 752535485 752535503
    0x31a06030304090c0818120304060b04021c0902041d0d05030a0209190602071508161205180c0307030203030f03072607080609060a060c020d06050403271508040f 71
    0x40000d68005c00e40301d001d58901c1481440c800c1c3c0c044286580c8100c60f0b01410124081040004c010401d81c1e8054424950014400f602d0321095021410420103480e200c006001c3e543c0c141101117240070320590b120f1120b8002040c10b1b0444010030340d43c071880303501d5144060050010001e80403240d168111455028000c2c80c1400d44590400081002081401040050b1080d984046481c92100f0b01c1c1c0180207800390741d941899521347d038210019826920b2410300348011a011521204201c0c02854032070700c00e03c0b0b01100c1140c0340110303207071038200313190500c0703000344c000500600c0561030110454803130a905030300c00d56490310b40200445114040c0142c019000a00301e14040004208a002600416542d0348031107041d140c901c10000e41e4030041d60741a034803400c080020080c0030301611091103401e0006140d14032485140e04e480080c0c0e0303005c031812000903400d45681702140803c0300b02c0c030038034141e0307034a150f0903240c10900a00f22003100501c4500600402e2000a810441d00f40715440708158402000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 752537985 1250 752536735 752536751
    0x81302011107170609120702101806030b0a0b21130f08030a060b091318140f06090a0b0a0504150e0105010504050c16080904110f0a1206031a0603030409 67
    0x4080d003da20f242e40d80743c41e0702540f0080f4080002c005000c035040700c407a8104030f140522130fa080041035481d80d000d400c140b020707a01ca12081c10760300b000c200303004100700c0d140410343d080e81c0400c000f0059025000300701082828040d14020310080652203083c0740b01114100d001d900d8030100c0011f4440c241d44020700d0b540101a4080030426a50051070040442490520000d615010110030500510320196000b01d00c04031028440c004a030400e00d0000d62520340f41d4141d000ba6280c0005801c40792070010f280d64002852500d601c00100243e561010000001d003550034000e40da80d00054001600c050902a21503011030240501c41c0281c030a103540035481000241030055166002e42024841d003441149050000343c01000342d030b411030b50031000b5191145411445a540c420035600610282904030390ba6940e00c402e0020008000c00c28241650601c50326400c00300e500a0080c15800d00e0070b00a0340c10003d0170400a2040c4e842600041d00b50b441000c025941e61011900d140075551295201508203480 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 752539235 1250 752537985 752537999
    0x2310210e0c06070f0c090915200a0207080d08010b04330f020607081b031005060703050d0c18030b190203150a1a0a0f0311070b01091b081302011107 65
    0x580015a1103005c1089501d0b039113800b004101c40c885440500340c4400c101c1700100b10485c40d1300141d417208038803960f4403980102c0c505800040d0010440c00001d03910144c410300c1810420030030740e032000159160a0b0a50340c1813044400c0d20380030b248551841e030780440f007a95501102968140603103110780b0301d04001804618500402d05105075a500015005e0700010a40881c4a21019841484441e001c03501403101201c4090b11580300822080b4001355125004c00d4569440300100801c0c7d0280c0c1d61262240d825500a4045030400a90301c0180070500503444103981c0c00d07005c0c440807650800200741d102c4c0e55241088001040301c441705101c0358400070810040c0c0ca010307031a0303d00c01d0000780c5188904540300c400c410030101090801c403103150803d01a10100500c140075641c102519032502094580d600c00e2150b146401c03101d01183c034211400014414070016210341149500b0b0070042207403606c02c1000142603550080c000d1b0110841643c1c030342040d64010303d82d002440d01942d040380c14080da1480 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 752540485 1250 752539235 752539253
    0x50910030e120d0f0e0d0f0e03030a020703030216080d0c0204140a060f09110d090507080607120b0102011e0c05040806010b0301052e0c020a2310210e0c0607 69
    0x1075030402c0c0500c0c1c55600003c0025a11958050082040080a0110b4080c10948607101070801c46801c1003c10301c5d031500d90349c4091003d0000c0c0e07001600280381990031448c0207410700440ea00d01084140703140004201e030741400101d05c0580107050504121000302c500201740501400c1e501040700441d014144515603070590720031404c0700c840100114041d502c0d01e04c1c100030f03240b010000e442c40850520011403004526448000b515110318102c902c0555264002030419a0403500c910120b60f40000b246c0030301415001e02035000000340300030040f202c900e610f80e81c068225000c044501c00d541300356048009004004a40c0900601c108840b681d682d25a0400c0c6a64000d00880d401b42408243c0152020080d103410214980d0b0803084031408002020f0468504d501c0020a0740e0080014200181465118060752010382488a11440700c0d04c2100c10301c44072099001e01281040b0b0061a15581c8118440c45504000980c5602250085000d032030a45080070141030751fa441807001980100b00504c0350 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 752541735 1250 752540485 752540497
    0x2030f031e0711010f0213030212070503100b011803080a180803070506240d060513020604090b01020d09081207050c0303040b04140406050d0803041a010b09130b01050910030e12 78
    0x8002817101d0403c0440c480180e01034080f1100700068103560500040c074000308164540c039160400c40b61525a02c1000034600001050ac40c42c200b6076803003243d01c8035640300d104125809600e11031000151f15542e031741c0c5414804c5a8040b01006120603210480240c07503070701304005042c01d03030890741c440504c1d081480c0c03104c900340c5540741d0082942c98501b110076902440c1c1454071000030b10240c070800d1030791903280c043c0c600200070340e6112252030b50745401a500d04001d040070b46899800003d815128400191034000346030848010b2190140c0c040080c4000007460810307131040c40c14000d44805252820610700f0711402c3c43c559143c0400301700461a0303030040c0098012201d54141c41c0c15402d00c1001401b044480500a107038002070540710120100307404000850700a8420171100d002d01e02c980f030910031080000e81059400301130000b5110214a8020005405040002010028900c000d00047c01c2440740180c103602909100481d103400a00903404400900752105c00e0b5644000340e001c101c0220742c000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 752542985 1250 752541735 752541767
    0x30e1203120105090402030a0b04051f020c061e150d081210090216030518180105030d1107052e0c03120b1027030f0b07080702030f031e07 61
    0x907a000080602d4040034540c01217401801400350420341c2c2c0c464812025004009880500c81c0050b01d40b6001c070000f0780b070040300b0010240188c0310105013900d50300b00f0340090800300712540b41501541d503895440d182190042840c1d40c3c08111400c041e408500102520040a001e0000c00700c2d41080c90340303600108074805c8007000a8040e0b1251200c020608030b0003403100c2c07412003001083d420800a406140103000300d075039910560352081e40e540c0c00600c565004405020381c03ca1100c004000f2030908106000144001d81440795003404100e41c4143c1da010b192044603c2a07580b4000c1c9055029210302e0701c07005c1003440747d800c03000c4211400082d00101c4a4841200060440b070b0300906079540500c500410450010403909040ba242030040720b01d08003185001030b480150301c030308181400e0304000060086118400039408002d9a0614620300d0340001c03c0f4a01f4044d4250400540c258080200e13952010700d500b0840c1c4a40340d04200424040c0c01c4080503110002c0241400085c4d038000603160805049 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 752544235 1250 752542985 752543017
    0xb0a02090901080703030f230d0c0917031801030b03190b0c07110d030e040204030c0e090303090a0f05031306180b0c1b13140a06080622030e1203 64
    0xc3c40041c00e50710000d9210281c0080c800c01d0f00c00a00034410340540c0081442c21030300b56a424400e00f181c040640c049070f034448001d541e8410416031590840f5641006090755044510b030424000e01c006d40300c0c450006403040d20b80e82c4075101c2e400c980c040d60180d958440d014080b9440d030800b032114800b00e1440c41c24165203100408000440c0e0030503070412241c10960050030311224408503401e200642003420011414040500304110040d01e851010b44015800b90707070135410302454000d00c4080b0342c602424001c003a810030400c12130500f0001074180d8003541c0c0314280c290042042d007003280c114094003440c040c00380b44030740c00054002c0d070111b040100b01c204c1410403070005540e031580c0c50441c0b02e1104080700c01c0c0c0209000c2c1e00c4114200b03205000440e4098506024848290022003c58001c00c034503614406142d410320078060403e100c4e036005407070340200602013800e10038405007110540d00c44000745042050780902c1010320804071b41987c1e4801034040e920700070507440c0043e12900314010711195011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 752545485 1250 752544235 752544239
    0xa020c19090516020c1f1b05010e030d06090209060405060a0903061b0201050901052404060e0f180102030c16140a1103010e010b090a09030512090a0309050904020f060306010c0b0a02090901 83
    0x42c00d01c208008424403190341c144001b10280080e0b6500703452899032030710038241c0041007010070801c2c0503070703035550072544061340d44d80d5001c50440040304c1868000501c2d1901c14040340c05152200e00c1281e054130001c0f11100d448620b07440c000c40d045203098100400160400c600314003005064550320b8503001c0b85400900c819510700d5030a50881d4401c40d03188114084100c41c0000c040000341c10005100b001500200b1061f40300c04503e8840401951240040481c030420848000d21036183c4004042c0340700300951071420800100109030142482204e81004d840000740200189401c80c80c800f40104020303204c18031704c1c41c01c4c0150b0f8103843c044007600035424102000c1c5005010311400300c0c050740041ca1035149403900a2801c00428161804130180041081240103000c2954922489000b00000621880300381d464014809003d41d80014041e0140c03600344801682c2d42c41901c0c41c18041965810b40700d6544000403507078044040710141491078040248129020250000d000202040d5182030b82c5e40d03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 752546735 1250 752545485 752545489
    0x706110405042d05060622170303070f080c070204150f140604090e16120210080919020a0906090204080c01050421050c09010b03040303110a020c19090516020c 70
    0x2480c0c4900e5140e01e41c0b07910000c0d916511a88199009000a45514201305c1e540300c100e0012186508001f1524000440070042e5020281c051150742d144900a141541044030015206140e000440d60030312403580006522a442501502c2800740c008005000e51200048040149561401102c2441d07003400c1c40800c0c60381150900911a600151002d45040c1c0b40c246601c000301108409400c0c940900b115805400c401445c017803000d489603400c48541c84642d0b01c10044441c01c11400042030294140c20401000700204035000091200342c1074802039500d40c80001d091165540003015a141340c03004c0404c104142d070b8050007c0d00ca00004540305044076500640e032178080e13885080d80c407510361161030311b851a4a00c00151281e10480c00c40b0001055200087c1d000d110907085004844004404c00080c136038980101d14a23906000201403400c1c41a0000a48070000610414041c043d03001ca0000d07800040341c03211000b0040090100b0050800d0990b896280210b21655030062240341c0c14458a4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 752547985 1250 752546735 752546771
    0x1707020315091924020a050a0e0f30010605150c011508011a090408030712060305030d0c0305060a050f0d0305090901080a020111151314060403030c02010e16140303070611040504 78
    0x407041a440301030400711500001c9880609c40131290b500140002901440c50b00c6200ca800c0c106c2070490b5501e0300f2411030f01302c0b04500d800304580101880e0305018007007146440300718000d140248040305540d5030748000880745014100c20f4113001e0700d000e003088001980341e9041d03010300034094402c442000401c0d9000d040000c2c10a09960142c85484100081603181d4000c240c200c06091511078041207180d502d840c1c0358107641081043c0750b9100d4a681002c5022039151007415800501125400c912500b0000411007500000304401d0091048000b44402e0502400035104140f500a01012507076840704005901e90b03032200b1041740894a4036650050101001c43e14003002c0b00c080d07154542650319004017140c100411182581c0840c500c00d108180c1d14014000c440c0300b42c4c0a5100462540da91302d074002c0c2100d9000c0c0880115420058442c22501020381d913000450355800c210010034005200041c3c2948610303400204030501d02071a040742d200384040a0310031900102d404200e6200e60400152311 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 752549235 1250 752547985 752547997
    0x90c150408061618030302031305030a110105031801051e0f01211e0c0f0b0403020102031c0b0a06020d020d03020304030e13020412060207170702031509192402 70
    0x1503508104000340180003d4403400811803120314141041c0100c800b40e40c1c03c81c10554000b60700580002420814104101d00050028142a070042c03c0e0328507161070b0000607290954100b410000e0020110f48074141401c4a00c240c161120001c00141c00c0243c00303603d41300301605515645009110000c0c2e01c0e038820349103003412958625807007111415030f920788080303e410300d1104071410900072a010103112001080e4810742c500ca8800c000303004e42800c05e80b07429090307035600841c20381c0400c200501c0180d9000c0300355010314003000601607001506c51220005841c181d01d0a507044915a4000140b043d40050285142140c980940d880403491910440580c07000b00c0303018010a02c0d00c0036007889810301d0f007445101160102c070010b050540b1141e41c44401c41c00c100742a2281a00800e1000038058244409145501c02460a40c500062540803d8541b00512110801c00f09145e001600c1044184102c04842a84901c2171500c454907203040c0c404007030341c005110500d80c4885102600d1349914400c0744e003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 752550485 1250 752549235 752549249
    0x4021201060507080d051503010e0303150603090c04020c100b0a06090302060706271a01030b1609031704060e032a0f03120c2401050409020414090c1504 67
    0x140903030070408169541d9215103c2213034461400c000940050001d403007114001c200c2241000c06074001001010b00f5500700b9004146603410800500c10508000315601c48038182c01d8071015100c5d03035182d10540c00d00c1d0591300c80c030f900300b4000030310301d841004c022900c06a0b0b41d03603250003040720081e64810b00100384d40c03d001d144080b5903806814005440c04d88050801d4912540001c40d0200e40d940c003010216103081c2c064503020128002140c1082000c2c0341c08400600005280c1640351300d19140c9001c0c40c4800f400b60200c0d48051510516010711541e0030002440d0051034410280d884044080640c0d03100c0c0c4101c00002c0c2c40e01d003002102389000b054405414010389881f11504440504a89035500128000c0764070400600303407601c4a890a0040a00c05203400c0c10301911880401419400e0480a4820400300a19002c4003c2007600e6050a00d040d00c80541303001640010300e10201c2e00a20403401030010100c0c40e101004000400040d2220826030140c031004080018421882d09038003550083da0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 752551735 1250 752550485 752550517
    0x21e1305040305161115190815211f0c030e06150d170403060e03040f060f0504050d0f050127021c020a0f1e0815040611040e01050f0402 60
    0x10003044541300c01c01e50145d0003000d4040e900790512001403d4015601e5801040c0f0402146031130760750700740400d40541d642003800d00c5081ca00d0f01c450b589062000c4941442c1c420004101c1c544980fa0003500d10b12410240c40c42200c10007650340120004102d240c45210941d94203050076581072910a01500e00d035402003a0040c13405da05d0720308112507154240c008141c0c210a60702c1d90200407a800d01c6480302006c5041804994407410350800070183e40c00c10314045c68940c81040104100c1844000d10400c6445520301000c0120350a08225054030640d809254402d11101c0c448082c4030a10200c10304440c03040008001c10310504032a1079403002c02d1078407031081c181041c100b00c015051020801500108000d0000c1807030384542e000468004664100e1060500715490a2000405001d60401204901414034034440d2915406581c1d94040f84a484031108a4101007800c000240d0010fa404040c5040e03040d40b29515420b605402190905c143c610412100c58040200e0400d807007280ea041034019005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 752552985 1250 752551735 752551747
    0x120904110a080a091514100609050a092004090b0f030705060d0f02042c060d08040627140103050f0603030306060714100b0108060102150a1107021e1305040305 70
    0x20340002c040c1c4940603124012448000710b69005c0500c125050082d40c2c407100b1800d41840e0040e403810000a40000b03050000c0c40c00c0512241d0744500c40e06044405003000481c8020b0b040d240032000007124100500c8964010a011034541c50300d41001500c0d401c1030740c441d0000006c1c41c003016542d1896105403034001a04202c2d07051100d84580050000302c401000c0580307420342e2070500c0c2400e02038440c1c0c464150b41c903030100941c80f44c41d1041e5540c0c00100458520500b1070454960034840d104511511050100424645c0b282c100b103002e2441c1020400304e90440d8450f62891101030480c441c072540c0780007910305000100b00ca101100902e00030f982c042c0c025825507980701d0501c80da40d4003110090314110700342401c1c190a183c003000221811100d021004c614903091301c0001d04081406403c0350b0554008403003406007075900e50381d1640e002c60080c0c40800e100000d034901001d6032095071000f1350400b0010a040c10a00c07c86145104205000d0304c011900300c03182d03400c031000c40b481641c2c0100050303c10400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 752554235 1250 752552985 752553001
    0xc070f150f050c1b0a0203150610020102092115010306050703150b07030c0812090a021512040605130f11030601230d171314060c0703080a11120904110a08 68
    0x400502d81c4007503000c817940c1200f6900001d02c1d2002014038529900f0005003000300c07900304184480241c4a00e80000d5003070024a45c0040c101c08003150214091a0004031414012081000941c2a074454a0100501540c6909010014000443d40b8502190800340c040c0481000e240c881c1e011a02c02400132401e000f1260b1301214241c00d44101926020404e121074050310000c114007038040c1c0c0844e03004020960300c51040c000c01c04042d140354546890140110741007000440001d0f54004e42c81000040e050b40d4031f030388524072449204409040010610000787c00c200b4110280d2160300c504608540391aa81c0f5404210300d001a10a544007008141008500c83c5c1403541e000d41526101d90082104607000c00e4020445810506d0a841c1c0c0c40d40d0a0000c00c0b00003214151942041d406481480c0340000038003c19988121500c0010020440043c240301024401d80b40302d119401904141c49505114804004042d005091924401c51402c10701d010441e4644080701c101c0400c80c2c0f240340d107603590a03072 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 752555485 1250 752554235 752554267
    0x18060f08061e0604080318010c020112050702030f1c0506090105100305090102072406090b0307050f0409051e0f010c080f040f060219090909080708030c070f150f050c 73
    0x70042c00e85042d880b07124041580c81d14003500103884007000039070301c0360480114070381c000802c06201c905200600900c100907036401120000343c41419000810b0b9519007010480c80c2d0311a450031000300c107501144500c02c64400b0f10000c1d498004e100c0040c012030f141c50f820003440540a1142c03076400352040c00c0766100b41d8002e8107d658000380200005050002545400240100407100741c0801c4551101005101c0460f100b003c01030008404100311500c1c0307800202c0d03510600390045030300c01d10030103040002e5aa02c40c1c101c402c0d031943c44406c4d100350f8001c8504d14000c407911118442440e004054a0b00c0c8500014400c1d82d0302c0b01401c3e500c1c9034081d01c1d00c61040360b030008081e0040c0c1d020101c08404802080a500003000c0c1050300428440d40c6071440311004118414940100c00c8a9043c508820045006601618032042d0040f5010f690703074030781562038022403064010060030342554990507410f004a020000c90300700424903050010301c58400c1c44100726502141c0740c000a050a001c05000c020501d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 752556735 1250 752555485 752555509
    0x509220302070f03060e0f011b0c060f060b07031e231e03010618030c0504050c04080109060b04050612150a090515060a06020a0812130f0318060f0806 66
    0x1c010780e040c0350b0301c8190403a01d60200e608242c0c0c04540702c116551300540100000382e81c0c540250000c0000043c2d06424107110000010315108029641421b1814045c4991182c1c95404140004000081d030310030300701c001c9800008064012822500108202602110200307509115607680c2c0c1840d100903544001d066000c150700b40c0c90003081071004140c00c085400302e4200d10451012903503260b40c580b02c4020091140007c12080300d0b03095500410000f11140c2c0d0450603114115000b003540d03907451901004500456009050b25828407224030240019603224511080003074505001a41d200b00a10100000307441c1c112119901c00d10120216244d481445500800c001c00085070fa1706480d2515860411465640422003801c00c040c49110302c1c180c00104000d0502c1e002601200000381c0343c5981038014000e91900d0002c0c194001218403c2c41200d000c0896440405406010000e00b002042ea041e0b0408035a24904495400710f0300324010031207100340501d15070b00d10050340d40310414444090a00c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 752557985 1250 752556735 752556737
    0x9030b0a150801092010120209040e15010609050108090c0f030f0d1d150f0d0216030c0b060616021c0f1412030121240906050105092203 60
    0x20384007242c1c005082c00f420320403502511525240700305e04070305c48551001805c0441d01c41c1c4410301006030036903000307160116140c110f40300050b110b084030004200545a120408001030003a1041203044007010103841d4141c1d05555141c08420744c64000640d1140000c0e90764017005c0c0c4c00140040001d25004084250810000d01501d621918001c6010315201d101d1000a0219202d00d0300b85a9190300040d141d420007000310f1341d152003805c0303c1400c07041c544200c903588001c005000410307080700301450301101c03003000c0403192a0551060608004040040b00d05080301c0f250b81348801314455150007010343c1d0010f1040354042840c00c9440c2d082010107204561906000202284010003142c840007280030180d0043d00c0da40710003000d410081d41000c0f188092140e100034148014494805100070345c2401c4500c61480d092140c0c05405c01c940c4144201d1401c800800551280904e0301c8103c0d04603c4290b4420602031056980710070400154170340841720312461028840409250565030440e82c641180a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 752559235 1250 752557985 752558021
    0xf06050a140f1309060e0303070c02090c040e07030605011d0303040b07140303010b0c1005011508090a0b2509080a030e1f02030711030c0a03030809030f0304060b01020d09030b0a 78
    0x201000704100001d609410242c0c0f0b60b886a80c042800031501484c43c4603000301000d54954603010304054406106004064000d480190010b540c051040b801c83d4003400f41480700e0801c0b440c11000013000f92506016450004080002c050240349100000c0d461005004000d9800d05040080000403504500c0003929201e02501020b05403a4003800218040d0210a2401c0d988982100c103491611500301101d920341031420004020030b0701404440c0c1035018061a001d142d680758201b0035880c1040d11800500a1007101c000e002c520808442d0144810382c3c49110102e021806a0090340c2040c02d620400900340c0096840e8400240300c0c1c1c00c4198100001032a58200d2104600c1049901140002080c0036074400100e8906110030207603004140082100100818403010002c27800c003010521000f003c0c0611400840c96070b540078010307204880b0340e0015151710b0349420300b0f000001d00841c207412030141c01401c451681c002c0c441c800030340c01c1ea40c000d01c00020310348030a03903040000c2502e01c07110100424 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 752560485 1250 752559235 752559259
    0xb030a15020d0f14091207080403020904150510030b090f0606062109010b04110711010807020316050a0b011e030809040b100c0506060f01140c0109050604050304090f06050a14 77
    0xc1c1c1845613550704605056640401c0c03510a4003145801c80b250140c5103800024400e190010306807000f10303015603606849440307044d152868127610340c103100012042100e0801d000c115201180321074607421607006910480e5561103060805888091102c4148825082940004c10070b0030202c00900000c030964041000e6100420700d41350345a1401c1c0c030407031380d103075103030341c2c44040a1800c2e0107a0745404502240043c948507840d80c2d02951500d0f50500181801590030018003284e0092056036103c40c40d80106803d01c20b0700746480703a00c0c0c0010b5482216914600300010a0f0850a45411003244814020b1080024107507140c2e0716041e004800650b50082e190001c40400b900d55440b081c03000800c5443c3c144111156180c030301c1c20518000d10722030041040d0381c45500c040e0307404030601c0031070000204025658020920030501408114002501900c102c3e8181700400c2000401081103441540d4100308441c041c80c004001d5800a00c50190701c518604401d21a0aa00000d0110a800b0003040c000c0000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 752561735 1250 752560485 752560511
    0xd020607030206011401140423100905270103082811010f0905031602030a02300703030f051c050411040e07030215030402060f0d02030a0b030a15020d 66
    0x16100340022801a00700000400080800c480742d0360020000342060003040d401103417144040d000394400e10894074202c42000700d003000e0089500805e00c00c05442c5034030500442c0c2003e40320007514072825000d405140b2140903003d100c454041030b51403801c0161031069182d0340718000e040d08450b00506840c80b6032a04c1089500c0c3c40c0020080c19071042e2035141a2800c111075103405c5036001000982c14a0400aa5100040d800300403104032441060051400301214004289045001403000f034115504074603d1604102080c400c0c4101020042840031004881120b542c6070440744c8002408210241d123520341c00b500901c040d202160941041e03594010035000f072001900c0b802d84003a507100b1001002d107441030420303002e5080c2d00901c1c02c0040906c0b501d150b001c50340c0c000d00111829500040800031400310765555044407162540d040c0310170f80354004015884020350040d95542c51040c0b41200320000c80c2400300302c10004580109580044601c0710040d0f001940c40310000a41c12035580d81c40c16020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 752562985 1250 752561735 752561737
    0xc030403030201060e0a0e0606090a0902061218240712150303030c030c020c13021611030c1507020f2101090b0c033711030709051507060b0d0206 64
    0x3107019a0022500c10318100b5405072000d005400710342140d0a1524a6551150000751290808410354001d02550740d0000c0300801803442c1c000003544030748009140214105010101342c040d030041e401d01c0c0080650409580c2d074941406c110100c03207040340302c3e0b4680c01c1320078074007203c0d40701007281040c500e00c490843c91041218a0052815a0155120424000d0592500c5070601d540510b0404000036480710001940e10b0905103000b512408140d91420980c40840d0140c0744016442c8403100040122481d000341c011410f16840e03402403061001c42503031442c00d0a40c4189214000c50340a2425059400b407019000d10300703001d182c12070404c400707591074207030702c030b04086a0380e40000000600700000741b803d849081000380410f0035180091090003e071010b2200001101e41907803d00500c0f609950b1013840c12040392102241180b494a440101c1c2040c03240000c40c0300e00b80a0f514010910b8440080208800040c801c40700c420742e040c0125000100e25034050050301d0f0700140348049000a5900040003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 752564235 1250 752562985 752562989
    0xb070e0f0a12150606090e040503130b030106020f0a110d0f120f11010b0f01230304030c0209070311091302070b0403020a030f020706020312070e0a030302031c091104050405030c0304 80
    0x440950082c0e01401c0c0300840105100c08039101c1014842a86003407402004804140600b44031089000e010404005081040f40c101e0140175a1072014030382d480120b1320054000344a0103002d8015007a14050426002c42c0170b0156a502000c800400d0f001c000070b2140c0c69640000407903c800984081c1004110744004110511409580d2440c21040000b4003e0409000054020445e030421082c00b00950b40c00803062101032082c609407602421402d1070305162003484200034010380700002804145a400301803000c03082e0080da01500e140d2101e5804a0403101141c0a90b07209850521400c8414034140070203080070030904030094100b20305620b0300500c0f11410b032412000343c0c1c0000300f290101038201c0c400100c4295a800a040c045181c41d1002c0d403203104402c4200181c9603030741d000404150007850481c54954016100f5242d440d203d01d006503983d8002c0b11502c2c8064403010901c62a00c140c1d0084141d2a075110200444503142581480050a03001d4000c40342800188095a0440402c00c06440 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 752565485 1250 752564235 752564249
    0x1021f02130504180308060a0e070e04140609061041040810020d061d040512090a030b040c0302060d09060b040905032d0a020105060a120b070e0f0a 65
    0x1c0c1c0c55603041d480005032030055110360b000314101107000302a0802400f41071314103501410889403a584000c0003c8288001d44c10039518414040c1c140f0168503880103024035070680503201004420041800032002c100e007150526030118039240040c000e4102290040b84080007410010000c1d030f10322544405010100310b141c1c1c4804c2c8501c06d002800c40348000520001c40341010340902e024288483c250303d4801c04400340e40403e4000a01c440d5a01482d402503008040b10307055119524008050040c0054040e0b4041e2210702c40c022040720311200c11412910300b10002461458231901c1c5a548142600e40100305840c03094000c000003026864003c000e1121004154000407071122500d410003c0b640151a11801a80f9120400c80042c900004076000102c07a8900c5c29480d0f1040030b10b43c4407413410131503003541113180402d020074060340542010b4007480040b20901406c40d1540c0100201301c0c07a004015103034120340c10100e040d150042c0e51401501e08080c0c120780c40400b0480100e403504485a110b20 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 752566735 1250 752565485 752565487
    0x60b0d050a140402090c03060a031203020306041416110f0d230403020d08090a0504020a0903050c120d050c0c15030106020105100b0306040c021501032307061d01021f02 74
    0x44802101c6114240c640c0c100e0b00007081c1581455004102d84d504020b00c81b2111050003c00309840740e882101601c0103507030181c10030b45d201c1ca402d00001d0181d007050301e03d02d00480c02d01c881c0103000b80300f140d021841040c20703005800240d400c44000300e5200b03002e00705811060141c2400e5010b090010720404000d0760150301c85604001c80e440007110210148400c588454400340000e100507981c001c81407404a0f08031a0051f190b500840004264a1195100300d03401803001507142e42c00380d041034010301103e0041083c0e41500490000784a80511143d040b681950854280c0f400350ba8040c0c8003070300c440c440000445040030019804103243e0510f01c442c0d941d0030200407004028241e42402055401507000c1011300c5c1b01d074a44981051180005040e02c0e10498aa100c015a621f01c208041c2c0a0035426440707a08070342d40d490a100080c07032070103c2101d680c2142c10752640c801840000c0c68800700c6170a40e4607a43d900480300c0f2003402480310004400e045001d212821a0704024a810340550300c90a80401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 752567985 1250 752566735 752566741
    0x1051b1606080c0406140d141f0f12080a0c1401060e0112030c030305220c03120503040c360f0b01020106030503071b0308130e060d022101060b0d05 65
    0x1030074600b0000c008104541080009101c090fa0050010344103541c803a0300540c5515008aa800c007612020381c0e0301e150031100303600308440c050b080c1e410401c0c0c3e4078030240340d1549191110103042040465005000c20f081032000008005144c0c0d600809042c441441e0102c40d00b0510340d035140341ca010f50500100c0300c0e91904018484005421403890051a2206030400144480d41d000343c516003003a2005418140d5400c0084d03406c052000200034004802140206640f46926006003241518042034076861409070003041450b000d40c2c1128007a44e0080140103441346080440034000c0345207075030206590f80504091100e0540c0d008016000110202c0201c4c00c0d402110007001120031010700c0904682c1000001c2010a401000311095550031203080300101c51203160a01d10403525500003440d441001844001c2141807012150a9035401c1c0d00e408507a485d91020040340300900c0c40d01950041190882160000301ca651054800807403100108046613600d03040030b080e8100031310201eaaa40c44600f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 752569235 1250 752567985 752567987
    0x40b070b010522090303062c060102280303090b241c0803061212040801051f12210e24090108070e102706050901051b1606 54
    0x140d80d002d0003080d150700c0410301c042801810981c00c0441c00c596a580d5410700203040c10311a03000100076285a0030350000300e060096592080a018459424155548c41c010650640c408500c40c00c404052040303080e40766280c10007a90840390084400c80038142d540c03190030700244280512a00c0362480308001c00c03103112020060352044e85014145407140c2e581d008950301e0b260b405041c400a03260080c503103603100c0e5030b10000f2580e103010010452205200b55032190703140c0002d80d4000d2081d60301044c000e1105071584030300c41519031086d51200028065840040c0401c1201d0060100c20703c2c0160b208003051014030f40d2403110340c00c0b02d441020004030740b180001c800c0c0c2000c01c01c400550003c1e50302c034120f900300b560b1100014025196007504000c0e604000c41d4a0501c03600703210107082d000900502c0e1000c5000c20207801c506e004031343c4040e4444103403410613046c5200c510b003208540041c4c640c2864031121900449040c0d011403004a48151880c5542204103c200300140480044040792104d603414048 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 752570485 1250 752569235 752569253
    0x9150203041406040503031504110d02130906050303090405060d21030c11030403031110020d02030f15010c1b0807080a050c0a0609050120010c0801060311040308070b0901020f040b07 80
    0x2e006081a40090140300000b400042180c0e4003541d0030b050000040e09001c0043c0142104095016807024003040c545034040c2d0399401402d0840000003c1550140c1d01ca0078802a54041d05c20b55a248c0c00c103200c650441e0800d5080180d0016001b40344500e840e102d90741ea51248049441c0511a01d450301005200c81c9070548100852a5001d04100c0c10000030301440c1992813240d40170040401c07490b400c014400c40c804000a44070400c07100340554407000307103540c0b80009400072221602071a90b0800404d403018450104180d8412040c1d50344c444101c85502c0d10222a49140e810091507450800001000b550520644d00500503003006005141000c0c182a8074101c4402c008510404010504104080d040140d25040715828200444503045440514051034050f914034070382d65082001ca511641c0d4811f02c52416608551801c000c680c07420404003405000350301006001e24810007016011481001d40c40d03611204010000d860510200d080320105d400940c88200c40c01c0c40410440304000c0444 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 752571735 1250 752570485 752570513
    0x1305010b010c020a050f120d05031b0901082404020406030207050601051815030a290106030c05040b0705030408120417010908070f0501060e070203090901140303030c0a030915020304 80
    0x442c1140c507900c965000109040c54502c1140e01ca0b900c045181c149544481c01c000c800c9901020584280c40e0f242c030740191040d40216a44610a046190803100c40e04800c402d075180608183e440e1080c555031002d0340b4032682c0040407d855580c5a103041c0491170340d40e0b4002800640001e54001d82c446c1881d02d0700520b88401070304800d01c1100070700c50740207031403604c0c03030383da651010401e800e80701000b0006000c0307070410107501c40c0644401d42014000660094000c010451008110340859481e0790f2500308804032a00000740d000020720400041240fa41c0303a602410040c0e0040040d43d01d01669089914601030743e407180c07154003e2001c40c08120b07007039400745416051002240240030140543c3c1ea115080d200340000144807507400c0038014144602540a8005040500b0740d80c000307070905004c040c1d40e9401000c803e51080c1c0003003001203038071086600031100000c1c0c06001141103864043c4540300c20780000da24002003607510322800000c600007014400c0c14040d00340c8010380c0c03828181022010a4090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 752572985 1250 752571735 752571737
    0xe0303040b0a031407020a080f040b122203050a030b0f090f180f07230301050a0e010c02190b070c0c090f0c050903120c010e1515010c0302150408121305010b01 70
    0x130410002c1c295000f1600b0050f46600c052035698822129540e8106401030f604100030640700440c030341c840b000d5034104040c05892255054160182a400c10142442c1380c00c0c001400144d05100d0082078034000e810114283c10010040044050102c010400203801124a003030b020700c071002032000c0d0704504100c580c010b1010304080d20603901003041445d5100c0076441003030345000c0f4070301c489070701800c0003080c000489134010000d1185c1c0c1801c410900203001c119948100b99440c00f02141c1c0b149000148118410b00354480203045071290340c50742c10b03969200800c48028045060100400a4200a01003002d4402d05030005140c2004008a100716200d4414a009020007000703c04400d80d4001105c0e46581d13101c404156440000040c02d9000d04021a00032006d40b107000d10b120340d5100a13031030b25441503d100c0d1504801a0b081c03401101c4090701c040000e80503800c01e10920012142070244290302501490040c2d14180d01c1400840d02100d0449400240354401d41c01074013000000c2c01441c00f09502 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 752574235 1250 752572985 752573021
    0x1c0c0203070f1506030609050606010e0a030b01030f020301180605010f1706061e03031c151a07021c05030904150f0506210c03041208070503160e0303040b0a03 70
    0x81c56507050360101c9000d101502180c40041000703291142d90b0098005568000810320040350207281c450382c0ca49059688601095540c1d621040d1400c21100010823650010801202a4030b180c4805100700e00202050740c00d5520340c2100307000c00c00501c0450300e00510a05000601d585020312142400c41c981d04102c6071550030300030040300e1140c0040c2c40707504200100c51428400e000c4403091000e00e0000b1960940500011030400710302e4080d90040740d07544200b0b50301486422038051458075211024025081020302d9090b081648080c074001038541c0e58030140c03141640380e0140d0000082a0310140c01212070f03610000c0c0c05000d902b001e001d081240942110710f44d14441c10030a104900380382e80d0060600403e00840c6490300341a1400d004600340f40c6249402c10a030510694841701ca502c1250240d030076000d00301210078034034818403656100c6c2c1281c0d51a141580c46c1c00e1204c0500c401b030101c240041010f007116000003942d05000400042c804113045951381c2d0144030001d000c0d031354881481303c0141c45c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 752575485 1250 752574235 752574247
    0x10b0307050d0b0d0b1512030a02150a0e07090218121c03021213031103120708090309040f0c12050c0a03020a050d0c02030a1403070e09090705061c0c0203 68
    0x1400109841c4140ca1818000ca0b240b0034403401308140c01c1041001600402140060058030307000c592900681d01820f03142c40c0b030740502c1081c0c0c2ca9642d01c43c030262200182c0c00040d00343e40c0c2c800e102c4010380d08035005810110300c0ca0851468207107440303456003045c0380750785d800a56058191031040441c082c140c026220914040078410b61315840f030302da002c0b8242494910031096060311f84130b17a0407120151040302c8840c4550810a00c1086a00d080400032070100e4034a0354035031400c40c0c000043d144480d201038810902c0c0c0d070b01c02f00c00b19407084016010219a00c420f00c40a9075594860084585121a0510000d07141681c1d800091403100c603400482c1c099440d10060150b0710081404030b5001e03000a040c00350390b40000b01c07011038061182d410507103441c500d0b0280c10181c05034040010801031030582c2d655030303840804e8840318182c1d11094568401050745a00000da0504041c01180e0b8040403150039222450b9503100419221740c4603600003000e07003032a0171100c0b100001c18450a0000f80302c0348000c40c1069 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 752576735 1250 752575485 752575487
    0x3060f01080402100305151e0a050607110f0f0603090a02011b03050d09290403030c0f05090103151a040305070609051804050a0c120b06040b0a06110102160f0b010b0307 74
    0x50360b05044404c141d21000051f680700316429102004074400f03005188059452024421300445006c0031034819044000005100d24241d02aa09115041000950303254005d10400100840c02c00481da001902c2c4043c1500666a80f009944034104580103442a040a407000525003818401000c10000841c40c11801103940708054603e80c0f01081000502c000d9142001d003405007200390341902030300c800255013501140c51803415000e01c1c0329032024060119004001d456058003141204c001070070500c0a103c0c250302c6500890030018400d1402e221480d200c840b03c2c0a09040b20280320800300c4005810010001c080056200520192800b03048141c189030004041006110400040710038080205003480024404180d100d03034040c00e00c651131541c2c1c5101e004c5481403880150341510480700019814282409603180000006080d103880600b8100183c0700e2003894080102159422b2103072040c10410426510f40c07a41c000c0381c10340802c684900d844080c0e4401600103004c084424402d01060f9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 752577985 1250 752576735 752576749
    0xe010e0f0115060806040f0c02031801020d1403100315090515010e0f04150203040b150a031e080c030408030903060c0405010e12010e010c032c070308030613090803060f01080402 78
    0x286065241c1026280c44600004014005c18505c20080c945454122308038540c001004280c0030950075021800c0007141c00041e61101c0803c40448080341d140c602151480100d50300465011030140c061414640d241e071202c0502250b42c09800c1032580d6a520311006212081041c2d089040460441c40002d60615882d100103080c0a4856401d03403034018046410807610710f203c6c0844074103801045403a858141400320341981309840c810003d4108256408141c2041503485080d00d03045884c0440310050307140221032242c41c081041e104c1c48001c1c81484401101407004000800148000715141d495000c105410308001408000c0841420003042080d66003141102c102d440040700d48072120701d840540c13503025081525008985520b00070405070030303d40690088002c07007818130340c03044102c11054195503018031107842c0c0d4005500500c7c0c10070020754900300450380b002d0040c1c958005119204104002d0703502101007120006800b00400c80306041409811094031800d20b085211824150007240b40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 752579235 1250 752577985 752577989
    0x12020c04020c2d03070b0106031b02073b01150503130f02040e01051008010b0a030b04020603074404120e0103020412060b03070e090325060e010e0f0115 67
    0x110008800c00c01d46a20482810f0110b00301e440c400d4954550f5107140800c0218024050600802c1c43c04041040d0803200005103554803074141c00401c0c00340c0c1403c0c1404000c140050920300d083d00032001020060301d05d900c0c140000e1050040950055042215480140708040143c00420070f040c010024005038200c0c60070641500420703911010b00c40c900104001e0142032504503019800c00707052081c8407000c001c1403000c4903044002001400744a6041240081032440b0140c100c8442d80007080141c41e0070002150840d84900700812003c107040c3d01d4110f8040608503c60024803030f900c400104400e00d080b0030701480c4418094405034036207660741001c0c4911141b031250400122070103c401c50703400b960485010305801644100090303280c0c60402d000c1c00c99078008500a0140031000104065072384861400b45000101650400e90000c52a000140410903c01f04d4010f00c02081804a1010300c2404040707016080042228260100154034050b210010061141e140440301c2c0081000c0c1000142 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 752580485 1250 752579235 752579263
    0xc0606090c2d0d021611030d090b0d090204110a03230a090302100501080c042f07030509090c0a0f09030305030114150c0106082a0405041e12020c04020c 67
    0x4030080305400b000119004071007a0016580c4002844d860318140904481c0703680d8410310300c0c61103141081c070034140c07580030030007803000850340f401d4041c45580c07181c4002d400c103248800400102e0b06da640d0001801d9441001a0704100800010322090b0707550f060041800585207030114150101c11203000500e00300c8010400742d1203659a0041d0010107200344042e50303803501c5c8510107000c0307940c50f14006038590308503290040c40381e86841603100e040345a01d02c0740102407000c0200900440c0900440503500d40c0150030403020031004101d41009030351010b142c5030080e01d503010642d40360404030f8030152200c0145120a010301000d6030f01000004d0340402140c4c1503e10020110300030100c03140104404505828510000701c00115103070380b400005502c0030007101d450b4012034510282040384500c0006201e4555403051041c402c1e68100c1703041a0f002075421511900d030041d0164a501078000242840c18022540c5085280d25001c9041d070402c18000d0415048400f18503001c0c850020a036903000e44130b4408 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 752581735 1250 752580485 752580547
    0xc0b100e0a0c05120103050709150509010b090d0803040c0e0112150c03060b03180618190822050f10090920070c150504082e020c0606090c 61
    0x1501140310f4416116002000704d80d000f103d503101c5c40c041e0307241c0d11140a120000c03858900391006224809500100300c41c4007074000030480e401c0102080041c2d00045100790000f07050491440003541031002544140c0c01440524035007828180204c034012410380c070043c0c07075601e00022440854800502071092918040001401103114102907020348081d0b40404d204500101c10881810380c90b103184580c2100320340a690032507856032404041030804102009807035211a501c0445c4d0880a441041d500b806a010181814070381010341d602000000e035030000b5808040030400460420072000710041c0c0c0111624044c154844000a04c0c11074035104450003180c807010600191707039603000c6080031a04510030441c0e8175441401c0c009440412849650301c011800c0e650038008e148101d090310b0541e040b010107405104218051074070624801a080c082110700d00d00c461650024138030040540100000180411f481c000c1c0405c400320030000d02641610701308016140c5490b0782c4e010b0030000501001051 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 752582985 1250 752581735 752581751
    0x80703182f0d080705010b03060903030406091703090109030f140d150504020a09082b0806030c03030a030f110316050c0309031e0c031c0c0609020409030c0b100e0a 72
    0x1101ca81000d009803504804060440e1060045810080c00d9003401440240aa507000c4824181c0e01d03582101c98210b250000c2c000326000654a0b0030020216010b00101c900d0252103844507001c643c416501c2940d5a0364070701006e020103410964500f180700c040c0c00c148865421000c115801b9116031036000782115695400d0a0703045080c121400043e1901400440d220140c013180541020389a01900ca20783c4120344041503000d400f030002d008014041e80d00c50041600d0000d080c0d980c0c8030060318855060040c400780d5811a102000030303110fa0b459036980494000d82c650b894404842241c2e1071007070039a908108000e0300c8081ea0280007500c008a141c0345e40d403001c4507000a03003580982000c180d490b00072968484911310400d03480c42d03483c030b12110a540d51041554109580c604080401ca00a00000c076440301c5118001c000c0c62000341d0041c00042003010382e40e40040c00311030510320704030042080c001c2d064091001402d1000c1d40448440540c10070b050421144103801c010060401507069100c01c10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 752584235 1250 752582985 752583053
    0xf01060c1707080310080d050d050a20130828440910032301030b101d01091107060c1706010e010c0f060e030a08070318 53
    0x4400c540441c0d54400c0754031004145064032041d40141c0707861481d805211804a298040401c4038004581c00f13446091802031407000d0000a4100100107403103043d511900544c0c4046056032440d180c511031480c0301d80e54100d40f00400c11120803500501070f5684030030155440b41404460704e050451902c401142c4400c102e1070a146400c0320b020414000c900502040380c0040b110810303a050804c0d40c41c25500c00d02c141c0f50000603480c092049225030103520518a1401580241e020740b010258170300fa41903c4221038504100b038003500fa88100c40030341502003040314080d008003c40b070181c01b50708000851800f2081c0d64050400701809036140700ea5480700c800c842d62007000c0494030340c175a2080007442103183c004800f614824200c26003d02d40c25031940003455540c4102c0c4030b4205100140c660081400003511041c200604c02181180d040ba0742d107244800009003013001d01000411759541502900e0140c0f001011b0f0f4028286081000a030000740c02c0000f000d0510600c465802244110322608031464 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 752585485 1250 752584235 752584253
    0x210b0a051201061203090609050114030a1104091d0111130315021612020c01050c12030901020d0203042904080a031509020423090408041512050f18060f01060c 70
    0x4c86072500180d00c083c144201034016030a401220703000e840b41e142c1255a00c0042d200c18142c00b0108002a40400000301d0f030004a07072082d180c0d1518000072509198441e6141011503843c0042d0404001da034921074803002e142401640c0110641045c96800c000180c0821449201a40001400b60001070303d0aa04070310035030306031881440101c54115181c3c40d81c0c1004074800d5001489540140a10301810840394020000c507159100044000c01517503103040a903007040d820140000015540820000c00d11103030034000f55020710b000e4400c0c00340c55110100801e112908005a40713030030080c10803c0001042030305d07080d103101c0b5829080c04560700f01e940300385440c54642500205002440440d011880600e07400d8a628107102903241d0350780c489804000c100811702c0895000304800020003007070010b41031050b150340e0f2050480c01c2030550000c042c001001a60401c455440325000801c0800c4003070780030401c944c0105401040900350038105a0310480700c207103050244006001040200c4000c00149032 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 752586735 1250 752585485 752585489
    0x403030b22050f091c0201020d0609020415020d050406110f070e16050c0c310b13150506030702031c0f0c090f05010c02040e010c210b0a05120106 64
    0x80c404a410410000344039590507248007622080c524040010300d40c01c42d030541860142a94800402800d0030030080803c10a6000c446141195000d009900c900340b268012400541410b501c0581c0b03ca09110810f030341c6000f01c010450841d407202c181c02c1d4001d034025045906694036441e020000580d030002c1c0515180c0704000e82881d0744621100080c0d800441444240100c20940d40d08400b00d2610104842c107000b103110040c0542c10a4001c51b0051510a01c140701d154400c154051500420059000c00c00180f1035460101c00d4640040003070714903100140d00720540780c0c82410040300325a079212100126250003614000c41000021401460003001914030031a4140c0ea903424000b03071240d240c005400050301d060300702c0d82040600c1d8483c42c001d198040981d0010140144010315000044442d0168080180e0700f1540e0740d02c824800e03180a002d44900c0e801c080d2140c2e815035840304400c0500760100d4078400348640c502030f0112093359408060600b100c0c4101da4141c00e082511880b580100165 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 752587985 1250 752586735 752586739
    0x118090f080c0708010501060504030302060f060307080708100f0515041d0f1b0a060f180302040504121106090c040b210706170106050d020c0a24052401080403030b 72
    0x418420740304000003c0000680d240c041c000d000e03d982ea4201541e150056000003805038020f0400103031b07000189000658000c000400b11400107a4441c9200c0c10800d55800c103008503080110700842d011202d0082840392007050508010380d150900056504440f20303810f0714400e68950021403a078000c00c500448900d680310003550245d0701250003442c1d503107050045041031101b5101c8014583c0c500030180c0001c5038102c1c0c44083c20130005a0080358104400c800380c645009012601001580762403040f030303114030300c552041c507101005e6044c00f410b030012180c0807000c0307907101700c040010200e000f107104503a540e0180d03400b240211403580025150307841d1380d120b46104801c25200d50980f040009540040300c10ba9200e1303d480048030b04400d00c00d02c20074003c544c0030580c00c0210801d00b8107141c3c0108041d520b4081600d41000803035541d10003131007200a04803a21031145007007140c2c001b820322030141c01091041c10700b20480d541790080b8a004201100315070602003810002010b05019401070301e00b590380 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 752589235 1250 752587985 752587987
    0x50609150c07051201020f1e040b070605011e030c05010e011e030204180501030c0e0423160b09030606010521070309030e0108070804060c050c060108030405180118090f08 75
    0x1032100740594981440c8503052140f401198070141031075040c421a194080114030051503c002260324510241e1034075002031490500f00f000103241c0d40008046e1200700c1c82040040f4095140522003600041c920450240200c10302c0402c00014032101800717000c6403c02e08000015000400060394880e0314000240509803d00200021150b4994024411703168408010302c4500724098030202110400d000040594074490400c0c071523200118001a0b00600c0b131401240400e00d41d070680c0f8400001c010f8401d025500c110f1416061a400303a000d04003600d50100ca007800c1080f203000080d641c004c080c00c003506000c0005442e0014144034400220b1002c05030250400c0341c10120310050092011020903000601a140800354540c0705d407079014020441e60360742c006c1c1500d4a4550341d004007140f410032800d04c0030030005d0aa003d1024402e980c004e0845c20080e60700c43d403400052110205e000d42940d140800d070140107000350542a855400c19180c440c1000500750070070300d42294610480d000240c083d0030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 752590485 1250 752589235 752589247
    0x2040e0304030501060608040503030417071209080f16140118030f02013c27170f060112050c060d020d0b06270a0b030712061e05060915 60
    0x60004001c0c000c036403080c0020000184d58542c00c9942510544004015400810104000c95901c0c0003080070300c07a039100664500900b03980c1d101760142080c803249001c00c004200400c10003800b0303c100c000321084a405031011010745c1d00381000c15609405440301102810000380b049074450100b242c107101c54503844407041c5460381400001040170000803800205172480000c66200e621000d000180c104407420030121489030790f1313294080701e120303105010400c0c0c07816080d40d000300c081c001440ca207219004c21107401d03007495141200d140f110518400c1c10750021110407900d0800143c40c41c1150751070400c0700103c01042c603207103052800030101d003540420040b84c01000401709034000c2c000500e962204100b1341600c2d80c18003842d030044203843e03c0014044031004151100c41c07294120140c10045c0500c440d2901c8200c0032590f90001c0d91031400061000c000074612501600c200c030040d0803641b400300c201c025000552000c050140c003405008000100b0b9500240d211640c2480c203800b025028191910 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 752591735 1250 752590485 752590511
    0x1406041208090d2d02060f070212010c090512150103020607140717190c12080c06090c10020c0a0b1b0d0e01030c0905090604020703050d0f0b010e1804110406030204 72
    0x2880251326681071800c0781e07159007515040b15281041c22036010340418185500c40c0c290343c14941007079405a800c04000c42202007031900c207119035414080e290b103c140c00f040c20242480400d010a21182044c0d5014086c0b444850348402047c3c4d0445e0740c100d0321241e44084500c0c115403401d800300341415051040b0b40000c00c03030040e0310411441b80302081d07044410b403010846000c4070001030100c001d0080101154117100d80007102e460200c0441c0a070709982c0c98510750404d824940b060480e803d6899420203d404112460305503089028001c581c402440654103075000201805018852110503000020b007200c44011501510004034010304103640965228a80c0600100c2c0c081141d540082c0c645454614a10301420b842c00c1a41e8006d006c103202aa00c0ca800c0c03000940c02102c01390b06012050000d80c1c1100340c9801210200d4802d8400813a80d24051400900324111681e1054410001d12155130052a114655541c4c82500114010a051884c0002c20010039060700040c1d00a4180182e08004e6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 752592985 1250 752591735 752591753
    0x40c0210140f0f16050a03020f040f06090f180203040c05120d08010f06080a09022404081b100c110a0e1f080d080a020d061205071406041208090d 64
    0x30b0b03401400e07114150755911031402c0c15141c110b40c0d000381c984000600014291280001d0b09444060f800c3c01464030840313000c00300d4141c0166025810011000307205224842c0d001354004001e00b03103107003c101020f00300741a50440388510400c4000f0550f0100005052201d0803007010000c04000c1d142101e0042230b030540b141c88460306c4a4980c0442c20b00000012044010125a412191a50f4401c5040d449211201d070282c201e040707041c3d0340100004100320324012031640072000741102d0b21401d030380c0b545030400d550b080804500d403c000c80b10640b2204440d98984a03005a4013850900c0c0401c1c0548882c9402d012009610720b03043c2d0407118980000c20ba5201c090240d40c0541584201074608444241a03608903207010b00510045070402d20f4a000c0751800340b004603800414418004d404c240100800d00112080d55114140c00202000702006002c003d10822018243e04544500d60750041c5001c900d891050f8440c10000c1c030355040e20302e410701c04c0140948407580c40c000c0c10084c1010881c18400383c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 752594235 1250 752592985 752592991
    0x6110301140f030705010c1113052a03010501050a030f0905010518011d030f03150d030f1205070518030a1a090d0c03020d081906030b1e010311040c021014 68
    0x1e440b040001e210359140c000b40810840f207050b96103c1800e0704a41c3d07103ea40fa0300e007240e8a504102221603803401841c0d40e000c0d00344198122400300800b82e0340c049402000c40d02c0380000d80c0585404100600c00c5991050071151140b4980c100031807400303100c1844000a0910340c1c3c3c0500b181d4603002c203111403c400c0c16100540d002c0054028800c1485c1c007007590320220240c44c1c0342c0c00c4540c0b003000300c1130203070780b80360702544d03100503101c0320042d00d01119000305264500300e00049001813154a800306015810419014404181540c01c00052a043d04090040d22134400c88210791381e101e1240b9003156408000d040020f65001d5000340400d1002c0a14103c10102510701000901031040780300c00542c85004030300441609035005022003444001d090340d1141d07026201c1e030801c5a00d11442104482240114001075100c1d0300045440d141c90200352641003a40380c40391191000e010b0040010440b10480c90092001c1110f002481c0400c00400b60302d81105400c100e0401404d040103100041000808144 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 752595485 1250 752594235 752594239
    0x307090e01140111030c07030c0e070e01020a03030b0d08181014070b071b03120506030a0f0204180b0a020403021305060612101707090f020f07030c0611030114 70
    0x84094681100d0300000d042405159055001c00c02205030661081c4000061038500505072403810706602c10301802c000da103820540e04218030000400240300780f01003565100341d4925240e191401d03250700003521408002005000c00da2030b80d0441c07070169545011a5125507100e20b410707030b4a48400b411181d0b207420b0041c0396446000d039207441e080024064083c1c5000d031944c80110629104180e61001d000401c050a00760030002840307110400c0d00311040145410b140292554002c1c2d440034403402c010340c2d0008240354000e1300107c40da10b0005260188003074495604507000b1641445042107411501c0114501a02c09514801071207114549036008009a9000f43c44c4441001d03206d040c21010365006a9400390032800812446129000050b11560850741114041010300c0d6568071040038003200381c2c1c000700c9642107540f0800012003103100c3c3ea00000031725807066040000f6103841403164020b01c138015060006a86840003000420b07032016983c0395421424603207958603035100c03800c1c0003440d0320494 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 752596735 1250 752595485 752595497
    0x1101020a08011707080d14090409050307052503020621040317010902090603060f010905041a120a0302030a1107031a160c02030c0628080f01120c0b1b0a080307 70
    0x7082d0a0001c81d61005031a201070080c80341c84080b040807601120a600b913000c2d4000c0a228034208c1d45e4850088140300750041b00250b494482c6d9090182c188514600e10b150600f0548a80140419250011100300c940440b011510348482071010340001c0000200b03c48005440d000300820140c109002c00354692080c1020135042c0e0304ca0102400302d00c40c0400e010340c41b050610001300e90785085201100e60f01018507005825566540105d826554507540c480b040b10110307500f0800710305041058030104000e0500a1100c031708981ca0103512031041d1002582045416031040ca590601080850011507116095003044005100a020003841c15035505028048050003414600c3c800c500310001c0c250024040c1802d82800300800c21240c1c418641d50715030350040d81300122148a09190109012482c0c1c50718031319441c01044070f01e540901600090494542d0300704200c0405c0143d209101984c111046041e035446003290509240003101024070342034480c0c800000300704500078014500680c044e441718 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 752597985 1250 752596735 752596769
    0x140103110c071d0709050f130f0501091d03180103090c15030606030e030306010f0e01030b04050406020c120f070b062d010807030606020a1b120b07020d08160f1101020a0801 76
    0x5c988040c45031003110740c40303101042c01100c3d51415078200c0480005580c00099441c02023103e403019104260300000c161960b86800f1a5100b10200100c241403407400013030751070890906500031080741e01c0ca81071410540d4620030881000f80407611003000d001c041041040100e140f140060250006005d040c00180c20310b0130b1542c04d804000203881c05240e050711a01d4081e2030f0290115458044011868101611400400d04641b16403140714007a43c02110050303a01c0755070702c031000c1c40c00c21b00d01c40c0c014000340200f1004003450035400c15140f0341a0710640c410203680310140025000640014940115030000c42078040c4140c000e155040c0d0082d0030388030307010136640c0d06200b0380c01c698080c4605005a0000138642001078003600325604c036030010f000d01c0420b060300c6414411150285000803900903550500340079155030100314241c04c00c1018a018001840d2441003502985551030004080c441100e1070850303414002e021032184000d90b84000c54441c56007490081c0132160070b115182c0484030f50818 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 752599235 1250 752597985 752597987
    0x12021003110d051b0c0a0b130b0a0510170c240a051303061104091802100e0301092906180f04060e010501060c020f0a140103110c071d07 60
    0x4070703140070403075201c0c090421145040319400750000600d928142030611032022607141101c2c2c00340c0808030034600184803400c56413404a20030240500a81c08400034a45404000703240304048a502244c600c50220b020345440305071207000c8189403c00703ca2401c48080181c9a00e00028003040c0995041310008a07000c40c90b039461400e0f8941d04d0600008401c1001003540709030050303000b850000c86d02032602014a641c2d44498048494014254041000008042000050303e01468140c0d00c55419540800c4581d64002440a80012182424041c0060b03030004203075400e6211408480e00010440c040d9480208188094910011083c1002d21000e0220343e0074100080b003195025007030003c4450640761201101d46500c00200300302c455548a01d03075568003c800380985802419503843d800c200da200340c8100700303100d83d42c5c000450055000c841c04010141824285081040080c24005004800800c44488030311540c0e00140561107140700004240080403001c11500d00f050b006241300340c48001c8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 752600485 1250 752599235 752599241
    0x60801061a2506090203062a28030e06090118060506131505011416060b060d0204080706030b030102130506090f04090b0402011b0308040803190e0f0f01141f0f12021003 74
    0x206540c0c40300c06240a40c0140c020748001804400d00c130009c0e0030704c0031003400b804042040c0c021003101d0000b9150080e002d00300104100d00b580020600000b07002103600c4000d009440301a240700909001d40b00c101041450303c3e8008100841c8020120511030740042c0d880100c000c0315188a80350019920b001e2083d800c0700c007801510b000b00100008076100044940700c150243c0003c406141e0310520400280c4031442d4284028070081c50f0000141c07a0003072a045018089605802d1a1802039004000d040011901e2108400c2680c104551041e1245111404951007048148010350031500e00000b0720140241c00841e43e00c01c078800d0780c0700050381d0140d044c150f07844c0c07200c0d00000303010803652008030300020301c1c25002c1c507800300b10551207140ca00c00704002e060546035507040300012500074007964101c96009100c4201900b0340ca200034082c01d00e206103443c03401c1c400104000c800c006011002050101d088103010020150005101d03211916038000e0203a0307619216040784500c50f030181180c103903400f0780 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 752601735 1250 752600485 752600521
    0x8070804151d10080a0e07171b1005192601051504080a031103071e120f05180402160305130e01030209071b0b070504030501060801061a250609020306 66
    0x15940c181e4507102d1040c81c60140040c4e5008200600911038045902410002c4406103180300600406c50200424010754001805d270182030301070512800340811540d04681100c420104648010b80d481100280403211740c03000c850a10030502c06001c040b0100185c1c0b1090605a80c0100e0f880e007c21101483c103004688103d1103204a00d8215a0040c408039001d205603c100d0440c480c1070301e00d0550955180c407030541c0c1d92218002400c80c00f030100d00510180031741100341c810050610a03440c40010300c01030f004d401041074613801000600c1d0440340b90780301c0d0740503100400f107000b91260154074146000f400c25007014000a0510111210009109a00c0d81030a8102c07900a400e038401519003c504480740d58107807450b8669129061607160015141e032209901c40c6002d5a50b0350303111400c52901c20f080da1101d030300032035603681082c2040c0204003c001c8231a9140000388656986e0311420a269601d40e00c1c4442c23230001d21040c0b004260b0908c4801d81049140510031400d8803001c0d615003080d084048552 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 752602985 1250 752601735 752601737
    0x210050421020a03020108040602041d012102030322090e031b070e0604091109040503030105040c090305060f071404080105060a0b0c07180b0607110f10050708070804151d10 76
    0x60f0010005940194031054000e03005102c098030306900c4110440c4910850070404840707001c100300403c02c4015641d00640c1039902d2000c0603c080107143c00103507490080d00049010311854030036000f602049101031000a1502440500a900c0c0300c41d4a9034894000540b0207180003401d452003540f42401080e01e10039070702c48901e00b000c10f032680d0052000820303814404603002050003012500350795450344464800c0784100c00955896042c4428001503a076400340100c140a068041400001c0d008910343d640a49601030404c40c55440820480d000c029a68401021000c00a000b240a00c0c0640215103e0b08042e140395400700d60b1120144002d12030400703401000c1d041403106200d04190a0075404202540716000301d40003018600150159004c1c020444440d00390948a5039942030030300d03400408600840c1e44002040302d0800140003403041070001803444000050382c0040103401c10581c0c0c003425a064099080d4070920030094100f00300c0d4858008075440d80c0c1d4855020f0300c2c0003000d11b8200341407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 752604235 1250 752602985 752602999
    0xc092422111c022a061902160f0519060b01140f0a0c02060c07081b09011d07051e1c0c120209030a0f0c0e06060f160f021005042102 58
    0x3150300360b40025085030ba81c030020030030b103902106403040200141e0307800700c04400b0281c007080c208503215602c01c03007010104242990041c08080d005601c024420200260030400300b140412841c5002e90901034205809601c01600c94018404e001040d44211990310003a01c0c0c0721226040840456142c0c000ca550f47c0c82c440c03204105801d141c91068540683c26417020746520300307040481c408542088134035006800c840c3d002c0d118440054020505c91860b030341081d0b56001041d4109140100c0c4011501d0701c580c0c45080e454089200701d0302c1601103c00041d40d800001da5507291404c035103070703c69102d80d80c0c00502e02e5581000c6400306015216008a1000b144c940d400a4544031900c507000c1d4204202596043c002d080003040801c03e40d01c000c6c0c18071481015003000880c2030941d0154004c00251119010315010f0100b021510341801c1102c0301848492403002ca2140746141c8043c10400031070009420a142400c84d5030040c0d080350141c0240e81451500d810b54a100100d842c4c0300c410060b0000e544111 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 752605485 1250 752604235 752604277
    0x6070905030102090a09231503100b0a060503100e042f0913150f020a0f030e060106050d020c151e10060f020f060702070e06030c09242211 61
    0x1c0c980c4101c07c1c9819201201007004074038003501c42c0d040c204403a0320101408010444c0c0e160300e418005030840c501148400c00c844407140e0041101c070f4a56000303020510000001094001c2550700304036000300005c0d110f0030765074500f91500442414881504042202c1044110402c1c2d103071050f0194521003010780942682c0e86c81d4600647c4000801030107440c04000f030300c40541e455016015040e44400454030240ea156488d5100a01c00c100030b4040d10300301850251000000d0301e0200e0381904443d180e2501c0c0e17440e001040302040092003481003001c03c52182c0074031145d40c0b52a61a00314403640300c2c200c00708850200304c50046604481151118045040058203014407405580401e80b9a0505e00c100d03210310210702500c600d000006d0f02c948016038041c0380b027040861180f00003a80c0c48501900909104070340e920100e035407202d014000100c9443c906001403040c180c140c0c0d584440110080c425000718507030401c4442a040001100f92945051006481c0c40794102d00844807015645c001180e8108 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 752606735 1250 752605485 752605499
    0x3091205180f061201080a0b0f040b0c07080910020601090612050a0b1819150b01020d1d03030406030e010b040204030203030703030218130c03050106080717040203010603020a030506070905030102090a 88
    0xb80d500100c0c40c2d101d0342c2404848080c100d8800c480340a416020028500d00c110303810175541c1400010b059035020445202080b0015401c456815000401d41604c1074450b0300e60b2420207003a0080f0801c01e5007082000415907416580024600d0484404240c100005600c41d2100d650f20147d2440103042c640c049098403000500419110b0791049200842e05412401c840b800c500b803407034002103155580300d00b080c0c13181888212010301c1418041814200801d000160010303440c0c4174440060420f100e40c4940340c00240058400c2e0a5001c0310043c241d952716134030351002600801020410128a41c40c1172000c1c41c031401c040c0f08540030380707400a004605155141d0303400c90283d0721400007400c4103032101080303001c0340d1101a2040d2883c452400c012a05220300c40c2d0040440301c050784802d040000100c10710081c9900031618081090300242c0c221442c0d5294000b081c054055940000c3d0040030602d8004203100020442c0340c020075040d074a04511650345c1c0b04240c241c1c0104020a5480260004204040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 752607985 1250 752606735 752606749
    0x1091e140f0307030804080c0105040e1906180e0f03030601081f030203060412080a0501032411071b081605040c02010b151b07030b0718150309120518 66
    0xa4903004000301201c001c00d1011030300704080d80d0300444100380041814000003100780400c091841013843c1c00f034201481d011003880000405070040d512561651021444c205081e0802006040b007440a40c400098068010700240070107542c0100e00c0c018808843d00310140481140d0113020165503402c00d03610344540654900d085240220904440c035840080141c0f0700b80b090074801e90260006070030088141401400c448401000b19449e41e00d04030041c0001090000b08a0b40165080740c81d0f14074490100300c2c0c100038038001191189101c0081410410003d0300c05960b2000144696640c480b240d545c400c0c55a40c0103904001c56008511010501284c103041d8882d4810004510011495510000c08242d00303605407410740160800010b4185810419100d00f00040d6004034000c101052a54440244e48480600f6170810400c0d8402e404921914580d0442d015042600810050404603c2c002d0002c010651045507112054555200c00e039010318191036141c2413260680c6d1851006000b00500c0c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 752609235 1250 752607985 752608019
    0x702062211060c2e2415030b122b140a12290d05030d02160503160605010e060105180103110c15011707091e0f0b01091e 53
    0x301e02c5a140c0401881e207041401003604803c0402004a8604d0f1307030100b07400c0c0c40c0d03001c1000044010f201c03400c100c6540c0d004040022100344c9141c0c2103000c903058000318050040100c0e01c9034000c41d203102440004e10046100800c01c1c1031072280d0305000d6500d55080804841c5442c4160210f40000808035034540644010030b5080b92601d0151041d43c2c80301e207003034111410700071038440c0600300c91040d008060800700c0400101d2402c840000c50b8211781c0c0d035210350301d125030032600f1407145d004110580029591444040c146510106990310b481c481b03041d18006400aa00c1900c00f581044000680c8800452440c2d000c0c203c107940741c6140240b4a40c000f004100654140e9040550f15801c2501c14031200008e025034a00c40b80203040214200b04043c0c030845c0040c2c00c0b41d10480ca0000102d401d41c880003404400319400e500b40032442c100001c00020500c09061840b2200743c0c02c119660000001c240d0040100d85000d890303d42c20310342c454040091600c200d105045100084a10034021610301c0c1511000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 752610485 1250 752609235 752609257
    0x31517160509040807050127060b1509011817060a050a06050a05092e051207060c120915050307081608190b03070603020715020903030f030703090209070206221106 72
    0x652220b0788942d01100081d2010f8500060b603240700d00b07420006a0f01480c41d90f8001110074100307034bc0c90000341030641d03c0784e10364540c1402042c5224086000c07a1002d45001003c400444040070a91409095110b070001c41d0046809860300c0005280400075102e04020713100c001d000702034864100030034800204000b51440302e8501d2082c00c0f0613009241d0f00701e0351200c061128001c00099250800740f020390507600540c602c032600150001d2090740e0b0300161010340250071000c200d8100d0310380300c03054504a02e660000c070224040500c82440e0550044d000f90b021308410b685484071940c070080030f004985244154440014200404103c02c040320004035401003650ba40000b03424840100002d01e013840d5a840500480d8000c0b4884085c0002100a170a41c07c00d080025884c00e0700e040c001945070310440c00387c91041e1034088045030940e442a404103000c5a8050b000d41c0ca0390605400c042e55400d8200c5403400c1c150002e41a00c0007101405402d125099880481e50108111620411040b5000301000301 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 752611735 1250 752610485 752610491
    0xf230405040f050f100f110a1803080d15060813061a0319030807050a05040303032d0f0e0d020c091b0a08100b0403020f0d02010315171605090408070501 67
    0x40030920622285a131185150020000702c204a40c0712026211480c01d207010b4581f034400b01000b00d22180040b19408562450107840d800d000d460b581a021605800140020b0001f0458003a803c5003a0302212100c6c030440314080300310340e45d180c00326065042150301c42103c01d010100607000840b15000450b00c01c120283d65500010100e0120707240c245003580140d080011a0f07004000d050300103040c150403a40600e0424038115a4400280482c03045100003420161740341030040503040d480650f43c1d4000c0014030840921640b542e031300d50140881059a0312041e2a0060074140c43c103000903025040308594020b8600c2c06001c404000c240c410040c40c5414608182a4488005045500a107019102a00e800702a402c00603140e0341c1034011500700b1035503080304220038005030380c41092340105c800c0126241100b200903840105c6c040c00b2100c540079145400c5010110341075990301d18400160f031104c4219017225407458494200311009200d00342d0015070311000315011038400340090103254000ca0002c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 752612985 1250 752611735 752611763
    0x1a0d0b18030c0c040513030912050111040b070209060402091e06040b0a02060703141009200c10140f060d1a01150f08070206070f0e03060a02040f23040504 68
    0x4035007907a2159900710040c1d0007600c0a0300d8186000c2c860940c00c000c1c400b805804120b81564060b2682d0020b00031400d800c02100c02d00300811009411048d1b04165405010f919a0755440c5207025030b0300041012840740c410b8000080302420140700b50303000c19800804807400c3d9281803041440094451346001d4100c0400c11002c15002a84801040204103c2c0d00410b024901280300408440d1160f00388061a404041400003800c48040c20f0020342d201046e00254414400c43c5290311848030700304080c1040c0340460221031110f0013042d400004d107294641845501300803402d02d075492904075024801c250b0100701045250500c90003080c0158410381101e58591400c860100000c81c0981c800d20a0402920310b070180b5550080c6441320700c0049040600d42801c2111010f51500310003410901000f080c80c0c3c403001f815110f60820318803010054161540780c1010050540650701c20b00800c040c0285403040044e4641e000e501c07914035581d180782204100c4035044200701c00f800014100f07440b0480f0035590 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 752614235 1250 752612985 752613031
    0x50f0d05040b040c0e04031e110706081803270105130810321506070501020c0d1e03020a0c060f062102010801180e030a09091a0d0b 58
    0x5840c0902d00400300002c09160500c2c140c00c48901682020814040d45800d00001070b4020f8401d00c0502c2100b4500d0307c841c11143c2007155030b014180c175000320502c121500021143c2c4c00000f5103020308540c100e410030070202003028a94900c5035a0908070714000b0003030b010400c2000702c1901180d40c141454020f24020031242c1000d0b210945400800aa40000c081144942502e100f0444038008a440341e07564810f51070084a0340ba4000c0601c844200c0d024000a000c255081e0b04203034402400500c3d480d1180c0550405600030b400c213502c0c0710014440c0078160034049000d00e442d43e40840e10b00102200300658040300300d01a4124030818828040b0408017100024814050503415218034040010020304d8504041391604801d6400c40d42e01106000010260768800d003140d05403038800c02d059602c81d101c5c2c842d14008250350a0700c007000c0e0002041815023182d001c981e100840d459080140105030a140c04182c0328001811810b0780100c81030b00d0703c0d00061045603d140d00845581400007803800c5200c07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 752615485 1250 752614235 752614241
    0x3120908060a02040608060a0513090510020c07080d0215041106070804140406060e03150903120f04050609031c0504050a0804060c02041a061605011803110625050f0d 73
    0xc0303200300143c0119080c085c10b98403203038090b030007002110b0940f00c05250002091006e150382c0a8420043d450341207550902c00d08001e4201c1d0f511440c9001c40d070301d0007801013880d110000c50182503058091803503015010b500c00500560086000880303010640c0340c0d984c94411804054080e80d81220041c001c80000c1540d01000c0c00082900807046203801c9801c604001c200d42c0250412400c2c091500c4581c8015140021888100040c2030104825034882e1002c40e4078600920401070320001507042000000c1d103014849601482c85241214542c1d25541082031700c902840031400c04070551400d900940c030105400840c0c10078090010349243d041c0076180c581c030f06d40c030640000001c01c071180f019804605140c800c60f0104003035606a5280b14990300005461403190302c030503d02441c000c007800d2007403003000c3d032001ca01d844030305805441c440c1c5980b402400244040c1c1804109014050003e121615002e400c44803080c56012010680c544e144026500f5401c500d540407464403051000c2440710355184 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 752616735 1250 752615485 752615491
    0x90d17090a0f030507120810090c05040506131d160c141b0102070b120a020a18080106180903020c150706110301050a05100f030902220906150303090312090806 70
    0x2684d43ca40e01d904504151a00b0980d251540e01088400400c02c2080c1d64101518000d441c106000840c080d4099032086400c0d00a9811440e80404002070f231844603240841c900c0c003100c0034410018a000300d00c40340281e054008840c0f0086c041c0c00c0000b102d030340c507100c2c0c1842e2000c20301c5031300000080725080080720300c0c2c500741d00c8070b54103c62800c0783d103102c3c41d6804010b070360005c00707003010b119203071108150f08040070150160003071a10f60703008600301c8001c50040e60030440039554400080134403035941485a02030207141c400c55980081201464802c05428060b40c4405a015001170414180800600540b4006a4110301c50300c5c1c0705100c581c00040d01c9016200a0034410000300340c0703950402003001408130195010900c00d88a0705000319001750891207411006209040000b502c1c2a03d00200b5034288000c0041484c0c3d071815182c01894250f542c0c840b04e0014081c54080104522a40c000c04002d83d031400040d000c0349841c101080003d01d4880081030484540c50441045c1d0f0303480d00841d140c21026 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 752617985 1250 752616735 752616737
    0x601050d0323042c09030c0a06021b0a0309030b0c0405061801030b131d061605090112050906040b0a0618020702040f0e03030711011104031104060b040b040806090d17090a0f03 77
    0x2458a91a6540d2491001501711114402552030f02e0030201072242c1e82c1e0018900101010340206070451003150030303040f5502840f1751000303407000da00003898020525040d6000448680780d400c130115a000b0f1108055400707564014103501c1c5000d40b4141511300641c0d1501c08a81003646074010444a07458014040010540750300700801d080c0002804491061959045045180d000c8402c0008151105503891401d03882401d00b96034848481c40122900319901306880d946a04000c24090401800a1501d00c11806242204a1030322900c01503003c0c0c030203d01c950030031441c0e41010490560007960041080074401000000c000f40b415100c8002c1d540313226084d444941000c402c01c681e02d0b40111040440ca03800c20b008101c1807418880e4640107015600000d000c6140c02240441c0315100e907488040a404000c07640f945407a698005a9400da01c00c2c09003a10501030381000c035004040004041050101584500288a007061042d5503082c0e030007000300201e4443d41000401150754bc14041c007070b45020b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 752619235 1250 752617985 752618039
    0x60d090501093309020a0302011d03010606091403070f05101b050706020d0509030d0e030a0b010b04051201140708040206130303121d0d0f091a04080601050d032304 72
    0x11a007402c070020000100700f072006013055a25001030760740e5000d050951741c0c2400c0442000c00404001012992901303201c80d055884d042021170031a82140d102c80031035800103c01e01c00d0a440c1000e06890714111303c609a29409049414811403500c0c0400501d01f901d6440c4c0f10070242c0d2400d17103208080c03860300340139959030708101d02c10300c41c180c3d040c48a13548803440b600b0302a140c0a01400400d81e255108070039102004401c00e03110950b60b07400c0c030410070303141d800110205a075616500042c07220b5000d4807501e880360110341101000c010060080108508844998900581c0ca41d00243c0d00103c00402c1281d010400b000012101034200c08090051400f0f43d03034031140046081c80700e03412502404806411224078629400030807c0018455410403458074010f1407689046c04103441c00c8000d0342003640800c8181058a110701e06000c0600102c0d000c0344100c40084c2d036501c00b803207045009000d0103000a0401d041c5106403072034100c3c01d984508004110719180a5030340e02d1003440e0f03203100c00404c1d06001d8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 752620485 1250 752619235 752619293
    0x70c08180319050705010c06110d0e060a0c02070b090607020603010303030f051e060f01030e0a0f06060b0c0709091a07031d030a050d090f0b070207030b15060d09050109 74
    0xd080154490040b9500402807490740a42c80c0c040e550300651050034100201400c00300300b001010b400c8005601c58a0800c25101d00309040385101a00341d0040c68046846080e001400f02e00c45c80c003400a880d8855006071205505140160b40030381d2115040030f420290400985005884000043d4000c60299500041c401d160b448a0815140064105248100841901c80b001c003d16000140c0105017159800d00000035000141c4c0509580c994110150044800f07080034842083c040221062003072108000f0a91240841500340c001d012005d211580004000e00506102d80d20070490140101505866110b00150031403000004941c103100094641205828240d0213422030b0301118603107005035081c0710b80b82c88002d000380980e00414100c19110000b110070302001c40401c05e01950447c121100500c1c000c00f000c0c0d030781c0781c8030300c402ca403141352030400102c0114031107940512103000204480d207001290601c4030050700c25844142c4c0d05550314490800081e0408c108860050300d4200600e480315 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 752621735 1250 752620485 752620489
    0x3030825051206030d0f0c150204060e0102011116030c03020a080a090602190206090402160f1b090c0234060e01030b01080f06090919030e09011706010905070c0818 72
    0x40003501d480d00030390101083e1700c0201d4001c0c0248440740214a008100083c940c1817030381d0340004101d414810184000340204010780d010269240c1e00c0402c1c0c00902202100c40c45201e4284285041400100802103801000a2141030f01d007181c0c500a2045800c1c6100c1c90300c039803125038450f51041c0c0100c1c10f40c0381e00f00421901800284081c0082094010180d9002e07004286144108044184196400141806103040920700404160707080741400c2c6040403103151100c3c8a254025400100a0200300c0001e1307208614000e659410100f60b007d0011740c1e407008800f1a121440d007805040171250f5030880b46005036074440100040203543d5890118150b000005022540b1001c4102d04001500b0200050501e82031242c58000390f0507201815170b65a006029410b00b00d41e00c0e40c2ca155501c0824458060603800100035202c400100c03a5030032940d0380d81c80d03a04407450f002d0130800d03032a800c0340c401048515155400242d000b030540c2090b0740600c9076a0344000b1140c1c0300a29000b104a09101c1c0034540b4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 752622985 1250 752621735 752621767
    0x51210060e070e01081b0a0314010803070c0503030412030c0804031202070e0a060b030612071e151d010e01020c10270b1c021b15060603060a0303082505 67
    0x10400c2c2400c0c44941403080c1e00006d0090f00c10001d01c00c0d07200000e00980494403a50048800e00b40c00c0c102002d480d41c461050903160b5100441c1079075150001000410f071843c0200c101c90440701c10700c0340c400f80010141d805481034264003500351005007040c230000010900e40c048410129501d83d01415803a420044014035950029005648aa140040031f00c0f20304081c104603034000342c1c1250320000c0081614081d074540001ea4000014200114a00c003a0261504070302c031081d1808405100003040b29001c04440007284204d2a42440d80341144004840d4001c400c0c0342c01482042c8140c9800701402c0340403074035080020036818009001600302001804c07541400b016800349120000c1c11251814400700b845016000003031480e2080c92000e003141a403164110380f6650040844003100107607180e510364036072051a082400741c4043e03c0000d0014600842100d21a590042001000c02d0464500b103841c2c80000380107490a900f0440700c0120b9074640200241da0303030b046540b02551601110b0400c201 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 752624235 1250 752622985 752623007
    0x5070503040320072d081c030506090411030c040612060b0a0302010512090718020a020f0105040305041202030a080d02210f011a130611070e0907051210060e07 70
    0x3061142c011030441d00c0700860352100f1143c0c0007516800c240032060080c0e1800000340081410341d00e40c0417000504400c0031600c4c040c001c0707510569440d20140440c054060714801c81e40306521051540004001601005103a41090405811120070203003600109040b500b16410002044600019400c02c215003406044141c0301c06946640e8540c0c0f80d50f002810500840b0503000c2c03d17a02150004102e02010082c50008043c00e026007100c0000d4051443c000b5482004a10f0050040e1040c45100c95014002e1a020759810303a00e0300d1405240800354618401400800c0740d05016503003605020a402e00701520310040b020f440142e4481c202400b60310613400c107007010300580c2e0b042401c2001103540350241d5030441b08040802c9555002d0042c5082d40f9104103030350b850040c840d0002c0401d4180c1e1290518035003c0707104085584c03c07a241c00b8144240d0714202d41802c80d603803001500380711908210030310307002d014401c804171800781109150020135a0610b801c0f4004254040040111a0b03a0281c0c107021 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 752625485 1250 752624235 752624267
    0x7140f090a0e1014060301030b09280611130501030e0f03070804170d0e0f1f12061e05060c0307150504020102010f050f0f040c081f050a0b060304030e040609050705030403 75
    0x6840d101312400709207203010510024045084a2000415a0100380090ba4409650005513200030002019218080010002c1034070542e03c5c0c2107001c0e1400d40780c0d0045910040d440c41c1c000300c27130070b150000440c050035510303520380524003460180e007000b000d00f0009000d00301e204d000b50700c0e15542480980341c0d201c2c14110400c81d00d580322025000c54590444d07a1031a40030300c01c2d5000383c90360910401045002251000104040800c80c1c00c64410903400706034421a401006414001540c2d00c00c0305003040d280c40300a00d500c001004504000c185020001400008140015a81070095586a00520500400c0348091a54072002040210f60342889105a0b60a00c0b0340c04100c20700b0900a8019440d03002041d0040200c0c2c0007000c070301440360100d030f800000c0c020402124080c11400c80c4082a0a54001e5602082424540415107005030f6000d0800110340c0a052182559586e0300d04446180d030420300315401959079a008034003680c0500a943c440c1c1071980760903039641018a8010714148141d03040032 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 752626735 1250 752625485 752625509
    0xf0315050615031e090d020714010e190e04080403140d0c020f010905041503170403021807030f090b0103051005090c01050715020c0a0302060c0307140f090a0e10 71
    0xc02596204120031402810403085070b5100e0ba03400d02c070000420420110138010702201d10400005240000d0b41c450010000d41c00e5074807003581c610171502c04800220039640824220401151281081c2c47c009410b80010348600080a90f5a00c01403040282681c0541c2d00d4800081c0900134020400000071004484900034168900407640081030010101c0c8000c3c81410040110110f50f84180840c2c800b40c04002c0081025000700c0d01d003040c4045252200311080c40c411030034061154903072000c0e0ba044a401620624800071140300402c85040000c20f0441890760310008103003441017600c207000c00203205402043d00c3d5411804c100c1d103080440340d006080142070504210009601051898122200b800c255032940e00614094038050041901d022069101040d0300f40a1100040c4400043d4040e40035240d16403035410440f100d0b440110760080100d0b0703070210041c0d403191845009040120b0803610711800c0640c0d490000c0c1d01160b0543c881e10710070390020140000e42a031000860000e0071020581 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 752627985 1250 752626735 752626741
    0xa0308070807020307020d020402130e0a0b2205220305270f012f030301050a0501180509180109060b0325030f110901030506040b0604141308040f0f031505 68
    0x25500e05c981c000003030182d010b00d1034040844d05c5540643e080140800382c1145001d0300c50045031411102152440c0c1003a09201140c4c90782d0802c110105032000d0b0200090381e02440641b4140003030300015090809201c2c5032100c291170030000c28120007201344281d840c241d40301e0450782c03000300c06010342d010310301307800320300e58101c0d000e6607d214180744c902e0b400703080c80184808140d0030070050051107807050240000c412080701071010040001c40c16910b046900101c89905c0fa00111140c00800400050003218450700b0300107803a0081c4400e038041e1000c00050340c0c050b0540211800d507882050f046840030b4458096501a281c240100144c085440e8002c403030540c00c0e85803003094400244000340a1070303041e80e4000c044c01015481103030512006000200103580d20b141966540404480030b44581c006080842c1c00f900c1d007405540d00b110314040c110b4007a41c540002d10203120300441380032120f002081000240790603440500000070b140044100b64503a1035410301000e1003000b400040f40140c90700c810 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 752629235 1250 752627985 752627987
    0x306050904030305220309080715080408090a03082a0d210e0a08040e010501050301030b070e13051302030c100801230409080901110a030207050103230103050a0308070807 75
    0x6050790090305490007161640300d2074010360748561300c07003a400307901c1c24a6040c10f400d050b0030130051000c44540000700ca0300156a00b482108290100420400190110001c070303000c00c0c90800a020143c5004140300d00860f600c0e03480620319400805807000d280e080c0d45106c1c1c0d0700100b0244941c980c0005002400404165034002024940120500b00540d88120348141c1a0f041a601c000326200e1f2542c11200303444040d0403c02c1003a0018800c8106030003a400020445521980603281241e51080ca0303041c1c070792a00c0301c064500c140c804480580248807003907d0b2402001c0b500840c5e0044010752034000c0303102014010300d800c10651001c40c0d07000720050380d215260076620030100b40c1182c003a00c034100521050981c2e0f803010800f20011159106013042c45800910010300e00500500209032100e10034200102c04032900c07011803120207400758114060401407540280c1000b4603c811015424110101305074248075a04c0007a00290b500c2c2d40852900360030950010380d80d036004119030900254034904100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 752630485 1250 752629235 752629249
    0xe0f0d02010e060a03060e0c2d0a050a033c0228170f24010801140a0506030a02190c120c080f030f04060c140f03060a08100219030605 59
    0x18410f4041c100000381d441945109034040805801d03034003200b80050070140304010a5401987c221b42c0100c0300d00300d44c460300311501c4200990086c950102941031060005040d601c3d07070400f1043d4000e05032101480826000c003a0010b88012003c1c0c04040b50040c424403140d9046520b0b5488e04482c2481045005961350120841c1c1c60000e0010300081c202c180d113628129003e1805170b8484080c04051001d001000820700032a07489882405080f0311814503102554006000400c1c049001c10801001801038a0f0020150300c126000502140c0180d50b0b2000403501c03543c4110341d9448820350105800415290700140e403000c0c00100d2510412000e000d4480c104501c90b00c030f602405101e1030006240c10030200200b0b0b1030014040904203500e030b2800000d08802500c01310340c1160114078045020916a00400042e1284a501c41541341817110090141c445584090500c0c1e41c01783c42d00b400000c0c008420855001411900200540c507450701207000f40d0751900069900c0f0605042081c00e020301d45a0385 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 752631735 1250 752630485 752630507
    0x310080307060915061427070e01030506010e130e01021605010203010f0603020c07141c2a0807090b060c0102040803040e0604090803070507061b090824012303010c0e0f0d0201 77
    0x4480c40d1a0b070040e007540010b1f80b088138682045080d0b001080051041d040001050150401e8070144401d54071030f4011984155023b0000c1c1d070182503000c1d00e8440f0070203944000c0d440368071000010324081d2a50000ac1c0c007651508000c807003e0b900000184280a40a040e95008001905056040058815510f5150300103400386196020034038062180d41e50740d04101010800c04010142d12004c028200500811012001810b100c0540102d0000c00c1010600301d0040b40c1040018103803450400000d54007815508002d2603028006201c0d000c0c02c0c9000303100400c0104011801165510b242c484415500b1000401c4148103925101241d4041990f8200712a40220146080d41d03490741149000340081160511410611440300d01000c007050b0042e0100099072290300c115030f614100e03603254101269510781410f07503000c19130004100d042d65249245900000000880c904200d00e803010a084902c0e1510010000303107022112070250a01030203074052514269044601c0400980020748510000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 752632985 1250 752631735 752631739
    0x181815040c0b1804060f051e0102210906030a05060a0801021e03180a030905120102090f0d0201230d0c0e010e270108010c02070f060e010503100803070609150614 71
    0x1d0b40043c0d07100510810208490700500810032a512180740030141c2060b400f03014020307010707104401d55801517110a400822016401001c80e40c1503ca05214204c44207280d42c403d680040c48240c1169440340051441000b280034001480d2922008204480310b05034014100b992040108004030440f080c202c51240a00051580c0e80703403924019a4040007800d0040d4815000c7c46400c003080692201103031080354422141d800040c01d5040019080b4804c03800c242e507001076549034840403410a0280085c2690050601c128010310581a8501d43d442c051052a420040051000d07000f49481c81080c4544407107213003140c2d42d400000000380c0110201195140725900c030b400450301904a010449441c200340031403032500c6580d1061018042d000020041000d405403020100b50f03150400360010840e4259079945404115400044da2154405464012040340039000441c48150030001004000e2003450b0020301c1d5201418485580c0c035400040391003260806404000c00303100c524440c03901c1842 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 752634235 1250 752632985 752632987
    0xe040803060f030109031d190513090b0901051b0c030a03090503041505030123060d020918090309040608030f07030e0409050610030b01061e0c02181815040c0b 70
    0x551000611110541040b0560541c00c04811104056002400da602003180d4200ca5400c001c00074104a06590304e04165842c500599404200030720304101040d1010b458003200281c0386a5a0f160300c1c0d84904119650411340c0c0d1a0801d015029580a1040d080c60f10080d50b0b56040074406098103490344038032b8809404040e01d80d002d810900c00e0900484004008044180d100c81d00714106c050101e0300309208441c180000e061002d40f003000d103201c042c1c140e880300070241c038900744000c900f2074025080300e03111540010819a10180c2809a075031128011200c1d80c00440d1030b5884070040006841603a042070300d6230b40050104c0040010810282e41880e90305041a150030480100490300030003210720003500c03034440c002c10f20003501c015817222020307030340513480744c08241ea282c040c1950401a02200045841e1801034010030082c4180095203800d84001d00503001e90000d4020010a41c1c0705464801c00000c01c0160105410001c11041c0038490700314450241d607252039120103000305028030032900b80c540 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 752635485 1250 752634235 752634241
    0xf060411040b1906030b090a0204060f1d0d0f0b091618111303170406080105060c010e06010305010b0a09050903041e0806070c0209010e25020a150c030c090e040803 72
    0x914803851001c19510745442c22012a42c0e0134000b0040c222000c449800303100700c480440d000700864001c03901550020b4460b216007a1000c80201c0b4101101910300e41154004416001603688640ea650341d2640600b0617005c41103000d0402100714200508203444a80c080b51146940c014202840801ca8140e000243c42d1808405054806450704020410b0f195034002007440c50148480346040699024036906d2600784101c0380151514426402020701107000400104140c0c03400300000d06110f10345d04000300303c030b8003a640041c0c07918074280c10840c0e00740d450b01c0d20000d0700d0620401d101c00500403010305028506014003601d0300c0784298050580680700b501190307147d0103101c01c400710003004820111413040c540718030b000380002541c0d0000c9124070f645400000e0318040351030449014000410700c40d0030802d0810b84088201c0b0b560a850002e5005840000c008141d00f002c1d204141000e10402044404403a400102181e11040c0d21205014840e0300500c444407801140d21383c82948882c1255882e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 752636735 1250 752635485 752635489
    0x151403062101091b03050c0d0503030a0506010c0615141503011703040807080f010c1d0d1103031305030f0a050d0305090c120a030e061c09020d0606080a050f060411040b 74
    0xd1165000744c40700805401110513200081d60741e40c02c503409042a03814184c094000c002e4442c00c442d801415580c800e0011869095507075000ca5001401410007441382d103aa5a540800d682142d07010010441718003100300b08408100f55400140002295a040031070181800400140418003482184500308483c2803181b40f030400c00c44000e084404100c500007036480300b109079940011801c0b010254280351a0161042c05000360440001d80d505040031201e01b4041440310b054000c4000b03480c4500a80708600040e00c0a0006009542c400401c40c5040c40c100b5041c0b43c41c0c030031000131104040c3d01855203500810804110900d1041c41d51501041e40d403a80030f02a45807a070b541742c0b0b0b294442002c07410041004c0b0300013001c03c041442600c0d8500403032001c2c8104045070180c0080715298030050484004d811086078415500544000c0a2005201c0142c50354030407500180c000300366562000c0324020601501308a0700c00010010b0740285981d00d065501c204564011008003030140da1500103000307040d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 752637985 1250 752636735 752636741
    0x90b031008010204030c0602010c0309031409010c0b1611070b090d0f12081501020721141b0a0e040213050402060d090c05040617070312110106151403062101 69
    0x500c401d000035901c8507120b0420659071142803050a001d90710784000904078a019025244606815031580d0410b900d103561070841039404031b01c0240c104610040c1c1c1c0400a11801c03001c40c0503080d80400d041807000000f1024201d00100311111400f0f90040c4000c119003103240303086411a9a0640351062483c3c8545400940454000001403150541c4800701001c5640000c1651185000c2e040b403000c1c4080341401603840c0d000c240070700b00300f4100000343c1140111008009070101c500c6104030115110100d44c070305083c6a10041d80c0303100c010781c4028039500d0b498a502d112014040c0d00001503424209580080c0d0001940088030600c1034032000000c055641d801c06840c030502c0d200c0300a12003043d03d8949541d01c02158080d0030321441c03920801144a150010b103200d014040d02000308001410f50b1140b600380c103c1071002c4000c10940034040380307600f0020300a00380148410b0341095022145000c000d4948032110190400c000d20500402005580300700a4038110b142141000c168904018041405 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 752639235 1250 752637985 752637989
    0x4050c03070b131a070c0915090504020d140a02030f0c0a1508040f0f150e0d0905030c04050a23010807050d0f02010807230702031011030103110a030b09010506090703020406090b0310 80
    0x201c40c0300f440c800640341101d90011364400010044123598540c8540c000d0040341d000750b80107900b058101c10030000080314224810602c20000c0c00701e500168090340001c0c501075103010700e03041680052a10403954145005d0321000381440c009081082c03010100f008000d07080050019101d08207036001c18081c418240c1d00c00ba5002d070041c0301c080c0c4a0542d00042c00c054280e5000c8a01d09108404401c0d00c880d02c500013103401d540300140a454240b1a4404005c05040007405003450307c2c0d0b403602c000b860344c46010b03500c0d00f92012403980541950314041c0c506040c1506e55004600800c01c0d40c00c0680004e0804400c000c801750709007048515034031303145400c5a581c5035040120151035140703c1c1803111050301c207016114113403084041310a9034040b100c003c003c0e9000043d40c8415880c06000603c0051000344240000340c1000d070806980665903180c41140708019a0400000d9545409000c004d00303150322000c0d80000d00e420150315151900303d00416005882c404c08017030301c038044045210f2095907505000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 752640485 1250 752639235 752639243
    0x207052107061d1006060207090f020c19120201051504020a0e03010e070302030f0d2c0603040b0f15130e100c0513060905060403080a1704050c03070b131a07 69
    0x210381544010407030f030201d0a03206100b41500c00e1000d1012880258007030301054078801e40c0504009850103034000082e03c40920941100e82d020712012481c184100500010982c0c010300d0741445000b14140308a0ba00d0325a0040000c42e410601000b03003015510005240c10305c4190340041c0d603944500703000c4030000c0b0103410480d4103509084501c100384074001442c03803e403402101926407103082e0600741a5078200303010941010800c00b5400104440418445e83e4010301c9452500580d8010880043d40c9540100d404842c111108010f0040050b101b8500a030300c00c820383c01d8510449442030000341c50f030301c070b41d40861046511015400341d803c90a2080320842c2080c600140600701c09040050076a820100c0b0109884451400015280f485600c005045a4018141620302420740d12940d0440c1d0100350755405015514012001001110f2035040c80785000e84060400722000300300301800d20f841c03a400204000300500080001c00d00c0d08003801c045800b0120000540f425185e40c940c9213001c0d4a1000e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 752641735 1250 752640485 752640491
    0x50714030402031e0319050301180c020f01090b1b03061e01030b0619020c090c0f0d110c07060f0f170403111b04060605070b0406110c07180b0301020705210706 70
    0x10130704600201905074194071448442d80007220307002c2118507000910807105044145800c900e05860550b01c2000400c40f50b105030360f20425820480c5081d0703014144100e61340b880d120108038061956510000c2c04118582c961450342c142040000d078000304d03000c4d5a5203400da00070324800c4a6802544407200000b0003801054a4402025040440746c103515640005030141001c050301c0c2c0d2410f03220b00c601c50182d001c22107080800c4200b09503800e0f000303200c00c5084940c1c1c0e5006030754107603100005450807001e1131000308a254201140200f01d45d80440720b003c103001c07007040070304005504014903480700146010903641503079076401d0032640d031f101282000c1c046000e03c9a540c8401c1540d20a030030034251090741c090041c1695000200c990740305542010301041d442c1804500040c141da013080902407290643e0909001090b45221308081e80c6502c0b03442a0100b01240407218201030007012441e4074224021405d1000340c0c1c4500fa12448460740b01c0440004e42201d09100500c0c10080d20700450b0070460030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 752642985 1250 752641735 752641783
    0x1b060c0a060207060c02070302130203071b050c031506060702061c0e0601030501060501022b0e10110606090f060108040f080403060605120a050304140102031c06031505071403040203 80
    0x61002940040e20035604c96003003101e014607642c00000c4800442e5030107403a8801d02c0f07074000d000600035000501428100540202c1d22300800d950310146d80034040c003802c00f61003042140c4081510b8000c44180801c841c021101c00c000301991020141d8084076010f07640c1b950b5480c81810041028814400d240919a2400122340c4d452a0b000410034141c900c110020091a5158030040e60303100b81c0407a111010b88010070580f0b45000c034203100100e80d4107a60601c0c91504050000140e44c01c149102c0e420000741641151044401c0304025013074200d641030b01c220401e400c0009202e00700c00002080941800180c002103420000340c008201c04440e00030400d0341d215034891a0a001400b000d00c1458464480505c0000c4694000304074500b1081d0301400651a0502d05900800b960780004405070540c001440314610007054090180d09400c110791000030885d0652400c13080303444008800e1901a0b141004001d841c98000301408584883c40c210140c481d5203620001c0d18150701c0c90380444c541c03250081e207 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 752644235 1250 752642985 752642993
    0xb01120204141e0f010f112e06030f02040504021309060204090507110c040b030705280812030c030402120a060b011407051207060e03030c04080705010804051b060c0a 73
    0x1040b5140c01100c09007200480b000d00c504040410381080341d407091030040c248659600600ca6411405032074140500e0351000c00031124104080d540e01100c5003042443d80509440554038a0802102c9420042004906549400c2584141c8441c002d01840e65078002c5810f65a45000d1074500a00900b000d000c50140307807500e1070180d00300740304c2e1100e00c60800f4080350100380240c07055580e2080d032034018801207031404200720140c0406060070360035005005010034580c442c1240700c4041e55106901c21107005030842a1154401140d204071602d4004a0400b2002c2c500c00e07089070740014000141a07203070348482c00040e11703e11402024551900c5450003800070032100d81c200040c40c0350240c0b248403100cd065029100d00b445007440c020a02d81254203e64070000c0881c0c0a002414011000000e030f000410300600e146a0042c0c42404418402050801140c1c50811504c4054082813a110006080c1682c80550303681c0c081507040410f410010904059455010558001e83d090360304552031640c140c14 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 752645485 1250 752644235 752644259
    0x602010905070608060d200d110f0a080a0605220b071202160b090c030f1c1d1c05190c08010204031703130b070e010809010b060d0b01120204 62
    0x2104071050300460328001907040c01380c1025489000040c0c03140100d402c03030340d4450400880c0548900030301c82e00643c0810f690b8540b80300503000d00303106404410b40440700350100410611504050b500c42c1c161050140003101c8045000c1e5080c0c0e500400210b205d4842042e820302e4911420881c141098107100c031002885846003a9a00030000c0d500d1f0072624002c0d030441503007a03210b800d0701e1160307080024065100003030010700003650010400047d9951402104002400c100307028070560107903071001c0c0c50706052000c1c08202c00209552030420500b400101100b00c0828005800c000b4429000b04a080b0404080c0d0105100e10a0f80041902d08046a503000c401582c9500c00d400e8503000128240802c900105100b103a00707a82d0030a040403840c0e846400040d4036275000400c40c5940350f46101c100e5000425500010303024564a44860340d44059005c001442c08400401e085c00720380c10880241e105444120482e040c40110680114019801000581e440321088140ca084980300140c005031581140d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 752646735 1250 752645485 752645501
    0x603150515030c0a0528140102061608060d0f060c020f10110f1606181e030c03050c030403140f0f030403031b0611030403032a08010b0309030c0601060201 68
    0x2514100d05040200300b415a03620302c01c030290742c04c031185200520140c0380c0405c0040302c10003003c000a20346401500000c02d440f1207980b00e038141245000f6042031968042c01000d500445204804107071940c000c4008100d510003504040c052001900140d0911038043c680f21038494201c0b100744880c00784503a00940e203940000109005e80103910a035241c20b90240a0802407021a00800381401d0040399420000da04c24140c50408043d07101c141e400144e07080c011a0301d00c3c4010a44a40428031a0600700305c80498101c00c940e29480d80205040004d40000304058201c0e09880c1950b11403500403032141c558411904081c02e01440303074810044c3c0ca1000100c00c6015000780301514000c4440123003a079500c0c000e9020040204102000c4000c2c03280182c3c0f0784c10f00c5030b8020100401c0301108406501d40340d40c42504e0070340c00207440c0c0007144110200c0900245298000140503c255101100000c00014040c041e8074280840000802c02c4540100240c0e140d0441e0b0380260382c21543d4901c0e0203402000b0031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 752647985 1250 752646735 752646751
    0x3020705030d050406140904020c0a06020901090909081b010b0414150109230a03080c0102130e16030509010e011506091a0a030c030e06071d03030f0a050307020106031505 75
    0x40c00a2180d0a00c00c205031130885d400c0c1d4803400490780000007406445d030040a0010b40055003844034030329010042040a9481e40a00c03030050b641d85010000601914464208421140c1010742003400501500304661401e80c115014503040ca404106003800b615010003855030103070412503460341446100c0c100038011118050901516011040199a24a40c2d403144909001c0301c29401040081880b50340c003043d0400410884006480e580c0f80710054000d21b0094880341e501083c80004c0121031070046024016140074081030b840c005004c801c1c04074240e4810000c040c0c5500100749105801d401050f0400131440085c0510410300340d82d41020882c41c840e600001d0a9036100003503568410a20005442da69844030f8034084d85030401364040c2c801a2001000c16581d12000e04844000b40841e034054580c0e951904000813990081c21711142e000e039403071071182d04104040d0b11360700b6221040360340d40712036814110b4803540c0d005c0701a401050182e0010300352001d0303100c01601c9440c282d84007031701c14201 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 752649235 1250 752647985 752647993
    0x20315010e0a03023d020a26030103120e120c0d14030a0e090a060807061b061b02011406060406111002030a0b01110a05101505150403060615090513020f070302070503 73
    0x180c24048003000c46017940c10005a04840c0c506004034002d400920245003a01d1580c05d03003000d40d500c0304105030384240d0054804030010490345810607445016010103540031500d503840c40209101d0f450f212504034200d02d118403400f0254000f00003507100c2c2c40c421403590704c0c25203440d1031401e030001e00100000341c030491280d10090001084020b40c0e11440c41600c409800a250807803e11405450311041c1064003606007450107030420001d00c03d400b0742000100005054180450100f90103425903c042d0120719848100c1010480c09884003020382c0c084806138030305100e5a520b10040e240c20101d03c202180c0c0e500e4000000c000001c2543d4014981e0341000303a03913001c2008640c1e019140c480b0380c5940000c00d2034100310064a06460590060780a040100320144540317503803030f0000341464000c0c050b0303444500404070382001400b140d0310420b00240224542c0e0914411901c0004004140a01880788550741107115224012010ba0640b102141c15030429a9103103410f081c06565581c2902c18503100c2e101d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 752650485 1250 752649235 752649319
    0x60a0b1516060c111002160f0606033c1103060a0222031a09011b2105060607030309111815030d120207050c0a060c110301020315010e0a0302 62
    0x304c100340240c0381c644a01c0143c072444c150840d000d000b0354095003889161103004e00682001c1a085042e2000e80c900c202c0300020024518035000400c01e400c048001c6103410200c0483d0301c0c1100c41411346566044582d0aa03800905070314010714241c4c000c125158041c4100004c200f0960540e90003400106003d500c03401c6080c802d9130103211186442d002c002d03c0c0072258181039594014080c112600000b00b000041618400c107140d01140500104a000003c0d0031100114031000c405401100c20100d00a014003a524000b804200a4801c008008041603650030790718050141440d0710f1303d01c44100900c074245110755117001011070003081c0c8120990f10750560b11982e4a1030009600e4060b03a8581c1c0b5200030b008106400b010094000c0d81040c2e03158040c3c00c440c500301340d454a0602c005400107441d10700d044016403c00529503c0828a0307035010380e01c10801d01002203503100035008400400d280035a1440040801b10701044400e0b40025040035a603003041d226a940c02d00c41034030f03401a26505450100f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 752651735 1250 752650485 752650487
    0x221160b0a0f0c0f0516021f1101020403030c02010c0602130f0311040519021b190c0603050402090a05191a0f0607080702090c04030f05010b0108010512060a0b1516060c 74
    0x2d080d100e0102c01013071182101c4581d850044c409007900a5a69a00345d03038500541e008112100e1420880707480e0020b070400800f050f40c0c0c2060f41041c400320444002c508140c1199000f80c08400c1e40306020b814080e40034031480400130250111510008080145286150b441000030090891404200c1c1c1c911040952046d10741003907c115071081c502d40c0c40d90610b6560110407a03000350322140224800c25a003a41442070341d0030403c18000102010b1a010b82c429500303003080c3c1079050035904100200b60401c402e000150780c0d640b03030441d0080c0e1040c10006260700e4503002203d00d0b10440019903255410710305940302a0075040d1012811403020b07540c46c139510a03030070200403041c42042001802d030300c41804800058188032118603071041c2d8000300c507464a91079803246406c03801c080104540341d0303445000c45100303540c0c0845000e004020544040b00c07813440034007056468410040a0b101046d40e80c0e942c1e59050f41c2c0f050031400343d10341d040c0041a96182085c1e580e031400c1020744001d658003420114035601c00d07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 752652985 1250 752651735 752651741
    0x3030e090c07200a0f0f090605060705070626070f08090f060c0a02160306090614010e150a171e03030402011407020a17150106030209010221160b0a0f 66
    0x80c3d01060014201d40c075040303200764a14603080c41ca81c000d6640392010912081180c2c0b420041e01a40111840d0107141c40da9404c103035000f036080b0078002c000501040000801c0015400d00b5642c081c10b000035a108032400c03c81502c1110500c1c2003110b1000340920511540001000800801d00e5840d5103880d40d6440d411556000418041d098a6100c40005610b50050001030016800244155107011064005207540034043c0d41040d07501903558801709082156600c60900759900040c149407080d8504111090984001842304589064107088806503a8480342007201400c104807410b06203034007000c581c955a811002492488001e84a9648440540081500e2040340d0503522040d45c9540300070825080e40182c03a0803070300502d064101007910341c04010704c9800c60f1070010060210405960303a074000342d60b0680c0080e0078180304210045150341d01140c0c1e60744030000700c0e04005112000d0200034401e481040603684007012965031000c10445000541030041c441140309103d1402912420412 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 752654235 1250 752652985 752652997
    0x7120203041508040602070b010e090c01080402100e0f092701052205100921170a0b1201020705010c09080c0105070b06031e0606030d0504080a1106070c03030e090c 72
    0xc0348041e2002e40c0b0036140300f00d41c941d610901c102c00140c2844125507030380c0c042540a03000041580814003c00c08404410008101c4c203a00074a0403500c1400c094011615600c414aa440704214910080a045403611310b21074a600700f001e8101078052400c28845c00302002c3c4c5080a514801203400c040d400e88a0500a00d070069500400c07241c11500ca402d2444004000c00790215854013800004000c0310581d4412204001d015030350802c40d140d2011403124080200301e4509c1e0600c14110f00c50030309450a04a020741c8440c0105001860021280c0080c1100c8500e48610703840350b00005600c01081410341140c0d40207803181c0c40b89a416520740504a80f2030f000e0b0a0070320300107101031046502055461180715040300f4040e0594551340201c80c44450030b50400c944c0c800c0254030100a0107840d060812901c5103a20041c90990f0600d03090486064880740c042d00c01070150070442a80302810743d83c0c0000c507a03030540d0041401041c03a540c0d04e80034041c07201d545003081c4203401050000e000c0040d250300b00d1344 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 752655485 1250 752654235 752654249
    0x60a0e040b0604020a12111308010e0709150305070b130506040e130f0209091b0111030409020a17010e0405070501050f0304060c090b0d0204050405100513091a0c0712020304 76
    0x7642d40d44014480250454510b141c1044522070304440380c0b1503584125010341481d10034240e5642c2100e030050241c00c109074406081607140c21585a10003c0c0464000c003a507980c0100451151a01c00c555000d090940d0809003c0740142c0301c0c0000c1442c421030090001080305040403205036525410003c0034000c0c0c0c456050f480401000007040001442c900060961088120076840342080d00850850f080464940100f0ba000b2a8800011982c48592007801c0342d003440c14180c030060b850900c64a0340150702c152100d281d00801c004250703a00030305292440c0e820440a00c030503076944040d50071081c1000d80f0156141e001f06080445c1c50b51255044a0803511840d0501c0e1858440303503200001004043c03666010015684400300d0008c407c00e004018151700004096203450510040000311980030340030740e0703800380347c00410045d40c0c5640c1040042030184c484005449138860801c0c0e0314040c503910814519031802d03001c02c060b44d00c5400c080c00100b40030350741801c016410540b080c1d80d0313032080b805504 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 752656735 1250 752655485 752655503
    0x108070609080a0b04052d010f110435030a091d15130e1e240c16140d03050c04050d05030702060c1524060c010b03070608060a0e04 58
    0x1802050b9403e04e01500203109078116031001c414060401516800603042c035003841d41c04008034814160034080e4000314010144100204401010b0081440c415841450300c0c81ca04101800c8007070510810080010011100440d08050784010990700c0340e00031702c034403000300706034000100704010142c005030850180c200d06007506403a1410074200181c0c20400b0280d1000d80001481c44500c1e40d4020300c000100308000900c03c190005840081901c151011807481d07602a41d154140350398905281d1002c454421182c50347d944461041c040c492103002c0b0a0b0401281c5038080f0001c00c1103016038100040c8000b801d86494003c03401e4220165181610440303591403040c4414841c42c6040c001001915115008491802c9400e901081440d0403800c2d401e0141c0c1c0140094007102c00e52540740716400300400510460880b40301c1c032100c0c4400c0ca0010200e0060f00702040415500c002540201d58081d0014100d4403040d545d07800c000c00321402190482d01030115028001403c2102c0040a405070f98008212 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 752657985 1250 752656735 752656753
    0x1090b060307442e02030c07030809070b22060f02070303120213140111030c0d08040c090203090106150f02100207020103110a0f1b020913051204060305010807060908 73
    0x45103001081240400e41e00355008000c805401d04000822035000381d200744500403110f600303001c10703241c11200c03003011413900400402014281ea01c0490380d10650604001d03001d9240c5110461908400303411017270100c40001006080c442c0082c00100342505032068040610361603140031034040c03803c4c0c81150b005d41d02030070003480004e000303480c50581d01d402c00c44014142045a2041030f0881b40d107602024481d65501440c50f80c42d40d10020202e40000307444010340c94418041403c80d0343e2900c040310001004015004502004a20341c01b4000600d52803805540728202260381d40c0c02008a4403500f40c100050440101c295405400c001521900940241032241040550b8001030350000303a00300c0c101592881c1007140741820b00090308202030180c3c2d94540030407848001514002e41010500e41300320099518000590b108003005a000782d01c040141d036954158540a4500019803000b4120314038041004900c240e403551055040f02c90001c100d605450b5600000c3d60440308501030400c180d000036480c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 752659235 1250 752657985 752658059
    0x120503101a070201122904050a0207030914150a02010b04241a191e0813030e040b0307091a04060e1311041407030506090c04230301090b060307 63
    0x200c110400d0a01d4041002d161200740ea4000c60761403200c052006c10502c490500300e04091084c20703440b081c51042103151084c1030b00c01034400405031055142203242c00c80a0001034480000742c407112000c1707507042e80c3c03540a40e000c068040c10250307826a00551030040c0854081d241c0c00c0803002c0d514840407a58070700301c2c1800542c3d10013aa10340b400c80000c50741003050810150311038411407441482541e48204580350700c048099104c841040768810025a102402071204c01800e07142062a414100752003003140100210340a000941015035050040c000c00142d505002e802103a4200c098420702e0044008003000c001c1140c05070300440c0d042c05441c2d80011107208105201502d00d42c06914000175040c0310600140544501d00a01694000300000b88000d4a8060103034540003001155004802d203410b400c000c040f401240b0030035040c4841c0040032165214a000420506031380a002444620241d09085101c018103840460217032003001d800152000c004030a100072107030b40c0c2c9c80c0b0b414034440480d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 752660485 1250 752659235 752659247
    0x6140c0a0e12030a0c1e05030a21060308041508040c0e04020d080415080106030b0310020a1205090601080c030a0506010b0906040801180224030103020d0609120503101a070201 77
    0xd1035034115503078044203040510100040c080c01d13203140e9100f25070030440341341c55001c04108681d50420748011802441c002200031040e104c01503860701d00319038610885605081c0c00d074034001403404a42d10348031010092000c02c20003481070705d4a04030351028040c8120301c1280d812200b16400303005607040f50030501c01044a02525508540000c284803111542274461900e40c0c1c1c017580c810001043d600c0c1140641c590002101030040405040c2042007842c0900440e450b0312614403003607070f169400205849101c1c069560403034100c600402c104103625081944956070f100a0044a403148517440c08040280b80002ea0403d2403070b84407002c1c00d1180d280819403016900403416165000c542031001141c0384c0000d10616040401e404045440b9001a0043c48203502c602403d0451455003500c84030750146200080b00d04695065480c0441c2c1055030814000a0003030740402440c10001405034006581c0c09000303103020f4034008009508403540d0f400340d051180e00f03400e10305c08401d10a202d01000342d0701482c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 752661735 1250 752660485 752660507
    0x3b010e091308091305041a010b1b01020d0c03020403020a051207141503040f030f1e0c05030706050f0f010b0301050a0306020d1b02030c1608061b0c0105070503010306140c0a 76
    0x201c034203820444041c00013401004100c1816800554860400041c03181440c0d14102100f4002082c0003554140420390019100d2054820400540c00c2c01c1100c44010135030466035095201c40e0104901e103020407004001e5446448140e1051803861000300d02480c1607036020b0110f0f00e031103000342a007601d4660909000c018050042c0c0c1d00c040030000e1418508a240000c40c030070b03031050301c0943c0000c0c298500a00403003a1070800c28204410038040c0301c681840313800e00811800c440d08106510521600d0300520710700c1750900041c02c0508200901041caa03210502501444800741c40403110381c3c07154401e40070750000340308103980b1031310071081040171914960041c03c01c203080743c0c004100c0ea540f40745051204405c4600c50001a440002c2041000109000781804002c4643d101081107244c007450955170703c0d020f00400f09886c00c1910150403081094101d03500101490b000740803030714202ca805030003a00300348802d41e606130500c1c1900c103888a140c540f42d8400c540c0002d0321802c04003420400c681064070341c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 752662985 1250 752661735 752661743
    0xc04020f040303140d061805090c0603071b15051006230a0302130602060a0e01061a0c03040f061d0d260c060f041a0115050a3b010e0913 60
    0x104002c1152103038501038200a007140645601594890001f55000c40d000100800c000d45c00400b070070b242c43e07a100300031a42c1140a07407803c00c801a801d489409001120304c0002060580c8401e006a10038a454004600c540c02041040d105c190b56804d003a62080800e030003400c4028040034864100c84041c4000e041d6241a41c500181056200c1603820104e2040b80c00110150f4481d070100001c004d0603024140c504031703101000f400403602d4002c0798046c1d070b10400309442035400003180044a02ca8200155402048100c41400d9415602c0b07074050000c507280205000d00500c00c482d07100c00780c01d0450806078145c2d40f00f03200c003154070745c006010003030300c612000a00b02070b1108100d0441c0c0c4240401c4101c0c05040c006c1400809401c10b8a0810f486207460048640310755140c02c0100443c0c40700450740c2c20580c0c2181000da0352030100c464103c6110005244240a14100c4130b03c03101c1071800c0101424907c1c401c9105041d031112041c0040d00c010400b540c030b090784200d162000403016a000009100c402d849 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 752664235 1250 752662985 752662987
    0x2a01060e090634090905061903080702120a03030c090603020f03060127140f0415120203010b040e0d02100b10051605030430110105090d020a170c04020f04030314 71
    0xb096030501030684000c3e200007000b0500030302c050b603040c0c4500d6404c10030841d00c0f03079404080495001d81d024014030014000342c0020842100755210300c1c03008051042002d09407a103201882c50045c00070f01d07410a0300400113036003c40c0803520034000d1003152120001c00d01d1060469440f00d0044030781050300403110070b10020490440f10b0301c0d126805408054440c0c3c1c10307050400070860f01480942d01c840302c400c03440740d0300f840c00c2420b581c0300240302802921000c804514942c07a50780007281c05060050803154101d0f02e81091000d1502d004940e0070048000c60342603c1100c100701c18220244c1e60100c0c840c81e4020405000111007501500c020100401d00c90750190101845454090542c0c1040d0b028440c0244118000d2080701e10380c540340d01c84c50204450440e0140b0701c58840843d461005452241481400608420942c0d030305150044031982c010300400e5101e840306107103034030320391441c1000400d48140401c1111034905802915251081202850b040c50300e5501e0460316180b04603600300400354 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 752665485 1250 752664235 752664301
    0xb0109050123210d030204061409010503060915060307030204030213060e070c0501110406020c10020609030d1a031f0b0f15034303150b0f2a01060e0906 67
    0x804e200e80044002541c600503102c0f4580708018080441d080400f48440c081000b11242580c0c004094030740024003900c1c0d054565450f6000c0011301002800500d41c000800b00c1042061507040d0001d000360b92007540c4880c1043e11001d101030942c1c1050141c0d90741240c1100005007101d1050100190450044001103502c0c00440035106659006410500040e0042d0712652a0350070004400004408548010b010f145807004000d41c4078045c0042031842282c0364180e03110342030011008940300b0741004054400b0b4540d01c01001e000c4007281034812034a6410b100b4070715028a0103c0a02c031000b4400350001600005403200c000107a44010070a00314841c403004080c4244400c1420200400072800c15102000118030301c0e40d0304044070f108803904150401060580e202501c2d86000101d9503850803070f03134481d2a600c01d9841107001e1700d0410f10320b9225511942490b07242103031402c80760010f110002c0005d25122403101c11003480489101d6100c0d4001e41c0071540080402c50040c0001d060310f204000c4043d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 752666735 1250 752665485 752665549
    0x160201090c08071a031b0307091805070801090b0603040b0901291305150d02060c01020708030402040c0c3512040311010501050f01030905010b0d0b0109050123 70
    0x80d41d40e04a10702c0b90340140c400307001c00e141801081040012001c0360f0307810b41c548031450800c5291030b12031580e1000d00c040085151180650b2115015000403100c0c02c1c058140e000c0108000c0c0401c4914000080c0102c00008220003948201e0240c000003a019600d1550303151540203040e00060031405096603540c180d400421034090741042c0f1030306c4401a40f1031801d10071007004a80c01450284244080c580030601c04c080000d80e084000c03107442641c5c81031119038680009070342c41c018222001002d500024024042201c44801075208905c01c039000c200381d415140e0116180d009242004204103030303450312280c0c04400c1c0c2c256081c00350f1036210303140000a040303c5007800640110200d9404400424240310406800811041900800c24001c0000e9032400300080d15500e21185024181540c0f410704034103115007900265480c060103001102540c1d201d1a00ca60402401d102d40500c00b880c040011410b030318000134481803414120321020400140d90200b050303541041e818440a81100e1084112103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 752667985 1250 752666735 752666753
    0x218090403082d040b130510020c07080109032102041505070212120a0c03020709060b0a17010e180102160c0503011104120321020708032d16020109 65
    0x940d1090b600c040b12420240c41c0c01e100481d00684141c0120014858040c2601d85500c2156003e50003240e85520340d01d030403071421241e02d45458040c00500a094031491103032102d40061560390340281c221503641d6964a103841c00c0352496400200080e000c6543d04210f0300d0901100004d01014850061900f55580300d801c10360b83c40c580301c101c04241c0125950f415840e000c410f00d04c0000501d40a4010015a00e00c1c070300540c4640030f848002c1c4400091000c007854420003920000e402031f0789c820043c00b61a07031003a0496400042c142c40011b21040c0c401840c455000b80301a040302c00350000c2d440d058031009180d04d0004404112440c0a40d400c4c4506a1401094883c41c40003a0080f038001c114182458249801d4034514102d12006c0c1c801000104501c081d056600f0f0301d02c9401d89084210090042010039402c0011111800b9090012440c44244400d000c0218001c1c0c800400c0080c0c00c0408241d842c00500b140221501214a540e0005000e800c040210500394410b51000081c00c3c40590390314040c0d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 752669235 1250 752667985 752667991
    0x180501170604090222090213090b01061209050105090312100e0a0902010c020d1b050a030218090a0b0a0213050927190c08010506030c0303041a090607080a200a06021809 74
    0x500c40c0c480440d06c1c203506044000c1a046240c0240c10b02051540c2d84402c0100d030418402c01040042e001ca2006003414903901c461070041d0b2000080c8454144004156500c2d0442e040c030380c43c851290001306201c420800100c5045401d00f00d008005030b07031509461001454883e005a06100d20b08070174800507507641c0d480300d50141c440c041d00301c0501c00801d2140760890050b04032030301134036005c2e2003030002d40d039001c1c000c19051400d404049015900d02d240c450506120203002413074103018200b40b000c000d14540203030010800b45486110007555031010060640b0040d120002030002069110081ea48185030000062048808030f41001c01c1217042070581d003200c68816141926110818400b2960030b00446401540842c01400101703c0c00d8000b82c5c40340f081e032003005a40004030101c0e41e183c03900402510482c00c0010803c64485100b030074420003a9020140007000104aa400450158038440d141400b0400c0e600003403d8040309590f901d8000c0d40407191002043d522000b00c40b9643e03407842003540c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 752670485 1250 752669235 752669299
    0xf07050f120403020705040c2c060304140c010f0f050a0e0603190f051510030b090a0902040b121c18171203010302060307030218101805011706040902 66
    0x100707610701401c0082c10300040c0c0e006a849203091840b88131302c1e00c0c1c0c007501080f0015040200c4211400c00c2d003882e00062841034403103641000d00482007000380a0134500d1204158004420b5524250880d03004440d02c0d404603004201140071560701c4660306210b10064049401c00342401c071003c454181c0085c1d02c0340c02c103c4490400d046c00740d03550203e200c0c1c2e6008007010880d00090621032820040da040c000f9400d0080b10500030106094048010351082e0000303030391514090940d160a05181190001900709900c0c10b9006604291902c410f5082441202d55080455006090701508400030080c1d88203404e11028104220004c1400d0301051880c841001022203080115814580c040d000b810003a450a1119130799400b8001040540c44840440b903111015140c01030f0b0390002801c0300304681000803042500807640e2a091000b098010803441c010200c1340182c1404140d41e44e004441e50a42521942482070250b404a0b101d8202908140c0701244020404040031f210007146c0d030920f9103110b101607 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 752671735 1250 752670485 752670517
    0x5030d0b01020124051509031213120f06060b03040201120c140f0309120301180f020d020c011e0c1707170406060e0610050702010c08160c05040f02040302090f07050f 73
    0x14a1a10b46c0b0002a40d03500481842e0806142e40c0019854800d80c000581003414001132600042034949402d0000d80f182d90a100d0034030b02c5a00b0120040d605055044039003600d814004141d50030040f003035a224541c161345d621031403180703000c04802a0100d4050002801034804031140421801400b41080d2820f442d1100e4881c0781a9042c00e2400209150814070003000700018002414650300c1c0300d00b542c03100304c07010481000d02d14191000b1700c03480380011116840807801007130414040d042481d5070030041352424001c51312090032104441480ca503010201d040000001c904001000140d41c0c450031605141c40b210b0454211540380140441d4111a0513540d03000900c510008030544942061066400380c464ac003824001070030502c41e5941c00303414010108000001c000c840d6003159075401300e07905004401e22271444c00b45000d88841c0240c512807801c01950412245251098404981d0028440d60036134444403040030f05858050422001c000e41040b2030b009440c50b04005101d603050100340c0e4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 752672985 1250 752671735 752671739
    0x7050a0506032a0f070b24031203071404080309130b0d0215041a0c0f030301030c03060506151b0606240705190f0b070305090303071409030d08012105030d0b01020124 73
    0x4526007080d1f5084201e0180104a0744419903240022120185903028001950300e4540d080f00740c0700e9030b0040c403140c691a64001401725141401001a18a40c0415a001c000ea0f08402040c01e050301c10b00c0f10160b81044110701400c016151244088407218000903405103055180c0c00701d060310200340c2c10302c841d085200156520b4607080401403815180900c4000d1421941140c0e105540300a1922014042c0307a100c10210340c0555913255101425005401d1b0556154200004045d210620015016150049400040890a00f4883c205440450760307580c103224041401d50b0a1950040c1000347c7d441c1c0705160352000138800d82c0e100031115a004140c0c405045642c3e00c2c0000d000c001c010840003c00d820142030200344c40c0000107072030300f044490628032595000012454840d001d15543c4581c903204142002c0c443c0f079002800d040c180c804860142c400900031500103041900c41100041884e8010403038600c80386a150300081401c581407001150011004405409231381924450080b01500c50100b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 752674235 1250 752672985 752673001
    0xe100503060108010612120215040b1609030c0e1b031e06040207120e030f01060b0d05010b0f071212020a020c01030e01060608011806080d0207050a0506032a0f070b 72
    0xd0780b4014001c0d0b030000d000301c0c1d051140c55910b061402000620700c0c140c207805080140d0080c0840ca00c40c45407415105824039180c10038101200b0103480c1f4a820911100c28000c02500c5114500f040e40e4000c804000500d10f401c0c2038484100d030007071a0708003168154060091a401d2200294022801001003074603480b1800815946004043d0456224905c10040c120002e4130358180490f0841c3d0b507080610101c0304c51800300e8102021011071594651030240c0c08214059490080c2c02018802c0600704030507a00c0300c0700b04500b4410042c02d11803e40051000000141504072441c40010941c035010081e41d51100c116001d9810401c1000050b130060035481c003240d680351061070700080c00640207000351803030400301500088044c000c0f000f1211025a081c3d9003049039802c00c0700102455001c852030046125802902c2d404a801881e02c905961a00010710703151007070645c1e00607480c08a10340794900041c080151914035110301804860344c05e01c07207141107103030b150301030301ca42405034030b646e001841d000311 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 752675485 1250 752674235 752674243
    0xe07140102060a050423030903030d0218010c0203030f0c0705040c030905010b01091202090603150f0714040e06041515050a03050619120c05090c0415020601080d0302130e100503 78
    0xb00c80c207425458a4200320110702c040444486c503c16222078003010201d24a1b04c2800c61040b244c0d11ba42602c40040c505010801550040c600441000401c52000740442e0045681c030030004006503040d40107004055004c100d05004141e2240c21400b01e4030410741c0c03100464107849080c1c88820110741d03107005170024007500303006904480400b4a803107035505d0300b4807440c40e000d205034500203401220701c4000103006c0d850030041000028111480c1800601d018034100d10301d4902102c602000603151407094003000e10b0003050f00c003541d0f00c1600524541c1e4800e018000113105c65404010b020000c02d40c001800c0d5400001c05981d1011030352000e0392891007020150960300c000d4071490003040441d001141c50b424000c2240d06a46122002d134034906441d040c000c1d210b108540040b82e00c0341c00700c03003405140d03900c1000030001c90743c429207149092107108078140c2e02d4070b0092090001700c0d001a00c07481040f611a41c014017185100c0c2d00d012602070744900042c0020f0780b00b203440070031002c8440428001131800300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 752676735 1250 752675485 752675491
    0x131b090b01020105040507060c29070219081b0c0910050109140901050d0201110d0914030c010c0b0c070506091e06090705091e090a0c090b0303040e0a0e0714010206 72
    0xc0003d0007a1704040c1e484035544c2074144649010080d95a40a8041042290141d541c0200720941081500705481002c5584401521043d0151054007074056820a01c80e00103000a50482c198600b0020207118040013402e4204a84e00b8600800c8140e010340da45256206004030710800c5803100302c0f030034030002404500b41504811141d200a00c602c1c1d00d00e80e90180e21a0540320182c1d80f010840c0b005200507169102c40a00140c0a07001340c044584060394850088811103041c2c0c02640b152503048000c1c19240c561910340507000900441c04400822103840e040c0c2d8111005140042c40c000468541d1418083c0c01d0b10b1480e40c3e170f0002d01206800c04500c010088001c2003103405003240b824001081031f0b07601e1a5208690081c42008000b89480c528140c011003018441082035102d480c128100c0d5845112441c0c044417604031030b001c040380e40c0b040d500c2503a500d0f110250043d07181500300886500207141c001e08901c0004d071202005260540305000a50041c180103014107843e8a6402c00641010001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 752677985 1250 752676735 752676737
    0x709050702070f03060b030102090d0b040b060618041d03040f14010801181e05091006241d03120a03050f070806060903011b0e09061005030f131b090b01 67
    0x10440c00d00c0340207800f22001040340d03840400060b0b903804000102e40079025030203440e0351200060b00c004062012801c203442c4124030440034112295503400410070751f4003601c4030030150398900e80c45441540c182a4458a00c0781043c01141c51201080b45034a0b181d540030390041042000c02880400800c104000010703d104801d08000241e9030501032003414010140900003a220744031b215009048000411085182451500c10300443c98210500303950b44041b0041915003610701800040c0d0300c1e414120106000c031103810788440b204040300040b02d540807085586c0464044200c0c0c00700240c0d5081000850240560504540761141d070030020302100c00c010303c030340b200c10311040400a040381e105540300d6208204481944e1685d69900119004005080072241049a8070798a000096000300c500003c07000e040f00c50001d5607860a00340301c0090300020255012031424008508041c0142010540c030152000900e8280d40c800e8031607041c5503100c200420400a211b030741c18001081c290013100400042 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 752679235 1250 752677985 752677993
    0xc2303120f031b1201170d020d08070f2c01180302180711070e0105030106050307140418050d0c140604020f150d1a0a1505071b08010507020709050702 66
    0x440c1c20000c040e12000748088143c4000c0c40d02c50341c0b459801010343c1e003150780e0603105195035078603034485070103110345080105c1c0244a40e10000404510000c1d0046400040d0707510713070065440311a425124002c0ca654040d082c4500c1804c006041c9c0c64a440b03208503404841c0c00d0a040702c12840014140d2070382d401e00881c0c070752011803041c0090f8a07240c01004d2030280403c0f10f005955100701c01100c402a52201c80c48103400340315800110704042e812440e0684400318000c11005030340c4d5040554405082c8110308842c68000c40314000362605900201e00081c0316071090342180c102c0c0d0b540c030303080c600040007010100701c400754148280305000080300d0741514000c000300f07414282500020080c0241c404110b100e10560440380703031708200e0a0141d405000320111705014031440300040d50f10092709603102c180145e0980740002607070380f800141c5140902e81911118a0885140c9503100c00c50105c0404200c2ca500715100082c05507000d100d120b1068119601030509141881411410f6800140c465001c5500c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 752680485 1250 752679235 752679247
    0x180f0507090815070e03010f06050a0503070609050607230610050d1a04060b04090b010e070201021207050d1401180c140919050d0b040b06010c0f0f0c230312 69
    0xa80094883d80084440c440d1480c0ca964241045400d03401c54001180c02d5400c09079500506031058120f482650400c4a070485503585440601d0b9a4160600c158400211a400104002c1c1050b00003044194000c0001a81c48403103c0300720f14203900c12844130403007680040208400c04800c60020b201130942281c0480c3d519402c0e0300c4100c4207072141c0c070358481020804400b08007040943e0340051144130000c1c000340500341c06420203135400042480b0b1103038001011400100d40d0751041c4204e9402c0c000481e1090701c945c5039001c0485094201112030300c5a150f680e048100d0b10000351603a50f009000484024160910720a5074100342c074456400007050000d80048844004040300580d000000d0954840b9210260050120054102940181e8200300005554000c2c021400d0b00c0b1841140034440440498940c8001101e04940c0c0c5a0044d10404500700f0460009400341031a600890041503603452180d00d9800009200c0f60403804d0343c007032103d8004c042c08907040c10320a10304502c0c40b08030340c142040b07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 752681735 1250 752680485 752680499
    0x901150501030c0c06150303110309010c08070c26010c0f05040b0c0a08070303020703081006120e161719080904090201110109081201080d0c080c0106180f050709 71
    0x9640921410b05445070441c00c200d034030460b500e00d12980c11000a02100d804803055100d1100140402d600060712070404101d018000030885584078010781d82d05040081c20380750a600750f08031001c00c032600c40e1410000520905004c1c1101441411580d00380c000080503100750782103c543d4040034040c040ba0180c0f040006821509440c12502c2e0802129580d10391a060a414140750b08001010864040381050506238140d0217010414425142d04a50392a41141c000c0a0901485454002220309a820328081c8464101d200c01174040c00c100c60010308811564907201ca40c030f4001c0c1c80302d000200e0501c8001c3c1000c0051102200d2a2591a00c51070401d441d1502c1510074903c01e68040c0d80c440009030210792040b08008103204c0c0140003040304001c980b030280318541c4154050901e5210050000c20030380c0c0e010a14089030310b003a03110360900c000c0701da07611090740d0080c05d60380041c0d560320f0400180c40341c0410064a0155900c4800058400b5a900110f0444001904560400400d0700050144c6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 752682985 1250 752681735 752681771
    0x5150c060a0c09080a05070513020903011e11190c03030209120f010609020c070329010e06030607110d080601200610060503100e091e100f0c0e09061504060f080901 72
    0x921019038805100720104050000644903245cbd0380b40d0550328181712001a03100081e241c01c0c151590798810700111516030340c6010310380101110407401c43d034549c26000c000e900500b000c0d8502031007814054240217800001a00098100303032800701300e820028683c02d561a0a100e104040c00034140300f10705000b00d07150095a0354911303000c01031030640002461100c50707408126102031185514114020f43da103a0a0f81604080c0070745500d8082c5c0300e104086a02e45008075500c00c4040d844000500003240700d1030703040300c00c0300001c0d00142c144921143d0581818109441c500385280f00c650040c622814405840c5160880c070b580410f0070040103009001c0e250110700581d20484102d04c3d200041e90710340b54841410701420415000c0b46c400a403611501c00900491001c284042c143c07070400c0910032441d800c5043c1c40310703c0c0c5003800254650801150601d40343c99241c1d04180090f0800c01903600e50462a0100c1e4041d07045400032900100540005030761048113a9400020f0400078041071411003003080ca4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 752684235 1250 752682985 752682989
    0x513030507020301060f380706090c090f0b0109172a030604140c030a11190306090b100605040f06031a0a09052d0105150c060a0c09080a0507 62
    0x40140c009600300c19541c0075048800609140205104041d0b6112100740b000060b13480411401102207071002240030054171200000c110120445140008507503c080040c002d0305030480301d400b08880e011502100d1382c440d044102125100001e54031580800150045c01c480c3d11900403041a0700580e0b440510105010850061511645426080c3c01c583c040300992200c90300c80e003501c9000200b1007070040481c03e5000307803041ca6058640080d000c500345600c41404030703005400800300e40c04019060401086030ba9200341c1e607020340700d00c91b901c95480a040d075000010a0f1202d080800c24040c140c90a4900f1b0f00c010580c0c1d04000b03240c00c1c81c0c240c1e075050410140c40b03a50245a50f410070011081c540aa60000040c4000d046841c031544550310100100310646480c12041080d505c2900c81d00071404501c91000c4d1854000e0816a203040100b003d120814171030150b0381d880500154500300001c03c07603140240d01844000c2101341d400302c8001e06d400d0b42a071204030954001c40004001c128040ba040701 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 752685485 1250 752684235 752684237
    0x3010614040513090804031a0105100305090a021c1a010305061e0403050d140f1006030b0303180607140c0906040b010804060c180f05090703060506041e0f03060209040f051303 77
    0x180030043d6080117400c0d8003840c0d0000c0c0c40540711041c1c0001d03003080c2400890585134110349100d40b801c0611411012500211007000381540004030704005840c0420750030355138070b05111300308219903611390300c1c0540320200402c81603016052400600400c0301c00c1c40b544d03a01031300f09200301d00d00251903007604480320400f51010f4240200000c5080601029030850404006071a1b030724202403c05441d13030f00c0c01078070840703000b0200d203001c030780201c0d40c0c81c0300e4080c038060744800400942c10440c030246e00207100c80d101c1e110558458020002400001d00ca4584250303401100d4000d44568010081800b040c4140100784a1045241480894040e0381007401107030041c1e04a4000a0385241c0d000c0182c0c0d00410607101c0d04045150070000048071400218000140d44058684020913140c015040d000c0d504c0c80d0107001c0d80004244028012150242e03211024184e035401d403c103c40b07564a0182c02c0030040342d0003d40e0221b8000400500340d0609010f40800d03440c0c0350808125910700400c0c3e24002581a0000074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 752686735 1250 752685485 752685491
    0x903060e1f0e0c060708090102100513030819110a0f02071809020307051f0e030607080c0f07170d0b0906030304330314130b01180e0f0303010614040513 67
    0x4001101d003084007051403c000f800c21540c0701c0c01c605000903a504219000c07401407003180d145043d1583d917406100d0040c0700074070449028542c41c0d9800d41e034040303004100415400d003c01d0003504016141c0280c1c000302c1d4900c68001e40d540c8a4020060052900e01c00c0c203000d640c4110030070071a0038407104d1815880ea002c484005a901c4041c03000a082c400780340d120070ba2003d003900c2c00100003c0c00c440b040c2850a000d485402c0b180314007005154440c403044a2401c08244c812000540c4055500300800d02030714011001071411916664504e030750034200320072030040c440c0400d240b002c8100d240b0070384141d07a0301207034030f451545003400000c0c1e660303c940c1c00742c0070f03881d01064030300341a84540c126000510401d02ca0180080159200b00070010007403e181c4c681c0701d0a1250101e0f42e60541440d90f9040340e500152000000e07070903c3c1407103e60148926aa440103aa25804240d414200b8040d065014070b0203005550f60f5498003600030302100e46000107402d12003042104012a90340e500d00d481d20000340740004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 752687985 1250 752686735 752686751
    0x70e01180b0108190b0d0804052b0308070c1e03030b0f030c040b04150e0403271e0306020a0e010806150d091719030c0306060818030c07060903060e1f 66
    0x32000c1c00c6a460071702c1d00100418043c3e01040799200c0a0002e0712011b4981113a4040c52000f080d000c00e03400402a00000c02d40111100400d01c40c002c2e80e0785c082042c2c00d02c180e0315102c0341d5480c03005074032a100c01c440015040000b0003c240d414083d070f0a9080003290200c00210440700000c0e00c03801d011002d2803160b51f941d4140445511150028904040c500040e05120303a607070440d440d0107050807a400c40015190081d0504004102c25400d00050381c030341611190709051090000d07600b0703650032900c169110602d0000000885c5030004058041c403e42c2c0c0c5004000350400007401544c0003034147c2e0b01c14680d8a80e0615030614100c1600e42150081d080418806558100603401d0a0b840d5040000510700040c001c46420381860225400400760b0760030401424048011001c17590103004046c001f5082c03901003446041003541d005407914110b001e03a03180c600c2e075a01861528125600503004100c680030108240302041c40b40b001c60b0008000074003031000c1b02c40030103904c00d0410701203480103641d15405 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 752689235 1250 752687985 752688031
    0x312030a1d0606130b040e15130803011502030712051b031c0b120f0f06100e0106050711100e01181505130905040c17070e06060d020c070e01180b0108 66
    0x44402c6817200540b017040400c0c4005201922211255041200e0299101c04189404484d4070503c15035500003111608503401c002481c0c0c80340c0b200030308120440c80180002400702e101d840c010b050445558484a03a90110110908410f0a1180d8070244940040c03107440c294601b003050b42c00d400c2002120010394005600300140c0702c07010402d0b140301c552055072280742d18908009080c90320b0f1180c68040fa40e00341e0f255200c5402807480da0081103400d003425401000b645004a011344901e030b01c20b4501403d03105180340800c00358500f8010f001c000a078007140e001d8442d41c200b98003120055007000c1000c42c041c20000e551103d42942c6e0300080070010009010020722040f00102e2000d071413480410301c41c0782050700b4400e00101041c02880c400103061403915005440c006506002c5804070740c1e1a8000707949010420a81ea0001a6410b400302e400b001000540c40040c44441c0103000102c0d030468013541008407400312003400503010100245051085072580ea040b080d0141e0020f0700354122004d04c0d00c0002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 752690485 1250 752689235 752689241
    0x90f0a0905070e090102040618030503070201030b03010b19060e18060f010903050a0606091a0114033105010e031e0901030204083f040311030c0312030a1d060613 71
    0x4000e900c80760104060084c030200c107400500c00c8480e90b646907994503c0d0303044a09804d00301844014090383c420001400154040e40003040807140003000011000f05000209603a0302000c40c0c2d030380f055442d240c018094035400c02820f001c990780079034048d030044800c50f401200c0b0741c0d0080e2010344a865a004061010ba20030481e078405503a00030b013075502d1003a56151140c041c01e041d0090407520b074107250900c8444400030490a030760b20030503034a400068492501030f9000d54005001c22008030154100d8070360041161454010070709201b20a45860680c40c11b1403400c684c01460151000d4004201260151000c0d0603540c0c1c080700e401400558903200140164002d01c42e5602c00350a42c000c54006400c01100c00d007609021140300c000b960381822480034180c59400c035841004a500d0014001800404d858407151008a01c010b800c495410b0300900000389803c0740401e00c149500c40000c00c000403d501401144800d081035803a1200a034102800140c99031002041e05018001050f0410a00300d4950 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 752691735 1250 752690485 752690489
    0x15020903120714071202031c022a04061223100504050a0c0f081510050303030115110102040617070309060606020703061b0c140a17040e06090f0a090507 67
    0xca9996241c442e45407124680c403559201d0314041c010b10740c1c0060000e00c1101100301d060b9005000c3e10941d05014404c020448600700124210300c140600e0701e442410310703103e0000d008a40351200143d640010700702b1054900503007200326075494104404001649104810b259072102410000107010401c403001e00d07085079404c0405503c0d0901003030005010020684034850b90203942808901515043d0162031100c0398810743c8095813002a003482c250300f19103035060300225821fa103400200d54420000f8615002a080b65440d000741c80340c0c3c0158550400503004102180030002d600303152509402070841214012090000c0250300c0002d100a0700c41c4c0d0000410551000080194035201d40000759100c0490200702c42d0341c0c0c41c00600d0746d0307455000070707035140080f00d20f59a003800100ca0b40e41d040403a802d104212412845182c0000d4009a1490090407498140904807030b1610725045003e40343c0340e1302808240c0118403400500030840001c20380ca5038440000e6001042c0081c50f454080c2ca85081d40d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 752692985 1250 752691735 752691763
    0x1506031e081e0301170c0102100b0d020d03030e0f1603080d09021302042d0303052206030525020606040b060909250f121d010c0c02030d020a15020903 66
    0x10364042e21209901c0001d141a601151140c441d0049031522056485c80c1400149000d0380c13102c40444100340c8035402c00c02000c031015000c11800c0e00ca99010494040c481c0304100c0101e921515450808031040016000c2014100024400441e401e000322001d03400502014100142c0000c0101940805411400e02d00354003a0104001c208050345240007508140030300080340c10032030035412a03d0131030007242c02c03901c80c5d82c00300541113841d503134042d50355500c40c51401c4100c0b281c019404062016611101006080a850221711442c0c00788650710703440000580020310718a1a551148141e9001841c640d00050940d000100d07421074000094141c060800d819600c81041c0081159400028070400c441c102d4440300c0310440c1c0e80380305090f2888010301007034034001424080d0b072048500540d0040c680c00d84081d0144200c100b1440200c80c25541380c1400f0b0004240402200011810100180303880741240d88043c000400071079541d002c1510700d0446440c081d540100d001002c581e03050250500c02401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 752694235 1250 752692985 752693017
    0x23180a03080c010f060504021e0a2601080c010302181e0301021303151b0c032a120509060f07020a0b04180c081504052509031506031e08 60
    0x100340c0b807074041d000420204180504040c0001254203150007034503400e48403d07001c456035448809401c081904110080d10402c00007416894000b0101c54000c12514004100b118581d0f0500d4040352070032940000c040d04151041000c8034904001a1003100c10318411114000c03a0051a407107100c45984e0100c505a05500c0066609050302080d101d1000300c03440740107401702030584841c040301216a01c409401c1600745511607580300d04d01c224990076a440c8a4140005506001c0c1d1840701094501003211100b1044441d059080c0444a50300ea84c0405051074054036140b4100702140403405003900c240b90141020900f6021959500c00400143c0801705040e0b1310b95556540c0c544042c072aa1920580c1c0626000d403988160784100d500f9072090074862001901d50038040c0a00c001000002c2089188115110708241d400c40c282c014484004402d0352040b07081030840c28542c0d485460001a030140e103141190400014180584000e2641504940410541c4103070070300300b038203110345000d4001d0a00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 752695485 1250 752694235 752694247
    0xf09090608150105030120030c0706180b10061b0203031c060f14060901200604050303071205011d0c0408030a18140f09190510030323180a0308 63
    0x30300020300aa96119440821880c3d0741e80d01c09041c01c0b12410b03100c45004071229000c8006600d1000d000359000503c4000103450f0043c40e4a580c000c407504514003000e50703504003145000740641420b40c690000107070300e00b50562614050001c1c19aa0f05414484520300c0c0341018a820742d50280151001801d1406c04810007100c4490103600410031802010b030f21080d1800042440311303980261501c80310000c0c040c0c1e03140150010041d6005182e600b5009002003c0d420071250884017030024a00462142d8020742e10390070090790142090f16401e090070a0245043c004101c9034040110801492440b042800c450352525900700d50705105a4200c0c0d80c161200080d80c2c900b05d13070720180c41180e032412049084070f481c1d10b509812890151000b0b0965000842c0c998520b0f01d842c0c400505a00005a8070b11051a000c0032529101a25022150303141ea07804540b40410070302d900035425071450055840211070703c002010051281d07024042c2075040c0d04100d01010b100c2c54407542c892a015640095004c0d1300c681c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 752696735 1250 752695485 752695499
    0xf1207171f051008060412120b0301090b18190b04030e090f01030b0c040501050d0c030213170c010c080304030309020d0f0f0614060105040302010302090402120c0c0105061f0f090906 80
    0x4001030b0f5404101d501ca40e0703000141c07004040b4006010301d45c403043c0c0107542c049410048864414803807000c0c20840c0c0e0307607000b040c841c2c1e8244244545140b08800c84c080713902c1c1c440c001394100c1800c00007288081d04504500082c82074031150f002c480c5644008038400070740301c50a00b1a00030b10104d0250b50407100620500c16451405000e07d0b049910402ca40d030a295103240c548d4079a80668400c031800f00708180400560550503030004409400c01c0d18005052003199040000f00c00b007940e010140581c45110354600280c814410740e01209001c0c00c027403d12080958908c60144402032000d0101992407000c5011940c91120342944990407000810401c0c0c0c1904020a554412550846100d440d010f006040c3d078181c0d41c0c51621031001616018101441c680040d006035010701400c90340582d003044030b984080d5204480da0f01494240f1641ca449403165010103003100e4000c0c02d0280f04d80103040c0b2180780610140c80c0051303800700324506805a504018425a0074001e2074000000c41820a0000f00300b403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 752697841 1106 752696735 752696741
    0x305191110120f0b040b030a0c03031103090301020a0809160308091921030212030f042d080901020c060c0604060c021216020f1207171f 60
    0x40d1060392600c0707007180c0714411604010f0707a4071854200e0504091096090f9400140c00400101816440c0c50528110301e100040c204000010b010311071503410f200f40d82c82c1001c0130303000b50f46503501c03003402a000210450f603682c81d500c141c11075003001f41d2454000f0011241c00c0240f20b0324000c50801440001d5030980c03440c1d80c64805003580041c1c0715144903a91384082d200c007008000f071800c451a0090410a9175696100480302c10710902820001c0691103d801070340c42800100707808000d19403000b0000e107440c0d100b000700921450100510014400501404900b60f00b03981e43c4c4c0f9030000400ca000d004161a00c0340c1071f0301c1a40001c0c0003400719030190032018103500483d01807030620704d0110295404400000201c9062021b41802c500b004c1c15401042601100c0c400115001030102c150b80c0c1c5601c2c840d0069880700140c04100c025410301c814411058441444001010340d80311034009 = true := by decide +kernel

theorem cover : BRFrame.Cov 752517985 752697841 := by
  have h0 := BRFrame.cov_init 752517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 752517985 ≤ n) (h2 : n < 752697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
