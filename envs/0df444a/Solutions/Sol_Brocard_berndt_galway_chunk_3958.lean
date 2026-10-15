-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3958
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:10:18.518795+00:00
-- url     : https://prove2.me/submissions/89969d7c-a672-40fb-957c-a502ea06901c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 711690647 ≤ n < 711870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 711691897 1250 711690647 711690673
    0x10f050c030c0d05190c0e091b07080f0903070617010b0a020c0d1704030f1509080a05090f041a010e040213060309080c07080d020f0c0d03030b0a05040e 67
    0x911002080300c01144400d00030800784007000c8048841c0c80c803c8010000e01a900d0100c01d500840d8400103002c209480e14045842c8690803048442010008850740701c640e0741c41c41313a095462081c0c0d001c030345d012200c180100d80c0000c00d92001f8004c001c030102c0780181047d60ba100424900f110550107a40040e0300c030386c514403513214912000c2e4090301a014a00c0c2c0340440302c08000cac0d0340c0c041c84400300e40541424901001406815402e2041e4209a151195681d55480c00e00380110041404107641d009000b88400c040d0003a2841100302595220001c03505000a0104c00e541e241c001c1000503420400c504090340c0c5658613807040380403018900003191105009000010a401d4060300e03454040c92040180c020300001d002c581c030301141d2142c60041051105441c4c441c1403405040d40941c51b900c580c400106118070042090300b400401a4210340002020f034190507235814031502d000d5048190740b0404070208c1c2c442c2d00480b00060010704094681ca6580c1c000c94111150460310850700d80000c100510a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 711693147 1250 711691897 711691901
    0x61b07031104060e07080a06050a140307050d051e070506300c190203040302060c1c0203070206040e091f060812130603050718030c03030906030e0d0f11030705010f 72
    0x1c070000540701084028103000301c4054404001c2c06003828020b03080c0000303040401c0c03a0040006403c010b08840c00c92591440c4140d47d00d1604800140300b40241d541c00f203070382c2c14660540201c458210f0010802c681c43c840b0080d1802492209411480c0104a0302040d47c3c1c035660010701c1c054a65101142003207a03181508250700e443d2460b00034003901168188011071103c0401d1390392900c9424504032003201e95420580c918460713944001d40051010403030149002c0082640313803041900382d0fa10b04407902030b494126124420322000952042050005003d07680b0701200c00359121000270300300c0c2c3e0300340300555246084602240e42606496240c40003880404014086003a400c071010755103d0612101c4c00c0f045440301280d0054004243e6101c2c009840c5a1007004078501c08561019a03050307079034807070600c000c042002d0701050340451000e0000040c224443c0c82080304030810f50019080c0324028440807038840280400550420044010101d451813090008045c0c1130311400000030b00f207507a0054003007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 711694397 1250 711693147 711693173
    0x6150111010209100e0f040504080d0501240305060411270d0f02061809010909120c03021b01050c1b1302090a0e070318030503150a1d06061b0703 64
    0x80d140d005000d0034079113441e4810b6070050b403c440d0420100300c008410200b4030f8242c02c2071420b0751090400303052005000b010f1009120100c45840700f0b1201d42c0c2c0f5030340910f00000707000460141e2010118072060445100e41c0c001c9810000003003004c5800d015103804a24650040c240c42a4406901d418803c42541108000e02c0310610980344044000440e4680102ca254882806801410002103400f0740900070308603101b00301c0b0024000750507541c46019800c0101081c400485e00c0315038221809054038050106d10001c2a410b6000f04004180440030320078400c000b040850602070141300c00f0340c607220b0501c5284115013203c03003c64003c02d8481c0070002072400e00d0050f40061881080f1640d1079807030718040502901c59030761031034009481d178000c1103004002c0c4401c00d00f014140007071340d441010303480070096000325044c241746042112628100f1802c80c0c03680c0700c0e91410540d0f482c00041c0301d182c040030141d40460700a0520b803d003100c1c0480003091300c402e80680441900004424070802007010398102c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 711695647 1250 711694397 711694427
    0x70e250315031704082505010206040f060207110907230307271805010302091e0105040902130213030b0a0c050d0b04020c100510080a0807060c0908061501 68
    0x201c580100400c41c6074800c140c41c00040d011101d4400c0341c07850b508641c0100d40003000b60303008481a00420349078040740110034503c15101031112440000b450341c80020b40340d01071900454941d041403000d80d1158025882044226214203200f003242c0481d030f8462081c42e10070245610341000703c2d040b0381d05410045085000c1c00008160078003e1203025603004a00c00b8104200d00e24103043d6200003940014100303015480322400c400c0c801209042148617030400d50480384243c1d029615919402d508400070448410038400d0000f008004101c030f807900340c200ea000c00f800079180031a2810402189002d9902c541581407040c1010b0b60200104125050f8980d0b009182c210300304074118090100602c544a6080044909a00d803410100c084e662941151f1818011004032142042d0f0800c0300406403808a541e0481e0428051000070741040210310003058560100036285803030080e40c0ca080040c003000f055101081300341c040200e00f521042003070f41c0c088d0150380007285081310104001440324030020040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 711696897 1250 711695647 711695651
    0x6130b1e0f2b14060709140904150c0e210d0c03050d27060507080c0a020303012306030901020d0f061202090414010c0c0c0f03051509070e2503 63
    0x49648408840048400c0c20302802c031550262800b810804820281003c2c05126400f440080c008240d0b00081c20300c049a400e07503100c12140292200b0404a8035044034090450680e80400030b481c40d5844d4807044141401b818590b0b400b581c001c01148242043d404507010760665160108802c20f0704201a45a9031031030304c0d21260320520b5a400402500400307100141e06515481003254140c252905442d0b000209000481d50840314140743e03015140c207844507000301d1010000f28856110140440d070a03e0023980040d45180d21b0222044101e1071a002510b910b215079015415240da40c070002540102c005400158640142c508000c040b6a6010f182c201c0003880c0240411074009001e0010101f44e40481d4008010f9807642440e04031800b8401c1422419460b00900060003a0072103502508640622081040b01e0f407140c80340c40c0100301c81c0c0005080c5030701c60b4200d4011952901c800ca9400407140c000e603085590307241c0d00d250701d619050311140713a0300300d504615160301d00341402240c4502c890780c901 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 711698147 1250 711696897 711696919
    0x90a1b0201151a25060c0804170a050717070602220501051204031209140d0801050a0e1308070f0c0e10030c090c0201020c160f06030b060306130b1e0f 66
    0x700d006445001c0d0101c81e54819024602c3c25404a1030131051040c1c5c00ca5414450100c0392240244400811101250300e00c00c81e043c4610300d030300700d10140c84102485403581441d05c041c9803030f000070b910f03a22020365000391401c100031000036480d800a04900c989038050290103c0a5100040700300f08103412040c100501407150038560741d805141607070425003604141e0584040b951401d0302826144030083c2c0a6002030a034543c491000181c0740b0001c1c20a070f9a40406640c944003084008110b601c5003245000c1030001183d070400c0c1c84c40010f0005031040c1c043e9450a0755a503500c4c40b2040031031009854208407110100f080900307003400c550707002250a5645510a0070750f6141803140c48280201d15000d03580e020701d25041c2d8000d6044800b0a00d152044440d01959800b80608902c100d020b20b40a0081312640054401c1c040e000e103040102005100c0c0d400c503620a07003800500040741c0b0b801003401d500c62100c08610b407260382c1e40e05914503003001240d0309c2032580e1090204d1107002c00c201e27600404c49402 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 711699397 1250 711698147 711698189
    0x301902062505090102010906110d110c0a060c0c050a03180506090d110103060f0909021c0f02090a29011806021926030f01090b0609090a1b020115 64
    0x500c4000981d118100303079483c1c03070030203004034010410850018829481c0454180c1102c50703403070140281d094000e005010071040302c0150049401412601d680991140c10041c0c0014580d801001000503246440f040b848400e44540e49450785000c01600400e5241d00718410800c0c1165a070006001c0c252a29858007a500d00072515101d0240d0000e0000100300680c245140c0c0302e80c02c11402400c41040117680c050312140301000400103110100e200e0108a541d0401c00c1003207120040103141c01550440050130b0075000e00020210052800c012a0b0352481c120010580c95035038410489507952642c4842e8403030b100094410104c401e0040c441e200307c032604001035980061943c24062000000000355105458860381c41c0444010510079141503403181120905c0700006544a03212418140c0c180343da0f0761858800303c070100c1c1e02c0950410003c00101000c2e04005002581141c1c11400004100c040c224104929038414229540140d440e2502200080202e01c8420082c15241c0240700c00d02200390 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 711700647 1250 711699397 711699451
    0xa0b070504051e1e011e03050f060a03020616020d06020309160608010f050402070f0501020708030703110307080a0903171003020103060f060f113a09060230190206 72
    0x1c00900b203034442251402040d13074414004494086c2600345041c2002c050b5003006400342c842260301c00d0b010742c10880018602d00d401440002100e40140c8014a8004019040c2d80110310044041e600203240081c000c0020314284001c500c541d40130801390084180c405038a01700c00e41103a20180810190100510640039100350800031030b08200c4006990b5956860600d0181e259040c0142103035101042003003d0040c1030000b144200050b64040007404e6501c0550003107800143c0b402d1001803582c000154000a00b07601c51030346540242801a058003600d0301c10306030f82400b182c2c220b40403000c001d400c008658160040602400c410610810014100701c8020a500c42d0481c80f00b08100c0c50b20382c04102c60340d0a10842d203c0c410b01c07150591f070030709019641d80031006090b080c05200202c07640c15150235501c507800040c01c0c2c40b01c0368050526007055100d0360300020300d5a40d81425600c9019400c8a14018500081047c0c100040015159100d000f80190034198000c204c01c030712000c1c5103000c1031244600 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 711701897 1250 711700647 711700669
    0x60b030f011a01030b031006090b120a050712150504200303090907050325030b0127092c010c022406040c030b0d050f120a09050906030a0b070504051e 66
    0x1e190001e01791080d540001c0c0b5040000e450103d15501d0080c001c07030700399843e401c024541ca9054600ba500c42c06441019507030b5000b0300d1070241582c0c10044040c8801054bd01c078801c40701c1d0146160f44400800c0d0403044040700d000fa1000c803001083c0c40040d806e0000c20410349514440c0440141d41800860030120310b004c0c100400000c01c100340013002980c006002c080c1c0c0135100c0d03100b0400c070010400d49180540104003040180b80840e007800c500c03036480c52901e00300f0351501008004207107441d89055600d201070310b410dc40ca00e9000e448401c02ca40207403084204450f02c001100004601c69a540c18040c0c20501c462a03081c401100c27500ca80d8100c0c1001d51845500300405540c001840c0706415822030040c188200200d5220034a07401c07c10178040700003036801d4544409801e076980d0013806082d14500e442100a407402103454000100100e01d4601240d81d44550085c0540e081022296103d000c200d00840307241c0d000c1800480c0a000c0750402c072a0f0b9010072011007820010035008140050042562 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 711703147 1250 711701897 711701899
    0x20601061b0b22030e15071e02030319210e03030705030a02070f1407060201053603120406150302010509120106150309110d120f0c0c03060b030f011a 66
    0xd008154285540030070070b10180c03d2480c621040c15a24070f40104040240a0343c584922241c8410500c481c0820b0b04882d021075020760003420641c00b14011128000700b1500580c2d041c0418090820302440c1109841043c2c2c07416a504201c5240c5038a908940284071820001014507080d0603140c066000421690030a440c0d003001500c0e5a19441804045d2040950041a20b4a2100120f041041040c2d5582900d00c150b400c0d076017080d480e1401203088075021903560501146505a07032401e080c0c00d41c0f18400f81e00c0381c5040c0c800344288410080e1702e140d100c00a00342c1001604000c000c1400550310a40d804000d804080140044c5142c00080060042000f0240f0071181c070410009100d809501a03401042c40004081b40381501800240080403040411340305508880407006251070290f05c540d81803980503280036074501c4420012a1095540c0303030410300f800310518100010590064528008621504010591405034000e26007090700c2d800f801c0d403240e0704141030041d030514512900015824 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 711704397 1250 711703147 711703163
    0x1802040506040513021903270302070512070e130c06020c01080c1605100515150d1e020408030d0f18080313080c0c01080105031504031805130c020601061b 68
    0x75840c1d000b00300a2060002c141d2040f040f60809040e5103070035800c0403823040c0d918072041d0800700641981940046407aa0010010381241100740164909060000040409241128211902c0c3c6064a210304011384010000300d8002c1c0720581048110500180a0300032403001e0608080c0703207000a0258078025100703518200004c20008500665804000402d81d005821036600c00d41c04011900100026039102903400e240c0c0310461218241103001181813541002c1182c40c1030144c680850040084421303481c180260f1150381411241b181c0041e001600340342010310f0382c400038403d04a00302ca120004100c007550520708000501e035081c0319003442c4581c0010005a032a5214003603000110000c500040203404041204c80821000041ca59808a028ac0314021181d03280c0041548e0f400c0c800340e40d4000200540000340009114030104001902584c01c086001e54842000a00d0201e10f840104449581d403104003660300c1d41040348900600150820b481c2452600f01076001600c0002d0002e48048 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 711705647 1250 711704397 711704419
    0x507080c1228080310030b1e0a0203101715072d230405030606030f0618011803030207120323090a2a080613060510050604080718020405060405 63
    0x10b200c0110184580c0000b01643da490000d48920200e175140c04180c030b000c00c0780400a0a08888040e0258640b042107040c04025951400706202a5100511418401c00341500024010501c00d48901180103104094a40f108814400300440403000b0100c89c204200c07080300110002c441d00d107000d0f40007810040d402d214450f8227000c0d200d115803004900c00790262151411154000700303016105480c012001d40342151102c400700340d03031451000c182c003a0340d42124000c80c40400c4000d88403c6030505030030000c81c1c1d8054a000400324285208415008260005203250400c140000100c83c10501403c0420404401c21134440d118400c10f400c0141c001d941d0380203c2c070340c28402c200350403c82c0d82c00700c4080307507021600200c1c1c20900004030840c00900e044000104814102040c814400c68a00c01400c1c3c100c0d0640d1240c101401e070140c0f0040c0f010841b0310002c034890b00c0340001000945203030001099000d203460050407040701c40d207401c052082d03c10b100c144001c1d0f8406080710210b801c2120340010301 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 711706897 1250 711705647 711705703
    0x603030f0c061b0306090605090c251208062103091210020310050306010626041e210c0803010308090105040b041211041e05090c060301030507080c12 66
    0x14518069810440100911070080044c1c3c15048070307003a01c44e030500c02d01c02155a14203110058500303968215070f941c002d00c0981001040700d60540400e90310040f8055005d0308075210401c2c0400c6003a000c40001e21709004009440c1409528801c00112404414844800403410365449014800305248030b06040b20040003101404c01014bc2c0180d1448003c644c0c0c0d00b4098400068401e05219031800380c02000e00006600d4040c0801410380e5030004082622614000c42a1006000003041105c524040a280b03004212241c00140d08440c410a0250551202500c083c604a1100390580080000d0f64140c040003980322000d07241165030086910343c483e2000401a01d45004603001344994000c0400c0005480b00004c12000c4030038002d0008000814030502400705582901c598040c0075541c480b10103001ca0010740c043d03540810b0b08400d0311030070411000040c1003079000f03a10550301c96008600910034400d080c480140c480b841103400910311102c2c0c4c07030650f48031820382c603110464002c00b00d40d800b04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 711708147 1250 711706897 711706901
    0x60e0f06010b0702041401120206090114030a05090106090b15130b0705100c0905010c0b100f0f0f050315010e07090e1e0610050708070f060219120603030f0c06 70
    0x280002060380d469607115040c02c411a001840203a208508060b40c40b50781d1a880380420341030700c2c0da080b1801e8a0107111b070244201c60b8086041c15041003920b02c10030030240403244c09180100d040361808101810005a0142555500d03044100300030328140000e202c0755207000b030071800c180702494819200c402141d20104030b44280e03403042d090b410000500c0d4042004c080307400f40d00d40890500030090355040c244200e0352500139004003030124042503101c0e80811078448200368030441c181580114641c440e0508284080150700880500454940a210ba2060304100d20040c1009400074100022803c44124505a040c031692440400300004250480e2250301d0110146c070603421001003e0500100790002c03c00352051444880222030042441b6250083e1251a45a59131b40da840c20101c482d20741540342d40c000e14084440c2040038402c0c10000c1c80c10b0000e080c144c0c0100c02090100c2040e541c0c0500b00c80350726803804100500c4d0040900000e42c00010384c0340e0880c2c4528002c14940c0e668541100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 711709397 1250 711708147 711708163
    0x30f0a0f0606050d050f010c020c09010e042103060617131401060b0a050c011508031b0c191a0301080a060209180a05150604031a130c09021215030a060e 67
    0x81c00804001c04c0c10103200703000601d00143c02040c0003c104c200e864400c22a07c40c400040665484007466004120020700240c803241c00034010481103448100f80700c4200d90124000b074800001ca81c50340800c01a15421480d80c1d0f107441841940040ca030701d0400c0301141d0345902c0d19801450b81040f124480d55448007503008801801d4003840d950790f142d030b40c801d01034025084025051519820608030032520300700c9182040459a240c0011814840e528811040c007601050500f0924481c50b648615540d58820700b10040d0701c84102034040490030104642d845007090010314245000030001003203220780008500b001c0c260440c60042c1c80301546400201d28000021480358501b031300070140840002c5d143d0085004481d10040120b0302c80c10303401844840e000f0340c03101a061220081950034200d0b03100b4419035015541060100003200103030380700400000c6030781181c8226540403410412440c0310f650510342180c007020700084101d03040400243d0786d001e024402001d49884034006120020100321140c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 711710647 1250 711709397 711709399
    0x30c0a06151e090c0c030e060c0a1a01061103041401030f0f0e01141b03010312020a08030108010209091806240a0801140a14070c02030a0602030112030e030f0a0f060605 74
    0x40024040e10302e00c4001001240104101c0d103162440307886005000789000017009615072543c06ca030319801e6042000c1c541203261200854080d004000c00050000142c08070f603550200315121855040c00001044094801002c00c69070f070003088103010304103048822442c1e040d000d1074042888100020440c0181076851042c945540c14030650102405042d0005401c1c10610103441c1800e42d144503041031440311094102603510000c10040c0040b42e0300c00c8010b50900395078012565000c825941c1da403210f9100340c3c000301e03150b5404221681c941c60a1031f00e0b9504202c0303841400500059061410b43c4440c0081d10100c240d144689250541040141c44e2001d107003401400a2521a50341c5602400b0303161000c21001c1e00c0c0c0c0c00d05c001035000171480c801c8004550b1a144d03400e549544000c000d8a00030715825050341e142c8103401952000407003600085021781165420118030034454503000e04214031202c0c00b6440b0340c101501128032080e000420902454001c0105c07848100340303040480080c40300390011 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 711711897 1250 711710647 711710669
    0x11011506120f1b1d09010501050418090b090304090c17011e0305010204180501210209130501090f0506070201050403120c090f0602031b06010e0610020c0409050c12030c0a0615 77
    0x280025041440c0d5440c00350810034404008204004210800c5c40074083c03e80400e030184030078400e8496580c9008092035071404001074074103442d210343c000643d00329200b8000c1c0d4030000341400401214041c0d9100f0400b241040c200109601400c241840414050100490007488840800841e1030712500020b642080086603100e4540200060034202c284c441110581080300010f01b1801c14407440c15000d614500d10741c038181d945d90801000400250407241070b024040c1481c0c020520a10aa11882e0720070f00040d180e841e81480c059041000c001c03e107030b00750b914200804c0301198221215400c004051140041d1a00c030280d0152100368042c1c01c180c0443d14025004142d070354000000306450442c900d00c2c0d1440505070700200d5601d800c00d003e5881e100c1100400b00c1d440303003030258890b0040501801603481c03107441c03200803804949001c40155210740c40428120442e040c680e040004184080001c0d500c0c0c14a20511180c0c0c5115650f40140400da46040d2664100d0f50340d00c1c120040d10302e001c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 711713147 1250 711711897 711711941
    0x1412090f0d0f150e011d0a020d02060f1c060509040c0e0c0705120d0b060f0a0e0f03030703030605090a060e010e0601020f06100602011b0206070e0402091011011506120f 74
    0x884000380121184c0c8900c0358a4161800c01c00300b41d015050080078601d80080400c10010760034000d0025141e84126000390080c07140c00c13904410390000c1c1c1560001d00e40c0e00038071408000914419079215920860284440c642400701040c003ea100710180c2e01410303004600d507254456020389600c2075000103806809100031921210001c10020801464005000d10201c0540c5003085a00d104240751710b11980001c201f11203650f80640d6000b44900c10080405a4100101c40460700f1640104070480001e5a02d403002d0081c0d03d4a03441c81c2e90440c54000301003044506007060104182c4041c019030503240c501200041e49a8402c12482c1c000402c0c000580380c7c3da040c0744951181c20f00311801000055401e00132158800031880324000d468000d00c4d8000e10301034840c004d060724011a080c41d800c1c3c02a4081044151680f00c540f101e14130740490b540c13100c400c141016011400c48100c0030300c0c4c3ea45404404010081c01c1d50185171410f00564031074001401c004080100070050400c11740030b0003c01c1140072 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 711714397 1250 711713147 711713183
    0x303300e0c0906121c0203071401020d06091a010528020610060f082d190e1203010e0c0904051312020610120f0c031412090f0d0f 57
    0x74950216107000d032004602e0b5210300080000030000d100c032a01c004d9210b030030701c0c4441c1905c01c041120340301c1090040da40307004001c2d15035003031403801d030900301c0b540c7c0e1b400080340300c4070405a110743c0c001006d101100304076049020b511100d02c5038880601e40e04200e00850f1403201c43d02122090b001c1c208494403100c130b4003940008080c0d00c411007104c000b4810030740c0c69000600b440c06074810314586512951091340ca55501210302d4001c101045142444510800b03800c1010301c44000510700852483c00c96189100020300480207541d14840310360800e802841c07001042c41e420b00d0550741035403402e02116420380d07143c90240d8800c4c00381140c0b180d0b00509190500c041c02c0900c503801c0401500480b40500000d00d40d0320203036500d42d019030740c0d0715602412100411050348402590fa120340d02c80c0074900b51880d46900d4048000100c1e42040d901600c4003201c0480c50542005007600ea4540259270a0400030440300103180081e844003454080e0f840c0705208020855500c00d21100f45501c8803008101c802c0840c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 711715647 1250 711714397 711714403
    0xf020c07060210090209010302040507050c0a030801140a1206020919060c0605060402070201090303050a090306061502190b0103030c240b010912051011090607030f090b03010303300e 80
    0x4401c003809802841845000320189000f0b0f040c0498003d400c0e046140d181d1b50a120081100500143c10441c0a21448122041c02d100e61405540260b03500196035042c4031a50401c034080e0743c4614403425458038108483c800d1290040015500200010788a401c20300100e0722440400302081d200883c11440411501d420855030800709000b141d04120980c2c440c410300080f44030718040640070540c66001040040c1c840c3c0010600c0300c040c3c0c50010b11b080c0d942e64419041d160280c1060304400100900003200e960304100d0b80b8516000ca1006c001c401e081500c500311600010300000d010812600840c4060042c0340000c0441c1c164030340105a03011400302d13030442c01030052500c994000b030f902c0b5a000900c9848030b00758044440e049006000303c10b5550300704000402c4105c4190300800c005101c00b000030f94a16000d443d8007806a12aa6103a0000d10801400c02210740c10900307164500b4801130001c01c2d07000108160040d070801c80e0151140e5000c55180c0c281d004c83d00760a130b071300c1d0804043e84514030000c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 711716897 1250 711715647 711715649
    0x8010e2a090702010b040614030f0133050607060902090c0301080706050c0f06011514280c0501060f0513110316170f070f0905060d09060f020c07 64
    0x400152994038a480640c10115040c121010498540c240c900604929200c100580c00251600000039070100c90760100301542d02c0b42d4010b440d206001000295142018081801c5008422000b00070342c5024885000d416044090008681c021000300317100d08105c008280b4028003030040400e51203014a00e022005000e086904a0056140d0004a8000c40f002d000b6079050362048400782c003400b41081e100b2911038004c4180c0ca240c0d40b154804a407800701e8188419070103800d012441071610004200040c240f41e07401d94070560441810840000403192103612520b03c03038074883c1804140d4911600464034050f05407005865035180100005002c450300141004031103054800ea00d81545c102c0c40350040b60018200410408001c00005003586595228481c844041e41010034811034440d117a0f800c41101120080c0d603014051040c0f04000f604880f400c0101a40c602c0c02c1c40c40c25060802140007030080c1c00c0101c45086c2c517610041c04204503a004003001031040502107449103411000c3c80d0342c400031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 711718147 1250 711716897 711716921
    0x1e03020904121107210314040b120c0405180c1b0714152505100213092c070e090a0b060d0c0324020c010b09150108040b0703150801 58
    0xc180c070907404603001142000440b85c90007540c2c1801d0078441200c0104004950086007041744850034545c1c40c55048003e0005480c5041015445188944203030107050b20142c201060840f060008000c1a80e86011007000850400408011600d481c0415400c80c0601c8442e12131400f0407a0140c1c940100000e1640110f48110075840040403240e4180030100003501c0f0304890b8890108a401d03000b4a0340300200d2403245080c925040541c0b00e90315203900348901400040402c640014084400110301013441010b0302d600b503030400020240e03c0d1441c5454210801c41c4603090980c6600f1000c4c01000e01145000b440d14651000c8146801c80303500752181003100c421640b111550000c070f140d03401d0010307189030811ba101c3c0d5145c090303074107540f651401c42c15200381d000901c21102c0b01a451030035850020b0071f45420404008038004202404001c2066801001c640c40d804020090040c16a403000002e600150010300825454490b44c000728081d00079455540036a0885000c00504184154070555070542 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 711719397 1250 711718147 711718157
    0x120c02150601052703070b0301030807150605030d140c1203010305100501060210020d0632040b030a060b0a05030303100905090c150c0a0b130b09161e0302090412 71
    0x1881d40300643d454003411441c000f81e100720140d00055080390700e0510b1080d940c014202d400d42c650701c0809040e036520036042201c0d5840081782c0041004404180620100200c0398103012131410440401d03514844070310400c00708212080b1248401150500321109070540b4400d0303c10241744450010440e500c20b1004840d248a201c50343d4044081c0c5114140c1a04c4c074580c064404030216507002c102a40240c80c2c00100680c0d54840080c1040301040c541c01028082404040c3c042100c2c0d041c9001d69851803d550300031030401010940725075011a80f007003650f0b4844c50009503214880301080343c12502d6003119030548400001d11110f980786100380022200c880300e051141e42e4a1070300a584841041c020181c100520800084803840729030040e0011003031134800c640e050318090312007085c0303141d054444403441074280407034000f40940001150740c400351840c001d01b01d0782040d001110b410061845081003d1407000b0a5042084130401500019030300141090340ca400c05007020602c075412a07481101080c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 711720647 1250 711719397 711719401
    0x3021c02031b030a030f02011506030606030b151e07050106120506010807120305030a150603020c0d0912020405042105120f0415020a0203160b04110a1a0a120c0215 72
    0x1090602d0008206000580074043e1030015a806448400c0211006004d5541b40d00e03402d80100b101c151100003d1a041d50041a0340e40707000720203011038200e031141c180601c0c0e20b00080031000790600226040500507511910110a003190400d0290141041c002c005508050000490b0035205100b540c105e4020700c140c0304182d0381d514989955900d41e05c03401612540c11001d400109000e80c0c00303150702a5a1060100301100c50400d035188206180c0c000c0d0b004070b640829540e84c000b804111a40800003541400510780b820301c0d841c0c1017038401441c8005d2140741c50f00c00103001c100c8400400345240584007030107586008018000b034000e400413240100303881c40d01000034480b6081d100b156070296810003001004140179401c141d010758011072802d42075220401081c2110602d040c1100c10050144c00318a0709070800b450004900710403001001e11070f0034002014809101101c2d2440c1283d0034a4002503030307078280210240c41c12482d50303034416600b07481c003903401c61070300c0c0c02140710115000315a2240901d5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 711721897 1250 711720647 711720673
    0xb03041109010609050f120d020d02100209130f0b0d0b1f03020d02102604110609030d030903090b040b0a0e0306071209021c0309090e0106120201050306040603021c0203 74
    0x148100348945000500c0c20303a801c000b03c1c101086d0710040910301806a100000701841158600311501081d0070040e485103071100c90a03035041c4a814062210154154507041890000500f6440b285a09807107003503a4980b0f40e01e41c1e80e030650040102000281200f4070311131903400c0c00301c180c0c54120380c1b0705031039440210100400c180c0e4001c010181c0e9070050480340000346540a03c980c1f100b0780b075400e9003031180c0c6030300400400c40f1050040030445524111480c2d24038080c0f61018440120303a204a0041206010a110740d69010960001083c01c5240000b10252142400c42c0c00c111a80d200b108000320005020810490300d40c001c08280800d071f200c5220f4a0742c10001d240d501c203c100d420300009404051003442d4851aa000b108a40d40000c20443d05030040740c0b40380505c24100c01040f00898960740041142c0c00007800707401408410303031008016181c42e200101140490307500c0001c1c10003c2c0003000411907501ca0307006501541d00545000c521038101c012907900080341080c00c0e8130910503980c0d1700941c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 711723147 1250 711721897 711721909
    0xd050c0c0301061a1602150a110a05071205120f040302010206070e0112021612090f060c0201051b0a0501090b090705060702060412031b1a0108061612090c0b030411 72
    0x1c13030305460491584407244012402a5070042e0824603008189006680c01590380c1c1c85007080781524000b455640d501c1100005012008036511412541d0454150b10010074008160541281c08001c9009a020100c5c54618107052202554000f02100401c021641951420241042c0da200381c003120025200c11100b507990080c02c440842c0011500403085904081e544c010b898122010048007104c204280d071855442e148860005000449a620820401c01c66600300001054035060108503da00c0ba00024a035202d18803051950281c4810308154000080080c611480d070080004c03c40e00740d01c0d140042d42c008003a5075500b220312400c5000b103914a00030048a00c801d900900c00781c6840d103840f15400300340c82040c1d019000d104000f043d56020203500618030348032074450400040211613030680300700c202e981030b00b0001c0e007039100100300468a1102281804044280c0c18100c4c072084204420134042c000c4450b004001d40100d19000505030450b0340a035016901c2011140b9103819646e00b4010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 711724397 1250 711723147 711723149
    0x90108181605120105100302040b0402090405041b060f080406021303020907180b0c030405040b03251a0c030901031d0109110406080a050a0f0f140303071701121401020c0d050c0c030106 81
    0x148900d03111004200509d0158081c2c0395900c0301a0002d81049120340005080fa0021a02074034013900c10042501e02a50a0454002803d11b83c24403201c0d0800c00300008102078001000141100d80c005080300450441e28082d0380155030003000041c0f0740c9401030300200350313400c0451841c0c07216403000d2002c41c520001c01e00342c0758003560003c0214106803500c020003000d0140d00c49403c0e050b028003c01c00107242c5980381c01a215501c201c0d00004103600e880c0805840000c440b041107505e05050140f81300d040c802000312000050240f90111300d81c1112032185a15038800c941125003503190555900801040c4c10700401d210000700c80802681d569105a10780b1620740c410000d106800c40d07188200060302e5040b026008500480700c039800d483c42d603030320600520070a10383c0000a60020041140344c2d07521440380f004c2840040c03440800e6526003241e404642c0c6034803400410520105032044200345003541031394019081038048843c2c918000d607000c3d0190740840c800b21000c1c011a5030040342403d050241c10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 711725647 1250 711724397 711724411
    0x11010801061409090a0f0e030a0e0103020a0909020a030e0303071d191505071a0f060103090503030601030c27031401020703020d2706020618060903090108181605120105 74
    0x43c5880d4420f8200031603401c000301031540e0941c2d203540e02d0850300068071400c20b8200600008503501d0442200141200760000f894a041500400c64070428035440f01d0090222100300ca00543c9600941c0b1003500031700340c4404812050701c004030410004039031040d03110b204c4010250382004c1000300d03101441a2108481031182900752046400c001100301c5d110103000701c446d43c0c6411030038003d172a50740f110914281c460300307600501071000748a1100607080f031036034120509080030800329450b0781d680303500ca000044c0054141541e4042c8840c1c035034014150380f10b00800c013550168084040d6040c500c0302c050180170079501d150700d14031003000003038051080ba80b1883d0942c004181c072100c03000301242c03a107503101c108101d0582c42090902d441020302803401c016107017940240c02c96143c940820a1001e208100306005648940244402442c020040303075410315003031030b01645559652040486070b004144080c48c140c418404401511705591041c0b50070313548101c03654240e0445141e03055098034030940d082c0c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 711726897 1250 711725647 711725687
    0x4050f01181107031808070303020d27031b050a090c08090303130b1009150504050c090906040f18030c03020c180f28050411011b06091e1101080106 65
    0x2800320740101d4141da1116145c0302c016035a10380702c2c440c80781811201c0d40103c0140e40300d030f86d031804010b402030144c5814003d019240000058401c1c18004411304512001d40031b500d10001ca90002e00c2c902003413002828029151000c240d40e2549618002c00c1d0b03d404520000e080700c00460515403012084030b00400c0c0e8140e602110b58019100d0209404025044c001e161261000014450f070441c029611300c144101d10744189103141005110503500c0c0102181c0208004020805507a07039140402504400b042c1ca000440042802e10310004080342c2035541000100340491a00b0103500c102904c9085200b40c1c282c0300d0050b1000184000700d041080c030403807030241c00c200040311540c01e50780d01903100220450f9541080070300e4900c91040301880c140c241a140d01c40c41044140140440c8c850700d01c04082c81c10500c040c1d40900441602c102d0b4030001440940c4807022007003841030380c480f05c042c0a41d04028400c503031281444e092103024003425402e0b0116029000005819010310080903030000c48a8078 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 711728147 1250 711726897 711726907
    0x120b06060703120b04060315020c070b0306030729130801060506031e1312020c090c0a05092e2109020102190311060f1e06011d0105070204050f011811 66
    0x1c12006808504e0340b540d0072965449000010400402000320200c00480c001039036490a582030500307120084d000b08410381420414800380783c0300041e0100c1181c041150b200c0304107100c2c0c8110403043d017180001d070940340808100c00c07141c0c550503a901070417a040342d0001c002950740c034028002c19020031540c0c40c1d014140c111414102912822000780c0c4140242c5800e07801c280d89542d40b0580e00c005040c0c400c01a071010030600c4490510f04480c6802c1101c8402441c107007045004024014424a04018080c0120001c80e0700104804030040110f1040c0346064484c8501190f0028082a01c2d107004070407440c08026441c2d600c4d0400d05c1106030158041c1d001d00001c20b030030300079070382c00c043c11500840400040d0041c1c0c022640301408080d0240303166180d151003a0074803500a10280b810003001880001e00501400100c0c0c1e08180d1222020120424010391180c1c980010b84650040560180d0018100020044041032840b28141a01e62004420701180e4a10540c00d08031584ca4040ea1046202080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 711729397 1250 711728147 711728177
    0x220302030d050408090a0305030a090b030609041b030c0b09040c0f1211040f08330714071b08010f0e0312091204241b02010c030203090307120b06060703 67
    0x124a0f441400380e1181d600d005a0003011a00c540580d0348141c0b00c60300049802c60f0002e40c02400f6800420503800fa60b42141410000281e0880780540000c0c1000c504503e030100504100240340011500300c0003942c540d998035040e010b015480190b0b194821860304a81e5110240510305031445d45c0c10700c0d9500c2420000c0400d525004081e40e844481a40400f400001440d184540d44c00000c0e0903d14050584410140c13400c2c0a600304000428540c446440c503800d00c16016010000d038031401e07924105d400e80c020b0313980501c501d1143c840050400c0b42440352001e124070590380b04200300c4015030000c0000c41d0700044e81c2c100f291b800c0c08a100064208002e221591103404141640040022081d20044c03211080211407641c403a901c40c180d000440362a100d00a030890300300e09520883d600382091980021585000e030b403400c20030000d0502540100d000203140c406c209403005800058111182282c0303c6580480c0030520311011628400c4900010b00f541c284101074591484c2d15440e00090401040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 711730647 1250 711729397 711729401
    0xb04050c0a0f0e010509040905010b09013809130504020a0603020c0d08150406180b040b1018051c051b0102030418020c1204081506012001180b220302030d 68
    0x10241e04100382400502c41c1c0b91f956105034072407c3c1c407070800040c0042a01c01400320b48001684214240b10b61a4a0920301025144600b820034111500107001400c00d2017114072140104180e00d44c000340c45003400f400c0f2818603401540124021180c5848166850f1070860503485144019140c2d41c12084c0c1c0c812181d409101308680200c2c1e01c40d1145080744e051004141120481d511500c99080003200180101d02c1520030040200c009485c01c0c40700104000c01b041c2006800d02c920420040084d807075000c0e8021807038178000a0b102c000c0010045141140c85001d030106d0f02c0c00240d23824020015503007003805181c0c2d00200e000c031068015500342860202980780300801150300215240d001c202002c03540c4424004659000d541301c828581700d42c1806a0680f425440d441d118034419103003401d01c0300a82c1c1000c1c5010740300501c006207030b03851940d40c18480c7c00341035412016406841f107007207110100040c6544141c41030003134594031070110044407c580002d40800501130050b0300b04001940700107401d5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 711731897 1250 711730647 711730667
    0xb19090b030c030d030c230909060d050604030503161d090c0d111c2f040e040b041e0812102103080108070605040512010e0a060b04050c0a0f 62
    0x80550302d0b0a50341e8008682400a64051040020760350708040c461141c001d10107041c036150f100015602183c4da0705004806201301d0442c2172007564044c00189075076a43c20032208000794008261240c5090903d0050440d0704190f402c0c81144c803500600221180c410341015180c0c0b030a466445035050003050602204000103001004441d03801c0041010040c054040d0303181846100101c00d6445901078030356400c41c04031001d0741c4130841c20085c820f0352184000b5008409209003284100d5030000c1c14100d94000d101d96480002a030f00600100310a102100300035620441c041c2030a489900501c003800071800000740d000816440c03085c00f0001c0c01c4440354514961103082544607080403600d0300490441c01d46031080110752221545815402c069000361442e006201080050400382d04108014082c2d0140e40256405601d00f5a00600d400409400c51b2891000b5403080e105110040d00b414000b9002c5115564050341c20000410102c1039030404842e0400c030560784030302015808010403100500d00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 711733147 1250 711731897 711731899
    0x61503060f04090b07210504050c010e1f170907030f030c1a2a0f0405040222060c05150f061201090b1e160c03051e070b01030201030b19090b 62
    0x6100000e00000d0750804e40d041c00703001070b038071182c50310712201c140300710350700c180400070803102d4140780134440098000218680b04601c04d09003400d40104e41004100381490008070382c0a4070100c00e407182e000c07030b03004600103010400101c41c411040e52012800c44d40c0f0581d601c8014810200a0006400f1a108044003280c4510505180c040c03451209102c3c14440e4060329010004501149000410b01703c41885001198045085500340140c04180352801c0c052403003130703c1c012600020040790000071501507007428040318018003070709501e940b4010400342d06288112030501ca0061401d401101644500d1712501c5010304c034043c0c9640c0c0000f40b1603005d8044400b90a230b0344d01c0d481c03420002094102075900c28004101c0781c001c05401c1d503940e0001c00201900c000c0c0c064040c008000c01c6554044407903c8401e400d414a80d540d00410700140750030f108540740c009000c0b04081443c4081044000081d41242d000f66418085030008504200d0302c101c8080000310104607d0704100091001070b001081c2c4000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 711734397 1250 711733147 711733151
    0x503090907110304180510081f0f050a0203060112020403020a17031621080103232a040b01020303060d15110309060604150605040b1b03130e061503060f04 68
    0x80040b0824910342158210b0500d080f1000d5554908141c58440c09030300100540e81401443d15201c6126101d82c240c0303495003000c91800074498000d1342c00b43c1003d4092009040108264540110800d00940040c0c0d5410700040400d1804031041c6118001e41c0d003941d4000b0101c1da00a450401400c08045103004d00c2c08403030100b80030b607041a181c070403500c0036210f004244d18030611030286a0820500300c01e8034a18140a0710500620100d100d82220605100e5002c08520b00111550764540c40c105d003a035202030b0f40c504900784201e030b12144482140b0f400f6034203907130a01500001c0d400582e1a80001c9031916048140800b0000c0820442c3c034400800c0d03040b2440c00201840c2e50001c0c0211540300300c60590403540704109200c031300c0c2840e1050310856240303d103040118a0030a00b00500303a208038819490041c1d00440c031013107003500c01101c0007100d11150040340c1d550600d20702149520500d9103c0c1038007a83c0354800050403070072b00c0e0003070306011220081c90f04d10395070b148000c11820700c40006030203400c25 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 711735647 1250 711734397 711734417
    0xa110a060903170904090501091a0a140103021519050a0f0302031501030903110a080c0706050918061804030c0515060d080c010b0d0b15010e0901030f1103030d0e0111070503090907 79
    0x2d01f0a10a5900d00b5005000d014003800b8031a008c1011140080d12807801c031403030315400e803404411046102d41921340c11900400c0788194031000a070507014099404103d80c2ca018203030390410340c120005002220150320392100042400b501a0102c0c001100d1140460805880600d25980300e079000c0c0c21802d11906001c1110b50030114098900200c1605c200c8042c00001014a40c408040105500401e00303481d003541391000345008900410641c00c141c01d81315040402040c0d469840c0d41c02682c40112400003000145410b040080c001402c4c004c094425000300c6000714080b010390002d01c2d20a6102620f000001d1407250341d0200150705c80400142d01d95a11040700e8903d584240c40f18075154001c00140d07107c0d0034078002d90100c00340e04980550520003024100d100325210140d02c0c07411250054182c85560603141002d003100200f04030880d526001c001040d5052402070f900c510441800d1000030001d50030014181c00300d0340710301040946690302c103115100c1c0518100ba14250300c56014600038104c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 711736897 1250 711735647 711735653
    0x603170d060b040f03021201050c090607060204090207060902130903050a1817010b01020d02060103030e060702011b03050a09060905060301030602130f0f090b01031406130e0a110a06090317090409 86
    0xa41164111130555000c20508100303500d07051440e000400c1a031002000542010b04110000c0d00c0b84101c1c55002d107902068003021f11000d035050360001c1080303070000d56a800c074525083c0e00810703a48104030301c102242c600500d5000030340d20517003c3c0c0c203600d0784445191a100100549d014100340e81c40000903405590f0100d034201400c010740a803941c03803000214414083c070002a00307040d040c03900a021540018010030100e0717409070071300a1406040c0c9ea000c0c2d6441300f030b000485d0024586450b090f400f600c008510350806500400400040140b0780e141840c2d242c0f1540d0807a01c242091203050340c002414001400032a50560082039042c1c0d8100510f40415607507090390489944a502181d045030340000e0420220006001c2c6101c00503007442d00700910004030b901a4000000075240a003d00c00310b150303030319a00041d41c0c000404110b441d000c6443c80030300b502e089075140d00845030700760103184010400200c0310f026240200036a580000080301020614a4000ca5500003088965003d500c4010310808 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 711738147 1250 711736897 711736919
    0x2209031413090203181e06071e0e0117040c081b01021f15030510061a070b090111130504110a0906110c090405030c01200901141306080f09010603170d06 67
    0x3060104074486e040421401592810f1203c028000e074180040c842d40e80d8120210b940c01c00c18031107060f00740b00140714840740040301c4a940320000703036034020301c40030074882031010030b010f0a02100c166001711411502c0d0414010460f2000a40711409039009548400742c0740440b900c00d208040c1100400122a50105254050b556190b0310584054000d162800098145030103418064900d40c0d800419140c00d280114005104912025100394410382c0450740b1800c0a4211203500c040001d41240c441c80d0050f103501380c2140e03600c1785600c00c520b00514024080e000384251000881942c4408030580d140040c1690015850480e410090140f400c001c0a255200642103004c1c900500045403a610100400c40c2101d242040f150b0100b0b0070030341400380d00407021084691041080c60a030942ca501400c6010307a81c0520600501c5941c90070401040041e030000d50107114039090140080540c42c1c4200240c01c0310a24000134000d400c550b0404101c40352003800800005601c0038001030507d54900200c02 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 711739397 1250 711738147 711738163
    0x2070f0501090b0708060306040b0a0911040f0b0f040603030504030f0309180c0305090f03031b09040903020a051902030606061b07091d031314220903141309020318 72
    0x15201c3c00d100030300c044154840021a8844800e0f00100300070304040e00e5060161400410380f00395161103104840400a00e2103000e144410041c100380558103400d204540581110103038140607000c0310720780c1c544e6458540a003008a03901602d60074605800c503250002403007070104096080c46401e800008160301d50703030414584221075420000d028099004002e06503400600380040030f40c80441c250095607404412245c01455a41e10301c02611981540b0f9482409040341080e0701c00d00e4440018181600410a01c0e00e0922403c2a24501c43e00d668100c10b00302c40c0002e001e900340d0300000c00030b480790030300320014000180302565041201c0025034a01d860000590019140d003512101150301d01c19005100c5541c4d403040c000907600b000d074003c1c0e41006103a481d00c101043c00308aa80b00d8a40c680f90100380303040c41d90000c016041c480069801c5040035208105e0203c0005207660300c13400c00c28034840113031180e0f001e424220343c0c0301030326051000d4041e4001802c407030b06240034075000c0c3c400040f082100003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 711740647 1250 711739397 711739403
    0x70b03040807020907051e2203061a03061302090403052203051b01050d090206070203030325030c0219060e0109030201050402030c0604051c03030204210c050a0602030d02070f050109 80
    0x10b40d902d0442c8144075040d6005005001844018045044103250040c20300a01d070304107040a42d280c800e003050100040e104440c0b802d9420300b140102100f801515000007401500b24841d00c1080741c0c0441c14142d99241c2141d0fa07601d00760b42c05580134010702c0d0070205103400500900e00b0750b0501c0b05c2d40e104480710110f03145004014401c3d491080080000c1800002d190000d03032141e045084541c6c03c00640584620800550880d45e1145a00115604c02050f13480180c2c001e002c4070740b2440c01014044d01300d00302d161410f0450403900801c0070030510a004080203c140c5a01070301100d9003900280030030038028141110304988840b4103c01c0c0740e109200340081e0b03900036070000c11603090600506050481c60361005010f080c0c100f105100ea9183d880a000d00001700c403d40558544040c10120001d000e9504031094100c01a40c11f0501800b046540c0039240f8054a0a5070440f540c071001c0100c034441c94070400d40981c200b400002c134880d003140c2c094082d01d40299551042181c0c2903a40d40e0849520316030803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 711741897 1250 711740647 711740663
    0x170c040b0a030e0f1b06031012030f080907030807030f1112210105100c0501140a05191a0d0c05060c24010303050306040c02161511030f041205070b0304 67
    0x2034001203e0070040c050030807052001a2120600602459086120810289000308400004200d10b90a84559103005100717000d00f940001555180061034044880a020005100300021645044000c1812030850780e0268800d8175007101a60151091891240d01d48107001c0041140808004107101407002d00c0840c440c080d5441c03441510500c1e8107015007481088150801c8014009c507140c00c6844103180415040140c0d00e0401881c1003800340400b592541d01c0c000e044024800480c546401c10350003000f81c02086040c01c0c0901c44840d04980c0410001e001c80c032125030701d201c1c0300c1c2000c0e001440494095074682500b00d0b281d00108030320342c1c00360b40c00ca28103910000265681d43e14500044108090700c25a562880d4913586000700700d0300002e0b18052040e5558211000b5403070082102c0c14400c1128000c00003141d035110340810364a401300c1141030204100000340151400044201c400c0d038801880c03a982020f041c0009030070741d501220400c072007900c42d5820110f0580381040146110381d21401c0b00c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 711743147 1250 711741897 711741911
    0x4020d0c030606170609120309101a1f2003040f14010306050105160204151706012c040f0501061707030204060609260705121516170c040b0a03 63
    0x2041e444900c0c010b8a07600d440c1c00c08011b00140250204145416944074180e040c0c0745d8039003001160a0a20340e28009094030302e0488040d5208110910014118504842000c05502011085071070043c18006440000d0384000040c400c41e614181500444e0b41043e04036800c158940320009282110390b0007003200001c00c013100d19629030b030500640010f80001c0c83c04e40c1c10324201c400036042038500840024030560712510b5100c09a440d020b00c200c014145103809550049494060980f01d00e030030b004204405030214030b06000401286440c03082c2150414031306026590f5a00e40d003800740114801164995214800042d4803602100c01c00d03038850003440a801c0c1549107204000444685900500501c0402041003000e988440d404109080080c180b2040308142080b880342400b4903034001039401107146500180346200041c50002e0500d41001c1c00e0f08540710001d60b818101910159800040c02c500b030900300600300f20300f600d600095000503003801c1039260118039900f50004900d0600007a9180a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 711744397 1250 711743147 711743159
    0x30305090d0f0207030602090621072c0111030c0703230d120c0c05060c0405040f0b030a0813091a040f050c161506031b060908100504020d0c030606 65
    0x2503184401e049080038036080c0160700000e5207640841c40082c1035158085103001c040e1300d4090898840b2580c1c3c11300440c100306000034280303c2c9141075036503000140c0e1203d10210100010340511000009911040007801c440500448004081550010050105026295a501c4200701c8940554401c0c03481c0003044292420001e09041c90301420103a5600c02c1707094501d083c1d0401c140c00050031041c03801044c002810130040e594614800c0d401002881103408008421007084083c0058a004440a103d0141c5c1c495000090311040c8800350760640001c5011000141d0020044c40300d10b860712007980c04265241c0038801203407514000c90521107007240c4465030341c1c6002c1c49490010702d002003081140342014000d448140c0260ac0100e002c0490803a00e92081c00004c101101d0160f01141040c03148940742e242140703071046642001c2c2c06440001e071000c16141e00032241c48081d02c25040003012883c1d00303500c04101500e406007081e60804400e000002c041000c00c0050000b0b580560303404130b1282c1c5012 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 711745647 1250 711744397 711744403
    0x1d0f1906110310240c140309030a110a120b130c0b030c0405043b0f1c0306170c060306040f0c020d23030103020603040c0819050106050d11042703030509 67
    0x1c04100c007113401001d144240305411600784202c01307411242e00e05680c114035960900d944a00001c140c0c0c588610b1520804000b0307545850965118181c40c00292070741d84110300d112008940788010b2103400c407040055034100c2c08c03000d081c0c802d60041c00ca100c0004d549103640000c950054031521001c9034009400d100d90f00380340c0209006035010450b82001008169000c585900c030540e1707041c80320741064180a824840401003000741c403d0709415100301803501d80d4900c4500b01d00940020111303003809800113510300803601c242503400c07804001e8441101403504105c1544d0008000c6540183d42e140340c0306600002d84a0300c03001d940203030000c4c000760350078140183ca42039801c407030241640c40100080e01c00c150a5420b803411254180c03030f4161030b0340341c40c9407001e00f04c07030142c100c01030f148910040c3e0780c84030401102c5a8203441c081c20080001a4445081c410340b03144609000d080403640750710024082c10282e006252004040011042d1050b1041c40d03000e40303c000d03500c1071b00029103443c28081e2940f414 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 711746897 1250 711745647 711745679
    0x71515060804260d29031b01030f020406020106081c02210f030106170108070b0a0809070914010e010b0414060c0a060f02070c050306040308180a0b07031d0f1906110310 74
    0x80b03540305e589200000003076540103440368060030704003601640e5140381d00079004401a40c0d804001507440c0d607102c2c407009000f40305500c6610000e00c580414001c804501c03004441ca0290ba95001d80310310102050714001e0303900c1c041144100c3d07171020400a0b45810240c0c01131800f81c00070b07035a07a000c220101946400306075030603080401550040c0000300428510041200e45441903828000160f41e901d0080d02d0a05105a12124507141451401c00c40700c4004a0740905030b4101c401d4144075030341c031450811400c0c0120301485902070500c4e0341c81c60240c039000001e8116000002c0c22651081d0031943c801041e18450101c4008142d0085070102c20040055a0200a400709800500301407900d030b10020b0401a000e010803004071002002260450070500c1400d0030a50032000c42000380c1809000140101a18070070503e051299098100000d1404286013105115210017400c0050390724244186250340780800b00d030b40d141d4034250514010359103030107103100c1c0c4032404800880d20320b002c445806018507 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 711748147 1250 711746897 711746951
    0x303080f1f1509030507060309021509010e01121d01021c02070206090114070605040506060f010813082b06051f080f04030311071515060804260d 64
    0x80c01d140031500c4503000c038803401140c0300c0b4011100407880c04402990020345580000d405401162008036181d90980c204070405031080d03602c1c50800340c110b030701e102e043d0007202151400698100b10082e1198410407240c0480002c10744d0018580000c0c0104c0003603401e032282c41030500d03500070030744000c02210070700004000051460250715000380b640c0000d40a00c00c402c0386505100201180121a00c02103041d0341e810303580590b0820443c101790600c280d4801c0103c45c800d00c00ca0b191140f414455103c0d6603044e004044d01c100e02024103650f5521141706800420310090540c9015064035440c11404107008020301820500088490804040c040c0c039802000c054040e00c0d002c00141c0e427040380d0010b20f95500100d036100039000354840703140c128060000d0003100f001d4a00007050000074404002004510400f80710801c000e98402c01c080000e0b5180184603a10126400f80c0c009008100045045440c0d103002d040400700c40d07640082c5502940d0040300c0d000300311030741c2e519024103021f9923218a0084143c07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 711749397 1250 711748147 711748171
    0x3120e0a061a0d15110c120405041a031f0b2e030c05030705180a0b13090c0e2107080312060a1206020a020109021c020f060310150212040303080f 64
    0x8513440d4a002c4540000b401c2441556031505070200315012410f4424841e03000c0c050740d00314134450b0b80b19001a000343c00342a10413441d002d240100c80d080b4064074451820041c01400c0c0403d4210242c4840c40300b43c0044130000b544400003028140d46200c215612240d00d011020b181c0d15041c10b0b07081d010340101c0320b05414185410480680940c01a081d20703403008181ca04a959042c28a10907a4950000b6005ca600301800040c0481e1300700b075100c05400c011a040c0d42804404d03646015540c00d86100d100144045096801c1c1e07a041c44c1003992110382d082007003001d01030416460360002271820f04181d01a001a41011480d240300d022240c2c1c41a4101600700c4034000d1542c140100750b05001e6464800400e41640010842c030043d000307411405110740c00810411010110341c0c910b03109030001d800103d11402070501c00600a00d40801174034020704100002030072050510014103038030042c0030f00c40c07000d5100300000305c44407441200040c4082e620a03170781c0c2004c9003841801d4140102020306941c607101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 711750647 1250 711749397 711749419
    0x1505041e0e01091a07110303070c12030b01051c0207050304090209011d010210051806041223030f040507230108161409040b1309030e190303120e0a061a 67
    0x42c404940514445000c02c03034459071511170140944000350b2041008481b40408800c0000c9190040c5062020300d0103800529034251030a141141101d240e240d2260101d5070a01c0041704040c0b803401f00761283c15035000014900405511814555009a0300c12909aa00000c180e0381c1540e0116a10100b07149088800b01030300d80100000c4d440300d1241058a00705a0784400103044d034080e50140704902ea10441c00d880c0d42d401d0500741040c100d000302c024080801d022040b040c0003c000c415461540381c032802292820b40d00e44480c11508200060020348441c89000700216801050952560041d0109151000303855080000548070b80001400101c1c412a0305000e6481260809101c40000c05050822540e482861001400500b13040070b0460f0459401281003004c0f01d081e90054a15a0207600d070382e0341e00d0f0768260400c4a0b40c1003014024082510141d81080007a0041c06138155020b03202c0c402040002c10008014645001981c042c1c80d907a80321288444101400b03404410048410b0741d01102d24 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 711751897 1250 711750647 711750653
    0x19020a11090f0a020913150501110d050301061d1f021c1d0d0506010611060c030708060d2111011d070608070207030605041b05090c04060c1502040611061005131505041e0e0109 77
    0x602051103a0814002c25002803400d411001115260050008001040741801800aa003501c01050910804b6100d00401d4070144103240c840889800440e9548800d400300a910222440e0580341081f508215190340d43e200180e001d02c03d940c041d10403a504d00110b4100109100d260490107002c0020012041040c040d1865001c08815880ba02c25078000e07072260022f01d0004401810491003960781c8a0005440700c90940c0b00c00b00300c0e0078829240003070040080c00464000301e01b506140c843c1c090352000e0020003802e401907101940c09607272401030354600b50340c1e80c0714071042d150215400c50700301d03c0159403411824580c81d40c05001d0171303060b549084d50f80f91204006845201720702401c414801d2084500c41003002d04501840c0b0042286029512150350307031005031151612000074151802881c0015400c08045102031045039070091104000c242c0780f40440d4000e001c50312800300c04102094000c03985403103074003d40303c0b1000d50b040c0740c654182c1a480520300300c0d40c0d8150792281c0d990402c42d501c0c000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 711753147 1250 711751897 711751907
    0xb0a0f030504022d060f0703112b09050916030e071a090d02060a08040221030403031d19051e0d02060f19020a11090f0a020913150501110d 61
    0x100c0003403c000d40044180900b15204005503a044c2603501c4140040c4020648565002500c0601d00c070361a06031101c110b07030680300c1e12040810100b040c0d200012500e040050b00d44d501109080945007483c5c1010381e151760100d07540702801c44d503039000b14110413000c400b100c0c1d042c4074041e89888860302404c806410a186a2040040895203115080c40440c0c03080396555001074201ca001d40c010300a039941c8411440103851a0021070302640718841c0440443d041180c43c1e11206603510903500558602400c41d41c1c181c0e802c1d07685074101148801040500c00d41901c9126550102200780320310300114a19003c00c0100c030102e102c206e03c0c0c2000550303064200303540716550281221039045498640790611400300d541ca500031110a09038a04040ea8040000b076008240044214050545001c2c15803155081c0600c5441c203880182017220304000062004000d5405810080801011404040300d000e0310703603042e5034034804e0200540c132008100b0801d941c5c204980c0c400314410b403400792440000340400500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 711754397 1250 711753147 711753169
    0x20a1401020c06090a0e1e01120b271509120906070b040809090109050601090902071509140a1406094606021c06051023040b0a0f03050402 61
    0x1004a0300402c100c044c1c1c0d80d0b10b095803806064441ea18a20320300e8103400481c4001c040100103050849840c00219050310404910360150303402c8030034250f99450300c042c118820312807a1912400c90224001c00d5002040c213010702e000204681003001581d003489502c5038144000740c80a600b141c0005c02804190b6180d0078150362071030b604104440140d44e02d40c10141c0d80da00c035801860394040d40440001c1490313480d03a40214004c2400783c0e5013458964440166104a105402010b40b00c0340925050b10441360b40d03031f003140c00424410900410b000c41074810341443e1820201c0101c0c0c414220192031051000e0800c0003990006480000b0700c803080040d5103003513400c41800380c98081c0c0d101c07490341888419200d00244c882c0b158a200b03d00c030a04042d0400100941044071800140c5080c00c4211611080500846043d1a00102290711100c502e440c19a1004c620031003001a101000c941c12582d00a140040c000508900004603940c401070000103007445290100c1c0811b01d8a85000e000140c2c440114480e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 711755647 1250 711754397 711754399
    0x9060b210c091801090f0c0504050417070201021e1014011505130f06080405010c03090503032805040c051f020607030b040e010501030302070f08010b0d08090105070b070507020a1401020c 82
    0x1403094403500761150002400f500007180035804c1c06106400c000e0002c49103c002070217a8002d108a5403260b04001c05e81c0e40c03c0c4c5021f02121480c50108464110400080801c130f8414012510844217024400b901c080c04141c000103103801c00c2c09444030703520041c01003454151046030540202d42c1010707070501140040d150200b0030024040307507039810308072030000d1040604104060820416510314000f002c0c80d600b00c2d81261294244402c03440303214041d024219100b54003901071800c60340c40c01040d9040d920704151100b41c011041c8247d18001c2d0f070038807076107001d01d000f01403081d445801d141c14010140c8558016541c410180c80c204074880307901207a5a500f0803403510300420742c1685003000401a01c0920680d070800d5182c84000410190001144e00454003000840c000450b038402c0d01c60f013281c0c92500d43c19001550380400200240d1040d006120000b41418440d08007086a00d514480060445040000c60700006042096180000c0c450008101c9040c0202a4204040000f5110701c1e85036001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 711756897 1250 711755647 711755659
    0x60903080a0c0314030a02040906150c02090a0603170d11130e07090504230a0b0102060103170c030307231813110d05160203030c0a08040c050409060b210c 68
    0x10b0415101d07541c0b0301140c1d90208a03480d02c03410900303c03090080d8891b02ca25174036517117406800a0500041c07031404042c0161034444c581401207a17000c0c0700d50500000d03e2030544554903140440000c0e403480301d58800035100701184c0c0d200c2c0b5028400c01e0890301251400c14051905100d048a4a404000000159041c1c184000c6454a6098080da603e803c65084030b6801814003601c40c4012840c058070050700e0f006c1c2c2c90b4040154480e4101402220b061050082c0140c10007401800413880035034010303205a04030100c0c1c42c5003182e00a0070324250b400c155480070006000d441080b4a05000346420301320290100318962500c051a01d45031026100071681074010b00c010039000d26092a150310444030500d0f0000095950400041403400501045a400b6a5040151000c445052002003038901c1000d0f0b0380102e52911500140a4030500c41c01402103d21030707407410011645171078500841078500d12503100408c808000500300050307041402803d14080d4400c4c80b285a00e8100002c041503400c40594107 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 711758147 1250 711756897 711756917
    0xb07020303121305010c050f0d1d030c072c040b0a0f06090b01080a020408061324050103060e0c010203090613030b180d050c0606010f020c090f010f060903080a 70
    0x30034154002c0b007200c04000e9400d80100f00c400008034101412041c814802041a114254025990360061640e912681e02e4240460f50014074180d00c645100f5005542d07403800000307540c2685142d64000c0e840048107400043e000c1280f42c03220948040400700d0b805904054902d41c28400d0a0184d0050003d031851050101081c000101d50340701c54050b1100748014131160780c0b2030600c0c0c4040e0490540e02c43c0000c80f07800016420140e90300c00d8509407602c4c13001406594942e11400046104410b8041e541e24400040400725850700001c2440c490100c510040740c59071544c00d0850403a040302201034a0307030708841000e40302e50383d02008540550000704c0d20244c40b080480700088594110743c00060dc40344110050000d0a41009000c0414030360340421920740b2240f40d8001c441c1c40c00b6400c43d0041d940d10a4001c110030798040c400b824082a031074411550300b00000400101000c070709403200074400c1107240040c0548013004401074064606802c05042003031542c0c1e95407100b4460100d0140c1044a4054 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 711759397 1250 711758147 711758149
    0x603030d0f020d09060501050109050609030604020d03270501110a0b160c020a03060204141009060f26090c18010b07170307050d0c0f0e090a020c0a08040509130209010b0702 76
    0x410340d0311070440d8103001c005010080c85d151000f03201c280905030200700b840c1d6000583e0300d4104100c504a04016020b004142c986609020018010300c804a0511209020410507401000c0c821540c10481001c0109007500e0000054441270702417000203031540055032150701103405d502c01e16401020041901240c110514412a60f1444402c0d000798004010b14001091004a070041c0060303c2140c8440d128030236490f002c100c40c00b031105c0c0781e03180400c030244420000103004501100d620101411310300c1ea00c0b4440206405000c0c600140b00c2c80e110214010300040d100f0420194400d0041034a40e07064a00060750900713a60841445031021020300001c03501c04200d0803142e0300070300b01c0240320300b030352a402d1000004c1c00941040580b560f1003031501138030321905881411040840c0d07019440b6182825241700500407180d40052440c440306030200400c5413001030410142030524022003c85885500b41410803030030300b4000c0d10390700c800ca05613409500540d54a52400781160741c0301c0215035486801e44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 711760647 1250 711759397 711759401
    0x81e06010216030f0b0105060301050d2907031b03050c1c1d28110405090f0706120614030613050a150509150c030c220b130605030603030d0f 62
    0x307019100d542d04100d400420014000718204829104031881101c5a894600b03109031800240300c0c0541c0410340d41240301c08140203040741c02a030850b4156181641c110f010a01c0c8040c5000d9590a00090344c95814071821103420121343d90310300c0e60349400d1040c1d052015a070342403802094880e00c0344005180da40c00c14510b26134058130b004140e01d148000756003c0980c000c0e403101c4501504c42d12109424005420702d0942341001084690711043e011250141001400001d010080c4110510301c1000824400100d007045244020041307940d584091025690000060302e00940c0700203403440100022201e1950082034803a803008119100310140380c0c0c28101585041e070385000241800c00d9074100d0108140650308031600c11001c40b022242072009030f007030b000000c49040303c082d1030140c41400429540c0d10307000b0007001488800c03903c100e9101e4a00b8500d55240825030305c40c0c4d001c4000051882190286601050010b060f0390400c00d0452428a002c40d859100b040c2001d45099a125200c0351034900c15 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 711761897 1250 711760647 711760663
    0x1602150a0204410f15070b0103030206090607020a020a0b030606070c090e0d09030b040f0321051b071109090a0b01181404050319050f0307030f0605100e0d0503190e10081e060102 78
    0x1f0006241d940e40f8180691a4502614403001500032076000445441c00026484030440d80a8207010010f49008142d00f0960400f030322460784400200444800304105043e10700240c0001800010802c120700740303513480d11105212031410f0241c24034041010900305e45185d5809604840681c2c0029114030f021104a5081e444200c1c2c11200800c500307004686982c4410b1041c00c641c025840b001c075001000610a001e0319000402460984903c44a54101140003540050120040302c0c602440395a65040c1c0c41c0090700000840c0680c8481030004c0200f5018031622840b921000c5041400c1a07210991a442051207910510300d88028804500344164200c3d00700300d5a5022142d101d051014008001e010340e46501c0c403065060400106003450304400020400825071204c00c1680c4102040c4820182d6564050721180007d0040301c2c504554034814681440d807503510722040201c0d040401c413242105064240411083c401000084540e142e100341302c014495104048603510180100d180c0109 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 711763147 1250 711761897 711761903
    0x8030a110406091a030108031e0d0905030904110301120809062104020405091f0b04020c12030901181a090a0c0b121602150a0204410f1507 61
    0x30000740090441c1d44000720105842113200c8038442d2050b080ca443d6124007081c010305a841d041042000c152408003c116501007001c103507d80d0030a07014480302007c80700b0050055a131900006524012441d141c8111030500c481c40450354110350400c01014005429680c0003411801d0000c1c0c500455610034041e2185801c40305490030b4038100001660002d480c041e20304070f000e02e0429001c19004100070070354415102c03003200044008031038803001e00050f08141e442150080d60801c00d80e200c0210610402c81134604002400355282040c0000c142103680038001c07845420601801c41c00024060b1100705c40000311000c00c050b00380c0706e030540c0d541001c0880000900c00e48490780d000603c184203001822100c0c00e20509403159070744409209181d80614220b080058002402e4800300c0e10a551085401002c0d8500041c240b41d03d8404541c03201d401650295010f08003081071980d29003042004c648420580c81c0301c00c00000240300403500da018194020b42c0301e034142d1079800c40641d58001c143c85005030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 711764397 1250 711763147 711763181
    0x150f04030f020102010b10020606010f03091b0f060f0c03030b040219110708010605131e1a1005071104052e060e030601240509030d0906020618060408030a 68
    0x16403494a03071207030350340948200e015500300100c020071440c1140b000c002c009180d0300a00030360303512030004540d41350081d00e000c4241555034103a40e000c170b00000c1c514000305130700c81070b403c070681e040880303e0710840f42d968450310070070004103405c42210f94466041e2004580c141404910b43c88014000340280c05001107a440c801c502c42010110300b6445200c0c469100e01450684041c1e94030b564280d42604c10394050039400c181c160200c0780c3c44032807a5100b002c1001540c0b003864280011024080c00741c55101400088007240d000c16004c2915109081e95140304c402d0812a00d46000c0c0c1d650380d83c25141c1c00304198821a902c1c0f000501e6002440754020191010b01701d601d4088899410003889000903000b40f500040c81c0c583c0c140002c0c03d00084190584101e4078165610400c0303010401d00000f00310f5000b0301048030034880c8140d951410408485040030b141c4805000c54100b8800a181610003040c1d00f41142d50704042c1d140071080440c440e0340158008032080c0d601e03501c40c13000c040500400703191103960341 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 711765647 1250 711764397 711764399
    0x305060a03061a09010909081902010e07060f09060806030a02041d0a140601050a05090a150509010806070305091b0904020f06070515011a09190e0108030d0608120405150f04 76
    0x911180c480a4585a0440d03088541e170b45c840c8910821100b01c15001060b50b14100f04401c004418401c048210190900c00841c0341c03804032000074100409648014003080a03039090348507030390f004074501e409403046d4907040c5610b10f00f500000c0d0307603010702d0900a80955540c01b400d9800b0384458940304100306130032046130350400452034890048910001c10f1926401a0000498985009030007a4122440140052500d480e001d4281008009c09844024841b40003500051540c403003a850a000b480b03910060040d500c0e1510000d0280c0340b000340b2000e09500194070001c1d4400c00e4032006000f004c8242c855a00c103a03154404a09802e00d00c56682e54885400300e0707000f041000001e60303c00200081110034403166a1120742c5191400a0345010895400034070000100342040c91821507410303850303040d800c030056a504041404803005c1e081201c05400004034000d902c46a80507550051401200800040c0c091340340314000c82c041d40c002c1903c40c002c08614841c1c10025101515071500000401e25519 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 711766897 1250 711765647 711765671
    0x90c1509010207170a0302011d12130e0103080c0c100906180f0906030c0608150603060301090f140118020603270715121404060c110105100503061303050a0305060a0306 74
    0x152000d185c11001036080c5940c02d107418840c24000e050410f0b82d10b004000b8444040311b000d41d00d8102182d054550244400000f42242c19107110074001c601030304045035542d50f02e0300c900341444140c19901c0d00a542030500450b031240d000064400300c0c0c80e1407900e01d84442c0e6041501c00780d401c031070780403198010324041c0c007180c40c04455004070101c03482010500c000658642d42070b00c1c80d42c1d040710845022110903c0c04089030030034500440d401a001400042d90074456580c072014900103900c1520610b80800100c600d00c0024455045c1d544103990f05c00700d1201c016800541d403480010010054500c10010503444980461402c20000f54a801545c200d81c0d00e071540445009004c201c03032070000d100c2110400b055002882009004509044e42820650310341d00c891020f0103007000300c581080707040c08d5042c041510030301c10103001d00d5550007041d40103480d05d410103103480c4002e00080b0a08041c0011400000d0b0080c0441c2c825040900300070509949290009203a2120380d030026000f1410041e8040340 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 711768147 1250 711766897 711766903
    0xa110d0b011701150b09060d06080a031e09230a03080304050d0e0a030807030c0821040c0b090a03140c180603010510080d1805030d17090c150901020717 67
    0x342d00004000304241c0f03030742240c295004003281c8101d03003030403404102140309820007d0061402c2c6c209074801080d543d948000152805405004c203a000480c050440c01140c84001d0300a01c000d05540b41c100002070030001040a00c00440c4001e80c09507900070100c10f01511101e510400942d0000300c5540c40349441c0c2003450301c40701d0041c0004006502c2e4080e14002d440c1422004084d83d07003102e0090700f002171954042d5048401444140d83c6050288500ca02618011341081c280d00c01c100e5044010782001c2c50000300324042d507000796440030801e00034100140c8030b002195007200c0d00003182e034149004060081381001102403042d0780080d0410551b50030307155041c6206004000c01d0b030081055540b142441c2c1c0c4c41c1c0e0814040c10700c0c0741d0064800c40d04440d02c1410040c0072030301000c140704200b5a03130b5400640f41c120070024960204044203c24510241d00440d6140e0000c00320020b0314100a006001a82407038200f82019000d200205034910107910130400303440502041c0c41c1041210100d83c0c05255 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 711769397 1250 711768147 711768179
    0x617180604051f09030905090406290310090f171c0509060906090d03020a1e170703020f030f04031817160f063504030e060c0a110d0b01 60
    0x30010240c02200c3d4000702d5140709115403d60541c3e103400c01541000c0c10001e42d84405002034480c55151001c4056061906c640d030090341c400918462000c013400014141804c0f00c21030180e400c40c0ca4031803241d0100746e000010f542001e81c0402d11050070700075803981c120366005030070b0302510070b09003175240c00300848d06130f0302842c0914a03541c1202c2241d62100c40f0640e03210011242561260403500d1000200c900940103403040039401e0907c1c0d401c0010a00d41084003e9050800400044142c920f80413103082e004d264540291081c80d095103003d0440d41100d01ca88800342c45082d032a00000005001d15108400162a0030118040c400c02c259a46108006a001e251501e00d424040c82c0d4128005540c1d504130003080754990750198160f280b40010a5600342161803001d00c03001003804103440d4081880d0392008081c00d0144e9001c0440c24241401801c8500c0142028001d040811019002030000140040000e6020007407050303000c03003000407a142d003021180c010301d0100058004100740e04000410a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 711770647 1250 711769397 711769423
    0x70f0504090c1701090e12251a07050f12330109080102070203100b010e120f1603030c061d07030503030105031504020904030e0a1a0c01060b04061718060405 69
    0x6003007070340c0f50038801003141c02210030140c041c1c1c03003203e590036101203000c042e00b0031602000a0b00a541d48c040a0f2910404194a0894001d101d0071108040c44654101180e0810514a095401c04103440002c400511a0382d0300c1c850071040880028881d4054504054014a90000c0d442406202c00d0702c0700100c9181240c3c0e05020a1b1840c80114205d2414403e842480b500200101140e4400b01f5400006183c40c4840504210028040b40300c240c8500e22200c5001000b04010420310043c4000d060824050207003c00303140f01c8401d81000440d0b40144180c5c00e083e0040c2c40020300311070950400c00c0c82100c0c2e513803080305401000c41c004280000880550304a0314103405079481900304145219403080100c5000390701c46134190200c1c0201e8420303640082040c030094645001c01d901c904c40c0c5003400e5401c0c80320070b40c2c9810010740030520f004203005083c002c04142100c641041d05152024240d040c004000200c0908074200103242000d202080418916481081c1c0c2c40d0350809040107503d8a4070103102e0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 711771897 1250 711770647 711770687
    0xb0c010c02070b0906070f020f0301020f0406090b03040845040b090c1e0c100507120903090b16080a0305100806040f1e060e0c03120f03070f0504090c 66
    0x55024852049504115008000742d06c1e00040d43d13540001107244000a0341c00111131031010310180c8091004000f42c01c495440c0c9900c0300d2078035200070842c1c002c50308000741000d030600a01001179400c40c16030300d0700314a002c0c1071441c41c50030030b84130002000300806001c7c0e240d541000441c4c500203010109401103601380c4060001040140070711006050a403a0350807014810458082c6940442c0000000d0042c80c40e0340c1807800d03410000e202c3c41d0407038403c0d18212080e6108140800650841c135000c40c0281c0d41c25080c4001120780c1c8024100c600544644441d5903000590b40e08501d14062915165a030300020454030b03401d84140003030061204039094a0005542d4002040d03072940003490600c103d5020f5202000020f1030759401da050804805811190290340b59054000703003c42c0220088010030308014a130030f0a01c0b40405141115983c480d0886000c10855009038001c94000c50b0b5000055003406081038605100c02c45451140d0340c40622028601044041c0080d0b121002031081c0c0906105 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 711773147 1250 711771897 711771899
    0xa0e07110319030b0a1e05010e040b0d020111030708120601090512061512030c012901090b131e090b060c0a030309080d110309060106090b041701060b0c010c0207 71
    0x12150341e4821605292248030440b4038410140e4802d800071035984802404c003200080d5207412120701071841d01c1c1042103624401c02d0900103540d0100d00081410343c101d50501c01c4174405c2020804401c503003000641048a981504095287d040044611b020761110003240c0c0d4003e07106201c03e030a00e0503901303039000480c80340340060145810218130022105640103044a901c804502204108070f02e0401030b00500a094003c44295041c000303440e50704545e20000c194201d000180f0700300018840c0c02c2519210704010002e034141da00030014416650010503c0360781c0c0c8888460001e194103207074068800306c1c1d00c0074849040d5400c2003000804841d40702d0000d00c0030a102c8010071031b660180c0a01030040b84e10102040c404284030390400c91207d8000e02c511351801d00c00f0300c1c0d01420b0303811600050321041c000000380304420b8010040d41e4010700d00c41c81c0c0304108504107101c0002911491142080c5d120543d06003520460f82035100c0c800521807103624940c0d0318403030803840d0302a0817600d4000025008000b0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 711774397 1250 711773147 711773177
    0x2a0e0613090e030708040b03310b01270209060702091806070807050a080411100302070201080112030e0105070813030f061b080712020c0105010608010f270c030b0a0e07 74
    0x4d60b41c90980c4565200e0500d420081119002d400c000c12007108090300d120b40090341c0324a0504044844003d100010340c3c40500d00300810340040c181c2c00100c481d01921a0300b2032a80000b44c0e404d50803004241301580d2032209000242d0310780a15000651b020380c0302d00c140224840d6500c81ca0314030610040550340550f84032241078602080840300f15012640c2000003c0c011480707600400c0c1d0141c4240841500340c080d00c40800c01e101c41c610424400b0960000d1100c0556070003102d528010030030300544039101a21650018000c2c204111018103101007c1501c034200051882070751558030084410085070350340d0b0304045003403001f001c000791031052420f2460584009041160602010b07552107201c816220f001048620703214440ea228219982800000040d00080c02503d000f072125551b0490f07254103107412600580407075800300302031144125501c6c1c6031a601d1840015201401c2c040042d40701c4c00c968040e000f8101e8070207290b500898000307022601b440a1240140645502d1380ca41c412048184 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 711775647 1250 711774397 711774403
    0x33050f030a06050a0e12030c0711010c1406060112021303110109030f03020106152303090a080412030f05071509020d05100c0305130201020a120e130c030b042a0e0613090e 75
    0x80c81184801d401009500c0c0414003181d281da68900041c54841d1407500e26407104dc0a41c5040405204183c000006100056a011400501100d03591100b10b01d402c510b605490317206003072888000e081c10764098603100a40e00a03440c410046d90000c44000e40300d52141b90090003010a8095002d03040d504944d101c2c45c0c0c134400d258010500f554414039030360030048000d101c14242c1005184800c5481840c101800050074503014000801500e4800c00c4035624526001d452041c1a00546c402c04c8400d01007180821051003d02d922903000c41400503d4090740c1c00850740700301d00250060110310414814003824142e551100003546440e41d42085103481d406600d000308000000c0190059000103045800700703440000480d51034000d41032618540b0031100c0030401508204210f090615a1344546a0150781c060003059030030903045404000270364808412004405030111001c108104005040301114005c480d0016040001404161031302c0e0103103009070318440c0782d000728440242481c20440d4590000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 711776897 1250 711775647 711775651
    0x602070305010524041a0613080c030a0506150105070b04110f0303040609051302070b0106080a0e03040515160501052d01060516030c0b070333050f030a06050a0e1203 73
    0x80c41130400007800d040e0810028002ca0740750901e40031040101d805041e42c4010080101c4414143e410341c4043c40d140e60603040458250082c1d00940108074010001580414074a0340920f0064000314540300b04001280c2d14080c0072360040081100e03000b440140000e000c003180c1e000d48122a41ea04811011084c5038680c002c620039080824600b0340c060201e13103030418013034041644013000181442c00759118100c14000030303071241c404160424280140d154060007044408103001006500c0d10745001c001c87c0d401c60640c205e60380d402c40c3c04030344118a01066002c02d0140c0f500000244007030300b40001506107919203004040c002e0150304d2043d00504101e0703a1094101e031026280c180c101514800342020a240c925070480c1084a20003090001403820701e90b00e40503202c2d9550008048440b0b86100c1a544211303003614801d06148500c958810007490f80c20800d443d02a1801c2d014840e050010034644000104020041c90402e0104a500c080e145c0c0498104a800030071070381004400000d9032031600c01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 711778147 1250 711776897 711776941
    0xe060306040902060c0114040212060f010b0f120a0e070905010e0103080c0f07061d010e0a0302040f0f0603120e09070c020d140a0b0702070501092411030406020703050105 75
    0x500014965281c0755000c842c0c0d603030000e00010b241411141c030250850b60040e410320201800356080c042581400d00841e4103a000c4003000340441e003003158503002030039414810514442000110450707002c02e18810f89264198298601d8003d0520406901c081c1100c090403d203507100b6104006400305890150380e04a9075030505440d216400c507140c401d000d0f8045406c82032030384103854280d2815082000035034020002075036800d114050424100d402c1c0c004001000e4100955981c03145155902c0d41c00070401ca95044500091240c031121490019140c11001210f0f0f181c40e047c03001083c42510601041440419034410030410180c0c0c0c2000544503058500d80001003003a00c114005040c288031130a0800c0c01509100130070f03400c0341d1043c0c2c07800503425812945008035a003400710580e010022480501024200500300c582403008854251404460081e80010904003d060541c051000201d00b14201030989540d01e441d42c0c0f001c0c0d9184070500c0110341561808002850100109134030580d0020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 711779397 1250 711778147 711778159
    0x30816170105060315060403060605040f090242030a05010e19180206160203210a2703120f08190f1104090c030f09030206041e02060d1b0e 61
    0x400c0c90b050011640004020740d900343c1000030002c1141d6220809000258030421020510758109010f201c2078408600007a4801810004110016039644200c40108190b01001c034545014941511042c45c030100400921501040690103000003a04001e5201c1c110004040c4016641c030949240030b18001c43e200c401d424800302c44400c00d4003060300a80c080e0b410005200b50380604076000203125901c0386a50b800324507100160f803003c500301405462402c0700c10160900c01c08025140c401894070500c4220710410590b8000003030a8000000c89001e5070030303144289650340e074491402550994443c2511000308826044011515115080a9204000c0f9160b58002081850320640190400a55500d034464072100380b01c3c154190302c4003800080c00800d1000c2081c13035240e2406412180880303104e0640724100595100425000101c0a4104e503000c0d103400c0060400221560303482880301c40007540044005403c1103403840e9034200b00088544048009803101c1e102030251526803594441d650001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 711780647 1250 711779397 711779399
    0x30307051203130503040b180904170c030408100c1205070f0302210405100c1b1e1403191106011401020f03300c0d0207021c0308161701 60
    0xc001c2001071904041440300541ca02a076a9490380d0941e001a040094046004a140400720030906420b00c100300c5c00303490b1825182080d480d64a442e448111041d1860341d0000b40b041d41100c0e08004a5005002d840142e8415004180703919010300740101303042c00022b8030783e00e000caa5200e40b881044d0103241d2580320302c180080b5102040d00139401100120170100f520140101c00f8500c01c10940d845180304801030801c02e0a000b03c25401c4507044d0380301c00300f04013040790707000c95140e5540304000d06260010b24800b42d81c4103c450359801815800300c010030320500d01d107860005010010292814148880e172090102145000071920480000030140c1e02d81e00650041242c808411b000c0e202c0d180041c41982e41c80401004064a1544256210352a403086001c014480603004a46920303002d012058055980c280181a01000d02540c81003990f2564006900d80455a6540180c4944075808100404440e40c030300b40500001340850f64042c000d0304030070b203001030980301d080003024044441841344603d0b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 711781897 1250 711780647 711780673
    0x16020d380105010c02040204081e07090204060e1e030313050901090e062a071a01061b030809010b1c0201030506041104090506060f0f0c0d1e03020306040618091103030705 75
    0x21003113880701a82c04c141e0812022461204c10b00014060380b12522030040502031a9080901d4406e80b944074151a034030511090080590103440c004420f034003160440d42601050980e151007088400d00035070b00d40b200050700c0414807906600c00c01118800c880301c20060703030b0745d0802800b070b01d0a066508080e40c0010001a403040254030ba41c400e10b03285c01180d040d5401c80c2921405103540003c6095540c081c095000780e0000e0340260f20300740500140d15000407101c880d41041004c10800441c01000c1c050590000788030610258814981d0290007803420101c8410410b081e00700003003806050f800070381010000b81007410207014406492003410841480c1c20f00c1c011544d8001d0601515007a4000c034200b041c8803408240303d0140c070500380106c48490713403109501d420f586030004000c100c0301481713581d010359884500000114006068941000f41e90707561b445000034000d02c1290405403405035440844542c0d0021548003844140c03185103001c0e0b030700b04d004040581c1d030701400b400144594803500304640c003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 711783147 1250 711781897 711781907
    0x71203081306051302040605041107030503040305130b2709010b0a020c030307120206160c060c030f06030305090a09050c032a03041a0c070b070516020d38010501 71
    0x4000e24020390001500080e50320b81e825290f0030744014084000c3e00c450002549014441c0c0d0000b48012501000f1142c0c11901240180c082c180003e024007078040000703414580901d08035810451000440040d45440d042d4180180d08407400d030b8000145000303207200c0880b41c2c103c50626524002800c405050b80f03008200c1e0265401b144015045006401c503102c4992000c101901d000d52007500c02050f02201020000e19011004106101c13070315841003040380d00c2c0c0e0042c0f026000c80ea00030001103168001c019080e13014040d600141084207140a10000901d030303204c0301a0041800860700d6541d03451360b468518059a20645030b90b118854100080313480d109050500c1700c00302d9103150308400007004080c502c00d20b9070000c80c3c094604030b01660f1120003040e0355005030b95001c20340350181400c1c5a0070380ca0714404040000c1c5010244100043c14100784441e102900000550040094103640710610700441c0c2c100c46d94652404d445022041c0809907803078400c4404203407203999403028903030b0b00e48401110 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 711784397 1250 711783147 711783151
    0x160c060e03040834061e0c08030702071a0901170702210405311517011b0c080708030c070f08070b06030c0f13151e0807120308 56
    0xd128802000300050f0340310240203030318180c007510043d07032001402d500413050200034600c26503101c010f4070f81041c840365030001203c0c1c0703444d0060100c01800c00074107401511045c4401c44040c010880220030806140c0e030000d58681920b550350030340c0c10052184110000036000d141101804101c3d0000400400303d1105c4121703500c030000e44100c0b401e5508101410002c46d40700a00d060820000003014803c030308200a8134018800c00c5c959000000c000c0642d140303003040560006244542d142c502c0f402d04010386042900103010080400305130700c1a505480c7d4001c05010425002800b030308070b40090b82d14042e01e8140c142c1c603082a030861034450141c2e1040c0c21603000400d0304003144814030903140071a803501d04a014061069004540c0d42d203175404e003c40b0420703000b02418402d5003d060b858180d6103481140014981c41952030410014403029102d0140150050034034541d0412980043c02e0b4042d1130007480ba51540d02c900c191242c2c2c4030700d001078072010180580700c406903c180c1488006403107409002c0d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 711785647 1250 711784397 711784421
    0x1005090102040e190e0c0f040903030e0d200c2b1502030f0f161d06031509100608130206090d0b0a0b06190e1311070b160c06 55
    0x619094541004191288003075900d1880f402000c0840042801c003481707180c030056001d82c02414503545c0100018100c0c1919400303140a1a1545090010140250014601030442c84241c5090681d000401021038082055000743c81d100c80e890008001e03c0843c0004e00c4040140249070810f004848240d00e114000d440c40d802c80e0018400c40c07010030520000180954024407015aa9081c00e002500c0ca14a02070444109030f148942401050725a44108a100c0941810207504513800015003124030b002c65074100340c00c10b60000800000e254207a000d14810201220442c001c0d4454040c485490019800392901043c0c3c60f20210303c0e0203050032004903107184002d07d4145040103a00c0443c01d4404008800c480622100052105038011030150880b451402e40b44035040000c1c1c03500e000340291004100b98180164070003541c0c201e0b120340c0c1801060401e500e006019004141e600090300d80c0c07112800f0780b81c015140c0041015109030404015046c2c21580c0e81c007081007a2611008010702540d1102 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 711786897 1250 711785647 711785651
    0x6100c0515071110150e090d0f091206051e07090311060c160608011415130f03080703020c060a1e050c0d0203070c0e071b1a010b071a01060210050901 66
    0x2030481030041202c0284c40744c807104042541c540600d0000e10b489016004060002151010000e15a100240c45401c801c40c40c6040003070380b20740c0b6100b9500c06415410907540480103006c68818402d40b030b001640544528a481001e0748650030700c80001880c180c032a04006000004c003080070444194441c2507840c0010000da15060018920903d05103002890303000c40340c48500c04208950300042054018201043c03000590349042c000100e400c071881600031000e82e0041402c1c0c242c2da0000c7ca140700904991003000007003c0c4c80b420710710308681120f10103c005110781d16949016042040542e8224400360b200d4684021611600031386040e80031940744200329080c0450100f441e400c04c02d036002000307107801075035039504103040c2041c0302000d40d080015100003460074007d2881c1d11451280c071120600e0301410b03c561482c9408a00c104208441c2c502583c11a0004684a0075040040005503c2540701071031400d80030b85d0b00417070034a00f44902e1001d6003180310311440001141c1c01055000c1c200c0000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 711788147 1250 711786897 711786917
    0x4090507021516030c080907180626010b06040513051b0a0e030c0607031e020106030f0809090a1406100509040c0f0206070518060f0702090a0506100c051507 69
    0xb034142800001c40354a1003800c0000d164010080d01803280c281c00540c1482e050455242040b800c950b603981d0791191a44040c4071400c4505160500d501c4000078103008100300803e034202d031f0a6000c042a150498900e0343d440c05500c4a02450420b003200d0032a1409081e40240e500c680300d2000051000410003111030031400302280380101f50b03800414142005c0c1d1991140c40b038000041c140b800c4030765420035019400800184001c80d03004840d0807a400b80140c011410f41e643c0c0b0030201e015203200d900081c030300a038105a40080080e080701038040f182342a51032640c6079850300f44460a40f49049180d100301c103094030116016050418200b1840420b13418082d14012482022030210b546901e149030010720000c01585289a041c04031682051140c90030750f040002004c0304803a02124001c000e03108150020341d444004102c8815224034507001004500c0c0b61401c040200042c000c1118940c5c0701d0f0281400109084c0c1c050311412a80c560000d00420f040c0803040d0040340d8040d4040d200c00c05101d03800407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 711789397 1250 711788147 711788173
    0xe010807020c0a0b030a060e1302040c0203070b151005120604020d0e070807061b0b061003110a0207090e0304030515090102040f08010902090709180c030b0307032f060409050702 78
    0x40b0780c01810307103004d400ea4a28004c1d45a2040f50519080107488800d8001805040c2c0c0c24900c000c4002901141c0001e030b155103881c0180c1c070b035100d43c0c0001407031a080c400811045203201c054014005030190b03500b0702a4803484004840c51b11445d080d280900d40b1480c007242050170641e019000c0110509000120450354142040c070305007ca83c00003070190b205220510950341c1c0604040c0c50210180c2c2c01e006444d81350798500e600500018490f80c00703426200c290203440c5120350003052001da000c41d20b090741c807080200001c0d100e01e002d0007161005800c040e0740700141f030b10010450b01220b070000080e180000074100003060307942000e007000c169590280808203602c01410720020041114100024403403406105000d01207000814100c2807000c2030800300100c629550a059810001400c001070082481d0b205500404500803429014801c4030004820010b03900c0c00458134103032000d2565041c011103010071021058103440c0b50b422080c1400308100c4201c4a030410b6400034503500541d504105140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 711790647 1250 711789397 711789409
    0xb1b041701050105030d11030d1e0204090b011709070e1504060f1a0913021b011d0f0706090b180402030f041101020109051f09020607030207031e030e010807020c 71
    0x1240401181d650b107004010a140400c03003c5048030041c01c1c00c8442105440ca400d0f160f0144122007e200f588407040e0040e428410154030455011242c801c540300c603241c2c054a0000c000c090080b9010030f1800900f6248898005100d034803441c100c3e00108080c6040a800b008202009481301c60f11360001c144181ca16600e41c080c0304080d003501050b20700c40e207103040c00b6409050030602e1085a0078501304042d1455460701c01c1103c003500501d070005a03885040d1601c460b0301c1017076140070342c006500e06000b4000000d01d00d01c805069120107400c40720205548100a5181d030a21311548010402030202000080c0041005c0c018081e45c4010040725001c00c0404103061fa03000b21080c595200d20b21040004000304076480011002080c40200310824660b03940c0b540ea51032115290042050324000e4003000c580303e400044006502506090300c419503450003940d540880c0c0401c84504c00c00342e4111040001c91303600c120f80560580d4441c070311007200f00300648000101411807011405072120341013150b1500c3e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 711791897 1250 711790647 711790679
    0x130201021507181401080c2d04080d031b081f060e0a060c03020a14010b04020c010e010506090f0103030804080d090c0e0105040603030c112202070302010b09040b1b04 73
    0xb81e1500d6402c9000300c06503a42c01d20081d0071010584503030112440700d6036440b04030b240d4820005202160358120f041402808049000b0001c0800d11560f000f00490340e8240c8003a000b00d44650342250040304403e002039007542e03202101e140c1d0110618682c0103806124110841d000201044001c0400c2e80800d181c0d80c802c1040c0d080800440c4401100542504000c030321000109114074100440c0360103a900291141c3c40c0b440b010b0034001c0c1c0d00c40380c000003250039480200a003000030300440d0b0f40c1d8000c203e614084c0005040c102c9a55182c280059420709000310114400d4040c0000c171903003a0700b9a5015506964040d00a40b0703519021301c512050700500c1d101b07880d0451b0007001d0b611951447c0111130026454142c00c06030095003840c904000180e001000c404410b680074000ca6009250301000c1645512890020400e010501c1d400c004000419402005d03094013980c000d0041a480230140510540291b50042540000a0004400e40010801040340c10032560845d4541660343c43c03505000ca0300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 711793147 1250 711791897 711791911
    0xe150f0f0d0504020310090809130e010204081e0607051b0709240902040b0403020d05160e0103050d0f0e040b040603080307110115150f05070f14010506030f061302010215 75
    0x150b9030603c402c0d490108000c00780c0c0d40c1c0b640000c2c40903801503a45c6580c540a2441c060740202c0c052080c1c00c604000a8201c0b14400000d04003c548681d0b41c2c0e81e0040d0340700c0c0810040402d0f49120448902c90003408150284581800d030ac41e64a0305800e15000d4566000c0c0c1c5113804a075005036500414003082a005480e00340c0c0754101a410b03403095030700001c440707204581d11001550340b0400c401c0000c00380c010180d0b01140d13012900654041a6424407900342802c80d64400b1602d580c440c001b00307403e01003404450507030380200e044814414501c801914035040310344600740810f0034102c003105549801d0700440d43d5444090004134440d5500d0390340070b51540007030f517141012940d80c0220341c039808401d1148281000c00500901030007490691800004180c00c0b005030f042204403585034080500841c02c540c0c150798800b124604940881c2070010400c8100605c3c280103509100c08502c0c0c0e86400038982010340715042c081e100507200d00c00681030f03030a44200101d055001d0100c45417000c3d0766003d42603105100c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 711794397 1250 711793147 711793151
    0x30803070c020a03030f08130210180b0c0115060906050f1c05040503030619050a0506130e0405010618021813060b030a060503073609151b0e150f0f0d 66
    0x140034002802e003860041030008c01d500b24141c49805642e540c000e040c0b00455138281801c21a6044d031400c18000c1003070b000b94805020003e4194540c07401580a4004104111020144c0988440c03080311032903054032a00d070026205003c1c400c25180ad04005046000c00d081030703d4404000380340c8440550300121020740e102e401c00b008202d054203280d154402c42200a600100f071050078103000508840090041500482010485080300c0201c0140c00001d8030034012035040500c1d080c581035000e0101c038010341c102d11100101206c0141c105000b9940c0700c44500f0850ad0795040000144440e0b106041d50f9401d0480c0c4078140002d20905c100015801402d10386800b042e400d04040c2170610b442da141d408030283c0e0141b141040041a400c0321030700341c3c0c0d004000761202114500d150742c501400510f40080c000000c01490107054500f140e100c0c400032103408104590b12100304409464003440000d01075001190b064991003001c0d000c1c030003440c0403615001c40b582007021024501205402816181c1e42481d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 711795647 1250 711794397 711794417
    0x51602071d1f05031b15040e0a05090114041110080c03060f010306090c080603010612050a060207030339020619051b03011514160f050c120c04061509030803070c020a0303 75
    0x1082c8000c08010b1481c1c6d07414400d2415190080c0c490201c44003e050020310350b5204d0124554070000c2d0464814103d00680180560506003032581034a90882000341c032a10324055274030107060149134500d100f01c41c2e4024050465031010103101b1b14030420b10b1400d04050340c0c1d070800302c1c607228148101c89450700303265035048007440c01005044c00c41d0901c2c1c001c08012282c43c80030300b00180c400100b01441c42d80c4180f0141e280c00640c58280e01a0480c000071410181d2807030405200c0a03080c661508030740c001d68010821801303244a081e6104d910039101785c030340401e422a48601407c001d0308100d07000300a80120a101d14012803900840390020380140c00d40d40b6a000070703904d1407507112080c9505510700050103482c1c0108218550002c107464503005000000b205610424803009204015200343c01600b151164a000400191070b04651070100e40300d40d160150100781c4182c0c000551070f04c2c83e0143c81e0358000c141541c0300c0482a40004100c1410014498110401a110703207885800440c031a86980000c0c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 711796897 1250 711795647 711795649
    0x1908030309030a200c220504030c020f040603080a0c0c0b0a0512010f05130b0414161710030615080f07030c170a030806060c01051602071d1f05031b 65
    0x880ca904000c042d5120020513020300c0c000210303480400d00c000321441c03000362550521750304841e0040786048500600e060200414590001c2050304454800c44000e10303062512810082112114040500581c0e400d100101655000340480300c2002d010380341c1411a075070354400588807644015603610014101103950103058556401031800360842aa803171080070b04010110f4400051031a81c1901151140f1500096131599401a000703901600b100c6410307407030108660802d0352183e9040200150048060b0b503010400d90500c1805840d07001000c501c01c600c0e648a00019103805140c0100e041032036000050a400200074401400755444082c0054625504242e505980307030b940071901240c0020540c40d00404040dc0f07003907245d030385410715208640300d03107006c20014010314110500030341c680418822004200c0240481c00354940e0708551710980c99081c07032020b6031126020b1500305005e4101044860000601c4450301e05c80c941c80c2c40c40300959030340000f454144c0744810818011031f190003c030702e1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 711798147 1250 711796897 711796907
    0x10140a050a0f0501200d0c030c02090420010c0f0213060b0c0a0c050604030218090106090906060e1303051602030a0b040b100f0602070e0a1b0503010603050f0f061908030309030a 78
    0xd00315603143d80b25201729152000075191040300d2858020005140e000404150141d4107010f40030790040c000d605a85460301e04050340c101d840c940e500541a80c69140041984500c80d0034466943c4441035501544e040c3c0c5c00c0c00208440038900d015070320744613000816140103200140000c14030240050090b0016820300090074040c54002a0142608000070710168079804002c4101904a01d5000c01603690154414010421600032400b85814001d0000c2070041c0d5800080c113603000402007031071580312002d2054028058040c001c011a40c02d0012503800765482500e20000d90001c2c0907540500e4038bd0340c2c1d11002c284115800c0f03403003601c04000c1c810010800c5482c103000d0030000450b09540f071b09050001c0e5403403109218441105ca0220006072000c5155000b0911040c450940760b6280c280b0950090a181c10900070b140000703140c44001100d051149207102d00400416560300141d4540c0c00900181d540800007016100315603203400101c24404100842c4600c01c040e01a503140c400300d0100400c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 711799397 1250 711798147 711798167
    0x40503040b030705120105010201061a1b0304090b0a0914010b0c0319110d0807020304090b03030708040f0501021902060f070516082410060309020d1202010204061710140a050a0f0501 80
    0x204580c948041844484803600d440b400cd03c031409040e40c0c9494002c0003c94900d1416062110b46000201c0e00250343c074500c0d007148100d0f00007101c801851135142c595220480c1c1602c282d007181d441348080100120103d00c0c00074000350401000f50392401291482032007150400010101c0000c410160480c0030703440901c00000e1585461400303d0781400d10301c00082d80c0e0300440c0600c1003601e80c1c541e25100d00c0d94040085403101c0d81d10801c502e8a95507110b02d143e00070301e0b0713610445001d0301460401c0d40301401c5490324801d5840c0c0c000c0140341090108401c1c03107001e81001904591510600b28100030651031065514000c0000e60001c1a80d580700f40d02041c03400700c4840361003c85603c20b8003444014849501c07444250347c1d5610b00041c00b4251030000800c413103080c450181c1464107007140c55910075410b40040041d10103544901010540061a103034042d40d048801c806100721401040c04903d0b1584203075001c524000f081110096107a9001174403004440e4800a90448614000c203d00e5803c060014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 711800647 1250 711799397 711799399
    0x15040507030e1506011808010515150d02160b09100c031a04090c15121508030a03050a020405040612120206010e040f0507030605091f06140108040503040b030705120105 74
    0x120000e800701102c0c2e40d84000c0802c061581c030b28800b00003401a44030f80e00d105100710032100f00041103076442c510180244070a5808488100071004000944e0600c404d840321401211816a854800100c0310100203400104507540d4490100d030741a40071802c00c90086008112050250540cbd032890143d030003c40ba28103892000740b5041c00c0049042050107030355a5282c400544011030000250b145c0001c40b2007068210590310300e0340109400b8084d5002590001d1a405031004006180a19266000200e45c0b4444c09505900800031404d40700d10a8105a4112005d51300240c00c050310340c0001400e07a55603801070500310002c4c0001005204158280401142c45800030780401c2d41800f941b4120440000d001070b00e1110143c1c01340c010040200410002107810070020406400c0091645859203d0303c607004941c007007401e09a02100704d42e881244229070343d83c60103212101000d0010340d030050009009454900050000180e00140e243c01503204080361740c0c403160359182805800d091800181c0040d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 711801897 1250 711800647 711800651
    0x9120129060405040509010b060c0d1112250c1401030b06044a011806060909150825080a0209010605090d23010609051302060f121504050703 62
    0x50441d15803104076419200295408031702d40d43c40d13504440c0909a4040c0c003e80000b400524001c140e030000c5821801c0b000355642c0c1c00d0003c0790351404613507034034409501030562250801c0500c0c0c2403030100c00c1080b40c54600d002c004220640e1f589030b0000c0031100340d0002502100121050000d5070b403501c51400151011035401e400c007810804054600380007100240810744000c1c020307261701c003054190460842c200c2c0da01c0c5040d0303081641d031000060100b2b128690702c40031515042e616246441c026030781a02c20964038624682c0c030b0141c547e0b01400361018255a60091982c3c04200d021040c051008295180c00724504070282c902045407107040380380d0004056400154422005948550115044995a14025881d01d1b500800510807024241780140044410032860303045d00350210100d008034071048003c1040550701d070f000c0c00541d8000ca41c00c0105060590251005203401c0c000b4240c0b071610708404a0804440e60786002412105461a0171900664030401302540307428083c0b294091428601 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 711803147 1250 711801897 711801971
    0x4309090213120f0609060f11090d0b0c0405060705030a09080f100f060e04050c1005160b04080717042102060702011d06220f0e1b091201 60
    0x400d594030000340c020b448044a54001c00d02c14004030050301080250802e42c100904086494904020b08041150040403410150024042c154000903202007520243c040f0030810740d599102004e40000800b1141d1402d8240004183c90710790401818186200e83e0003140e03142c85016000d80900107a9114600301d40c00703c4440d8880b810b000c100305200740d0460f500421094640100c80024208a0b04a4040040c480040106021340040e41c3c15184100381c40c240c11010342c02c1801c844611810540031a10306480c0c1c0c0907000031710070300780c6684e216002d002420b04000f8503681c1c0444490f00c019241d4554200480c090202120700000010724a04110700541103502c0c0b83d010440034007c56001038103000400c280b5041700003420601c1c0400c440c0c000c0100e950381c0300503007140e20781440603030080c0c003046006280420094498008682079070162300c80e9800d03e075100000c2c1b20100e41c0801100703601c07080500181e001900c1c0d030382103811210100400031902d84031181c11803110f8040400008496800d02d16 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 711804397 1250 711803147 711803167
    0xd0c0b160b1f0311010201061203120f06080717010e0609160b0a0e0405130b07260f010e070e100816030b0108060103020a053007020607020643090902 66
    0x10b500112948044008548004070b0300507401803a607544032055a221101c0c3c424201640705142c040c031805d1a20040000919030b501c20300485146004401051340803030000c0c0000050312400a00401107200040f4040d07004001603810007034183c654601c244e00c1030320f1840000710740c0203144019154091465081100341c43d4010118060800218003440e61503001c176245080070580d5003020b82d048a5224014205601c00600880d4440204441701d00010304006003d08500303040c5000c0d520b030f2242103005900742410110100809440c4500340300350210602e1440c0c9540c01c0514030b0100d41d8440019600d070104056840c02c903000b154004151400043c0303c1c40780c1e00240e40d960408800e1800584501d8020381c107907640d225403084080005d9031418180c091030860002d45000b80040c0410412544035804241e980d00010f450020158000d20005901400d02c4044510040c1c1e68031a808035040c0c0401c44009149009000c1c10358945000c219042d4186c0c110004000915200300304502c1c0981481e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 711805647 1250 711804397 711804451
    0xd02040501081e0615070204050702100f09110405070c06090305030406110c1e070807081e030f04030f020a0b18010206060a031a0a110408010b030610060e0d0c0b160b 73
    0x6003c24030818401081005040740a0143c81c86c0c1507000c0e200700014200a01d02a5130380b480000d84070b400134240200f00c14a2101405902c0740154400a034034186e00c080740400010340001000d203003c00c03400200f2040410818003d80c440c4900a407201035a906090a2900030b5607590b1030140c0c48108100710503100341c240000c04108501000d40300003080b08238001d00909091345940a00c07914410400c0214890602241d2004400d03036100016072600d110b6440c45441c2e0050a51861407410188810000301d0726170035221b114140700406804106407603106000300c60b04541d9085031a2002d9001440340c5d540c04000541d00b00303808030b5503041301034a0743d6240c1c1641c5103000c0d02100d481e00441c0c08101c003010300303030000c802400f501120305840316250284075000345039078100355110b88510b0000c545002c8180459105071015035030b58810041d84581800402c2103011400c81d8854807140c000600c0a41c0ca2004e41400044003070004e622594508046480f810b028100c0d540c10002403420525081c004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 711806897 1250 711805647 711805651
    0xb070c05030f0d061706070c141e1504050d0c030302040e0a0b090603030306130b06091002150717130201141606110a05030f0a0e06180f12041202060f0d02040501081e 73
    0x945400250f80a689c6000104806d008103401380d144114802801405182c00c040070041c40140c0898140c84480c0c4003803440c008068501810704d030850740e800b19200c0e20030300303607030703510500900f00580ba0a64691407880441012103049081607030b102859125850900660783e0800000c0f8002c5055040c50000030700300811805071440c0d0707580c0e61020f0319650344800007600d410901c0102000c28070002801c01945440c1e0501c000714400802200003502940160340459003110140b01a0607107546044c07104103a04074840302079042c4510075112604024510000b8104030600b9080e00c11503202034503110b01a604102006190b2070b0060185a1103a544035041e00d030302c2881e0100300e14803031300c80c0041040100b0445805e01e0312400b41c40208020300d502c1c0001b00a03d0302e022801c40e0b914a1019840c15290800c0c0c2c0040c900400c8100300411a000c100e10342030050324002420b080c94118100180e11496010780c031030302c480725004541003005e90b8000038410303400308d0300b0300c085120031100c04d0800c070f944000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 711808147 1250 711806897 711806911
    0x10504090201030b060c010e0d080907030803040615090b0111011b081806040f0c0e070c060c031116020f03030301060e060f220e01060e0d0b070c05030f0d061706 71
    0x140c0e40e900c20a5a10980010524074070141038242d60710304d070304002406002964220402032144c0c41c200b0000c3c900c21040b10b88101040c4018118007030451381d0300003032a44040d01c1030b41e40076141d00d480110440c030581c4c40703802882058800140d20800200140404942402c8074400c1d9244c6005038806007005003020304480d00614001055a450040600002e107042080989520404040000300921000c2c0005520702502c040d9046565a0001d5800d802c000c80300d01000440301c405070030020740f0079040f0996424981c10003041d8006400003e004035000781da520034542030181001825401c240d5040c0081c4c1000354003461643d81031841c007812506a0703485d914011132002901c02c3c598034201c000d5800350340380c1c00540c2c1c0d10508201420940c04505008072450410a800006075440c01860b101600700c0c0d01418078403810031301d512220b010070300c010584001d0040080c91000012070034001884584039180300c0e10b840b070540c0c0780301000715840b5800640c03402c01c08d59180440c411001480c2d40d40664 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 711809397 1250 711808147 711808151
    0x207051003180b04031b11040c0e0d03020a0c0801181202030d0c0806030601170a02010e0d020d0c08060f04111c080301090b0f2e111c120c08010504 65
    0x220520071001802e0501d4590200c90260344440e003005200c20040d40141d0095449079015800380c0011003440728524401884551986550b001030304140d0040d9807014202d0528024188005c00440c4803044840411401601b0009850701005551101350000d40b41601c000c01208a20031058089002280341c040e00000725403a840c00c10070320070403c40c0c100409070003052082143d0300c84080c0540e503059500610900030351001158070603401c19014900d40c0340c280180013011030703900190341c066020900d00b1381244042000c0300c0580c44e4003900f801c0c418070441484ca0128a00030181707003000400303070644500d03c4c8000c0c140700c0856185040456420000c9a800c16850005a10304800c50030105c4003c159070404400090103c01f0b65000c600d0300c1105540a030042480d03801080300c85003004441e00d51001c400000b580380088500c0241004030303207a0600101145c041d80c803c0c0c1c9007502959152440700d80090070640c400364010001260703001460018404600c0384000038000703000501460340629 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 711810647 1250 711809397 711809419
    0x12061e2112020d140307020c2413030201110f0d050d0204031e12030504210203090d1101090b0f1605030c0f010b040b1008010b030c130e042a14060d1a03070510020705 73
    0x5004035814803035001115202d90364078401900545094402b9100603400300c3c18007045040710703c001041800030480c400000c1d203911030072880107484540080d0711031220a03a080c8008800200c1c2c90300ca152294840c0135031a9100002c43c076000040c20144d01607a0101801c200900000404400da90a284200800c8141045d03403056000ca2850088030302980c7d2015001c100c4030244025110140c0d5541001e03a1011500b58580300d601d0345c24032030208091008841000300011600a140c40942c12500c24005c0e24075280000400f1450b114850035a9455039564842c0c1d14590310340fa100d0340742d44410a403950b0120316080b0401030703c224030501c03ea681100c0c0020024081c450000210f502c500c0c0c0c2d10760307030020f01500d50300e0368040c00c201103c04454940d40710703c0c13240207440440e01d4142c83d107400705020b484080c00d28403801c0019280d55181b5810034000e01407010500014081ca4001684040c2c1754080c111481c010145818225803099000e85280d202c00340d059070303002c42c3c440240d40081d68440000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 711811897 1250 711810647 711810679
    0x615060d091218140d030201090b0a15170606010c020406150819060302030715030b0a0e0906150a030f0c0806010612061e2112020d140307020c 63
    0x30300c600152001401e1030050503000300070781010860381c006400c0e0b4960300c4050300508601c01200c0680030b502101800340c4a000518a04100103451040c400d1002007021003080d0b41d10006180103030f58074051692500c00a203084002449145c0c010711000804910002c00030015507141d000103000d407810400481e480609644036500420003d00340034242c0b400d03d180b0804c00034501c21003507654401c846a084005800d0402c079010714400c0d42e400401a002d15440c00c802115400d4000490700141501c3c2e17501d41000c1e903201e00014004102400704000c2d9031602100d900c0c2401c0c001050414a40c811070516007450712800342820681e41d100c078241514030b03060704044090f02080d5002c00542d11440c000030032504d07480081c40c9500c190100f0306015454440480040c140c0d00c840a4000300340c40d0f55000c001900c900a000501c04c1d290744c2642c1c210440c20f0301d940d050050500e2400d40540e00000010780081e51003540814400011140c171403c2d410702c048001d445100c01400648514046c03482d40c0d0007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 711813147 1250 711811897 711811909
    0x40b060103020304050f0d0c02091b2a0105161b030e0f0f120c18160f030f1401050307170307060b03031c05180102031006050c10020705160510020615 66
    0x840314020100c1f07001c4210310074010440200d030b0394100d000701c3c01c0c0000f240181a4500c071103101e2288048042e0308006001e02c41050a0758040440c0b0360110300040c03400221003081c4902c60041c44502c000c0100401040d1010b007111940308103006145000104200c080f039446400170210a004440300f40b01c1da0f0b450340003d0241212410035960280d244d074117a50b4625400034102e200e070b581c1581c0895001c4501c00840090300707821146054410501d41000303018600c2100e480e40591803e041c0000e17021000c5c8100400c49900e500d440d2500002e000c014046441c04000344002081c08401442d00b1142e0005003c1c0c41e40a40c800052036107440e620010810b68051082d180310f032911400e103a00d5145021100c0000d4802a41c00320540d481d81196041d600d2010700889225400460408030309601e00007048071346078841c3c0d080700724074010920003c1c0ea0314081d00051210901840c02814400c08580c0c060302124440d41c0541c1c801d084030122000029000310b41e06601c0600071901800a22a040200320 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 711814397 1250 711813147 711813163
    0x50a0c0b1005040516080a092a0e0a020906090415170607090608060915030f03070311070b070209010303050702040603060606110607111504170a020706030e010203040b06010302030405 81
    0x2900c108981004031584001121200302d40e412141484039450304c0400d0344580c10318031212000070710f40ca000a915180150030100049209007680b09500c2e01e1549219100003481a2021614030260010410310441d80713401c1d84c1041080300114908020303940001c8003889681081e0b8020380e283c511012410070b050708000c004011200210360401444110b0300d03151802114840040340030304801141440c41071b4102e900c40c000241c04408244c8034042e107040005844103886515114049124600c50802d2000d003409922075140c504081e10380020950034800c503500001020303c41444207202581c3c0c3c068082c1c2c11241c01d07040c42d95546400340042406011940c001401590030500009001640710040d0007694103114140c81c45605e413804102c503503a02c40c4014134442c0c2d10110f0100040c0d21169038582d0010300c60a071520412140301c80d240540d0300400811405600070000c204101a0903024200920250000071451840c05680d840d46440c0c1c0607160350b04040e800f100103000c101e02005110 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 711815647 1250 711814397 711814403
    0x6030a0f1505040c06030f090f23010c020c09010e090616021c08091504050705130f06061e0f02060c030601110f0c010e040905100c0516050705121606050a0c 69
    0x100851403e4200700808500a118141c00030346002c415002c520414410100e9060b801032030140065040d48560030026102c1d050022a110315a18035040b04800344110100007a15801900392011030034100408040140d1200034000c104004003d070b401f4000c9aa50303403081c0803001d240120050354004a1401d078625004616902c0b64901300d070300c82d0b83c110003201e00c41e04040048034220030000d0001d9a0104003501c0050456002d40010320280c030340341000c003190000d10000001c29000e41003c43c0151001580424045502c0104261600c046868241b0082040d410305040c804490362000750340b00801003130182000d2010021071800e81c0300303800345240c3c3d2110a040300c900580f00340079191202e12240459000c1200203c07081001d05041c020781350165080b1024210216103902c058024180f0203d00104011040090151081294202c0d80c1e66600500007000e0403400c100501210385084005810035030b03c00032441e05810b5100400200360749041c0390442c0c807820b54840960740807410303500003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 711816897 1250 711815647 711815651
    0x6050f0d090f0b13060c032c03070602040b03040618080702010f0e0904050106050405010510020a02130e0604030905040f14060d050708031b0106050603160806060904060b2106030a0f15 81
    0x101141c01c8120f1a03000600c4e000c5c9008101810000c00c081d02195020740070b10346030001080f20715090990300c0d91481d804502c1c441c00d50b072600c4001d0351070a040364015005240300c64400b1007400140030062050469010b81c60140b58152106a100c0c00420b0240c0e02c8001d0401c0f04280c03401503683c0c4950301100c20f1113009018000b440c1800c0c03404030301802807805114041c51610000250914140113040120308440d009403180c66061303002e000c40c0010401d000000f9a0b00e603031519054a8042011034403480c0203036a4a035200d414501004262109181110507440c20300201c0ca03000d88140d644990405c404070394900c04042c3c0c0f8902142410203540c0043c070070340004038880159049030080004d400114900800005031600c0802596000566480d00003081c84108590410301960900790808030041003141485010400501601d40326000122040c80110365103001c0740035102c0011200c506403008038114544440804d41d01c00080402404114454070034030284454001d405108040790305003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 711818147 1250 711816897 711816901
    0x3060f0506030f0d05040b0c0102040522050a09080f0a0e0a090605090906010303081311040203070c060b0f130b040e060f1602060f0109092f0a06050f0d090f0b 70
    0x99040145000c80752140207003c1c0600450001c80c011400d501003040300c2e1141c900306410002c65140b107801220300380b6040d6508200205003603680c8100e4803d8103005201c072201c3e441c6000c058000340c981c09800c2413905801c00c00300c1800a600f500c240e030013100345d5083e0140c6a0501c0c98048965414840c03000340c102407003010200b40d41081d13030401015120265401c100c15103581c1d10081d9580300910000d4001480f4402040c0c408550796020754a0074022030a0301116070021000034101e900c15906003002c92034442d811002c01c1403d000b10241103178119103800660101c0300c041942c102d064408070f05103d5603005005c003299125400340010700c13000c0040303400e1440c000c6e9180b46a00d00554400071111060031284c0e80c5503100080044c450949030a008806034600021003018204088084503280d8041d01c0c0c500c80b00034071724842c1440c44044e4030040c2d1124240780c2800402001c41d08240308001c010000404502444c9048502d682440ca0000800ca0094100064a0030006100a10180310442 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 711819397 1250 711818147 711818171
    0x6180903030114091003060905100e011512030c080906040e0a0606020c0901060f050304030507150b04060915030f050c030f030307031404050c190b0a21050105011211040306 76
    0xc051410303a494620000b1a01d040319042018040c01151202140c01e02a0f10503c0052903d801c603040992040d0b040307e01c1443d000b642d0200343c0381d410f044407040e43e550f810280752100c80284030000512241850400626003a00d008003001070041019280c02d8000904140e1601c86608a600074103075050119090b050210300c00028045500c140001882090001e011901c2c10000300d078100d81058507070070001400c4a1043c1c4050b003000f070094083c008240000408241e086403403605140840c05c0028030441c0300350800c0102e4126400008107203280222000040340c402000d0001c1c5c903040490300c0b40658482c40c00303034501036450650b01d400d8064010001012240000514010701361518207003c000c101c7e85011030640004c5402400c1036200d030600c0f1815041c074005001081c0000308241e08025101c40c1070f15030907401403440800052444541441041d4040882c03145500d980d4070034000c2703501d00000200701c04408a044025680e0399000c07024a4840d24003120b001307640c407000c2072207040c0c0202 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 711820647 1250 711819397 711819403
    0x60a080a14010e0703050702162304060b0403140316050105040210050309070509090705040c08041103010b0d020409050c03070f0f0f0f06050d09061103180601051e03211908070c0803061809 83
    0x40161001008480c42b12119151030b000c0d0506851443c05c0c25801d081c0340d525122906445d00d08811400c0c001040400511411000c521600e580030b54000301d80303424684140300703e80502c03000f40800c002c024800d2104521000c00d90200f240e40840b80100185c480300402400c00d0083e6000540c400d203414082c21240d07800c41c4240d031146004109480700b00380c01c00d040c182030301c010290459016803010007010040c90f140d07000d94507442c00fa030f044910880d0000c02180c50040c050308609141030040e181004014070340c40c41e040151000481e01c20b4050b25158591400e0089070080a00344500807030700703c8041e0f00b60b40c000b0f403040c0d4000b2030a021081c000f00d4a10a1030b4816100000620315242c681e0304020000074140741200d4000d007054298800000070729500542c6210000e5050082a0382c0b5000701141c001c62008200503c0181c070741e9480d485d240c2ea0b001400240d00c000078000c40d0b0702001415a0459501c2d201d01d9046007445640c3d5403840000783c419000d1680c4807080d12140414891101000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 711821897 1250 711820647 711820679
    0x3b0601031109070513030213021b01020910020a0b180a0606181a0108041103010b0628091410031b0906081513090c05060a080a14010e070305070216 65
    0x680d8504866180c1d03080890ba80c3c4903240d05d210800ba2101802c0005061400c440420780344110001820300e200c06560b08003162000e9030088860790045180e1a1519280410182447c00d070b00003010401455592184042001060000b40c445210860b503a2a00c00f445280c9110791b200744100003240e01c82d840e400c0d9a0705aa2034440c171152804080e0407644405220b2408003400585810541d030740c032660349001050321300305c4180e095503c030040c200d60354031000c0240c0b084107443d050b22401c100b980000b4881d009049400e00c010082e07103c100700100d408440102180b100180c1e03401c299450751f0b40c015800740109201115203908441c01c180000c640c8452510300b40c0f08950354801942d03d070410250048a421801760342d0203103881c000003560240355400584d440c2d10903541c0201242d076450018002e41c000365000000700d25034400700000450144035001078803803140303940f200550400752015040007000740070703d0a240d80c590102d005d241c000c000b0b0050381c0075101d410034503003500c804901c5810815 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 711823147 1250 711821897 711821899
    0x80a090f06050301030b06040504020303221a0306011b050c10080906090c0a14150f0c0601091e0f061509030c0f080309010c080d020f0301050102060a3b06010311 71
    0x10352240454454403a200302c0303040b42c1d00150340c40d0050700c400003000000c150140c012640340c4020014039484a44415040381700001040081284525207201c0071103000b02004044580303001002040008da07040070980300c2610650400c1441c8401514089150000300d011300c40c1d0007042000401042ca600019079407281c0400750a641c1c0580780c4510340d50795210030280103a44003908076001d00c503c0215004114445a000b81020510340f096640d89807264050b940180440400190244001200b04242801001d00340e0041000d110800c00f140503039400c071041d0b8550310780c8540001840103000c0e000500648059240700d00030020800000c1e00101c907a2001308c0c0e490100d000c0014150516206220071114a64051454200000d00440d00001e60000445440e40c003400405c0d505846803028200304c00d01220101d40e01c0d414400003900e00b6500400400d10f036400c00c14442c6207034108080580c000d0304d00c0102050806001d4060108104650040d0505445100000010320484400c1c003d000c0c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 711824397 1250 711823147 711823169
    0x2030105040b0916150509011206090b1e0a0e060f120d0207051806010f0909050a0c030b030613020f01020f01240b0403030f0e040e0a0b04020f062104020607080a09 72
    0x6144801007440d52011700c602e20136180001e1405541078003070001804100c03014948060082031003ea050215007803034100460f0035a40d02ca0400381c609040c030f003601160a80c0c2d84812070709101100040c070702c0346e0329014400c031551140004c2011900e4640c0c0150000c0d800503d081c2c0305140121303445a9514500d607111005104210001846003000e90700305070000d041d40c031501960755810700103450603800c400e4030300d00f0000124070020710b250301480b8460107400345610205444000d0b0500606644a02219074402d400c0711007407050303242c001907640790304a0341903420101c140040710040c4c0c140042030500150035402e01d000300c09141c04500f158071804110905180ea09a219840c070f03e0725010340d000c0140850740d04801ca00c66503000b41b41b01044010000c1001c511392107411051400d00300c0c2003a003140c0c81d0038a0003d010844c41d10a0740004080016100305003001418100f183d59480c40c40c884814201c0e0312000b05055449a0341110aa00d41026242e6520000c003840180041050311030043c3d480c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 711825647 1250 711824397 711824413
    0x3060c020625020a0803180d0c030206010b0c100f0b220c02070b0a0305091c0f08180d0509270403030b03010903080a0b280611010204060219030302040302030105040b09 74
    0x40b0320040c021074005159030040015501a581d801c3d12580302400e900307054519424800c401050400144c141c002080c1d545000351039a92402900d401e5041e080303003941c0c0c14180004201c00c000010040c4034518a914040783d05414100080014000c81e07015030381020b03588a04045401d84000c02040c090101d980822020bc80070100b01e0320f07002da5008140006004021407600107109400c0941c0040500c03040d58000f180f94143c1a00d05403260801c013001c21a000b0076000c2280d005101142c1c09120504c0b0468000041d0f01003544a480035a0814140480803a060303041d40c5032540000411440f640100c2031540540c1002402c540b01254200c00080c1040306035000b5040600510035015031540310080b59440390300b040006880040203981c0c0007100301c3c40585503002541000c800c00101e000e23000c0241d50400e0030042110900800d100e50607070040000304050b41c0d0025850300c0010b18100112000c2d03005150440180c030a50740040e51541c200820321040c4180100918003440100d0200d850704 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 711826897 1250 711825647 711825691
    0x920010207140108070c05030f07200d0c0501050a02150406090209150a2310030e071707060f142227020904230f1b040603110403060c0206 61
    0x100318840c0d00500107840200440c51700c0303003d2085081054400c2c8156418040f80b282c01c000e2035004203c0517030310000d041158182031910907480c3e1316409005d441c0120880d150b62500c120b5498580310740340c10000c00140548601e44240034080d0451356415410b0b0307084c14242090405800911002c1c1d110740c20391404141c803401900b42015100e1000341c000710402d45442901c00540d4101e40164820702340600c942c940b140d4540c800400488003d840c009903549c1021035a918040c81034002d40c03052144504d01e0400c0042c0014182c0071903003c0e01d0301d2002c20341b4404040b104500221010f1307154000204a421100320f0300c0c03c0113a204080780c074038400099520b205403554400c030301c4642203d81c0b84c410340303c168032aa130f60024049448041c0c000302c3d0341650318407c1c900c51004808280c1c5040c5046092080451041103c10781046506a0284082004048420f0988502d100700c034280b640e505a81c1a410354043c003954020754000500701b041500e001c1004c0d40740e250407100d405d03101000003480c544e4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 711828147 1250 711826897 711826919
    0x140a14060f160207180207060f09110105090306040f02030f030c1027030309060605060705070e1302091501170103081804020a21060f0312030e1b010c03030920010207 73
    0x440d001030780245105460031040b039170100717580014402c2c000e800300692004100540107828243c40854000210280c4904181d0111010b61609072f0400c6420000301466036400221039410030340024141050403500c0c0300182c604086c00b16003108034000030869625403a000b14846210751103200c4c0902600807800350a2501e20010440d40b0103104403280704102007407003a4001050f0741d2044800107452500d450000c0d441d038003c008104c032a030740f0128042c00102030422440f90040034031920760700342c18066800501070f00c00c01846171281c1c0c1504001d140072070b84618030901940c01140d0b440701d907558603410800b4a984c05071990100c100024103054041e403c01d0310888003070101507a6a0781001003c02c45d548c8811045800c03800000d6154003001c9141d04135404072a005500c5010690002d11410a01a0950f820004403090303580095226001d4004582c410344580c40c02440c008110000c103103000d90080c0030024000d0041004507203180968188100e50380300d40d4009800b1a400b0f07a50312604060 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 711829397 1250 711828147 711828181
    0xc02010807030911030304091e05220507030f0311150f2221021501051318230c0d120e150c0703060b04020c0a140a14060f 54
    0x400900ca00d80020315951283e0b024120443c421003040203d040c150000a1640c5c10036001114895901c03041c0d401616403852000064207400d002c03e000360302c0e02c0320890308440800e0400c5100103503030814210030071900703000c01c402039a4002080c160001050030001c0c08800d2400c2c8048951040c1c0d40d014041540c24a601803103500d8141300c01d1400d03610342d030420f5820803031848124070f1412040403031000620b00e0ba040038060782c2d1b403017032017440140c0c0b07130100914114850461402c0d0f00184801131140703455550000380b102035581c001050036401458003204903858008007501148800e114803000d940700e4102091801034000444e040e04594008010b000701041c0070007400d9a034003461090085000315002a85008000e12202200319040c8402034940e0007ca420040c5400c407600900400ca081d10031081900c100303660440c00c0c00807000c0e002c0c2da1204c42100103404644400c4906600038410086148415441001c900320148c404800030f03541c00041d2201403c045c1c40000191440307440420302d00d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 711830647 1250 711829397 711829399
    0x3021206032b03410408040302010f050f0d090302060a38130506101409010309060204170c030615011403060118080607110d09090b0604050904031205070c02 69
    0x580591030340505000907846003110b8281500d60a01003004500c2c020301008224440504c102401403080340e411010308001004095402c0340024040411500750940301920b0703082c01e0803400d40c1200801a181c500404100391803201c40019a24840240c5402c40c0108500c02d4089030100d46545024000b628500741c0448008640c003000c00000c00b6400030000d80700f10085188030320000c500c801046000c20100c8000e032805840d1401d00046040c0f00003042c02080c44c903d4004444849000700c5001d510480e1100d82c1055110300035038003404501e6045500030040a1443d100c088001100d0581b42d150300703416907100c1c1c0030700d0001034040c41040038040b208020503554a00c00044100064020f50000750525042100040c0b86048000c20415600081c0c440e83c0c004210514101c800100055a1180b8003101a045008804802c030340100c4610700361401d80780007203103031180d0001081e0036008551000b544001e00b1410f020134150804441c07540c10a10003010f100d41d42ea01001980c00d510500da0003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 711831897 1250 711830647 711830683
    0xc20011d070b220e0705030921030115020c03030c160e1303050307140301060e03210f09030a051c120506130504080c0a080a0210110409110409020a0302120603 70
    0x30060018250941d03807995850120010010ba19201c6403004100c4c1200c000b0b0100380008240f01150f0420000a0000f5220a208200d074001d1910307941d805002c103104000c0084540074031400034500900072403500d5940902241d4540c0340d40e40c44c0315998901e1884155009010b0318000c508141038200c1c5a111709400c1c100caa12007011582c04440301e92004140408005c0c055a0340e41142c8810801180204055078807603071040003d070704241c00c0242460200d0354664203984016000c04910f8240d07048445c10501d0592100340c3c0034046802d0107022072008015010f00c080340b0988095201e4087c5a03d40e01d5503400c840d03003a207000850200c2c3c0c0203803a00f030351064a00c07803807001d0204c858010585c0948184110b0b81403c07000c0d1008c0349042c1c408141140c03030840101c1c10300c0040c0e504224003840c1c0580160240409a14403020300c0c002c2c03040d03009604845458100d08804119280100c1d4001c0032181c0c021981c9140d0203900800a40001cac1c016482d03050800c2c04101e841ca0001030020003400c02901d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 711833147 1250 711831897 711831907
    0x4270516060e06120408070803040b0402090106050c100509070e01240c08030f070903021c02101b02090703060e0a0b03120301050f21030412060c0906120c20011d070b 73
    0x190004e54401442100e003104100a01000030300c4503c00f560055105018241041c10944108003019605070890002c000d818016150514030000b102c440f0002c10000004180d00c46540c2c850070814541c111344e02c17001c6d01000000d03c2450b410030043c907646500212020b02d8104500172548106941d10241400d0010700215070700900d003408090300034415081c2010b03c16626404108030f00140ca2941356000c030900350003002e50600d0701c03081601c4800313850200c0880c40030155a1080380c91196020703001d01c9a0100003800b0382c1c0203034800c2c00035006400d007c015510306505d00001400311810050b0190090100c1e1807a02071441c0281d07816510001c2640c0810072581c0b041c414201d14201000f500c9e5a40282c0081c9545014070003407020704242103110185240c80d00b480f10039203903142d00903c200101140c3c01c101465000b200c088101c040c542010550103000001200c0b03046080c0c01014200c81c2d22a150414482d0541c00155010f54425094010740303481c600c030985644817032080002c04401000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 711834397 1250 711833147 711833167
    0x20d03030213050a080a0302010627020315060720041a040e07030c06030b090108160b0c0304050a1d16020303060f0a0b040b0715060501020a0204270516060e06 70
    0x381c80c1000e008100c0b06030300741d542e07000903d0141c180c0e404420341d5002484048203065080c00f03920080c007180c0c0f8400140c0311200d05090792035141d443d020a60141c2c08008584e0030303a00c40c2034541c2c90b048001c0605440d11050f0915046c5001c0d1681c8407903050400401194041c2002e0081548290800841c015003854010601000e00100040c2081034028407201100080400c0c40305405881c0d56540081c44181c49000e0088102b01a08400415444450456104034000c50311000382e40303039941141d483d0400401564903500594224961000b001600441c3e0844c0802403981e06422590400031151900c00d1001d84083e00c0305192001a0000c0001551030f042c0545c0d090340026003c0c220f9410556959040c1c0500e4001f60030154031000002001814820429895580d1040d0088200203251070000040e6642030450802401140c45080601071000891140b04854000704803510400e482e52620603210841e111420701c0c0b446d0f01c0800030030590310580c0c01c0808800080d111500d0142002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 711835647 1250 711834397 711834401
    0x30d08040f050f0c0f19120c09230a090515072c030d0206150904020f060304030c0203010e16030803181618140a0b030102160807020a0b0304020d0303 66
    0x40060310751004068000000075010011051903100300c401074103c21300d6450030803070103054000320240b080100302d04a405410409007101d084610315a10804003004525206005000a507c00c05501e031402c9505440c0301c1464110032041c9444100f070b0002d075994043c80000b214440440980b0303e41c042810100e00c400c03250070702904079520f0304180c5064482c040c4d120044a21000032815500e9603c0401c00766803c0400007050806014000350070307540380501a61054810144c1440d124110390004282952103114624014050180c000c0c0d0b940d03c1e140c2000b91030f2000c1d00a04034002d40c07800c22800009440840c121f14080750082500c2c200500d035032075131100c80d04003600071101d404403001150040041040312600c0d0f1840c0c15004191586002c2c04102c451a20162442a00d4200740750080e40c141403940695000100c0d400c0042c42c0111030010a0080c041e040030080b807500981c9069060206170303000760011520845d0014201625160145518003007600e009401c5008205c807000002c0c026 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 711836897 1250 711835647 711835651
    0x1204030e040f022a01110a05030a110d05190e030912030903010501060215160509190306022115150d111902010c0c0203030a030207060207140c031b030d08 68
    0xc2000c00c500030000352400807644940407119840c1041e4890a041c8560241d55112424801c002000406502c0c031b00b56070745115994010003040000070000c1c4074590f5984c42000311103c51200c0d591284000c0111000a0800740c90391101228501c1640742415100d0041d82c60f060b582c20080d50514115000303200440d146803840c0307120303400305100b604041c0d1824415130340204403690003080f07000600401c180008001920402e041e071400c40d0031304e0301c1c160407004841c8034400030b03200000c03503252400301d00c402d00d0202d0b00010440760001842820300341004001500f00390180d8441c070385586948440402140041403c01e0b003140056030706044184442c0003928407801d4020010508800c00d5143c68400e5100d09403041c2a110f9801101c84459424410301000e00f4141c01d000d120700d207440d00007a54a0040c92151810540c001414100704812a01510300066019501440d00c8001d0058561a032506903c0c20380a403080101d02602049900c9070300b0f40041e00580580040395801104841840300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 711838147 1250 711836897 711836899
    0x7030c0501032d1d01020f03040209091615022e0c0c120818030313210804021e030109080702040e072102010512040308071b020108010b160f08040305121204030e 71
    0xc9440c083d420700080c0001d07d5408a54142c6954038682441041031002c0d01401844039603111200380c46400d00d4854000c0c0588410402d0203488111b00c40040780f810005800f10015040ca607034080d5841031003180315070b1205548010500001170304c1c0204448402c64030740058004030725501d40341d9195008203582a0885080518044803441d0074840c60700c0c690007030750440c4260092241100500411581240c800c3e5919000e040e01e0300c2413494003c00044014001a1141d030034591907142041250781c0102c24828060000e0205916038105500e90350011b00080c2e00803410b0000913000101c021490906484618002c0360030004100e0614808402c080030883c184181000003540e200801041140305501c2542d40041a00d044607005040e02610005500d042e00c90801010040c0e03000400c190560303512000c400e413200e503003c00d520141e024190015003a800c1881110084c000c4101c002c00640b030280c0125107500c0304100206116100b1440600944c1d00f0030350101e00041d215a02503c41c0e104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 711839397 1250 711838147 711838181
    0x141c02030c04080706020304030303110f03160e03240907080706110115090203040507050f060a08091203091e0303150d06060f0b040302150c03120408040807030c0501032d 75
    0x80c5030f801d903603e05030080d00f0060240e480450204201545406030092450206803030a007090b04200081000c1c0c003000d040f10708400c2c003100440f0381c03d501c0741503054641c4800900300c804106081a6000d40003d032403203004003156424000408501d0005010012500160002c1002c91703e000740c11111104005050031013075498000c3d082d481c4d0084c249840c040c0c515a003006031340c0e003042e1611074504032a5a0120780510701100c9240c7c140da440d11300703680070160345040c0201c0b15910660001d0400240e44000010440003009100240342c000400c0035880449000384000c4042d82c445042c0d82c2d0204803500d0311a05244180080141090102254041e206600111b441038803000e030750720044020f8104100c299404101081540791040440c8000d21410500e1481d08641c03904083d180d21401140303941040440300070030700300020001190002c009480580c0c0045440c0d00c0d01c0a500006845468002421f0071101482621456800c0d40c0001c51043c1b0740c08e04000c5a0103d0019009070081c0c0c3c58044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 711840647 1250 711839397 711839399
    0x16020f012c0310061a0f22090e0d0e220504030e0a090501180c020336010302070f022e0512090c030d0e120a0b0901061a04141c0c06141c02030c04 64
    0x1414080704034a0303c804d031f44550408903007012603200448400ca0700b5840c0c142d11a0000c5407403145c01503d0240d500a0039501d581c01c00c0c0c200441d132400090002038100410f403916003004185948000e1094851f1022201400c010760341c0c00d41c0a0030784a0a0042030090318039807001c0d101d071500b10b51018111180741d0040d40c0c20b015000204401500f5110f5088807400110600d10020111820541d40811001d0904509003ca151144032266085010082c020b090300c240300700500200e1214440141c0307007000c5410142440000c002c007150005004140d0024038113010680741400450001c003100c1c4050003e000b10b100011048a118801c42d010640042c001405004068014440021003030700401c0d00c0f04c2c0d1401c00403400e50840703806031300c03042c1e8214601240800310100d0004903411100c4d22030081e20701c00041000549282c0b81c51a0354205070408090003410844101c07000012a200740e100c40c02030b03417203000d20111648210380011082440541080740325040a45c00b07990031070112501030f4201 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 711841897 1250 711840647 711840667
    0xa14090a030b0906090f030a080109090204060e01030609020f010309030c0b0426040e0f09071415040312080a05060d1b050d030801140616020f012c0310061a0f 70
    0x54103907034400154100d41304210841404000030480700c1700c40401140b820a480e00c0c0184569018000c000885032540f99280070365980fa004240a004034100c0c030b5440303581d6032803c14020300501d90100c0c010380003606c9010391580244200c0c039050b42c2589900516040c2c43e60382c4244003400a20032154480200b924441001480e4241c0070501034107208166240e082280c24020058002d2048a04103045010403002200100f02c8000f01c2d8829080c9504030380c810301c00600a5040e180e50783c20611404130b000824000c502d00b0100807070049449202d030688032621004141c5400303d0340940c0201c3c9921003c000141c4c104190a4480310a241c0110110f440f01c000031580301d0481c800b540014180300040c8041d1562009901d191801100c000780762085424140c2c1c10350340701d400040c0c42101410189803840e40192003400e421080401c40390160b4601707643c0c42d40c00c900245809800b900c0b070300d80048080c00e518070841094901c107144106001c1d04064010703555602241e001c01c0012801e000503441 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 711843147 1250 711841897 711841913
    0x403110904170d0e010b0405100b07060f09080406030b0f06220503100209182802190f020714030c0d020d06022d1306030c020717030706060b0a14090a03 67
    0x190845070034022443c070b500c4501040c296213403d14418411f43c81c0c00705001095019030744610071202000805501e9101d541480c50040020303100c0c9131112802c00c6001c1040180e818002c005540e165241044480c507113009122078a04c085070480e0700180c003007003410041c43c2402c03461a209500f0000741c14001c1d0b10b0b0741c042400c0a1104440445031500800c411001e413910300c0103882c28404250261400745042b4400820070b0f04160380c91106e602d406404a14500840e030104d0302c03110741010740c11300400b441c44801041c60b400d0400200050040e9400828945071000c045500311500400810705a81d05e0000c0000510038031000700c9e400118426280c00041c00380c00900800300d03075607140c91715200c0300350310303803024100b445580214628040216a0082d1310404908054070594900001c0209800780164603006841e00805440810321f81c03440002d4130004010850280316800a0001340d9413130000c51014041c0c119034601041c030a40ba0128100c08200141182580c000c0ca54009240d4039118075030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 711844397 1250 711843147 711843157
    0x91803051c110d1b0e06160b0f010305060601050f090f04060e18061b12040302030f0d050108070603020f03040308070c060906020a080c27041b111002040311090417 72
    0x4100d000030803440c000b070303185106a603115880c4092010404151510040c80c111750380600a01c19000400c1401a0f00b2003050500005036000c2245402810050030b0f1150b2520244011a150320440c000504107500c0703102920f0300e0382c0c0b0b01004241480c50001c1000702d807010800480340c12035503074000000c0c03403c400c1d1049406aa034085642d9034132142404460300703022000744100481b004424501d40395400c404100c81c224045111081c070103032a54901241903101304a010040304402060070041c440c2e02d54011412960042c08984040c1d0343c1d01d105506a020300c0349190314489003400050046400743e00f04076480354051802c18076145980c0c5d40c000403035a0030310040d03620607400320350011803a0b0821001e80c0c014140c040854180040080c044500e030342480284148500048c03002151912550000280c1c4100d1494610390300e0344000006041002d40c0e44400300c42d12075407510004143d15803080300e0940e50480c1c11030b03a0740d0b001c800030300c58000005003040300c505e04e11100c80507100c207030100908 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 711845647 1250 711844397 711844421
    0x1107080d0b091e010f2709050d0e03060108060f041202010b040606050d140603030417010e062d04150c050c100605121513051c05090a091803051c 64
    0x68800512560f4210080c2d005030454424501c8082c41400001d00842a00b0f20141041c03c3c04a0465405640e11010341980c00d4014071070302c1011410020795802c516245070341042942100d019a03620412160349580544921a90200100c082000311b100500b0b2101c110146000104400c49007c0c00b0800703d0301d940e80709400060002c18221407403007041c000c4c25a119903000c034280d09070070680e0010ba280c1c41140b1814403620000c0c0e28509900c6001e4011070284240107094800c1c610b420070310360041c2d071226111100313800c0340c401c820b00316507041ca03143c240519000301487c0c03065110850b0100051100466074000e00c6000e015444150400f04181c115103000c4100c04a80ba61504051040080801c121074500d034000c1c0184154051100050b95031094820309000b501e80b0311801c5c181d0901840c1c0d02031071440080d103080b09072050340000083c14424410b0380c030703901c01d140c0d0f400c035601c200e400c0d803403e084008032581d9070300d030100744124042d00386805040c0b0700303581c124401102e180403204482562 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 711846897 1250 711845647 711845671
    0x31e2c0312191101090c09150b04030602040302040b1002031e04051908120a230f0424030b03060414010f0e0615030703030206190609050f09010507031107080d0b09 72
    0x2d0407040354020302c40b03038500350010300038005099255074031003941700113000d8074010554910b0f81d10184c65106400b0720041c000100d449540e962281441c60180d8003d0106030b00841c04c006203080141000600300000300c2d0b880d405942000c1004002c40c21622078020000d0840c0c4d01804080303060307600e56140001492109040f41c41c198a0800c01500700740c8035602e8101442428000300003055044182d6058a911142e1005281051200c969800303020f80c0201d100050004200840c500607054040130184109001214484a1140007107041c5c07074100c20040c4c0c0540080010500245e858288001c58484890010646259803484402190704240300303840790780c1c0f21000b0300c41074015003c0c0d003d03060b00d000d5000d003c1490458502030358610020b00389550be00045c0c041c004035410568081c82c086d0011941c203102d10305106d20740490481003030f01d00c4812940307080045203600d0301903c241c0f009000020445420021142c4914409402503403050090907100c1c02508419030b2034000b031030312480c00c200035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 711848147 1250 711846897 711846937
    0x1d0903040b0d0b120706020a08090d05010c020d031a06040e131b0303090f060203030609090a1b05090609010608010b0c0f0a030c0512090904022b031e2c0312 69
    0x82000079890031044e01c4040d0011901446481e03070204403e40980d401c00901503440c0b03001c0001c2003481d208210060841d51a184041a600307a000c10319562440316a6001d00007003890065080100b15825115503000350100030812050040c0200c240d40609044903484c0306400ca41c4550b6500701c6008041041008040d509008158200f403484000c0c1c041c035502c000c6207600b03008000c0e64178480600b846220b2a030010008003104000c0225030480f03588880a400c00800039090107450720f0241c01842e2190340c00900256883c201080d03840c5c101c0d01d096903403801603441c1c45004807a650104119480c2401840d21222140f00c003000500a00380c400d54401421501c80e0a1080c184851199101400035003004244426684c071218a9001a011550103808080d0400d18010000041d01c42c80e41c0980c003080035030300f416000340380341c00a00d00a400e02d49404488010888004958115248103042d41c440c0303100a48039562601d59000ba009011603084000d201c5009005400c036900910740709040e900 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 711849397 1250 711848147 711848149
    0x12010c02071d06150f070804090f150e1503160608060607110f130518010f06030f0f020613030b041a07020a0b070e060418060f1d0903040b0d0b 63
    0x4188401054080e280e0380c0b218960b0100d40d50040005403046202d68a00d05414540f50b400004442207845402c00050791000b49140c55501d9800a2065200340c500e070010540400915000b04030b4104500105541518201240d120f60304401518440f03035100f0311403240006840410010708003043d610078001d440341c0f44c40402088500000c29043c0504024403003400002c501903000490160101d40c4071603545114000f080d40b542e1004d407175080c40c0d8100700038000003042004d081944603245400900050084002e800b040e82d0180c84002c21003004c034a42e420200342080711074241c0510050145141c100440d01d0344000709030701d4009594100341c40302800204241c0214091041d56140400da98514002601030344039142404080c203200e550381d0014410a100355010104624002c00198540380c554040d0b4140d4070804a10705000c0d0b00d080404140500c81c46864800c443c0398a60715500000302c011480086013002e0076418040c070081c800421418200c001800290000b980b0009540385a20 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 711850647 1250 711849397 711849403
    0x60c2f0a09200f0301030809010e0a0e0601080109110405060711040509072412020c0a061a040e07080325020315041109042003150703020408060c04080c090a0b12010c02 74
    0x801420b820b00100709404141030f0103802d40707045a0b0040c003491703210380400005a800c04040300b0350544c0b10f40444070129001042c030440c0c0b8055038082c0d03521b801d03580e01ca0310350340200c803041c034512280c07094140402c03c11807604800425a051061131803c0fa07003803a400100d000ea4009031000000c83c1c001620900c0101c071160114028440d0030034030419200180c01c0c01902da0f448d42c410380c0c1c024503000101900060810400900030f55407140040001071920600001e400000241c00c07440f86007000b404002c40000001d050741503445090145246c0740c0300c00c0ca1080741444500c5417000c11200d2914940150750103100c0c4000402d80b8008113242440e080c034100c0f04a2000840040c4500065400d10011070038584541c614178441c410480003596026000038601701c4281e0100c0060000881041410b540c1a005030080b80c011404a622903140da00c6d0300304403402180039003c1164094545500c880c5000600f50350001d424020000d04156020040380c07000047c4651401980c1d110444444096410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 711851897 1250 711850647 711850691
    0x5030c120322030e1e0d21081510020f010c0804021c030807081308041e06140702091012050c030f0703110909030c061f060c2f0a09 58
    0x690302200601c0020369002c0c004804c50020b040c02217110402036426600380050b85506004024100c030740440b55890b01511440c003015005e095240f40416100c0c090b401040282d002d41c01d40c05011000c071a060b030610204201002180007103104019083c0740d80403003803203032b6036254400d9600c2a0030b51411b070040c840746001c10403020b0320f801c1d4103c01110111754800101c54010040d840c0490702ca850702240d00201c8160b401028201185c000f400185c0200500048406680301c2110440d480303a450300182c414501400148140780002c10007070f4010710b400744503e54008034100400c030721607072503049001c400b0f25101e0b4110b45640c01524107984c02e240400c400d0080c04000e078000c041d042c1c11551026408454800388a00444807a0082000c01e070041c020340d01401d85610443d10740d46003203200031600000448101102e00c4140202140c4c1c1449107255034030243d0011000842c1ca0b450204280b6030403841c5101d040103120b0030507180a2a81d9070300f00e0320300400b070194010640c1c0c80000500c000303054403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 711853147 1250 711851897 711851941
    0x2306011a0a0e0904050c0315180f0703170415020d110c01120e07150903060f02030403170615040609090e010504171c14010e070206150d05030c1203 65
    0x612610220780d40c000310400d035200701034039592110b444901c1c080380b91100c0b200400d41e0601511100444080d064a145d42c403035000b00c98041805114500c1c0b0740d49900c04182154102c2c4c1100c0010710108050480d1420404003281080e0700e0203603140d0802c01e80c00c001c2c045100042c2c0120800040316035009540c455030081c040050440c0616050003e0000b4500008401c40f2648440c6c401c20801c01c14442180180284034034080780012031354005000c41902e01040300c000d450000f102c1160351052090302c2c41554140c0381d5440c100f9800c5c40f240303406100108100e0b40101c020803070b84940c180c80300160000309499110254001d090511181c280c07803040f5040070145e80b4040030000842d952001400140041c080328a80e00d003146e19440c141c6480342081104801d081854a145c40389900340418100e80b000502d440c900c0d105c4050481e15550152007030000e05025202c1d11680c0c0c508940582030040c0300e1001c4920303124041c0f02140c18155184883c0102401c080f04000d1402000031202d412011 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 711854397 1250 711853147 711853199
    0x7060b010809280b09010506030f0304050d0f060905010e0d031802180c0d0c0f170f0c031008010920010c0803040b13050f070f05041413230601 63
    0x508000c2032582c50b080784800d41d2040c80c3c88044001011001d543c10080c0b9508a500c001c418503140c142c0354060001038070030360301901c115215a08119004000c1c2c43c181c504c000c0150010116031740320052140100b4206031201c40c0c2d01d00007140007c100f4071032000000a6607015140c401c2c1c09c00000360840d90551040d4891014200c7c0c80d10041e40c445811840c180c241d00d500194a80754580c0380180b0380607030078540c81014500043e00c0100e9400291040a14140d03541e00c25036040310b4001100c45800948040c0030100c1201e0100302025488009194814580110940c4003659105600d00355502c03c0016101140312080000505500d150725110360a002e08002010540b030781c2d2807840d00c0c80001c002402d0701d0542c2d8003242e107101c24000e114140341e410004581c29440130004568681090344110030100350350100c005144d04040c0110101c240072249002c1440d99142c2000450f10f2880e403040300e141304001a01a4064240c103070550309501c50b500188031640c108148028a03081000c0b481140e50 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 711855647 1250 711854397 711854401
    0xa03090f080c13140403170109021602040b01110102070807020a050301050420031e030c1006080a0206090609180907060c080403260c010c02071401141806070807060b0108 75
    0x500300052251500c00d05070b4140007151081603c030001040c0400c0a0328a2030b16820501c4141a40914217140052403400001c00999880034a48124800c141000d503100300407804160151606510001c3c19034010f0400781380140070700100500b260702140045951580c08034060301503041030034a10001e00400c1d00200454100364503900d0800c1038040c10b8644031801101441500c0d1028400450086140c042c030006040c564481c03141c07603402c480c100c0f00e0503214541040c020700e5124022507007154422805040a030381a5020f1181e6580b090003010b400c01000c000008494030380200d196030055200210b403d00d8100780800c9420901c42d5806071003001400d00c21100481d2070780c0102e0b0f00710b0350b0041e02200128486082091400340c45494a1a03401001c00c600c0c0e07100906410803a007910b060fa0a4903920ba40724060003403408010000d1030b0001d907001c8203400020318950000d05420b82e22404002d0341d45450390001c1c030b403a4440c0e8821a07050401003403c004110442c001c8000203035003420061024 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 711856897 1250 711855647 711855659
    0x3090c27111606110f0a02060f161107170106030302060901090809060c0c031b36070504080313031a04171e030a14160219030e0405090a03090f 63
    0x1900a09810710b86101d0341040320003c00034984e005241d65024a24150745401d15602070405035002408108098000e5000154001e01c95094441c0700d030201e03010f08000030f04210011981c0461a42044a00e4814004040b0740001c11001c040d8604100c0000030418a00b1807500a04100380500705001d42c0c0e06110f865000a400780b801d4851584c402d4603a41d848048585803245080303520714486030540202540021303c840004d5449441d00c2098516608258803d1505e030a061044600c0e016076690a014031a800c0c8120b110b500d410030359615045041c16111903d250071b540c804d10340c1ea046060303070074000c00c100695a00303450f02c05404042084100c1c54540c0f50280501c219013080081c5a41c0014040e0403880e0700c4a00c1c0440700c8440090075120300c0d02e458040010185504102801c0c6119400645803103100c00c001a0081100c3c1c4c040d0001b9200001c02c50314030510840c1c03c6083c00f14001c20381030f0340c1c0c54502c03800b0b105081110081c20203205034100034080c0141e9401c81c881d5010305a40c04d0241e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 711858147 1250 711856897 711856931
    0x70b0c280e01030b01030204030816050c0a060203180d0510020a020d05040302490c080a150522031d030d020d0804140102070c03110616020105070303090c27 69
    0x4046000c0c03d01203030202d0550012030003407003160001003c0d048040740541031a80f88000c00b03003206100340c00f01d5200007051010803c2e805018860b03e80103034010054a25843e90030069100c2d2880c0140c240000740a150f035a03541003100f58804124861380c040b0701c91f40300507410040c014001a050070014601811030300072031b111181e4509030741c03080c4a0441c0c04480600040d141c1001201403418604c51180651b0081004801c01400603501c081489001050804010910841082c1e0014049008003c0700316a500900307401050780a498121004140c41d0802c017940410b0701c188255a00801c4c01d125160000254001180c814000c1d4040000c02030004d80000d0303040003100460814880a03503440c607044108100e041d4041c2150b5001048003400c105041b10f1a4080d40c1c40352042c000c0e003220100c05c1c00348a010345c442491a5542c030744003000c003650040009224036802450301240d0041c41d0344622192002540c03144000e03241e0090310740620524034208104001440350140825a0b06400382c2e21 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 711859397 1250 711858147 711858167
    0xf0423070e01261b0f041e051c03020102090d06020909090d0f03180206160c09020f03040308090f0a031d0306090c15040f030302010204091805060a0f02070b0c28 71
    0x3580e1801e10021a042803c0d00c428982d0150854156a0f1756074413000203440d55070040d00c520700e80301e888051402454201e2440d08002d8480290500d14003001c0980d180302140348207482a007d655003002218644d484415000074803501800c3c0241e82e51030140e0911081c804018a00070003074104018401e1036560050003e00c950106281c00328055201d40d9509200c00c445c420001c0d4040700000c1c50f0800c0892240401c1c80c4a80220b0020144561300d216410a0788565004c103402ca0104000040009000340710654001c9c808000f00c4180d440002c205500d040d0250f01d0940105103484400d06004200042200e00380c40154041c1c001c9040c80e1022030b5443c2c1348010b005c1d1107109124003198078105d010b42694024882c10b5407150810740c0d40e08003c0c0c001e61060054032015401d1400d0034500c095048d40c800ca80c00d500c4001000244d460b43c640c00000e05104400740c26070350f02000740c90003088569840c01d00409002025681e54541e4141084003101246010f448070103003d0010ba603690b801808500c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 711860647 1250 711859397 711859457
    0x110105070c1e0b040803091212010e0c04030c0312030f050a05010306060602010e0c0f03032a0d0c0f03030c1107030302071401020f1908040f140a05030105060f0f0423070e01 76
    0x6e4586c0c94106086090403180414034200c1c1801103081510200840300c3e017412200d444a01a081d51078a44004410344220300000c0c140e51810314082001506a05000388912250314000070000c2c04488030409480c41695200c4400e912040140140000d52048600030800343c0020031010513481c05143d00d81281540317040c461503001c09001002d440900c122042800f8999400c58403c5102c040d00f8062140b030280c81c0308901c0f42a6600011a00410f0304100032500b20908240e040210350f0200d001c0c05843e50340a0403c150480c1d0310810304000c01050020350712a070054a070305410b010320031a00712041148a41194032088440710311203000709c1c1b9034541c010302210f002c400140d00d0400780e1440c07051307a00444004045107000107a020210724003210340d4038210b50321059580c2d0b4800309070030fa4605403040303079000205403070b000c170145005500002100c8001d4004560030001110220a40c400040800f009022071001c04c40c4480d4040b002403400c1d0800d0030174079001e00754240041e480b070f91485070311 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 711861897 1250 711860647 711860663
    0x3a0e0705031609050c070b090312100f0308220b04050f06030f0408031e012d0e01181b030b090f040f083106030e0102120c0a110105070c1e0b04 63
    0x4103174901140011503100e80d40008042644c0e08003c0d002560300e600590394008500c0091012503502c1ca22400c0007803c40c0c1c60f03001554070650540e00c6003003560340045291182c7c02c011723049080c003521240c00220001c0c4560b0244d192601e0cd400113120031180e445491340d02c030b000700f0802c004075962040302041d0455084115262280c2e41c0541c8034822080300803580c04042c0360200001090340548903055404800030100340206881c42140220039412409000401041e401c0107005220001040b88002080710038080f03011658018916400e000ca41c0c0900f000a0301d4689411050901c1c0d600c841d0401c030602c9172009946400e40f141320090300508001000e032a0009607034040c1420340007503a1000f0340c1000705079007549880e000300140302400344208008281410170110084506100b5100d0f5a9a042c032503030713156521401e10720500d910280b4a0818098115410562100240304161044c3c4141d125400743c0400390074502401c51030f0701d507590103414481d00c554000400c10440c3d540c103e030f441144 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 711863147 1250 711861897 711861901
    0xf150613181b060f02013305040906020309010c11060a0915020d09050105090703170d11040806060103060b0307051608040510020a0210020a083a0e070503160905 71
    0x45603080044010014010351454400d1040451290b400d032412148035481e0101030010070141607090f02ca0110442d40c4800c203000f490081035880488054262515200b40c08909480307a001408441c400031041d21890382c0402086806207091141c0c00581d4101c0c185075070324440c0102d840f9039403440140004c120a0700d8038552020444040340b5100b42c101c1e0402c2c1507450b044140e00850003450080e0042e60702d9800c1201041c0031000201d0304000780ca420014038051002c042c00c458425600904807910059600c0041080d000d00d03210241c405004160301810325402d2072070004060381c210381c01001c00c41d1810001d204000307400500302d0340300a10040b21003901c0700b902e0600d9501c07401180d200907045042c03c11181c40c00c60b400f05958090038400c88880540c20b0140360100d90b80e403816600100040c10810a844404182810100f03844205d4198044000f00d41e904444880210944000d025a200d214840440005028150141800f0340090101c04540740c0031458884041c421072094a0b65040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 711864397 1250 711863147 711863171
    0xf0a0f021914010506010305160516020405010e01060f03050c042d08010213080a0809090c0c1501090e0c0306070507030e030d0c0c090209090a2a020f150613 69
    0x144035881c88080402680e40340382044108002c01c0d541c0c1c880c40707501c0c1c039000070655030107031080c1d5000c0d00760002000c140840c1c860b010f9501d98810030075103000301c01d0380c1c3c081d0005942da405064041c1c244540c1084965250440107400c40101105001c01e140c1808100003140340000c0c1500c0031600740782c4414a0804407a89a400340880c64001403191b40720030040820011015001880c401c07040c0c83c0c080d0f010b247d48510090b1103042c0210001d064142c1000140d100e4030302512120f800030203125006203424030604204c0d241401c3c03c403591414005c0c0400400c030200240c4201d42245405402420040c02a140000d4440100800d04014088041200c3d424148594800900c0e420090200e8005d1b94840c0e00203004046140320440e1112512480400c0509443c000c1d520481030203420074800303854105d41d0501501410b1501d10070b5411030888a1000381110908015840300ca4024092040c0c0012445003050000c2c4480803e5013501001d220103901e501e100303411180c0003010000b4004034085 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 711865647 1250 711864397 711864403
    0x30403020d12081b340b070e061207050f040f0305152d1e0c090a150c0b181b090a0603080403020d1a01060201020c0d0305190b0120010218060f0a0f02 66
    0x7480705c10004080000c079020014120a01d5024240c15200c2404580c02e40007040390a104250840c80015500c10109a029020ba0054100c0b49075800e5003c0c281500c0d040c421242030352039402951144c0c0201d94607094400142c0d104c0d0f810800c20103a203900301c003120b100100040422002c07503070aa0791860010301e02d42c40c20b1703000b480b0400708203000c00c4c01c60405d0780b900c0806400c070350022031051506080026101c108540965040c035410b4032640c00000854a510758003d03c010300c80d016204122110124502007401398064010b10307009552070212101007841490b04005040c190064644041880810601310940d01280d42c110b4030030342104034528082c5800c244031644255551310b80400070841c20f4040d00504585e21220f070440d0a860f07051801141510000d603100c0b0b40c240304110401c030700000b568003c44003101060600b105040c6024080749102501c4034650010b03a50701140c800c0300034500c200d1500c3c10920480d11507051492220b01300d22070740301e000005d1044c003402c02c0790310012500078 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 711866897 1250 711865647 711865717
    0x9120b07030b130905060105180c090d020d030c030e0303040b040506070c0905010f15021606030c111e070801020403030807050309010b06070c080606031b010c0203030403020d12081b 80
    0x3d0806840c0d40049030041c0c0240c43c0008003151203000307030000800c49003451900c4500d01760b8201a04200350711003080d10340941e8450341d60307103401060381c8040c140507813207a4581c0c01e0158880e903510081d40c0c405082c01001440002c40b5288280c100700020032440c00d03020140d800781c030812206913584038560304c1d2030015021240d000780788542c02c050000882143d0710b2074074000c80707039040d0a1418070502004200e032110a0100762605501d2441740501003248039501100071440305051039000000640d944034503000c1420200d00c070300c4c1040c05814140c4181488031000900828009604150540e0b80c041d00d40319008141c007017000320101c00240721302e0094000c0690140c0140205076150014140103150080311701039000307503108140101d0340b03600b000a010301c031203010040d01c881030184070700044401c1c3e100168140e0380740c4800d10001c00540d561414812030700d8821141038001003c2e00318050603819009001c80301800690520194108a03041110030702c4014155000c00c00c0c3c80001c00032082511 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 711868147 1250 711866897 711866899
    0xb090d05011d120901090b071a100f0803070b18190b100512070522020d0e0c090c1206010c0503070c050103060f05150306011b051c09120b07030b 64
    0x200704003400c81481c00ca50280c00e0a6050007034607140c00040311844914444c0003a000e000030450340b810040c1d01704071070191503013601c10005c10450400c40d01500d0540c84041e100307801c200085c55800c01102000085030f00040459501450425201c1e80f5081d240581c001e000000c031850120350390045600620a83d00c03d445140700e5403180c540a030501c0727a40d003c803c54000b05101d0035180085818070301101c0764030720340504600030503017141441c040c0101101d02c16503481c84c40c1424012029903110030300190400d080540c0001422070110034840d0b203421922a441c3d400b6000030414131450380f00150484180074040002c0302d900c0d89036003004945012100c0d10243c06400080340d00d404205940749032004030382c1c00740c1c2d06000b11501d58010a10307a60b01d03803085503413000e03000c2c002c24440c10300d070f501030b5902100504000c004400302c00881d00d010031600707104459079084518403071611460380f012099100314a181038028141880b100010311000054041d01c174659050010305031a2298201c4080740394 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 711869397 1250 711868147 711868151
    0x306040c032603040303111b030904050a140109240306150f050d230d050c06070f050703030504060603140f150411121507050306091308040b090d0501 66
    0x58181018034030303840d990100302e40e009803010000030550480c0b044080700c0c41c1c0c2c4501d020320f181c50f40c0c0c3e01076004003a03140e070502036071030305022a01c1c9840d56142109487c04094010350303507554420b000c00c000c6410050070141d85a1503c440e1081e0301c0e07031048a250555a00721b0700010717240c1c06110384208503540c43c5103200004002500c0401001a190440b000c68600608540c20707481c3c60300c816900807e814052182c0005000c8840703030203e54100203544400907215400441400982483e1313080014010904010800006004010a10070401154040c0746480e01c0c41c1000003562005200d803041d00d0b409003c1541314400715040c00181c0d4400c030020b5501920000708140b070380f0790454441e100040c080071035000707120154803c080040c2c9000d200343e41c80040c10800281031810001d10300301100c0f00b1480c912400801c0c00b42505c902014a008201c00d840b0180c481c070304042041402130000b0043d0580a52156016000441240a80c1c05482485580f03e80720340b140400b04014004569015003658 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 711870503 1106 711869397 711869401
    0x2031c1a03010b0907030911030303010303030b120c012316110132030c0c010f02070c05180f0705070c0e10050d1509060e1509060601090b0301230306 66
    0x511502304e0f1080c90f10f0220200f49190002d07001100031a91710803001c5d1307080c030303007412440310540488000b0200100d0b0100020801a054050fa40c8001d80759880040c03480f036180c4c00d0310104401c411164084800905111004041500481d40414008807440200d18038050300f0044240d1b06007030000980303804140040711640018044107a100e070a10807011500e10a014103000d07140c4200e00540c072040c107801d04414000455008a1194070700c5c0036004050901e211a00b80e010f0300c01d407111103082e91176450546180c41a41d10050030300c4c034590404a525103a113030519011300c8400d003050380c10503241c00521038888034411018100300060030320302c1480c14490b0469443c076803042c20046030281d80780641c0340c80c00082c07094110b2145210010048601300c10440787c1c7d84040b09180c4242c520b4078140760122a840706014218801d032070744101c4400c0c124400c208456a09018088072517074 = true := by decide +kernel

theorem cover : BRFrame.Cov 711690647 711870503 := by
  have h0 := BRFrame.cov_init 711690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 711690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 711690647 ≤ n) (h2 : n < 711870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
