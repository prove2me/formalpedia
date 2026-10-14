-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2940
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:11:28.781996+00:00
-- url     : https://prove2.me/submissions/e0bae0ea-bbe8-451a-855d-4497f156fbfc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 528597122 ≤ n < 528776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 528598372 1250 528597122 528597127
    0x303070507090b030703031710030b0f06040501060e130911060418051005010c02040b0103060803211f0b0313050d03091202060105091815180615031005150a0b 70
    0x5481d007640f05410302c014060300a44800c034659200034203411540c125230602100b140c1c00007880c00c0012103c46015551280c141000d505084d103180000c1801118501c1c0103520380800030901030702403820783c40081d800404191200e010b03038203000301030101054101c3d0030780c075514200800f560701d400250010f04015010403500800d500c104100707441d0058503085010f6030010051000b40d0340400070150b00345e010342d00800c2c0052020300481c02841a51702000f994080490341a42b980381041401e50300b00408016194a5100c914980c46116468162050001c5802d0420006140b0001c06564400006a03d801369035607a0740f5a1410003004540c000e00080e5500e40c400c08228201135019030380f40d081e1009110f150304000c041030300c0d4000a000a00850019422419081420410304800c0100e00c4410320300c0303082c10049111860345001c0e2900f19805001e002070300080c17265401180070300c0010300030000b03d40c0425140b001004060848418048912050300007a10f69112200080032070140856 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 528599622 1250 528598372 528598379
    0x20409020313021c050a060e0a12030507020c0f0915011209050726100f021b01060501110f030f03040f05010e0c09330a150905100504210c050303070507 67
    0x2900c40b58200311200d1214103407140343c010171400103800507070b5588840001a030031414844603117406525a0000c2c418500c0510754907030194140c0000b4011a415022a540c1402c11000c0000060101044a40000c7d080000550b81c10021301100038400040c180140303800d10f0841e5101c1600c5408101783c4859025860411000d000700b00c040b20b40004603594907180a590a000544640c40800c3c00d02c0350070b0721800c800d0740c5000b135a8103ca054401911a4000c1503901c007088502818140c401d15000c01c8024101135098100810040e10210701940030391324000c1440c003001d40603000948103581540c80c0e1000e080010780c00b4442c0410840d010f1006040d4098240100802c10100420601c921a502c1c15100c186500d10540c84a048410b80c0140c06420000300c003042d500c81643e880883c2c0c3c0c100c86180480c190780c124060300c094400c1542d4001d400d0071143c0044d10180b040d44070340c100c1c00151900210340314101e44042c40c505c512590300c102005968000003803454201e0f03d029211038000700d03801c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 528600872 1250 528599622 528599629
    0x601060e01050906090904020a0504021c1a0607060c120501030b0402040516020a03121b08010311190b070c0b04080d020618032b0504030c03020c04111b0102040902031302 75
    0x2480c04410928019141c00168400f0512501035008594001c500300c60103d011943c0718a23480f0040e0902810840d10b926000c800082c2c4810b44241030050a031070078800ca064111000c1018140d8440500032620b411041d81e5054010180030341000d0800c000f010152070410410300a840c002c5002d440cae018070b00e040c140100002c560003d0440c40300260a20310a0306601c0e0003048600320280c00d4281502501d128191036400b40c000d003680c9074503940c400000060500d0700240081d06884c040c45150304560002c2040c04010b00c42140041d8600c0e0004004000c1400014001e1640500c104c00e0320051607504d02a10846401c6070300041c900c2c1c3c0005d0803080c3e901341e041080c41c1d4080320354900e030441003441703003407950312846105408000d120140903680510030000d242508007000c03d1004101525050400801032826803804500502484091a40340d18280c081c50b0000e40b801000d4620300b0b1b070003003000703000120809502d0038255000d02001514112502c042c51249040c031034201010081131040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 528602122 1250 528600872 528600887
    0x11070b18090402030d03270c1802030f0a021809150f09060901050d03200715030516030b0a120f050106081b0f0f030d1215061409010c0212060106 64
    0x590140c000700003048003682d00043c101e4880006070800050a44420740310490045400c0445543c003074032040003000300001032095104070752941140b40756142010380904c1c10f034481a212503070b0504405001c02c1d50400380d907004240100315002170031181030000000c22481d1034120b9813112a02e83c100048507050030000a18180e8075011038265860f860540005520040107010300342c010040c031301c0120304040c000c0ca8907400d90209800321100125120001c60781c3d40c0c03038a000f14040721580031040303003130755020740179090080d40d0400301d0080d00304804408800800210f40707088e910848405c4001003030003010030704551071800390320035075001a03281c1081820744413681d00903201a40280100d04640c0060745159010034402c98000d00072406020000d03040140d64182d10b64907001d030000d2110b8440d04813280708004400680c090000b0140c0c030940b5107545182e48202d10102d42040e0842c01100322074001071030250b405040c08000324810b5008968030030700c0d452400b2856071000f8010301450750040c44 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 528603372 1250 528602122 528602167
    0xb0114010203070b0a0f2a0f050a08040212011b0e0f100c081305090a0902100e030a080304060f0e070e09010204032001030b1512010807080a0b0711070b 67
    0x1145001c0042c0c0e01e920750220300030038812440b55241210f0000d004c61f60000b54640704000e4840b420b50a40e00e00b03101c0c400188441d0140402c0b500480400c1c2e044c003c600741d452840041d2030703906a0745d84680910029000f81501c1b50815541d400082040e40400c4a0100184d4610340e40c401c5004011b40c1400070762050421001e10904140010301c015650002d014842c495020600c152036841a0810a500b15801e0704000d0344102100c0800603001c080350310400c070003402110803506038a80100103940340c3c5e43c5000c503190181c014008540c041880d0314021604a07204d0f18001850100c40703402101100c140f4440c0002d50303041444100111281d400f00303190003003000c000841c0b4161555503851801002e150050b121172a4140c41020030b603010342e200340e80c840801b8007001400341078404010002c4d4003250080b006801c1c64000801e034070100003a14025284400024034104040c0d45500f080f05100505100400003d80c102170345045045c010840200040034100307407228032202c400c401c034110301c12 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 528604622 1250 528603372 528603377
    0x609040b04060914070e0604020408030a111903030504060b0405090c040c0203040806040309050a080606031c030f060905160c0f2a0f060e04180b0a0f020c03040311010c050703170909040b011401 85
    0x103102404000c41100c9a402d00ed0030699000c0c0c0c54401e03042e04110300c0da82c607280c40381d0403600700d0400d064140d001107102d04d102c3c138000c200c0302c82003808210440300b0580c1d100b40039520503880c2a00c117003001d0b40840c400c0c10080c0122401c0c42d580d401c0301032400e5412541100055038078401007103641032000c5200003408002d0080c0c13105291440110b903039000c2c02e18012004210404003030044901036881021524184002405565210038200015020995043c114548001d10b02d0741e6140c03103a140c20705942c0d881303a1110210203042e1189140c0d060504000b402c403050720141c220f6070502003000e610003080e544400b860500c0c80c009025156440382d40340c09004038200701881044c4d4510000c6d00d443c055000310400e544d48c07074404d8403000920151190100c081d100003840300005400002074030840c0e100310740d45030044401c840111111490184000d0466100d490140005019050703441013a8219001140c100242480001d0101005403420340b90b80c0412001071200c0040c103144000700c0325003030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 528605872 1250 528604622 528604627
    0x1080c04061e1106070c0c05030c03070b0f0c030316092c07050d060f090b030d050414130f020c01051030020627090609040b04060914070e060402 64
    0x840302034854118032000104410750000c40b00c0c2c030759000f051800c28100ba04821a001450101c002070149500715905a580d25201280050316103400100900d05060207006058039902d00f00149900340c010912482e208001480080d40f00a0100050742c49618041c41d440c0206c603403001d01034a03000d0b060700444640b144503448401c221010701c060015440304184044c04d00d0399030213022a0305001c1c07030511074a85030a041001400030050b444607001d58040740e00411065514030100360b075030240f081c90032000c102c0c140800c00106218210401540d0400703031002036140d10b5400b01200b100c40c1c0742e1040080d203a000c10410542c40c1d0910450744c2c080304551320700c01072505060003400b41500b00700c3c3e14030384107050070503102c075000f01c074010345803100c0d4040c00311350700e030f1000440055050901100150905503900c11490083c0b43c40c2c011107000e076401070065140b5850ba03072900e00c01c010000b80255070240d2a20042d000280d40c100c0d658000d080418054451a401c1c414070360390141c006840c2c280b1a9005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 528607122 1250 528605872 528605879
    0x5010c0801060806240309100c21050105030c011d04020f0301031203060501140a11060106020f0d0212192f01060b072a0902040b0301061101023405060a090201080c04 73
    0x80b00100c5100c0c201782c01d41e4980b1b035600c05e16010700c0d12091a080ba4005401d00140c000e0300787e0800e0011307a00c1400e803140d603007010030000010001c81e40244206940350740400c00702c0d080ca5001d41c845441c4800d5901002c6c1c880480c07040450241d0b0700903400a264500008010802d02060700079280b074030255441d00f8401c140c80d00000a05c40005404ca9003141c500001c6d40300951400fa80c5520050001c20007540c0e241c0d80d40b94006511504034007044003441c080d207245c020a0130b1001c100d5400c1030b8400400d00f4104a000c8e60b0301c070310340041c800c40c0301c00740b29034000b030800d50707848481c1020300c02c000d0170401456000c031005809003514103d40c40340c1c29440b020f0082c0c1c400034034125401034101441944407400702c0031501c500c045103440c41d40600d4810340700290202d18240746030002d40c1642c801e0f464141b00e801d511040f450803848ac40c60240344103803103113000840416400c00b008c6028600180c090001081ca0f85a05040c50740c01d40e040440d45a0321070700b60301156040107410303a2004400742d02d40d00f0a0300c0d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 528608372 1250 528607122 528607159
    0x60d0c05031b070f080c0703022d0a0806040f03140c0a02031c080a090c0b0a050c01111612140d020408060f040c0306050601020307230c0915010503060d05010c0801060806 75
    0x31400109096004106920061b00030881e16008580040c8503480800440307068620b064441c1054020f448410080c000396828442c2406080750707203c40c001e107040d0f41e464860f00244202110304a04014000c074103030140a9101c00980340a000040241c15120f1003881014a012035a001005000f81304503104414a030700f22280c1f9034484480f00000ca0000440e103418022070344541c01000211201003001c034465507018010b400c1a81c0240020030580c5001003a000316801000350024114040208800005e020300d00080b410f400c01e414601050a240151602c494014030483c4c00a2076010038200100c400c200719045d0031440000c001d5455041507120000f0902480c080a010b813511903010820f80d034400c204070741c03420343c01035001000c40516121103012050702d522280d0b038134130440054114625156422900942d003c1c103400880030310715401980c1c107800c0205202d6126800c0c4113100041442030040751409045949d801c00c00d0341c18001c024052560151205000e00c00d000d12100e00f001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 528609622 1250 528608372 528608393
    0x702030a0e0406050901030b040b090a1104020d09081c0f1104051009091406090a0524010e03010509010507140f090607020f030706030e0c09100303080402060d0c05031b07 75
    0x1414a004032011580e20040b90191490703901c0a600180b900000000380103100f800c0601562044c81460a03070b4903040c070b00ca40e441081c843c0140c0040543c0328000740d145801e41c01400c001c0c903810408580c408140d03c1c1c0c02d24603027040342d0042955425192207034461442c0d2140c1e210780d0707407400d200f002040c0e159001e5035500c1c007550069901072400d4031513000030b16000c0e0596400030040e1074070500840d82c02c8400c1c0c4003000b000741d6040e80100b02c0780000c95045541800707610b21410302c01c44001d914042817110307040300b0a07044200d10f062025062030044680c400f0301805200381c1442c000400c007814103601c010192401030001c08031030300b800e100340c14100200d01d04a40420f5030880d000b6450345441d0002403011800c03114038989c548590384c80024299015040742e01c1c00c004240598190907041024070406500441c1c004500e28030245040c000a80a0003a440d081400a42420304008c00106c6038011945800c44080100d40301004000d030301e8903145c0010b03504000140509040c004207907200840d05 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 528610872 1250 528609622 528609637
    0x81c14070807110d0507031431030f0f1101050a05030a0f0b04020706050105010206070e03060a020a03020c03040f151e0c1401060303050301050f1f03020d0b0d150c020105070203 78
    0x1c01e103000400c40d0280b203545003881e80100340c419a03004900c3c8200151a40d840110100e0129000c04000601e0191210943e5140d20500c3c0d003000003400e0244c80c0384001c2c031800d40d1a1159420450000c80801c1038000c0600400b84103104088000c900341c10541c0d03861001030b80362410003500300200b0702119885425030340c00c505002004038900b41803140d0000503000032240d41da0030902c0850080140102d80d00443d0483d842a002e5550326240c0b26000c40300380041c40103c42e0560b01160100b828032036651b00502c80400c06150040c100707041400440e0070f641c40f80c1d00c02d40000c00003c8050000f001c24000464280c0074a00300071608124801001c5000d0200e001d60314140443d1114500c24400161801800c83c5840c00003000840e460340f8025003c2d4000707006260064230b2581d9800c001d401d00c00c0d414071102841c1c0710928419002024102c0180d0300901c00f200090342c6582400c1500e8940a010701c1c01c55200d6080c9440c410021038410301150061003140c02103a05101c14026155000710403280030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 528612122 1250 528610872 528610877
    0x804180e120421050111030a020703080a0e0d050702061b0a061b0c0308090f070f0e0a0c020c13060b0307090e10050a12020a080f010501031b080c060306030a0c03081c1407 75
    0x1074200360030914010003101c480454014000810000003120f564002c101c0341c1d00c01c1e15080300ba602e030320dc0710754103d03001505661050350208684a0041d03004001402c000352000382401e16210381001e0701500c12102c1e103600081548108200d01c10059a80a04810010b905c0742250044243d408000c103441c00803d0003806106c1070b000450020b203000c0c030132801807842901c1102c0c0c04950340c200c91001041c1c2e0380b207000f100e200d4510100d804000344e40901a854520344c0d00070454902654100844201d01c428420f00b00d582c0c6072000070710400a6805180300c0c0409468000c03c0c9454150030f0a40c41d83d0050400c3c004103a00704060103da981c4802c00f00c00c1d117251078820048c1d4807c80c408030f1840c580701d400070510b512030500704100d1800150401c40c143c0c0e114400072446a4070440c03120040b01050f00490800d900082d07030000c05420404080c607403060006088902e08281900e8140b40c02e12a5082511903200c006100504d090074003040b5088022111800c10501c44082034040712140041c040f4000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 528613372 1250 528612122 528612179
    0x7080c0d05271503190509062202150306011b08030f0604020702090c0d0e10060f060206090309040f0f02130f120b0f0604091e030909060e04030c0804180e1204 70
    0x103a2017480e13120000224141c01c0200120f04214402a540d910b080f109c0a05d111802010068001034245000000c10303800341020401107100c0324000043c2d000241744904101446940240368015984200700c001e02405019607241131010350292800401407049003d10b00400032000140c8846442c140d002c1a1501c040303484201035441074001d82900c00700c0c0c103154400c40c3e00c00443d94800b9441241201c0410f600352490a80e20601682c0740c0340112810200d03900f044c40201c120341841d821400031080c412a00040060036000d982040b600508540c40c5440010001032090403012014940903106256154904114960342e001d1407100091000060800000202303c46031102e81050020507032042d56410741c0d04040c01140074400c04144254001685001d00040300304181c03103030760184c8103074120b04100d43e80c1c0c40d20700b918a4030918804803101c031020440042c80d500c60491020411040c06004510340714800400340c075112596103040010b1800f0003041100c01e5400031941c0c40200030315003061 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 528614622 1250 528613372 528613381
    0x140304051b2403090106050301050613090516150f05040f1a070c0b250b01030305030405100c020a0c08010c0f141c020c060f0603070b07080c0d05271503 67
    0x74540e4004245500c041001521002c0c0310390040805144601c00c080b00810540d940c034400c02d406d968041d0f40c100d03000413a4250402403805603800408505003d14100c40283c00b42800c0040941c40650107050090810500c0040c1c0d1503001d98031401084441c0b0300b2a050a092114990034103042d407181c421440107015030118030080c8a42500d407240c0d00b00c48400a115078030114220f096200582c0c04200084150503000c0314604110001e420b00d40001040c0d103542c2c210760f01a11aa8400b0b40241c61901c1140d20309100840f4038042e03009000c1e101ea020301481d50461400304100c00c0e250708400c0080c0d0508240300c16065201d501d19070070b5107251034844079140c2d1030700e4400450b11440c01e80308080f07410440e01541035001030f00240300c0d82341504100e4455a80d10a00b01d240c3c01c2e01a83d009031305412011082250110007800350805d0740c000c1209a00e0f080d000d1000d2446c204100b041a4041503020450f00c0d8181500d03081040e040140349401d85080c5603440024000d51145501087c0148000c400308 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 528615872 1250 528614622 528614629
    0x60206191b03061a07210e030d20010203150415090903021f0b090a0b06132606070c02010c0f050a0f1506060e040228030c140304051b 59
    0x2140709240c50003a60180d5800c1100080203040240144034068040c0540000c5101c0c400d0222405180c01c880c0800281940c00c085002200500d034000c1c04000071480364260030399003440707004c41c4031085072900c0040c902d0b040301c80b5100700214032140c0902d903c1801017210088900d40c5403814444101d6002405031420810804030441640244c1e228500d021040030400d41c0005508411240c0049005800ca002c05101404e640e900c102440e00030f4891300101d4071000a0360400500319038014401d508040c0095807002590b2010740c040c409201c0b8500c001800da80c1c1d81a441c80c01e43d5040b5005d0003c52410040c094500d200705d100c003e040207101a5820180202c903425401543c0d0300009443c40c030350103400c00710218540e8040c2640c0c01030a482490003841828810b078411141c094a442c08481413900400c402900104000002c40141050002c1441102402861645030503200044d05644c0007000608a030844226002305c0c140810520011030000202e001c650000340d02c0742440081c002010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 528617122 1250 528615872 528615881
    0xf090402061902031213211b05150a020a090308030a15080c0102010c090819020402070b04030f0906030507090b07051203180c030703022b0b10150906020619 69
    0x844025031601c002c0007080a5000c4002d183d200700c003901000302070f2511203001c142074202c010001d15240900f120350000e59130f5411a001400068180640840c42c2219041d81c026100ea50440e40d0760440d40301590b00c0c00c061410310340c000310b400d1004c6061103142c0c1c101504038080f0340400380c52100040009604244203802c0703c0e1004c00c0790a50a90803c4c0da4200317050341d4000440d4540d0241d42441c54000040d8440c0074001d0445110310010900701d01484880c403810300d00c50700181d070001e0b001c01c03e280c0450800e403819801a840f0756a8000c032562402e41c01802c00c0420707004282051300b0101072000b22940f002d5000292411050703490340c1c4503141d00c5c016103010311480a440083c07001104015013044d20022400d40400c0040646d4920000081019101c50440c00002d50060034201001c042815121021202c1c50b6540c40844414203151242c8044003000c4940d4001c401c020030003400300710541504c40c180010350382407228056044c10350180d02c0c3c0c0001884160030506401c1c03000c0c401e80150b0030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 528618372 1250 528617122 528617137
    0x70e06031f020f0d0605030607080403091502030d020a0c1403070309090c121401180e030301090c050408010f0b1503090a02040b1c08040806092a0402071b051e0f09040206 75
    0x142265254240b00803e40500060700c40d0704e207c3d00446000072001070240c25064030075607160740d4115019091850400c0031941d00d600d18002c500c03040c44500c0f0218940d100401c0401110703191010010301d94038110403225490450141030f90424003a0340002a000b503203203004d8552554006c10041013100c0100c070f040b480c4000c1407241c64107041c520280403020402a0b4103990200d8405030800c2c000c891090107030b034140400d07090b0035401000100060091342d8032240b002c54442c58424a45942c4a40080c29140152401c80d08a552820180500c1c0740c08060118000c40c51034a040c11803130000407a039280c42e00c04c00042e0189407200c080059558401ca501703450741c0c6010700b03085d011002d14180500140c106001e081103034414000410030f43c02e40040c0b4500a07806074014484d089000307540c501541100d078000c49800980038010000026000380a044170501091041101d491600c2e042098450440c46501d2042d208400da8074420b896010350400c032400240e4102005840d00d02c08182c0910804a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 528619622 1250 528618372 528618397
    0x6090414060f040204050603010603170901090e0702011e090f06050a021e1206030a0f03110c040513170406270308120901062c090106091508070e06031f02 68
    0x2041100d8010340b500c03024002c0f030007035804104654811050508070b54243c00042c001202404003062028000c40040c202c4000c189440200039644403404a01c15505503400c0015075101c4050b145014450862031121507103510044c004100c1c40c0d00c44861412200030003402c03a82d00c0380002140c60b1704540444d554140d4008060741c450861540200307150300942c80807200440c0590104483d45030011300030340703200d4020017113582402407560306851841481d076000401c0e0044800000e080ea23142d03c0748910401c07070104400b0100c00607281400c0d00e40c0a8509800d032114080c00300f4800d0961003503404210a400d074808000001c1c03070520540a2100301da01c02040403000240c8035250444c0c03909424014207125000340300d90b5456281c421034185207040640d0220005101e00700e0100c3c0300380401500101d0300030000420369101c0301c00d0070a641101450801d2041c401c07070304002c8104100407403401458081e0510300385052980009880711210794948001080720041e40c00c0c0b15540d58112030a881c42c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 528620872 1250 528619622 528619633
    0x9300a051315030603020a0e040b010b07050f070b071a0c03061e0607230c090c03130c061e02030c0a021005041701060303030627050702030904050114031c020606090414 74
    0x402c00200500444d0001700d0042d50411400180180040140c0e40502c0d0b0200000109038206050f41d42c041d00070181c01d13110b6200e5158000e036543c00a11844024018000384559604500d0510580c5d190402a5a919086440381040319641070001600c1e0801c000702c6d0000305c0d001c0c01c000c00c00d038011110701d40180d0002e03001410f441000380691540301d8110001d00ca00c0745040c6028038080d22031010501498100702e448001801400806004580c092030007101080858925203460107180c01907040320020500c1205449400428210420a080c0c040c1c40118034018541c030803951075162620009000e03403550300048442c6801502a079016148606009103900500d0072403e018107a03a10040e40800c0c5001400314481128190b80411300c024171030f44540f0001c0344001e0070001c04009103950118001800000a1541c441c0540c074001c0c00030110180119043e54101800c2a42e0100548545148030500109464000c01e14075400b9004a81d240703090365860a0a945a174000403580f201030050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 528622122 1250 528620872 528620909
    0x50a020a0b1b1206010905010f02100510150809060117330c07060b060a050304020f1c0b040b090601030b1506090d0b1603021c09050307060509300a0513 67
    0xd02d0361107180c0c00d130f07aa0741c003443d03688005650407482c1110060050308a02034410f2f2500c4250400c1b500282132502043c0480e585103224a1720310000c01c0741900040d03503103007030240d0340900700500303409004c8002e803401080324001e010a0399810322600078600d0806030342518040c12282c83e22645a102d04400048061414002032003407540303c1c0f03104880a03850143c00403182c0c00c01038260790360007500c0e407a5a4910780740c5801704003182e40501d200d20b44c403114401c200c11108207039100381e008140c462800c043d16803c00c1c0c9010071715110000c150b003032030707601c040300410204025005217904034051780c2408000074206000300d0154490521025009002c0920540030081da11480c64800c0c80d000c1040c10401d090004110141d1207891001c1c0c41c4258900013406509050303500940225111f03100b242d1508241b0798810003680c42c100c2d0010541c1e000040c00454001c1007a030042e090629003030800407640d02c1e07071006d0b1503140104801170007001008581c90340c91103404840c01c40980000c803082882600e8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 528623372 1250 528622122 528622147
    0x10903091a03070e010318080d06090b120a0201050c010605060307050d1a0102030d33060219020a0909021207140a09271e0501060e07050a020a0b1b 65
    0x921500001d840865901400c0404010030389016007029034540409013002c000460151010b803404018480c200388022001804140040c0100c00558101207151407034804984112416900301a0141008218041c1c3c60303a40880da540150754242001074950054801090050002d900b000e6003084d8004284a1410341080213000181c0c11081e003440800c04400d502c02c0c3c2d400b84000724501507802403042010511141d0000b000c2c01c03c80e4036010042540e0003600c6600da014400068100d6010401d0a2108a81c1401114200340e001c0d01e2051803600319501107920201144281800030360341d1800303c002c6503944501e24480290000444072441e44030004400e84640c4000540e20685c111040046d901202c0d015100350103144800d80100d46060503c0000c0042116a0484070f0580c040c84203040500412003000030203002304000940d580c00c006140c2c020200140076003050100c00e101c020b166030b60001c0e0003070100e540701e0030380c0110340c8030300c040f02c20351082890403a1501000417038903140015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 528624622 1250 528623372 528623387
    0x215040209041e0303150504090b0105010807140403110109050307060503060904080918061905060f030601020c100504051c200312070605100603060303170c1204060506040f02030907050918010903 86
    0x15111b8125044d5980e1002000221040a080140b01c01c2540340100043d40c02502c403d40e00c1030140c24001669000c09583c50000d030300540003115021603035641c80c01c195901400e600041c2c04190000c0c480c1c075080c0180507080740801000c01d441801700400003800c1141d03540645a200201402810480a4440400d21480c0c01102e4542c0208402c0c60034480c02086091450b040380c0003c0c00710307850408070401c80305c000d910080415056100700030500301d60380c40d5000144030940e43e65440d2500d40d401c0004220402c070741649520480c1c804803592201203a000f0703c0d0100110f81c60b0000f2600c0d503078850003090800060304254540a10f0200b001000e006881d002039200d4100c40182070041515000141d08517140c501001d0b0001d032840887d2034003654071f60403590300065803120795420a00d000c01d1000302180c00304c1d804c44030b0036210f0061101a06041c002c0c3c8400e100000c0f41541140341203080b030303955070080344075207446820141e021402c010810fa16441e40404e440c80284079074800c40c20702802ca007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 528625872 1250 528624622 528624641
    0x9020c0319031a0411180307052e0206070e060d1401080706020730051911041505090604021b10020712030203040309050f060d050106030b01020d0215040209041e0303 73
    0xe030000d050f60018035081c4a822882400c608140d03080100444a21441c0301c0c021030540d4061092620201e1389070783c2c1311044425030010b00000d03201100d0500d4412241c1c9941c1c7c511340295402201402509a08186001c2580d034003500d481d5100d07004a8400d10141040d081030000034000384001007180100810410103858007502215465542c1c1c07209840c1c2401c0c21164440d090710f850507125600f1194100b0b443c0c840b030182c0e0444d0f1841c050851950318404180a04071442c500c540c1d20800c41d4203050041421340760020301d10b07040305407800020614030320005200c188180da00150f0718451681000400e1042c07241c02c1c0840c2c416040c01690740000303611035001074643d95800c3c07940303a4485200c1d000f124410b84e8180e81c1c281c00b45150005205240503c02103280d8491800d106000c5050917902c0f0b000e00801c8165400b18009485000281c2020841404842190050165207403096400340c251034200d039064800c4051540d9a042c10301c41101c0d8101c02111482900b40e58030b00341035158001c0c6080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 528627122 1250 528625872 528625901
    0x10e1e0a0f08211920030d0c02030a020d0509040e151f120609030c06020307020a11060408061819030314010b030906070807023309150109020c031903 66
    0x30914205034061000c0c8184040700c403001c0040000c180c4c09800c4000c4401c8281540c00c08619011009160711041c00b40f11000c0c1e040359201091034160809240162a1a001107001441c5071000f5080300035200c40c2c03004841c0c014048006031b942c8150300c880e1300c500307020f003c06025614009002c190307425038070406841080c004a4415540554030090394410390850311900428040d5000b0780da124405402100340650034002a80c3c010804140da5000441c0710314600e9020342680141481c1066031521003c8010340549802e1000740004a80028025005401a1403800300e0b4607140503507078034000a2780c1e001c50700b03000036820f508201501900510100741e0b9880d240d04181c2e0f08c0c0c0044015a010480b0082c500d40d0040e8003060403180078a40068001c5500c0c415210700750010f0184031941c261b21100006c0308551404c2903044000d11429554000d49a20f002c0d240c5a007240c41c6541c505141800741e0700c00795138005aa8011f140c0d04004440c81184002c06d5503407024211400a0010500c84912051 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 528628372 1250 528627122 528627133
    0x1b03021005091609050a020717070201081b04030b1f060f09140607080d09080406020a050624060c01060906060503061c0206250818031506010e1e0a0f08 67
    0xc550070124902c01c403003c8496402011600e4011101c02418002d04040000366003042603001007100c607038181c800d031000001050b684190b07a1000400e51000180480d40320400b6010311441007281804580c01c4a410501344003580c1c64104a43c4030240310307400c02c1e81520981000000b4074030740080d8100e060051689600c00c0b080d5031086142d5541d41d039080916481101007007640d0016000c40050700515158140c0081c01c0d0042d42d480e9034440d40190800c5d0050f0307100d200140304005007004419408541a440500c083d0f815045c0d00d0500101844c00a00c1058003003114070300c0b00800d611920003440320110600403541d0300c41010b030581d801070b40c0c1c90380240c0d031350700141a8008840c800f40d2030303c03680900700c40d207010310403410781d549040552401070822590a00c03100101e5a840090442c071301c074001d106044c0201400406240040d01641c2d242c0c201c1c01642040241da0b040000209142c50589800c0c0c49203100c482a999205000100c072544039501c081c000c0380703030036648d0303000c0041d0740b0040100e50 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 528629622 1250 528628372 528628381
    0x8010e0f06070809031207180e06100c02060f030c0d0204030b040b131511041a030a0506030715030207140a0b010303110c0f130e0a290702100902011b03021005 70
    0x8408078004c83d010100d56108004207500c001c6d03405800d0390b1143c99480c24860340404148188928000c0380e010500d45006041031162034a4a80301d5081d42e02078900f40400f0440850703002c503416000d00007070302980040c0071000074a206003801c22545030104080d01190b86035103929000010010655090342c011101e00700240722180b4070509021010b80004070704518100036207401d0042d1003500e5154400003414400003c0001e454604401d40c0d2101a986548070301d00311940304100c590042c8a00c3c841d40c00854100f0502c05110340064451003240340241e51499582052100414412032401c8240f142c40012000e0144c0c800c00c3c1c40c142ca11a58500003c00c1d01c480416035104664015107600240080080d500e520702184c0c62000035036030b65000300d05004407500803810b140d0a58420342b1101c00400c04421244900a6281046540b40310380e071500b4180b4ac400295203d209c2c980000301d15030744004650035607018282100040c0000554030460b10342c2864020b4641d0002050500e5550a020103e03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 528630872 1250 528629622 528629627
    0x3090a060b040e0a0210091703030a1521170c030910020c012123100801020a0e0f030109060623100c1205041809021905060405120708010e0f0607 64
    0xe4034014000401031030344c3e500305d0f001c001e10300d41b100981005009003100006106064170180404010380c01d009143c40b803515440c0c00c0183e0b450310482d0130003800d4103801405106c0d50300743d00403207000f05a1140f6820f5401e40c0742c1a008805059089200340d0004500030340d500c2000001042c039004c0658800d009040ba00a0a0340d903454200310042c007152410030081080c10000040c6410511103d001007900881000381608412680240310b0a07008500108000303a401c0000e24002804500b0085151a4407250300500c403181606900f0700c10300c1c83c40e1800080d0b513402d400a00803260040b40400485daa00c48080f0031401c8001d0303030113003000d881071a0b4030384a2070803020780f004a070307242d0302c50320822085996030103041424a043e01092040070710010a8520029205040e00f0032118000262002c01d40100061400425040340d83c0082c1c5c80024002522a071065a040302c00944030f1f040341202c43e100450400a058114164940c60901c030010845070014085c00c6480b5000c041d1411900c134030350704 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 528632122 1250 528630872 528630881
    0x320010236040e06061507060608070e1008120f12090d030b0411091903060903050403022b06020d020f0726070b06311d160b07061103090a060b04 64
    0x30403046400210010305d5600741920403c420a441040141c900081c1e952100d0840711a074001031810341c003c0f40c05100d5003072940601c0313410283c0465030003c0c0314a00700c00c0654401d0400504100e4900c040342c981c51001d07101c400c3d10000d03920110803c040e0714040707010b142d491820f8005100020b04101d2000c0d550b00b80742c03081c0015940359405040c50540781d00700b44030501c0c40c0b900c0c070141c0c181200c580001c0440c0700f44c032540240620954425646070701d5401000015100c8209800c00303941c0501c01c011003420344651301040780d076209a0150701c41e140c522400380280a18080c1c0c000c10321001640600304062801d2a003800e219414070032503c0802c0c01e190340114000c10500818480601c0c0200751149404071007880c010b40c0400c000d10084805c0142c818516095020f0750720701c9500c600e02802c00c04403e00032546030090729001062031030541610700f80400c07500e00c14411485c10005055060240c0d9030410b0f800c0211801ca540d9881c10803c540a0307991000300c8040e120b03185043c000403203030300e054000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 528633372 1250 528632122 528632141
    0xb010f140702060307140c0d030f0b011b02030f0d021006090b010503010306050a06150807090819020d05120703020a0b07020606090105040c20030409060e0103032001023604 76
    0x80e080c14644075034248020b41e4000707403140d030500c40100155119002c400c40202510201c00d80908040c0c0c2545101600751010118200101401c105100d000c90b44e100c00049484508403081499151403400800c1c01d010b403035214540980208094481129000181844a80c50f411402c0083c2542c5030140c404a590750150a400a1000c1004002040b429000070b80c0040c42e001000846035a65084801042c003c6403003440400d9811003046603503604090420010807546001c1d10b0249000482c1c2034108c061040700070b03c103a01082c1d20f03005000007007040358407981c140000180e070382056080c040c3d540c8000792011104102c2c03500014a007140301149044c01032002804468091b420f01d81000301401d0400b07400805c01c0060079000c10000807003030320104815401c001450b80c40342031480c490240c0e1202d403c542801d1010703000400000b0760024500004060b003041c8070310303841c0700c24404c07502a1103421594413119008810ba004900005034668902d45000c26000000d5010035090100b40d511401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 528634622 1250 528633372 528633407
    0x20a0e0108160203040b130e01030308041a0405190f120810090b090a020705150f01090c0c0f08030907080a060c081312030c02150a020711011d0d0809030a05010b010f 73
    0xb204100e007030300086c0681079070782e42c900c4001310680d1a1000035a002009900a42c009107054090006102c2c1c5592500c84440e40c94149802c146010784403141d4840c1107002c1000c0b118010381c2010244010791200c003071b4265212540318001c1c400c82c0001044041c0517103107010406800100000e0b420800d1041640784007001d031030b16103903542d20402d000007034101d038800b61820f016621408039102201442070340725003d2406071180f15410701c0b00c030314100c2d108068100b05000e88050020003043c904148800c045038400300032556551a0b8a4290500d4800e40c00a0138030f115080c50351041010940000c0826162075070342459a46d248048020030181c81c20b00034013400da1003070301c5101e294440e8115003001d1415004542810b00680c00041c60400202ea000005560100720314042080c1102107410410091038401c2c0e40d0855080340c003d10440404409119006206044042011032004e503072203802d008081d600468024102035000e0002c419480380000c000302400c4851368002c1c9501e0301c0d40d01004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 528635872 1250 528634622 528634627
    0xf090e0d0c1506210c0504140c090a03020a030302060415050105011205280b04050a0b090a18080309030a080f0c0a0806060409060803041e23040b04020a0e0108160203 73
    0x3919988040001075807a008443d032100b601040041c200c41c410b042c003003a0711404401c1d0303452138100310b082d03600c1a4200b140300d58246000400c0c4100441041d542140865407070550791f24501340040d89a209a510084d00a45010000802d142c0c0101c0d810344118050841000241c000c1d804603070407a1000d0003082c1c007007000c0a200041d41c0c0015800150b0000b03a40440100b0342050030059000404603420705006151a19940c89090130203020b06c680000340d011051140e5000300c0005071041c68003c00ea81c000603610320009510000401000c03240c5e9411818566403403c14556a0340c40703900203c001b001065081b4042001c01d0011102d01d032241d00b441c4035490a20080100850744440c000d81240da002e142400081510381080c8031f61350041504600450744d951138222414803031100c071598401d440d05c0b1007074100a005900d2108007541180d5402e1140400034040014008024941110780c0107403011071710031041d41c1c0200c84100500c00c262103541c45551500b0301010b000c5844400d010058005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 528637122 1250 528635872 528635897
    0xf030711060f1c0902090910060801020f07200a03030e0315010e0a020c0f1c080112020a060c0302012a0e040e0703030804050f0307030207141806150c03040f090e0d 72
    0x40c052021104050400d01048185968000131241c071b5084e101410311f41c002c0403e86442818030711881009104990003075003840c0c20741e58a401c142c02640300141035807524140084010b00b0184400c070b509203004040510443d00c2c0e081c010084000c00300b1040c040c3c8926504410500f50005c00c2c507049800c00c900d40d10347c50752441001b0b00a50881201d0541511445001c041510000d22400e40402c0342e0710505c071106c040b016001808403c040c2c1c456036520350001d41d148096100c01245000b501c00d036080001c8009050700d0203d00510291402130359610000804100507111075080e0440005d20307a580e6030000c1051010802110043e141081d010780c0503000c10000070f07004811081e0301600610964901d9036102015504551010b0001c40c0160428001444809004414000f201c071095402542505020181a410909c0035109500c14071040c494842401c0040b000c84501462000a4a0300e956861071909042d44e40c1d4044e801105080820105928038005198900295a50360b4403054504 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 528638372 1250 528637122 528637147
    0x150f0f13120b24121507080103030e061b19110301110409050709030b0a020403170301050108190f060f05030106121e0201030207380c04060e040207050f030711060f 72
    0x70403c40c1d40c4151080204004080d59000722002c8100550005004804c00d60300b08058803480c01414039007446815001440400d5020840203091002a603000703548215299810800a60b401d1140c5158899a090301640c243c00d1540350071031501c00d01008000c9503d1104050036541e4880d044110800144410804038200741c105607000309050030200d00c501e850780c070f43d501c2d098000c851581c5502d8000500704200400c600c2804403985540710305604650604000a0460038080c0500c2450b00c4060000346880d420760f03020541c0f0300344407002040030542c0c0d480b00360081c054500c1164442c0d40703402c3c000180340d128440d052020650200707141e00054506024039070183d850703030f200b64101903080c440080003c22240d81101809001a0255100c0c20011584004901e14101402c0390f81410000d1165020308401503400b902d00710f00b080080703003007401c0115009001c0c0207406011407050000d4041c8406001c00180902d6000c0c000401a0704185c0c1c0522a207841200200111030314100482140c0c4c02 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 528639622 1250 528638372 528638401
    0x61214071220060a080f090a08070b0709180c1103041d090c04090b0411010e130e0a0221120c07050603061f110c09040c05150f0f13120b 60
    0x404140b244031542004020490782e402c10b04410001c81c8000313080c400b418602c1140706038440084e40042c154004c0300e07603503070026001d0b00c00000c0100701d1b62001b0640060081c0c80d00307800b07441c071906058000d001e01628880540308401c0280c000c54483c8014a40b400743c08003c40f070a8070100c0c040480e21090100d844100040300508110240c000c08004548650703d82c061001d40c180134041036515810242401c588400d0308400507814444150285c01c91611100100428050204000102d107aa6002064100032803090000d61025441462070920710000310480c9182c0080c40071550100f4040201c0e00d01c501c02d00700340c017586070700000007006a89000402142e000704083c0048003500c000350307050358150302102c0c020343c080307840000644442c080c1000392a26512003160540c040e428103845003850a503c038010f00d13000b554884100b50428000b14200d0b074005550145281d6540d54220120b04203410031440c4951285400c40b000840b5144960200203064101105c0c0640352034a4074882900c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 528640872 1250 528639622 528639653
    0xc0a0501050c0f0304061d040212180c1903030f02150406050c07210305100b040b07110d06060f0504050903090919020414130509100504020103020405040612140712 72
    0x51080c48442503030f10000380080c01c01008030351a40c0f00d0340f0301d2090b0101d00d5594030802c2c10380100d2061111390301601195403d80d810a003084c52a02903c40300c81202030a00d82e00c0c0000700d4000c0c2c40680325110103070280e1b0311007007100d010360364424036081140012030f242c104003259140c1d0104603901140100d02d030b82d0310441c6c000c40101001d40c0340132034603907640074142c026403c107c4c0c07120300d05401e4080f1643c140c02815804203441c44014881d42c2800d41c8800640100d008980c811300340420010104039000c1c5403107030f965a006025589040c1580741c04d0026201030302a500c01e492401d0000109401c0c1070055501403200b4801a600344500d080070300001c030900400c510354130140c1911030b00d440c040e684010400b802c1c0080b103134030b020400e040c00e05c50000e01d00c0040c00c4000e0301e44810003003d294040b0355462001e10002c40841d2545403800102c010380110b0300010b07885850403a000500c00343c44072034100707a00c0c403502c59549222208420340da110103092080c0c003408521004c03048000b8804020181c0784 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 528642122 1250 528640872 528640897
    0x5030607020a2d120512010905060d0b06031006031b080c060306121509010e010513020a050904080721030f06080d0c0302030c060c07031b02031f020d0e030d0e0c0a050105 75
    0x643c201da161010804603d40500c40030420004401074005002c043d81409404006800d000f1420401d020030740011224401424024020020034040c0e074003403054041200d4100d1061002030b44034144003855504030380401c81e000d240c4000000340b8400115000c0340e03400c1d004081d141140e8400b0240080311a58071540e08990055042402110300861071940c05080444000100070440c00e00395070841b80040e01c2e1403a4020188401001641c58a07808415140c06445080741078030389140c52041405000c000030540800308200038a051420700c240e0001c108e03130360350901050b092002c4580071620030380549403c5c0d800c1501c001d0845070040c0307070740c0c00001e00c644116860048141006800d21206480321580321400142c107800b815031051036130f108283d03400182c001200684c0c3c002907448070313841c898144400c1c1007030007010304c1c0c0c03010f5055850b0f1752480b00d001e11640c0042000300307442e41d0044c402c1c601c00c10300c1c14285c1c095081000950302a00d0360040d0440b00e41c3d500b17000064500d900000b290140307 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 528643372 1250 528642122 528642203
    0x60e0a050915191e05030709020901050705100903030b0607021e130603051c08011d15120105060405101a0f070f0308060a090c080a1d0307080405030607020a 69
    0x302d940301c918100140400c000d01c140c500e2420100381c1032a03e8401c940c00340038806866014040c80e9004038154040b10310b62200145e80303941420060f20580550a00500a0300441c1c0c4040c8a041c408e4000260061017a6010012070030034604000e0746009881d030107900f10250042c4001c40714013818060418440c0280b040e10800d1882001c00103030360140d0421102c60300145410f9003480080101c0f060b10080c1401d083c622581850301074a8bc21075180282002e11800c100401d81c40d012901001511a1000d400c03408000c0c2c5403001079010b07000a0302d5042c0030310f1402c40000c286903044990807003035803d0b101a001d0300c00d0381384850012139003120a100307100d0f4000f046914000f80c401c011314900e0030320907291211203141002c2000702c0b000c0540e012403005810315849842507030703004400d51b80c0107031051800038964440d4592881624140d407031200c103138840081c10308244802003000c1c0040b01d40490444005030340d4040200d0f01c4000b10480101030601110007035800f0302c0e004901040c1003403803414940 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 528644622 1250 528643372 528643411
    0x3050912031e0d050109020f03070c0f060f0c110309030307030c3305091b010507140d05042907150b09011503050a0905030a0c030e0a0303090f060e0a0509 68
    0x9003840c1140480300c140303620008000341da4010b80d00071180184011b8a045007030403c904484012488002d10070801c03c400e015010080290a8002038101d0f50801d500700310010041c60184024489a0013030701c041007219a82481c024000002c903042a5406030265003031903c00c0c0d0702968840e0360b502048542c07000c19110f10300c043c40e0f08400300b043c0000780300083d14030b900d8a411003422140c028004290981045462903007498044202041030038003860a29a038400301c2c10010395a0407400351088003401018440d101c401e5004000c3d0013640c0e8010020881d40c030703141d21480030080c042d640b0780c8a14941844110041100c41c02e48122004061201003540c94a4200058005009810505400d0101e1903104490303035251007400d5208200140801900d42d1075107d203684d9002d100d60510400414160f04010503100d41c9111f0002c21001c0d000c00212a2a4500600018441d014450300b0a01800c0c000070002e22412950749800009001c2180547c00c1c68140700800400030b004480611042c00c00d00c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 528645872 1250 528644622 528644647
    0xa17160807061415030d0c02040b03060a0501050f0108100909020d0803040803101e0302120c030601080c09070513120c23130c0e0618090c030906060d0305091203 71
    0x81c80c6042c414400001c0040c0c004400340c2c80b410019000d44040b0b800c0712400e031242e4074000b91955481e0782a06001440c20603d2002034054500c41c00d4441c6c050188000303104040d00b007900014140d4100312202c2d100d400b0f1aa00440e46002d040394a16500e03040b800040000081c0380d441300c0c10440c009040502c40d1209512a00450380c801d503800c442c0305500000300100060f1000c1c042024102c11155031820082c0010404074201550001a00c91080030120011025040203a0400110080e041c1e42841d030703491a68030f4a034508085070501a02000d00000c048074420021610041402c52820808074107042d8159003080040745c04540500304103201003000c0e240011100020880380d140035128420140a00101340385a100c1002c0141c2801190f0810681005000000e0035007038801c0b03901d400249182002c07210303013007244642041000c0d003400f040f02440c070000e40c4135403030000c12900c00da2241004c1c00300010103a40c001d0002441846000701600c1c12900104480c00f002c42202e04045659010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 528647122 1250 528645872 528645877
    0x307050312030a0b0d390b0d0b011b08210a090507090b0a090e01020d02040806040318060c02040203071e05040603110a0e090907030f06020c0f0a171608 67
    0x600707150004810003015031024080e62401100560314000ca507400d43e5200c0070b155100350001c0607280e981d584001c941004184445121004000030481955a15004031025920290701759030101c1c14086062020350051070300828030088004400071802c03aa40700c0602e0b9400c445c1c0e01710402c07441e003545020040c1c1040d41d542d01030000c1c80c900184880305ca250951400c0c030550b200f09203003810100c095155075288001c01d0215007240c40d021441c07940f0066024024892140030280b460b02c003041c0410001400a10a40300784c1c406e442e11030b152110461245c00c0351140d40b0a10340002c1c035920021005040c03d401850f00000d041c1050701e02c180c5900100d4800c4214104000006000030400304440395150081800e41002d040e41c00389000054200100b000c030075811901c0c081c1c0f1902011410100080240200560b044242d54044e80135601e04840a98002d103143c00b85480b5a14810440400c0410b13240d0800d50b1040d214840114400300302d00164021000c01440396588003218004600031800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 528648372 1250 528647122 528647143
    0x90105011209050d0f120c080604020c0309060d0b150c031e0d0e03030a150b090d05070e0703090b06120d1b0209130b0108070605070809060403021e040f11031503070503 74
    0x85001442407003c5e002403c2c0800000040d100d01e0808409400d03643e00100c0094110710140c80150342c03010968000c41c5184580160301760003410001e8844e01c5035109030301c050440c20045520140d2850400805400c0d40a211000c0100342c000300301d0f102c41602e07084005000340446d03445041c201058030548508803015142d049041d9007002041000d0b500c00b071b200d14644240f66042d41440c0b0341c200747c650710392030207540b5880c1c5c003410720505007005003c01081000b000f40303d004d0b04200285803140c0001d01803c802c0070100c030035140c4000850080e107400003940410303045260080586503a003402c21910700ca0344080103020044901c0d0f04402503103400341d0062182403000e203040195080e031b160039040c00c001680005010740200d041444015441b40882d00301580003940300d074980c5164000070703c032880390b980005d60104104000c1d11500c3c0049941d040d044038104c074100105900050504240d4414116003281d003041080024000c4a0100304d4130301c1d00d507002e0304a516454440c4080ba151100410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 528649622 1250 528648372 528648377
    0x4030206010e07021b0f04060b03130c120327080a060504050d0903050303070f031d16080105060a0b0d0906021b0706090303120b0d02130f060b09090105011209050d 72
    0xd005000d50040380c42da59400c903a161006001044c89400301c20100d203070900511744100586000e20905a0300d5030004000750000e1042c2c55034a040c0000d02201020040408640c0c1035128600003c000c007426506002003900f40d11a0000c403604d0f50001c608524200d0f6440380164607048003c103440d1030400509060324810b00d000101c500303003400c1c0f00b0324044030030700c14008019003858140009003001c81a0784d00f249013424a46d00c80355a161040c0e003e01074444082c0040741010381174182c10040014891801c0401c41142d080c05519403035014241e80e030440304e464100400034420081142c40000030b1119204510000440c00c0060761801d0590380417206d22080071011350342058621380c0a1086070000c107007a0400512152031a07501030300410614400b103006507625801d04500703031184510341582c140e00410030300740c0254448810009048000c0c060002d9890000c0114100d446d80c02281c019100c01403241001d40e19040c011640210075000e9034ae07025403502d6208001032403c01c205841d0b641940c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 528650872 1250 528649622 528649633
    0x15030f0304232b031215090c1815050f0f07020a06080105010c02130e0f0f0c0406030240060504050903030f1b1c020c160303140706060e040302 63
    0x780469200000b1060141c450207051032803c0119206140a0f4074014058102101000840c10305540020610710030209650404511103401c855062091041d500310400c01c0006c550b6210040b940d00000025001d5080a842ca05200103c007881503c9210308542c500a4544240482c500c0d11682021071000c81688001c19400d0861500a079245c003d40440d1800048c60762608000901c081c1203100b011380195611410020141d4141d000800710450700000c80c0c5998490082955652558024560480c000d900f5400c1c1d0a1815001d9081145d80091201207039101d8203c10b02030303110380300404a01015210409440f0900c12001364103444014040002d03559103000103000948000500c0220b03243c008004000b0002d1044c0e03a6a60040c0d101c1000c5c407c032280078140102584540b03041c292000c1c1807108030b80c01c28000343d00209411311450080e07d1249410b4040203a5046150000401140c103000b9900303c07040c402c902804a090060034081003e40d5601d000d2550000240c4080d001600310f0b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 528652122 1250 528650872 528650909
    0x13b12040f170c041e0515010f0215040611130902070b07080c1608040b1b0706050c1f1107151a0a170c030106120308010b0a0815030f0304 61
    0x1003a49800140a500c0081c2c001244001d039150b126a10303080e4451140f642c80d41d14002c03514640c1a401c1181c41082420040c3e41032030040d000700c80c0343d019540c0d40020a1641015032051000c034890500204001404001d03498581d41d0b000503040400c10b010410100f40311043c8071192541510f030040503600c2006030b9401c80c5003455a0300480040c050790504c0112418000000c0321141206c822135040c810060840c0d07240c1c5040f01d6148580e600c020b107140004503911070896904c1c400d4030560310503902180c00180c0d42e0038080e101070080d0401e02045421401c1840300d404a80941030016106d805000105001c0003c0c11708425000204151000c42400c42c50188001c141d11840a43c84c2e00854600780c01050b500014a0300d41c1c540c000d14181c0c0300c3c600035003411010100070180a00350010024032810b42c4074400d142c0140000d0b0410360000e414080005110014942114240342507079032028100e96504500c0c20941000c030030b00c260184108003802d00801c106002800180031100c5a42c07400594 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 528653372 1250 528652122 528652139
    0x70801061101020901141804060f051c020108071115160e1f110304030b0c03101401080f0c4f0303210c05070b09013b1204 54
    0x480d81c2100540e8810080307640d49030b82114440c0681480c00071243da8440a010812841c00310043c412178000e07080c070034082142d2104a0a1400347c41d03094400c1d4650211406507000c0a100c5064003a000c42c0003400814051440b5160000c9400a214210380e207042c1b2043e0580590402290440030022070142c2d0a20308660010044000810407145480c0d206400180300d1520701a00b440c080504c01f26021640040e001070099500031038000025031703100e142010584240d5030040320b40d6009440329a2000c00c4c000f45100d120386003501e040e55207032280d544101780c0c0c550040d0080d200c0c9011490500509500445c0c1061250b5402440009542d60380c903940c08440b200b5021020f0840a0a84200a46d8810800e2031551046a405180407901c00c120600f9605025405100176154903080000c4014007076003000082c03055500c5202400c800f81c1e10920704608035840c0ca141c8101c03450004900c3c1c48000f248085c4103e8600a50801107124840c1c0d9061a2920000c810f007070b120100007040c01c221071603 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 528654622 1250 528653372 528653387
    0x50f0a03020d0e10140c01140115080106171302010e100905040b0109180b012703050d082710020406020a050f0109150c050f21180706030207020d0b07080106 69
    0x440035100683c0e00c107030040021740310700e103014a1070a1494011070000c0440b2803d401161240c1c240300c10707000c00b030b503110714903540410380101030309002c94542c1f0000500e07244500c1c0400c18005000e40340d041c0c50b84404545440742141540705030704101c0d4003403105c02903558904500302d8080305034450000544c42d103800d010030759040c0b400d2581800001042080303160030340500d00130381450755440056030b42810001a5410469001c1d1401e80014001c0542c002c0d421a1802c50141d1f4001e0080380c444403829141252010b10455040c904811700e0101d0514070501402000c140c0e807050400d03180c0440501b0349001c203d8115501440069000256180a025080c014100070580e118001e2001410588989041c1c1500746d0015041aa4406003004030318490070960b105a191161041d40c3c44c45465844450a00c0d0040840c111040005c003181e804480100d40c00d0350b52104070045c018152070321105400035081440140c0e04014a401d40c4000100c0088510b8403996807621681d16550400d50010700c1c44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 528655872 1250 528654622 528654647
    0xa1706030c0d082808010801140c1204050109170d140402100809030708072001022e06030b1617060d1e1202010b040b0402090d030309050f0a03020d 65
    0x9070010440d211042d01c52040c82c000c0140c1143c2c00076034480e1800c00740e0340c80040c20a0040d620b01d40b1100c03540c0c1c0c00b55100001c0e50494400c90000e0000702506c1c54110305115007038418503404c89040240b0f6183d4081c041314194010301650000548428a8845040004040c0d00600000500080d55054500d15200752030f01d003440344ca5103414516056000c514101600c001c0301084c0400e00c00080c14112041040702c00303450703000000ca512112285403007e01506000100000e04641c0160a001e6501c00a0030741d64104051400003004a0400e0946c1a21800c0710810000291500408004100b011862074001c01c400314407420488184e6034020141700d43c0c845107103500c50074407080c0040c40da11403030200c00c805d0304105c1c815035812640d0718844450010160040c1040c0400780360003507140d019446062041f205560a010340c2c4560010030080707104110700c0076406846904c440001c01e00c241d2020360000d21520490f1410030380001c2d0186081d0b5039103000c60059020700c51140f0000d0340006e41e450007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 528657122 1250 528655872 528655879
    0x106080304030b220611030604051302011d04060302182e0506160b0709030201020c0a081e0c060304260909041b050a0b1201060215010b0a030b04020a1706 68
    0x102400e568a0100c3d142010300128010004001488520f10285034102c482c0c1d0703445041040201c0511501e0b41d0682c00450b4954480c0d4034002c00210282174404180038419070580d1501c200c21120502c803905540080743c490b1f0019614200400103031940307501e003c8600001110102e0700d03d466003c64800c60000d040c4103001d441007054170320a005010075401c060b620202c405a0b1254034114107c0c001071340d0704801400d00d5100b0418003180c66000b120150a99000381e0a80f211004200c1c01c0c0500d004252040c18059880500c160203034080701c1c03007500c029418003002c1ea0303202e01c00b40303002990ba90130a440a4603504400c0c0c200300d2184040c1900400040c0c0d45c130480f07504140b0b41c08005001d007400288003521407002001e023204004001106c14010300401400c0d079080c191100b80011888d040151101c003062401000032400794000502d03032801820026440d0030981c04c00c04542c6154019419541c02e00d51500818080c995850014101500c0c040d40c0e8401c1c2d0104500c0494907980e00640582d01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 528658372 1250 528657122 528657127
    0xf16050d080a0e04060b0c0d0807020a0b060f190603061d07081b0a03020a1215060f051c02070201021506090705071406070503090f0c0a05040e01181401060803 70
    0x961121080114815080180ca944445002406444280004801503801407900714042070010f2908094000403040404490f201c0d00c14007800d4a401400f941d000002d40e000200e4100000d1814941a0f44480c025107110450311000012079150210f28180b082030090000c028402558903215110040418943c813024044581c400c80f452110040c1c1018200500314001401070719100c44c004403180d02c0c14400982d6503190420003030094000d002c4400001b4207000d03030082c00848500680d00352021505048650501d05a41541c1094500c4207600910005000c844800340114003020003a00714224050307035602c8144002410701050324850301c090340e03000c024020f03282c0b14003031920391005144c2441950340280c3e0401003041ea51010f80b611b00c6100d90400c11a500781d2110140d40201041004c4820401c6180d04294545402d8109640c1054030325100700101d2402da000010205946400007400001c090b0002c8420f2003402425108038010400e01c1400180910540f070041800b98051030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 528659622 1250 528658372 528658379
    0xe1206071e0201090c0b130639080d091101050c0c010f0210060b0d0b1c02060a0309020925030e06010b181801090501060503010302010203090d0c080a050f16 69
    0x2080e0078281000d481c030054401c000600a54001d60003003d20030f0304400c114041c10f64924060349164005640c24555a100b80030010303846024004042c1081c0105044138072051018001000021151000a254101d4220440c1c04141210000c000e80b104142c0040780050003030034248002003212003003504001d010003040e403942d040402c00b0341242c002440d00aa1144003e4000c074540505003c03490102850804c001405a1140c00200244a51004140001d60880c01048025100d2402e0104168810b04c1c89100502e498002001e8003040d90800081e139042d0b64001ca26120021200103400c8840300c040302c08500ca400558805c403084500c0c06000f802c48800c8025164541841818250b00c4081340442600403550280ca001920240100c4210800da9912071040381d401e10403105894035207000070405a04c50001c8905898041e00214a031035409020301a00c0c030302e100010750b041240c8900110b241d00003480f8005070240075030010821162650b0084d400d0405800003000c14041042007003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 528660872 1250 528659622 528659627
    0x90b01032f0f04090203072310020f03030a050c040323010510080c090417160c09060509012606010b22120807060608070603020c010f0b011e0e040504030e120607 71
    0x1031a1500b07041c1d80104084949102280c80c00d0040d810145000034450b08020300341c00c6003150007050190407500c41c0e000103007141e0243d0701d91041650a41307441e0010000a50721080c0394001c25000b101518400303290079a2a100d06c40310540311b104118160069408901820609003d082e400400f030450340c054080c60604065070301c480120400340105064070004040c4051071484410000420349140c1d550410500080e4008001c05000c86147d10500c8001c2854105845840c2c1941c0d03004e440035489908004a1400b0001d000035282d21100744004500c03800a01130010354020f06086444984a000051102c02c40c8441d4105400c0d0700103925a080001c03141005d1102a0030b0382000c00199100fa460401102402590304248040c0c81190b000040b03076036146e4000c1c8031050855000f000403025200c1204103076011a4505c3d800900f50640300039400c2601c0b003170361040d50380505040b145d002c2810302040684200b29002d801094031465140c0050070a04088014454010041d001070b10700b40401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 528662122 1250 528660872 528660889
    0x20a051c0324090b1c061d01060b0a08090c041a12120301260a03121a0904020411210f0903070512030a060e18010b0d17070501090b01032f 61
    0x1c0b1120180c40f0101402d00f40c5851713000304102190120300c904400140c0c01c080c3c0c00b9000c204088100039465454585c000c41c4103200b04e60507910342d601e441c0d01d13000d07405a046035480ca0140680519001741e9400c0c5a4559451140c010200305526411070811814000c00400c50340c6485002c0964104008404500748001e00701da0655200107403495a04001c082d030040d2056840c14a041940700e2410f0035414107401c00c8800c04000e616000134410828103040049400c051404119000150780300841c00500e002c0d000380e0030310303400300034603a0070303c5041100b00c032410800a20540c80400314030180540003044003805a03000c0e6404005601d40324480d51000c3d944c0084541190050401001040355901ea54212800411003010080d010341406070b042100c100c54041035a00b2586020346504860074165280b007241078200c6001d0b403444111a4080d20554002d81c8111069565040d2030b400295002e103145000e1406103488810b244c404404560400345020301100782070b201680501c51541d80c0805 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 528663372 1250 528662122 528662129
    0x30109140601050a270603050f07240e01300e07050306062409040c08060a0e010b09120c09070203070b06041e0b010309050105190b0925020a051c0324 66
    0xc0c0040a0501c1c41c0002040547c200800d203000301031034910400d90000e500d000b42c4400601425070000302440d641c5522141000c18404100400e0018517650f0003240400350b47c0c512500c0c2d140d410385c00c6650121114420000d1980701d2940e84603020404542001081d000c5c10068000300030a08222000485d0801c540000c014014000400b04905011a2098441c070020281050104104001003d05508000c4034031a02030611381078000b417211010b5500d107040368100b1903050f260807502c805102c4100d82007910313441c00380300e00340c911502511030047d070500c03415880d405035445400a24040c80503100c05011284550704107075464075884030300c1400907090101c101000600c0f81c0a48016806000710b034001810a507e0101080600d00603207040b600800d080b4002004040c01c44030800259280565004800300d184e20b10904001001600440c41d001e424011980034100a81d50f082c07505d0080e114024005840394200300d0440d0b01400384910001418010002c0c0704145201004074411510 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 528664622 1250 528663372 528663419
    0xa09140a0614180415031a0105100f02191110031b26010b09041d03090d020a0f090219020c0d03050d0212040b090f060717060609030109140601050a 65
    0x6400c5514407062005142c401202800c20b11031050441d00300c40954021b80f1040d500f0100000d583c4200710600000c06060322801002ca450078003c484040b00c0003544003207801c040d445520325032401c080303401303103074558261240141c81c1180540200780651020110701a41c14582003502d03003848514449000c034000e03825440c00e890030b921800a5031038030401c0a018548403880c414000720303520800b4001081e58450554040c4120580c01c001c107002501000e0004255810501c05425107147c41c00351078207031a000030501020242c48509541e16940c40c0d500054003254001020705c40740140c0002c2d2804e0400900240c9488288140411000038000200404100001451034248202c55050307490752580c07132030f15000500d454549512255010790701828a4440c0c0c50700b14141d00c40c001109031048240396918040310402241002e103010016001e01e078454011712445429440034410b01d000755001d480c004c45000580d0718550f08204060304468050218000107216a1142503658044031501c00c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 528665872 1250 528664622 528664627
    0x4050a0f020d150c02010e0c0319061b020a26030403030f02131d01080327011b06050403080115020706051303050a03080f0a02031608070210020a09140a0614 69
    0x144002880102e25581c01404407041c6800c03001032121642c800156054075070001c126110744d1a603800d0b07031080269517031541540074101d40d401c0003007100162009c640c407840c3d01041c2c40390846881c1440c1100100d840b001130340714044100500c4110811207050081c0c00c03041d00120402d80e2002050340c88010405004e260720b0790295000e0304180e5040b11846800a24848080c175211288940400104001e01d052801d01c0f4001080780d4502208486074404042c94006a00c0341c1c0c20080e0010180c0318110701e0610078140049810880b02c00080109a44201800102450300d464044c21079401a00020740300786c1c3c1034908007241600018640181d451340e01b006900c407902c280314000f0300d40ba02c1e0002440c500407000c070b513420140c01000d024003821500c9001c400655480007100e08074001220080e08000e894495914028000c65240e83c000d800f510503144224500c1441c40242c2c1d1141003d80c00103280d0801c10000c008910110744028402180d825805525010009001f045014400c03942603200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 528667122 1250 528665872 528665903
    0x30406020a090503190b151011030f03042307140d020d12020312010b0f07060908070b010b0405010e0d080d05070903050f03030a0e010e06070503060a1d0103060c0804050a 75
    0x40450b540241801002c48040c8a1980500c00e001302d2501c0c001c41d40d0041079408140b4215040360700036600c1c84003a02602c1a0030b500c030707421a0001c51515000980380030070480070040300d020200940c03143e400f0361007482c01e42d10540d09030040d10b001d15009100a8001e0b450a11a400401070045038107603040380c080c5030344a901e00001d020b14410040c0280000214000000d0164000c400b400300b01228162605103a1781e1041c50034414410040804141501045440000350302d690003003402902610849091101c6565020030b02202a00090010340c00840c0411040d130b403009820b009524141c64282c3e905910b075a510060740a080d24001085860b440050744c00d5215110f04401540c01c41e0440300128440816542c5030b42c401d40340c452001c5c0c01c000d5a802c03c480d05000d42c0c0004a03d610041c4040c1e40d42040071603454002804a0754803403007080d0001355401c4a880500036080741628007249652540c0b03000c0c01100c02059840081c860a281000041100428101003c0d0341005628956220 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 528668372 1250 528667122 528667127
    0x50a02040509010f140601090f030c05060d0b0603150a0801060e01140609061803010605222c010b1003050f010605160b07080f012301050c0a06050708041115030406020a 74
    0x84c10001c500c0c0c1480d090b980c0d00d10b00030b04055240a80c81c05e880e50060300da12100c040030006010301018007101c1e03091741c0401440c2800c6006100340550b00000042c02003801c00090429170040d100d142a60244455898161500300103003001800c145008011080c074117550204443c07414411400741514208801e11592618408c40d4043c940040001323940c0d80b4011216820340100e0350940f402980b07000408a900e00b4044844200002d11507034011280b01c400541c103001e0815110400340350401c10701c0000384400300c00d00e85030400182c0400800c07866200707400d20640c2c84168030364008141c201824010003941440140d410740f00c02d440c0c0503a031041c1a10004040c100b40c14002880b0000c1ca03010080115449100e5500800701144840703110390340c13601030302020413032145403980300c0c0042e100380307509580100c005129000d04907041d20704950140d2225411200704494071004030b88001c00b003202300400d0f400711014a0404031610a12840d403101c0151a40c04024001440103900165152244e070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 528669622 1250 528668372 528668381
    0x70c0204020c150f0a0b01030218042408030403140304050609090703180c060f020c061b100c0e0a08030a0903110d0c0602011e02031509040f05010203070e011407050a0204050901 78
    0x1180024072040c2801d015800c2c0c03801341004c4641500342d615181e003000c0710798841c1c0221641d1000c083d10900b0200c000500308001080309030701c41c0d09a0160702c01c0940c1d0829030110b04200810818018684551840c1484502d04c00100d0740c0c1c044540007040b09001039641c0d507007070710300e07104054030822010760360301d141540140003005540400545404040301005504188402981d801c0ea50b41030b2030034082d1000b40c0e030b00d0f4450403c040e03214100340b000000507405500b000b1124413541c004c503010341800780464000c0342c0b400c2c050040001c0d102c01d095105418051401170050004074011407400d6800c2c2001800c81d8441e0200500d00c1c2e00c3d00601d5a1140d50784803070b8101079034000e0684000c00c3e03903940e4082e00030814452014000203407003402c140008400d00c00e032072144036a0901ca10034400440d0402084041c024030480d51202c018038a030000c10f40c2440a18402c401e140c8171b480e0030b00f800e84009808400703542010854131408011800c0040c5000c0b400050311a41650041a1502d90000b92400340 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 528670872 1250 528669622 528669643
    0x9081203091510141e04020a140d150e0403210929070306030f1e0f202209140a0305030103140606010801060804030203040509010803090108010e070c0204020c 70
    0x102114003448400705002c00e016085035266152455401d044e10709200007025042452441a00d240c81c1030046400c10f9002000c01d100245081c0d0b1400114601000f0207400c0310022413030755a55501404036500f0403032403c5024040b0101100c8162500d03560013000f4020300a1b00104124509801c951011025040348807240d500c52054005003d00151400c11203041016011a0346c20a40c0800c403128049d00c2454180d0b03030408241101000c560b01d030b2340000c40c030120188d40d101c104111641d002c125110000011580b0641076801d89955900d01ca64501c14000c01ea548280c0c0741250b034003175144d50880d01c1c80b80c0b00328540700440c00c041ca03802c0c41c00250b804d0111030f081c01c1c0140065442015400310056041c1c0c0d100b070b4a060b03004aa090b00326650359108460781e90106010600502c2018010440164018400c4c411a854641c4400c0403801c4024207a1007a49958408200c8214030741e000b403407050142081d40000110380c0b81c11580100717141d4079400080d015660005107010050028400354400c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 528672122 1250 528670872 528670903
    0xc0715150905040501050f0c0a05181801060206090c0f01030c21060f1208092b03110606030a3906020601081e03070201050c1905010218010908120309 66
    0x441d07540610101a01e4101d900301c4140d46800d0002e001041341421442c001c5040311b4956040020b080c4090303400c1c0e4000391728a43d2090448101c0344280c1e80c0e213030b442400120b0902e41001a9450082c0c041e1429002829107a03117a002a06aa0b170107031141c010700d0010b83e5092034081280410160192140e5000c400f100150714101504031070010f00503001a011240d5031442e9901c0b01e5658518204c41c154100002812418100b0000a0625021050391f165107800002070120340308802000031070000030328045003c00c407200c80e0391140c0102440b0065005230154041c1000c0e2450707580303c914400802e8008040701e4510002441d41803c1819651b5407044030003116200c1035203400c0c000e0742d02c020074400c0201a110f40c01014000c0c0043c0c1019001000540009500700743c5954010346640c0c100700b407581d505120318215000b00983c0e1410700320f0b4085c001c000047e0360345c035402c40306208444c0c8846a6810300007600c00400c801000012400d8a108540d0215a11307502c0351180329040002c92070a46c0f04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 528673372 1250 528672122 528672161
    0xb013005090c030f03070807030302130902040e0402040501060309050715030212010e0414030f09040b011116030209130b0606090a1a0c1606021b031f090204050603060c0715 76
    0x6940708001000c02d00944110110748042040c1d41d2020f6a0f44103280f4000c0540505000302ca00290098003d804040c0c800d640c020f00b20703030300c3d1110700f0220381056104081d00c01c1e014040c4010b6081c00d00c00d041c0508041c3c98180045042510b9443c0d07101a24400d01c0d60b00150380040c80030051181d03050715101e0881c10303c2e061155075125040c8100400c181c4041e03d01405c82d03045400c40a1000027281c00e40c030564025030303003460104400c00000742160304106050020520304050a220b050104010008944584802c2d240c02c1d40184020300c1002410340d5200c20381c00d856840404c0c050302005520110440344180e0792951007021507500c0c2503540c000920090116030410351721900b4000307404081d03000c208940d441441d41040300f007500c10758841c82c0d0141c0c006207028105080e121b070700300b00d0350708000d411541c2a000742c0d40460480c2e4048d4042d1103c2e1b90350b41741340c1406c40c6400d000d0660880c60403001000340d0306114015000324410560300408400e10400090301d0101550058181010600311199 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 528674622 1250 528673372 528673381
    0x90904051f060305060117061b0d0603050d110f0304030f063c0902100507021f030608011107020a1e230102160f09020703030f09031806030b013005 65
    0x68202e0340004c940a00980001040c02c21144584417040010070000b0708041d100c220b61101403520459000045100402442c1000f030110b00030440158810300081c14004642c54004210298031010100705030082031030034548035000020b5405990304034494200c902075501d03100e0020f0003548545000201000305483c100380000d40050a0009030003803016041c0c84210781402280c500e504000c1d0300800c49080001c0640c0303d030380500880d40c405029803c41314440c104180306140e41d40f02c2c01c8000398440d00d0503c8000005c1c00f44d000c81d1100d070200c550401e01d141d0b00090a440050141c240d2143c80c4910020014004180d10001005295030065034820b0b0500b03180100f26900d17111b2805032007136000b007200350581010009c04840d6110544401da904000840703000c0e5009010540170580c172043c201041c1c403058490340004074401d80b50031b550990350031441c9000c0120b560094090518140440d42caa9070400442108450036851000c0d0a4450f510445806103800e00c02508880c608400c20 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 528675872 1250 528674622 528674683
    0x6101d12060402211c020124150810053105010e0114210a050106080c04050c03070509010c020402071211011116141f0603060b010e0609090405 63
    0x40d0242c1d00075104846541c6050400403511402e41c0c00c803591a50140c5040301c401e60b50000c268078240e10314030002c10711540c145d0f4400090710030030510b000c044201820410041641794400181004076041c05011880d0440104102020f5481034502a139542800c0c40c06840c2c2d140b862620744400d61000c6207051600d03e0034480204024040d01444c4809240080f8ac1080c0001c00c600d500040285440c2510940c2450800512180d480c41c4030544601913140c1e0025400380a66009070840720001c02203101c90f1010442990340c0509200d80d030f2070b010001e0003205640941100d108440c00e003040c214180d403500c08100244291403021303150282010050b4080e03a030041c43c0d005100700d820024029600110000070703851043d0300e01c0c06034540242d0038040015140582540f01c9000303c100340c500d00e1081c0244038650780300490b90002c0040d982c5038180104902d501c200c511039a0203280020b4880004000700e14603110b140b540c5482100540006010028100300e030440460248a54400450445030711 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 528677122 1250 528675872 528675883
    0x903140304050f1806130e0703140c060403020d030509031005010e04110103020f0a120204090c02030705060106080621100e0a031101050c12150904030903030e030606101d12 76
    0x400f442401c4090001c24145090040000c4040b4025004c03034107502c4100130403560b158030040c00c2d02d019071200e0f090081a00309220000046004500300f242c0c24440c20a40b906204a04140d07a00c55074081c80b042c00580c8942e2800c2280315454280256246031640000e03281c01e0f80540c0d22180b082c00d1000100e05402d0412006005901c80e0001880c0040c8000040d030590207941d08200d40548140f0410040303a200b100710315290315603d01c0c01480c0c9500c0d0000c200aa8001d459500e000d03a10000d2040100282004600d005160500e4410610308088000406a031005890b01c4807565000d82d001c86103110610580000f20202003080001c07084850207284c072010014002d80204201d50f441058510040c000c40c0d11510440510303d26058225800d1140354801400400c00140c0e013a000d107e080d200c03090854000c030700a880d0745107164910324005010401c507882030b030300030f801010a220003034031a801424100413007410070710030aa44518014a4903803a44502a50145282241e20001c8201161 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 528678372 1250 528677122 528677129
    0x150c090e0a06062c0a0311130b0d12120504141006081903021203041a011203021b04111201060801120c140a0e09010e06010816050d02010903140304 65
    0xd081415589510300001199028802c24000c40c00b0303461841d40c800c401490040e2a80c148080070503581e07082e0710118840380085d40045903c00c5991a100c801131420b601124650000d40b001441a94070301404158000002e41c8020b11014901e115040d1490003801c0c0c0401c803080682d41000103242c80d0030040c20152030758502c000103015040c1d14250104060003a01d0a8880030001403040c0103290340e01e441c40c0400c0c103034141c085000b0b00c41b0301c0d055800c0c15170003940128040c602caa2503c64000840e07000308203042e07104045490384c11200300c00094011030044004648204c0850b040c0100501080c0601014421640c6205002078030b071300040c00e090b41c00b83c103039000e46c0c4d11031585a072130f18648403241d400040c000c3d14641510b4420000800f400742c210801071006401005420340c0c40c1c42161001009a5441d081c5075180c400c1440908000c011042c010123500d40140703a07018151a141a618026000d1240558074080800c0103590040c1c050034010742d84041380e0071031031000300d80d0700f5100d402501 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 528679622 1250 528678372 528678389
    0x9050a060513150317040b040608010503070e1654050120120c0109060b03030a0c080c03090d140c06130608151f2316150c09 55
    0x2c540b02d07001414480c091000c240d07403201c0045141540c603000020f440c0003080840c803071820440441c8442c410350190004110944840c501d9504190825003010115044819818688410082000726403806c10100c81d20f81e003040c28074589034984100680001d050000810b0b004000f507107016001c02e01010140400004c54002460143c4801c0101c1d02407601c03c0600240b8004103903034014501c0114a98505040c808584001210b50750640043d002681c045203580d5440824105101980c022080030503001ca01541c5005554440604a4040240041c0081001181e01000054100101c0f81e01c00001840c10700c80302c12a2030039035045060100051041d00400c4041c9041d402d02d48251048080000600070101d818410211100b210082200b00103c00c000301060564441044140c00390407108080c1180341c540d800081c010a00ba01d0011800d01501000c0040340d88400c002d175903d100701400e4076000c844c614207000d03036000f003c01401030841d0720740794903d41c0c280c1c3c01c60703080000c551820 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 528680872 1250 528679622 528679639
    0x130f0b07020a0902040303140d020d050c091207080d0302070f0b010b04150302030609061e13020406090e010b16031701090203010609080a0c09050c04081e0c030703080f070201030609050a0605 84
    0xf4400142030740901c0c440200070490301c001609000710841d0190404540321840181007601040100b820340704144c546851a650014001c4800d082c50301d01000d207101d540c8010035410b441c0c07003400390355400c16400040c200741e80410321404004843c00c08104150f003050008a583d6143c1070000c0d00340c0e1042c81624007001d41c1c0e91000f8038079130003070003036a104980050080f501a44d40700203020100c0d00c2001c1c406420301c4000c3d40700351280d46e620500000d00010080058469080103405000820203400210600500c1c1c0c004108152204044407600c0ca100081040c81c21720b18517050750250865900d842410991900200303a104041d4040c40c101c0b2600c0d60703511b10084da2075200580f9241d011070080c2210f0443c00041c0703d10387d1260021508036110380d030110700c0c081d50348a100d41048224048403608040d9080701030b496030b45c01c226941800400b01d0141c0500d92a590302c6180381e100303000034104c1580f00810f00c0d0003903a0281e8090002400e58a005101d149002c0c02403c00402107402010b105440a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 528682122 1250 528680872 528680879
    0x424020a03080f19180b100e0a020f0f04080a05060a0c0e1002030c030c1b010806011715060c030d050c040b0a0c0615030507180c080705130f0b07020a 66
    0xc2004440760151101005616090f0f0204052180284410081c800719506501030708040c0c410340e0141d900609000150311000e1500c03220242024041042c010120300c01804452020b01205400202c0b004005070364682004a003a0039002e62070510084032804103000801207000700b40044224031400594010340c1ea000540802c40f40803090200010302102c06040450400701c03480c00191201c0e00469003014030400410349103520000c0040c1c41d60b00f003200c030058504400d60520303040c01c1d006d0070060010720b0700c680003d1025030703180105502d03041e000b4085404066150032600c0200d001a0030160348a1031070010541e69130204c1c14240c402440d02c000294103500b00815201030310300041085242c07004a40040700c4001c92000241ca0403582c45001d4402c4995a5003164011445480500022454404544900007007080c50b443c0ca035050030040516140e0150b00d4507030001d0a0308160351101003d13221610400c1143d0081000460414004914445000080c11505100f01d0b1504038140d01d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 528683372 1250 528682122 528682127
    0x91103091216030e0d0803010f08010b0301020301080d1b2306070e0307050f0f041410080f0709230a20160201030b0d0f0809090f040c17010207080424 66
    0x2254042c60105091544501c000380c0b04038414003000d14001d0111848004540f00d03408070764001e03031011041c182c046904008000081c0113040201c0c00480c002c42c207561402c52195202c004a0041000700000b01411512140890840100e2030750400a0008222002d14901c280c2c9410300610341524031030740c000a040103200344018600e040d00036000c0c0c04514500750512804494082107181e200c8000c01c904003143c0c4030392062000405c020140102d450030803400b858600e205a4100c82960342010481d245000e01c00601c8000302c80f114400059030386203007036100c20406400d000c14001914520140030103000a034000704090740e09005000c3d502d402ca0f9200e040180b28100c100c403604118900002c0142d0f00030b500c10345000d00f0180580740510001d90b112222107201610448030f210001c618000e02c0c0c2041c500b02030740b014030203d001c809400c1c6071f00c84080c202441d00c42c1c014500ca244541c484079600a405a0700c5403540105859210354480b207401103080584044a2030800403900d0144e101407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 528684622 1250 528683372 528683377
    0x51c06271526010216030e10051206010e04020d0b2107090f020c1213060804051902030f031303301206030803010603020d0605060f160c0911030912 65
    0x1030042500300070500c0d00444921405024505003050100780003000001c1000b0700003000c85503070343c1e080c41a14541c81d16028141035003400000d4016984c45203901c05481e0440201c1d0000b0b51000c0700304c103441c0d0301d22004940010901072800c0c0c0040c00456856400c40c3c858005085000045840ca01c45081000000c00e80d4a0881141941c40e808040c0420038464650f1008172a4000f40c480075142142c0031b0311041c9002d00b580c1100c0079610002620440210000d00508054041c503c1c000071582000d40b500d540c1c40028402c04502201c00c05580000c40d5002c00290400c03103c084141c945507042c00200c030b120115544401e48141c1d559041c1c1007008146400114031030381c2400b51343c0805040700c2c581202c030540200e25a03800d4a94520300440801c281c1c40c003950080c40700703607005640c03803070040d2801050341d0b250742c08107010311401d0022109509222098410b0400c3c08804114900b01c0c90070f02c19020300030b9a0180c004c151a00e2a01c1080845600c01107101e40000d9045680781c0c0c81c0402c4800951 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 528685872 1250 528684622 528684641
    0x209030a020d080d111e180a0303020d0e0a030c0b13091805010f0e28020d060501061107140f0a030c0308030f100509130201120c081e01050a06051c0627 67
    0x10b611031900342040c0034001400c078404140b0f2851014001d401c0125023800c80c00d420035400350380485401d095070741d400118624101c2c025110584141d2035507a030f000d40400b0078014080d5181c004035450071150b2690800400400084105208068880c08000003d41441d4001e487c154240340242042c00ba050080c620084914401484081c08107003122694030b21800c80c140d0b801c1070313159041e4050f9403104003040c01b013801000002030325450100054000d508042107485150003400c1c0030000b1041d51090985080f00c199002030b007a02d40d010000d003101131103410080c010314004001005111445014500c5405003c042c09103d44801201c1601307185680310362507001c02148000741d43c14203d800138040031841814072416200c00c10803035405680303a4211500000740380c0c00800038890020f46034000d8444030810180c010b54181000300b15034007850b010300e10a20000082009001d0108402d5880701900110300300f04203620b9030700c03d003001508039041d91118071401c5484040803160b4810880007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 528687122 1250 528685872 528685897
    0x6010f210b0109051b0c0114060f090a111c0c02160b0a1b02030a12090524090607120804020103051008031b010e01060f050a0803030f04060209030a020d080d11 70
    0x30781e182c62200f1018100040c00041c010381280c00d0380460741d118401810a10011900115410361200c0d81da041445006000910a00011203500180e8444c2c80000390420f4041e0004901008441440411807044c0059120004110040300c010f022040d4003003101c100041d0b094440c0180021031a601c0c5585501900c00c0300841001803040407030080b0380880b81000c4010340b107500c075400754001a0400361054420740e055985020400822a80550f1110140404882107070707001212944451041d041000801c0d00d00c2d90001d50f507003913a1384070020b5940341e980c04548800d032641145401000307900c00740d604a02090030240800d06200540b00e12505a0b01c41c0c60045090698007035010110440a41070744805550b1103071075092001c421301520001d000c00881c80030034986408244945200581d0226505820a10500030804240c01c199600282c001c0c101680300c03d51500080d00345905200000e42c030403900354141e8100000ca802414002c507034914204010305a1618110700da11801c4e80c00400d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 528688372 1250 528687122 528687143
    0x14040e07090b03011806020306090f160c0c0b071506080102070f060c030b0a091a04050105031504061506091d010620120430050d050c030c06010f21 65
    0x540607590007000240e1005001042c10b48601e0f09960703200c00c800d40103407a01c035000410002d541c1003e09809820140c000d05494061070300000c10001c3c143c2540e440c100308810340c01780c141400707140a0407501801c1000304803a52540b007071801c810395007030585c0c031181064141540065044010702c2070f1400c1a070851181481c3d8440c40d500c0c80d0080802e00754540c00c1c1075840f4013030249900c40c450310b14050403207100b0025007003540c0d0b82e1140e11204281d0315944074504010040c4450b44000c40c41d485c201020442118064031246480c1001e0400e0001c10141e40c12080e400080c0958041d04203421144250740140c0e00c442026407000b5114000d0050350040360015500e440b011480f21400d140000d001d6080e42c12001c2e001406003060307481503010818183c01e8252050701c40d031006134550300e0080d01c08148000042d01e030307484030b07100e4080e203062701d09110002c01d00d003401710402d01c11a6101d2150b14156a150740e150740c2068094543c60003071107120140c1145865446011201c000c8101d50022074440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 528689622 1250 528688372 528688379
    0x3040314091306030503040807120819050c03160312091a070219120e220f0f050910060603020a0827071d071e0804050106080d0914040e07 61
    0xa0407940010395142d0421500090701a2840d503a2090310040c500c140040c1d95203a1800c1a068a4000140c0141c600c8003031024115000a1285040743d8034500800c03140480003070f4117041584c0c64018003018800b64000024842d01100d074410100c606035100780c03940100e117003803120400304941241e4002400701407251000010640b11200984e44115240b040351002c1c207580107641540c001c082001c60709001c5000c400d110054000c7d502071150802910210b003c00030500c0160050207201c4071f504140c0e613491290740991321050f000b0165400030700d1024417090500c40600359660807000030fa050590310740800400d220b4030a000b10ba21611650b5110701183e298180750191400e510708030900f007012460341002c0c902c0d0050110348000d200e9000d00c01048900d840c0b0400307481a00401c800c080001d0404004003440205402c45003450303c61038041443d03038441c5801801481e0603001b85040b072288110311200b1070f5000d564031080c1c407004070550f070a4040107021b00050b0b0320f2200d80020150403030356090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 528690872 1250 528689622 528689657
    0xa0221090d03150510030f0c03140109090f0f0503090325030201050f0403061b1101050c0f0c120d0b03190c1a120c04090506010903020a12020a0902030a061a030403 72
    0x910300542045480c880301139646001800400c0c94000f01004281c85400c0141c1ea07901500c00e60880880e5421b05110300005504184140141409441180340d502e0120206100d044811a80043d45c42803000360000c001e0300b00031740d49400c44072800f0b10034412000e40704020042c0d00703944070036a90003021402e0083d0840e4010355480d00300c0139211050007800e00000020844030b01445802041d5620818000304076500d0040c05a44040403400890f030501e420700252001d60002c130303009a50304801c2c2c070340c9074101442800d08000c0d4003140054800004545030094080301d03070040035100c2d421421510980e40460702c5000714001e02c2005031046500b0001004602c005a0a414034162803040c068604000c05907040480041600e000107840004242844081040c1c8107042d00031509084c03456070382c5d01d56030000d1134100d105d001d41f60f02254624026011900e569a03198082e0903030030019501c902e0708040500040c1518840d10244002c0d4807030211912000c2c1007103900070782d015951203007003240b0036400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 528692122 1250 528690872 528690881
    0x8060106030e01111321080d090203010b100f030f1407050702031c0f140309060610210e16061205130203030703080a0f0b010210110f030a0221090d03 66
    0x42440e55403a2030b420040130020100405818080c804e41526441c1000195106040400221144a09000d000700e01090112041d100c01e03c0c2c0c81ca50225845526101080c09030500d140d0150300720150b60494405107420500c68032003401030b40d40030060b11b0341c0c04a40768240d803000c05161486149040c04500158455401000043e00107000c40700c2d44004101510f0300d00070302440540c00901042c0e850144283d1001c0120507892000103183c0c11410982e170508c0d1030f6000985903d22038441c0c841301a42c464041c0c0e090000301c00c01a41908064598041341d0000703003a0302c1c0f2010244d4000c0342000000c0301d10001c07500041c0d4502d41d603104c1c1c43c80c204041c000010320340500081c00405a0041c50001130390100000d212482c803070750301c18851342440702e040000d664400c070b208060903060200510507640c0c0000c6801c00403003090790100ba4400300c8200e145d214442c0442d00d90042d000007040000342c45e056001070116000841484005000907056002848010342c1c1481941d000306160481182c4079400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 528693372 1250 528692122 528692141
    0xc05060723160302130b0d0809040c080103050613020111010e06060406050a03080f0c1e03070c0509070516150e0d0806010c02060403150b04020d0614030304061e18140f0a0806010603 80
    0x70002801540c0f4000140740b547c55520440d41c458001468403074a007418015420360714900e080100a42d41540e0702c59442d150007c1890142c00802e6008505580c46541007820050000d8001c0201403a603000031520f4002c00c4403664000d4cc201000080c0c141440001002126080000281800c80c0c2401d0079005038003030403c00300548140b42c900d2410450381d181130001c600c00c1c03000943e5116050b00d030000c1148030b40d034000b5103d108020200301d445500041107500c1501132140c01c905000d200d2400b14403d02c00301d494104520703c0c02440301d00b050800204040040c00c07548551840b0f41d6204011100140c540340025080001400700700009030704d07d58140c0c1152100440441d001a2440200c1c0403600503000481c03c0c1c0c2c1d20f0b0441040340c02c002615030b06a01d80194084c51600c3d04105010341140a107070f0485902100c040c124205040c411b003050312580d480958012502503032040041d01010301c0c00780c82481507031440580c1340203141c0300d40c0c580101c80014015211903032034050254000c1960a9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 528694622 1250 528693372 528693409
    0x1312020c030c150909070e15180411041203111e0601270e0c030a06050a0e0606100f1e0f0f02010b0a06030e030f121e041e0c05060723160302 62
    0x3804400940e5070423021000c0803d0700c2c40c16074544407031050f4003110212141304280928500344407015a07003059002c0300c00b0758241c2000c40c05803156038502110f18410320640e107400c0d40158960061542d0b9074035a5049110b141104545940c0d803030365006561040010203048480410392a5400f0034100c98000414441d40c2c002030382c840030602000300c0d00782602e405c42281c0e41950740041112079000c03032040324400342c05800101100e2400c40045410311480d2080380c0140704086041310035051061040c9200c00d030130ba8400d9083c507400071601605403903010b80c01c4008940c0c0b400218942520500c2040c0d80da520040100707a440746410030076401004404811044c500041100c41403806006d4000c1c08066440324840003c0c0c601039084400d0b4004128258401e510b84106010102d8a036450600b4440c00d080a0a900340d0b0036031508440211a50303110641102c0080f030782105000b858150744141c0660791908080d581070710100d007171301d9216000005042c0304003403d09001505060145540550f601c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 528695872 1250 528694622 528694637
    0x2090612060906160c031b0602090a08060f070314161101090c1a03060d0b060319030f080c031905060d02030712031b0c05091312020c030c15090907 65
    0xa03401505140c421100b19040f075204105000103d8025180084842c81c20300c0c000f0a01d0406680081505200a140040b6020600d45070400d028142d41240c441440040c048601e456503500e060b5240d00080b1540846440b000b40069820741c0280a20f01c955400940142c409656103950324665610b110b503444100922042011800d8100340b28021409000e2043d20000a213400200d500f00034403010b4108011105000380303d0a81c0f41d4004034242294021903403642c1d61b4401340882d203480394031001d45210240b02201c00083c590010144031500086680d031001c0c076039400d4000e405070b03c4141d903080886030864000f2501155554449034210b813006002703554440050300080d00d800b5041e04100428403030085035a007050340042500ca40c803403d003042d1100d8030015031a8500703628010b200301030040c4100b0001411040f507803865107984983c00110301a912817448030095940c0c49040d403aa01a104810070a03001d4a00008014030aa00b2082440d103810031603424007820300c901030030900910201 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 528697122 1250 528695872 528695899
    0x30c0807151104051f09121b1706070f08062b0606082505060706090609080901020c0102060411010e060d0c030209040b040b010c1e02060304051507020f0604020906 72
    0x1402007214242c800044103880314204000c0101c8011008103542101522070074050100b600710722200112461101c00c1200852107040110310f070b034030901c0e00304a0202549004903880c1007011292400801040031076100d0b550b40c031410303941c044170110340c80301044d10f40b00003403200e11b003503403141c08041000d0000b442030a1181e0311020340b0400c01c00044419a803a05000e02c8005030400c007421004965900260f00c10600d50900741d0030030524010180900d40001e403000c28040682c00c100d0345c2c9580039004100c01946400c0c200d00e42d41111444038018012038000300620f40c8000342650080341c018910703170558440d071401542c007172a624001c141c00100502000c40780c41c603544034030f03803107440542c5015030360310003030000c000450f0901a6010300c124074140545d0303081e0740e0081150458543c000d09001c4182c501400d5035248000c4a0b000960164000040000304180440c8500c001c0001035469003094441540c103988803081442c8019181d1310000004000d071501021407500500040c1807100d50f07052 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 528698372 1250 528697122 528697163
    0xc030907080102040e09241308040803070606090b0301150b090a03020603070c0b13080a18090c030e01060e01051f0e04020703110c01050f04090b0a0e0115080112030c0807 75
    0x400c0d442882c0405144040140102003442074113420302c1d40e04c02c8000c202c000c40c1c0300400e0711f8102070400d00c0d0808a0142d40000c0002030340440f4060038281084940f500f045190440107410640200c1d150310f81080500c001c07a0405001e12291204c45907400d01c40e1500f0203404501a800204001e80d2251111308001b000d81c0b60351000711302403a075954452600200601b04854101c41c040c0c440d058400440e0031074004600c6080039280c103c180c514107807805810101c1030f00842c000a8001204061414882002c02505984084100c0461100a0140590303a101403020540248a0782e60409ca4041000e82402c0c0400c00c4526044000d040c006500c082c0440803138100d030010706080300414244050403080c004200a4010858400d10b4054075004c036100a94001e0300541c800e8000c5503446d6482000e682e40c44440202c040d00d4200544c0c0c21640c0c4d641e5460714007074044142038000c2603104c2c0021902f003003042070f205202034040d151200c2d5020981d4481401d03622245050700d001c8244107440841c0035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 528699622 1250 528698372 528698377
    0x3120f050705040311060a0e010503070306030b0702031b060417030a020f0d050901051524070206031f0b130b0703120f021b060906060d03090905090625080c030907080102 75
    0x1c21542c0d44940301e40c198a40080d1000300c0c2207a03144910402d000d00c1034070fa0703404103088480030000c0c6080c070b85a4543c21400e0b00030300000d8000a10b002c4015081022060780080a00041c0b03110411904014500c00c190507295070040d41c0140c110504c1041300400240108010340c0c020b040c48a0052424841701c040c12400e4210f40841c0a00546075820701c85441000d028041d003082e45999903940b400520000502c15103c0c0c5210030381c0b05440021007040c503000880548502c1d6402034421039030381c176120958810651650304d1007039450010748001300e40200c043c01134884d085000205031400d14141400310000307030040b050490130010000510f21003944c6038059071881d4107451001580b12000740c0049166511514525030b15680300c0300421080103000908550441000da40556041c10141401c4400028541145c6841400c0ca002d2102c003100004540d4460b2640c0b0504140400c500548000040c0d180e0480c01d0004075520b010414808640c030007140c20030000c001303c420507035440b40150b003a41c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 528700872 1250 528699622 528699631
    0x1e0312072c041a1e01030905030d0605010212190305220f020109062a02060906040806010303080a0525050c07060503010f050303040806010e0c041d04140c060703120f05 74
    0x203000a01000e140e042501403024030110503540d02460f49140ba000c9102000d00c1d03000e5881588500710b03c60042d034000e07809194900d420406880d92003480c018807101900c01e52003054010b2081e0020299043e03500f0050f1480d294110140060050340c5200072070180c1405002e04140c0c4000014a42c0c2c4850014007014003284582c5034890170002034000501200550741c03144091191601a4111148080b00c1341e40c01a80d044660514620700e82c0040790460241d02951a001840000c0c040303600c0c000044c189040b648266110a03560b900c11000c40e050318002e48141e603000ba10b00610140d00e0f045408001010071060bd800307030405544d0380c03d83d8074115585c3e000b6004140c1c004010b0040300e400d2103051003d0001a00150f1920340340080c0a580e1b814140f1034642c401c5501d42c0440c80b070365a14001c66008040c03c1800003c0c2c5a8001e40149140d0020342d42210b46200d265104c1300c4402cbd0200b41041c098200034107190a1401d0740d1401d450031109000c41c40c010f903a461702c030507010081320f1080741c1c0138 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 528702122 1250 528700872 528700937
    0x609030e0a090f2405090a0603060203041a0114010815010c020303040b0a11030702010801060507140102030a0f14040506060f0103021b060105030d181701021c0e1e031207 75
    0x60080c603441210444189281e104d604148694518880c24007050f401800c842060311421482e80d9095210801007120313410040c000381c0000144014007150306154202c0d0a03840f40e20340b6450f66581080040340840d18241404a858103001900320b500004c6c9030340d51644181000d201001702940000c1c1503600540124410800102c0c661080c103501903074248004084600a6180c04990b40020709203860511402042010018420007040f40141043c500b20803a840299100d080400c60385001c2c01a00c00c0405c16146482e0b501892059103555690140ea0000003415981c0c07110814054005415943c180c1815000c20581401062404900010f0381000d8046c01543d41010200340c00c2540d40000c0c0b0040062030300304424804c2c81403d800c0211402d0000d4070101d080381c03202042c00381c0145201c143d070304c0bd41048401511001504040801c04455050703031010f80b140d100000901c40032031312000c0c0c40d80c42440146841e000000b01d942d0417072807508108000c2441581c82581d010b00780c0e122500fa = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 528703372 1250 528702122 528702131
    0x6090324090c1c14070b070609061a0a060e370609030c0e07030906090303050613021c0221070504090c0e3001090f0218130609030e0a09 60
    0x1d8400051000c90a403100407168404401020140c0548038204024090b118140019040c0e000c0c51007000980014040d0444031612042c440c20f05070001c2c440581c0c00d0707a40504019254004540c012818a84504001e218070061800c01c4412603042d0941004641c004188051000d1618880a04150070880461820000d541180180f8181c031406034005000c1c403440c51028130010f046c1e2544101031b1541c4054960ac1507482d918120060200c3c0350014020600e01003140051683c140c110314404d400c25036001a60140c000709041c1240b0071685500b4103c2c80c090401010703203001d0b400400340282c0051061241501005405540040940e400d00210350009010405a0f0484c0106500c03040c0074100000d100c5928400f05004282080d4810030041c110700020500f80c074642d0b11b002d11380440300020031421a0602e001010341d14580030603441001c2d0309100c00b0b003c030401002d040c03090a441200704808040303036503802d01070400d42c0c008600780404030902c1009500d0b000307105002040007903000f04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 528704622 1250 528703372 528703381
    0xa02090604080703200a03140a12110609030a0504181116150501050109060f20010c0e06130e0405010b090a02030a05060411032a0c0c03060705070b040206090324 71
    0x6003600840011201c000200c85441d21580d605c4030191b604594103c542015900040c841150800601120080c44041d0890016450503484008508886501400c66040d5110f2509441c3e41e8092000480005807080105008140b84040c01e00d484a5101e0004100c01d603c051500080303400007140340a2000c101a07290062294800c161100c1d0380e40d203038081005504020000b0031b0800309005080a201700c1d400f040c2c0841e445840748800c04d241180046100c007400006c5180a0075172100007100090f0510410710242c81c1c20805c441d50700e0031000b000d505c550f14000300c803a070710724008000303603419582c5062040050311109402880b88480317040c01640ca16100700300c0011114041c00042c05285415110030102c070f140d10849400005441e4800b014011641c000140c2004202948000c000042501909008002200b013482d034002c030103a07204d0b9528414101c0e80b60042c110050a1480d8000114002d400d01000800c45268058140c4420305a90401c0c50b42402603012174000c2c1002440c03c10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 528705872 1250 528704622 528704633
    0x12070b0702100507020a030618020306091b0604080d1812080d180f0611070614060117070e10030f020310030507080a05281410060b1606050a02090604080703 69
    0xd20800e51142409400c28104d90041040a007503030000802455036100e0048402c0c2c40f200d51402d82d140d0042c11140c0d01d103081c0300c0090b225240c5400c100025904003d44100510300362050700c06480d030010083c217095204050494501c901400040b200010442001c580348039203035240c1110b103005096156840c81e041407202c045640344c4000442c82084100c02c000007480000c00501d00540120000c122447c0c110f82d282054401d951006009070b107071480ca401a040180c4442d44284400d0305c0340b00001e01d80c01d50b202903c41e0100c03900350010314580144a81882c00b14174407440e408540c50300140d903007081d09100b402c0340e2050f2850081c5121061041041200c2000000041c08041024005000d00307a611203540b2180c019440c0c18505072120701400304170440004030460b0340c01190380214040002101e544420040e480080041c2c1402c80c0030595031a45000c80300c4130b6031010798803d44810710b03445641c001c00c00035003060f00c403540812410505a8410018001500106018012851952400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 528707122 1250 528705872 528705889
    0x51807021c080f1815041e05061911030f0405010e010b010203090918030324090f0a05070909060b0d050f151e040c0f03050708042012070b0702 63
    0x24560114807954a1104655000c40c40303a8202050000d112a952034040d101d05400341c141c2600145480781200100c0e914192001c0107000b5070040b08017002c1907502503000214100c000201410a9000d0400328000b082e80d81c03c400b107070025000e00001e60f26402d148100842d0300c03c0d101c40319a0440d0f8020b000a00800b8443e01d200f4502c61750080000c00c4080001030b40b24007903040c0340c911a45903003001461800c1100f030700400780c880b00700c2925543c0c603004408910108414420181201c1d0304072501035903092040c0703558055040c110b60207841d580e401c0d0300900a00300040811041100a200008456810340a607402174034201c01000e88802c403100b4044c04444001b40b40c41203100004c03080c0141010b558901d02c45558040d01e04d40980d440e14041c964003003102d00c1007150041e2501c0b45103822281c0c004c0c0c8030800c4103455502400720b80c03a89041122109421f80340600f508084007640ad800c1400741080080f8510058003002c444041010110300703202d602c0e480421845000a90a001c500d4007294 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 528708372 1250 528707122 528707143
    0x1a15130b1009030c2310171f1208120414010c020c0f01050f072004050610021c090b04030b07020105160c0209040624051e010518060405180702 63
    0x62a0994034555220300041c0415841541c0803105105001421170413a180c40c55111000940314003002111080020222007404800840e52a04500802ca00b0020314000182c41c0014600f51800b0505108101c0181c94030f40204541e4200c0401c103181c9a45820942244124003580810b03007180b100c2c004c00ca09581d44440e1440445d0003e50011003280d40301c070f841303000d20303082071a00548480c60300801441c203204003400540000520400c42911440e0100003090841c0140c1d401e01081c3c07248424010318040208442c409a04140341c40c141c40d02e40c81041040b41c110b140b40900b40a0340c0c40500c400c09034403503001680c00c04900707810040b003207809008843c0c00583d00c4503540c03640114800020030851250000a200d0070920010400780650ba4001c502800030040c0005070200c01150038002103280c074810039005116030302604004c4054460002315410f4107843d100e14003030038280315400c0c40c2e03484020b03641c0c4100288008034081d180c1200d01890032a2085000c1180c3c107240c407010f45050341141e03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 528709622 1250 528708372 528708377
    0xc02030d030f1b021e15090109020102010b0f0310050402131a0a08070308031f33020d0e090a0e0a080d050c16080a030e03341a15130b10 60
    0x6400e00c656000030711080c1c2c0c0b13404074031070032085154600c0c103070034420306c9119901600c1440080c0480003074194454804507200360001c11000709064280107803501c84620060b45500240d40d4000c0e100a140c1110381d0040c402460ba0422900c01c456881c21911441c1c604000361003d110301c004e0600302081d1902c0642402002080980d15542c4c54040c180305c024450020302d00b0084090350880403144e5410301401d60100c1c082002100459461411558203d4035203107a62141d440705a051300204a0040540e40c0f4ad0312a07542c0c00d106820f100094034058454a10139581e1109241c0042d000e0104901781da225015076075441000316031040c1550300140202c4241d01080003044490422098641d442c15480701c4c0d0907880f01c061110550040401503d410694000001d09100c1f0f9240300304550f031000010107444815404a04c402141d04030740440061001c0d4001d464a41229400b2401e640e00468000490005110000218954034032015508100945601350f600e00e52804000004610440d40b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 528710872 1250 528709622 528709661
    0x809070308091c061109040f0e12090d0605040c05090f010501050d05040515101a161403070812010e0a1401150203070b010e061c050d030203070c02030d030f 69
    0x16140c100091040310b0003144603c80e1090254a46803400d40c2801c0003d0b08024100140101005622855400325071041c0c4250700e89012080003002c2803080d80040e4110b00001d202d000c10174092002c099112100440e4001030651481002500344d02889100314455080c50f90311a01c2c2c00240140d20801414011400030560014000b43e40c2c081c096840c1440900740c003050396191030400c18202840c10824881d407661403802c12909c102d000240342c00302e4100c40494100134860342421280e600808186200241202d421440460700c406285e0711120380c007c0a43e071404c2c1081e56007510fa5440b520946500c60b41e40d034010420a10f40a060341c0d80326050520130700c1012001c20760354102107814054411015000c903661081e952080041c0d9a03c1e41d80000c14004950b141c00d56001024005c681151107500142944909240c0307004054030f107294440002d04c590a85074805801030340004020030208130300400040d0250390204801401e2018079180040e4206034801680180c80243c03e20041c000d5a1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 528712122 1250 528710872 528710879
    0x13140a0c09150206190e0307061506020c0901030204020703140a0906180b03160249080c0904020f0a0e0a0906080703080903011401030515130c12030c0204060801060303080907 77
    0xf10f80640c2c4403201c8010b0303000d2941c085ca440001801074080c3c0400500c0081000e204125482d0710020312010300c680140a19550760030100da59481c000c03d92a000005140104018101500a01426071080c00c1054036442030412400700c1e41c0000f07840c1e00000700550810064907400c00442c1d601c0404084204240c1e5007400c440001da0b00c000342541419620607690304603c6482484030201c890901403000c1c1c00325210751058000500c0004801810b4625001020410042c01c98022003103281ca03107580c44155034103a000c0d080c54104034032080e0000c2e003c100125403410f241c030040010140b41c1d292030040c407042c0014414003020580000340224900306040c001c01500003030304402c0303d5004480a40c1c4510b400c000c6800360500d140242440f009008c000700070420042401c80706c0e100c6880e603400c9241c1c2c07100001c8039031002c51072001e03003041c407001c105210980365070886905290181c10f140e01100165804641195420740c01102a40d43d0746106108042d0320003100c60700001d01d00000d0801c00e08 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 528713372 1250 528712122 528712127
    0x1c0207151805060d0b13020c060a0204030b0c13050a0e19060b160f060501090b011b0317070507020306090601080c06090f010e0a080703080a080703020a020c13140a0c0915 75
    0x101c42c01418841c00e00030460541840c0d00b03070000281a20b014084140c0c200034144214080c0d040400d00c1d4046010301c1001645000451003540c04480d0071031031a0041e6110690041c1c4603078405000742c00c21141c543e1001c07450342c8a000c0f51030020b1900c0303840c1c0c16041ca0690221540500c070320000c0f488850a042c1e0400900f60880140e07814240c031040c15102e42c070810714020b545000b02900090620303080400020b03401004da800207854090030380b19000302000d030000107442d1941c2004024045006104420000480074022682c01074050400901d440403540010b0301d05a4100c5041c100350f0711a000501680109020403d814402503c0003030800b4079901c0000d0b07031040310320151410047c1a00901c102c564400b03005070010092001910845612414449020350118160300041000c0c1e202144003a0f1180c42210301c0b0303d030039074007604ca90310b021010000f842e60b02c141c94020f480d03103403c90702c50724010f20f0500c2c50282594403400540b040e0b0b109070142002050354000c0003120528006204c0d0307980c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 528714622 1250 528713372 528713417
    0x2061005060a030f0f06030b1003030c0807140a0f02010e06040806040813030c0905090c0603090c01030504080d0612210203030a0b150708070c2403020c1c020715 71
    0x64044420984032051003030100c004150801010301e0160070400c042110007220b0f1b00c424281ea0144171280311903512012074246c0f0305a2848010006410031900c4408a1000d802511070b245c40741800314068901030310414502003c0d0041a9140c40892040704119a0054050041903505a503181c1c1880d1401c20066200c10008001408000002070203407a82844a44a80c01640c1d000b40c0704203405032600600e000810013120200c480384501c0020400c9450040252442401c0c0034000781000140640110050000540100d030503c8081c04021401034140c05000041e01600303001c02e0703500c0b032141031005043c6440a9a4880c0481c000d40201d83d40d5404802c9952021103480003281c0d070008403000c10044c0c0050100405d9030000461076008204100008080c02d0b40101000d0a040340c40d42e440544107050300b02100c41c40c01c4165015100c0501980141c190596031000f83d40e03984420607080c00a445296400ca40140c0040340b06102040002c5c0c5c843c003601c10300b03140100c02d1410f02617141d200d03807 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 528715872 1250 528714622 528714629
    0x150702010323010f03050106050301180312060b1912090b04030c03050403020301060303091806051e010c02060d06030b150108040b250906030c020f070308130806010305100b01020610 80
    0x961521071a1107560400b01d4060541d20640340e0441566949000f60388600d003850004440795402e0980c00a450700d814001d1040c05100d158600b03c0308000c40d0340958204c07000c200c07401c40ca01d8640e4000511600c1180186c82920b80100c01d00d940b40d517401800401009041280360405d501c2d003c07503000829807503046150301070360600700314101c01014141603c1c10302456000a5041d803c1c80008010503620000e03e20464010407002510400000540d4003511201d00079a508400c400401206200c2d40c0c500e080b09001040c10000c140505079004070300d940c1c1c4204070701210b26455441c20010000304002042e0f0004518415002e00061840004c08050003d00050001903075600414400c00038055005150501018040b001c220106d0020340710101501c103640201e45080c0152103020f001251801e0840c5c2c1d140d004d0107020341541e648030301c0d0b9000030b00069407208550310007140c0c1c08001c01c000b0b4003950180e0001c00c0300200403000380301a03400c0c40c025181103401400c1403000400a508000054 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 528717122 1250 528715872 528715877
    0xa1d010312090e090c09060607030f0f050d060e1e0c1c0b040c0f0206070c0321090b040501061814060915041e05090309012c09012315070201 62
    0x803402802c580010301c40e00200f10b071101880c2071142e68100010502c03080041590381841039036501d070411016024078980500031890841c4070174201c2e40f01e410310700740d50040c5050142c10404c442582100f00e509a40100705501e20041c280a550881d03030042d11030311540c4070a030f0950b519000e111210b503401410141c4050201402d151170154441380c102038455900500304011070144000018014800d0001c140c000d40210004a12600e01c12910605d1254041d10307191942e15800a00344c000b01654a20041c01c90b03619070301c14000509800301c03a4000c0303004030004208a405c00000141c3c2d00b03044503404840500d0403810600651a98200651083c0301310703a184010307907a41c1803207243c0303952400150b5841480c04405145d00060380080c10308504081d0400c012561303c8140065403403040c451294081000341d070410014455083c81224840101c02c0100403c0000c4d6011415403002a007101009888804440d1090f00c4081d1030300c00c03500c03404c8800344000070114040280c030b803056000c040d04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 528718372 1250 528717122 528717143
    0x1060903030302210f1005120705151902060901181205030612011b0206060303030f040b040302250914010e070e040b0a090504050706020d0206010b0d290a1d0103 71
    0x14407200a0800c000d2094540100402c1e1703e01290100100c50342100c034036402107105080031910b401c0504404c0c4646130420010000d032400c1104010100d1610030307001e42c07008400c11840340300e00000900030100f07031803580003000c036820001c84003401d440d800041c030400440d0441040021680071807031021034210500340301d0f98a864580110390200001c50055900c4c4d8244080c00182e050030958052a0390b402e0350a0321100d494580030161030384000da8109c074001e040c0d40040f0300481c2c41100d4444c0c0151103401104e2807400800d0013004030f0303c0c1c8000410045015420b04020703d02c0b4074000c88a450b0380080140304150306200d04403154034400350021081044c407001d03002c0b064655a004c14a10a80200512040399641c00c41c00040c1500316022a8140144407000840d40e0000a00b89184211034002c0c00c0350380c1c24880e1a900a070400134207034040c02d869840032980e2a800307a86c0045100e84160f021109a44c405003030160b9544c8660020b400002041c2081c801400600d140d1815a9030042d040c50 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 528719622 1250 528718372 528718387
    0x1e03080c090f1210140f0411010512101401020d0207211a07110703050a06090c03021c0c06050a0507121e08040c150f03050a0618050f0f01060903030302 67
    0xb1448910341e03500755040742000300301c04680c0e81c001034921070b2285000c0c01800700c00178030400034606240a0790b0411031781d0b10a4000c00c000801030042101c01200624005050008001c00045c400100303a42c0c1c442d040c50380701000e01c56050580c903400ea808234207000401e883c901c24440250344003507038130407810080010740e400c1d110321201e049003090301500800d01154101d28004d42e203501e8a07060300d1110100b444079440c1c090030b003000700306281100d412602911500080c1d48a140250500110031605c900c4c060f1400304c016130361a065a942a80302159010250501e403600981d04841c540005060107030038411440c0466221003200d070400d62001401100c40050001a201000c140120301a0b046215280034220360b805000c46200d540102100c4108640d600909a5010802c42d070100009050b5059030104500035008660403042c00180054595540c00c41c100400d0010390041041a0702c1c0d20520482000e45090315822070b040b82018400c9514025000d443d18401b0f101c01802d05802044d400b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 528720872 1250 528719622 528719629
    0x81b04080709020306030606010201060303051c02040504060b0306031b0a03020d050f03040b0d060608060108040308040218091015050a05130219110d210213051206041e03080c09 78
    0x158000d01440003290700301501d664a91003e0342044801e02d00074415540011540e40c4140100c40407079400d03417525454502404070800e0140c4081d0b0300020340b0b0380c00f00b1002402d5202c82c17003144000d2103218221601c0e41003040c101818181c1d03c8400029218a11440740d10681e16071000c402201e0703040b41c4141c41d402403898010708012840344104021f001c0440c00061410302e881c004e0a03000c51a45080140075160481a10b1070201660001c1c0020301800c006400203001d0300403550000d00080102d154030141d41078500621004454041c69500710f01581520721965008900d0700404c1d040c1018416400d01007c074484080358030400d03120712000c1d1028503801c642a4101da049a40701c80840701c10000d140005804414100e5020b000da01c1108084e0034024403402001201144034244811012040b40c0000e010350004524a456000440800103840e5540c1c05000f041401c40b002070f10891405080a006150044c506403282d465500c40d0170b0002540215081e5004100703481498681d40e100012 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 528722122 1250 528720872 528720877
    0x30c01080f1303120603110901060903120c05010e0604290402100c0201051605030304200a1403160e01030b09030304030509061315030f05090f03040504111201090501030c15081b 78
    0x1210031340340380000c04000e2040c94200e000f40c0c004290b503a2051340e665003a0448040103644030140c1010007128020007514421340d800c4048034058000400c90b10081000b960410078103440407034450783e41f903c060740c50740c88115112038020090321598046260a4001c1030703507101c0d0074018008001100818500f1680160180c0d0107141c46004940e80901072132510541e281d00c00e0b602078400b62040d02e840d041c040c4000103a4425418040e00403100e01d8035010404c0f0801851108550341401990112071400c100c01c90900010a452116240254503500b808a0100d20280028190f81c200300200004a500f12007180c070f04480603113216a80e1b03640441c840001550a400c0300c00f04001d0503035445c10301070b40354104500000c0702810401c41c0f511645091583c4949a109000030303a00184010000c07483c16030f020035841401d51020a03c0c0a404c06101345041909030017503212566900c2c01403081c044040d942c1400b41c441c2c0340c4040c0e04007864150140c052240206642e4500401004074525031060400307 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 528723372 1250 528722122 528722147
    0xe070b03180609100f0608211b0a120507020a12020613060c05010605030f150c0903010e030a0207061404090504020409061d010b0612010b03091c0905030c01080f1303 73
    0x10b84109080c943c1d02d264950750300c606078840e1541440700c85241c500300c511401c400ca1322000e0090201c5e070341100036444000c850701c00b0060014400c0c00200c00285243d60385001d100001d201400ba5040c0c2c42c50300d00c9980280f150720318100101802000016202c0300d024209a5440440c02c15082c522440065070034032554481c0868882450400075240b90498403c1034200e00c070744001d0002a483c0c209055a0349000c0841384126840440500404000b0103281c07a0004050b034012403404001001003400d41e2003c11016400c0c1c0c3c00042c1149292350b061001401404081c58030a2001c2c01e00c28051041c0c1c00b03a401242c05959454020400319555a401050029800642840f80c1440007105c0d0720306840381541e5000b95428840b15845c0c500d0036100312180d640170300241c03140b940d0900006036041d400c001e0600e0024880c000000140d0411b0288107a00c445c420f640d104001401c140525081c4000d07581000e041c000078106000000247ca050350368819607511071442d002e0820b090413030701e1001c241c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 528724622 1250 528723372 528723421
    0x30314030c091c2009061908240702060106050403140c03010c180f08060f1f0e180604050a0b10030209090102090f0d080904110712080a0b040e070b03 66
    0x210210b101c0c0000142c21020140582c2d04140815070940080500a5044101a500c030a40e040006c0007840c00d940041041c41a2001120303000da11350f0807141c036003440000003040c0301c600704418514180e20801065841011803015114552502c640034299004034000140340070541c540c41d02c0794140c10480c8100d09103004000b4401000d1541c80505045c44c880c121004142080c2400718a42c0306400082080b10003003030040400303585d860380031824103070007801ca4148079000c8034207000342d0a110b95094001d48109014456182440c1203502054102d030181c009031500b00301c0811012076004101c090317075160000c045030320540e9441c00300c020140081d00000d601160b900c0034007004400540c09441d0392035058034040c011605160030843e507032141c007500900c80d41c4100310300001c9003003581144104c2030825101d20701f40312040d03490213610400c030340708980003407403030403c100315910329002c0c8018680301510100100c48420355100e4480d0003500a0320552180000440c241c0c40116607031138510031342035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 528725872 1250 528724622 528724639
    0xc0331060f031e0501050319030804171303030509180403050912010b0a030602120108161a07060e1014071d0a031703090c0105130521010e1e010501030314030c09 71
    0x184480d0f00a000c00e0089500038800c6c40960041e03810901800d02c1d505030103848400c3d682d600da954201c020950400760302c0c1d00140500408d402160785081c1e2901551083d2142c1d03072200302c107074188460114113042194541130f042e0140408290404201c0340080c00540f040450039101c039000d00d02410358406c40350303044040540f000081c000503a026101e2040421150840d6076603c080082d42e0b94408a03c0c0c44c2413041030b80003000142410340d0301700040d00101400600b810420380b942001c9821041c0900c00c590404401d058424609110b08100b5100600720083d5900b0944d40003404146100c2003905c417804201511001d0f6526950200c2c02150b201c403107402d04c4882020301d0347c120b41003501c400040340700712415100d441d030059055441291001c05844040703460101080340b208821007014510089034011a03400100a0048070500c80c2004002c0c041c040c448132007850002000b040641030750b490800180002503106103140c200b007100c20034450700d0b5191142d8912003403080098040c0d005140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 528727122 1250 528725872 528725921
    0x405070c0c08071e0605161a0f01290f090f1323090a12031d071401030e0705092d0f07030e0601180905030c0331060f03 53
    0x300f00b8281c03690002c0890300000ca0f42d07814421300c0364902407180030560601c2190300071059401612015802110b0b4502c01d03112035620b0170f52820050f40d00baa42c001c0d45000600603025410403543c12070f410380f9210040b1209000d1440214060411041491000024112003650310210a45001e801c01400c540307100e1a0f00c7c403403000414881e00e081503080522040000c031030713040da40f449100b0b00101c0c0103410f0141c1a6500c02c411000e01003240c03410305540f404040c4c51000c0710300200c50041c2088008121242c1085001c03c41919540381d03136410941055040c0c0102c030710120307441c0210352081d142e001030b9842d4100c509119403c221300c0025410181c940103161100551501c6004071a02c207039142c3c1d151540203084059071080344540c1c019034048801000880e001d1201c4045003904500c2c00a203001c503035601c141c1107500081c14885181d101291005282500d10306805100036600b00c1d03038045602400100054407824401d44d018403070000051103070180250880403404000ea050003c07482c44 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 528728372 1250 528727122 528727139
    0x2007090506210a0201020c010c081e120a0c03050c0906040302060c07030f12180506180f041e1805060403031109040606031e020a09050904020f030307081213110405070c0c 75
    0x14060f070241c0c0140301e5111a41c21030f50088400040c20750b00300490382d240401c4190703156007240401a035100005c00800030b008020b220f0142030750051030030304404a051400c40c8001000c1d2075001c0c06008415a003041a980c8580c1c81004480440c2d6068508070344400c041d416007818055140c1c006080311824601a50070420310249454120f5002e0720f903041c1c00107070001c02d001c0b00c1e80c07240a940d401000811503414028068240702c5c11582c0010040401000603101140c140c03010300e16946043e03150104603030071001d000d005502803180c400c2403061801c0d481e900e40710758030303500500064185a81c4444402400840c903044072200000500144081607803250003d00800303426440050101000e244100c5140030307130003203c1c80500e03c2e6a0720700c84c0c00d04260800001c4400940200d0384080b80603240c0e80203407418000707810b1a9000d1441581c403020313040e1401c040c00130000d040c0c110000004084000285400000b918484819500054aa9101d0a041d00c4044a891029011910032031002405c20b1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 528729622 1250 528728372 528728383
    0x50a020f0d0e03070b130b0c090d11120715080112050307080a03090204060b0a110d020c01030b0a050d2d0b0c0a050705010f0509011505090708070c1205030601200709050621 76
    0x7e00c504004a250b0b59500303440321013800360203819540980d410400b8008a00a01c56414041c00028030204074265811030851524050782c2c44070302c000c3c0c080c0050b10701864011004da070040800804101082003d580c8071a100c2c42043d0000b0710028000c9010140180b003503003c9400c4036400b03842004401d0321007001201c140c100524a400003202222024003903200480c110f0a08412a0007c01c0c8800051006501400041074080c1c2c02800710040000e179a51107922840784240501d1186043c0001207440850144000d160321400400603a40c420000b20b507076160300d6200e8800c668042d20f4200c2e0b2141100c041c86400c10180056003420680c5002151560110340151132441c02000080c000921036400c410162051036400340c040c20000c0c0c482d43c0103c0301c05a02800c28507003494003104596031403149400815072103000403004800c104540d60404407040c045c03040c0d8110345154680c02c2200c1603840300c01d8001e01c08269102c070017003445910b440401182003003048c1200c02185010b040c040c0d43d2032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 528730872 1250 528729622 528729661
    0xb0705010912020c0109090c0c051006080f07081515061207080105150304060b150408060f010b0f0d200c01150b0a0c030c0c0e0c03040501050a020f0d0e03070b 70
    0x1001081002c2c0401800000c85000d48101a110469118604a001c100820038035060006202c1d1800310702000850520000c01d488140c480005000c1d03050400441c0f4184088c0401c06080e4813221051200710f4000640081441240c442c109550341d407080d088103080f000c5084250004408034030b0101d04000203d00c14405e14280c0d4de144070f103a03070310350810a0010b0720b9810900d4882040000c034020400c0303504070b541c10500c090042841d0013000c80300580d581c0d1203a4803908840c1c001d0300c00d002c5c00c0412414498014520b00b29a18104170302d0a610051130b1044c140d000781e03201d81d03403032940c0684100c2614082400c20b40c2403219071103e40800b4030a018224a44100154408104010030120b400030309890b89503ca590350014400c005607016108000514400d68900c910044c00180044103081c0c03191040300031814035512428589041425207801900d14020980144840381c07282001c5016911546c40c80311012840701c000d03207801c9081d4810064064582c08030041006081400409502c050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 528732122 1250 528730872 528730883
    0xd09020d14100c051e0f1e0705010c020a110108060a0b040b0405091008120a09030c030807030e040515151b01021c090f020f040209030105040b06032103130c0b07050109 74
    0x8500c154404460b140b04011400080050398141c2e85c5020502e013000e00300110081140501e04450420b140700107030440084c1006044c070000740d59081220a0090800504a034001000090102c1d514900c0c90001c0b48a414104401d0304000b030801e0340c0e10400708000f031104c400c4d11303a0342e90780b200341c4030b01103910070300649010322886008260728100860000341111254006860002825160744015130300045900c02006400c05020010410810700c003001103104119940ea01c50f0a0301d0702030058444c86032218451031030001009111442d81a081600040440381d9150502c002001c48000b03003d110f40d03500003d030300e415001e44000300c15802810f6918500764516080c00d858940d000036108104001001c00d003609221703800504142c0a0180142d00081001d0709007605800401e00b10781301190309a0b0140344000034010715050501400c40c4002458007241c0e0304c8139601404135018840a0141c040285c4511540c2c0e060103a2152280c0c050551003c65560300c0c442802e00f28003904205405898 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 528733372 1250 528732122 528732131
    0x252609011406060301030602220602010207060f020c070303140f0705011d1b041a100305150307050117070306080706090e1e1b0f0d0204140f01050d09020d1410 70
    0xe000740202080e80300e104014000d0340b5503801d5640b204042d42000411416001d00540049a215031141c2d0030005400713540d0005866008904010003500c0d0040e00400ea60751040060080900c4082010700a4940505014501c1115400020228031612040840c142c401045210405c4019001030414007601c00c41c12140c80405a4255106c20000d041d2411810b10703081042d0880c00c154100816920000034111841105a008503902c949050340040010390780780100140200c9003a900010000c0a0f130061811500f03000028026501146030343c09400e1242c00003c1945100b6000304001c3c20340c80c010340b14a540c2d680c40c06004000d02e40100640c000502c4001400740140c0309001128031022442c1074103a4503031008040071112420140080007004100c1c4407809803903034008200a40045100590740c42c508070410166180d00c2240301d2142100301d006417001e03030703000041c0c1e001c2d4049003200280b01c080ca44009581903502402c01403041c1401c13140c1c0606e400d0b000c01e480c403044041050a00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 528734622 1250 528733372 528733391
    0xf1e030d0e030d110a0818010305070e030705220905071a090a15020a050706020f0f0705010807121512110a0305030a030905070b030c1b030325260901 66
    0x1a020806119442d8250303201602d4030b55024424003803000c1d0f07822a41c0c20b071510b862040d03d60000540c44580400c0b50007884008106455a00d07119842d4010031500d40400e208101d075000035101d9109204040c4100b030424404859102864143c070707986846844108a0780031b42d8509141c8944151107091a9031820b5044c1e40c0c92071344850115009401c008084540700b60402903540c200300d401460355001c51150303888400c0021802c10450019004640082881300c070a0004075240c503650762074090064010110801c02640c02c810519000302c410b0400090059140b460f500082a6912400ca01c00d00700d5000010f0702030201551883d4540203006800c00d462805060101d4a0250701c0024019070042200c00e03040d030f02c40d90001c081984108151140a56070380d0f860455504262003444000d4000242d03105520042440d0228100902016508500d428228654441a40c403030005036100d150072040e084078403a81111000048903030703048100105901d040310901c003044036049001d61921000b403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 528735872 1250 528734622 528734627
    0x70507210b010302060711130b0a060c050c060730030b090912210103080d0e0d020a02060d020c060f0105090a1e09030309020d03030f050c0901020c01030b0f1e030d 72
    0x440841d000711080c1c034580d1969080c00f05541c000f0b072068914030500043c0701007070303503d4020011007030941074400300d5442034810401061100d5030303010744240168918144c2c00100f010039807103c503071422500c80e929070070300d0300b08400c400d440b9000c4041b00c04141c00780c00c560b80041c915404205c100c00c0c1e0b810041d0140c100d052040c0c3d00b07029102000c2940c84651528a10303c6014001c8c640005c1003070703280740717000c1181e5541460401d080e00100c403028008258a5181c0440307200384025603844200502131080c01002c06501c480d0300c010040c2c00b0358400034a1000030300180d01156200c03a102030456403103242c16928a40c68903020b020780c61040086001043c0c2c1d459250140320183e2802e110880c24561980b20401d0042030168021400d050700c40d0184000360b41c684101c4403c03540280c50100c0c1280041840c001103070700041900542200a0080103003507640001d80000d038601c203081c009800d01100c80064070391000280c030540d00c01e0910743d16189a82e40b4541c00801658194102c80c48805046000d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 528737122 1250 528735872 528735929
    0x7060f0311040303230f07140c0d02150702031e03070203010e01050126010605120a0b0702061e090c1c02040605040203280f050403090311102f03070507 67
    0x4e00090880885200b03001d00e030300305940f2021038190702e0783c2c40c004180e095420240c1000c00c0a4482c02d1500340f003a00080c030306208401e800d05003198466904190f560008081ea091000c2400743d810300411400211744042210807800312400e20482c0d95440b080c450f19650707900c0800200c1c025400c0c0181c0060010301401254166590141e041043e0b03003450b42c00c150006130100c0031a01a6490b1500090b641d1079403102e0704401443c0c0e03006400c4854650400a84008003e0002400c540c004c13403c011401205c820150350800040c09407100d60746401e80002d2a0010f404042640010035079941340c1407802194030400600e20a95042c440140e0b00c0c01000202d0008075100090501407001784400103000c082800420005502c00007070f6590040721140884e80121411030219030104014400d0007803440c01e02000b900200c130500c01c1d0741d000c00001800c0192010000c050007140044416001b0316022440b070624622008030380e11045141006543c802244c451406c034250f05440100303074640701124 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 528738372 1250 528737122 528737129
    0x30f0405192003030706060e071d010503240a08061602010204051507080408031201051309122003030c041a03070f0e010314040c180b0f0f060c07060f031104 69
    0x1009000300c00035024840031042e40200a68036000030800031001800611850001e481c10441c0c1904074645010701501c0040641000c030b5004210220f5007020760382c44022039901150304d4110300400b000ca17070141c5c41c1404e05180d0b030070b03401100c0c600301051140c0001551849050f4215141c00c065889103800e80c200e12684c0600d036003220b0018a41003021380300000406800f441800d0b501d28041d520b002c2541035402c015070702d1402c0600d010042105140030501d00c41d12101082c0d040080000980c0c039510301000034900340b010b02420220f01d81015184840201c01118800160f980d01d10b8030a6401e1707401e60160166503651074410751b0b440000e5410506032032081d0b000d611007441040c80d000042d40e04098030383d1683c0c105601d40000a0140b103c1c05010b6015034415510345903090b0800301844181d116074801440e40c946844040309443c4d68100365106400b5007034400390441900030340401c15512520104001341d100300311000518550042004c40f0718071290340e08008594407000c90784d006110758070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 528739622 1250 528738372 528738383
    0x5070e090c03060102281502040b1e04080a06050f01060201061d09031b2118090a02040302060307090602011802010c061d1605010909180311010b0303030f040519 71
    0x28001000a000100107540200d0705004031030201d8454100903050703128800040e00300005006d000410007074030485002120002d100194101420000905c0c2c0300c4c092007120040701141c0c840075101c44d101c40b000b210040c000000aa4017501d03400c0c20900d01610313041c0d580441e280310405c00012210f20611550003035440c5c2c2c0c00c0085004181035810070540d0400f40510305079000410040b03140c10801140c1e008442d080401501001b40b56000e02c1101c1408140000f40440d01001a11601c1c030300520b17061980f08044a0007030f0035880313011004000780542e40009400c0344000080c890f0704c036004150307103040300c100e13900901000b2001c02c25203800203800d401c0203003c02c0b42d24000301c0000d00b09410030904850780410000c04103600308a1103107081c5000850400c1507a502c10306202d40d59100c80b035a400b4100e0f01005010f20f96103456160b180143c4000064101b0100d01d85a0014860a401000800e00001c08494490030321910841100e50b00f66400c850f944502498440301e03041d00f80d0740048054100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 528740872 1250 528739622 528739639
    0x20c07060831140105070c031701050906010318060203070e09010f12020d060b0d0c06030b09010b0a030c0c08190905010c0c1a040e040809030f0a080406050702060909180105070e 78
    0x1000345103900900103a00321143d142e4001c3d165070701c070400d10915100d081d0036600c06002c020681800703885030318000141044448003030010300c0240c6a05983c550003020030320300000c200040c8424080843d030607400c014185030002081c080c00a9001c190001c40ba0021281d40c05540d0385d84101e419003100911580d020940c0356040040503291650610402900800011038151941800a05080c0b00c000048030014007900b424061580d05200f042009101a030700d55100e941402980c581c1c5019102a040426032142180b035031641c841c00550341a150f2001c0e46984030480b446291141021a000d1203002900b0181d000403e90f10481c0552020360308081d20134445414070640c0300d0b508045400344040041d04010005030b01d0203401c102441103004441c0c49440304012010181448106882550264840104103004c1400b4004581c00c0310401c0c1855656001c55101041c102d010300313228660321600c4181040070f461541c141c035030701d2501200000c11040d600c0d85001ea071701c40c075443c00164010282d03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 528742122 1250 528740872 528740941
    0x5010c0b130c080d18050409170309010e10020913140f0612190506060d0203030d0b01030b040603030e1003020f0409050c0d090f0506280b1201020c070608 68
    0x1d031103000301d441c1d01512603000920349074292030b842c2c6009014580700017030a409038070a4071150403038450098581280c1c140010702660305d8a075101150846030b0400c030070000002c18240ca400f5402103040c2441101a5110585100315000003074000c40540c4c0c1c041c14071103045c44001249481442c0401d401d07400403040a494004124142c45030061030f0917001040c5034000c210728581048100b83c4200c00c1800c07011100c500f40341c25410501c015000390f002d804d01d0b599810059074044242e0340c040c00390781d0001441c0e40000340101c000d007503079004c6260024030340030010007410340c400e001005945041c1c0780f850205691a608800320320413003052940281081c4414080402c01d50401500105103810990a000480c050178007150b503c80000c607800c3d400210460b00b040320030301415520101d20b0200840204051400c00c2495452081038000e640c0c1d600148901d1b41d617071004002e0840c40c0e0390021510b601403052100c0e91141c3c030317000e43c5001c21840c40000344003a5649146801602e5008040d5103000d0340e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 528743372 1250 528742122 528742141
    0x2070b0a05090f0301051f05030f0a2006030a050106022a01051c0f09052401030f08190305070201110c151b070c05010e04021201061107030615030201020705010c0b 72
    0x5001c06503442850f008100c211a0f409004803801240d80c0e00c54804440340c030050f0b108210480d94000e9019800c1842c00070000c3c0008103071020050340112280d10348410500a04480d0403450340a00da0084007c8144506811298801410b90703d15408a58450102c01140d00c98542e910540740f014140280006126521490140c0700708801858000c0b844018a83c09a003950009410f41040a0781e8820340400c0c45000c1100e04503207084d2252045a001401044200f00c64050001801c05104503240b6001c2000c0c0e4000c49a00c0300030021107418014480800401800094800100540c04d080080c29400d203060200c40201210701e0040001032030041c0d448110b205c00038210001c0140070503e0315030044161004195a5100c0c0c030306e441e00749007040005090041e6801180c0d000d24410b000210f01000b4040308541034560300c0c00c103070b2024190780e8074180c81d100a40d000288940e0900045041e28607028002600b900c1c400d03005d95420a4460004507805145041d02500009150011980300361 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 528744622 1250 528743372 528743377
    0x904031107092301050117150f06030910201801020a050d0f09091a1302090a0f0e06060f0a050901020a080a020d030f0c1d130903050703090602070b0a05 67
    0x90311042035416603a500d400010032900200d503c00c0b40440c018000f41c0501110707100140c007401090030454107104c25640e052010300802031024804580340f104c4c4030f045581c1c822810b482008014143c40d602d191a0300000d0300c84509015200d40d040c2081c00d500c46200024100c0c1c035040b01920001403c0059403402031035210208400c0c0c6055028a038410b001292040c031004c03c00341030716280d410040054030b0009044c3c10059104101c0c8a15190813078001103040b0886003281e9100701d0703000d0f07440071911b000d03c802072003003800d015071042e02c2c510001041000d50b44400221041e0503210040b80d0344550a000070351050700442210201c040000446441c06100a4090020107104458820078160f480d0b00e66035001d0007012015030321100c500031344c0c5540f5025043c2d903e08600c000340302c00f85110030080c0c190b100c183c0500049200562401c14582c441c43c1c0140003c851940301071103050020b040140403503010711000d8000802e6800d001c2120b900000b040011210f00b8030001d0300c4c1071405503040301d0b180c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 528745872 1250 528744622 528744647
    0x406060c0303021e040314071401120c0210060915050405040f020d15020a05030603012405130902040c0305160c03021903120516032301050108090f1516020a02090403 73
    0x81144064425485661300a000614466808480b0040e04151581e1602c0c6603a802202c030615800103032880ca9900c04140040c0b40c2c904040411140c000b02000d03800d04800c1c5c08070307016040c0740c250300085e50f0801d604034140450f055020050040c1d02c58050005882048a0107400b202e41174003031b04014104004241c0c0210f00581030040d00140401e400b4090740c3c0010209400a140442406401e19081c070884130494140081c1d00840b403501040d9000b9601c0c54401e292083d0b500d15824007402c2404d8005020143d80107008000707410505801900a2206460354203030030741f05503240010603004680e42c85210350590014100f0780710007500d84504643c052011000c200a00b003c0841c9071415024450003503911840590221900010050458185440601c462803806d00d03641d0043e46124005815280207103010841655081e00c1c00703140130040440c00245214281880c15880018803040b401106000759040300c110303004c00c0c12030359a60034603c080d500c0034429000c100001d01030b90810818 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 528747122 1250 528745872 528745897
    0x825051e0c181e191a0a0e070e120102070302160f03150f020d0c021002040b120a2409060f0b0313030207080708071508090a081c0603140105060406060c030302 70
    0x1400c4580b0f00000594000d44a803c56541a011401944a07190080c0b26144011211483e50b00381d400340018035000c0107110380712605045d00c021442145c42040d8400107184064501e080c4020395041c024003e501044098005020313401e0030341d0640d10100703803072011240e00381d5034085220b04548400380d040a4480c1070840c0240e99580d004a15565030002c3c048002c08208001955080701e0400783c200404968000b2040380704003c28081c2d407403040180c5084400008200303a00d5035804410000038461102005821440d1100004415113a0341d03001c010740e00004c0091004035a00ca002ca140c44000e80590301c42c00324140002400c0c03150100d403c18085003e84125010103648003403007800c2500d660410340d00c5801242e4140002605001422000d000320b00d04031501d4544020320301e8680d0b00e5043c00030202c110001d0000b03000f0410381d00180d1081005182081078541da854a103043c601b043c0800c001c994200b500080b541e00d010720900048441a840e0150401c1325a40d080700203600c0345104025 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 528748372 1250 528747122 528747151
    0x810050910110705010e030c0a03082205060a0605030304031101270b0414090127110d0603060c080402090a1119030903090f0605070825051e0c18 64
    0x1409035405840c00c4182c070060502d030303200c0b61402c01c1400d5802ca061a074101e98810405030032107460000d503104101d9014134110100c1d07141c562210b079842140b101800602d0b0342c0480d401c1d082c00f10200380366015800801c801c100913030780c60b0141902d034000c911010700b0400340403e881d0181c1d4010902400700341182c101c08900c000e1117950420080003541c10100c8c80d8500420103001442c45030321301c605d152104a0f240a1258949405400b0228104c0c40c035032085940e11400341e02030700440d0014281d112407180078039140c4455a0001004104521080d80c12600309810707910038501031f10780301d401180c014103071301c200d9601d840d1100060314084066144462080040d02c084103912074105100e10f1041c7c0d4042103918071810010031310011900050040680f003d02003090f15000411191025484000c4c55111410b070802c0301c0b044c07010111070050b80560080e2329001c210b4085052420708400003c032410780d99501c408181d0307620019002e1030300180400780d55000110416003803944003d07400480103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 528749622 1250 528748372 528748393
    0x70f021c210e03031506040e0a0c110105010312081311090606070807050c18010b070f020a0306140108060a0c0206011707150e15120406050601032408070b030108100509 74
    0x2040724003459144440d030f0004020b100601000404120b4002c0d82190b03164141400c201c00c464600c2d50103001d61481076036504907003e07128011017203508160583c00080043d503940e400c2c024001070013003145400107403000d000a00071403035000700079040c1c42d00300701000ca64000f07490500140050190280c0d41c00101480380b60001402100100403041c41040600007802d801d5080c444440007254001050000349001848800c406d042901c0403c0e81140c2140900d06c80f5001141c1141c06c107800c00303040c45061907844403004400c582c6441c12142507500315a602e540316002c6400700c401d100c001d0380060300010010026a80203c5000d6268050700c010340c0e40da2691b40c8a500099441d82c2082e07800f05d04a64442a110b10349041c0f40c502812075808118a420700520300310400541c0288000c01c5103655901017840c076407180d0322007296500c090781c17201c2071035001600008980f2003a00c03410760903100f0120040b4031a4403a5040e24126000c0d90001c060035011000310001a01c4010041d41c840e1040c09280c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 528750872 1250 528749622 528749687
    0x309050c0628020c090a051009061712090f010804062a170f0a2003180f01090b060607030522080606010c0b2d0c03070f021c 55
    0x41100c035609042c80d032a9010a2100c0c402071070071559a48040d500268404141619400c2d030095111020110009013551002c000311800700c0c80d0b8012050076032a183e004100004c8940c03410306240c0000d0300f295000d4800000e01d458a115107440990080c5844051205c00d5014015031381e00b02d4441c032000700b0120032092000c210b1a403503460801d51a056049503c424a802030300e1050243d0b0b400d01c155803035180c050021001404040e141c1d0b0283c0e6074404ea400303500a00100305d55252504400030b42d45e00c1c148069150002400c01071001c1c0e8030b024074003000e003c10780144a0515510390200e00204140e44d400100001c5400088041c0c06124003040750301c0c5640328540340c00650f61041120642402d0604268500d88072000f1b2006061000400a0b0801300f1180880d1a40c003406928111000c000184101c0f00d2030540a291180239561440c140007850185401641c0314600720740c0e441c2e42e0341015220032651010141c1280708961260740140c20018800c108040100c01c0607041d5602242000506 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 528752122 1250 528750872 528750877
    0x90c0302070210230403050303071407470606030711070f0e0123060d09230c0a0605090d020f03030307020726070b0310030807060605040c1403070309050c06 69
    0xd400001c601010980c130061081070f01d1054440b00700c0c00e00e030502e4255a90103949101c00b03000c81c0c040c020000e4010788c0ba08801021034514552003541c1d0303015281c0c1c2d540000c1a00d0021052070b044c003803046c510a911300303001010b01d02c41020700307640c0b0340c0f540d4490f6406e00c25298400703014a001c00c10711002072501d03048200700980003400082d5401d0926450900c441c00000c00603008200e680028444a0814602c452040603c0c107070103d407001c1c0ea407640c01d44d03198000c2c01e4a1800a200d100e5100ca1900308a000c0b61008910380d04d2282590581803000c000c0002c4e03c0c0303460060a002c640184003126003410100c206050180c40504101003030600b0300300207481c5070012a88a40181d000c0d940c10b20082a100c03600e4a14181003d00100c0c24019868031551a146140590010068040001419a061000040015070300424140e688098508000015010b24019a070041d4104210341c4500d40c4110321034007056058000403821a19148001c034068440d0100942c0c682c4034001100764540c2d02c4500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 528753372 1250 528752122 528752149
    0x604080f0a02040f0506010f2d020303060a06140304031206090e011a030106080706120605090103141c08061002120a0906021e060121170d18020a090c03020702 70
    0x40660700820310410040d00c1e00d0840f8074080c541031800b8000c00740d802006841c80c2e132030203050034041940d40e074072002068112012542056810704801c1c00d41290003000075800380340150354252443d1b46500069504829400c0802d4803100c04000140209114100c880c0113030789106000700718180d695680105841815a00001a03503407005054008200c9407a43c000d40031041e40248a040d240456840d00e40c60a40314000920a21943c080c080314100d601100240c04020b01043c01d550310303800c0c940600070304081140d810b4411510301c9504002007804c5440c549046641d038103c140d403064103205051002024401c03d6100e018840b01c4e10340071400213001104403039a603851032107140c950024a0f0816020001280c0b5004200e120100100891307160b066810040c03010906c024105002170b40301e002941e0250000d0070902c814900111402c0080c003d40500c080140312050720b035941d402c090030500308000e521015440040101210503003040c00c032017400b030800504004441e00030030f902c16203259 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 528754622 1250 528753372 528753403
    0x110610032409020d150b0907210e0d08070206010e2a16080d06050105180f0a170d030c051602040f020d18140312040f0c090e0f060c27060408 62
    0x100c003a0040178501c00c24003400300407148440036040040e0080c02c0e05181c014400c000712010340c8141c03a1260309820002003030125100312490559643c030000e054a00c2504d0010040c0552800044d04800c07080e41c6c00d010764680c5500403903c0c40c42e2400c125011045082402c3d07060030500584401d01024010080e19a003d8140140d540090b500f02c80c08451454002c281440341c1070001c0c1104071100c40066440d200f0a84441c801c3c40100000600803c0e02da0f400940c0c0405081e141c02200c07413000c1411395113464103850500151070f071140103440900420300003814100306040c0c0350000d85080d03081950b0844ca149030061405035440400c0c0c05482c4180c00980c80011004400002c001c010b23103442980d01100c80141d0304100c401140b0034040c99018101903c90394070001908280040e030316084000740b500390340811a10641036502d5032142800c481806050060400103a60b00a0341c07411503640e020703001e070080c02c00d070589100340548e00c02da04400d0750002003d1102080c0300b1800c00c1121403648402 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 528755872 1250 528754622 528754643
    0x1090c0f080f1008101b03140408090a0e18010c0e010e0d0809041508071a16020112020309011a030c010c15021b0a06051f03020409021f110610032409020d 68
    0x340d101240c030707545441b8480c2c1014a4410662030306c05110505c40c0d005503000b24420f540300c10b81c200240d510003454110201807020103040c0300a954480d0f40d00c00d00c04011314001d01145800325001c2d62510402c4200c036020a110066403201c0785400603108200d0703803007a40e035141040a4400800e045a9142c1884212038040b84400e000d41e40d8104904001403100041003072215242c00d0304c07e0614001c01e01d845203000030300c080360307001c5a0044292042151034850110b44924280d01c90b107001c0d00c403904e5080000e40d5204815840790601040302c918800c41078481c0c01011200f43e5402d4820130303004001044890b402d02c00700c2c666000391401c4c131000090a100814021840d07051400841300d000e4240c40460310301700340501c48400c84c00000710840c1d03011100020f0000340d5002083c035a14a41141900000c14800003201d659040301e0742107a4091907004803103450361851450040c0c00b8490202522056070078400e18041e0b6250006d64100700c1220202044202240c0c2c003103840b4040280c405c60742a90b80d03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 528757122 1250 528755872 528755891
    0x60a03051c02070e09030a0c0f0b04060f050a200702030a0c0b0c1c12020a1808030a0f022a030f010e15070f0806010f11060f01090c0f080f100810 64
    0x422a4002901540c441310311581880d119150f03907446203c0a100910548900c41030030b00c00d04451031581c03680c0000c1000407034900707450000018401101200c1c00d0504d84000b01700030716000d00c580c2e000104080440400001407a10001d05500441c808907414469142c1da131000503401100003000b8440c0e19203261301c07050300100090410340d11101030100d04040f10001e00c4a150721407120b20004407901c1700146d40c1c1a1007513040f40c08840a148147c010320b0803140028030510b0000040c04504a80c2e51240c04080c1011000c903200c0c0e8942c90404600d0700c5d13209104009240c819410421703003000504551501c0c3d040c449035800e4402651b90b19882c0d40100182d04003000d10400807542c4400f04d07241540c2e006164a1000e40004006000345040013400c03541e140078030b40140802805594400215491450080040c10f10702c4424060a01c845042c4250040002d009010a19035a100780c0c40f04ca007242e40da640c0300c94141c4e00003840380200040d84070001644450038420358084540070302c00410542075 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 528758372 1250 528757122 528757127
    0x150703030b09040b060402030c12070c050601050103110f0313020d050c0306070804020d03110325060609060305070b031902040e060931260a1119030305060a03051c 72
    0x3050700749a401036420b1010032000818103020240c1c0183c003124010784a4680900d034990b24000c074125070544144034414400e40c41d80007441c091945104808880150381c84500441c01d807616074400914103401404082c44c1105001d000d181e20a42d81312002c0c4040040c4e800007000380c0f040c4c4034280d40540050a4100d17450505010303c9501c401181480010b6050685c08280001c10001000e800c008582100009680d014400c940034002c945503c91107621134400c00c18524020301e01c00719000741c6000b80016211030540100021203030800040c0403041c0c58080d20088650004008482d4080000b12501c41500248040c0c03000e8880c054000420f40380040a001040340060a0320240c14400203985070b6500d051036820101c0300d42030200343c4a0100c2481c1c00e0b0010b02c0c2504103241407120041103020301d444100060240b5409070360b44c07a100c10102417001e81e140d49000c1d04c0184402d008800700c1010074083c0d00001e40050340600788a090503503a03111142060825071030140030100810b20440c9080c2d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 528759622 1250 528758372 528758381
    0x1506110601060806010503070c0c0f0b0a1701030c0b030a02040b0301030629100f050c030a08160306030201020a030813020916030c1706010e0310020406030207140105060a170c15070303 81
    0x10107030400c102d142c2005000a01b02e0f000040400c0200500e8015200420001c00030b4280100004c0c00010f46181c1c59003a151a107420500340e50000901d290b100042e404065032441e41200e41007802241c0280c100700d440c5600382d100401000c01950208000640e030300084000b1402180581c00c0002c50f514120440391300083c8100b1a0603640707018110b078015982e0b03165102c400b06c0c800b60070300000c12111103806507454000d01c00b500d1344d00c4c00081060300180d5005030b400e030f00c64514400000c0e15003440d100e05070112074040c040039005911203031109000038022005180c00c00e401e000790401d0340300706074005008400100c941c6004c015001c852004516094001c1c1150400d4600740540e0318509100407540181008007214104254041c0c0d010b2151014441e1407a11850f4030029075555440d5580038010358884041101e100c0d400c0c4c4900d080b00c1c1810f22501e40520030042a800240c0c0c9083c00e5000008200b4020074024000c0700c02145030750340c4011042e07600c1611418491380710100d0742230160454 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 528760872 1250 528759622 528759629
    0x3030c1b14041b0e040b0f1c05010e06100311130e01061a04031509020f0901061e0507050c12010e030d09020906030a05030f030901181a100b0f0c011506110601 70
    0x16001003070349a43d15411601c9000c4652050b18001604820080003498042c90003010702e400290314180d42032000c40d180059094079008034003c3c058004001d034140c0d0345410441c6c5082c5d010081e0042840020030007103249016001c004c082c826500081440340c01260225803201c84160f549000406c0000c82c0407c50056018034010840d041526580b1540290b18905164401c0d0039039400740103007150b0b115035110902c81005045c0959968481321301a1030950300318441080301003000503005500384900d04468060ba803100141c07440d501c0030707418040020440800503085548aa5000c03440081c100301500307400d40000030102c2c80d01d0060051094943d07010302224000d03008544648086a4000100c3e41885d4841003142d5a980d1000b83d128014030680c2003042a2012000b50f500c280049082c0407d0104042d9681021540320341c2c0201d4170721441ca1007070a000b104140960364a160488014140c2020314900125142034801c904014410807a041030011604441c07401803a09020003249016 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 528762122 1250 528760872 528760901
    0x702041409030309070b03011d040c170d03060e100905060a0503010510050423070c03170f0603010b0306040201020d0e12120c1b06070f021206190e1603030c1b1404 72
    0x7d42d41821180c4a61050440c445c420300504080814104101c2e001000000c0000c0513100302c040e10001d81454585043c0214040000e007000070100d0941c002c01052806644000c0140e042e00e0721f020401000342c003006119a074824448040058603450a0203910300c40c2c0500002d800b0070314100310421044400350600382500b02e07182d611701100d10b500c80102c80e03008407440c24a00301d428102d02e0101c81c41010350380c400c1000940b1200380903401d1070b9035060600a10382100244281002c80301450390b110011140640141d0004508101240c0120a00f004000c0050000340c2200c1d500d16240e4036121850280d8000c0c91400140c60f07079032503403c0c020340d4171050032240410420300e41500000c40e98010070030040e10300c6981d0f150110440d41e0b050002c3c501900e400781a1070751864400c8030301c04032040b009002840a814441040751103100400c41d1904014081040e0b0070b15820b54508590201541c1004c0300c07a8014401522040703444100f08100404006a003c000c003d03003881844240c0d908402480340 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 528763372 1250 528762122 528762127
    0x60e06011a0c070308030c0d0204030501050105040f0506100f0201150e040201080609070806060904060509040f031805150c031608210c09131e0614090702120702041409030309070b 79
    0x31144012610f4421250000e0021381c89445030709a0a46078414121040c5007244001800800c0100640100d17048803409c40d000c202100d03030280904140c1d8421940a030384095061032851076903001e01003036890035480307100000c0c1e2030384c050a5408802c9030a800440706040c40c002000110760307004210540c064030a5500c2101424003080150040388040c1ca554401d08011070780d50501e44940e4023980044c0742c0181489840e0500d0304141e2503989041c0c00175400901c50382030001220400501c40720440d0301c068100c3d61602180400c0e580f4580213440510329900041065182c1d49541154041005029040382691808611607040c400c054115100c0303102c82441c0100a042e245a5041d64034640081c1d07041385145410300a018000e042c44140e07001201000c0c800c134400700c0300544c13003003003070304c00c4003042300c03051041c1404001d001031007102c0c030f100140e01283c03000c80e18810000c00f80c401240b004e0804582000c1d10780d00c501004d80c04582c0e0014030307480441041012a010811380e0000c2a403e0304661 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 528764622 1250 528763372 528763387
    0x309030d1e0c03020a0f0b190209010906080c0c0d0f02010b0102010c0c0f021f0c020f03070e040f0804030b04110102060a09050304092a030606090e01140d03020a060e06011a 76
    0x7a49003910440c100511403081425400d00d03000b070202e2200e40e580041d01000f07800051500b601240c078156443d41a4030720508800d00c2490041c400c40300c607460141c5440c0c080502d00201141d41c004010300c00d454403241440900d1a001d000c0110414242c030b07a403079100290440a50085c211070380d4018080c110380c1440c0d000741069405c4050700c1911500823002a4510038140049011901030511103d41e400107500c4140c0349940c400c5001d00198422601c0200300111b181c00c06540b032081d0301440c0f000b81c030740d00085000204070b41e0701c41810500c0b0782262400c0a0760383d2500c03500c048084400f907603078880c1e00304421900c0d0b030705000d402ea00c0860340c0401c10404a45854203a920f00450246c80d4101e130382c90908002504601c000c0202001c2c040c2500c85448003c000020090140ca1042d000420303625000401d076019003003101816141040d4035031201c02e03800e1003004045038030000c1c1602580200c4090b140810400e014605110070504014007055240840c103a10440c01c080300818484414031208 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 528765872 1250 528764622 528764657
    0xa08040e22030c050a2a06020105010e22050a05010213120c0303051b010e0c090903030f16030608030a031b02010b0303030c0d06050a0f0f0b0901020d0c05030412050309030d 76
    0x4a0005400d86044000f080c1e00e440d1080c584604250081d0a440e2803203469149020a180403003104503202002082840d40c0794420b9007600e1007030141a211464402c0014000010031213011028041c20a0822000c8929144c03542003003a000e40907925650005801c0801c2e400c1030300544014100d01080b9050410181c4460302031480034000141042000552444627030010a94042940c2d00c200c02006001090840296950b00c0705501d140259542070009203810004000d4078406d80705800704507000c0c3d03544508032034016a4800c0d403000f0b0540e90400440c3d2030f032080028046540941d02d0014a062110350800107000da0b611441c03086a040154940903910b02009480e0041001c1c0081c2d03448900402c09200034202a401058100b0f03445c00f4002001c072450030f580d00c102c034140700c80d1041290300c840110702117103c0c01c546540560b008100003c0ba0901c00c5080305c503100c3c000c1c81640d00300b82c1c5940c0b80c0240018400401c1d281903001092fa85458541400001480f05003402d00c401c0c0c405d102c4021 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 528767122 1250 528765872 528765931
    0x209092203080c0408031303021903020102060c0f0403150c03061a091c060e0a0c0f060c08030709090c050403050c1e131112070f020c03030f0c0a02030a08040e 70
    0x404001007800883c070a90480d1040c4c3d0b000d0809503095984802422134100d40106180c48243d201d01401030140420204008840013a207806902802c800e070303100e1a4050300c0b03611510b03d40710b608404000c004042a106071044d4004400d0400100c0d505035030800050070369601c0d40121407132040c035410f12895010008110760300d2400954003c204c280c12017512002401c04a140070f40410b040a9440d18041408203000d01310620600311151002c3e12096440d01c50800c5000b03080c01b05112404a8000c11415000b4541c000d0f241c2c600152a16151001c450a541c0d202074120046240481c0038001c0000c140116800d00c60306803664080d8001035802010207070080c6403000d00882d00f86074240075403030007030f0042c0d00e41428610785640e03140b00b800041d5003450800c03544000003615510102d0700c114804034030841c4071940140194101000390000d1640d0382e001081d00105482890394070030041e2018440d4882c56409070326495100d03894141d001d0b00d00c0400800d049072100715980091400c2580c10302 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 528768372 1250 528767122 528767191
    0xf0709050d0503130b0a08011d0103060e010f110d0e0c060702150c031c0b041e242402070b180402160606080c030a0c050f0102031606020909 62
    0x70a0a40c501050a0490440c0b1400c00f1038801800c05071404205840c10704c00410600d24103070780307490a903a40c4806120f06248400f44440c0822803c900400220340320b500402e46607030240000052180924a8000c112505001c9203141c001c40401c408540304110710a0000c0c106020f000350042c102c2c42c40c0041c88038842c4a40c024410603141801c1d07000601c041007555441d00a03182160b51700d8034010180c90b2140000e07030380b80c50a02d0500f582d10a0f82d04113030055100760368500b200121039107510000c110107400341555a101c0c40c0015030b04200402c880e002c40308010103688000030034803134901100140b90701c043c0c01c02e0029540205e0081001c038180e0422181400108141800c031400001d00190103842070349140034244036801803503030900020b54882000c44000604887e0440e400005054507003481110141949211036001c2040c0d081941c4854140c03081481640d1400982040310f4075220304101040d540943e01040c50f427842d007000540180c00510400d014901500c8514214482417011034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 528769622 1250 528768372 528768379
    0x50306160203210103020f04060302010c020d02040f110c0606010201090302060a111204050c090901060506120405010605030f030d053303011517060c130521010c0c03080f070905 78
    0x4004030040c81c420b00550342440406220040d901c0c501c20444071880f01c2c20301050f4400c81420205548602d05031080c0e9003140e0381a1260707800350400341c00300a01101110010790304951585400c50341d01c007480c4a0040b08100c4c40d8007603912000c9a12038613191a200900751419607260030002004250001411076101c100741070b01080c07403901c00c281d03002103004007a81030503820400780a00c000c1080206807205107580649512070191b8807806000d00341d81845c0701c3c940c0c100d14200700750707104103080c40c1c44158064094000490703020b0b9101c001c40d2900c0540c03c14007030960804039580308481d05500505030004c00a00d40101000300c2c48410007003916200c41d403058103400490b0101d116860a41040c1c1c0041d4580c8a81111555512542c40c042443d10084003154040d40303001178103884490080d903040c007110801c0f880d00c95040074180a0600b80340c5804401c9110f4402c40c0742c174040e409024111304040b00341d60750100030f007880c6400760045501034144080a6050000c1201d1542d00c1005001210f2089 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 528770872 1250 528769622 528769651
    0x80a030809070602030403080c030d15060807090513020a090b030a020301030c0f0e0c030915040605071b120c0213110d06080102030601020c100c0812010812040e131505070e030c040204050306 84
    0x1181075140d031251812540c01e20f070410741c0382a0f901c0300101d8500200d4dc01c903151940595a0307521b08441c50760031030007100c1c1c2c04401c0e880346001c0182d0940c06132509003490305004441a80703d1001d00c04980040304d00540e80c5030004010b000301700716504030700e004280c040303c14441c050900100600b068801852807039950b00100020708109003c1102035040541d000c01040d00e401c10b402c0c00b0015080c00c403214404124508400010102c50045038114141c01c076800100010050f40100d40414219100340d0340310a2500c0c101004248074030070345210804003440296554103001009094a5640c0d1040b400790344140104003659802245150060744200c03406290310604841c00c0c1c40e0b85200b400040d0010310081511304054902c9600320341070340c5a00080307851841848481001511843c02529410202c1c10b000c41d06100b408044020b03998441d4541504001b1001210801c4031000c441410000b840c584124803030342400e1080082caa4070030340f0154901402e110200fa690134010302804110000d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 528772122 1250 528770872 528770887
    0x62105060601031a04051608011e03060c0e030708150c0306180402040e0f0109050105090a150e1f02030f061c170d09051e0a110f0415080a03080907060203040308 71
    0x14240400c013004002d201b0006800c005030310744605e440b0b114808010408140001c101005466140c000c080c8034080704071b101c035082d6036400c0050000c2c20010820311000d031143e2122a9028003140c0050003300c2d000f0303c0380c3c80001144001480c401340041c4890081002408015100c2d12441d44180e2002081295261a5440803500421030108003a80714021400c00c000803d034190048209a80104002c0c041034481a90064540c1d00f46000108031001500c004142d65286400c00c8041c2420304080e6140c4c003210100032007807100024189482c03183c1c00002c00103140380c164149030700702e141542c0601e402d5407850001e81c80b070b149030f0074082c2c14084100400300205c0346201c1100c0510036500b1085c0501040f0f4035000e42d5070501025810015000410100d94404001071000021a000508a42d100c42d40b5400d000c8400c403003c1c50380d50001e84513402d00981c00160042c1000600080000b407214000358100242100700c003625800480c0c012070002c000d010f9002007941c06580e001100260755500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 528773372 1250 528772122 528772151
    0xe090d0210150504091718130203130308041407090606030f0b151c0608010c0813030e0906030c090c09030c0a0f050907050403172a0a170c070906210506060103 70
    0x2950f600007000c940010020043d02d0303001401f181c60442a01c83c015030046140000050b80001c0ba081000c005420074040d001c280704400442c0c2007405115a0101645032500036424004242c00c01d4005644a0408010155040c03050240d60182c51400304941010180018505007464114110031200829035420280040c45032080032403546d1810800c00c0e40c0c0301c00650103030103080c0d19240401d1044000070503035045502d400700038540c5030390ba160380d4910040070001c5503540506400e40501c22404151000d48840000a02a851068080b5112807000741018640007003218017034041d4109220030132844154400010540d0812288071740b2aa5501500f201c4601443d070011b000d01e50500640f21034164201c2c01042c40d402c40e906c20403e10307a0b003140c4400c201c401100300c03442254448480400400e200d100f04400700c00c18031084030b181040103a940707450321a03da00080d4000c0e41d034034800c08c040c88030030321140281ca040b03801d80403071a000c940329a51203410041c09941030541f0f59003004140407 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 528774622 1250 528773372 528773393
    0x201091703040509130c0b04060c02060d0e0a0f1110050708030c070f03050403060f0b09060f0418110a091b120b060d02030a05011406040911040e090d021015050409 72
    0x401a00d4007000c0c5c0380280018032040641102500c001c04016004900780514008640541d142030f2a4004100d280c1d03400d001035640700003a4511603c0d0344100e00d012400040c05001c07100e41c01103541c081481d010b4204029003038200341003103204203960a8031840c001d81242c180c6466503080b000745a2245c0d01d000703c40c544c0703200d000e2004100350040182c0004054001000e403007924001c600410035040680c551604542c0e15528460340300e201d5000280f01860203480e4482503076006440030a5a09040d07024044100d082001240c20036103000c2400e07464100503480e10f000709a105014465414880e917202070f0711201c06110341c10801c03c0e000120a104a5400c12500204080d1006a8400440074100020f420644034070008038104000000d404891030069810b00030f004090f980745c18945134002000b003011400f500440c135010302000030443c501c900b031180700b04920320150032030941c0290000c8c18490940481a481d914000c80c1c5c0e40ca00101900709003d9907001d0b6800520602c80e428a00c8151 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 528775872 1250 528774622 528774629
    0xb090106030b0403080f0a1107110102151018050c0a180b03160206061f0c06090506070201021c0543020c01020f03030c181c03030c08060d020109170304 67
    0x40c02da6051104041d401812640701da5580c191001041c3c072000034a1046d103641e01e8a0440002c81409894007080c101901d864110b0014011a981115442640901c0d0b4600702d4800c03e07070b10f00702001040440501a40000e1951000000304620b1620903440051070007080007410800c0000500405a0042d4000407400391112083d4162a4500b00c25010303a4241190b0803c80180147d40c0030500030705085200703285902c0d031403050382c90300c0c0700d61f00f004c0340d42101210041c1ca480c1c1d02c41d4075050100340d0500c40d860240324264005030b51506501518180b00245820100040d0f29100c104200000510020018031a0b400e455850780314a20030a2002c040000f600301c02c000b1180384041d00c0030368000901110144080c2c007034030b8100c051503e1050f264001102da101c0741110422040030344150b154000c0440c168000d01035140c240800d94040c81c064900c000c100c1c0800d50780c41c0d003207060359004182103501503422900855583c04a50000304511103c0c4150450901100e01d400041c40044c82990041c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 528776978 1106 528775872 528775883
    0x2100206040209011a1b060403020105012414070b090c0f03121602030a0c080a030806040c05121812090a0e09031611060412021503130b09010603 64
    0x24100f110355105a805c0208080342040900b51030114020035a90300809280c946450080c2c211941a04080800c0101442c041c020716120a00048000260b140150034110f1002c01d4117582e010f0075100070611a0380d041040a207180001701e50302c103da0211100b00d1103055403424940c0754000b10b11036541141c820451200c100030102c4040c101c507480a82220000040394845200100254215441c41c0e04412500028164403480c80c41e0001c10450301000101407901025106200700060040311580c0c503800070310100d01501c113040f103400020094030107000e8080c2c2c10b0310b00e41e848904941c1c4100413080c00480c9405800c0c03602c610036074500c07008518003100040c00345108074080c403080307412000480b43c018013070716054094001807000c0325810003610700318410040f001c8522900907110010034402c00c8140c4004034407480001e9000201e0001688400d072545002d4a0282c2000e0003 = true := by decide +kernel

theorem cover : BRFrame.Cov 528597122 528776978 := by
  have h0 := BRFrame.cov_init 528597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 528597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 528597122 ≤ n) (h2 : n < 528776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
