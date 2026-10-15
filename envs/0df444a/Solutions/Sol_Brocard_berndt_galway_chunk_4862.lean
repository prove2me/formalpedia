-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4862
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:58:46.229412+00:00
-- url     : https://prove2.me/submissions/1259b202-d578-4511-ab4b-ffffb50854aa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 874280575 ≤ n < 874460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 874281825 1250 874280575 874280579
    0xf040309060c0515070c02090f150405060612071803051b041802060906070209090120040f0b0a03061502072103211b0f03061a070311011b050d0b03010204 68
    0x20a44d40d800f04007400704003182c2400065012032245000342d04140e0001c0070351a031820704040070045458150703001b60006a40150200c59802c2900859026000c05040e0614201c844600b422200b007000d40030000f0003400424105500040c0000715020354000c1d409000b140c04949545804a421030300521700803070034500c44545c1c2c10039526a007515980c0507580e0766551100c3ca0f0000301c044c86844002948560582c0501c10700f02015448030244e07007030007031012040080c51413841c0b8a600a500c924030000038054810300404100030007034449082d0310300b0045102a240d24403154584d0349642400700613405008100304003c03941d41804128121025a0014005240c40080903140d040d40b03951101d03029502c0303070308100003107900c60b00061400000201c074049404030010056101140e609001904050b0f02041200c1804080007a0404036491070345080b50583d02612001090441c51840c0c0d580d40c00c64007034074007001c0343d802941446e50751840d0390340d00f01d01145021581c441800d10300070b038418041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 874283075 1250 874281825 874281833
    0x3010e010621111b010203040215071e0510051618062f0102040b12010e070c0f020d050d050706050a0b0a0501111f1b1718010b03060f040309060c 64
    0x9100307a40945060200e8401440220701141d032088800c5004d4202668491400c800c00c19406580114404c640d81034490751090700214050140ca600035064401140c041e540c0030501c3d4144940310b41c4120140e5034000510b08100d0b00701c2d02c086445100b01c4000c91240342440f9801005140090107210f0f01d14507040c10000020501d88a28400b008908851012101c4910482030a0f8100c0c20014000790750f99601c1d0311542980340c020101c03402d02c2003003c0c00046900303a44062414440c101507030320401c0c04601c40d1207000740c80416a500ba600314055640d0040810403d205102000281b620f805130b84044900e40b0900300d4400400449c49140341180c0501d0903a20f03540d560080351400d00e00041c00e452024061400d041d0b6145a000070701102c1c085518170000c403600600c0030301c2c00d4542c0321850307010b4456003520460b800300ca1042500c06040000b0310503c6080c1100e91220302c084000080507100340303000c02d00d8a01b017954004040c051a84c100170030194000d202d00c1c040c050501e4590740311407056403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 874284325 1250 874283075 874283117
    0x1909110f1504061b050123100e0a0b01050c0a0c15030203090c011809021909091b031a1503060f030a0b130809030a060609062c2a03010e0106 62
    0x40d440070400010008000c49800130007405046400800810142818805070340020020707810300a441c110700c20000b20020301544d000d000f2900036a007068040c1d507510445c4002001e00162250500100b070200c0f004450b0700300301c4030b5080c9101e502030610740c60901c440004130000c54840e9104240c010000c000104401007a80a0680020300301726440c01120a0028640307070481e041610001d10216501a803551840342c0c031a8210916254000d845840f0303041131050360099040301c10708103c1409141080c9100354000c05800e00401c000701102d05000c80041c5107401007210b208100c03000402441503d1600781c17584003024200b10001c00d064241d584d10000c07502c000604900c08413460150b50000d210b003a030202c444000004040c0e4a00c8481403400ea030007401d040c010701c400c1c18540300000c5100540d619009464101800070f140101444a84401b01d5400080c040014140191012180c1ca400390144004100718460203a03207960401e00c0300040701c041680200100b20450301e42d4001c1c418020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 874285575 1250 874284325 874284329
    0x8100b0303090d0f08120f01091103150f120606040e1f02031e010608041a0114040b0f03160905060108060f060702010905061b0111040f0501081909110f1504 69
    0x43c800d070500a40c00d0900b8120403151a40141c1418000203e42d9580032075906050312941f60840da4400d2a601d03200c5007402c4440c102d18202d040041040807415400c3c514136080b00a0700d0007840e600d4030301034840203c0c86802408550842c0d5601003000d010080c98640214000921094000e28036a000c9441c40c61301d4503161030006050aa001000ca040580502501c5046c01038070030b080b8031196540e500c0140b428000322001d4520001c00b510304c0180782150f20705141218012030180b14008401030070400184802d88c2c241d40d0000c80b198400352281ca045c4812140c4614100d04c9060b441d06e001a030005507a0010981c1d410040e044d41004103c0d33680d005000c070031070004c2d40d102d515030400e40300695016801d500201c1e44240c0102d10070801c141e100c4020407004100130700074000c03030030401e0340740303099010b00c1c01461b2010141c100207212951060074582d03804001e4403a034200401d42c1184200c00c488554101792010600079031100350505042d150b964000c4401c1d6140029400c006a03c6551405a4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 874286825 1250 874285575 874285579
    0xf0a1b170a09080a080a0e031c0f020f010615020d300b09090d0f0e0d0303111e0711030c01081f0e0c03090c090c040303080601141308100b030309 64
    0x21a80303500d010712070350100b409030505508803810820141004c0005401c003a44480020308800300c207824900340400c400956840000d004044450b40c0c1000362000580034954008611403840e0a00c0300c0b2109009250040800c4040170045040c0315800a082a600545040a006114800c0f04c1c0004450304122100c030301100f02c8564510910510301c002c2c01c0010f0810f94050044418041042c80216850001708541d807900b130b660300380c2e013041640e0404002210650087c00c03c006080441c1c081d4002c402d11541841d03503140f03090703040d542d40c00204401581c00d01110b0b03800700b00c0300c0400c00ba00300c21140c14501107000b0180c50400400092090000600350044002d240078919012103000850101074412420061014604028400c101d034100f01c604260601c01d2a41e01c420360f090400019009941e106840340c0760500350346040e6560b01014018504000749814105100082200501800c07540036004d11542c81c41c01010381d242200c0d038030140364101d1410f0002c6806a4000080760114441 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 874288075 1250 874286825 874286827
    0x60c04080606040f02220e01121a0c040510230405030a1214041710020304030507060207030e13020d06140f01080c09040603050a0b01060c030804030819020f0a1b17 72
    0x1013101c25010740030358112003a502c01100800056884411159010384c2c55060b0345500b541e0b81c8481c11180240c4100c4040c05a40c0148403843c410303a15024016441001c10404a280c240c0c3c0d00c0100e03040070100b07d0303040f000903003007040f0071022081e0520b8640610711144502e4109410000001e8640c220803a000f01000d0200b80c40b00d65160050344d4000c04a42e1700103075130380c96660703a0445034088101d041a0021301c0c000c80c12001d141a103a442501d00031505070341c0c0c0301e091150b50341e240c2e0000d40c80810b098003844000890303000c103961103504120041c41d1985015803100114010401a120369030802018544402070040583d211500200c0100c1000d1920410035110300b2010101403003003900340c0307401504000000c014850300051004078280700300f011a001da03030f031914110703002a03c4041c0180000c030740341c021a000c00d00c1200d030359411641c03a00800e02c00746981011b44049034847d07901040c8480f03011400c1c0340700e9034200c88603070b004a000f080c2002411103155504101c50040d95141008654 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 874289325 1250 874288075 874288091
    0x6130e2a04140121050903090315070f051605030d1a09010e0a243305120403020f0a0b01173c301c0209011817060c0408060604 56
    0x5004010100c0e80c8411300c0c010003203810266045a20703a840251854001c1c41200c800031a100280d141c5140b090602e640e41d0300f181c8082d90012152039001c018440c41ea22007491049020407014801803869410b51580002d00e4200e0241c503502d00e01228030164030603180c2e000100a1300c101102e180d68000184500003e40000c015200d0321017400720311070a214484201004941d091503e9800000380090307050355050142c44840c4a020012005c944400141082c81250030700c03644065041e4002d846070056409811920800e14a0b01800640a581c81c0c22404010094a904440480701c4040282c0c040c00410008502d046211040d05100c0314000c44541c29540b080b0440b4600000d110006105503030540c49081c0b19019100030500400d1003020701c1e035010380d082208a00441300040005c800115800740c5101020303000b500b14040d018117100c062803810116204110718031000d001401c41e151030710308140b5555490f200000f0080d2030440d41c01c0105000400c000100e80d030b13004000b10350101c0c9540e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 874290575 1250 874289325 874289357
    0xf0705090d05070308040317041406070c12060f050115022d0a0503030a0f0c23090d060207110d08030a0c051c0b1e010e06130e2a041401 60
    0x1d241c15001c1c2c11802656004000c1202c0c80c402801200d00401e42100070a034004507540c0c8034400ca00c100c00701100c031b202d600c0034141802400380850f24000d01d00007440d40d544010101a40c0817080c030807104030b42e9690100325000e038248245405017075100380480c00001e5070343c00a50b403a14400e9160540300340307001d8205c0c44042d0006d445544002260195201e1070b089140c401d589400c1542c0c0c5401140c10040015031480051041c0c8510825554407615103d5032524400380048480c8014404500300300511110b03900c2d80d540c070b505d54038031130303600107903104020b0800d400315410108005103d0320030b55000301d0201d010300045c0c981020940b81c1c0002c169110550a440e40e10440c01c0c080405407072a400542d0a40e02507120403410034042c0c070a030b91555100c0b6030403089100140703006408104110716266543c20303c4400792404003021010515001c0c0c840c00c0c40d20a04104483e2500c0300121844900c1814058228028841054518081c103150030460001c03911009818050b04200c070b0720307260111403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 874291825 1250 874290575 874290589
    0x6030714060c030a080906090c06070b070917030703030524120705100c060c020607020303071206031a01051e03070b0c01090b0a0c0f21110c060a230f070509 69
    0x42c410900880f83e9801800700081d00c0141d0840d900d01850140c1000180c08c244081026030600c1c400034415460404941d69108400502511041c10403040c07000104110301c50313442000501c40007c00858072005940b500074251100200702420604800c1c00040d0111300c2003007100a0103004481c00c800c25440d2002031490103495600c16944138201c01000851146c1240068848500480080c0428442c4460513a80d0302e4060b0b07004070041e882040040c01c070a110f07510700314442c500c1210100d07590766a611a035080d0008a5061000e0800000c01000340f0710f0180d681c903950010380d01e4440910303240200020789441140c4112003c1000c00140c48002401c20340c0f14103989035014580700c40d241032221002004291108401c9c003c120701640d4911540d01a0014140c0349031280904040700034122400320180c1035842d0842122803003442590840c070f8041c06828410210400300083d903640c10406187c0c501286112a160441c8500600203400d926401a55101030710381446a5190000c80215003a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 874293075 1250 874291825 874291837
    0x307080715141909030b070c05060f0a060e0916080a03090b0702300f01020c0601031e0f03050a0f090303120917070c0305010c0f020a0b040f0c0b09010908060603071406 74
    0x40e4180c1a001d02c083c842d00120034806032030088624501d95910140141d8944039402c0b0003408c19804100000c41d0204000000f5900107003980d40440d03c0d40d90350b4000c00c0d98140a540100c0d01742c11050001d600c1c00c2403241c01500501c071f840300030030a424158401422016050040c546170800001d00182503448615410018005051190388035507488218411540d08201b4000d84034043d05d0b005442e107001c1402034843c1840b20304090030403a407a65940038020801031000d964441e641d14050b00100306648001079007a4066102c02c1e40e540903215009010800c07440307400d002c0c010302581c1400460317030085289020004a06000a200c80c141c10860100c0e02010000420305400290003070801c40d41404440441e80310340005c1c420030441d10030556100c01040600d00040c0e00100300350340882d8001c0b1580750000e00a4810503c0501503440300f81c0141200d82291000190010b0300341c505582c012500b00003014024007400703480c18118002074641109125041c1601086414142143c7d82c500c01c8400c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 874294325 1250 874293075 874293097
    0x30503150d06020a11060106120e0c040c050a030608070303050304300512060d0f0b04140d08090606010305010e061e100c031b0305040b1b06070806030708071514 71
    0x41c00c00c0c010318100c0b01030340c0401091000116400c405807400940040d210341039034190f44481140c2032a1114400007045041441c0c1003074840d0380341d0030782a910389100d44c510080041c0e0303c1c290344215046020301a210030f58000801c030343c0f19000c1040840d85c00001c0e290441e6210b90070300840c100c0781400000c02070703503200c0d136400d402c181015a000c4070fa04400102040c00001c401440190340b5482004030080881c1d0000c0c1c90500e00d26440c1d400141805a1590f1003482031b185c0c0d00d580000381f8001032601415070035803070110302c07584140454044200301550340001c003403170b05100a41c100100d010320705a001d44860301480b166401088400703120851509501d070b0150000d003100e0500800240491700c6490150081281c482e50700e094001038040c5140441c2d095100c0c10f01c0c052800f01e5214256004200c01c510001c04220145000c0109018481c0203000743e644a803c142401e00030503084c4007a540c000c485981c080d450800c50341d661100c410000001754107010001c03429041c401c94183c0718080d2401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 874295575 1250 874294325 874294339
    0x307240f0e090a0f0f110f090102030417070f0806370e011410030b01060819020d060521060c160b070201090606060f08060d02030c0a090e0c03010903050703050315 72
    0x4298100305511a2100504c0d01c0c009110307854081541d4002c4404600940c9940f020402010000308071601c01006010301c188100e03880c0c03da84501010b0080341110301e01e0b10a802850f02000a4800b18001c6006085510702406d5103042455180c1e200043c0d100d4029285a40e20503a0f220407898240f40100c528801c06040c0000c80f07190710300328000d1000d15000c0341c95021007004038255895191070079040c2e030f6010b42010340340c6e400d08506594200c80185014000c01d03030031412034048103450010340302410550b0000b2030018103140421180d00c02c25210305443c1054079140481f04178000881c140c10800c04d0055503520040d1540d00c0038840341d9818042c140758100d20a010300c42d40e0543c004424103001d4030b4100321071a22050101d40c4460440c0b2054000381151020034030f50319202c1d40351040d1a01c014100d030200e8540c140822001c00480d40180c03800c42d61458806000041445819402079044000300882c8100d590003800b140a0001c003d0104600880007800120707000d120b410300600e000b0450 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 874296825 1250 874295575 874295581
    0x15010201020c16030c081f0e10020c0a02030c0103020309070501110a05010c0f080c04140603070c051b09060303030121110d121205060913032c0307240f0e09 69
    0xb4012076100840301041c2c105030020700500040742203503824a6181c01f1550328070520049201070705186d501290300e805400c84400c408180e91004052081a1001410580b171050041504112454034204d051500400420843d007001140080642d842420052030f0815403a64981c68660304d244010400e42c0b9080c408130203141c010750303050728440403503940144681e504540a00507014502c200e1050009a0301d80f940240703084009150700100c0b5280803904480c0d0354a80c42e18220720b22654145100e071610040000d0f003840c114280d80610150003c40c42c0d94904581d940c6850035815040d4020190500d021040081c081d0285000c00001800c0750082c1c2070505000814214400e100d401003000f100b10407004290a01425214410045c5a20b00598542442c5030007031303100c02c004808000f12064266001c9404001080c00702103480c0029140d4031410040c986000280d8001c2c8074807090f41d050f2843d1490b4401588200980240380c41110304441c008181c60325846030a0b40c5600001c48010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 874298075 1250 874296825 874296853
    0x9080d050a060e0912190509090106030b0418021302030403050d0c0806011b0b0402101404090203010f12170708041805090c0d03021e19060b0906041415010201020c 72
    0x90820f580c0903040215a035140ca030710b50781c0c0d10001050b1380034421000340117001201e0031010101350880118203005280481050004290b03582c240c11103c042039641c05200114242445480450b415035000f040c007005403074001402c4090712510302c03422990000001000c1520840c02e07516030304403103401030088510b011406001c0341802c0702c2150006602480b40e426a5449840c1c0481c0b042e042a00c040c03180d1600d4080c40b1030081e0080781941480321012548242801080082c8000c2251250045e20b82d410b040042280b81d40390741c0a400c850791000504000301d05c0c9080e61001d89022112416035400c22481d0008860241d640004070040541c3c1113050041503a030084c40c0310314031003c01e4803100c5541204100041c00c4009010f0010390240200581c0000c0580d25030400d13001d40800c442c2d151124604144885034229004c4030043d40740d076061501400c01416968000300c1c03c071010320140d20380c0c0c4010147c07107000070480038034103454101d17180869000b941141c01c40600d44040c4d507903551071005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 874299325 1250 874298075 874298081
    0x20a0212042405250303110705070f080708030a12060302040615140f09010c020d0b07020307050106091b0c060e0d030b0a0b0307050f1305190905161209080d050a 71
    0x7541003854068040100300da80303e041102d5160300e041d00190391080c141e154074200300318440300841c02e2550702c60710b00020094540c094440030b8420002050f0990a04105138540045136104024030f40c400e6000b4420904080146c070000d030341c640b0b0070790301c1660b00f0b030380703000190119030310194100f0310b80803000c070b0200e48e0510001656000781c3c50303811815090b1000514644140780d643c07100301800780030301c109170341c81059900c0d411400100b6608004540c1d0305d40034003d03a0141c0d000c0c809079000080d45820401c00b0b021300c1004115440c020000d1300401c0c88503840e200c988441d42c508102d004130003181000711035401010003134001c20450300c0099030040040e0040c488a4052480b40c3d04c2c1340000241d081c200400c4a10890507561101e04150400c1426049500b090320b000280c035800035000f047c9a2540a540c00590810501aa000307501e015440000c642c00909085690154030040c007030310503080344042124203240180022003010368200701480e40540503941d548107042c90180900440a60 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 874300575 1250 874299325 874299359
    0x3f080703150605040902091f03022110050d0303020c0601081014010803040e04080c0307030302211303082211010305010501050412080a0e060c1e030702090109020a021204 75
    0x1850070000c1440d592050405003107503200d0000010003c00092015501d42d80240100c080041c000390410704a82d02c202d800800204260000a0360106031290303a25481303038520024102e081c071041407500f000c072000c0c00c4804a034001c0d01e025400300c542e80800c040c8658103d0365080e803441c0a0ba809543c6030484262180340c03400080030f000741050b03004442480b80302080ca048440c0e0f04029864a440d016403c1c001d840700a0094640d001d0a008103a006901480104907451080c0da006a80e01881c04108a6100f03e51034400640c0280c003040080f00003195920341c01075034141c18012401e561341c0c815443c003000600c000e08801c10400722960b04001510580c43c0070000241ca0901190303072039000442d82405103102d44c4002001c00c00d001030104004200928204006180040c141000b800c089a04e5034000c1302440380980c02020305820700702c80c0100100240389280c003c0c5280c031106800040c440e190601409030100da000402e4410b150003000710440d103030b030042c10998035035648150701c0490480035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 874301825 1250 874300575 874300577
    0x41103101409030f030f0402010e1503240f010c0804050a06050304020a0806070824102c0f0402090d0c03030807030e06010f0608042604213f0807 64
    0x9040440d0303501d400402074070080c0f981c0845140c20b50707a421200c5280310b1000790003230f41071021088080079580ca07001c1020200b150000341903079072414044001c0d400144100c040300300000113000c0d0603480e5510742c11070008080c4246002800001c1c14200004144210380c08517600c864212000903150345c01c10099403207030b8000c4036500703050f46c2da030070a50391504021502840040c10800016884420b0780000c411400001850003140c0081840071682d0000201e802030f01094080703080c0042040907030488034003812400d501d0180d0500b0a00450000d8a04401540c4942c0d00403440c8503054852418a001c0e072600400d030182455524280644109000d5414000090421019003e07034000060241c1c12210b11141250400f40703001012200801c000d0001c0304d810440b8203c455410503910360281c9a1020001159900c03880d2126115851012101d801114142e000d05440450000c44910026918101c188804088840e00300340847c00200400600c07003c8920030900300c65404600c1e03510031005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 874303075 1250 874301825 874301861
    0xc08060a0903030e06040b06060c0102040b040b0d0c030603020906010c0f0209150a0f050a05060c01020c0601080304080c010201050c04050405180d020a120206131101050702120a02100809100504110310 88
    0x3440344c1c10352544d0382101c0240c81100141d000c100c090070304070002c0010965100c0010b0a181d114181101144c7c025841071051500200301c2402005144c030656400c117103142000c00409286074081000303110002c14203418409540391810030302140c02544d5998a6000301500c4003450200c5a02d40c5e400b01070f03200a030003004040d10100d084a454040e403400e03114018050b981c0c140c904000c1110b5580000b2614419540038000340c07186920400010f03012748840700c003858445080c140e580c1e1920f8944a410303030441e03040100384a480900c1800700c90030740c0c030b003617901140c5a56902078524481e400c1710151030103031180f088580d806640c041031030300b0714130301c600b607682d4101d0018a0102ea44030402d07641c100e000c915112060300003130910076050783c8070001030416a04152441d000159800b441c500d900c0300e01c0e00b280d4441021450310a40b1005c01c8105800c10004a0800f216402d44c0e034a40c1104680711a41d07181d0202d01408007101c0000e140b00c4004080302c80a4010490010103482e00b00c280d50603001c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 874304325 1250 874303075 874303091
    0xa091106040b0d021c0905070602121606020a0507080706140a05090c10020115030c18061503020307090506030108100501090e0d0c021c0b07080703090206030c03040c08060a090303 79
    0x506103080301c0454001d80901810040340450110081d408103104400310001e800400403c2501e6000301040c041c081c4000c0c1c81c40070b1920324040c4c00c150003800c586110b03e1082106525031b0203041510040d49410810040c0c44124005099405124800c006400d003540424410708112003500039103a900e0503c400c9803120b0720340030454803e55100751000c0b4a81e40103e1b02034441c60030035441c0850344144510021031402850b6007801042011504181d540a1881d41d0034803402030640b00e4910490b030490300070031059203070080402000940c65182010540c00001003548580315800c01d07401b4180040030305940b560346e9056903a494075190f00c035100d428141000081c0300b81e00c0d840756005215a00c005420320902001d4101c4049550960403a4000c41e2082502100c12102e441154040d1188001c40d1083c10f04400140c4001c000400a0342003506000300080183c48520580b604001d244017080e440303031161b1816244a04070341c0c00101d0303184540010001e50f610650001c40400303000e0f8804000d040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 874305575 1250 874304325 874304329
    0x1b030408070806010b0f0306040b060c0d0813030c02330903010b03010603080d0c121401050108130f0b18011b1412010b03130f060b010f02011b0f0e04050a0911 70
    0xf0320902c00c0c5d155598090210b0800900c0b0070005691040b0000c02c00075070f0260100014050790071140711400b05a01c0300d114404602e400020b03840e0021801c400701d03881300c0e825a40003060002540b400a000b615084402d0350f502202c00030881d1010350601e83c503003841d20000000000c9401113100301e4829820603011802ca07041c188200c1c4192900a5421440c00503441400005408a13400315805c11404820740600088944154524400340010300c00c910751410000401c6050040c1614414590395903941c40000c100d240c0e51300a481e8007004082d40341c0d955030001c481a441c4130141c00307615400c1110194171700c116002d09003a4500d06403180752040104003845880d50080f407020580c1ca15008005121550074032002d503501ca00400d510b481103209958078206804494070048644a484e0803500403a903810081c3c82100c8103152008000c80c145a840f007148103c10904d0799000e2145404055250a03c540c14040d40128080d02c14001411b05415140c002c0030031358000d55045840000c03e0120b8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 874306825 1250 874305575 874305583
    0x14030c0613080f060a0507182304050a050a110a0509010305150603180601210206090a2c0601031a0409140d021f0c0c03030c05210714030105180a021b0304080708 71
    0x409402d444403c5203041a002205003022800c07041c00c49c40c00c00500c0452540c46004461003a11501c5c400f250f1400c00301070242c10750f8259032700740110720400c2c046000455440005c2e54660f460910700032a10740c4810312610362880100e2802d540002c0e00108002101010b50321180110032000112001e030307a644c1080c0e002508a00d003140c014022052400390152420320081c14200c0c6001b041c1c504025030300c010742803200d0103c00c040c424200344444010012a00d1200f5039500010030b007000c0c051190040c1558103405600100144159941c1d010740d400e1151503500e810405226100316030f0907052055001e540c0d0400380c0b6981d0480c419002203200c540c1820700a4601d07400040d280c4008001180d138050b0042c25000105404111040c001c12007030300342c441980003103140e5000c0d84209074144201e0084c51040b90000c200d054000030001040030751543c40034940c0000801135036130542d494802c0715001a03c1051030380c1080b5200b4200360ba18900e000300007070080b0340c0740d03200b102c004507580c8980380d8035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 874308075 1250 874306825 874306847
    0x20a05180a124b0519030f140301050f0402161b052419051306030207030206060a0807060e031e15010e0702060a020304020d020a0306021314030c0613080f060a0507 72
    0x10307110a03c03480d4842c0c0200300c450140040c840c0c02901c1540366421100600d005489006030001024140a070741d0310b03504810300c44075005901204520b1076061101298890040d9036140c0d000710b50020b140c080c20491038440303c000b84e03400707408410b545140d110002e00c0000c7c107009980c801c5803117942c50340381108000030b411718456000548600b8a5140e00c0a240c154130581e010380306002c820010445100100030345030f00a400769490040e15200310b801c0003844e014009140398050001e003141804414000600d4808440e840c0c5061030000a0100c0401e003130205103200d4540000c1c486204040524001c5896a00f0198240e03092100d41e82e18840305809400c240c0303002c0096081500410220707429034000710b60080c00030b40700c503540300800d5000c80c7c1400381ca42d2080e20119800b00b592204c019080340204000c000e0000d20b00ca400090500098070b4141c0d441c0f038140301c0c120024a6003d5603443c280c151008040c45401c0d607040e08040d20400740c81d0341c0c00311404d4424500d8400004c46482c002c40380c0c003076 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 874309325 1250 874308075 874308173
    0x20415110606012003030112110f010c1104090219140d03080406090201141b010507050403020f040207030e030d030e0c0a080d08061f0509030709020a05180a12 70
    0x1c5552542c4005554a0310150229050018180c044001d41e044c204001d41c020302c0b001c08101c048e0f00d620f00301905000c000e0b485480c8182100090a00c0e560b03800714007503c0046d0400755592001c107401e0000b4001317282244000b9002080c55045000c880601c6c010a811640b525040303412900b440070402020941d1484000e0100e80410040b80126210350320a804441c4181003d42c81c1c094100c0e00d00240f50400070f0710307800380c400180c28403034803040070301940c0d40081d00c6062641c01d150455000030a1601c80e10352040c099980401c000c414144940440e00c1c10050140540c0e00308440c401006018280da00c21040c7c09200d00c1421304007a013000c1c1c0d040c40c1150980006424400390004044900b01c2018217010360001c00c44c00b201c101580b178110011424005900c900d66240d03002000c0c9424440c15034404012f40d4414040103507501d03004402c6a9090030300645c40c2c0d00102e0710b4000644500d132140c000b40c040c00160542e04040000c241400c4280a081e6843c134548591400c0d035050360400910503002d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 874310575 1250 874309325 874309333
    0xc010503010e15090c0a1806140f160f0c0506031603200301140f040501150f1107031a1503030d020a0203041505030f07141803010f050a02041511 64
    0x24111210b2034032900004060148000c0056860000305008010303228a162268001130300c2203083c0c0c00907400100c14929400c00c07603c40707161107009004081c8a801c0b0301d02d42c08000401004820116040f24202c3c5194100003c2984850400345101641c0a80454503620704500c08030f560300d40641686c0c0710790440300b54440f52030304840c0202c01070f0841340f62114899503d132001040c004a441c01450291041906581038410790340108001c4071402c2d25201c1c05285800014080d490890700c1c0c1685084042c200b001801a5581e4100c0d01103a070b5044080f054000c8207000300400c031003680b1800041805c0c00407070038161940c8004407010301140c441c2c0b80e4154000c01503910442d0054000d840b80b4000383c0156402c041d40c542d5890030f4131414041c000b00041000082103181c4e0785141d6000d40081c424a481c0c0019004101481c5091061040f8101348494081c402c1e81c3d1075400350844c10990407012018007950402242010107500180100c5148030815016140c100b88990501c900040e04c45000b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 874311825 1250 874310575 874310579
    0x80f0112140c1503061c05031e0c0601080d0e030c090624030405060a0c0c0b0f2502071809150905010209030f0c0a0609050105030a0c0917031b0c01050301 68
    0x94040c0001c000240d0340601495114159943c2c42c08003406541103010759144e43c0b4a4984200180c0d03403601075260400710354842d80d0001165001040c6c031000d0f8000441c84260140c02032080000780905034400300c09104980c008035400d800031546580782e4109841d00d1440c100b15008241c0ca0302c04071510b468001e0a500d000480a10301342e40d5900021544a01c040c070007800e41e10751082039034011030302a2040d600c90390500c4140c1140d07202e41707465202d01d45400900c000c1c0c00d030381d074000303481014001c68000005071020405814103018190011038800321090071071251142c1c065101d40f01840b40e944141203400c10380f84060121300421042e00e60002d0004075084006003031100070191404242c690350350900a0b28030984041004002c2d110009008103000e52240f01004114465908194100600c0c07020030009a60450309480e002118060007080030b06200c00101c40160303041d0f00006a451010200c1d507040d43c0c002c00205070a5502d5882c15101c1391492103156510b140b95040355000507420801 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 874313075 1250 874311825 874311833
    0x31c1e0c120e0f04091a0a05090a080304060f020d1515020d0c0501110301030c180c0504060807020c0301051003020306010b0c0a0f0c09060605090f030706080a0207030c020a030b07080f0112 83
    0xca003042c10006001c01d0050640c1c83c00700d0221060f00104640b041a45600310b40f94410820140740c0c04101d40e6030620191038007240c1503445040811000f048030902001040400016800030407403112020390454443c12002a07040c045c00703420642400328046200081072007007030a45c0103600400c20760010044400c500d902244c03003c2c030104040d604c5550310281e0b0f404480c5600c0065000710300825092240e43d041420601003881c065800d40310041c540b04e400e1700450741040075501240d8590812000f0750340c0352003007a81842001c19644d507055181008102204035110200c109481c000d504035580d0380e0729640c085000e4407917402c0d01000b1340d0042c5000300001c1ea40d0000f8003442841a07a0b10010140c0c0c5010420544600ea041080810400704070006030381012000361000c5503086005000d11440d01d00c0103042c0743c001038003801211340c002480005040c00b4215034600c040c1d01410320700c00710351b8a0902138a0389200b0740c0e1030000215441c010031181c03c400e00880781600c0d000400070907981e00071381e1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 874314325 1250 874313075 874313087
    0x402070c05130b36040c150f092102040507031e02130312170901050415140f09151303030b090f19060b070507150c0b010b0702031c1e0c12 61
    0x1980f0002031000c1c1541307040f07059840f001a03020300c1c800c03c5030b0304055080c0300c032402e007540403028050300b04007640506a00326a80400700b101143c0c01d000c044c0704890034444603901032031101c020103500141000140420b407030707150740036000c2c40c642d0001000041008000210580c0709680025541c0341c1c10040500200300a00351840018495046c59600d003080414211070003002110441c540c1d954840c100402d2101e500740d855800b90181000f0804d100801800101d524405001c0d00b2104103410000303912240200301c480c0055110b60602c07078103403a20800c052015503840e641140001e0403d816101181424801d05014800c0d101ca5010f60380d0303903401c04001072000881c0700302c00f89446100004000c05250020044280180040d04226007000103900346a51040107070700070050011110008500c01e08035150660703400b0b600c050340d10a002e000017450a40700304880c1d8401e00302c45516815481c1c01450003601e440800c1e0b281c040092200d03805444c244840f135070107000200c61070302d041da81a1040d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 874315575 1250 874314325 874314379
    0x30b0c070b0a020f161a010914150307080f1b04021603031503020406060f030e06190905031e0c010510051806011806020307050c0a031a0c090402070c05130b 69
    0xb80c072085c00d0066061155045011a417002e4a8150304814990110050b4031401805010318031428044104804001c1c500301c100149906000e5088072071007074403a5001c1c804880100010350031140d50940c2d81b8100e5031955005100c055030315181d209207206d107040c5402501c01078a44140790704015142900e05402804042c01e0380e00307480b481e074540400141d0300e6110740005440c8030b903228070b0301d1110394101400321116515006080d41c0014204001d450700c071503150264018011020601155503d01240386020b09890301c030300508405010300c0c4a441c032401a001400001c0c00a11458680c4030b060050f1000d2800354a030001c1450786550440c5080b00080c031b401000615103000c0004504103c000c2050507134000c00c00682000400505010341080002c0d40c507142191000200303440c0d40d03625500c1c1610207200342400d0840000003030386042c00700c00361028580083c00540da1100c030380c03600c44044800ca00869104a50101403510304207814403c40301c00c500b000d44000321084800c104400d00400203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 874316825 1250 874315575 874315597
    0x1209030204020f07050d020c03070614040305030f0306150c0c120a1709190b070f050312100e0702030304020f0613030204140702010e160b090604081501030b0c070b0a02 74
    0x400000005859500c01481d442c2c40d02c56499071180c1c0c0700c1c0740c19814104544a02e004640c014803a60740301e0b03900419030004031541410030b040405050ba404400e180660790000d0080d00011410208922000c8011407140d8003c50f900e00142d8803d80d810344842c0190848901c40358081032610009050800441044100301002c58000c00201e554a418900303880c1d581e6032410001103145180d50802805000050049009141645041429240307a50181c2080035005aa1501020041c0311040c0200d0703070342810b100c0603608185003006403a400d9409500c685d05c4a10000d0000904461010068078015580100850064802001041510303007008114444a584c0e8220010040c0c0e03441c403440b00b10301c0e59071007103410500d00003030b010b0308545807810600f641e60402d0509141d070101d0310b00104207983e880c50142e0307102c50301040402c2c00350041e90091040d40c8160920b412448c1c0e600c41d00b49048078402c004010311030b030350383c8000c040b2409041e6004003e042010089408081580c014150070110 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 874318075 1250 874316825 874316837
    0x20705191a0d0c02010609150b09090c070b04030207060210020301050f101e1707020601051804110604061d0a0807060831060b09240d08041401080a1103010312 70
    0x41031201046540f1070b021500036079500c802c208081c061340d00a81c03003c03a1a4003105410b0a00d080709010451207030406040c4a081d5541c000307044501c05806072122507401510303200b09881d00e031501a40d035134a180907100140c450940301450002c880c0c003c89050316400b4000c0f814114030741c021302c600c04100049442c140508074000700c0000107260b807499200740080c1e031201d54800950306450405d2001900040441d0071560051060f51561043c1c00e0540d50401101d010310341d26401c00c05d540e000c0040342d1310b9110100090010700190720218801d602801b4048045840c0032500801003101c40c2c61040d90001e4102c500304100c0c0303500411039643e1100c54090800a507003902520003001d0001d0b803500e5806868400000d1080c48414401c0c046c43c2034040c4d424a425040007500d000b134002d80d1920807500c54144500c000e0070368669104045800e944003141517191501c0d0b20400e07111214150340b0a000880300c00c0014003020042c000d404049000405503407550f400d40d11840f020701c03040c01c803820a10076 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 874319325 1250 874318075 874318087
    0xd0606170f10171219090e0708071d0634030f030c121104030309080d0512060310050901020c0c030c13051f060203070309060302070b010501030f1104030f0201020705191a 75
    0x71002006215140c41988170162007078800c00090301441307042d080402410303407610400c600c0e0341d04901c0c9150403030769500701416a04640f14000083d814800d120301e400000c08600c22500c0c9035100d1100c000d640254956a0380b0710070390003210710180c00031000a00020800e4a042c01d0903400399201301e112543d42e2134210150074500e10b0b0901941d42032581d00c40c481000050820a055010b0118006041008040c10741c482c070450004115000300c00704140341c0e198500c00700e019580c00f00712500e000312108105000f18138003100c002d4000e400902d0322410500403030452080341d02d00400c400d045520000c4c4441c07240000c8005200c0200401046458402c9031441241032001d030240048004000d00d60040d9500c0c60b0340c0c41d0017041016680e1101c1c2c20b16006100c10400a0200146030b0b064a0702841c00140841c1d400c58000003901800080750460040003d021050250a81a20855600030b07000c40d0340c801d03a68414040c03440e8100071b01d07030606151520184401c0303403d4417040131807101c40091941054 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 874320575 1250 874319325 874319353
    0x100f020d1e0e0304081b041b1805012f0118080406020c04060b070213021b071a0306130b0114120a0b04020f0403030c02060d0606170f1017 61
    0x1200040c0060030032141040c000c45041c028020414055119805141040e00e4503002c80e945030902030306101420300d562114905601c440d80318522140010303405944800c04404007034540c1710b10740070280100d2581103000c00d031540144292103001d82d0301d80c124030032181010500c4107954040030940015540314556815050104100c0c0707500c8901400d580d541d518640040a0f1801da51540741900883c20134404000d0290381c082640e52564041c1e5164074240300c074068580007031180c1000091881480307804080c11280000c0d604056a1805014070800e81c1142520705290000310364869001740300c41c10110000c03005030460001500706041454042c00d00550036107450b0031941c2c400c06c3c11a6110300300010341c0614020701d001030b94241c40c1185416841c41c0c401d049807003113000142c1800401c4207040110344407107007240c030b00c14100a02000400c0e201d1034010452050a011501c1320107164000c030349511400d1908500030460000c0c00c025151402c5240b001c1501c0c1880c0c40806400340d80c14500c944 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 874321825 1250 874320575 874320581
    0x30912030115090f030b0402041a040203070c0209130b1b0909070509180f0c0a140d0905060a0506031b01030902030f0c010f0503010305061308070507030804091d100f020d 75
    0xe4445018101550742406000904001d825400310b0700480c0313190703010030210390041c1400e42c00070340546010510003402050680350340d90910155403c2440002004040c552110020003494400c480719925615510040e882c40000780745c02420381e81d400d00200c1c40d14800e00d40e4030201910a10720745408d01425000040320307454200ca0240c0031480c001903070301041c03a0122010190f12101e980542d0035003032450a80c88201d1008203803c0b5803c10005121010900070b01c0c0701c40c00d42a2407040c4560320740501b00502c001e020b80d503004071041e100e44400b24030410128020b452282c10040c0091040e1411324401d03005440a0b8041903060643da14008400360702d041c0880300c1e4100d0a00700901d021145200010200c1105641d150201720f401c2c030042c0000303503010501e03980084440e4003407081009a4201041140b0900c1c0c0c0c001c19501c141c1c00000100513a800160048a4148008102013440d6110b50210051040e171201c0e4a6084201040040d104507803060800703003481800141480381e800705003011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 874323075 1250 874321825 874321829
    0x250903080d020d060b071101121103010b0403060b10020c0f06120a0c080a1a040b0a0f03030206010810020408030a18050d030e03160536010905060a08010b01020a0303020309120301 79
    0x81d903000921802a06614000c140041151402407450042d141e1551a815110740401d41d0400205158414100450f80c10030030112000110b090b0b034a5a480e140741507903034018842107034403c3c204001c4008030f103001010b500f90780e411138000e410702c0d0024908000d0302c404400c1c0c00e41e500075814170814282140d6180b1042c4100308135080001c0341810303100013909440000f41304904d444e040c9400281e49030b558807402148070760140e5011030304802c40c030001074030000720740c102c10342c2c0c3c51590a000080c5075001030681e049510346003d507846080008030402c240c1c8900d004661040e4010880218468428800c4d0480c0728004012580c2c0c180e10386d000030f4009000410140c0010390000e1456005241c02d00007009111810702c0c02070315503880d19011580490154a040e1194042c4050b9060b03c03400c8482d0b01d15416410024036000e560b11a82ea150041070140c03641401260b10920200301d0a80510550780f6101050b0000d10100171703150790072400f9510043c4904554003c1020202c1c01081c8200a140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 874324325 1250 874323075 874323097
    0x41818030c03140f160203100905070e0105191404241806050307151b030c030806040e07150912080a11120313032601080f01020325090308 61
    0x200e04002410014000c8922043e040c0710700c24208185000c1ca419034007215a10414176014441400181c00001d042041072607012079000c0c14030f501001009404100d60041d920042d1100d4416603c520070301000c0d02e01d0202031544503042e08024885400b0715080324511500c001c0001c11001c1b28a08050700b0703498401c2100700e0340c1d2104003007400700a00303e003070584ca405d00700102088034a00d40340002c2e503120140d02c2101c101c51740d00b0186c221818451142244450070419070104005c0062400a0405040c1c0100740d001684c0b8002149003840c0c18002d500040072410001c00d1030600305100011402c0c0481130070400e020400000041c1c224151079100c8150380038030103003a00e0f4810028040c1c581080c1940e80012900090408581098000306036038001000d0039501411004a1906503680907120143c00100d600c04080700700000300144546050704c2d00402542c030300d890310140c0355080c0d01050b00e0300c04038417201480d6080002a8a51504051042860a030340c00d01c2ea07a864200041d0f000841c290 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 874325575 1250 874324325 874324337
    0x110a020a090c030614060f161709011b0f1707151505060403080406120b061206040f020403111020031e070809280e1501020706020304181803 62
    0x120b4040d0103208035002060210015001d8400030342c001207142c41070301600c0201c134001003442d80792002c0c4841005c00169002c07051000e4444200008090b07500480c5d040d90000702d041c22028031000310708804640d1658132003644071554030f0f543c2c1c4801c50b54105c5803400716454030030b0041c034010034299010100a034191040000b04441034008461a81031160001c07805041d00b04800c000048900048800f00c810918014089100081403080500200608298000404201c0500d4200001906401650115401c016811503846110140c6c0502d20015100c168404403401c400c0c00c148041954007162490050811100031441c2d003188410400782c45442d900c041404825260014013012141d1207044640703040c820980c1c1c8000151080c5800c45000b19005009107610002040c41c0e46007403140f0019003202d043d12084803181000003160b807060160000034106c0ea0075400031070500c017074070140e07806185810f091894a00c40b2080a0342c481903802d07a00d0a0701e6100ca03080c640306568280c0b1903542e803 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 874326825 1250 874325575 874325591
    0x12030209190e070c0c060806010306030c03031e0912020d050f030a020d020f2d1509010b0a0e01030309120f0c0311090709141509090c22080d110a020a09 67
    0x901c82d8080041101e824031450340c40c3c440200b041e0091030400c851441c40c12414070ba0340d0900490190905620041850013100804020150009102c030101e480e44210300c0010321009408a030324444a04c034080f00500c580701d42e24094180302640c00001c44c041c0d0b0860f26030f160644600780c40d40d03000d0a0450016006011070f07181c22a418040c040944038004010254900740540c007030a10001e034403104074401440d2149400c0380d9824083d00ca540d00354070f002c0b103020b0300d04964064003070f00364440a41e21400b0700751000f061880c0c00a00e01c905881d00f658035029201d0030450001915030f4500011380714000b08a4102d03001404540c52100038512640312030b094038504c030050110380c00024240e0001c1c45185941480b00c1c00c0401e40fa800203510450308007003a10400018503655115503c43c1d6070f041200341c009c001c44c0c50010b00041544158a455a8031756120300e14412042c02ca244c01800029042404188051032180408608a11480e0140c80d9030a1884d4009022001d455120300c03030198407500c107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 874328075 1250 874326825 874326839
    0xc0c1b0512010b09160e032a1f0c020a0b07150c02010932030d090c05030d0509040b12101a12070306020706020405030304030f0b10121203020919 64
    0x381d0111215001d00900003808828005009400014012926100400d062036803841c440d0085202a400150946910034020b0405446014401404c02c4e03802c1e2180702d4010320380c00d00201b801c000103103030700c007501c0f00c40c1d1412801c98801260b0442682d02004421001c1520b0b45600000e00002e842000c5411401c10054420780a40c1c0d03d1814010540e4584858000030130190480110704003145c100006864a48a203128050300500701c9070510323480301161082111203190700c00322100380589030150500f0396500805980d0381c104004140010b0061180c65000d0902d0340140c3d182d180700400c1d00b80c00e8421001c9461a0010500d4040420f54443d40c400042c0d60038140e0800b16410262543c1c0040054144020703542c60341840000e085941c0015014107010306a41960040c040080540c0d0341c80e5503a041500d8220001d035000e03a1691501c102189000854550308411950200400c03038009186888240d03400b1400b070030303543c00d25408100083e0a1740e501403030b506c2010440c0721110002401d00d28 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 874329325 1250 874328075 874328089
    0x1030510060e040f0827090c0c030a03020c190605070e031605011404080a0311010c08060d0609020102010e010f02130b03060603040209040303060e07050a030c210c0c1b05 75
    0x1000d0000c00e07103401d5092006800e80402c15a100f07030408128030084103030b4584141280304a000c200e040d800e103500c552a14100343c036003191052004580c09040c6440d0081d110300140b00f0203035625190350040012581d0380d07000341c0280c074100058005441000c1c48a840b200240c07450080308030f070110750358810014000d41240b14010b00310b2080e001050080c0201c4c3d020708141c101d501a650600040c55400388103403a100048070050300a25085e0ba10820107894050071500c202d01e4400d40a50078004101c0001c1e00c50f800580c400c802c001c0c80c4854640050700c80c1c10003404803001c164115504c9180c0704892000900945554143c1c1c081d00695509504040e2290500035400032155400104144100c075591541940e400c2501141e1101154840d45029001007c0a83c4110070401d040c0c00cc0016035504071014003921b202d0707510309101d04042280c04558200c1001d02c848901c5001401104010040303500401620003107080085403c17945854861504c1c050354038240e850031034a00140140e040c054 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 874330575 1250 874329325 874329343
    0x909010902121b0d0b060415030507260c0708070516050112020c0706080c0d050403080709060e180a0b09010323160b03060409021306050f030708120c24010305 70
    0x1c00ea00b81150405011403a10484d9510071030300d9110200302210341c4c2e4440459000b40303550b04004c40110440c2601030b028203011607410011a148a04401107102050b038200f511703003034413019800c80d40da401d000520b545d0001c40301920102000d01403003001a108001001101d40400220117015240100041488440780d010726201401407196540d5540c0000f0a401640c1242c1803071001c0307075164400380e90355000d40b1890f28a2076040030144418550000256070007084a0b944080d411034840009070750180c2401855900032108442e07003258100642c0c2002c0d003105081002051800d00d440002d03034220007c1e001034541a0320340746034142d0b07602501103441c60700010360042d0140181011210164849510900719480030000002d4502e666079070081b5085580206a03042c1807921080e808014560707030040e60301809605c2d203042201d15000030402d00712130181c4000c2c01070100700d524610242c1c1005500030030130301c500e07940301d414a050703240c9051103110144c3c80d4100640c950709210f4034200c488 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 874331825 1250 874330575 874330591
    0x150e0d031a0a030302060606031b04030c090b0603090d200d170108120d0b01020106050604120605220228060c0605010b0324030a060203180717190503090901090212 72
    0x4400304002038011030a242e02c040c044408984070713604c403c4ac0e02448100d030480b002c00c034000020040108400c01c5001000c0e1005175030104044229241404441d02c020348141144d0b501c0400940007040c80380503c61016091848541c01c601044040603103807803042a90100429204000d2101510803486618010b21601004002004214403940003606c0303500e1644d054035031210710180059000350001c82c000c040240016a496a4521045042007030443c1c003265600d0504000c42e0303030302c1c010f000074001c0800034181d0103482c4d8250b5030811480d03043c800c030040c800c60031400c00110030200c841e14840042999880b10300383c1901529024080b66016048040040000c1c03091107420441d2012075800c0f51800c5012030b1303440154000007494594039400083c80e050000003002825242201a0051810100200c808030358031040310028110100c6003440c0c15502900c1070f40c0e140f101402c840b008190140083d04c0c50310300c5030000300300c1440d001d030010fa5203da0000b50007840b03081c1c41e0300026882454 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 874333075 1250 874331825 874331839
    0x1905090a060312050c240103120201050c0d0e01060506030a05040b570405010905090606250f030203120f0601140307030e011a010314090703150e0d031a 67
    0x42d070390380100ca004840d40038010042d020900400710710041040001006200e03250342c0c034442d810480e40042c4442400300300d40305001e80740850706a0b0300501a0714010000108170340e050007204c43d0039600a18a260203408259204d600000c1c0a131507410055002d544045808640c84c9050704091002d004003401e8006062600d60383c80102491110112204002d90403005074210f0b03e884030882c03000010300072110101c0c80f00d00c50403099120f640050080f42c3d0300b80c0390845c007103a6442c1084030b48d0360220b03803551f040101000703440d81038002c0d49007406c048000d43d10002805191500c032410a0300413468100c0244e80300060345120000e05400c41540314000c0b0f14490b6042c94450b0000b070256205c425862a140d80200101d48440e000c0c3d00714503800c2c1540c60080011280e44503d985001c46004619800f0a141164074880c41d180020014880c16041e80103003813141c40c1d66035030241c444001088854180c5e5030350300700c08000310601503800d0070000341d0b23404513501403072414002c00401206003c52040f48 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 874334325 1250 874333075 874333079
    0x1005034216181805041109070207091d03030a0b030a0f0b06131802091503030a050d050601081b0d0b0405090609010b0306160e060d05040c1403010603030c110f1905090a06 75
    0xd40c01e40c0000303600c10303d810081055103441c600b03580c100c182c407000ea651241180782008240d59001030400105c581c010300c14484a803d00002036405c0003029050203281c0c000300005446800150055260200090200c2d0354402c80c5444280d031113500850111401c01c000c81c140880307840e180b41d000c00c14081592080220705401c0b0b9110300c0e0801a424024000d4050038000f60b0f0041264070080c401c400301605496031500003035401020355005010300d1919a15040c0410950f52103014603510581c52500703038810303c403c041c11070f00440c0c00c0501c1541540341c642c88a6211501d803405440d006096000060400781001070410340ae64000f0712806000340c2c807171810090840286245410000403d04264422080c20b4001c10744d9071140012040c800c03401c00c400d02080020007182401202c2e20100030204501001c1c0400d0700faa1140c0c0f2014000400750540302d008aa5500b000b00c00c1d000d00280201290b00b0442c01003440c3c15880c080c01c1004440d1800700b00664100241c1d06540100842d1080007224 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 874335575 1250 874334325 874334339
    0x10228081219020f0a260106050705010509070e060d0606080307032c13091505070c020114030c030703050c131415040e01140111070905100503421618 66
    0x1020b4100b03480c0c100290050034406e450381a080210508003950304080716507848076000303000c0b80c1c004103007150076600e010006012094046022001e03644480fa8a0300e0030340b031350700421410005d943d000741e488c40e40c1d806000680700402c10082444510a1303d07802c4a4001c490704144510240345081c124030022801703420301503030f602442d17590411001100020f4401c2070f42004040e441c80c1412030007045180c44c0074820020341200329200602d10036a1684182114240210598001a01c3e50311000d4400d02c04500c0c00c6020b1b4100c15480028483c0d154100708012000c8040488150311182d03014401c40d059250b18201032010703034050103484044a14051070400480d8006905200d07008240d11280304581c1282c0c85510b02c500004484070807208066100d580c0807008040903110f03404003103800750001505003008261300800f0800403c0001405145880b0700794450080c1c440c2c410002c501c052000f00002c10740002030f014a6402a8090400c1c6014401903c80700244020f040080c0110608104038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 874336825 1250 874335575 874335577
    0x80a03080c03070c1518080c060c0403080313020d0506160e04020922090219080601050d0206030601080c040b0a0503010f0501020703020915040912030509100209010228081219020f 79
    0x180d40f080709051490b0020017108002c050108120522421003903103038060240c45805000d81d00030354030646440380c9074010b0000043c410303803200520b4500280002841c604031040e86014890014190807207655207130350341d541051012610386a8101006102c8042c0310341c0480b5160b000d52007900c2c11440c001060001818140f2190b2041e68500d0f1202000851100c00350440e4803030303c0d13002d0314545440040c41054003808529014001c0d05100310340001429143c0810340c1e056264010300341918540380c101c011240b5902c01003c80c0300400007000005441005000200110001503490320f881c5d504142d415003505d1680d6100310704545c048c54092025076922070a050700300d42c007108030218800c0702001040150142d018050080d40c1c4000c040c08178240c05400c0280301e08070803419140036050403826001280104125180117030302c1042c01544507900c4043c4903609840210700320b00350404a6560340c50700d0380612101c08040004a05110003c04076074080f2164054140040d0b003060b230802920b02c41 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 874338075 1250 874336825 874336847
    0x20120a0e030418021603020d0e01020a020a1509030203030c01061406030915070c12030504020f0d080d0b030102090904140709111204030509030106060504051c020a0302040b0316080a03080c0307 85
    0x28034960b02c0c80c25902c030540c4c11100e0341c15420524196650040c01c010b5103e000010300d070303400f10f00101d03222650796101150684065a0003071804810506041342c1001c00c080c124002014410f0109010015076410408ac203025194030300081078050410580700010b60040c01311502405091051080c403003401700e04d61045100043d80081d06594080b0304032680404010054400c1c0045001394010a5054000c140f1070340c020340707440030005030000a1210081c44000b02800c416014000e203403020120750804585420700900140c148042440040d1101c002580c049070001800200d542000c2d0052050000811035808100400242100f4070449881801c0c02075110144c8900045c04240c0290141d800c0b030b01028000700f1143d92615405040c55010340100e6208400c4440c060746c100005034140780c03609a0283ca2201c1241c0340d0f81c01c8c040503005950805034540a0858040c20305110303001000003c103a0f03a0000c0140c24903904001d0151180941981c2403c5004c10030401c40b560043c0f01c45003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 874339325 1250 874338075 874338089
    0x1703060a050a1a0723030a030501060f020a08030a0f0608030706050f07080f070c050604060b0102211e0c120a0f0e0f01080403020325120507030c140120120a0e0304 72
    0x20340e40c205840e000010140c000c02916401116981c071100000e00007001c7c02c003c00607900d04100691302e0300302c10b591040d4514801001a0310402c88540060650300246030410003480d0b000c5010120084648141e80c02e80d0000c1034107a00115a2100b4004a40a0306402c413040c11100d1107030341000007000740f4a40c00140f8541124480a01203041a80303d010841101f5410070265007481c101803418001500010000038011702c203054029480700702d6038031044407070454100401e2400c4519003021418042c0c100720040b22000602c942c0a00c1e0f0703400d0010042c0c92481c81c000d65902c0e404500040e00700c451700c024500400042c9903d040381c0e0380301c052007403100400c00d090081c201d40d26442d0132480c41c400c0e16098503400000c590b100428440d00c504040c3c000c1d200d00700c0004201300050741180c4a0240440240010f01c10111040c0800d20906644d161300003005d0000c079010110074440c1056107128540e1880b04540014040469401c3c0ca0740c454204903070b00710038005a039512422a582e070280d409100d03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 874340575 1250 874339325 874339327
    0xf0b091b0a1209030f170112140120040315110d05062b0b0604090c0509041b230406030201020d050a12141008060c0304060908071703060a050a1a 64
    0x40071260260303120750820301c000a414041100039144c001c040e41100d400303800c040707004030702c0795000025282c02090507203402e85480d034504c0c04282c803016080d49203040b6200c925540c98a1180b035a03c030325129041c101c40c080d01c800703644515500c0c0900d2041c1c44040f216150500d001c0441880c2c110041c2291003000843d0702c04a040d840d0341000483d21040c4640c1c01ea105070034800541d240c500c024001030305442c06400003248965840080c0010b80344a03041c01044c0301200c45044c0554900400420340160042134a03440000344002103280b089102d0b00030701410316021900d1840c1c1c05111031a1294601d007a102070041602d90784c0080d5442d18003840302003c1c0100030421501c00c43c85544007a007030b200480018407003005612411015680c00752040e103408041e0080103d084480003419500903a05100c41900d07503078458580000501c1c3c070358801c440701107040003088040b54140f0340745190300d03802c880307000d642c3e0520204010030300107103030b001030b005440744841000014840e1003172403d04003841c0e48907 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 874341825 1250 874340575 874340587
    0x22140f0106090f14060c012a020d05030c071407150801050a060e0d02010807050702090c070209090f060112080408030a030f0c030b2d0a090506031005010537090f0b091b 74
    0x407400742c11031822860428001c918600030323080c2d640c2200b061140d081d409070b60125042c3c1d10102c92070320086070307100307640c80c0c0403c000000030b41800756502148a0307032015200380310f40b28040d502c21044100e090800007145000140000c0c602050042d0082c041e034140011200701d03042c04990b060780c1010000e4180560380380000c281c0c90081c01110b905c103a0007449541203240000c0c05019580080da03042e401448200d000541144000031a0b2081c603003880014062607181c8141a41400752150044074129410700c000525401d080014090f81400780c0c801141d07100034010f41d1421564080706503030400d818444101c03d551140d105a90a9041e4080505203c8200b8160400921000d001c0c0c0b60b00203c0c03010000809690a038880c6000b9041107080d211030042601c00002950401e003e01580705000c0e116503903061414681080700c03d20006040700340003c218808842034407580c0d00c900a40c54492090380c6000703580d03105d603414560080303442081d181000591501591891405146644000506 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 874343075 1250 874341825 874341847
    0x130c050903030c0f01060f1a0c031b0d020d030c050414040e0609100501090618020d0608010e1e010c050306010c0c0918140c22140f0106090f1406 64
    0x200da060840160449540340c03400e25000381d80b042110460720b034951a00101103810307000e500d43d02080300c03103100142101d0442035080002030f03031000b1020f264a21080200008804408103004880c01c040f8015240495582c90f004c0d003403d40000c242410103180c130707411481c0190032409480a4034101c44010729102402d90126006185a484101c82c03441800704201e81c42e01d0002d8403045c890041d0006002340d036078840200003030b5007860203040302c442e004100461030260301303030f001e00107420b103601021811558030b4003802c4c2101d100e030424000f04d402c01511038210901d002ca00604903500705000300506460028010708901000d0300150400c42c0210013481072101407003402c4054108100200058640e0001100d101e4442d074004030b407007078465090074030001004601c0c0c809480c0c000d030001300180742d0170b140105a00d40380381030058215510004480384100d4180e4407446001e00e241c001200794180710000e080007580707038482d41c4842e005581c1484428100e0440900009003039890f5a11400c500c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 874344325 1250 874343075 874343077
    0x60a0c0311060a06081b0a0506090117040b010602010e0307020d0212100608010b1002060f040b1315020a08090609100203190c020c090105150403020f031f020415080402130c05 77
    0x1c10001c85100b54014030440d05034543c011000ca036285001c8450b40031b2504001502140035070012a07101f6084036007004907081c420020700580c101490030b1029491452035407038901c030090301c1c01d440c102ca140005001043d0240300d9080d500c181d440045081002c240d0001c0c000034521000203026607618024000d8100041101e580804501603003841017907114040745000300211049988105080c1c004041c003103001080c103d0140c6801054090b00b5036030b9480b59110740c030b409000d0302e6030f0441d48a20702c80810343c511808440301d42207071070140e9158542c2000820000020b40358000035000301c0c00f845885d10001410000e40401c4100241c3c0708d527141c42408144802000c50740c0030341e83c14140d01d410078545c04994600d14480494100089036220410b0202c100d2005801448401d420401840546002903800c00710100007000c94451404450f1603000703108407044000c1c51b50340c0100d000d11072410901d082880358942850a080c0303501e0030350000781030305c200b03c800e180b0f00d42d680e10250002d10384500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 874345575 1250 874344325 874344347
    0x51c1709120303091f0614010f091505040f090c08071404051012140c04060e03010b1903060c0201021e0702040e0304171c05040e13170720060a0c03 65
    0x2030703d44a00e410313020141c5880c08900090241c01c6070b002c1e89a03e0001300e2103207000b5a010182140103031014100150b03030820842000714144a51180000360008000150310307101d155568a99488524007501c01c1501141c0d40c001014a50410359405001c40d40698641e60100740e510306140c805000503100c0c107903886680c2150740c200341d0f075036110409507411641d103120360300342183c3c100040070f41c1c4603829044200998404180500801007008024071803d00306c071540d10001e00000c2c1c003201620000e407102844603140c50b2541c280c0700341013042c862144950f105550351b0380000c0d494407100c1d0348507a0b8064440e4088584182010601900399215940607421210b05081140e0341c8607102c45c64000c0d1040900c40c61142d0744a502c88010500541e0500d0320445800313901c1d060305081c01d000c11020f003070000a05c0d041000741042c10303020216061074038000f070401c000304043d9914860350411100340c00c2c2a08194806a4003032500809030749404080750518215840c00101c0940340b840d01701c0d0007500107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 874346825 1250 874345575 874345609
    0x111070b1306090c080d09050a12470424020d0507180f05030307080304051501031b05060702010806211605040c020a0302070b0d0e1501051c1709 64
    0x400c0301002000520072113541902c0c07410086515140301d28004a81d04d080c103000b07032900040e00351000c00c9421468210b18424174440c2d1400c4050900244110000030b030b094158a03070010103a00f83c013598403d030340115020910280800445454603032030350345085d816030611504640603022900740007040303903064480c441350b020014400f50400b0140248441d204403203800a400000381c1c001400c0c0242c003111004c495003e17001c0d60a103851510b40f41d18a40004209541754022038000f80032801020303000d58041c5200d6410042d02d0030039041c0030300daa13070307002d4100c24040c40003042441c001d40c2e0000310140c0d200760116021481600c000b030302d03d40c03129401401c0709810f00c540002c4500002c85842c40d14140c0304190340030030251404d820201d03a207131021a4040d0150b04554402d200c0c0b002440003c19003035488050228406036159541440d02000240c5048007411210040c0118540000c00d51420041400c1d07002c0359402036191102c2d81c21540104140000303000541c0f072850f44921582050058003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 874348075 1250 874346825 874346831
    0x140412030504150804031407030e1003181412030105031906020d0f0905100506060a180b040602100b222301080607020f060408121003060501090606110111070b1306 72
    0xd00035244c04802d40f03084000c0350744102c4103015107205000355202160941d4070005030480703c00034400c94108c0300e601c9804050301c48110318041180120740101d070078842c84204501068003440076040241141a0039040c5008000411403903030001a061001c0d0074030305034141c5000340f81c6010002031284090403041a0308081041ca0443c803943c0c070005800d4028000d465500741d45031848800c42d002151100c0c0d00c5071003402000c000c203205405900d146c22060b0450b1803585e440341418a020f0300a54401001a8003000c240315841609014035500482d007990350003241a111401e9540940550000030b911607580c40e10041c001010b10542c1442080c002d40340c400f1561960b100d00e868480440e51840580302c0d1031304e1000342c030200082c041d00c5680c1200e002c500b0580d22050389100b402002e85101e9840c02c904101202140c0e9600c42c05000306440f4074001440f07440c0803009032a06594480c020b1003030349845201c05200804e101125a040c0e441448904207a440300c5040b01c03070390b520040152000745 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 874349325 1250 874348075 874348109
    0xf04080114070e1c0c0b0702040b0d05151b0706020d0e070501121a210d0f08191b031a030c0328050706020106090b121515090a0b0f01140412030504 65
    0x61b070b035401000114020780b0188582c48662040c018040c005000082041e0f208131003d80ca62203494034003039000400788441035580300ca4001c02500316045100240c525980c00598105140c0041c03080b408206101405400194134140001e0804100700501d040c0194450401840c06100c9076411000d203040200104154400025440116020856031508502c10380d031038130400c5401910303c0828000301e07a680e18616038400100011a15150501d0500c1075150140560407010843c01580104002e55000503080710b0001c0c6a080c81031000101402904540d01c14540c5e5107011650710f21400480b009580c0c03c980c0ca5184604000803618082d003640603240e008100d0781d5040d0030140855600180c14001650400d00f0001d1000041a0b0200694403c04102ca410740429160311352216860203500340704a55240132402c45241200c40288655403084120958a840301510010302e00a1920851250880350000c000d880b40f400f584d542e030f100c1616200d040600c202e0480c0c0c040e008021942c16550 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 874350575 1250 874349325 874349339
    0x10b04140412021507050901030905060a0e1c02030d02091503040812010506030601211d0106090606030908070b041b0311041d0a0b04020a0b0f04080114070e1c0c 71
    0x280341a241240c0140d05202c01d201e11500c0058080f094200341c042c1c11030a0340383c5e150705503116806241194107241d00c54080c1c4d00816014001c01784100c145020100ea000c1c1303140391250410710254416182c10140106140a0548c0001920000d9540c0300c40180c0e1031010400054402034082c9820310f0070f40c4000200020482104058001031140a04140071640c80794104402e500040702c2490004542451844200c600e1000d051b01c042d401c0307040068001c035100c200c04036440700d5403111015a07441d00c104000f140010b2140304010045031404102c04201552503400300c0c070407007201522003094200414144020b0142a0404000300c1c03080300324181d0790385031804015060003d0944150b00d4048120b042d200d032081201c44031400c1d0340281c04c0d61003482c1e8800c0340402c0040e00a90f0041075250300460002c01e824000c2241ca03031341c025915200c81c0b80003011401c1d1040e6881410380d690905007801807054200302d0b00070001701d04841200e181d400456121096010180014042c00f84590b0001442 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 874351825 1250 874350575 874350611
    0x9090c1b060905031c050601031a01031d0105010b1c090c030807030207050d140114040312200c010504150b130b1915110304152709050a0f0e0c04050603010b04 70
    0x341707034115080c802d554405005508840741240340004400486503001d556611a5008280000b0350340302c0c80c504515100c080c0d608441c000d81010b03069110000b001d040440e01c000740140c1001c848841404865203e540e07540001c0c43e680f03c01002c40202003405c5003014024850304000c0d18010300004005001030074640300d411402a5031500039407038030500715511084d5081051246405407a16a0000f110001b118000e24000c0300150f0348010b0045560030120b002ca006081c2d0840c40e0340085001c1c1000d0500c094080b51035102d000203113181800e4140a5210b10304110b126852040002a401d81c8001c080307001d420000c03011500d203828091000c9202403007040c500c8854175041c2d8840c0c0c2041c401c8803410340d5900c41c1d4024180c126040b10708503000184159015a011184c0c081c03010802c2200b107031f001e200c407051030300304e00d8449449400700894180e2902c40c9050031409458203100030700190060342d84450348501c286010b29240d10008040c1c1e1825044036074000e0000d8001c100c1c41c04400400d00328 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 874353075 1250 874351825 874351867
    0x3c06290f0d020324010e091b0429180603041e060f050c09010c1106040e0907080d0906080601080a06050d080301031703010e0106080402031e0d09090c1b06090503 71
    0x10540c0300c082c4e4450784048403c3d0441440030b042e1201070410345100100000c1c000001d00f010860080c5240c40700031000000050001040900c81000300342c0d000d54080340003106a001168005202801102c54401003449102e0300204141d460710354035150f0b81003aa0182040c40c0007222150742d5411003201300560341e40985945001100c0c00c2210703032502642c08000d0700c03c114155002a074031700c0e43d0001003100000300d40340c10680100540c0ca0320340d41e0641644480012501300d2185d401100e02044a00004c0c441c0c03010b2480107180014080341050000741c1011005880c080c1003000c1c2d00009804a4030503031041c0c2c0a01002061141440d07050718000040c0e80c0240002c54062210442080d0002c1c01982924142c1e2590001102980c1c2410400c440388a0003d1059900d0303c0f031100034000c01e0020340c02e44000090b40b000980509541c0303802c0a424601c05e944100c96580c0b80c0410980241e5008850b0301a465105000510041ca1030529002904100b070000c1c0030f0340400501000806041d051082c5d03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 874354325 1250 874353075 874353091
    0x5090915030c1012050a0f0c110f120a0806040906020c01060626130524011508040c06120902030d1808011a010f033c06290f0d0203 58
    0x1c548902d140900118529002070980400c0b070f5003140c4603080030b540d042140c0c010011480010f010381c0c07107040101900c1120350a003020821182000700b1115040c8212040f400001c0010003401c41d0000307211078640b10f100c518000704605080800c0b42691039420208070307140c100c8030a548a03114455051700030a09841404089100070302215032070001412b075140311004010001d0101d90300d0f402a503c1504007218101c2d85401039075000400621110306145940c4502605540e1542c101000040380f81c4549001200380b00c0000d0410000034039480a19007170341d16070724041c0e543e0910f014a1001800c10524001d5160207501a02e15625134060340b80f4030310501c0852000d09140e80c418442d1308031400c02204030712065600c0306070441940581d00b82d01c011046032a0010710411807013090034080480042d60401c2e2841c04240520b09503d020480b07250f0900038200704400c0345402da04042d6000c0003840104141901400d0030f002c04800c3e400e0341c08403800054a90f540361055215500290b00c1203032000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 874355575 1250 874354325 874354333
    0x100504030f024e060112060207020a0b0c0606090604090506070f020c4605010e01050c0105100303020d0203251410060504060b071203050c090a0605090307050117010303030203070509091503 83
    0x240303c0000007512074100d403103558041429a0035034032598060b5005100076a0400031481c00055003641c68401446140400d02c05084141001401c0182d11a4083d0400780304504020150011032008079255030415101d00300207210b020340020903414a5414640e0540c804501510040403a4480548000f2920f00e404035142e00c03142c51700c01070b0454a17989a40618548440014020765009003407102c0070110504001e810040c2c8008180c1c00d4030741c00c84500310340107030241041040540401c24100d145071240081c0d0b00f011840445401da08060f44004c98802100710700e000c003441051411011008000401e80d40460501e004d02c10146c01e0038402c00e400341d0325041e000500183c40380b00382d8030000c6d840f911400300b0f112111001c40160601030503035490142e00300295812a640c2445190003030180b41c542e9611900b09a00701400c0500e02d038005414000c0107540d034101040040d040c00d06496040c280140c507500c0c0e400040310140180e0341800e030810740c100d050041c41c408002c00d10001080c210122 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 874356825 1250 874355575 874355719
    0x11090a27050d0503010b120c040302040c050a09050f150d0f06030b19020a1b2a090f0902010801030318090606080f0a140105040c141305100504030f02 66
    0x71203c0744424404c04401e41c40c1440401600758110308610b41040e0341c210000d090544940002c1d0440c0d0ba120540d0000c03410000c2c86c0e44005820607110001000e089807409556550800410400f92805d1001d0420750000030f0400c01c0000d0941c0050011540400304000060f1a4075196007407a1050751a20302c028044400d0340307105030442c001c5a120000c1c0350386151140c4000450501000c040480031030b0041c3c02c51641980341c006460700024507025100d045a03000f441e280b090b004552403400d82071641400d080c0e061000d40d80040601e03044170751602c0d01685d040407040000d001c41c00c068201591142c1408030014820790f1000e00310340250303034180140c0401d4841c501680100c544101d000d40c240074961004101c10300d015401010200f10905101800350550f6403c0052684500c80030114039400800a211604200001d080000580d0400307034501425074036034208888203440000d02c03911096182c00c074001103825058040007601c94001c00c007018941000b880303140810b0034000c044000304240f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 874358075 1250 874356825 874356827
    0x100507050304030f0f03110f191a070201051603020903030304020105070c0f030605041202011802060a050741062406120412090b070803180607030204091811090a27050d 74
    0x10207900f4003030303440100346a00078640c0c609d50101503c10b007a03aa842490382816000075104185034410720803039000041d0b0b071030002080508074043c144070030109841800f80c81c560b0b403030020441b50015024241580c86081c145040301d070000c86a000910340f0000c241c0d0001c108000c6400c418050361049020200450b031100c4201e007240c1c4000140044012a006640090306181004003010364141c0340c4240f60001325113841160141003041c134808150303101c80e040091840b0480140050302480054102c41d02e09400701d56580502510000c1408101c0f2000c4010341a19819090403040c041e040f552a82d82a003500100310310119000e031440e03945005000c885901c150101c2c000d4030f6181c120a814041d150b04e82000c10781005146030391306503403030140420241c802c01183c0d10901441e47c0150b42c0d1810030b01410103440c0711000300b20501c22000711a50004858a08910003841c055646040c223684041210b00544403410401ca8480040c00c903901138100b0f203840f00303803001e4024012208105007080d8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 874359325 1250 874358075 874358083
    0x209130225031404060e090a151406040314011e02090117060f1f110d0e190515280c030c03020c0603070807170402100507050304030f0f0311 62
    0x15403205110101c10140c41e1520701c6046848035000b40b4004411959049010100354001e42100e000f103000f80d01010524540070742e00c954080c032800c10500c11464004005505500d01e4002c1d003d11603c030410b07095030782c1c9561701940d00441c0c00c544000000a0052150741c0200562030111040203401e041c41d00c4800401e0088130040c00040e900c200b050b400b0080342c40800d80c0d02606040d4040c0110384141002e03a00c00441903842189151a280c50103103420b07003c0d0012200c0034a10310940c10804542c806260040020300906006880680000c013508420703c9128404e5000b20fa48082204400e2000551182c01740c490080038040484215084441040d1098848000300c80044d180300300c0040041d1184601083c02c4e4403900403100821701d010005041e540040307960000007004282045001580081400e100c2e84041e6182182c40c00c10307802049070042d66907040b4040c080009094030030040100103c1c1c00031a00081c51b00c1d00d001941c41d1003050303000070800036000100034070071080d15088041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 874360575 1250 874359325 874359337
    0xc0a0305070f020631050f100606090506030403120c030f15030209070c08040b07050c01120902150a09092306010504120f0201052a06010f0509040620070602091302 72
    0x3d0020602c84d43c80c0c1d40c5c4801c0b08940d0310408241040b10900d0690088031400010410f54801d0b000b6281d62aa0041d8041c074140350110242003850802004120040d00603000000b07440c0e007070300c0541c0c3d82d58890609a414800072040040b0442c0780130350144001c0c2d03065019503081d0a40385010f110910640354086803002c900c1c04040e509c101300070003140e05140503402080c0c0161140b449c0500303185e554511041140c1001105071500c0d040940010070350b681c0103101001c140004401048080055000f1403000042c4034021040b4110004580288900401a400c02404403d0f42402a0000d49040000011107110100468082800450140c3d0b006105980603100303c0002400045020707200c101c0c011466000c141c0c10700c0000c0107984042a00c0a8590304003881c0017082083d020302030342c051032801d0016444006500d61680b41840240d5560050f1600150420030106070102d4003450010200320207600c1c120844000a002c40400019030003916010300202c840d5040c00700ca4802442c11b0303111f11 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 874361825 1250 874360575 874360577
    0xb060427030f110a15020c010605030f010207111f0c08220305010c02150a0207020609090126070614091219050c01030902060405011803021309260313050c0402030c0a0305070f 77
    0x480300d1748031201c007907a024001100d00301e00040351640d0354501013400c00400300117005140e5000a010b5051081c0d02c14007941c0d2002c19a0002558880c0182e480b9110410a01500030400801060000e108001d0f00b514614010f100c04c1c05c41c0350103007000a800511652004460550a000724800c58500108d280345122b642041c003050507a503410003540084d40075407000c07a8040070600c125007540d11018031250280070181041d40c0100111299a800705498141041c20340d0300458003030000d158440240f101c2d285070f580003180c50789004400900011003c03008d0100398030800d00440161070400c0449080350f4020425100c030120540011803d807100360102942244042200b048154840d5402c1c01ca40030a0240c4021015101e03030010701341c1400760301c4415105884628501c04d011106101c10b20a0360803c0042c03065802044000c0d003d03001c02171032680d03007061104608007030103404d01108030a2140204115540d14265030700517041d410807a100000240b40000048826003c2c4c5240c0c8100340c02 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 874363075 1250 874361825 874361843
    0x10905010b162306131e023019051501030809010318080c0c121513030e0a090c02010e010b0a09020a120f090c0623030a060b040906031109040b060427030f110a 70
    0x4001d0007250318201052108c0d01d001004c004545004d00180b0928404880b988007160200d0043c1c1070007031803c860007080034201170403800104001b5282c00200e4080d03c500317003004075940340c200c00480301c0081e0441c40a0034036880050301c4c040c42c240c0406d000000000440b110b02c2c1601075034005039541c02441c03400c94252482d030808a420740b011b414606086521910302040071081c003501181003404140d000100d001c0d00c039001920500d80a00440004404d020005c001c0460807000007540c000d594480c0080e203582c0001c089207000e00c070f101050414547d400c0280f01151805000400030204000140d0b03084400d5500070484c20300c0f80c44420100710150300c002d540f48600781c0c20f8100c40e0303001a15005843c0c0d903074440050001c4034040900b00800e0030010020f1500d183d414a01105201449010300c030302a02001c10002500b4041c000da045002501c0000302e00146031102c04442100882c40d20080c0c102c001007004040e0f000000c40f001403220b81e00c40b595801c1031140031f5554040800e009244840d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 874364325 1250 874363075 874363099
    0xf0608010501121d0609070605090f0d0c0308030103030e090a0b0607122708070b070317040f02090c0c010b0907053906010905010b162306131e02 64
    0x8071aa20443e400744001100203006000c50707483c0d07045160311100b4400950800802c001d0900001d00c80c1800500060410030319110600001440a5030030400441c072429880c0c1d424014000300c00380e1100503680c01401150b5958480c03d02074124002061074511039446100024205a42401541000c80020b88064140b101310b0f0346440c1001c4100384100100003500780907840c0c103c1d050a040e08002805490101e166007010441400c00f00076800030aa4004108041000241e1001d400c0205000380c0c07030b4040300c3c0d4a8900c3c0c180c24041784040041c1d4007a400d40240140e201c209401400d800648030001c02090b0b8084080c010340820407250340011800920131048001018801d090a0307540c004410000881d20030400c0b05214400da16003e210383c0001c8c01484925242d1280d030f800f40c901484814100b81d80302d06080d400c42c1003120024061a45107501c030041203030000011700c203002030101365245894003550b03889405a40f0803007a261451049100c104050b0000303814904941c01510b40e2040907 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 874365575 1250 874364325 874364327
    0x2100612110d2d0c05090103110108070e0607030e01030b09040327030609080306091821090a17010b04090c03080a0215010609030b072c06040e010f0504060f0608010501 74
    0x29103220002e0f65a0001e001c001c0c9220a032074005142d414902c448040032441c41070504041c162081c0c1c110b41c2c01100c01200500c082901d8182446440c0801d00e400d00c21551102070450b8610001c146898210401148031010560044803030482c081c400e99041000714414002c005943d40242c6018001c59546031480d00d004101c1c524905456940455034811541c3d00e6035607008440300000107480030303040070081c0003076803900c0340c01503030801e607904c080d00c0c54403102c00d40180d00d52604416100103500050140d0b070004827547c003a00c0c04240002d022207803950f039940346144080300c144d2a0221a510705400d007156440d29101d4010348640000190000c00d003181d5039144107520007042c1c1c4d001c2d4404c801c0c0d03000e4400045403401e07000c1c5c200c0741d4900448503e1132500c0030108401500240a02c42c100d05e226040040d0740c0d10444058508884030280801540045021445190465640701c89100c002044900b00325101e20102c40042d5801c0050990320b00180701e04070034900980001440c0140100899 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 874366825 1250 874365575 874365589
    0x61003021608040b0c06090a050c010c1109090604060e01090f061815060303170601020a1704051e0a090902180403030b1309020f03030421051204060210061211 70
    0x4507900d0407828241c00e01501c45007080d030020362021440c800c4c0020140305c408014002c1c40e030403010305001040454419a00d403511440c40b0030300341e8100107980324080103004202a8030300ea0844060000c0c9801c2c1403024281c1e448410403281900d249091100c0c1503417000051081c10300c3c054003c0e04503280013002e07903070300d00c05400d14201d9205040d20540100d808584030401121100421010000e8030a1075458081d00340010001c81c4e503008520740042103416600030910960725544141040f00140f4582c1504181e0b00498002035008010050620b038040101c1d11447c03c50030007182c0001040382c1d02e5107058181d52002900039040440e0000c0041990b0002c0c40d05a08184039060100f00040e42c1000b00300242030004107035554030386a9440c0340035410148032900350000e003038020b5441e2504041d031a94045200d85500a10a141e55940005201c414072038940141540c0310710300d64407aa2200300a503a503010b1428585914035000700040d11640e43c20203507a0b002c0e0700402c009800f80070ba4040040b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 874368075 1250 874366825 874366837
    0x1d06070816030e1005100f0605090607080304060618061a070f0813080d0806040c23090f031c1106070206010b070317070f0e090603060f060109030c080c1806100302 72
    0x1900c5004c491041100c01c0380921441015a00740381b80c0401d11300b50000744800c1c4168404814080304100c080100d81301c0b0301c229515113800c1140144d0704d456510307002c40100195480307030700040601d9040c01481d1300385c1c4c0c1049040703a031220416881604002c5011040340b04400c0d0013821041c41d04000800500079802400b120945013400305545a920351085003820300104801e0700094042041101610b014480c082e5140010700e482c084e10342401e88110801905001c115261150201c0c00192a0f40d5002d00c2060004000d01542c03a236400400c2107125406549124001180e440902c01d030b54420f0000300c0b1403040c416a4010040d42c0d00c4c1400500caa503210040680820480b203603480e28910103800540d010304034540e10084c0203040320800801c440503001101d0700c108020400d00c48103a40009200b030300034100d00754030040e5469020058a10994a070700081c50240040310000c2c2c16800812102d183c0401541c0c80b04020a0035101646086c41c12140c0603400300f910040104601e100e680a461 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 874369325 1250 874368075 874368101
    0x11827060c091203170c03040302120f070218011d04030e101101021b06060a030804030b10080f060708070504060c0b06210309120d08011e091d0607081603 68
    0x1141c548074031100381e0f03124218034213501041d8000110780f043e1414518036680115180106400c6040c03c0c0e074000d45541c480701030704040340b00116520110064910465141036402019445001c02c402d507085c030000340902c500306010000b52212059240d045402ea88101e501d6641c4846110a00341008a20220b5000460420440100004004509100404440340985412201c880072070100c586400700c000e000c98060f80c3d4015041000407900d10964040c0c3e07501610000e020f5894012106100415034000c82c0c0500c40d20412420402c030100e5103a004480075075646c80141ea03501c6044e6200c0c03003588609000200e22003110004030340314200041d0000001802c00c800c044a042046c1041c1030b03420345d0148180c200061156051031705038200c55461007450302400c0c3d80b4000503405003181b40140f00e440d07042c81c03402c2120841a40d580100802811503000308000c000e0741100001d2010141d40e50100d4144513440201341481e0041000910038201e03410480c080401000089000d0184009004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 874370575 1250 874369325 874369337
    0x1e05010f031a073e1f0f09020315041b0b04060806030a050313170f061603020903030406051c0506090c07080909160f0e03060a0b0d0209011827060c 65
    0x902c4030307820074541640c1320880711a41410990b0a02000c0c01e42e044218001c2d82d0340d800754805441c0c0008050009407440020100001c400030769128040280400d40402541409903000c100c5003818100040c41c000d601841d0071701040b041a401e000c004800c0750080d80940032050100304561880781d06e0380c80e88103801400f51071824485a4425246030040c1c01200b40b50000d102c0300344104d110303194146032100c182100404002c00d010200d29124040075200225a1042004441001e0700a404640c0030300d401074112907aa5944002c010495000103800b01e0301d413a201140c0204014080c09030601038030004100b01c90300c0c0c64220105886900100080750822401e000d0040240e0764180810b00c0381d036081040c004d0a0195580082a03030505103800c10034000c20030412602618000345466001c1c7d818540003034140c05d02d40011b0300d1031401c4000254008620400801c1c18002c80310282d0355034000e40014815aa400d6045400c0d121080c00080510300004100c0c001184003504030b0404a4036908081c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 874371825 1250 874370575 874370597
    0x603020c0a1410060b09122a030304030b0106090509072d0c0b16020f16050609012c0f06091509191202010215040230011e05010f031a07 60
    0x10344284c41c0c0a0380a603208003800b0410f0440340c00d008480e080c008046d0f50113061442c0e0748080c00071041c050440e49248003040004a20085c1d18100100c1c0e028503080030380307104c1715a91401c005000802da03000d868065610780d00815412801414848080c2c80312401541c0402c500e401020100c2e450507510404201c41601000082044100c485003c3d0120405060109044200c00b030b01c0c021400e464110a40d2200d940c0d28040c0c40c0c0d0408180645104480e125916682280101e400c0105940c0200540707003041c20240000080c000402c2541e0710641d04109500c1e003100c100300040c043e550324260400355074034071034045821100c001d04000200508488910348104003c004101440c2c0084c540c19245200b83c500759a010441d42d0b06110680c1448100780c64680e0116418514460412009112a40403080401d0114541001c5103803074500820061910141d4410200c0c2160b15104103549030200100e41d4018007110301c41a40d03040070200c0d41e030446a64191a28840051490041020005031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 874373075 1250 874371825 874371853
    0x40b0703180f0606050609061801141b0d0504080d0c060207060e0d09080c1008070309060e0705011e02121c0f0501051801050f0103420603020c0a14 65
    0x6071049018120000c0c0c5914249080b10446074141c0045220300c1c03043c00882c5040c0e680d141101c0010068994000c01e01050b540180c507141060f102501001401140c959110003201d00b030341c005082860700b1036604103041c04c4255554401c40c0501078140c6c008175880343c080340c0560300303c840e0345100b003100616080940e06e552084070700028501c20380e5041041c44141c15030b444545803001d002007801a000d414150000982c3d04002e02c4448414406244005060117001c0e902000e55203400540501c0391101c04e1308100d4076a01640650b6021410310b0010a5000c40541c02c4100d40161a4004183e11a181c621901040c0c04c8940d40000031211504400030101c003900491018480c6c240703010031594100820000751040591090a801c181500104069651001580b01464080c2800030791941d0002072100200d018080c140e4051120050074094108000408070354800694101400551201d1003181070344104584d154440d80318080310400f03d00340741c4803288006030020899007000c6144c94 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 874374325 1250 874373075 874373111
    0x1060c0f120e190608040f060902040603052104120f150c020a060c02160603110f122d0a0515120a0605010501020d1e0c02090f250503040b0703 63
    0x1818034000345258905100e40e09005016016040c10140b0f00b90503141006001411403000030000b4103032182d0f0145032010710246501c658002d5401900c18410140c680c2082595112140042c40343d1412010303207402c4101e58081510b080c0c4400711640b40c0c20f000c55403181a628845103030140c0388580c0e0410070451280302882284514070564014018810581c10800215020600150b0641d00207207041c1020b5040f031641a000d85005080c001070481500c04905114080d194041d264a40c000a10541510541035418494141c2543d000c0c00301001240c0103c0c5402d40100400c010514800401c41841860300111b500c1004460251a03101d010700c001001b8502060302c1c18050b0b00305a52100500c2858000c8502510003800100700c0310031071090007400303800b01020301910780c50590340007840345109148072020346400a200010341d0a0101d5011b45090044e01e07424030b0301481c14243d551040800c00300f01034100e801e807540c90444e07030355490300c06000304006c121f0f208065407008010410b0274000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 874375575 1250 874374325 874374353
    0x30b060d17070c0f152304090222050d0201020613050316080304170903071a070f080417010902150706090221060c040b16110d060c121401060c0f 64
    0x414102d043ca14090480082005a0300314841260b1210041c850454001c65003c0d01c0c056140000b00c5801340d03801c488001801143c006c04291400060000001403080002000d010160082006240c0e6500d04100f4014501f44009015070407007000504600c8503008003690305405001500d00c0e0250112104401071700034041215413503408402d010901c1112284200c034450b61044851511107000f00003580c40031036128210f4030300755882000030300b010200252029903912182100a043c0c140c90030102c6504180111851401e020311000100d080500540412680140400c1600c12000e1584442c55120038030585025032a02d0042005032110b14503903c54603901c071603440e640740703040e1504c9060200190000c01c500d0804d010a112101e440011110070072901309524642e00c1d02c5262200741900711000e49684016640c1150041c413501d6046410301111660710280d80d03151003140017088030fa00800d6040d4002e004801801058050015080c03081d0280140031101883e0340d450400500c4a0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 874376825 1250 874375575 874375583
    0x1230c0405100c030e011112070203030f0301060306060f09050d11040209030f1006140906090919120e04181202010e0102160309050d03020a1716031116030b060d1707 73
    0xb00f55409144d40100712401030741c001d180c00d116043c071107500d071682d40012001e80c0344211700004492085542c20801c0301da81480100030151650394a1401038000d01c4140b05440200702c03504941c3d94028810b40510050311001070005030810b00c1c93322114694840c69140030b420940c00c1150005641d03081102c4407054114000501d401c40a0310708007020350b846ca03400321281e9840c40c0e024071800d588554007141d0140c01540e00d000359036141b202c040c4c542102750b110b101e40e50450302c0c0340d001441030402d2502c1d100005030300c0301002104101c09100456038040c40141c60000003501d048005070858601c10740302c0a880c8008202c02c0108103c2d41e0072070b80040e0000c41d540080014820400d90020300100c01404212041c194603003454030081c0d01d036041d60100520396407401856800c0c2254120a40e041d0b105060803e814545c0c6603d8041c022130819040014203110300040b04140c0c00e13100102d10309803640301d45070804070349440040c8820058120380489070140241400d51105280f20050070a180c02 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 874378075 1250 874376825 874376837
    0x1a040306091b090204050105090909031201080a031d01020a060e03131202040f091e021503070302071a0c070213020d020708040f0b0f04120c0902030114030f01230c040510 75
    0x10b5030319400e008682c50b900642d41d550041c0000c0186a8011041d03402c1500199288456652800b8000d4294451920010060102c200010400c040001101c0c100107201ea198155080c003401c1d000340308400c411040500607400a40c0302000180943c00150108100c2e078120707170a244494055040680c0141c110040056001c0703011400e5145c039000301a0100d10b0184200010506070b2034161740c00140c514100803008884103103c0854030389000f007041402c6620725042e140c0c108034200030041d5209c0c4000740d8064426217982d0801400644900317020307101c003200041c43d04000ba801c0c0190b641d60607100107142542401800d1180b445030006000ca94420f0a800350f0721810460804485004e83d086030b0041c3d102804941c180080201c100e9046d00c0588030388101d00821450302c0d2042da0001d030060407a0a0011000240380340e0b030b4007080c0030440411000e07034040c00041e170021800c80e4a21010101e4012107150784041c10610710100e6034100391410401c600d081d4442d030200d001055030101c40c00c00540 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 874379325 1250 874378075 874378103
    0x1c2001050132010207051e0402040b030405010f0e060106120f0606050406080f040309091a12010b042003011403034509010303050307031401091d070f1a04030609 71
    0x8804550041c07885103000402c440002c010000f9500c0c0031501405002c0d413140a000b0803074080220400c010070800400941d561600d8688141c44c90b0001d075000c032171a40c281103402000d07120902500d80c047c0d140000803c1c1c180c5c6000300446400f031419024035807880d69802c1c04055038142e8003510014004903213890340c1d5145400380c0100000001849498502c01d103005000001e98041290b500300c1344602c4006c10480220040c40141c8c4500c084c2c0d02c0e600113602c0c400c100d9400011341000090000440742001303c0701c0c0460040721004c00c6d004040480714010001406090444010f45003160300140480c1d0405800d0469806800841900500d54150341c4c80d24003440321800f000700d6120301c3e0404400d1407040e00200844c1c0c0940040c00000c061000100015071054403a0b03004002404c3d8540e0280c100e0b50f507030350104005201e000e0350b030030540704015400c441c1d1110001d51441101c20080c2096411442d0030065020104c90303010060045030204400400319100d40034a8000600030040041aa0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 874380575 1250 874379325 874379369
    0x6170d090608010e010303050a050f16060e010b010c06020d06081204081b131e020f03060a1d040f03020a020a060e0405010522050c090d0c1401021c20010501 69
    0x800d203030703001c80c04009005005028030403908102c0c0d4111380d49070821a856405001041e41c60b801024410704600e2404201210240d50b00304000860901928007003008580d032a5844c0d0136200180e8896010402c2c5803038240001d00158010a8040711901d400107100303480310505818008500c412040f80900410284031080040c40308a81c80d9840c407600c0c0034051700040c0419a940c01a031210601c140c2d403002c1d00302040c0d0f48203011401254010b1030440d03a038401c1a440d145250000e41d17035503000349001d2001043c544007441030160211418241034601c1d0b03803142d460525181110000301d0860003140600401a12501c903e900a400103071643c0303080c00c0b40c0348c09010031248145d22081c0306102c55013110a4000020221480d90075030100081841e40d1940099101442404800c2c0d8000145030511021f00032290203000c01d0740c24410f00a54980e40e1200120381c0d814040122103c04500d40014a912078020030b5601c02200421140340b0b105071a400380a4215182603010b503251400341803d214040d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 874381825 1250 874380575 874380587
    0x1116030506040b130f0f03090b0d06080c06072d051902010e0f011d0d081602010f031b0e0310050a061401051903150e0a0b120a0203100b010306170d 65
    0x2015000c011444c1c031180940f5450b65001002001915070708001201e172003811300ca1510b080c0034081c40849184e580d400c250501c00141402e100b044000d000b42070759600b85140c22002c440403150402e40c07283c0ea8000d43e80c810b5182400e6905050110003250410300c000400c1070200e01c3c81176810401c00d02c50104c1600009d0480e1070041080380c442d03920b40a83c0c61960307820000442407180c820132610b11040f11440802c10704240e22401a10012011481b88101644100b41c07402d001d100f03a9482103500c01010003a0180d0b409404512080010a8101d041440c1f080030008040380c0000c04480e4001c900c5400c0f50f08a40c400e444110289880314800e00c1440e02c9070006c1d10401b0020b01c1c0c01b03440c0847e103848809407040740780d88003010962110340c0e045da01c0c0d620101d81c3e1b0107003546500440ca242403170209a0020085110391a005684080c0c0c10294044c000ca0102003a41c2c01401a206058060040400030810805410305144d40c0b84c0740480e17403a41d203851003c000043c100003420040c1c0300320405404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 874383075 1250 874381825 874381831
    0x50a051c1e09030f03020912070b1b0a080d020d09022d0303070c0905060a030b090f07120b06010309150c03051530031e1b0115061116030506040b 64
    0x35042a0442c40040d6100581c1c0301303a600940740050b11403100c600040c0e00443d1744c1e02c4031912840703034140100c1e211441d00000c24060880c400303020441010a00313400d8441c3d4003d40094240d010601603403044196030b40080c000850002400201c0341790a50014a860f84c16490350362012804003005e48441f100d00052440c80007084000703600306846580c1c0c59000c0b1001d4010980358070b0b20b4101107189a21000004405103034040d03514104c030f141c4034419651b2a0550030390303a10035200d01d000000d0040007200c904039007a41c01c40c0c160780056559100660150020f0306044528004080146444003060302c00c0c80003a010569002c038240c1010031001c203001c40b034842101d20420354000c01c02600d0220842c105408404101c1805692038042801d9040d80902801d1a19801c4010100c0d0b0045048100922003014001c0700441e030386071150842c5080302c6403492404075190540d241840b0407400b501ca2464413217013000844030580041c0d01a00300ca0b030041d900440305940b014041c44108031300840f015074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 874384325 1250 874383075 874383131
    0xa0c020315010f0306020c070503030c0f1219081003051b090619030b07021009060501081c0905061c060b0304020a0815010e07020a0f240219050a051c 66
    0x5401e5041c040808a0510f0504c40102400d500003154180c01c44140f100e00c0003810024141d0351200b100c82c4d4500c4d1944100d030144400360184041d210201d0143e8025036051802980d0105d003044607400c1d05403101d0340b01401107022100c1400000001940c02c01811030707100181c401d03042c0c403003440300f062210034070b400b410684c86004542c1d81c03480c080c8210581c003c100d070703040921480d0039181c0340340c00d0381805d0140005a0940b41490307012414428581c003d2070407208100f080b11081c083c28110400403100300d0140301c000482c00b038002c1081e1710700343c005016203101d9910030101d404006840e00c411682c00c1d0b070140000d91400700c104401d500c1c00134a9038004081000240a004600ca800c0e90a0104140100039003a2036850100d02c10700d108000b002902a0310900703c0800e03640074104119118041c810300b81240390040409e05007020940281c658000900c07615040d4003510410580e41508034a11038030401400340015500c12081080d15036012a42c858000b42110800c500709010150b04103441c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 874385575 1250 874384325 874384363
    0x25021e060115212405010e030a1b050406180e0f0304150e03030703080906060409050a020f04020c1f0b0d050c040b1522120206030f04060b04020a0c0203 67
    0xd601d000b2205808103a80510300f054080b507038107840401e5109071151101001d0f280109141138404189441094141c03c00300d6082000d543e640110303503a03204250401e8040c3c1150780769000180c140e1004440318440c0c0c0110800654459000c00c0864001e41d115541c0000c5401c022006800103215030354040034008094050814103449181d41c901c00c51040d4100a0452001b041100d403088240f81800c0100800b600d80d200900d00340203064100684e0460058000c032000310794907160501c0b40d1a803a951143c0905201d981e00d80030081218021049150003a03020410f10030401d00520610102c0003580c9044204244041c144a0841c0c1212030721340c3c0aa00c02201807c0403510002d4540358400c0d00325004104048064081107443c0001081c201c1c64010100b0020480d00070107c0101100581b540f01101456031824200543c5032400d074040d401c001d04001045a0b0902003400b40c2d4054020b40000c1500150342011600300d030b2002c1b104a0008115500308400c6180c02d01c022114202058292 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 874386825 1250 874385575 874385579
    0x10902120303040f0b06190e060405010f08071a071e0b07020304030305040b2d0403021e0a030b09031201030c031a0f070c030c050607080f0a110a03020325021e0601 72
    0x104c0000c036051070050310b000c0e80080003510903552942c03842003170b011074100020059a604591092403809481c0725101c6c9040c04004507a81910854402c01c452207180240156450003621034090f00b20140c401e1480350041000e90042050558850400199858040f8440015041400b030070b0380b01034282d40464104201c100082940303c0701795026100b0240032070f50303520711110801c0e4813800982c05051051080504948403070341c01d180030b002104d000b07850203080581324000b00c901009000c801c680e0721020040c01440895802d064035039008500208480c5005112082c0704980341c42640100ea944a01240a00800501c10031184140f2280c1c00152001d06000c1c203400385020008109004109459030f240c0300307042c42000c0481c50f5a800605480c00f606200400034141081200c4501010305141d003c02d1110300c903485011380682c03035665080d00780002031500f140a58000f40000c419109200c01c96194032036400843c0da4034007001e40080081402d10250894a120500107000c4150450001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 874388075 1250 874386825 874386833
    0x111201031e02090609060d14030a14040e0f040314040807060e0402030601140306040212100801140c180604030203060703090516050a150207180b1f0e0f0103021b01090212030304 78
    0x220700c0d08180120750940e03c0755614004a11821f172600c0340608075407080e490b4aa0040b502000610340000e5540c0d030b900c0f54214010740408144524401e0200e001d4144001901c1c07100101302440d0020302c00c0c03420003040041034440c22240d402580124529030402d110420400c1c0d0804a01001400b0684080d0300b50f151100010f405086540d0103005080d01c0000040d10350782d2140e04941841070406200d1209003000a4440030b18075041c0176142580d0328102501c4011188802035612880001d01114600740601d01158051082800340d5074200e40203100200c0183d80611916108204594000450100a090681c5454521080785820113080c91092010303403105408141500e80141d45007078541c0c05080108d00d0301846500c01c0d042c2c041d001040d00100085500041d00050045801e890007d020308002401003248280c41004510103d58170361882c18000024491800305050041c201f8100c22190758418010b228140110b0350f40320382e20811480c025000304a0031460600850940c03a190303403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 874389325 1250 874388075 874388089
    0x305090a0f020103021603030b0907030204230d0804080a0b010504050603030702040b0a15022406060d24062703050606090a0b06040e04060e061612111201031e02 71
    0x2201074003420904042005590094040300d0328920701c94078001500000e0300b0020014550342400c40d00c6508181d0100d0019403190007500c042e03c00107001c0b070406a40c0e40075808441003112205c15080000c20803001d0101b1220805003005001c602c0c058400d01c6114038280c255081d0507008548242e00d440113000b002c0e140081a10515a41660300082c040c0e03042001030038451090748942c0d41c51103040d070801d42041c0c1c08200004143c1e03000c040d560041c8581003041c0000c035000c582c2550090007e0069002e080c00035049104064008401c600d00640c24001d00c24205074640c10120210701a040504840074002c43c1c102c0c2d40400311544e9942c507900755602c10f80c403a880030384032a00c42c61001011a01c0e031241580400b0200f64010183c950f116582d41c40760150302c0c0c080301c00743e646500d429248040810089070312840740700d5840d0020041542e4004c160703240c0c42900840d10f0410380c2c6422039801101000d004008030b0341c61812142507985103181505002101e14041c1c0100300d41103c1440c01a00d90300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 874390575 1250 874389325 874389343
    0xe0405160807110606060f07290c07020f091f081b04060e0601081023010e01020c0f01081e01030809100c0f1e0f060e0f070503060408030c130603020910030509 70
    0x1500656150710081a1080030300682340054000118a082c080608098244080e40c40d843c0000c03c1000d55121900c000017030052000194120a0300c2c04032101618002c150180d01c80c1ea248118140c0c48600d413003010103030905400c2182241e2003070768900c1c0803c075103110240c1884400c587c1400031500381140001d02e070001070400c906000c2e120380892403800c060903900c4003030700324000f074075080b85400715140f503004020070049400302c0c2d0700c5c403060741041d40b0100340a0801c60018003804d41c2042d2140044400748801040710610820017624280344143e005d006a0085000e0504240c03280c25500802070244200c07880e0000780103020301440c001608028080b42c407190824400303407003400300d061007201c00d10f0890350080c8200c00411220041210552003042c42d5541e4000b203c9440140e041718554450840c0603da91603886400010006242d8800450f4071000c1c0c002c0c0701e41004200c00801a032504140c004170040303600072900820900707091b11110110203007483c040c001400c02c050b5054a4a00c22 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 874391825 1250 874390575 874390579
    0xa0204140f040b12070609050d031d0105041d0108011113033c05100e030d0902030118050d030b060307050403290a0609110c07060c030e0405160807110606 68
    0x66290201c803941e85610100d40035501400c0112044016030071985c5605860040c070000c910502008100c60070a1000c4011142e8035442d11690a031400a160882044803044581041400c11010608900301c000381c0c107403a9441340d00320310554100041e05084d01d40004c0c103104c10302014800f16030408108481d0501712900440810b07240b034143d100b607841d5041e1040c00c406409a80681c0c0c007021074003102035014294000c0054920b111080c0b200d102c2a02c0c8110803040940e401401080e200c0c649647c010040d035803000700005940107001e8100c03008880c510340180c1d91034100800d070358142a018000c500521404880c094030750b241c1100041d0480c0198040980f96101a180e9a0103002903071103030100c210000000c0075202c2c03030806806d1000d00814050160440e0601203d01c0d5401e02c800c05640c04d02d8400c1020340140c0c2e0a21101300e51030f140c82a41501042420043c15100b511284074a42c00362075512000562035800740005040440040d003808100702c080300c859181c0c00c0011a000381c0022003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 874393075 1250 874391825 874391839
    0xf100c1401110f250206181305010602010e060f060303070312150312020f07141c0b090d030608030a020d180306110c06060d0f060504020103020721080a020414 70
    0x40400c4035006200401c5410702c074040003e00b20b203240400d4405001c0c031035040780441185403581c2880c0713403480700c4da880020340080090011907402105107040c044c1070b80700504030a0200c80b8084040c4181d400c00e074410300250b5900d09400c050030206104817a0720528680c00e4428900708040403e0352441018000740800000d4280d112030a59940c002c0049070303404107035106a9584904013a8009081d15080d00c015204502d181541a00301060020465040751650398054071044148288081c4240005944a1032100700f88006410200185d00501800009002456843c0e00c060101c40c042d80000000b42e01c24040b18000d6580040c40324070a4030395190400c50030307c40011821202c00140c10040025040589420b50185000c0c003503c0000c1c03d0310111845900e980040c030104604858014125000081001012402c01d0308060381086c810726005240c14041d855410ba1160072000440c081500c25040b03c201ca5032142005801c011140c030300310b1a140c50301040d03280b01000401e10074002c0305 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 874394325 1250 874393075 874393103
    0x2a020f04020d0504141b0f060912060c0711150703030b1c0305030f0105010918050907050d080909060306160c080f0c0607030606020c1e0415140f100c 66
    0x1601d8040c1d80100071002c5007400b1900703103031501d04e0710b5407002900000340c0d1240f0001e0919a010707030318a0711003d40000c0e0141c940103040070140f001c1503202c481c050b42c00500740b081240c030110041003410310416141d81d40688501140c070381880e039410b01c40e40e800c2c070480201d001c81110114010454a0450381402c000841c1c1840c1004244068441c180c0308100391103040c3c011003415000340007148101901c01307902006d41e0302c0b24019684003d041c00b0b482480343ea111900c864608580d484144c0156400046450040d55440028504070380c91004490b0504042892101400e1641c040c4d07400200c1280076005e1468440d00302d841500d4920044810004141c2c1c4203800d00c07140104031020020170720f5046507210851a252507480b0000d90b190b800081c58843c0001e007841c4041202c080ea404001c00380301c49d403100d0584624245c0c2a85000a5125a039141604a649650b1410400400811048410b80c240345000c001c01c03000c00a5015000710515070350306004a41c08075076008502e62080c64007070264 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 874395575 1250 874394325 874394329
    0x409020a0801180218010b07140c1504030b060f010516020604050909010e061302030a08030a02221505130303111608010501030b090a12030b040b1e012a020f 69
    0x414558850704540d440c1c0714000c4074045080140f0b4024134000d488020100910700e070000c003011824800c44030800c80c00d000c002c000481480645403508040c1048172015801000060300340c00750040c1c2d44540901c0000c04200f04240d030350074580d1080086500c85c501030007210010b4031600c5000350200900c00d4502d503250440d134690041d40c029000c0030703155440600c1c100507102e0092140c00c15440d214441e103800240084124207400000c1603010b8054082a542035940051a030805041240e10b00d4007400b5105609041c42ca5001800800c100122411864201c00f02c1e4009400c001c00740402104001c040140407151a0310412603501d49044100d01c1c01403004941070000004000111310501d4400040c0301c001500b085040c0c0e4000c2041c400a0b844041d1003d80d40c00c4e076914000d1010b0165001c00d040b20f8003e5205014180b0090801303d4950310000019054001d013000f140c60b12500a800640e565034000c0d122500c914145009000032102128801c8501c04c41c000000c1c8110f0542002c0ca80381c1d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 874396825 1250 874395575 874395589
    0x11d030a050102040306060e09120702010c020a0e1e1005030c1003022208010f0e150405120d050f15030a060c052a0f0c0a051c170a090b04050f040902 66
    0x11a421070000c5403074648a1409201501451244120003034000d00030840c585c801003101550304a120300c02a240100a90064030071032040c2400780da1200d01c0a1000403141c02d00d0740e13014403030550150140f508030075181c000303002040090198003040c4070340070040c0f0407614005030030850b026040322a41c109080604080b0013a11500c28081e003006040d032142d208d010030b440d80d010290741400c4001c0c48082c0711995100308481e4054a81c0e00c0642c081000381c41480c1e4142440e94100f0b000c0d00a841c03170f507145a00980b4081d804410008442d43c2c0e40d20402a1000d040500c40c0d8100144065031038038410342a00207a580c0c140102d024182e20380c3d510059038030038019003c58000c000825012104540002e695094011f480b44002102c0e000700c0007520084000401c6442e080e14008000321955070414060207200720241d200d90304075143c54295103002c520b0a441d1032046060604083d0b40e00e0400f00001004034200394000c5c01c80354070620040c4519070f81c200ca55020b4000c15500001c2c01c000500005000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 874398075 1250 874396825 874396843
    0xf19061a03010c090608090307110907020f0111070b010b0316110c0a03030c020306060a05090c0a0c0c0e01031e0302060a1a0a060504090b0d0804061b300509011d03 72
    0x41580303400809598180c01c1300e1182e0440702e0940300d90995941c0d00340443e480344107204008002051440d0580280d00d00710080b5900040d031441291054544000341c9403c550300b0703a1036049403190106843c0100890b0461150142042440351411420070322142800d0058618003c02403140100c5490403030001004101800c4200412200016030b80b8100a00300801098069000c1e018403400540c50b030400e04004021102c02070705484040c0c0d120400120990007034041101002119070306200400d041880da47e000d41400c0240c1c005a52441c6000c400d0140e07928cc240c000c118040ca003250100c1e07000700365641c0c0001001000705000040c40c14240030104400081d550100c0d620034041800e5902002900940790301d43c40801600400f24100181002020001070121004010a0180b01d100e043d1102c1003081d0840200520f48259a801590304902c1510480f141200000700d25814102c0040da01e01c495542000f51030060314400091811b03040c0c801282e858540f144421100751030800070740317007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 874399325 1250 874398075 874398079
    0x60902192a080301030b010e060f0103020f090d0501051012030e0d111908070f05030a02040c03021b100b1f0c020a090e030c0f0c0108010e04240504050f19061a 70
    0x81070150318051002c2d0b0020300042da404403820b0004140d4007042c110440c02820002c1188070814034140046002e984207810502406506005452090711022520204a8868400410300b4500028006409a500d500006840f0001c3c80890003098001043c1144090241c0e28480f2040d654101000401030300b90b4026040360018550440e070384001e220f20b0040d10648001d40306042d90b200c00341203051040c6c0c0952581074001125071030062525a0240c004820035040140c20612450701d0040c2d140c00c0340c1501c001d260003810900d4a558040e1140340c09440341113440351007200c0303214a6058200760301a114020f114030b01030b000d425942c51040f0b50300186503201d020b00140c04050312003030b1607030484100d648961043d80218407400801260006640c20107130755031000c03a864203625460102c4050700580300d100ca80041a07644600041446503030340f05440c80030609062510b400e5203040403203800303207074160000288001c204410341240030a07103820502c08542d500000842e015a0002586d0342a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 874400575 1250 874399325 874399397
    0x1518020d030309030e0f064311180109091a10082a010f1106330307050f0a05210708070503280f03030501050406090219 53
    0x101981600024250fa200342c0d201c1410382d044000380f1100250160341142c0c032401c10700c40c00c1045441c080c82505000001e400e154041c0710341d1000c00740300c0c10164038004d0050b00c0c0d864000040c425008912903080b0780a031658590440d00c41071001e521070060240812003038858015000f801120a03d104500508280c0304020303040101d0170f807a840d001442030010600600800000d20031681000c6103d03181002040000055040011030710360560007001410f021621007071480490b002c2001a105030100880c0d2034141e24001030980c441c400c0b00600041e403501d9100c400c01d994130b02151500031100140c0b02c0890240d5194005481d021f400d030001604040e072000e242e48041001d60403400d150301382c0815581d01c0340e01c5800542e03d5511a0058503010707070028011640560a0f048035114840304c2c92082064040c007507980c0d0f1141601c040060300000d80f0340780141324900d454440c4900038460f06d0021442c20341e14062036890400ac0c01400c006004010407215401483e000485e248110108150 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 874401825 1250 874400575 874400599
    0x30c12111c022a10030b030604170c0d03020a092403050c09030f030a030e061e1e070f091509030206070606210b010603091515080f0703120302030103151802 69
    0x10b40319100080000d01d10071813011001c0c00269020740b20303c600c000d00140c0905266a00c42d01c90b081d07510b00c00094244201c000300080340011805200d0451000070b035a40c0542e481d440840020300c9404035801c900307002d6102e00280f84088212403008d1600703d51504001c40c2981d5207403a540c1c0e283c001c802400ea01130240d10030300c1c04504804401000c00780000e4804201d0002035200f0030340d840d5401c5510320709080d69040840d0701d00c80b1f0165115800841052131060341c0c1000d03500001c98040640c0c0d00400b11380041c1003035035542d030081e03808400350901003103092020823041401400d5042c1448041c3c01103c0010305e2205103c220380080303028101e0303400d4810040c2418004100e2500e0445010341c6d000d421800040b403050f100e0b0050280e842d80046441480c10714480e480310040c40c82c1c01c080f100580000c0c00c0000c400c1018031004d1821051000502103884c1345041c504284a1900302c01410584108014400648034042400b01c0c07170301140000a000d51200314000e0314050b6007078003a500010004c0c039 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 874403075 1250 874401825 874401883
    0x1e0c0f030c070608041509060f09032105070f0c11040509100e0106030b070f030b09090a050106211209050301021612020f06190603080403030c12111c02 67
    0x6124458030758080703401a41d542c0c403040f03c1680042e50014000c00c104200c4c455080002c0c0c00032145036004103400200b444412031850202c407000101100802c1c002800115500c80c00014890490f00741c00c001d2040c0c0c90b209030010a4a69111103d406202c4883e21b40418032000d6161113020402c0038100f0401e5040400c80c40d680c1d4a10030007040100e504100e800508510103002d210201c82d0b01c81d80c029040c2c0c036011815100240d400824804041d603c0c05c030401d0a03a00c0040c85400b82004401034810090103080c89800d5a440b82c2290085c43e100c1032340308081916070807008a105030048042802d41d210741508482600e0280e015030b91641c00070030049032070329802a01003c1c040c0b094002d8603141440c0e01c000e80e21102c5140041255410000000f07410000700350070b4a22501c8591000504291241e0b1420104e8002d9001a070008800034451f508120f0080c000844070085828006490f42d01c0b40e41c5650348511142d48044040d6509080101241c003c01201c000d0b132030200c14280200c00e030110707 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 874404325 1250 874403075 874403077
    0x14040b070c1a07020616230d0b0415090b0105090d020f01021204140a08060f060609062a0d0c0b0a200a11010f0b0d1e0807080309011407051e0c0f03 65
    0x20302100d00d0740186c401402c5c05000b00e681c503964000800c006008401400d8009806401c0050012136060b200c242096a558651060101c5071844a09a18008e41410503600880d1007094580341844020800c030f4045903030f000e14120585504481c0c14064030403500040f418450b8070030418603400030115012888100310a888010315100b61f42410320326640c1d90f04165101c0302503800800e070100c0c1c02c010820606000340180b81400010341558601000e103402c0382c82029094541a040070311510305001008414404903110704074514008010100c0e42d2220488030030701400e402c50450355580310800f0010725041112641a2404aa0b5260304030b100c005059200d961900800a5281800c03600e00480740748110440c07141e0185c22062581c3e802c1d50346554220130030380c910b506071034030300448400100c3d083d0041c10001e1107501a50340341d0034003000480c25a403644880a58001581d0b040102403a07001c41690340d80c03801c0c80c1d4400119204808130401500c00c0d110003244074000c032032040a11040c004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 874405575 1250 874404325 874404331
    0xd030512090d0e2704051e060402091b03070503070210061203120509031c0b0402070c17030301060c03230c0f0c04020307270518010914040b070c1a070206 68
    0x51580c0040c070a400c1c080100b80d00d03102801c0d007800d605085070a00700c2009104d41c142d2251142c1c044030131010084640b11009042c0c07402d40000b66000704200710031070070030172015600700d140f44520340d1038441c0024204100713000041840d02000740100004014604c2040340d0a0920018441080081d0b203401d0060034440d0208002c0d000301d100e061404ad0100c1076846020b104001d480091403c6c0b041403140144c80290000e80b105d612502d5025660550381c8920040c060075100c0d0058614040c035006400d83c020031003105a0744503400500042000541007035005034119850301d4190803105120341d01c000112040d008600040d0000305400704000c00002d11224001d1550301150600c94522041100742d100480710400003590046c500c0f400618010142500d8180500c041400580ca900116842005010300d0640762181440101309030202440744400c588000d41e2000c41390315003625448039044016012204005403044007009000c85400001980100301000e03ca00781412031001395200016 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 874406825 1250 874405575 874405577
    0x2a060708030a1820060408070806090f15072a03020303180109150c12020c07180212180309060c0102130e01030308150f0d0c15110604020d030512090d 66
    0x210342c5010f8200c02c503450b00c209a03100c038441a41e0b013586281d070341c0b020b01c0e07038100c3d0781c1c2000c400d11000c40d02a400384200809040060000c006a04c1d080c40814649010900c9258007904042e485103501050030300a60780c00191410b207003440242c0640b11004100380c85060340001e2112050810130035030b02000440c01845070f01e054590140312100a1130890307400d1580100301c10b001c04400032000080e900003c403102e9950030b02c484071282d11003000c1c0583c1d04c06082c010303a540000d4014054100008200c844275030700301d0300840c200b800517039020086401c080d01c3d8481c2c001403030f0f240101104040085840611010388010b03168001c8601c1d9601070b421070000c84510388881c0c0da020800319042c0c0c1025040300c1c1c0583c0c8000c10707500c6402e202d4440b0052071245c640c020704d003e40c0500e0741da04c422010258540c4900b134140200382c40c0a110b03a00908000e4140010040030400e26026040b00048494005404403050b00d07100c40245000e649a119242e8041900341d01c00b41048128078011404400e50106 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 874408075 1250 874406825 874406831
    0x5180a0308010f0b0408031b160e07080703020906090d0503040f030c0f0504020a1d0a0b0301030803180f070303110a06050903030405070509160e0136172a060708030a 73
    0x102d11100c0105e00690003200040d601c248500b4007034041d4450710001e103400080035102107030001c90380425110403c0e0040f000301c0d010701090007111544103200907440303071080ca000c5090140e043d00291041c410092128421105543c0003028030000b44210340003001000182850650349140404200302c05204841007041c2c80700c3c0c0081e060600303008584901c401603890040e02d80c0a0544100d034110354208081e0403800881020400080341001107000e14040c20441e0348034540150014001c80c07110540302440d4100000175050340130b0015100b01074a038941000700c214400341580625115a1100161942d03003800140b10500401000a6004900800aa6409944403001c1c85442e0100303503a0b100e5580342c50030300241c01034460b04159440c11070524190510040e00005914803000e480850f44021400c1c0b1083d11640980c86482d034000c03c0103560700070303841c03611001440c0c44c2e1200c9141c0c640000341d9581034400c032522112040d603072083c0043c103c0c1e80f40c00319400c186c00150001c64080340030b10305e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 874409325 1250 874408075 874408079
    0x303080912131409041a1e0c07140f120f0c0607030e0f1912030b10030f0b030c06040603110d09030207090605010804050a060b1306150e1801060305180a0308010f 71
    0x4088113468481d5800032000740444000d6003c01c1d001b402c00800d01042840e07255104c1c0764403418a81802c0c0142c000b180d0284d12041c1ca828400c50915511044107050b0b8803004c1c40801c440b00c0030803511111100c83c10919120b40508035031518900c0f501200c000719014480422102640503402290b14030f034041c1c12150403080b2214059680c080d0168854290013a0508603400558011110404001c031031402107504110fa50104542c060507580d0303100460b4440e454094180440e201724440c00c4004c030018070488001401081c00307445180103240805813681c06518007250f06000300e500c900d81c810000c11407080c0704d04000351541001d01503643e543d42005d0303000501c0d40c0b1480210380143e03040400b60035500155a96000145500d2041d0341d00007500c041c42d48140007403803040784000c00400a4441800001c17120041c5203c1d50354040504c10020b00c1c0a01e41752020001400703040d1070050400040580b103540c1381c6104a003400c10070f642c551062103d11400c241e80015854100c0c1c0040c1c1c00d041d0707025 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 874410575 1250 874409325 874409329
    0xc0f0f06111f06080d0305040b060d0807020d06060b0f1c0506060904050a0f020705161a0d090812010305030d061502102307080f0c03060a03030809121314 68
    0x71098290344080e68840009410910381600c84001e07100240607002503243d9036007101c50b04101d01c407900b20000c207a5030030400c401c0c0618170380610382c4403100b120801c00c5103046682e042f070345000e00c3c00040e01035400741c02c5000801070103a10500241c9a11105240c6480c080080400136921100b0b4940e0200807506a90403000c10601481cad02501c4018500d9041c1a102014030004010041c861070043d80c4a14400035040400d20050401c0ba00890240082020a035182d06a1004650011244c18a92895085194801401e40781a0003881c200450044c2c1c140c2000402c82c00740c40a8070190109182c000010045d000008101820307062405004580d680d24403100700042c05100c10380541c000143c06200c2d240258000403140c07110352000d4003440d5a04813240200c043c111040004614500140a011002c11841660040b074050240d403862600700e011032601c0d04103120003018480064081400006c043c040004003100904005854550702c1d0f8100b802c1d04c0c6288190103182c90300101181c854 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 874411825 1250 874410575 874410587
    0x11d1806090d02150c0d0924020a0201050f04030c0f0804030b0c03060906010206061509030a0f050601080601170d111903031b02060c03060d022409090c03070207140d0c0f0f06 77
    0x807a002c1544c1d0b420f0103611120680540702c00340044501810703590390040c00d291064410a40d044008c40c0050301c0302c01d00d07000039003110000b80002d000002e03c001007000003075000c070011443c5544055501d0881c1484c0ca00070100b0700641d00010710740c54066042100340d0041c80c0143d03125200403541004c06403540d0006a807200d600351800e5400c030115000c4400e00340b09800080044080103021038200f8921501c43c11035090724400100c4480e00700000401003c0c200b08100d038058203580c0942d84441c41e28001407079940c5030469460040c012806102c3c00f00d0801070003200821040c48410b107181855500c0d00400815440c0c0d041041c178150b0244401200e03200085c0c0500c036800c8100002d00d0b54940400b00254518440700490b4002c1c049900082a0492030071824224099084640d03182d00040007002940324006100c00003043c5c041c13007001102c590004d040021110307122216034001c50b2100108241082e4004090040300c87c0441c005a00301c400007540d011520a42d41100301c481d107d2008580c9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 874413075 1250 874411825 874411831
    0x5070807021b030a02030f01020c0609071404110409020c0703050d03020a050d1805070905010f06050a1d1c0c14090106090b030910050702100b0603011d1806090d0215 73
    0x103a002c441440c80180400244542401c0c008048401034501350b03001a20b04010416510502d9402248062005238100b024641140c00303280900025401c040794201143c41251920b807080e6151071000d50311550712801c5402810000d4411b41d5100d210700a40c60341e0391740504c03040b02c06e44210310a10060911901c20784a10074066070340c1c7c2e03141c100e10800550140c02e402450607951440c0c85402d01c0024010010200208042c03030000c11590b140c1210700a118919034002402c0c06010460211820750200c0880b144140341e5682018240144000c140d03070741400b00000020025280300c4409100780c11150104450250021400340c01c1000280507801c81e00307100b107030046800f004061241c0d0403020060b6a10985000440f04201c0d034015000094401c1518404091f8011039624141c4500f035005811030540b05441c1145103502d0034211150300f540448402001543c00d80200744070b100685605120345042c1c0084403124104803d80980301da051400c600c000d44554a064111100c060140e00d00c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 874414325 1250 874413075 874413077
    0x10060b07020402252105042d091a0a09020c0c360403110706020d0c03030605030304030c230d081809100518130204090f120c0605070807 60
    0xc14a00d940d07007031101a4000107943d104a0715000c40c03602210030b40b068022149800307910700c412a240c2410b55402040c0400c0c0c980ea0401000304000d10440c0c0e460b121904510490407400c0d03c0b07c0910b03000d120590034503600b1840b12103007080c0d43d02842c03030168840b00c00001d900315950214555a5110102280324400342d02e00c2c26000740d450164140b40964484c019220b4014110b206000e5489024125103030150072003030b000c0014418002031540c040c607800d00b0306040c3c070000e0850301d0034568043d40d54183c1d0342d6008100461310383d02d4001c00d4425000000100405021244c4564880c80c0003403643c042d034090f820083c04240d100240d0021605030145c81d07144003400c2810404455119601194084481406260b603040702d181c1d42c0d42c0744d68220f41c0c401c6040784625120f541c00c1c0410800422200b0041c1003081503180d003440f01c1a6441000d040700e440e4101d60000d05041c8a24221440b5659000c026066440340034114070b90030340015901b6440c91040c40d04001c10b60300c080060303e1968060b00c10304 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 874415575 1250 874414325 874414327
    0xa12090506070c0303050306060f040b03190207200604120b010618030b0c180910030b070c0c140d080409090204180b0601230d1b0207030302060f04060225020310060b 73
    0x40030a000d03c1c007c581094001e0301c01444c00b00b80540325200ca030b0140d07000100c0c8100c0001041000c0b03000354035401c6490521042135142c140107450b01c50031240e610804088001c0c120007100455503c180454000340000111352881c4034290401c2c4103040000d100711404540c0701c11604001c9035100c5405010b403a40b1100c010401c1e02e42803d4400780340c000c01111860401007121961680e95400f031036a22030403510f0424274085003989805040100301034100020b109260000200103010484d1050603161405810054071210700300280c95807107252005000c51000050125002140340c02140480e4000d440a104501500d110480064400307000580000220b8011814540c071170714054400491070700095540e2036142c0c0c0e0741c015980c00009a000d0f640d03521814103440c0c0416000b01984440d040c00500001459a2001703921217074020b080501604603440000e0400803184e040e0b03100d007444407041c00e051488004034000010420182070f4405d01c27618060b00414051409031509841c1c80343c00070f0f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 874416825 1250 874415575 874415579
    0x14010c02060f0a4a0616050c04090f260a0c0f0b0a0b0a0906051507140d1101290409020307030605040b100e01081b01030e0a12090506070c 61
    0x90320710b500260040d00030002c6044042c0150460707241800e2081c0c4c400c4010b52808007065901404400b007280c3c1868910401c6403040c1c120359162401c1e14004407420308460316501701d929086040101001400783d200c0c0ca1f02103840d0921a240c0204440c2e90302c40c8501c010043c511040400081e50090301210342c4d01c104120416400b072285419086d05441090f4a0249a40079500c04200f60000c4901c0c0d90343d03943d00c40e45010f0790315050031004006d10b105201008500d0400380865000d4030310084010000130b0004030001005480c0b04190b92510242041c3d503009000e1220003407080044111459071036082c04401d810404450314450000d80d461141000c1740344070081400080c01d0500b100b60781c14058135400201040c07031402014480c80c41258107a0340d51030003d000c1d045a040e60740017500029100380c014000d8020008100c01000f40c0400221901031101004902501d0030030104802030150544120401200b42050950200703180c5032241c001e9281c00c240025070140002c003401c2c000001d041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 874418075 1250 874416825 874416847
    0x3110c06090111031911070b040e04020108130b0115120e06070f170c07030906080c120c0f18030706030c140708040e040c0305010c1d09070207050d050102030114010c0206 75
    0x201600340d94500c004c2e00e0401c800d48140002c895181a0f0746404a0500c058004034a80300f03200351805061180203541c24142040308c940c0d07019078010402030500c5108030115504920758030220300310b158060076190803581c603195001c00310800029180b020800c0c03400080c10304080e6004503406d40d803c442c020580c0d5512840226a8144c65541c4442030050200c0600704034a42d2032260f41c41000c03100752640d602d64152900901001559100200f0019018244202c601c8140220346620386010f04541458550110a013010321a9120100f10b099001601e0200d04071907200442c12110b085050703c3c2c003946d030b40380c09406581e4804580c000181c030407010200384221075000b40200e280114a018149500d50205840240c01524141d074440031042d800c0007002001d0040c15041281481c080b481a105c600c0592034103103000b21058420305200300000c3d00c0ea4402c1104000802000b00100307148461030800714001c1d8002c2c000e54619010380d1401c401954041c516820841e13601a100b180f40606841e4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 874419325 1250 874418075 874418087
    0x1020613050d1d0a141f0f030e010f0606020c01031a06040515090312030a051b040521060a06080f030415050705011b170a110a0f03180f03110c060901 66
    0xa260080800262040b0541343c907004000c90180803017640320f20304240703800c00300701441c1e000300c0c0c12503652143c6400300e000c2240d002120f25a000010305001c2070300c00c001c54010b40980f40000f80e070803085c0c0c0307061400509660300140e8661141000e803001c00c024241501c20a102c03d00840e09140c00c0001000100240c0c10038800d041c1c60550018035081c01d11001400180c100704000d0120342000c1d8021003807120050140c031038280c1050300319411291480c100c1d01d00303000034019441020311070b465070112200300c9440032050301d20f8203181000340c403981d140c060440001421180030f02c110740c1c0316000c01001800310010840f070a46896040780725070071141440865031980302400865455480b2100014030203100541409009160344138001c600e0306a81c9486900000108541c5c0c0c06410000c141c2000fa1241c802c0b910003034002e11b801031181310001826009040c501d104810080c03501202481803284400744258007034440c0d59480107003608a40c1d807581c2d80c091600c0450380181c0c200010b06c15503004030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 874420575 1250 874419325 874419347
    0x100602060c0702150c010203040b150a060c0501090c06080a060b0c1009020a0305011803080604090b0f1b03130b0903040b0313030c051c030b010c0c03080903030f1801020613050d 78
    0xd007241000a488500744000385c005076283c003e030f03a4012013030004010521541e654400c0640340c105080107006000100b44840a115840c10310440301c40d0f0800744142900511a000c0d0003441d020140da58a000051401d41c003159083c09036031400030082012800a0101c0e81e400485100410078070010380085c400524180b00300300d90101003d4070001c0001c02c2809104c50302d12184810703103008040b609020700a04001810244224a48540d010000d8010b0017410b4001103a403512000c50750b1881060f0803000c1840d01c194030075406c08420001010801001104d007603114590060f0282c071418a403e940c0d0003980641090003c0a100090080040d50382640c003450023441c1541c842d107050744031582000b0404c03004c0c1d440b903c40006468400ca405004410f0201820b08e08150040a1602d80d513031303825050f0100411160001921380c04940e0304000b5581881446409a90340e0040c0d5094a03034420b500881ca903003d4043c9000040640c1c0340a03114103042504000a0a41100364880480352155070ba = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 874421825 1250 874420575 874420579
    0x7030816051204050106061e0819231e0f0c070c03061a120d020307020d0f02180f010504060614070c0902030a0204031103060603032a1501060305100602060c0702 71
    0xd100c00c511040b0000d2215000d01e01440001507042d04003403004007000102c192001400004500754224181d220216540c440c5003103440c851039070096084600500720842102c140c941d043c01100349110144500c03c1d000701c01b90361003500941444000403019080c1118411410722182c000100403800000080010303d01c0f0b0b00e206c08030591a544c8040880341c181400014008441700070548508049034890b0400341c9000007000c44404100d0004e540b4828802c0090056001a403044100401c810421140c20360051000c1524031220603001c0da0044211056252a2013560002505081910030b10702524426a6042200d4148440071501070b4030000045858103000000000d145100741701a41c02581c0000380940c0e15841c604003124000714000f001c1d48290410424014542d80000441d005c048402450003461034070222820142c41c900405602070703019441e480c6914200450340c03541a19040c0d01d0801c1203032030b004000001d10140307004540160b0300142c0425091955500980041c900c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 874423075 1250 874421825 874421827
    0x2100902210f030a05070203210d021308010e030306030d090e0703051f1e08031305040e07210204060b03100603020903030705070828110108060d2108010603020703081605 75
    0x31081d0b0b02440e503404410700c0c0e000594045180421450b042c0059040045080a0350150138482c941c400098416100c404603499800149250812004140c0b000240450b10080006003005001c1d41d84aa004544c841d21078080c9641d82103085004a841074103031090801e0602c549e80e200398050b401010090500401d511091800f004e114212800c040f014188001d00000289480360020f80320400c160880b1010303400602c00c9080c458101d4068008880341103e005c55105000e02d091401e00100d074001300f0707440c80c0c5181544042554200c1d007000e040d2003685e04010f02ca9486041251902082d00c4420f006c4030704400800c80381d0301c00c2e0013800303508500400f541d20307001c040c0c1d840e285000743d00d0740b144c0060b800280c3c080750000303440b25516000d1407014844099004c10703990350300c41c1e02718041c44c1c003070502c8001c2c004a94580c48525007803660641c0305c5180c640b080048013042d2212425425800700292480e0000700c0c006200b030098450042c2d0544807642140c071170075201c2e070060f6003c01010003000700c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 874424325 1250 874423075 874423093
    0x50418060507090609080339030f070b06010e060304060b040632010207081e0106051203090906011d12030d02041502062a0a09050a080705010210090221 67
    0x115100d4140942c0302a211100d01500e000030141000400d5408425030b500103000a11a9102c440402080c0380c402c046c1c403510110300e1140303034142c01e004101c11074801c3c40003043c000c428502070700040071440d00407501911941e4845004541d410083d0603c0c607048070040c80894000380c941d8000b0041030030020404188035440b15849820354940702521540c00f20071800c1854050300040362960400c40a1007c0c6c28200c1c01d040c8901e07504c250b4030a210002c401b88030107500c3c0303c5c1000e500c0380000e003000078420f40c00d103030440c0442940c0c0d0308401d0105129a02860100703000798051110a040b00000190840f001c06140e0200300300c42550021017409400f00700402444101140300074005010340403566000ca00701810001d02e050070041c140034041e103000103001c40014220f240c0962004410000958a0942200032518140035602445e0404c0c40000301062901020882030151a020fa00b22048407600302101820b540304200080d4101003007400102202d18114032440894800c1760443e08008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 874425575 1250 874424325 874424333
    0xd0e06010f1806210204150b0901050a14180f0a03110f0d080309030717030403140c010207150f0f15170f0706020c0f0603070e10030b060c030403030e0904030801050418 74
    0x45140e03140700000e04065840340b4111b02c1d01e407143d5101c000020751411301c0e060511880f590f25102d0404001d0621201059440311513100b08030340e90078020847c4c1519203c448840420385400540d0420a102d0035a9120500302030410f2055801100d80158400080c4488042441071031440b0601486d00b2810909a61001c80c134040000d6028500b0340c401540d840a15040034100d010300111003051141080050101080d4000b41101006840c112081e40d00c0311020030440c028030074488010240400c030342050141c031046a001008040320000148010b00d199261401110f80780000042502c9076504280414815864850608100030080328520050b003200d492030540c481e030041d401a40510b02d00741b23450404404c0d941c003080042d00c0440c00c50401c980050700700c070201c2c00c0c110b00410002d285c541516100b608950380d45c52000c0e01c5a6968408800d6040d00c90788140425008901c00001681c2182040d54500d0b03c620f41641e645c3c220f59007080c0400000e00a0b54003034003801100110150301003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 874426825 1250 874425575 874425599
    0x51503072c1003212f19050d0c0c09020304110a030b040309060503070c02040b0105091005041e0b16150f0c02060c160212030c01110d0e06010f1806 65
    0x9440c158070412201d9195240c2260f6603100e1381c1c441c00403a07056500d080c600c243c000b105002c3c00c14040030081d00c0c07050440c0c82c241c51011201d540355554402e8080c06075100700c428440c8440c050040741601c5a003d4010000c0d40c2c1500d400c1002407024040040400c5002d403164090768016104140e85180004040002100790526800030f0301c0e0340e107040c1c09102c109078110b0302007001003105040690443c40c1ca844043c0850080c0e000290007117458995240071603100320100c440c0c40c80010042800c0f4900c0c030b00011700b5500076000b074411004030000c1e00352400a03500d0515080b2001e0100051a12000f00541880102032510880344000514050184a58540660580482505070000c0c040c2203154000b440c3c144060104060f2250400230050481820f04036a0032103a0180c0b00d05074908000407007e440c5d4407a00010704001d52824030114040c884070740c0140440c411880d814454901003a26090310750400384200303c0c8400395480100204070782003a900840d06040b00c0001105940d602c030740c103d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 874428075 1250 874426825 874426831
    0x110619052e060e0906090606030403121a0103050f010b0f0c0102431e050a1e050d080108060f04140d0f11030c1e032506051503072c 58
    0x60758240e10000e000150344a030000418860480703040700f60b4185035000c907031101d10151019018074170020000d420325001e080c0303000a07141001030801c20040900741262010f02e99924080c0001d0814000c102c1c5043c1451020381a5800700410b50b24240301021030504603403004083c200c140d5000d00c1a108044284d03040c00c0340d85955400040000084880b070003200d000305045150117940032050f0385010602c1d81002d40c0c10021400003e036829809400d0480c6803040c2c0c120020001c60794440028883e140e40c0e164854005e2041f030440311000d4170b960094480c24000d001c0d2a4041c0d01c02d0001503490144007400980041c091401e10284000411015041901c0c003500c01d40420010901c1c0c50501c0c3e070048010441e03021540185040001e01c6540c5a101c001d00041c07007120288840301070303002c0034040c02211a03032000030041100c0e84450144441d20562120780c242c0d80303586000009086201000003a40f51482c00a0260010505103126540000004800409060400240b13141c90b000c2600d40c0c640 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 874429325 1250 874428075 874428151
    0x910020102041409251205060301090f1b051f03050112110f0d1407050901120510020d020f03090a02130203040b07080903041509232d090705090111061905 68
    0x141c46d4044499160a42c1d40280105010b0380c5400340600c003094028940310591070340b082c0d00ca81b81c50b1041c0340c00707100c90401d070300720a51290440c2402020780301c1c0640c86040710502514180701d1a80d075280804c03400b0894140180111003210a05165458402007180c0f10400080000c0060483e6444032420103d40c04255000303603010801c280201c3c80c00e100c44a006141034801d0340c095006030359501c0d031121015984008280c2c1c006c070700034804807072540607258608011003c0548910f4160820f41c1d860f480760800781c0c040d0b092502c2d0a410101f10f80203c80c07080c0c0d041420800316880e00b210813500b1042c0180000b140340000d10000c9681c00003000c04082a1142d40c1e5460081c905010b040c0c065050b0503007665414103850302d40500303e41c4a50b009a100072500746180d50319450030107a030715800c3c5004c484c01940040814200b04040da0001d01400b01a2000c0e80c0e1081c2d21001008000c1d581d070b105131007a1001c03400d10219042001c5090b000349074404a1000ca001103401034080e81da80308084612603030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 874430575 1250 874429325 874429337
    0x1314041404080a090b0408150c160f030329120111040909030210050106210e071d0603060103050606040b060712020307151104170c15091002010204140925 68
    0xa11101d03030013a24200030340007a00c1440e26051505c406c503a42c1d0071a41008140c04211300700010b40e44803501c010354a06040104802c5d0310a11240b50a03031101c0690041100860314041e84010702221645800750800b60316810900387c0301541081084005034040c1002840d03480340c03a0030329070710f5000d4043c200918107503202240e02c4000b4503002c1d0400741d22850baa4081482e0800401840e42d0100450000001c80c43c00001246442460400540035040c802500c9104036080090000c0214101010204800c0a00c8150382c46e20410036403075078006c0c88090700a90003900850803902d802e500c0900d03c20300c0280309624101555590014280320340500d0f90158201061b4a014000d50030b00e140f44040901030704003da01c414404070400f6001d1400382c1e0021282d0160714120040040116044540004040c0300c0005056121001781d0707031116443e54024a1104841c40b14035005001356400c2d50b0103000c0c00702050b0650000e112400400810346a424040d072481e455071040d035004404c811402c10740d40c01d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 874431825 1250 874430575 874430587
    0x5031f0b0a020d0201050402030709050601090b0f0d0c0f021005131a1605030906070c24050403030609090b0612160e091c0e010309060605030d03020403020405010b131404140408 78
    0x6400c2c02c5080743e040d400d41e4141070802c8010b0354080b0300c1c58181c1d000803900041c2d036110280101e512070b4484c0c02554040300f000841d00301c02500140071706680040c0c60814041240042001c80c6d0212420403400b01585c007200d81800c03291802c0e000280d001c00c011040d499002c1454482104800034002c01c8580b18083c07400b03001e001840403c01207404070103030600900d9400d158600c0799541e50700910700000c001d00c0d0b1500c0420003203012184c84040d01c081030340f00c03002e10300483c008008000594041300420b1521500150900b05809a5030000c0d8018483c103003669030310014032407500040c0a01c05007500945414044807001107440d280a08802070b4013405d071b40380c29000c84c0d01d04811214101c140750720725510030b1031007540800080c80c102000c2c170f4089180103040c9440000352010350031083d414000c1070030302640340343e25601170801c6038001c98003400740c3e0b40e80e00c00070302041c452800f419103826090300c0f0502110308070b001e19800043e0058000250041072100c9801c06400541c5d046030b01c11000211 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 874433075 1250 874431825 874431827
    0x117070e04090f06060f30020d1a07210e03070c03050604060e01200901111e060f13080f070b0c030402271501020a050307060606080c13050105031f0b0a 67
    0x42201030900c002c202c031b0920b07041040c0c814036003030390321a00100034211004800c108000000e8002d082540a40f941e1062607480c503181402d0014400c205248081c1e600003c0c1783c41e88141d040c40c03d403a442424400240703016814850107032101e0001d15800c4d00c01009050f0000303c01c01c4070300000f5030260780a40024102840c4c2601a2550b0b1003451030380b603041c101020b0b401ea040c1e40c0490f40c08a013804640d5a500c0701200180c3c0c4010b00031594003041e000b8800031450380c0465142c502545041c5005581260f5103454000c6c1c410075050b40c0702c1100d4444007000f01300060740380d0300811800708011482401c0000554804040300011180030303801840c040180300c11802c0442000b048020500041000e0000745c044800f4503000081600400403205c8409092590007801504c1c2020707045003d4030f50342c1082e420484041c1810384188000940c0450014015840c04000e40703801d04c1400101d114a00d140400440300ca07080a02908103d200d49501d2164586100300304400070402402c42544071480342d48 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 874434325 1250 874433075 874433081
    0x10031b0507080301060305041103120414060c191407080c0111190303051e040614060a140d081902010606270e04030e090f10050d020117070e04090f06 66
    0x810024820140309901c0040c561005613410341e1070a1800048030394550515100c1261b84000250301402518456092141c0400040046d0b581d0003201d00c5540c024541030181d2440740b4180b0350030580103025541629890048464842c030300039410b401d903011030350040c2030404900781c0c40004103500c207004007030442d60801d40600c19420380388042c118081c2140b071034030442685007000800b00342c0d45000144250a00c00e0720541d40c18140100c941140c50186008401801410101488400c03004001380061801d441c04400781d4400920340d0b24250050300911007200d1180c2c900700c0e00044284030440103400700c2d1f1041580c001c1070350f00100740caa19052003c0d0a10402490220b8803202a0705400703e80320346002d0341d008a60100c40303002c00b50340e0755050031034000000c00d020780e40c440030039014414442011950341c0d005280b00701c0d1807030340c5035070f1581000040008034600034080b80420301304440a400309840e20354041c225050131001e0942c1c100010f0200c902c0b8400455021410040c01018018584 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 874435575 1250 874434325 874434371
    0x1203040f1a0c060f180102040b0306120c0310110d091212020406052706070b010815062d031006031b06020309120a1b230f0418021003 59
    0x81d481460801000e42168070780e10000c0034060051812404600c0e10900c00e6829801e842c0c0c5500210b44554442d00030710015482036030114424440e410f41d2a5007100c000c10354400090004005000e0f0100344070610000c2c1c40c1e2040d225403041e800740500c19000d84140282d0303d0680c401d07800314442420102000d04164149203006040610503c014009543c0240c211403441c02e428000b03118080c003042c030b07040c004180c101f0315540048006c40c0070b0040011072030383e89040c0c5082000740e030002400c202071510703102400c5540c01c0e8085251710340c010014040c0c1540301246c100b80009018410644408203240505030081c03035400c41d584000070018062107802007200385418915035800c1905d08140250340780148030960f0301c194904201e038250180108040c070850307070384443d041c65030000050701d81e081440c0502c00d251107170242080c11589982500b02c81c00c840403004080421250310003083c04000c1040000f1042420421180540540d80d60410349408040c19035001c14240c0c0c02401d00f640d110300d80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 874436825 1250 874435575 874435619
    0x801051306140609040f0c0906020d05030403090b0f1201230d050309012a05030703090801021e09040618020403031704030f2d0e0f060f0403020402091203040f 70
    0x8002481400801c1508549000c0120344098441c0381c02c01c00a80200841002c103d413151405901d02002504236500d00115580c50302643c5d4441d1031488150382074401100d0040029803e14814018090740d50043c090408102030154100440c0850210b5a14001c0c1c005140780a106241c0412010382c85520401481003590141016592641d541da642c1c02128401030500a00560310390b4080c134013014507600d051213203d144903c601c1e01d08103503441caea120107020b40c005010b000000c00c440c0014002c8030000c248250003000445254040c191440d0010100c10f98850340341c035400102c80031943d441072008060081d0040ea1130b131641c07501500041c0102d00c0c1c08000c180d40e004010201c2d03080f10250203201114208810b01400c113030840056418281004d140301c0090410980000707610400c40e140303041d016210340940d00c240ca0200441402400a04403000d00e04000500050405401402c0720160140100340c0c0411440000c0d400c58006411400300000028020040c0b02c02d0707403c0d104c1c0c00c5100d0b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 874438075 1250 874436825 874436831
    0x31e051b040819020f0d0c0306150503100c110a1a010807062c0d0b041a0621070308040b0c010f052707150f02061e04030f0311030708010513 62
    0x58480ea25884906103801c0750408043c02c80c094003551200601c51081200c02014440142c1452515030a015000d002c199a0740385006901503980302c48880402c181da5004005040310241c1680380c402034034902c004c020800298480000303140000304141640310f0f1140c005c00d000403c4081400c905004164041c1c41d003588209801c1040710380155000382002100b5a41300c241c0e82030f8000c91812000306040054200400c0d10342841801204a44c00c2d0080d84681001442c1c80b102c0d0061810040c81a80c9041d8400c1040e941e503002048800700300351005800001b6035480d0b035603035102d04056070440c2e030003072480c2040000d01021001007841400e211a03030484080045061500c1602d80f41422900c511800301c41491607400b1120b01003281000806080400342c80450031108000c0550700080722503401351084401081c0311190145100000c10012134070700c2c0070b07951039803000c8a6040b851890002495507640501e140c9449000007507124181030b4030f451416524100034800111f121108450001385 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 874439325 1250 874438075 874438079
    0x11a0d110d0f0b0910060804110a0303050318070515070606180c020d020607090b090f030f030910050702061912110415030b13053c0f010b0415031e051b04 68
    0x5c40b003408101640e45501e080c5400d40d4840c075014003944e1807480f00591204000000204265100d00110700c80c10450096000100c8840c403800d6031003a40d405410f84c042c03050a640a4a40c40001c007829040d4003941c3d004c54a15602c02c18031014001201210b1089604e4501c0b1800c500d40400103110408024401049685440013009064400900802c848007200003076215180d511040b0b85003c0c04001000e0b1002c8010390f042503662903014260f220302801c4135841e84030405016005580100317401504041c42d180d40203545086600d820039002c001e01c12401040012078270244941145030b5041e04980780c0d00d900f46140003070303900d02007440722007018100490115641c80c0c03a004a00810300d00440440c00e03071140180c881b03101a051800e82d02c10b40103000c10701070111118400c01d5901013196003c8000f5264002c14020042e401d0191001c5483c080104014141c018032400360302a0b01fa140c0051080032000c2c80c50342401c3d1808101c1800d81c0c5030000c2c0035061203042c2a10341c1c0450191100d5103082c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 874440575 1250 874439325 874439341
    0x60402121e070206094b06090d1e0207030f050d1206060e010f120e06040b13030c1103150408090109140a0b09151306020d0305011a0d110d0f0b09 64
    0x70900d40e18101c8840346c812088a07030100200b2003804400420b481e03c0e9215451b0144901904100c409041c0512400001c281e008002190b540142c6034180d440184048400c40600d000c5044041c00d84118820741100201241500b00301112091150000e0600181c00c801c00030725001105220000040c90080c04001168002d4541ca0240d8000c0c28011200043c00741d059400d03003900d080f940c131428100120749040480c0411824070992090401010a0301c074240d0184000d149a0170041c0840e24074800c0c070010402120800312000030003003c40b10140002040140100001d40d021204400c0104a00c0095a009800340010703168280f0300246141e0004000760a0700401d1050107001007002070b00200d00e40395041103d24038459840010368442c850665504403980b10b110780700060207602242d0b081d2520902a80d4100d41c0070103804103030324000c0c2209034000d07030044d46c00d40c049643e0344102d0307108103c1d01d102928010680e200c0001d62076016440e40760644d1040700c00c07a40306007083c4042018803 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 874441825 1250 874440575 874440583
    0xf030908120703030903020c150a030e03090d170c19120e1e040e03040b0a080a0b0612061c050c010f0228020607150504150203040c0905060402121e07020609 69
    0x42ca8044c0380104240d10b00d41001d0f41402c501480c8540c101213a11841049c6502000042c503a45c99507035810011a00418056510ba010310607070079600081150050011500311110b00740c0d4584a201254505a00c08960303515001d0721008000090031607168000034403440f45c2c1c04040550503070801c08800b41450002070180706200c040c100308400004100d1040c2d450350ba1110900d91000c40c11241e80301e0706d036040401550401d098080010f02d01c8000a080823074907002d01240220040c02480c00c05150b10b00c0285102d4004101903001500d41802d0218624000a00800c20f40104042d06040045d08001424540750344d1406040d54811080c151040081c081116505446c1b076094001c0e85040c1e00c00030b0b10b5440f0310301001d090722007000900c1e00f0383c4550364045402544945007a0360b141e0070241041080c0c0c04215009001000607010030040103d145e08841c0d840440180014039000d80e54104180020b400d0328105042042d0101e6034621590240321310b500488903000801030b070714080e001c0d1071791 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 874443075 1250 874441825 874441837
    0x60a0b0922141501030602130605070302100207020609190e0115080105121204080313090911131b0203030603100207021c080d060e1b1903050903090a030f03090812 72
    0x1804085205001001000b400800000921034010f0b00413543c4d01e040040c040e4000b0703c0024803c241d10b1000248445c0580100c585055040e0040c00ca03244400c06c03500001d400a40b000c1c0d8002d4010031021100341e40c4c3c0038580d0102119001c14500b01c40c14a4140000208160803001d401020300203e54200d076008030995044031000c0b522050078400700c01e0b00b603040084004519460110100780801c1c040804800303070400103043c1c2500d4881035075074550803041ea5200c110191101700300500200309414104000b005d803000040c1c01003200d05080c07040040c6500d2220304800140c0001c001e1041c0ca140c14080d16803c0780810900f9401c0014540005071801c1d951052107802c207108450f0b2008100c01002030701e03104140ca000c108030b01d56480301071140c0c400b03084a1200d0030710101201c81c0c4d240c11907034042d1920300d41e4070500d01e0300104007200f0035002042c01074540d03826072006012888140e0399000c040c802542c800d42c0301d40300e186018580541515034507003107503a243d040320107543d5030314451105a5031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 874444325 1250 874443075 874443083
    0x6070203130b0d0609020304080705160e01090506010e1207061b0804050105160602130305060915061203041223070608070e13060605040501022506140c060a0b0922 72
    0xd0341e1903d01c9482c4005146030307481105681d00100c00c00c0103006c070110181050a000c0c1080c1c4891580c007941c000d4170075440d40160800b0b00400b20050001c0c50199001c0c9900003030605080d10074048000018404a00b070007404095a4095130702803040c1c50348071460408501300010158500b0006035903003081801140a070034108400402c400e19074002e01000c01420740d0308030104659400c5480084c550b032081b1404250b60314403482e0085410800009842e01c101001404041c0250300c43e601004181c001c62070001806100622000c42d0351002c0540380350700342e485402c804003d107000c8001440c200c007801d02c1d0185542c02c05001080700c030b900802016030010440c075064071607100400c0055901d10010074115960b034130301a0b020410641140080059480980031501e01031102e802201100e550502080352088080d1801c100c5c07280a4400400340c141010a218181a124030704140340240480f80c807500780d40ca503040c5e802c26007000c945040d00820380540e41508002d510107070555602610708010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 874445575 1250 874444325 874444327
    0x102040506072901030501050703050606072006040306051609050d0b040f08041706060906030a21090305030d0207020a1401052215021018021008041104020403031106070203130b 78
    0xa041d040080700845034080f540e58895240d61641030080c000d0100b03c4442d40840e01d01b8020031075030b1034028140d0f80c10f55880000114034249600c14859440703108041c0c45e4003d0800e000c080000b0b2203c0c043c59114803c00001200f82d03031507805005140c280294403d80c020084920000301040c0070b010400d0344260484010b5840040701d1506055501c03455000445003d4059205841448007080a6006403002c49142030300b030f1520303003c01d40c4916440c580100f080c03245005481c000c20300c0541082c0a81d5442c1080c280c80c03607aa44829046a1040b0f1201020641c0040d01200314601501a2006403610f40e4004c07452040140010700a44074201c01c0c1d254603500320350014245c02140c1400400340c100d40421306031561203000d01035904e5000790b61700d481150900d945400c49030480c03600139109980040014580320315103034045e181c540000c1c05c1501c0e100d0381800a0001912130340010700c021442030362141d0f002c20024250364102040902a2021504100b005140d00c1c030f04c401d44003041c2c3d0403020405d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 874446825 1250 874445575 874445603
    0x100206071803080a0201020c1005100e04080f071b09090809061309420501050d0605180403180b040b0f0c070b25020319060b090405060117010204050607 67
    0x1041214981e50701c02491800b000038240003560381034000d444445032010856407480700d110710140c25035030700701d80d0f404200c2da2969082265402c208525a0410701a040f0580b07490294096100f01c1e900c65407090300c26203116201c4e69901009180f0310710003400070349020031104015588031603652290411281c49504085842c62401c401403600b04018000c0c1c007420001c1c00c0c510207186204a645001c0201040a034151060894401c01a4004009801004140124108401907c50f50070003400511a140c0d11680441e0a450703003041442540341c4500c00c100e080c80c1903c0c1c0286050b260700900355030307251200d1003002000000c0040d03500b0741f5031074031000e03031510161140d801443c0100044c002c058400d000000a00c0c91300c43e00100022403800481e900001110301c1c04041210a8240c000c0d01076210380e04a40350b80100311054140640715001c00304010a13003100043c00010141e90551350707500000010041e010030080c60300400c0c10080c0095003458035000000346103000e032a001429a0362403400c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 874448075 1250 874446825 874446857
    0x8010c0e0405060126010609060c020d0b0c0408010204140918070b09061c06060908030712031a030109060c11011107060e0c0a090606024815031510020607 68
    0x19170003e903504048881004180e40c0b00c4103060280a100d040301280c603400f40851061f110310000031113250040e0403509a00d20a603100c1e001810020040c2c01c080d03034140408214000c0138001040180b480c291420825a66001040507804000c0e020720b004c4103142e1020b000a440c045103031012104050682501ca120326000b1a010380f040c81141400f401c0d42012001c105409039100d074054070020790711301c00980c0c0c50310642ca54911650001400c2c075040529000c41d002d110740c101440140c440c0386c04821444403440441e0035203031015002c07216548c8501d000140254001002c2c918104520002d008847c0c0840c0c10140728410a6400b410f01d50300e862001c0d41c3c001041000c0748135588060702c080c1a1580c3c9006040c0244010b000343d10060090380d603d040590b25682c000105030a0100040f0018000c01c1d51080d0b00658a00c111400b5142c9040410525615407603046800d181c0000300342c3e03a038070704001e40c10030310350111440921410754400000c8010340e002441d00d5201c0d00b00c3c144440340840e6550 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 874449325 1250 874448075 874448087
    0x2030d0302090306160e040c0908190503161104140a0b09070f050708130807030b0a02040f15090e13050c030303090a0210020a020901060908060f0c0a0c02010309151508010c0e04050601 81
    0x1105d503001f6052070011034009501c021498100d0301c00c941520095010a4081c3d000c030100785001800962080c0f040b008808145603800c1080c13446a80c0d10b0000111220114003601d08000c89240e13442080020003410f44082d016400313005004480d90f01c000d281c05000070b070100c903903000d0704420070001141c010100b000300d60450700d110075000140f40c0c4d6240e48503441944c6080600007103032007030880008641400b40d140255826541c903003000040d16401c040000d5038203110061004104140040c0000f8954150001c59001d460107407520440700000303051140c0b5059007014424000d6008000308010040081036140142e80c0c11192010038002c1610103d182484864029500c1030f600030001903810b4002140e402125411000e441e19035482580c21101c40c40100c0e00e1140c4588100300071582c40b4801c10036881264414180010303c0c074400c3e00c038031124840d00054040e659a076100340500c421114141c080061400400910841c1d40c4180001c08868000030303d14055501c81d0003083c1d240e030040b1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 874450575 1250 874449325 874449347
    0x834020f0d091a090a140114130b0a02160806060102150f0711030705060f0415051006141303050f01060f0308071e0206070b040606060c022b02120a02030d030209030616 74
    0x202040020364a602c1e822600e14404600302d4041a0000d001c010144040303230648030307185e075815034601c1080d140071990041503108c03e84510842c0a9804000d02c40a003003d0305034003601642c2c0041c080f03840d0603000685009038029520580d80004810010700c140d401e034200754007012914000d1107188000c0071192942c0030f850001401402004200440d5210a079241c038495801504074a142001e0b50010b8000c036001941c800e52181a840418052940076100404181c0384451000d86424280008800807200540086030f10f40c0040360740202c0070030300b4064100039010f00d000a041903895a581c0c1c180912a01d0001400c0c00d00440d04580316550581d510301806401401040d0f030303440789250844081508840171243c0600d09100032814500c05d00b0218540ca45c064007200440702000800228030410440380382c0800002502800140c1310410116945006c54006100c04ca449104050a00c0c1c2042d28400805d403051000000aa0f000141c06420441c50400000c8018a80d03508492101c02c075 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 874451825 1250 874450575 874450579
    0x30409020d1b0f09050f090a0b1c1505090d09120816030e03010e0c0d08031506040303051b030a0c02010c020a09020c030a030f0e0c010834020f0d091a09 67
    0x21081c81c2c021604081494920f0300169228081d258860701003203009200c0540c05a0003c16040005030b16040300d038050000e80f4030040c82a900144894141c0366010003030b500464458100824003400f40065004e12600001e20001030b00a46d801c1020051403c2c516104426101002c03543c041c0600002d10122440b20342410102e0540703204a041c043c0070b4080304404140a5883c0135030840b01c0700b0300402c0d0549450401880b000181c031103902e890180d50000350001007140900c100042840d901c01d030003000118481d4403a1504d0343c1a014207804902d4500390b4001058004001454900703611050b6991010f509092810307a5011030f0020403110310f180e41140d0718581c4005601e01041c100000a00540302d0f10380d4051003216807001e00c0c1001c2e41d400d440011080e5101070100c130340e01d42c024101c140d8003601601c032640f408680d5010342c0c5e426080e56902c008100c012034203a6080360358140000a607807031a5100a03c91035150120042801c002031082943c0b11100710f81c48240413944600700c440100b40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 874453075 1250 874451825 874451861
    0x3020c06030a110a0306080c100f0c11040e160806090c040e010e0a051b0102070f030206070510050a020a09080c09071206120c050f0901080a0303090201140309010b0f040e030409020d 80
    0x144e0034002d80100054065039110b40300f07540301c155291406140d040c0a1541039512008003100c0148140c41c0820308403000c9500422000030000f05465038891011140c1c0d07440c00405283d0748980c4449aa1103441d0040002c6411510400482e110700086540c20074009031000241c08004802c0c2900624425035480342d117004d545031390b90034030100140d085680b80c192600401c0300300510b001681e80b110716103c3c26031200302102c400c2002d0700d800c402418543d8050340680380f60701e06014082040316411500c4241c2c03140d001c2a910006544410110301402c56100200340c0110040e00041407682c00401d0750080040c10f500e00c1d1841805038200400038680780e8510070501009160a10956000e8001c103070295080d000c0040042c50101d48481c100e49a0001a0203000000d1b00e048000d01710002084c0d040c07007605120401c0d002d40e004c00440c807401040000149004c1d01204010160100307082c02132189050007003c040640010088800f10340c100100169195005100c1d0340c0038200d80d001c40b1550200c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 874454325 1250 874453075 874453087
    0xc15070504030609050a021017060f03070312030501080c0d080306090a180606210812070e090408090405181009170403081b070b090f042c1903020c06030a11 69
    0xc4000b89005e981442118840198440308c00208c8440250036940b02035250360002003102420000002c1c2103901020b000c0c1c0d48442c2e26a10340c0c444100c1290300700c40000f0b681d04010040594144070304000d001084445c0050300340700c3d880b800ca050002074003881c424805040411540542d603400343c001d1000507100f043c40840241081001000b80f0b1091103241301580d080d0301350805990303c0701c01d80b00781c1c01441035003007a19403120a0303051617000707017000240f11030204a00b5090303954902181c459485071080665903080c80c01803200792000584a800051704185010310200000704521103d84040d84002501d50010304022900504000d210640c01030b00040100610013a02c000340b607281414042c10b09010b0400c079816564076131901c81c84812480030b100c844090f05c1c190007101d9246000410100350003802c4014003030a500d004050561000c081130b05907000b1074003404494418035841e80040420302c03164401a450b1001d450348280309a8000000030a403111603403290340c81040b00055507840b00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 874455575 1250 874454325 874454333
    0x10209031e06010b030916091b0c021f05160305070201090807050a27153002040207140303010e010e0f10290f030604110c15070504030609 61
    0x160000140a01a0140c049081d0320402025003210084010800500041c0e282220b041d02c290805040c0c0106801038003010703e102e1080c003aa1102404234032034005040d4101152000c901200814610244141c090b107000140e45c519001d020035604a201283c0d007a1030824041f20f00b4400e44101401418144201005056201014141c83c0e4800c1c1c031004480c50329030364542e5503800325104856200354400418840450494680355450082e00c1409003003040f6004020181c0300c9032024800c945040d40410003008041541c04071403141e01031055090070440c40240e00e4444c2d00c0080190296800080c01010401b000d804560090f10140c26030b601e171b503115410204404c8080c800e4030900c0d404500411003c0c59910360040c02460501e45050b80c140c07900101041e484031003c0c101c64401071840d079a42c3c40140940050024684442e03040e0f96a143c000200411100030464001000e0070603c6985010100000c81da02c016a6901098105a66002c011945840345c2e41000700b0250403c2c1c4180100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 874456825 1250 874455575 874455577
    0x40609090212072d03050312160f090e0c040b03041202070b0c0604110604271a1c0c170f011a010c0308060619120f151403010b030f0102 60
    0x9071080b200b000182c5003072401e0903034070035480c003e807a01c82c00381c0b60046000f0140c515036441c0102400742e10384040d07980e9440341030450708a580f019200d200c00c0020005a100000b50758030703681d2034a0414030000c05480c1402000c0036024004c0107060144000814a10b107855000e442c0100101c0c405140d4915051418000d50040c0c4403031200584a040c1000ca210000c08040e10801c1c11488003c040d243d495171201c01c0c01004641c00590400010440807981c4001c446a220601056021102c85c201d078041001040380d03d040c034010040d100c001c0300c130504c0b540c2d20070100244415405000c6440100350802001c07041095020041460750056035038413540c808034007200d00350700c2a4000c00c080c0501140a00c0d00554809400340000c080000480000c1c0c011003207c1d4003c40d001e0001800c042c2402a2640140c0d2400c5500c030116043d030444440f00143e6014507001c407450018240310380c51001038003d80038881401182320781001000e07074160382e44003507100d00010704005003280e02403034111500c80e0003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 874458075 1250 874456825 874456841
    0x509060129071e08180406030b04020f1201050c09010216050924060d0c0e010c02101103120403080405060a0e03090d030512010905010f0f030f110d0b0103080a110f0a02010e01020c040609 82
    0x8603d111700c00c401c0c03413458180f1914045070f80012000b02d00c0e0341e555003000102025029083d40c007200c0b102302d000d680c0700c09104461090108040540e5506002c000283c900f241c9045644018815108140120346030441e08030b800c0035144144031050032000308140c40c160b00640c2180e42001021803c00241c3d06c00383c0150345030411646a40c249480341d000110b880380e80c1400082d40200c403217186101d0240c0b241c44840c10410891043e0790402400d40c410100c480010b907000d03030000c0c000e00240004c6c0b000510103e41c206150800404c08020303056129500c3c2d0140c10b030741500c6000c51840c00d40506014004942a601e134100300c0703050540e10360780c03058010030b02802000581c4c078035101c0104000100c1e10404040c2da410083c000c1c64403240d6521121803a1035405d0241e00300614201074030020710103816680c06148213604050711080c221034000c11024000030b240c04298061030302c005400ca40880c001da0910780a290110700808040c1c0181d01c1c00c803100101c290003e00c2c1200010f800d60040d844800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 874459325 1250 874458075 874458097
    0x20a030b1608070c02031b130204080f0705121c050f1b070605090105030103080307051603091806032303130b03040c060509030601090b040b040501090509060129071e08 74
    0x1405844280f07013140c0c041592440250136500c0386007100e0034148002c0d91061020b2008082402071005000d00105a030000d0b8000e4405905c03400301c600c41a103060103c5400303003d003500e01c894002030030050f1564031000d02200a18400b096110034001c42c0c803480c1210340703401c03a4541c801c1e44d401c00752009003500345022808081a01400344040388a81c4a0030454604c108140d41d1682140d083d51240d1045070300142103030301071003010003801059158001d0b100418500a45950a02610384100b00c1c1c03c01841d03582c7c48032200d20b881c2c410700014180c40c80840c86854840410601035101d600b00078614403905511040c256000720b0700003101c07881d1708011449980b04c2e00e50760041c513a446600f500c00303019950301e00c2da0640004006204508941d0700c611286900103101181680a28000c1400c440080c0c000c000080c2e196820807207091001c00500b8018041303507000704011102d200780310b582004006241c001c24100041e40c402845080d41040e4500550b103400484001c5032803074030226542c4120000c0c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 874460431 1106 874459325 874459337
    0x2d0306060b07050615130b150d06050f06040605030c0a14030408041d1603020a0203120f04020111060f0c0901120c11010e0102071101030504020a030b16 67
    0x110040c03491210250b42c1c0e2003141001d83c18180c0c020200141c055103170701c80541c0d58440d82207130b01c8449204403001030007100c0100015010300d81e402c031114180d240410030b621151803e0340100101d0f001202d03558001d2031320000f48801c40c095403040c100841d000b80b0000d81c0e410006d0b030013000f0313441c4185131a14808140210680d4150815602500c01da8030105041c0031555445154480c62103000c5603644181c0760040f6030520b00c3c6e01d40c00b084030405401040241c8054000c0099843c8184030042d419a546003541404000c0281207800343d00007031001d4107401c281c11010071800d02451031546a180660b540d404010070603403000506a040110407006010a20303600d1069078002c05080e40c92203614140c2203021425109c0103462140c01da44108240e400046892881400d09082030901051589e518000940b40c030750f46034400740800d07003054100101303418490245e4041c900281c07642 = true := by decide +kernel

theorem cover : BRFrame.Cov 874280575 874460431 := by
  have h0 := BRFrame.cov_init 874280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 874280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 874280575 ≤ n) (h2 : n < 874460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
