-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2914
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:07:03.771512+00:00
-- url     : https://prove2.me/submissions/39e8bec2-83f7-45ec-8296-c7780a310e20

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 523920863 ≤ n < 524100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 523922113 1250 523920863 523920869
    0x108010e072024150301060501080c070f0b0408030121020109090504050a060e060108010612050307060903050c03031006111c0e0d0c08060a1506020706180305030c01090c1a030a0207050a0c 83
    0x25150f1030b00f0004641ca04107031980c500d250980080100f40e0411002816000d40500403042c126000725500c410000309020560f8955404000d0101c1410946000c0f40903030800e01688101c80c520090149204050400300d4401c40d805075500884a85080300e00303c020040036005650601800a103100458028010681d050030300e24010043c3c0e41c0b400480710708448942e04030f80309901c10495200003280d000015a02c83c10340000000a4403109440c09a40c81e200719000b402e42404040708220300d0710b00080400c801c580e415140d0f04d1046010003012a05c40c150f2400000784511000309141c10144526007050fa0804054281154402543c0790304040c400f0990182140f62312100402000f2000381c003807240640303100d12070128145c1c20210080d481c0c62441c0a41c034108049032200492a2100c1502c85006582040030b42e0369500c0303d426030074060172a1000c1603c40345544034001682a6565014481d080411018030341107032112008070010703500c44082903480d44683d007020030120380645044401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 523923363 1250 523922113 523922173
    0x40c050d0618030c0c08161505070f05060f281a04020f0403120c02030303070503070201110304030810080721050a0206030c03010e0c070c0905040219060e0108010e0720 74
    0x260a40c43c40d010000540c5070708007070700769004a0031810302d10007c014044156080a40100503400a0b40d8040f503007030080302006070484d0008000c1c20140800425028012120140c0402c0f09a44103507a2200e4140e0356520441d00300c0880030030342480d03603a55002c0540e0b806000c07031845500002c0000a01a40c110041e402c10891000800300100b00304560385841880c9141403030001c00d0840c0d00001e48900005202d04288000000002e003154400c2d40710320301600c551070910b91242810305000b0f0800d80101c510a024041d044404613000301d00103104800c540c51250714210404050941803507010b5103c104580e9849144008030061350780c00080c0d849050030440030303500d940c0362443c00c0440510242c225588540708000110126081c030403101e0a4482d2749031b0110700d82c4c4480c404500c00000309200401030341c0e4643c4d404240b81d07900116500070760509070f03904055170b601c0b03003003592403080207a0b42000460315408205901004640c481ca12241c441c90551350301d46008080c140081200c4895050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 523924613 1250 523923363 523923377
    0xd0c021c05040f120c060c051603060f050703110313020d050a0b070f21091b0311130506030a0f1b0602060601090e0405060703051302060d0c0314040c050d061803 71
    0x20300d1102581c0580185002c0a1403204041161608030142d952400345804010018118030705000080009c0355101280602101030b0664a04002c80145041a03080d4030040c14039011600c66442030280d00d40509220041d03501d561a02c0c0202c48810192480807604460820b034a070010800c203108181060380504c040c081c4901e8421001072034510404d003401c05001d068880000c090306a500703401291265040c0000b40203e581c205100562521803000000e558100004801c0213080804076980c0382080d220340c08680d07502c586e0305059480485510390943d002001309004a500c0520300b1301c00c21b00a803e491990400409000b104240e0b9030810b01c00b50b80300506000140d64002030820041c0110034108000e82083c0d0713519521040040d000b0070405861740e004c100d0021413407000d0010a40d0080c0b030103980789100580d0002038128207c00c140400c0c0307031010340b070b11403210440310780d200360707404001c02c2c4400f4103102c20440c11000940d000e591440e6141d40408ca407100c0680c10707141c0c5900903100c4007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 523925863 1250 523924613 523924619
    0x1c150515030307083015130f15090612020f0f03060108010c020d031a040f0e0f070e1b0a180909150606020c03070512010b0306010b07060605010c080d0c021c0504 71
    0x30220345840741c00c503480790618181a214542060b900a600325603282402d00b4804002d40000c1c0487d40365074030500400d031a06a07160302c040000d511501056555444102080d40d4507408681104c200748034801c0d650000d008070360300500c2c0407080d02c500014010281e000464141c00800d1408009070020021690b40c1e81c0001c65440c1c04102901d81c2d5080d628040c0504800041c20000c409042a01c040c01240c407209180e081c0361060b0442c05050016004491080d0118070140f031b41c2c0c500b00c1c8039403031800509001054030b2030f1800008810328500130b01040d150951400c8101c03a0103100180081e502d085104c00851501480d014403070010340561610000042c5240340328045401c076a00180555114424001c0e5645000c0740300380864008030b4640c0c0811180080766405000d881c0100c0d60705000c0c3c4000490050248005490380e1802580d0400001c0c1d2034200640351041101c4011340301840c248101f40010030190411603504525106960444085008541d0702080d025200340c0425000310f824 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 523927113 1250 523925863 523925887
    0x90b0415080a0b0a0908040306150b190809070303080c0315100807120b0319050703060e0303040516050307140402070f08031f050904080c030f0d0204051c15051503030708 75
    0x1458205480325001c120842c0161b4400070107100d144802008252a100c04050000f412078884009002c0b5009003aa50341140d491085081480504000414240d20205039051070000d2150141c9526844501c10b40d02c0c0c003004181c454000a00c050300a013180031200da241d440310082c613040300801761104d040c1070600d0342c001384c090520b0b44a42120301d03150080c001c80740da40c0002c03420360340143e4050346030f1820101e08215090a00c103400190000341406a02d0b458240c000005605c207500520507102d04840120610204103114451654180c0c06900c0c148104400190400c0c40841c00600051402402c0c0c0e896805000c103081080c0d440311004400c100c560003010b4030516402e50041d10408000d402d09000844c2e5010103400540050000314915072420700c02c01c01c50b080e081c6003081341501e031500c0010b0040a9402802603d008010f00500310a1880790180154001c030351002d0440c4070f0102d000000030090100801c590b440580846110002d41c4050009000203030007202c200d56039482c05404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 523928363 1250 523927113 523927133
    0x13090c0c03090b0c10110c0f0714091e0c0c100603020f060c150c13080607030c030506010503061513030807020f01020f1b0a0b04170f0d09090b0415080a 67
    0x800d01011504000e10004c3d2140800e2041c04403440d0000011341301040d0034201414020450385c03c16511601d01d514405800000d5450100c0301201404150720301403005106003040706440038124003604c103441221102c4924907841d8442c004103519410407810030072003840c01400740b0b144983c60756180d00070300a40c01c0c484050511050180c030614030300805156040e42d5504286030b00ca80d46008280403c0303a40140200700d88a84940100d00014240c0350001251601402e917038402c0400e2400c212002c81e81d01a00420744100016140c807400c0d645e454050081c04564990186815030b01046403080303118030b00d19941d0245010b01d0103291121064418050702030740e074400c00740c15503000d401d118200c030000050410b4441e15070760410030a4841140410903440103904a4110842e010030040b4100006040c541d4030081030344100e0303083c0009001d02c99103410107a401440000c0e03038580706020341142600041942800034100244031512084442c0080c160381c3c014000360703005100c10006004240c08 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 523929613 1250 523928363 523928369
    0x15012a0605150a240309080f0a0807030c1b020603040312062d0e011a0708070f03020c0109082d121c0204050108160c14160602030c030304030513090c0c0309 69
    0x108402088204d5801204481e800d8520010151192185420413444200356001600346501640d200d415061001d000d81c10211014800a8031b03115119196503c0788a04800140c401c04201ea0341000e2031702803200a91000340240c080c0010180010403280c031900c1740c41c00400784072100715003640074551244505100d00c00011400c840c4554140940c0320b003042d040e411614604460600300c6180d08074601c4c0e9001e81000504000008204030040c011030003115141d880c0709600380e8004055030710042d21025034501810900758011500810440c5404e07100c0800360805140d040119001c0c1c101c0c0510300215034001425114010507141079a44c0140c0c880540b65440c0c580640c00c190500300000d110707440003429070712030500e055054841c041c0545042003005800048400080e407108030318594401c0c28202000003442c20000010701e0a2000c03003a1020300a014000e58034540761600c040342e480e0824900b940c18401d1507040050541c0c0c1d00e02c0360810105490720744200003141400c025010040c1a4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 523930863 1250 523929613 523929629
    0x8070806090601060c230318030102030f0411010e03120d0c11100c0507060507090e07030209012c10020d02061008150a0204230915012a0605150a 64
    0x2090044002000c0b03801810b6503007a03e842c1103c10501d0401840040c800c5030b192440c0588001c2009403142c01000400c03000c140c454040221110020906080344011114050340312010000b140001c6c0e441000d010a01d00145000d49200700e910000a041200c1344010020003040051a00b041d104180641c0b43c6d4002141807200300c00401e08001a10340b00d840071802541560bc51350a10924081c009468041d900400200104d01d8981005401c503411401540304a40c14413000801441c800d0086503802d81061307503586a69558010f40c00c00e044038080303908021203054180701446417a0300f1010320441b007075940207103601500c1000207410310801030700c010320549101005120540002880d202440414020300080c0c0d560401c0d080024012a0003d0100c1d10250740340085080100a000d003c0304d1044030146d0054a451854a401c0710080c11a03c3c00b04215103001c1003894040b00c0c0e4640112072524502048108a07542d4008440c021a090325400042940401f9a030400182e200d0252441e4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 523932113 1250 523930863 523930873
    0x10f1b080906011502030f03070f020c06031003020d050705182208030705030a061802070209061801030b0406060803071505070c0309170c0a0e0405060c04050f040e01021c06080708 79
    0x4022240d84501c01400b130043c0c41d14041c044041c01d684200b00b1100c9001c0051841616401e00c024001c1011301c20785901c100520800c0292081c900e41841241c3c01050311402000390240f45a0900201c0c41c07803040c0580301802900000900f030b468002516183c103003480c212121500d440146070305c900d2400300350340740b10380300c0359030a070340090040000c5030f170058080d0034520748940c4c41c829a076000d02a10780000c0030340200300c50304040718132853f000307030900e54400c50b201d080540e035403000e00101408240007040c030f02d0410340040021480183c00181c00c240a03210124030240c4440801e407a40d4001041190244030700506200e040a007407080c503800000034034001420b200181c5009183c01ca6902501e01c1302c0c01983d0100040060403c45018182000f0b450401080e5540001c03041c8142e044030299280d000d9000002c5214801008031001d40e072005000d4160074001c04c1c1400002e01c4c820a5103081594208401030394441b890084c444440d0048501050060800780180e007010340e1a4403194059102c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 523933363 1250 523932113 523932121
    0x1113030c0e0a090c0b1c0603030801150509101808071409012306031003050a05101103040f1104020403080d0504050f0d052706040605090108070e09041112010f1b08 72
    0x70040d0040803640f0180f540754895044019081b034a09a04940d28000c9203000c070000105904090254100c40811f5440c00142a242c10309072514440c40e10301c40e5024041c0c0340300c44160742c000d103942ca103922086800760f9500c0d80c644c080b0a1800e49503030482d03201c0a0040c400403c0364585060468054100c07100a00c44100200043e405404c080701103082c8618004000142007c0c02d12004c100110780042c02c580c1c1135011814026101c0742c8141c0368811142c01c00300c00405121441040b280925404142030340c0c08100b507110800c0d68110700650540c070039020030001012400c00c030003520200c4226500010389080c180741040c5080805030030b60f8000e810007040e01d550141c21100380c030b14a00c02d03211745001c0700d0038649103002080401485c00364081004a030110381300360302c00c0207855825001e03200e03417003251140e0405a84e50013481000ca58464903410010700019580c409982590201410000d10003050078175950179115404a1000510ba03110b400c2c030070140c820b180c0d0318901c50b4141046801800c0c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 523934613 1250 523933363 523933373
    0x4030b0a0e0106440a0b040b010e06010206390d14060105090d0f0204090b15010915030c1e05070204050a0b060307080903070803070804021216091113030c0e0a09 71
    0x220300c08074011805110341c40044440210044c50701d91501079001d6429a8002e440c1085507030b00c0a0f901a1400309181d400441e00e8031900c1c0016000e850160018105035490240f00a0781c0030b038620b00c1c00c08481e00604e030400e003402402140c610300308040d041e198452083c0400041200c51541600b100415440c050142c640d030000120b45044d2404e45030711a00d0256824031403401048580300030b400034505010f11042c810112000c60040c2800740b0031812026040c801110002141d02616900c500181c0d10301050502907804010b4090f0207003004030000c0ca64441402d00901ca040903480816000502c000840c6001d100389688a40041d504000b041049404903850b400014400814440c1401c08159406402c1017640c0e4a1079100c00013a540f450440c0004000000a81d0100c0c0110054504030b40828804110411501d00030f160005203585010074060280400c18031325400c00c1c00c10800f141c13540707004c401e00c04050341c05501802c070094900750b01595081d00041c054000d4914051404002035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 523935863 1250 523934613 523934669
    0x2202030a0308010510030b130b0114030f0610090b0f07061d1b010207080304060c02010504031704050a0608090a022701420507060b0d050a0b07020a0b010e0c04030b0a0e0106 76
    0x20b404c020340080c1e1259500c0060f1241c419841c2c034122482f40100411901c01c81c125031491003114103584041c0c480e4101c90007520002e9060152000d081006e01c407103032081c02e006016200c91030240c20081100900c02d15400c540c041007001c61452074000a9000e41c040b84c0c4400c540700588400c1c03005120340f0349880886910780c06980030720410000400120002d5a12910a60300515040418103500303945020005a0543c0103119550285c0800c000001d0000d0040540d80d03c0b03102c28202408180c003103a400c00c031220000d100124444081d211800042c4a001603603580030f00070008010319070241c1c1c801c060f81d226421103445801d0861800e40c0d6285c80b8401d25032249480000d040c101d80700c00300340c034110340685940248160001c880102c80010f100000a1483e40d00340100c0d0002103d481d1010308076202e004501018080c0b45020340100f105981804429602149080407142031945943e58403e401d9000e45600381280d0f01c88803d680d20000a101d03e0008000e00a03000d14a0741c90100e2404000b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 523937113 1250 523935863 523935889
    0x2704050f0706170912030a0911101b02032d16030f060c030f0c030c080f01051806120706180518010905060103090605092803082202030a0308010510030b 67
    0x318410320100d5813a0404008440c0281d010f1050291a441c0004000c401445811010340740c80003c500342000300d00f0040419020223000366034540100e00750b40014420051903c40c00c0703130544201c01c0ca50400c00341d00f14129030b420880e04e54080d094120104c40d98603015034414060030800c5100810000614580300c0981090341c088004203184a11082c1a8020f205800c48901000c6c18600005500c81c3c0c968011107a00f03080d600c840c1c2598403031101303480840901f401120b40001a000c1d44410780c6401d002c03400d41c050700084c0f088941d01240e03040c040c00c02107254800d2002c121020441110510000038810140101341c400481071404a915034140d41c0040c071a074080030b0b64690120b0102d074401d411401a4a0b00100203000c40c0c14842803080ea20a08250f0000c100c4400d140300031007984031a000644043c2d099901d00e00151503c207246c440004010954844000d618039400300181c80500000140500941f1740102c2585444180800840a500f03c0300c02c040c64005880d1150303445000f0250f072 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 523938363 1250 523937113 523937147
    0x402031302010c06060b07031101180201020c12031c020306030714010903020127030c0513090803150a08010603050a031403090703030509061b102007060207022704050f0706 76
    0x1d4003c0741040700c02048107800141c0c00000008980041c1030b0441501c48000c90103c0003000354070300b62400340d500e2401e28940280160442e00c0710143c2032401ca041400010000400d4030301d00010202e03420000c4075a202d050017107580110800c6114a4244056401000c01e01c100d00e5000204000080140056010080c18060000c440d00002c401507201e44034a42d510640d035400a50300c90401044280407031103000d20402c015840c844107101980100c0400642c8605402c3c02c1d030301c9242c0b8007680c042c2d0002e80c9a0708031544a4000616800034080c01c2d0046025601801401d4800c2c14010151032107800c0e40941c40c01c00b082803211108000401c44112130301880c1181d1a01d00d101d0020380d0520070040c110a00030009120702a1520b404200045079004110701009404000d4041d034a20b03064541c1940c0070340c1c40500c041404550b09400034051144020454000e41d60b4040703500c0c103c1da9030081c452812090200400082050404c040030b401110500100001440d001008203a00703102e40000035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 523939613 1250 523938363 523938377
    0x9040b0a15050603180606100815240310090504150f0b06121609150815060307020a170412030c02030f2b0519030c0905131a040203130201 61
    0x142030901c003001400c0c00500c01d50f681d00786800c0c05081e0b42c2c0f0220b500d8650340105c1c0c0105a00b4034001410000000e0503880f060312660380c80414030f184441c031081480d00000c54042c40d0b0192540603410300c003040460b2461503103a0420359010a034681007034010101480c42e0506100100d04209030800c00c0c203900220200d002c0c203042d401e15020f0140700c511207806c039a0101da4504035481e0741021074810140b81b0703008a140c608034881100d5505003031040034100021800140301542c45005955030103a8181800c1c00c40d1a0702e10080340342035004441140c010780245510034104506410400c01860882030158205428160242c091106220000f410312544000d02403c43d1020700c0755800141034081582c05504000620740b201030409840c582040080020010740c045c020341c103860040210a00c2900004584041513005086250106080c442c07280da0004059480ea256140c1a0401100c08144000180641444d00641c0c1020706c2c415030040c000c1041410300112141035080c0c091034501703 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 523940863 1250 523939613 523939631
    0x6060f04050402130531090f030809070b121504110405061b06010b0403120915110a240c020105010b0901270603020a1709070510180f030201090509040b0a 68
    0xc0080350681c012500501140f540010710406d14016140c11031001c001c44c94480a442e261004880e0f269000920340b0150f003c080000c2032291400036401a11903080706c0015454010940300c0ba0401d13004240181c0c0c4903003c10183ca4008522824800e0054a052000c0b03e484410f5142a020780d0113201c0c080c041c08114040e86500060204403540404000d40b04039585518010540d83c0c03241c0410380d4020a003d000341146481090b000040705c03584c01d452501c058502c101160130780000310440c24180f1901c8c1c2c800f0080340c119051610000d10405008580107400782000003618109100c0409691600707004111032004102259000403003480c0001140c884550320400ca00180314040ba400c04204401240940d0180c0c000c06010280d900c62010b0006445a0f0040101c011204030602c1d0300980e000700180d08180181d008104068105904200d6100d840d0080041080d4070010b022a4100010001d41d604140880043c00003a504242980b4060311101020071020b0142c440c0aa5078040304 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 523942113 1250 523940863 523940887
    0x4030501020c1b181f050a080105010603060b032511030d060303020d0504032006040e0708060103060b0901020c0d111509180f07050d020403020406060804060f0203090a020d0c0503060f0405010506060f04050402 92
    0x101c40680300046c004d05112362584080d50003403c0900078400460f140420100311444502d003070300c1c0b04e5401c0d010034011596049018101c41c59081a5040c180b1011000d0360070100401d00c00303801912101c05000440078030f9810000c0c035145c0352052810a01104203c1030001c2643c01c00e4a0082e080c000c4491021101d001c0007042440c86683d00c510301419818040c0f102155000d402903000d2103090340c003840015102c40b204c424610600c0030b00d45c05a400a079404500741041c0d035100684c0c0e40034980c00c104500035130010605104550182584400d0000380801803480c28240c41111420780028104491614030318544103900003800d82c2091020109040501840c1e82e0111030241d035015009100f11076441a004c0e22400301641c1c2180c000d4280003c2581a03080c0d031003500d11484280c0d00400380d45149400740040b629540c141a59021580b510100b61380d03c080040318040e01ca2038500100c070b460300c2e0034a542181c0d0064819440380c2420041000254071100035035065507821100142e40e84004210 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 523943363 1250 523942113 523942171
    0xc2c0d0203070f0f1e060f1413030611070302061b07080d0207030e0d0201120b19150f0305010513052a041517010e0402010504030501020c1b18 63
    0x25070500c148100401c039801d070032120348125140012040c0c06640c44603c03034a00e40001030707003070101c01c903000e1010001c2510590700040071006c41d080c01540c2c03041c0880701d800c1c1d9a1105440b206200c142103000c00030800300f403040c65203071010317452000c1c00c115103035400075221107018006120550317a101d0110401c400700012a00996803051a45503034520b034180040c0030703421401d026000310754240113110181c20506030704180c4030f505a50f001d00e2010010003060007000c0d507006858208042101d1007540c00f1540d41c5007001740a6201d5916a2210b600400914220b000c0111200301401d11004104075110781d00142d0410312016004222070351244046142c0c500c2c0a0104241103103815920801400c0d603d00034800c0d2618900076091401c11501e00751550000642c1050072019003100400c215000d2070201a0050303c140b41031407420740d880e1a02400d98000c00d01d9011260840d000b00d40d14015041e00b0645000016140a0400ca01c807086c480c0844000030050208a10040e03c400b1800c600303004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 523944613 1250 523943363 523943389
    0x905121c20031f0f0e06011121040302061314120a241407180f09200d02122202010309020109080d09080f060103200d0c030b06040c2c 59
    0x2e030b0448039544d50180010080e01e01c100101c028900f00031a10a510a514a101040c00c05008240048030850700c080090f00c1c058440c000108207200100040e40e9000013400800300b40440940890305041e22450103003050680c8a106452410500c070384103201040101c0110303001004c102204880d100c0040601d91545501e01c0601e2404150300f4100e9080090280540b50301e03500ca009101241070788035214091030044281c1140018030170400904640c00c880419038401000040004100703405a403d42c0080c1a0f4901060300400c1050840081c0c03013500e64080c25040000040e000541000000c40413003203006810952100008000d590003002080000d000c140300700d8107100042e6030300400b60552800303005418000c1310341c030304c849100008405040c0c903044540c1000e1390b541030710040302c0103440314103c603000151610004007040e0400840c00045014010844071840e2110402c01210482543c44003441040950b000c2582d00e001d154020b076501140140d00040030000c0042d222000c601 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 523945863 1250 523944613 523944661
    0x5060109050904080d140915040203030f040f060e030a15020903150c0d0501050f100518100f0f08041502180316030209100303050d0f0905121c2003 65
    0x1d4180000c00c913450000307151802164004105130340d104004200701d440c00381c802641581c41041030708a0081d113556540d801c103100400300c1c0d10b8075518220089507600300380d112a202203005a000c000da0341e044405c4501c1d0107030490161203078126958075001c2d0f100801c040b00c0001503020401c5841e81d1020071012410f04040e00d1240880d1a040300b811003268800348044c80d002c0d08013000000c0e9400d15030308031503e00c04000e055a00c1c7d0b844450040701c0f1500800c4218100e0542226880100d4442c1014071000c0005c3d80c0e507c043d00030300c0f068040e0103a051703503140340100725403203007004041280d0020b41540d1455410340540d84046944030014010402d0340e0050703060299036a429040282d815a01088920070340700d090f10f545d2081c0d590701e6001e007103100180100700200301182010345540d2040000d25901d00002403240c00340e84801c1e1809001c803602c440030307060000d5000d4081320f800014500002101034280400d04041c03030b44400c08504031812100034032001c400300d2518680c2c6018881003078480 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 523947113 1250 523945863 523945879
    0x1c020a050703050c040f0b0f04110706051906080c030601062313050a0b03070c020906150c0a110a0503100207020414162003070b04020102100905031305220506010905 73
    0x3820469104c5940d4141140300e50319082402c40c1024060040b0054044000c1c400303880c00001c5410720025001d0214040c26402d810000c800c0050784621503d4000c14844a00115049c210340c004011103019810810b101d6003d0070200d109980c0c001001c81c10740720207203070895225040c0c0c0881f94041c01e15803000c545601002c07032016901c1c0f0284c4680011208c049600500d0030742e440e2a00b202d24441034503010000dd42ca107640d00c0150a0001c04190401006000038041100080780014a0740264180440d51f410a05210302031004d40c1565552400e0202c81c4104014988400242d030740d40b8617062a44041d4000c203215095680d107500c040013900114080d140b2074a41418030121180a807014180481e2400072540e000e0148480c2c03025045070954010340ca001016182d07203c807014018012411403046500858100c0014010324a40c3c62181000b580c5611407d4954114000c039604071a0081d059490b404a01522003e07140500384404000000d140e2583d40c0103d03450707000ea4001030f401c8861 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 523948363 1250 523947113 523947119
    0x6040516180b0a23040602073b070806010306050a050103050a110c07090e01140a180501021306020c1f11030708160b0f0f0105011101020d1d060c07051c020a0507 71
    0x326640c885513403140111040c0100314a0030028050142d4000c12005a0051005200c800d4884510307002d17104142c613083c000403a040c00740440071840c2001e80381360001e41c84144104030740c112040c1a0000c10034241886410f00b4080413130840c0005104e040e04064582c2d011a0100c100c40d4011285010002140742d90307600000080b43d66001280b1481040c0d41c648100c8175880001881407080b442111040c40e5205d03221384150f000507029000a503844038140c2600000011001d20003044a04080b1004130b018a24001001e400d11002d1985a80102c81800c2031a18506201401d91422140350500514117076001d444a0329600a2070802810b002001450400b40c11100c4910200719100b956043c11030f549065625140364015075034120746070010401840103600031141805403056a4000500300207002e2114016204242c0624507000f00705501b20a0003d001d002199204040c000d14905c0e003041555107640e10052180c000e181c1001005a11004c50310030b0000c808916080411a003140d13031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 523949613 1250 523948363 523948367
    0x30503072f0304030c170615040e060720031905070f050718050c0703140306010201020f040b0a080c18100e040f0b010306081906020f0702030601030c05030606040516180b0a 76
    0x4840e001c05c0c0c0d50400e00a0000560303004041095240b20f403018094a00b9859a1103034140c200c2c1000c1500368040c2e1606034001d4402020072041c1c0c0301d0601590342d410002d007181100484440704642e15280c680080001a4005c0d00e69044a10710030302524200fa41e072895420031030206840517000030030038080c0040c005542800e0295100019000300c5040181c1d4550074041c0030a0300c51640008e01040f25401d680044952401c06154416010300000d4908099a0201c2081e03031f009803c10003070f0900c049102310b14142d2222180381d1000024000c1c500c1d01c030034514100d1105043d6216a80304426000811604a00c83e040240c9001000b030024806c05c038180c1c0ea03034405003503c026610300003440d00d2030001d800000040d82c5035003401d0610310002d200a10b0f4507010065400b402214044100c10015500181c50421019000f140101c0c520454242007038101401c146010b02003910850610041c8400c5406031a50359075480c2032424800b0b621414000601d59000e1954410300d42c4040104c1d2280d4969 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 523950863 1250 523949613 523949617
    0xd050703080a1707080906040b28021903020913020310090c0201020c0c150d0510080a0b01030b0709050f0409030c02270115020d0f020c1003060e06090103030503072f03 74
    0x151076580882640e138829500b160b074840201ca07410000d500c0342e008a00820152050315810840785c0845420b469507c00400004040c4180c1030480039900040d42c01070340b803810311034040250040c0b03403d42c5460003500004035444c80603102e5039021307540080030034421020010100c008001c3da6805101020b0333801d001034000e40015400307070b00a01030f03165121500c2c0f604d011072454852280b41e1050400011070284001000000c102408040d109480441c81c003004010b00000da40c46440d84250325030541c0b61441407008003401802c00d025022000380041c2c0d03900d240c000c0c013400b016680001c1c50a05810102d410011110b0007a4201070606982141246203078042174003d40c040075171f2a50b990baa0b24100003102d4030baa540c040140c0004c82e1a00c145803084111580030200c910441c0c41100104001038225490340c041c400103e540c0390400c104060740c80540ca9402041254181450341c9551070140152200618140400001c18030f0603000741c641c840111300313501200c403081c81c4041e0003041899982d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 523952113 1250 523950863 523950887
    0x70c09050f0f0105010f0507110a0806040311030c0705060708070213020910020604120e06040b0309070e0a1503030e0604090609060e06121513052a0103020a0507020d050703080a 78
    0x211101d4070000380d2030350300502d03002d040f0768060b507502460440c1c122040f1002e80110318100d581001d0010302809580e1140c0034030010b4010305001d0081c500341460302078803401000ca85c508040d00288400c02d003815021903000d040315000c0c0d400503910f5010b4900a0f01c2071140f584004d62000d540c25001020400c542d0242c88120350644a0550140c0c100d80141c0e43ca00007150014002c4868251100020740f1480030142030700c0000d0059400c064442e0f075060800d8100312030141d0103a102c018208666400e42d2662500310b01d5040c02000300321010362844038140124000a004e0041d6a05804429116001154000c14050504108240d2074051800c090b00340c40c4100312107502e00402095043c82c041108000040c18180280b2901d41c000e50001c2c40b020307000780460038801243d8440804103c00788405c0210180c401c044070000450031008100081007088410304151043c05080480c81c0c0010171a52500e4040325814140312045c60403914006054000800c848008105005181e800c00122038032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 523953363 1250 523952113 523952131
    0xf0a0501050a1e0b01030b0306040609030318080703080606040506070f020901061e0c030c0b010e061518040b0402160317010b0f07110f0901082401060f110102070c0905 74
    0x740c0c4a59041a003518080710a15151090f82916640000301940c0314180c03801060501140310741112001a08048086030103807015a15500c2d80b208042c0e041c4030748003204140714072043d0081440c0c1c580d1030060050340001018000c488020600d540e8130202924002c0c0001401c2e159034002e03900d06941c80e0022400300f03d008800400c00466060300038603242020201078200c0f40020800d011086840000d128002d800340681c0306c410030041181c5e441d9490203000d24003810032042c1000400d00610040e0006064807041040c42417441c21030418150b405c405e04211400b140015680c00002c00a100b03070081c0d140c5101008035500c08141d0082c000016030308123030b68805002ea903541c000b0b824502c81c4401030814a68104055000559080804944c0c0000a45001400074600000c10003115081c0c005072071980c0702080100c000700740c0c00c088528610800510b08000d5242c8080600100c200705e602a080c000c820942407402d410940c1034408032900150603601c00b03550f030440140100b5054034041c0c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 523954613 1250 523953363 523953371
    0x3030608070605130f0501020a0b070c021e0102061b03130c08030406020f10060b03010e0a0e0d081807300516030201090e0601200a0c14010908070e0403031505030f0a0501 75
    0x44c0020340c2c8031110200c81041c0c01905407249d0941c1e54481001000b03080c901481903151004015840b00c4041001000d4601420320214040500281c60000024602200003100d840da1140381403d04d8140ca800c50b1488003001079480b5107250407100b80030240c101d2055807001190020340554005601d01c1d400c4010801e541032400c42501d0b0506a424501502c121528100010001c00301c500d4411a4004001c041c00507000c500c51266504000c4402c600c580003801607428420648551210b1481c400301c00d00c02030003468075001e0300000c260380e03840c488101156003030411000031600103601181f850780310b8242c5031350241c84085060307840014002a40000e0550b0760104461307094030b480b90302450050f15102a150740907406122160403440001110303016144040c0c000a00010f1100050f20a40982807a820421400107240c52117036032100209605c012000c00ca201d08032500c2c0d6401540524010590380508440e03075101000320307403065426111300100c5190240700881c40e95881f0b845035000740 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 523955863 1250 523954613 523954619
    0x1060e010203041d0a0f150915140d06150815070f051e130308030f09030f0403080c011401080c0108070207141216061d1c0f0303060807060513 63
    0xa03034070f0185008043d107107491183c1c10f18010700d400034280d41c40340140201040d00c0722510544803d030340540c59808030420108409100c0c103e00d6019008000006980403032030716203070050001402c224003152a0051840d0f19654080c4043c40e000781010000c6035030300012b000c1d82ca0011070798400dc0c4130901c01082c5500360224140c94880c6015131400d1907250f680d1400c10b07000d12140101b03101303400d0040d440020104102019205c0440c0d02d03000a601030150181c032850002020f8050041c01841c060040d0000c100710231036104684180ca0075281c014a486403070b00000050180103100c0c080c4001d80c5884200000030f2002d80003ea010305c07040c006c0c0c4e642c1c0480c0c2c84081060b6503415860150011140801c40008014103141d000720448407100e074120360b200d10f010ad0f0711020700003030703500150000340042001c000e142103290f40820072000207652032200c50440c40550480c06204000041c00c00341a03c20f0141818440c1c0c04c00406007504006541507035548100107840c0e68030600794598a104a54400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 523957113 1250 523955863 523955867
    0xe04051303081e1e0c07030c110d060f0608010b06040f18180f0302010c080123060409020a09080f19060b0d0c06110706020a0b010e0711031c110315040f02040e0a020301060e01 77
    0x6586c009905031141000c1050ba50b4507a500008960700c819005000c407000c0f000480d21900906403640954a400540da81c03d124405094078050200240150b0042008000e1a401030300c1c51421104403030b0884100e4804000c81030060014010186080e04606000f142400382d0446200f1040f4440d4000700480c5c0354044003501e10328003d100768201c03d0316040000c0340120440440302162000201800d141036100c004180c101d1300310003111700000703a140400f031103c06002c01c203034100e451120006098481c0d840c06a21000400307140c004240c036845080da50040d40701c65280b002100c1d07200607031200c1c103511090000c0c44615981d9041d00544107403240000c0190010603140324240d0415140e655503828182215020403001d0451002c109428603101c088000c1032018280b00c0000c0360030301d604c80001d04061b0058940700c8100c605490010010f0140d40f4141e20003da0205000303880115075110480e043d10002c0c003132640240720060f00030341000300110f59540158180c074082d40310409912070361001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 523958363 1250 523957113 523957117
    0x706020a0f0309020f0103020901020a0524010501110c0f01031119140c0a0807050c0306070c0201030c050a081315020a08060a0e06010813110d0f030e04051303081e1e0c 74
    0x1000c5d41240c050401c81d01c0b25403003900100142c40c4180120b810318038407503542500c0c00c100107148a2444407815042282c46c07054a00660040c00246000c0080c03001110300151a461301c80c141070700ca007400524144450340650041c400c0c0c03107140309081d80c48010782180400b21501c410040000a441c151140405100c100c00750307150005810014070300c1c20401d54070395126611541c0d040d52107114258481000340d504028062041295503a060a0031665200240558201520840034094140800380c000c0d54021507072980600041c1001c1410b04503801c007040184423038804100e0300741c00024205a10740d04100900d0082000703591114003207a03920715074181d040d802ea5405001500030070114400e8a04900c5400001d4001c207a80384400400c01c0c00141444000d2408031112261600d6460516401200b0440740a0040da814000c0d494a100400048c03040c1e164003d00b031024500100e164295030004030340c0a5226a043c003c1103043c694529040a002074411480032200e01000600d41084003007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 523959613 1250 523958363 523958381
    0x3010e090706090b070b040809060304080a0807020d1e030f06090207050f01020910050c070b0424182304061205062a0c1005040303021806190e0102070b0706020a0f03 73
    0x2000d54240b102c0b51b81c400000300c0d809442900c44181c184104006175071600c004600581c410850180e840600301c03806001c0a6005069000351740120b104001284d4004e420111004180080aa00040f41980a41c020010604800002403034503001140c0d80c03070b6a038020681580074108480100c7c003172603455420713403140c40003d0f41c04c000c0700b6501103903070750182c1c01405a810002050303440031502e80390700c072038181c0165100f1103051100700324400340d121000c56006d82c24146c1c0d191004040240a00e280581c141520401c44090281900111040e0400d59400c800080041c4113000d155682d0381080b00145001500b55014000c100100760074008511400c440354a0245070105900c41d90000080640c00ca04014070260007081034038044800c16118035403090b0702c08d490050b180c1105000e0118006000b9130828092001080704510342e035080300307000c0c0100c07400303190154445650000403420300005510040d19040b002c1280010001560080e107030340301169543c08038a0329a04021015145d9a403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 523960863 1250 523959613 523959629
    0x307110a0c050a121110020a05190317060a0311130527031c0b0a0e101a09030303040f0f120309110f010f03050405010204050a080a0605090c0315061503010e09070609 73
    0x640091418241041b11110940d03035030043c3c41c0c008889464050400e0303102541d1100c0c003460041500304160f000250000300c0d0480342c2a11085d882d104010900701c010f039000240003842100c004c1130bd6a9640080710300f481d41140414450380c03d00280c030b00c030540710020211800c203046c1821440501e000209441000b8040e4802c800c22400c08404003000385914034900d07800002917400030a151100c058524015074208a0710103299140030a8040c48100c610080344001c00100314481d0903580000641703810580094003000329401c2c1c2d1824140075010035000800402d0b0301900e4216031a01544800d06050041c040320884658000400c0103004008204a0114141c2041c020a845c072a40c012540188141c2c0014070f0280c0b1752001855003182c42d4400c0f01c40340c0c01841041c080003420702483c0c0d0040c0c9039100801d0b20554000019448198100c3c075039a10110650000d2030350340c1c40400c2046c041d000001d4196903561a411454081d404c02c48007404a4424400300141445c85524210100c81c0300c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 523962113 1250 523960863 523960883
    0x3200108041401061a0c15011d0a023f0403080a0518011b1103030c1902010605150c06132103090203070b0c100e070b0307110a0c050a12 60
    0x19a1050518030182e00c500d02590b685500105075403002c1030f41c0144080b450406280c550741468000361500203017240480c082c1d640e04004000c81c0000302c00f100040da001c03003032100250341d4407000103000f401280882c4903245014120a04580350749165410307046800c00c194a03e2506100010300c6a0405440040000c1c5200001031007141c0c2c0e43d40503541290082c159034000b01c0c0ba10b01d800d401d40d04a50f1041c8035110441064442468001d11a20510081b010141d0300703510704101e040119002d11368001001d403408000d501c0d0308903c02e600c07030740141c00001e14840c0c0300c0c0006101c440740f079048030740145540e1041e500800c1c6207054503004142841d50022048900e80941c610206034a05a03408800c10301d510784056100507582400480064010203454649170082403143d2468010809400e00199140211000440001180a0090707034060804941c0c0c80d10380820480d01d01585401c1d0310414084d00000600b080040c0300d20008a40b002c030303a01d840300c1d074861052022000900900500d00320307031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 523963363 1250 523962113 523962121
    0xf07020a031d030a0b090106090501080706140c07091a090402030a060c020111030906040b060603190b1c060504020307081b040b0a030b04030905010f030b06070b0c160b0103200108 79
    0x200d40010201c2d0102c000e8010340344128600801c1c40d040c0c220300d04480040181080008045091044400404207041d00b4403081d450007640c540c544a00380a00801c0124034040c2c50f0440491004a8042c24800001c0f45d440341d6407071014034010071070000002805030b500c000007055480c261440718052900207001d000c0903c020b40c3c810b0010244640d010055548030911520340c045041d0280d4400c50b1000042d000614091820301c207010300003040c1508c00c180074018050700c1c400c4d019201c5000700700000005007010038800083d0140e03140d24120820b00d461000c44800300046600010b0095100354100c0e0500c680702c5c1d0b0a0b688660503828200e1030108420400310952401e0f42100d1407101010300b182c6c1d02c0b81d40b26190141a070004460690128003203840030820355038400e198841422103443d080140500f4040000c0d03040c816004054003049a02002c140c00503540000c4130f0441401c40308180034000189400503e020092006950ba00b441c080a008006040a819580d03600140d40b412083d80d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 523964613 1250 523963363 523963367
    0x10218061c0504150204080a0b060109120b0a06050a03050a060b0f06160204241a030408030a15080d0f09120c0513020708280f020d0311070c09060e0f07020a03 70
    0x390041c0b055409074054441000410445d2006001074152031002d00140c000e0b43c00c00c04140980076003d0f07410804445010400d1840f4682c000c505154840024030b06521030f125554080d02054106541c40041c88000000300840050038504152150806101c0e0110000403c120701421601c03042e0440010805444011466440c00321800e2009100044403080300c6040481d8401100c04a09a41031103001404140c100303080c1d100e44865034810540c80c515041c0c1d900b2800e400082e000f100c4154441003810007030002010710310040c01e01d41d000c44841e00510700d8014400a0701450600110381d2540020030a00050868040c641c0d0b0402100036640b45801c0c244905e1a8800c810060096820310080c0f000410f01002400030451651640040d504180c030740350ba82d10b00b00d081520500141040c141151500425851411309003401c0001d040c1d0341c403000a403054400d45070004d2465059603c04560100c80341d11000c26544500040e070320582e901d1030400700f294001d171900c1e00968083c602d4030300028 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 523965863 1250 523964613 523964621
    0x15260601061101020d020a0917070810021b060405030a0e0a080304060e0102030f04030b06040501150c29090303070906050703080f1003060504060e1006050913061b02010218061c 78
    0x400b2060006182540b080c190000300e81001c00c0c0c900002c1e41b1031074200180d01d080310922901030380443c0549092880e00802c0b60383c402e0003d1840904d0798012910036200c0c09074083c3c0e48a81c1c40b0030015a00b091600b49440d81e1240c0c03080701c0780f4020a0002050f42c42e0342c02d12412a00546481c5001549443c1c1050015141c182e291003d1504600c4108202000e2100312400740000350b02c5071201440f9810180308020554030140c005c8501008140e030700402003980140360b180074542040a680c2a40e82d0a40c010040c81502c81402c02008806c001340010350800200840c401c0200b507913481c04c0b05441c2c800840b9107118021000d00000c00340001f0036a01e980b1807081c00d8021f54001c5502030201d0b40c1c3d1b900e00c0c0c1519400c44064030704503551030b0039041c5030b8400c0c400c43e460340ca0b0a020400409041a00158150201409099801c001c01902d03804100ca03a80c01072048c00c030ba0b800611100315005000034041c0d03100700f21414000200203541203080c1060800e440c0c10400c8240f44945103a000002c180080c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 523967113 1250 523965863 523965887
    0x1e07030b0d15022704110702011e02030c0a0f060e030c1b01033809010f030809030a05161a030709060804020a0902160215070b040b040305070203011526060106 70
    0x41982000302c800240410240c2400324844c0211140d03402d103c030300412040b1050150444070300e540070010000140e900c501c260386400c0012078500d0540288d640c0c1240744d40500b580c4000e480c0320356000c9100b84075000350200d914038810b01c014800c80045584154503802a004903a4069220b4180002c05281d10010005135039010314002503090000080c0610005c1d010341500307200403d510f82c15004c000c1c2c04122400e8807a00342c500c00c14651501c01107101c3c00a10b0301c805010a0030100d0001266030302400a07502c0160050100c0700c1d49142c803904c0040703102041c8901555146a0440504425810803c1c4c911503200ea48401d91803501c1d0100c180c0d080c0364010000c0340c1c041d40c41c6134041407602c4a4405001d86514041920005582d070344140450790303848202c0241c000c1800e01101c800600d000d44240c0e40158400d1103540c2d6034aa038a41500c3e00d002c2c0001c000d42c1542400c00c606010b407041030000d4119060303c0a02003121241e688035500d07002c0000513409080e004600180a540e01031024400c2c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 523968363 1250 523967113 523967153
    0x919120209040f05060c0c010c0801270b04060308040f120203031207020a050a0506060f0303070525031e030305071b020111031b0705040b06180d0c0503061e07030b0d 73
    0x30703500c3c10744c0c0e02410000b0445082c0e0352000c0110703520154447c24420011400340a05118060b07506000540380b0740000c41c5601071040c019a45118031901c40b80c4c2000e00c0001c0c001c1c009110b0307580c4034070b450742c0203405c14044c1c0000c0c201041d9002543c0001b8007a02c0551540240185d0b103040381c01e0784e0150405c0301c018602e50651040014060002da030070040c1740c101501980290409050010410041d8424082424803a0b4414005540442d07008590000700d04206004030241c2c800c0f000354070510840c0f80e40301820106d1007040c039003140d0a060100f83d00c020700c03035501040665107440098455413100307621450707914100c181000c015400349210194100c404002c85e4204051554082000744007641e0b102e074560410542040541000e004441125070100c3e04182010618160700c0340050320b152025100e01c0d40d01d406442800000c02000e0060710024081e03907030380d00e02504024402140595141c45400b008400111410b03c02d2042c190341d45001020502e901003141c480203000c47d80d2520f0512 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 523969613 1250 523968363 523968383
    0x215040c031e051006090b0303070510020928050f01050705030909061903051609090510020a050423130c0f08061201061e0906050109030f2402091912020904 69
    0xb043c41004140c921814801000c54114103054010050781d06145955010794000d00a040008a02203012900007903034402c01038030b07000400c0018840c100d0400a902281400e03201c0e0040c0640030814030015038005a07040c3c184012601e004590911480c10081c00540051010781a1072500d8900395810031f000400342000401c0301e80c01001c0700d585a600454490b405010003032482c4a0511ba008024814403404110703600c90b40c4ca400e0341b214800826100720300d40c0040e0000303183e409481560b01070254442041200c0895903201d074890740490040782c0c4030310003004c0241301880090146005601090340d0394018045030110581d40d00002800e99644041c0c0c1a4128120000074800d8000034254001c252030b500e18045420301c452410364101c039111500345841480030f66003003140d201c00c0325131200c14883c1090040c14a46840c0104c04600144150300200c4441032000d035401901a06c4812102004014943c103218407000040e44070b0701103481d242e14501030151501a034034a500c203001d480140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 523970863 1250 523969613 523969673
    0x4090510050108030a140906071713090b011d01021902040b040c05040e0f06220e12030106200c040506060705030406080f06030d3009080a0215040c03 66
    0xd02910000d0f001118158004651140d182c1d50010040300940e1020303524070700e0b081102c40030943c10f205288001d46204184810030201103200000c0b40e00c501c01c4101c00f50703149501c070680301e405405250200790028202440343c10b4980600c0344440c4034884143c000b00172410100c00c0d840c0c8181c0c0b0402c0c0a0b42d1040c0c0c4d4020180c0d66403554000c49948134030341d0351030560300c07810140b401d081e80da005403018045e81c40010410259032a00c076448001000c202c0f1075a51401121005040501600141c0e01c03201d003d8244200640c401000c06503050b074400f82ca40c001182c0100343c0d90058140c00007014003441d81302010500b11400d1a500154010f40041d045510b04035954170303094559072040d8000e80c0020381880c1046104000c81194581000c0c049010b080d20000401000b0102c4070100c002e41900d03880040140200034007440465001d0324405000c1c808502c00e4106542c0c0e94101280682c054050b00503440c6091019100e0140705070362000e0848150307030454481d4165001111000524207180c05444 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 523972113 1250 523970863 523970893
    0x7020d0e15040e07232d18030f03070b0c0c01090219031109071e03060906030b0f0a0e03030718180515040c02030706051b0714120414040905 62
    0x1000681000303100002c0300c2c182164014100b0700c0c00007a080c6100b184a1311105c0844111048840c03413812000b105810000c03600340c5000754141d03407212952034900010a29503080b410152010f0140e4100c083d03035280504000581d462780704540300100b41414080014210b8006000500140c090300f90000503074201984c0030507803601840c05401da14a401c8c0310104100080889d010030300c4c0800359284a45030034a110301800d021100007240b0f0f0300d0702580a0050450f4440e601020090240a00c10300820350703030342464000b400c000c0d9041304003009036400066000050b03001d900201c0300220015803a555404104403802c600c54421150741212004000030901c1c1e446028210030004c116000030b017070400c090030545109186400f00d00441c103000c4404a07258010003603400717240d000340340410580e0340d0310b00e032000d1501450a0300c109210b020890700b060248601220160982c0e03801110f800d6a01403c0c401e0950150b4810310135601d010050340d06260030550808580188540102c07030701d2171802016 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 523973363 1250 523972113 523972117
    0x613170c0a1806090218060315090721060303020d0c15060b03150d03050a0e040e070303020105061903080a030e0c030105070224010b0906130306020307050910050307020d0e15 77
    0x4200c076480c0002c106403108007002c3c07280500800303004000b10300c0c00c0d90180b00d010742c025545820030321804000c000124054444007038481c401600800001309854196000380084415014440400c0c0100c0200c0c808200c492040c0c0041d250982c00030301d00c1541440341240c8155507188220303180c0b885041154400800c5000d4900139040b10202117031249041c0b4035864a1403440841144165946007400c80440d40110807245020024a4074506004100c00400e0141c140304613001914401c4660010078144d0640c0442e01480c021038420704d40010601000400c0c042ca400080c1a5500070020300892034026030242d0741010351001034401010302400040e003114411180000940c201118162a103240fa14440700525140180301009505200402056008042049000c2c5000284101c800c41040c810040110780c4108107550f240b4110000611030b4118041440c0107054510071000014016400e0368858030041c0e0081010b2100c0a9080700c00c01030000daa035410400c040003d08541030b0942c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 523974613 1250 523973363 523973369
    0x2030304030f050f0613030f03051506031008250e0108100b0414040b0601080108030f040b0a020c03030a1e080403120504020111120705060112050d05030c0f04090510050613170c0a 79
    0x101e9000c101d8081d05001e44556800104102098542000c102cbc5151840c618500740035019142ca42c0c9a50700c0c4a010480c0f007544c0d8104404134403884251024440c49a40b00710b0080c40005094a1700c0d6a68038003903200c1420a010355001a00030801c6814080e801d51310141c0c200030024000f085000800c3c0020821510035a8140c415504010030040301d540c0040d40c0354010200c15008510b42010b000c080b945501403030060401b611000102c840c1000c0c800c0041040e840c100a060343ea6070002e02001074811281100748042e03803100d501c40005642d0290340103a00c10794160721111030032124090035030024200100201d05200c2c551512007039400c03080212802900c0301ea003079103a5a907043d003800c83c9802c034164005c41c181141d100c42e400c00600081010110301342c1134100035460b51501d00e2560864011580350003070114000c607000ad41484550005030050040e10803800380306488405019907403066001041510400c0e800402510100742c0f0f44440640603402520038100b070701000106800c0403a4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 523975863 1250 523974613 523974631
    0x30210111207170906090d05160618120e131503200109171905030c06101401020601350f01050f18060403031a03070923010302030304030f050f06 64
    0x80081c0300e01107010b000300c0341c04c10150030003080903203010703c84140d4071400d01d18400e0400c040880ca0741500c8206c1112002510f9002c03005100b00c0c0303100400c005801c0064201601c00d0440540101c1026000f0180b0802003400a080c0319803800c410010300c000780c4070109503026107007401d035030020106100228826641e4500600d000301103c100d000100120030540202c0ca00c00203c00c54402c01d50300001c3c800350184560818000d5020349800c05034118021940407440a0040c00d0802c0690410b0760920010b40e4201045140c120f41450300499690400340a19001c0d110782c50b2003040181c030202018078402100a680320701e0b101c414400d0904282000da503600e0541c2d102e00a00400003013610400c1c0e48802c0002d001c1000a0f0840e11103036030b505010380702601f419a5a240c0c4408074120703918901d280e03074014044602d26030360740a107900100002c070071640042c5606a80c447d6840d8842c80e00354100c03a0010019400c00c1d007982c80b8402583c8080b0300485030740c402c12100b13207010304051280c684652054 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 523977113 1250 523975863 523975877
    0x90408031b090904020405060a03050f0c040c02010e0c06091903110405371b090e161d180103080a08060d0218090c06070b060f060403030210111207 65
    0x501c2808100800003000150761032402d2181c0340c0c994441c40d001e664081c0d0100e03004100398481c003001c101e0b2480e6681010f001c4c0d02800924040310b08001580c8140464180e0b0304124010600004074204e81c4045000c49060300b012114813039600d07020024094641000304401200030380c02000c044c1241072035004480c21512140c030030086180c90b1084d1580f02c0084540c5428203100040c1003401000801f10010b0350001e0112820140c0348a940400d14580348400e11b004103103000440640300d86841d2180c40004120040010160200c03d80c0c801034012a0f515100090780e41c0518406d81c0c203904080313032900302009402c00348035580c0d076a079400c1c02913010700c0000eaa640d0442d50020540d000042c40306004100d549501c00045e200d071a40c01c1c0b0b1f2038080e5082050301c0d84a17500d0017400c04482503902e0358054008a00e007000c1c000b6402d146030045004654082c1c508080702c0600c03c050050740f00140250300302e01c1103000c0b98103d5400c018032282862500714681940060602c41e0080180e0741c0700000383d94 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 523978363 1250 523977113 523977121
    0x9170703050114070504090f09080c0a0b01090e070b3708070905090118062706050f010f271413110f09060d050103030206040b250c020d0209040803 65
    0x2c1c840d054880c680043c0c025042d01d8401c101600c9841144220140d20303a5034200018492410b0788015101035019140555648c40340700700d6076403200c002e103041d1404c0003036a0000840131042d00c94000442210f001802c0c080d0f00d4114188400c0d00801d05000314161413004803d44107222005040301c40015198841540080d1400203080b4940102241d0500440c16001c0c0300ca555495505811a00384450000c0c04084860842e0060311030ba901043d40e038005141c0e0804012040110401b82d030000c0702c400c0120760fa80d1010000f0154003c2d0040d808100d080304080040d61040a8071900c18008007000d410303c045141c0902d80030101f5500c2040039850f400124400ea01e082c5600c44064104d0302000d010480707105d41340700707680e2003560f481709015040001c94042c9500c4000669101da03c1c00c5008124175070350317803c01940320304003281c0440d2407400d2303440001c41c84030000c01c4030301120f1080349110615880c41002561800c4402200740da101354403100030b0700103070360707840c4080c0c0300303e104045081d20707410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 523979613 1250 523978363 523978373
    0x20403050706050705060a0e06190227040c02030f03180a0503070510050112020f040c0c0c0f08010b01020a03020d0f0905040e070f0b041a0703030e070801051902032509170703 77
    0x401f40105c00320a0401180f190b080400041c0141c00590f0320341c1110001103098021700092042e4804464070780080c6e24044544107902d2402000752406850901031152030020407600d0388542c0c040990303c40028004a0041c070055040003520141c6001140d00991413074580c2031542d000003000720b515a002d08400c00c41072401c1c0c00307043d00609103074805e6081d61001d5800140244000d8030010b003c0c903640c14440c5251842294104a210707002880c0e000001d403070b06d914100324407603402074029541c24020070310340c29480001c603160040d0b0164054403401c07403001001c482018240c1124001c01030225400725242d0740780e1164141c0c1c541190000c280f0246406081402d06019a0200441c0741c4240810807a10904503003144003003c408900d01da40b002c80e854181e004002c003138403001461140b540c002c07444550542c0004d0082c01c5030004141640c501c2c1c40c0d418103911040f01c03065140d444803480c0014080035500307031986a4050341844007003980c5441003040c45002c60081c4000b070382e00031031007081401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 523980863 1250 523979613 523979623
    0x3070e0c03060f010c0308190b0a03260403020105030f0601020c1c0c1512050c0d09120212030c16060b1914030a1a0a06080a030309030e030f12070303020403050706050705 75
    0x41001e00300040c40034402d44000d00340e80341c0201060400243e46650300a080c1840d4021528200c1c01802071840c241c40f0304281c1d554403360848500c404001c0c04a84c80c0180c2200306880890b9416910585595641d080ca0f110b4000c0152200c0e05610540401c0d034541e95034140c9081c0682c0d803026000565000d01e050080450085a000d5100c0004148400304060780c4001801d10690840602103a1a228956004580c2c8540060454218905000c2d503003000307003066043c60808010303401c482043e072070f0308039244140c4015283c4003402081003105001c040141d00c0642e130720354002c4400050328907403440800c184802c0180202d0b207850f4006002d010150a2010b510300102059004085400c070703c0d03983d03102005c030303440407450b040214400192403980c040d0008000b6094040688110446504d8064040d04648030704030041584005080203a041c002201c0c50f82484000042c03006010040b00752169500081d030540070150204804000310f20100074144c003c0032640e03110350307039400c0c981072040c148 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 523982113 1250 523980863 523980889
    0x4120306030302030d0b0111030a090e07110c04090501090b161b0b010e04020d08041d1f1e0b19020c09151507150507030f090213020903070e0c0306 65
    0x898a41101400420b600106490030300003a500300090341004a00140c13602c10080f80a4a2203110000718022042e1348981b1003805c545990003564007589032554280c80320442c86204003a0340d8070000b101c0c0d41034a0160443d07503c0328050070001501718265182d010002d9002c840e40f014201d101d01c540301c1203d510030a031095082c4000540701c403580e4150344e8034162031010700c40c1d40c0c400040c0d41302141c1595510401014401d900400f40b035038880d0b03100d2250001c03e1100c1da2010642c0c2410001401e4801c2d1701d880c042c05010a42c01003002d09040c13009a8400b40c94440855281c5981e045020a1820b144002408401510750103006240b00803c0000d103001d018480c414081c070803180c280701001304005c0e00000d60344011100b4140102d850588074040d030040c00c80150ad8807845150390041e4500b035a011070300a4002b50f030140f20068009400030140d07185644003d412290864900402d107030039501401ca00d072001025529a150744003000705c00e81c8410381b4089111400007040c0051032800300c03040f000c5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 523983363 1250 523982113 523982117
    0xa050703021c090209070c1a0c22080106050904050a1b080a030905030d140f09010311040611060f150918010c050d060f060e060703020a050607050d062411160308030412 74
    0x4240320742c0e0b0b4501800001614088c1c060541c5c0000c86d40c58180c3c0c4d41a900026140c2100c100b0210a420007110480403034490304165500e0114040303543d00788000020300c203070307040402004074003099554411100350005c000e10405008a0f00030501380c00038803815200600030b94810f1100350800c2c2c101820440c001420301e050101d0b00d205111100d00390419101c41820000710581c4851145005a01510146c4d00c00440d00c200010041804e0381c00811a110303080e5040229040c030380d82c4928420b600441a04c0f0400743c91204006901036142203003d5680c800140a1030144100031140343d2400c0d5028084071001003500070894450070012071180c107000f0320252603030714402880c00002070304800e19600310340d00a80002035000103050080009582d219404401c44031185811480100700750803050f58280014281080003400b1080340c12041c1400101d90b6191212005004d0300303a80e40181c500d002846400390310b4100c80e0f2410f0480b40703a0700850103000401c4d500d182c2441c1080c0d01d86012009181 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 523984613 1250 523983363 523983377
    0x6150b12100609050618090a0504121107090e10020c010b12010c0c02011413060504090f061505031f0e040218040c03020105030901020d06091b090305060a050703021c09020907 77
    0x82c040d4411260b82c200da805a4440b030703540b0302045400305040d1112a0454200350300100f0312a1070b0105078070092050313000720b407044400700130700404440404405602201a0788041001e000004a6a21440c602601e0004a0b8812500005124280d8001030303818403090355545801413090030001e502c02d1040c00200c000704100440484041c000041d09500030341086a80103e6503070f003000d50310490302030514810302500740565504004120703138481c0c051900040d003000721030340c51011180111410f03110703012180340340c031450040f0488064000600d0f0901030002d41d21012607450307552441c04080c24105803600e90720b14050040c01000800349901e0001c03220f181c400c0001048031607211100740c84d8240b80c0907a49895581109019008030300b90202401d03d0b040300014418550382c81108450b400340c90302c120714840d041050f1810380e540d02c4043e0464000d00c000805019080d444668450190304005060003840d451000403003180b94075864400b650780203c902507103041000140d0040c81c61620381 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 523985863 1250 523984613 523984619
    0x240506060a0f080c09180109200301090902010e1201050103051e03090111030f0a02010209040b030102090d0b10030609050d0908010605030a110d05031204140c060f0706150b1210 78
    0x40986404181100403c88030030701145115105108881103561300030039420b01c1c2001d600d840740a4050130302c24107617610700d0600c1c07188c501c50340600c3d200c400c5a4400980c074110703031800e41c50030090402c210049040101023140e40d6000da898841040d032895409000003107640c19498620300e414640c0b641c042c120034901d0700304501c0c0031000040314020502880c0021005800e820344501d9405070140041800202040d69130046a056028204c280310490381032140940d00402c0c10f00700c0c8680c0688036080411423100b4070100740300046258002c00c05c1172020120598a8440300122801c8880072203d6401c054414000f0941c045c0002c0003401c2a01d0007001420300e0440003980e50722000c90010020700f0080d091200310782d80e014401000720781100c1a6035a805000c0034502c0340b513100301d508881003080513202404411001500750310303502c0c01030605460641a1010391540c0d4001d501c04442030303625198034403052035864400c4801814104442611491000c88500c0c10a000a1000b0b04070601081c0030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 523987113 1250 523985863 523985867
    0xc06020102091e1207300507270c0302031608060a17010905100204150504050d02010806120d03230c030103020409172d0901080105040507020a240506060a 68
    0x4441c80a0f103561499040505000100d42496007401400c00540685240081e00452010145000980204813802801020300710401240e400c0c18018082d40d00c02e030401d10540c014942e00c01a01c450142d80c0728883c00f40e0b1580c0b0010342e090f0b40310103c0025000b006101414010030080800054130341810006841d00c00086039011182d0b02c2844100315403081c418150700070030740c04540300755041400d561060b5890403c1e0382c0030f035109106046c81644560040140544181d00f901c0564000810000455900c0e800450341060007a2106034007481c201d8824611507002c10100c28aa001610045469000c40c0c081c6000d03400f08c25072141c1044081001c010000600b1400c59042d00c0d0b04540016101c8503a091007488044900c18605100b030000922022103129407800b8940481c074410f010082c0c0c0010354030075146007d103200190205480340b0051000d4505070b0030142d8024400d10481d128080f0a403100c40302880d20201c2d0200c8070100e0301a0b0135803a15140205030780407000b81ea03080c0c6800c03481c000c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 523988363 1250 523987113 523987129
    0x40f0303020d020904150303090501090311090c1b0a020f0d05060415021902160b040e0601030906020d1508060708071202090d020a03030f030f0e120c010f05040f0c0602010209 77
    0x1005003050760000c0c9040c990a11541030f603021000c00f1300b013001821a19040da14010880e400150041980c0c0f4500040d9988501c0d068001d4070b502005000b500060007092100043c0d000d0325903814418148402c04c6089160105c141d448403c1c42e001345075019003801032107079043d044619a8003070302010300388074081400026484d8203d0ba21031034000050a40ca19020024090098010791000300d40c64240c2016500192200200d503040044101e0640c0c0c0b6001d8862501c030381c1c0b0030685201810800134076990700a47c45880054016000580f410520004103011200b00c40c030b2a02c500e2180c150244040042003120651241280c10300041d00d0400300c4014000c1c00342c80d0ba45005d1282c0004a0031500c3d101c40344000d840e141d0213003644141d19243d01e4050250b56096103030000203442c181c0e10110200d1103020740d45008003001c02500261081114050180d8845941d102403992200d240c02108050b500c04e00344228041e43c6256a240303d9442c00c568035180d1503000008681c01400281215980c1d854 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 523989613 1250 523988363 523988393
    0x152a050c070b160c060903060e0c0f191e14030114280c110d0806062706030405070806130c05040f090506090c030f240603070f030507030c05060304 65
    0xd025140c103d00d1003d1070710012180d1000303005240090f000074015411402c0002034038810760b428070420802654656440d0480768805074080c0e000c2000034554105115019000450030b0214070015455034039240303464101507800008024010403c00480079902804804104100d00034048621401030090003090003a200c00c0c900c40c02d4008140d50801d03515600c0d540d40c1c6903085c00307004032110400080c00140c504455030b43c0038024110812003da00ca41880c92080348010b0802d403c1c0703001c05003501e0384544e0070200c591071010008070044155491b5009184114403600050801301d040140071810400090304180c04a03500003100e40014000c0d01c10101903400a44001843c0241d10070968007402500310041e005001d00c605200542c02d011039242860803050b402c442488603914040c070b6039011901c000c10700d6080724281c02140000440e003d5a00240010304844030103481303a0290890942c80d48c4119001c0d40050000c00400105079462402840c086804a0551401e40c80c2c40c044464140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 523990863 1250 523989613 523989629
    0x17030c030d15030b1603060b1303170d050405031308070e0103080904090b10150e06030609060d080f0c1e03071407091e050603031c0504152a050c07 65
    0xb1030061020030000d150b4500540d04080d500f403890070800d0f885507000341c14160307480019061420200e8100f854400b120f885260103032130f800e111451612508072040704070407012140c80d000c021000c4060541e0041d18003580c010409590b40345905204002c0d842c00aa10904054108890402803410100090350441c1c1c1c014043c1c43e924020341340000c008103184171004020070340c514140f01600c400c40314100290b407500b60b0006201e0071220f5090740c0c40355094003007a500c0340c1d08200240090609a103000d0f0400c0025242041600c621b60b00c20003140c22000000ca0500380124288150400400000c1001c400c42582d258400b441361000302e071280309042c0060443e03500d004a4000c082d40c02c103ca40000e14442408000600140e03000a4202a141079000415070800000c0b901c10300e40401200c2055034a1240340c103200307509070510006410f00030416a410351941d10b441864110600480e0b50030b4035018800c3c1c000c109124100810792240c140c2c40f0b02000402d004400a882002504006492400c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 523992113 1250 523990863 523990871
    0xf010608070c12031a010806030a080c030c0d08040606061b080703110106060314160c0b04080d11040611060c030117010207021903150e0c01030518011517030c030d 72
    0x5005a440a104650003040c203c04001c801e182d0f42e0f41a80900300903041a40303528155a040c000469404906945c0680c1c107811070f001500000c1c0c6000c00030800c4075080019a4200b00f0203562003410b1444450f624808103401c001000100700c41481520060500d6081c44142c0303600030a4007290200030810010560440084c9590a05000e120140c2c000443e41001384031030358031142c0042c0a0071740c1615050a00d4500d2010500881c0c186c0c02d4015081c000c1e548041c801d28903600d8452000300b02600a48186c482001480b5010340240900d503040c000f40e800081e507813840d1074030080c40e19400710000103a58202c5030920411465810450781160000c21030448964805002240240700d820360080d808a4810b02c220061021104182c0850707010701010282c4004940c1c28005407500f88207005020703000f00e441d240759580207a103c03c0d08040ca0342085440d5541c8602d066084600f0f42d007000070448150307241040b0803200042022480802040a1420665640c0102d560782c010b0030100c0301c000b038072 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 523993363 1250 523992113 523992121
    0x2030c041401030b040c181a09011b06060b03040c0608150918070906060e150901030923060415140105040c05120c040608070306081b06090a030501020405090604050f010608 76
    0x303e03400c01204000018410440840c003e07002030500414000b403144002ca21610002e61500c01c0684050140d01d42200d0341d09c2c01070948011500d510b00c0110300c071008005c1495017004640184118409445000340360b40e920300b440d04180030448540d90014040001580800045d103901103c0b07150241001d40c1c19510319112a8550402054100f817881107500c101c00001514101c150440e40231030b25692180f0303075291a00010300c60700184c298400305051000304080211548a640800701c40d41c0a46072440140b80d03150004032004003003550460302c503403100303040c40203111055070a8682150020070802c099200840450f1440c00140301c0d103849039a80f0700c807408000380200221000658100051080ca141001c000c40071030304203001d10400141e4034000078a1290080c40f40301c05a40d0403000a227030b1030310400c20780441d400000c80d042e6003151041c42000d000740c48814003000507621882c0096222410309080c0300310210000d2446104504010520400f00c00b5a000281551440e00c0c00c0700450b5070f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 523994613 1250 523993363 523993367
    0x6092d0510150305040228121505070e01030b0a270207080705030c0f0607081f0b040f05090a0632031b011b0506070c03090b03040501020703090902030c041401 70
    0x4855100811801c0b05804615450740d00d070740850310951007114046560310b020200c2e200c1c0507840e40b40035010580458000e200d2840d400d081c010860344154043c20041c3d14041216054490580b51540480c4005c04440503561701805003b0811005a54609841d85010580c8109411031035041c1c40400c0d00d03003d400c1030441c00d0740481c3c09864001d1101c50f0348400b1850305541d039074800003401682d40070314071801000240c0418541d000e5003e69407000a41d84500b044840c0700c4030400002030304021200720002c3c0c24114407014200800c0d42c60f0301030f42010310344030503c80c05580060500d886989011001d00601d0300701c0510004e044486c4500c8205c807640807901c070352030200c0c0301c841951501c11039a41902d419601d07008104400f000703903500e0000480c840c21618040664100042c80e0b03422690000324030900c10341120f0655030082c0f0b4801c06040d0f45100a01181e0710566058035a80d4000960318241a00080344000030030101030704520b54906143c04140300d001d68010030481d0800c0c1c2c007000455038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 523995863 1250 523994613 523994641
    0xf0207020312130602070b0706180b01060f020f1c230d150501110c1203040f030804090e160e130b09060a0b0303071716140106092d05 59
    0xe6024080342c0c0804031989401d490341d00601c010380e0542d03540c1e1201003507041c1702092410485103900c3c126400e10101e6030ba081c1c0507244c03100000241c40ca44540c1a00410781c1d0140ca20f00914154450908200c0b420300020304101c90b9005a031082d5001c080c1101e0b5000c4044801840101189000e8414000350588200e0040d901070954100c814003240b4528142615405001030140c0000c401400c2544c0320010758034621200449035054016045a01700760500c2170183d50104015010b80c0e20b4162690f00c2c060b503111940e0401d07502000003190500c20f590180c8180c41c400210381004280340e2502503c11650b10185003d071b40600b880081c00724101c030222180c042c544950100f5041c02d0303840d0082c080740c0c1d990011906d01c0d49040c14100422aa41004021034400d250010040791070102200c11410099101e28660600e041c0940c0d00d140c04220b03091307a4403081b840001c0011941310314200e00b031016195820403060001451071210380032464010340041504507140d0000c0391076900e40090000d55 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 523997113 1250 523995863 523995877
    0x20105120a06120303140a2702040b120102041401110d1d1e03010c0503060f010e150c0d080703050c04140301060e0702010606090e090304061407051b10021f0f02 71
    0x1c0072414881d0420160035800c100c08069207221086c80c590b441c02064402d4402e2500308445460307100d80c94408404180580410860004d0f2000c52000d01c0704c2d010031510304900240d912965030120701030001010000c0841c0d5220b01c24030781801000c1c840012103803103041c070130003840c2071003034441c0c0c0b90300e60042c03890420b03590f2032005006018040b0f03906145007249000b030030a14401c1d481c142d45103101c02c1c0668192400f45002600080607240014015101c030801050b06550103d1392148a00840c0b00e804020008014600003070f00302e50320001c001508200010749040203240c1403130104104000c01c001035600f158003854140841d00548004a401450a50021070782d9401c86801c02c44002e1301500207508488203a42c400510390740c0d804003080081420b607210999034004100c05c02007284191030506c0c0680c40510b0081c6480c2c096510113251012403c8418184030040c481c407000b51801d410309004e09445070002e044040d00c40c4c9072480d28420101e003c081003903681c501011545400303a040d1004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 523998363 1250 523997113 523997129
    0x4061d0f15071410020309010c0804030e04020a02151005150a05390c0a090204030507090b06040f0603091101020d020d0503090a061104050a0506040e010b0d0b04050a1413020105120a06 81
    0x2d9001031130a000003a43c0100e45103d01903003800442801c1500c5a140d40d482943c055136801c0e03e20b408441000041d50100ba40c000c01c611964410b00d140c0d07441c1c038126030f0045115040e51400c0034548000c0c42921071440750f0040f0030a100348900400300303800200b20762500c0d500521198013034046020f460101c0b030710020030082c0e5800b61484031028480010f5180b0000104a60b030800d880d42d10702e400c20980c130450000821030f4219102c00c014007201900400140c0324024203890a098031814002d002c50041d500203000261100f0551052018200000b1040300087c4007034060300c0001c2001941d561804484031042000c0040080c0c103901050107214626039002c7d0003402580004040c80c2d00c1900903004680c8551181c100005180c5810011903080b5140705114101ca0ba107800c00f031314150b40251501d220101d448031920543c1c0c2d60b0324413541d8800c020100c00041c00c40903410b40e02e144a140201300c0d44001000b0040d24026070303001004d803108020403074920201c80e42d8241500f07003c0e0605038001e81c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 523999613 1250 523998363 523998373
    0x6070510090605220605070c20040b04020301081506030c060a1d0102030307020d0315030803132001091707080106080703050d08060a050d0201110304061d0f150714 72
    0x8180c84180c00c0040076500504042c0a00c2c4c43e100c003000c005040d0302c5030340896a5251204100041c080741c01807580600907007040c8440c01e0403510b0744d111001d4485d440c0d440f04038091262140500d49031150100d401400d850031400d640c1000001d03a6625a4018054110301c01c20000414581e010040c2d000c0d5084054911703a2244480344018000144950b0340c8030746d403000c10007140c0c510f5100000b03680c4075801030b40c01050186a424001c6d00244400301d00c00c030a00c01000310200209070030200a50152425044041078a815824425860a40d0b4240001c00b20311160000c0d0440e03a01c80088400d40340c040034400b116a1412111614082069009540380e50a2403000602c44d0b1002c9010821640210166071101020020841d400d084c00c07a0b0b002e9024110100600490401c0e07250000344d03d206041204a01c080540380d1881c6070010b6004000180300c020311a2040002e900c0104208001034941d21903001c51200025105804510341741e980e84004110742048c04010390304c142a0356004c0301510 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 524000863 1250 523999613 523999633
    0x50a0506031512070602011805030a082a0d0e0d050906131802041809020102060c16062a03090206091212070506040b2815080f0f0105011a1206060705 66
    0xa03104d81192140c2c0001d5440c0c160740101c050842901541c010341e01c1800355140000700301c0c043d501c1400141a05500c050f6190088110500145450320401c2804441d25142c00c0340400d000242c98180070001980d8009902c0004169000b9054801c0507408860558590b180d4410308500c0044540c00402c0b00e4900302c100d150a444c0d00d60003001900d02080740b602800c0e180a200c00d050301c4003182e0090040e40840009940c1d0030200003e4a2581c03e08120407500c048103840316429109136070701001440510030041003441354980c500c1004885181010300c1090042d0700000c1090194000c0a806141601190381d55103405015036620442451001905d80d140750911035542c21040310121540c4d1000000300b14002c58003040d03151103410780030005c25000110301d40c072001f0745000841c2e040880102500032454000a006442000403004020a9208040b0040d6403d41d101a40142d41d07040145c010400424002822946c101c840b4840000301502d40c44c0101e18103105415000e02107001e02184a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 524002113 1250 524000863 524000899
    0x106200a080d11040b0d020901050d090605060306010f081b030c1305071803050a1716081c0608120906040b0703030509060906220606050303070b010e070306050a05060315 75
    0x98442d5400c105000c010034941d580390910b070707481140107030600c9400a001000c074003d0150002c014134541850143d0414480c00201800d40b8481503044400d0b07501e50081118074242013003804d004298400c1100100323890001c8040e20f0b40358005404003443c2d203a250b01170070ba4608100c0c01c0071780d00c0e02a0030b4101d4902e203450018002d0400761030141c0040e4044805d0210008102100b2040d03981182c0944181030702e41d42c44c0c1c205205482c104900c1c482d42801000844000d0791040800342d4001c080352035036985c00c0c80c078040b9807590746013101084500c0c089007031015601c0001d41754101140a01c0155450142c007001803030314040c581c07001c8090080040c00d90200b640c543c012074095456a0110b51058030b810100c5612083e0440b1402c00b9505a00b2441500290740c990500546004500020f09503440f10003080c15584151811f503492011200100300f882e5550382d40950000780e0385000c10909003008000384a4080c2445818031a903c0800030a4400840e442c0d010001600282070307100c00d014107841 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 524003363 1250 524002113 524002117
    0x180212070509010602160902040303080105130f1505130203041211032701120b060d09020625051e061305030d0617070b030c1603090e090307020405010501170106200a08 74
    0x2c0c0b03007002034051200047c698442d00964060320ba0544816505030f0a04e0180400d6505012503100e0b6603459107486551030000340700d00541840c925036403111060802061007507200030070741c0c0d0f103803200e104008010210b18541c50f045500080c900d410312620038817800070343c030b54058041881c010003080310107002d0709885820a06003500e02a266880ca4889003000da00803504d000b9401074210b8030030450060058499800705154a10007041075080c15114060002c400040104610b80c1c00c1c00001c0c00014000100440c08406d6240b20005030b2401d82d1881e40ea0300c0c0c0314081c0510707603000305c9858200e00704602401903942032001a01c003040a0f681d107480220040d03c2100002c00e80f405038036004284040c0304403c80348504140300300030f841d002642018581e000c406510950400c03104900100d07000040303115060159030030b80021500e9081c2801004100c91061348010b0500c0020080340c1154081041030ba41156800e003001d45528000e0039002c040308513540301c6034045010391f11b0020100450000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 524004613 1250 524003363 524003383
    0x14060108060411060307170709030c091d031905091305040f0c060e060304020f15040609090b0d053c07080708030708070f150e0c04050901180212070509010602 70
    0x496810281002c5060011620013640c1b07041c005a03c861b802d4000d03030102c8052035000744240c9401e401e402ea40380c0300c0059110481c2c00c4003001d1074403003039510088900c404104030000500006145000303c080310000c819034500040714284400071a94284d10703902d2240f542d40b008480130043c04186040e1034010010914400201ca640b52081e002140f50b9100d6440c0e006221800361415265031115000c00c14042c5040505d1684405003032410075640e038803203010300001c10343e540b10080170b00d0501b1188800d4414031903045008699034001c40c400314038001002010f803462202d9404d6002a542c0402c00390140300d110181604113007400711400c103080015907808442014041d10341403510782c101541c807480340d890041d080c4501400828045043d00103412440342c451803040036155100c520010613942410100441c035080840c405000b0304180c0a02640302c1c1811000300311149100862141c4a0f1500c200a409600d414004124600301008840e0150000a20040c07035503a50300002940c07410450 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 524005863 1250 524004613 524004623
    0x60b0a0f06050306031506010c0b0613180614040b0114120d0c05010e1203071103090405041a070206310609060b011e0903060e0a0f05010b1c0519140601080604 70
    0x540d503144070040d070440142c05447e0581da520307100203a94485500b00c0340083c00c950380c480000c01c00940d203d2080e00c6a00f481d08619035540d1103c0b1542d0030a03204603401c00d030b51040214220410400041e03996040d40b4150b40c1e40c0340c00c0c100b540b4803080100c2c40c454000d0b41c00810900c0f8a200701110340c3c1e04080c6514299200d41c00070b01c408405102c4050301c4020304000359030945024000b02d8081e80c0036130044010303d440135040b282003049880c00107003a11010f40b010781d1480d010303134075400c241c07450583e9030396200a540c0020720171401c055500c00782600e08991035131004460081003c00740d42007404409206074116030107000d59a40c07810000002e04101c04900d021036104650014591580380e588800d01425440b02c14000f469510360b42c01603c1070144061081c040c8150620020340c4840350800218010400060b19080207003d01151400401140503442c0c03030886403c001480005050000d184640f029a480e2400d07482c15041c0524081594241d40c043c0d8400403035921400186a48a14022 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 524007113 1250 524005863 524005873
    0x7020405042d0c0b16050d090e0f0601080403030e15040812060102070b0d05060414090f01061413090501110c0d030c0e0303180616081b0706020a060b0a0f0605030603 73
    0x2c142c034408805242c0c01040c0e40c3c0c611004000e0788400e04050b01072036451020100b4103950640d18141050304a01e0780c00045400d0b05001e100020303115580c2c07680301235031100c100414144a000602001001000282007648031001c2e10f04200e03060080d410300d4806e0825000c49410316160a0f00d9a030005050034400e9450140001d0580d8800100350302101e408950300f1b440d018503050300d0340180c00000c060702d800a4540a0b004c4034481d603250014030801c000005090318014002e0442d00b5610142c2c4005200301110880c03082941e104c200381c42e402c89204400158501291401a01400b9049102c3c03000000c0440c41da82115008030341c0c190701074a0380d901005500c446c801d068960750340c880e80d00c1c2e070903500c10702c080214859810230b0741024007070051096003071503a00b6140ca01d0b0b060302140d04560140c0b001c200c0075101030075040f0001510050801921440e400c007a0025558a00548054000d6807600c4041843d501c0310307420b010103404403180380c101e4580c0b900030143c102d60051ba8114003c0c820 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 524008363 1250 524007113 524007173
    0x1d0118091a011403071412010b0c011407090e04050f011e06060306032d080d0e1b060304170c030a0507030f140f071506030b06120102030114010c06020702040504 71
    0x2107400c0162801d2240b0843c02d0440d210800b00305c400a140d5242c0c04043d1004200401a05089000d050300034003101d5101e96a030000040c400e801d4814410a5140c07400c4050244910036030440e102c1800c5d116100c009038859596410300c0f925100189001c81d07903d520304507a034402c0c000c42003050030f980b4100b200c09002c0a503490008608031069488054000355281e03004001e0580401d0140742414041c0642406600c21622202800c0e40000f202c0440c4903690b91b60040b140c5401d0000d4a10681d120080c0c004112200000c110984401000100050b001580b1203d40c4c04c1303d070382900d60501840b0308032500c49204d8000600140c1c0500300c20340c049084200388110715882464590040c0007201c02c810b0801541d0551206950080c8000315603a031440c0801184020462058200541c0900480c1c80e0a0810401b44a503800c40208000826401040140b0011906214072107802d1020710340804114002d05183c0e0081c050500005e6115041c0300c24032062140c3c0b043c90380d00f80c154108161410b891 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 524009613 1250 524008363 524008367
    0x901080606030318061903020c010b06030906060607020111070f03060501080102070201090303030c3e0604031718063615060a050a03050d1209031d0118091a01 70
    0x450354264168010001804010341d07000c108101480e0207003885d0b04004021340d10031010301a040403603000940c041010a0350603070034040e0001001094500c14550f013011007040c4d49450300200381c58003c1c08001000c07021a4410022071706522018420740d0702194640d042d201044d8002d100070b5845a09100020864181c180700300e82006074140c6503c0c00321451681c081c2c024024800100c170a06c02d101c40030601d0710301c0d40c480003040360591501c3c4000c0c0312800300c02d01c2c2d601613070341d034901e5002d030301c41001c2000181d000540c0100340c20750b0560068003603a54120515031020480c181076401d020348c0003030046045a6821203080d030445a500b041c1141e6210400c50030781410300351110030310303803101e440300d0701d40030b0800c005582000b000303019065195162804901402c0d0303550300031030716544451201c00f0403c3d4008152444440c40e00000e000000140d1002051060005254081412824100001030f80180e02040101c07400038a04200e00359110070080007042c5ca00c4450130720401d0000c00c524198 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 524010863 1250 524009613 524009623
    0x903040e180105221202030f0d151208031302030a080a030203040c050907020703150e0a0b040c060804020a0e09011407020f06010b03010f0b181e01120504050c06070807060501030f02090108 83
    0x120b041a8134001c0300e4980f00302085603045080e081d4081004403004101e81980108180d01c040c0402140d03d100540f0304c5544901281d1200f0740d5410751906000c00205800d04881e0003001c5910400d2620800b40002428052800d60007085010001041c019694168000c0c610540c050f40140c04420360702d038140492001c044a025005810060041c0009400555903a03c12140c084000440822503088a45000f007214829140901001c041100b0004e501c6040400303044145086080d5007050b03404100f500c200f500a600505e9070070000946114000d6014912042d02690640041c0c141130300c001c2c0d1a2800c4100e4480741e80500400401c110402e20107d0f0f04981841c4800c0010310b1815904000503005200d94042d144c80c0940f01d288540e1300c211011a941d01240f4441c0c140c8503800d0009044035010f80142c0b01c10500b0704007044045980400c10001c104401c2d1145070b510452413a22079220b2107504070090225140000110034042d02421902d4201d1090300c0480b0140d80340c0b200c0564403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 524012113 1250 524010863 524010901
    0x90a0b090a0e011103010807031b0b0a08130c0e09100b090103030825030605010305070f020a110a051c111804022e020a15061d0903040e180105 63
    0x460101d51148000d5200500407000031000280354620030030302035019403080c1c2c00442d2580c031401d020300920016000c0031703da0f8038108031902c4006180031322800b0240078048c80302050183c0080015000002c003c0010741c416403080f400c0382d1301520740ea9142142c12003618203281c203101c0c800380410000c030b0600c103d0501c42d6000304040c1d0300fa803030341e5421111000000c200e03290202c4001104205020100c040601d141c03103d48011400608120004040358801812482001711642180d1030942d00400d0b50b00c521034108025654000d8510086451500954001394000080f43d0182c07490803011503030100c1c00b41c86a100308000c2e00b48030041007462039501e00c0b07600620303040401007001864119240003412801341c1c3c40744981a040720340340b0030054070501d00c040560809000c102c20010711200c0344204400340e003c1000381606000c1410114803540e05040b000c40304030404581a0314041060303400820301044c075032419140c081c4001c3c944075081e05080750b0a600304000300340e110344002804c0e098 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 524013363 1250 524012113 524012119
    0x1b0f060915061203190512070f120507090807060504030c0e1e07180306050f240108041104110a08061807050901090807080708060a1401050d05010f1a090a0b 69
    0x5031100410481406010300f01400144020000b1100c1000941415031480e00d0907101c858075000c0110b03012028840040409040200311121210080d80082518843c0d0141050010b81036a40d80320039a8200d8858200c04031620890170002240fa900400074000e480c410444001d41c55660440080081410b6501d205005010850000000038060041c1c4c2e0060035031070460940c0c0020103c040e8091010380080e90b4103a150b00400c890b0740004400342d038000030560402c04162000c1c2020a02c0242ca0f290031504000d5030801207001d00c050f0610201c2d0400d0004d20800506e04909042e00255000080440100b10b40800141c014903000d41c0760074030341e1801d88103150182d903000d104507066031003031004906004103120041202101081258054045500100000c5080503125071510b00001e04030180756003056507142c0d2840314000b505044031000c1d5020031100d07401d0b2800754007501d05084d401480c286400180d1045a4038036a00d00d404c40300c20f6036480015210005500e080c0d480c010312040e0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 524014613 1250 524013363 524013403
    0xa0605030601080d02071401050f030c04030206070803060111150a0e0f1c0f0302190f05071a0916031109190c081602010207050a17091c020f0a06140f1b0f0609 70
    0x103840c0a0000250750cc44c0188100c945410b44076400100f054000090640316030401208200c403558000e82a90000d0302003000070002d902c09903c120740e40103401000c24807440c0c2c4900c1c01450003d802c0104400d4010204103460485480e2200207008003200b244480018202d4242c3d2000203000e482201c0070035080d00803040e0301000c0000c003a00c44409010880040013420080c101c089004441804064240e40413940201d00301b0b0906030340307400c070000c1c41c040c01c0ae0000078080001440c08011062860f109552503c0c0c150744d00c00030341146060130389406078814101a454243c1c10352000d00030b8412812a0f00c001d40fa180100c004038202e025000004005601245050002c03032103640600b0140a0b0701d006451138260f080000c101514644041c07000c81c0480510580c0440c0b5051701d41c90000311080d511101542d1500600030818401190500d1105000082d1844840d85000c1110740c2c044050100e4002e0b06080529140c0c0c44a081500b02e00e64019030000c100c041202103040403043c41c075282069 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 524015863 1250 524014613 524014627
    0x609010b0418080720060d0b0102060c0906070212030c070e040515011503050a180c0f0914160203071a06040c02030f04260a150c021f02030a0605030601080d0207140105 74
    0x128048079103039043c05c0a100d0006404990740c0c0d001c0103207c026541980070075061499000a49490030203089030300b580005025020050302d4007016552180d0b011920203600d002e00f002c2450552140046501c032074010020040750b0b2009480d03003d0b02441c07180e01240c41c00000c1091411145d20203005090200960804403100644070b500303ca03410900714080010025500014800c0302003120340112000d07441c030b0350104001d503200c040d8000141161b610134050885501ca0044103d10000e008010b00c0e0024103504060900c00c005a030704540c1d200850311110340080354611880a0b003161014402d90070104000303140c0d41702000303a81490041d41d078414101800d100c00424422152502084c0034051245110f259140412100100d180107080300b1101c41d888400d11015103503611110f41c1503600c0b254445184102085041480b120301250040e2282c565036003440207810903903c15030b4540709403030021455000101c1c0303980100c3d80c04e400f140e107407590310b45910b002080c5220a46012036810700040c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 524017113 1250 524015863 524015873
    0x510031a22020a0503100c031803020c210613020f0409020a0b1c0f0c1e0c020607020d0605010803090307120f03080405120408031e120a0b030a050609010b04180807 72
    0x118890b100500444241d501e86001c82c0c0b82022580c3d1000d642c2d9210711a00b80d029405114655503580980030075914281541c80103917031001c9100d1030324000d804540c28240719604400d00b003515101e000e000d550407424003503000b119050300f00105a2041c0c00782c00c40000b0034070f8035120305030300c042c2d001d0a80703080e00f483d0441c440d07402d400582410a030100b002d09036590030340301842414030782c104e180800180b545006074018000d440a2141103d4000c002208124140d0000710707480010350304030360803680c0301c5091010132141d1105c124020540350a041c004a0704a07408006170451340d6040c1e0407510500d07a00c0070f8602c60700c11140005080c031407205010102003481000d2041d400307800341040f80c541b51012458000d459000794080907d030781010a2416150111944000c06d030f4840520030750800903003000f00110054041c01200c0500d1340c0362258002a05c0501200b50a10f8225060320701e01e28251241c1400f800c49040f04904c078915014507007900300186200602c09a81050b102800d242180d912 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 524018363 1250 524017113 524017171
    0x70e06280c080304050a12080103030e100507050303100302090604061a0c0a0507150f0e0306070e01030f110d14010e04060e0c1003140c090d0201030f0209040510031a 73
    0x204801c01907002011000b0554101c0114000c40c0300f417005154800080c01c1041108034101c01103400c000e4210010000704e90b1090320a81c000388100e503a004800300252090751144507a900c01002400003102304420800f030020940103c1e0300136114030b00c00f40da84408000450300b02c0c0c0608049a0740d43c09a40340000071308000b5000c500800c40440c1c132442c200741c9071383d0b01c0c2c804564001014a1444100e8050013544820480d904909509008148240c11030000382c54070781c02070010040105150030340c800c80c4e1294200300050500c0c05400c100e80884c1c595682c655a01184091107030b0740c1070940c1d82c6140403002c40c80714104c3e04500d0240120742c41d642e0b034003000b800f201100a8064031801e40c0d00d0a2580e142106070031954055200010154080000008540d90042101c150780d8400c1c40342a9140e1030b00c01c00003220360750902e8001040d0068458110007801050403041c2c00520308010040c030a441c50040800f070724064148050040020076407403802c0c4004441c60403400088900001e00d00c1e2500705 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 524019613 1250 524018363 524018437
    0xc04020f0f1c1d010b0405060132041811040b0405060c030c07061106061504180e240c1c1a0d120906080421020a080c010203070e06 58
    0x40b08244001100041000e80b0021008828001c071400f041c0342e103244003413140c5411035005503810b20031840d091001030100745001d000704041006401c012481c054a461040e581030f941011407944860b141c5410101821550603654030907417902000b511880c10301381c140c60450310000061440c0c40e013000284041a040518805201c0c0b00500800122420502450014013000c0da12094010120f01d121490680054150381c01500d46688801c000041c0360b003100c069071001c0194155103441e0502c2100103007510701402541e8004d0301004000100d620502c2203082441e9070346c85c042ca41740c0503282d00703080c894070403080307036100040c160842200540d8000130b4a11a0221442c5030316008040450b07802025410122a4010741205020803140c200fa0000081c00507403801c01c850340380a644a48001075038485070756103c1e50107000c07540124420444403050580c403ea460351100000e00d0b03803a000c0d40054a400001c500c58101505080c00d0440545503c6d003810014500c0c0300c0c00c0101d043e00a0940c2e11 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 524020863 1250 524019613 524019637
    0x50c041104031e440403021e030f030f03130305070b0a0618110d09050f1e0607050a0e090a020f13030213050609010608090c1503090c04020f0f 63
    0x40710010120360742c181c83c08001100d0102d004890303409407411241d4202070001558042116400b4108001030380c0303040c02e200f40d06009800c2c0300200509601003050080c0c1d44020340c40069850b1680820880d10111121038005030210b80a50a0140200303440e405528802c402c4080f050000903c00802c03407401c0c14100b4041d04009160144513241c0580580080340d201c0c00c2c040d1141001c100020f541030b4144016840400c0400801015151500303552058412101440c0e0b00e0315203100c18020706001c000000741132a41150300d44035034003801d0003000c032000c00c80b001280500000210000d0007002140e5400304581d5515149408260030880035000250042580030303424807005941c017140000070318011003111145000702d03140d40704104c0011000440200424102000e01a282d119048290305440c1541000d01a540e5150300081c40e141c61825200e40c40b41d074201d42c88001c001c200c0011805102c44000b5116030a00e00c1040c0408d0f44204081c5889200081008802e180501c1c000340036192105 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 524022113 1250 524020863 524020867
    0x50f040b070c081818010812090f040c020f100501240306080106140301050108121914070f1a0c04180f0606050a02150402030601090b0f0d0b06011407050c0411 70
    0xe52585032064004915002441c15461341000c0140303001c4658058800d0850350450256060424003500da0920303060f900040305011400310f00507a19002c03210340d9844094803c020000c8941d8000b59032f035284440520a6004148200c00300d85401c0c011241650420040584c0c1c810001c2841140300c1c6040480d5010196aa18049103020081c000c1c200101070745141e894000c81000109421118107901c40040c42c1c1c003515400241c43c54070410784061a0304012103003082200d0800c19602806200b00c00100440001040c604003e0300f200107622050103043c150a40100d41d00072104883e10658903040701078024481007240c61044000c007886005603107000300e482e403000d80b202416074201c6d40001012a1021443da083c45504010807004d04040c600400428142a008030362207003c18010f0707101032611003407880010f4803800a45c03420036001074030781c0e031070702000f8207024036044021780b4414005030030300000300107400c40c1f8400d440d08190040041c000b880c02c2a401c20005101c02c0c3e00442489100b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 524023363 1250 524022113 524022137
    0x3030702040e0d0909140403110304080a0b040b090f1b0a1706010602120a0c02091b0c161403100b0a1a0d110a020d03050601030609020c0f10050f040b07 67
    0x180e4080d4442e46946a80108081082140c01500051860f001400c03041c0c0382107003111282044107030280d04a501400c1c4108020a00315401e4114032803a080700380c041c410110150f0810001c018100e1080d80142010f0101d616112000740e00d40300480001a00c42c0e0100305410004406089043c0321660300a01d245540c0d555030404000780190b000d081515038105e0401000465014007011800c40d946255840c0351176081d21024140851075032010f03004140c0d00c400602c4011711644240c00d4031204400b220703190145c0c900920307901c172008072001204400031100012140c41d00f4415200065004015001960200049000400f9130140a55000ca801140000c1010a07055030106101c03003507150720b64866021603400c1c1540c982d00c94050300c00800304804150300c0d07030110354010300c807842c0e1401017815207412004074050b10f071703d41101c06440c1c40041d0309114450001104203108219405407a80a000c90000408071242210a03503020001c10700024000340d503003070310b490348a90141809905155 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 524024613 1250 524023363 524023369
    0x110405100e040605010c0f0305070302030405060d0c09060203031e040f0f030906090501052b0b0a06180b04080a08030901180b06180103110402090f1003060612050106081503030702 79
    0x125050080031038841c5512070074905042c05150050701c0e080c04c03c401003800c0b0355039180ba178880400010f800c00501042c6a0200340c424002c8400801c4000e20041e00c2b140e401500f54000c0000f0081800030034102d80b0000f80040c00032007602e1266130f8400c000e40504032507449003d21040c3c020801ca4200210312104e40000c0c680880001446000365549085030b800c095001c0c180b034149400c01814444280f2401c4002d001d00140c0001407441c0301b01c50014000058400000b030000c4510140d441019000003088480c0c0c01440c504580400c561004035065031200c1c00e0200748214001d0300c100360400c80800001c01d0b0640003c541090b904c20000a19045403158507100c401d085400315800701c00d0070b00b032000340d24044104c1d00c0b034140c0c91550b040315545503943d0492054010b0201c0c90160b070300841d0051481e40c4480e070700410300d54003808617417101d294500018000c1205000700744c0070540c1c084c403140d0798230414810b1505940c85038031b5440d51911407054a1000102c485222903162004005440041e2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 524025863 1250 524024613 524024629
    0x1b020a0803040905010f0e01030203060402060a23030a0c081b16060504060519020c072601090b09070614030406020706110c010b091501271a070302011a090a110405 72
    0x30469000211541050b50204c1c0c641c2c2207074800c41a1f9a2403d0050001d81e402203140d03030300141c0c1198020742d2620034000640301c004000c20085940c0a02c0c90000d948006018000e52282078040360812000307864400540d9034030340980c0d10100110b20003c12040030345d03101c00181001503003216501c50300d06a90fa140002c1c0c5000300c0c1c003100c442e80c03124103000d080d0300c141a000e01d400ca070b1150254107001900d01000c2d960f04141c0305051100494510814500152200c0301c03810000c240001d20a90b41c460802c3c03a40070a0945441610307100340030b40020484c0c410351801c02d50301d481c03440d0686140c0701c0f9140d040c041d4200075020303502c40b90703030303184449255200800424555001d000082060400c1004000704008006c1000c4184a00010703040402c1c4e82c0401d280104110201d0170142502c464140d50004084980060865000d2842001d04100040011740540c038420750090000080d0440018001c8602914450f005030f4082e000c5400d522407504640e43c8504809031660901e551107000529603 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 524027113 1250 524025863 524025869
    0x22407050307021504050f090a0e1605120a080a11101b020d05030114060c010b0a030506041101030618020309120a0309020f240f0408010518010c030506011b020a080304 74
    0x1640c000100c082c1141001e1828406001d248103020f81071905e800045402e104031407200500c5001c401000802400141c5d2100d01910612002c44103001e8076214080d02c1200b13140203280c440c403102440da08481500003844103029a108880c0b0781010380a150940d010001004001014020f150b80120a981140b10b81e20900d0460518051070070b4820300302a05010401340c130304040050410060049541080c899000c0c85000d452566954401c444d1483c0100902050941d0050007c1e40c00014440300003000360040c0d00880d8800062869580190103c4595101d05104440c411040560035070f21a400303076600141c600207a03004030032900d032044181d501081d43c0b000482c5e5150846425030401c0324401c60406000d8881c01c80380030030f030703104089241000e80d035036540c5110014a80f4030b0f4402640c00d81d00100803a400a10650a1007001d10240003d103410301c3c6103039885c0102c03600109212b800b40300d01400060f1250402c2001c030100c81600d05100100681c0c0140c00b025000071000b008100401c02 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 524028363 1250 524027113 524027123
    0x1803050d050301031202010509071701020904050c09130b0a090c0c02030703050d030608010605060304060507091203030501050108070302071109060103020c1510050d171e1b07120f022407 82
    0x42ca44c151300c0c140c901034501528110031a0324103000c20481c160006134420a4135200e0070360040c0304d000510004d01900c2000030040d0000e08101c00e01c03d002c1e1105020b8000548200d42000309640d18004007022600001c0d5071690004008400b0011290b080c0d0000840d41c4091405020980082d00428a4441c080d8400c07a9564840790903401c64660620a49015012010003403183c9072400000400d1800041d0014041c2d5545a02180c40c0303500031140380e03000349200290950501001c2c02c0c043e00400c1c1c24881e07035001c540c0100000340b200e0f200303100300e40c1ca181e84034446110300c2102c0c40c14044101f4004000314189a420010401c1c0e00d01d040101e240640101045090185400d00b2143c0f00840d095000754020b22480d1402d20000306003000500300b4081d00901c1c01e0301c0c1c04446020031503070300381844044105c00300040c26074002101000802e402d0302103502150806551404c074800340c501e20100c00750444103e1030383c0100501d401c19043c8584004094198803201c19140c80e0742090340303d40b0044035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 524029613 1250 524028363 524028367
    0x6041e090309051005070506011e0f0905060310050609070e270414010c08010b0307170705070c08120a082a0406030e01110a0c0f0b011412030306010c031803050d05 72
    0x9a841e14040711056134500b464010305001066480a41e5008180074410b0300201c04103d0751501c00350605118000c00c081c1068080650340c0d0201c10740242010745e40325001e030260f2040c0035000c403024001e8038010b550181c8551400e98034144211041c028001405501c160250000001c10792a4a080700b0a04080185d80301e081c1090b1504801040018214400d11b034103242da0008400c0d0003070612411a080d01c0718465a03a035455100322070240d400c02d040140d0040300414000410742c080701400c00544104040540c0c030341c4841c84281d032017421038481c0c180f40004100803441984606142608404402e01200f001f41c40200074032061110302c41d0442c441c14002c2403c001c40d40d8103000f0118401c00d070900070404807941c07541c0320689106000403030341449080e030424000c110078581c5a00d48650003901800709940c440441160104100300f040f071290450410f400f115010101c04c580c066101610b404880c0d00c5240d80a942e01e00e42a8000145078110701000408100140401001c1c1c44880e51629 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 524030863 1250 524029613 524029619
    0x40203090d020c09040b131502030103080c0c150415110f06190204060e0108040302100c0f12050f0a090c0314060a050108010902031e0f2a030d0806041e090309 70
    0x3460403000783c40e010f100b03c0d40013007440081441483c3c00c94000c1c0c0a890350940da1502420300761260303400554010103043c4004000021703c0000b50160548400c0c0f40b040c4d4580070184400c00070140607140740c1540d203c40400c02082202d42c00c864450042c2c010303043ca501c0c0f044543c10603509008083d0650b002030f410003001c21280512811804c044040110700450401d410903d0080075400c1f880c800d82d0502107100c01042c00c2c18002c0180301024508188103020301c0302d00101c010f104090300e14020010139141c0d03036030796148080c07401007903c1103c440010000303030740c2d40c0c40320034020340841c05060b605142ca00340e001c0081040210803100d00ca8051006089a0400e02101c8080302c1050340b10304201e915200704000142e030b01007548008122428a252114171200401a04250408010140314410342418801410302c042d800d8816170700c0d0f280101500381c040400c6c5916096603000ca8000502684005086440c4c580d10848140144001003a0380090161200d411200340b50000d80204042001c10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 524032113 1250 524030863 524030867
    0x2102010906140d0b0d0b1014030304180f0207150b13022b020c0f07081e1011120a0516142703060712051006050f09030705040203090d 59
    0x304010031052405084162810140b52040d0040080840003151a0582082c0995031007282e000c02c1034000f506c0c14003c0c03c1c1640c402d000c003d2180304d040340021000143c02800e103070200540d01120480340f8a10003840800c07103c64020b020321190a00d81c19424041034011038903105181c80902202240081c0c02043c03c41041440e9035a499607990403401049800380c8030242e103240c090072280c0300316007500fa051031501d408081d0085055103041480703040e22903100c0c00f6002480804407207100d03094078000354044460725001e6100090341d082c142e020f105c0d80f03e8030034256808106080b42d51040700e8201070001d1500794142e0800e03070711081d41ca0713111024411b070f0040301180c1c1821081c050a12002c81c0c00100a862150300a25541d008452004c800000210211030002c050b01d2134014191072040c90034034800350102d0104205200134924140c001500100194501c00503220162221130901034038000a031581c0c2d0180c1052070b01070007034000008068030303140050b5024504001c00307080f410540d01c0b80 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 524033363 1250 524032113 524032127
    0x9070b03090706021b060901030207171c320717010e090d0c030813050c0406030819020f070515090406030302030c1b0f060309070b070b040c060e130b0a210201 70
    0x2c022840034103551600513603549811aa07d40d0001c1c240581c80d59428200019250800c010344211007000080ba40000200408950f01c02040340c0f904000c00b80d00840c0900408903600c080740212a8018080c680c40b000c0002503903848001d915107205010040d10725900044801e90000d428034101000b4044c00c2c1000303005618140205141c1114a00034503100100648005040c03140f00314074000070325042c08414040d45130f40e480090014401a03940f0b14000381d0a50100719000f034101c06c160782498a551020440300440d00c070100047c04105d0a182c04c000c031101c0f0002c1e110300c148c00c040001401d15255405250300660081d000b444d11569050409030030180c0d0040c014001d0741d088405894255034848c00c5a880328420b0346c4841c3c480e9103e1400602c1c0c0006a0011404074030041500806c01658001c094842c0f48910744418600355100400d803600300222035800d90014100402d0441d00070290300900780d20b00c00404900d0019070707901d07540381e08000e04a000049080d000e160301d815035800c404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 524034613 1250 524033363 524033383
    0x1091209050105180108090c0402121b03011a2802070603061d01140118030f0204110f0d0b01210f05060303030105030706030209040b18040b150a0e09070b0309070602 73
    0x3c1c0940307000c1910083d200b80007691418a4140140c480100321555820480070302101d0014104642e00c1210b2006a00c4040081b10226030b1504910b060801c5040141d0643e070494011165200d0320110140c2d050b0a80e41001c80d004007a075205030002d00340c02c03007555818014500c0710b4001d02401401d0800c01010b98800d81c01c010303800100c41c0c42e100c0116900c260b050f4112103141e00d41d80c8001e41c0900040302e0031030492005400d070510300b000200502581d03140c14100244221002c0145006494100740140202c100c00041524148004600104503403c41061200d0515012580040425642e18294000601445815510040450020b105208160f08800304900641c11985000c000039516203090045004040d00403e03841515280c580260403c068000c0c460200c000030007070143c0d5180e904903001d45601241c44c01082104600c9440221640c0700034200e000402d04105400030022409890700c2c0e082d00c103104000480010480103075016160120241c050380c0c3ca0943d00924100880c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 524035863 1250 524034613 524034617
    0x6050a120b1c0c080303161205060901260d02030a020c0f060306220504060b01030507081014030f010504030519050301080304031227060f030b031518010912090501 72
    0x4038522210781c1c400154070301180032034034507002c00e1849240c82039403203910380e002c40b50610011052108600000c400284416040e81e038504c03040c1d020000b04416510290340d0141c01c1a07214005001c1801c240701c810030380412000598440369011001c262a00848103045001a04041078800c0e1055051203070019082080740e074806680744400006855201c0640524850388946815540d9003046000e04800b600c01c107081001203142c01d082140103480d2100341c0600080ca010005600a4050008107010382aa0f1800c0c01203182802d44c10303c03a0800c0c0c40c82035a03051045c5c4c4d212261820702401254881c9100e81e9489854008404820082200d81100001400010f000600c0206000802c6d034041300d41000c40d5440034840304d24142c8003485004005000d40141010160901000f894041c1c100c0340703140d42d10100b030782c00004100c3c102c4228440480d4107410164442c810502d52201641e04103091070507010003a0155020325084500f058811244001c40135007600d00340350884062802800d081c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 524037113 1250 524035863 524035871
    0x12230106030c2606010e1f02031c1a040e010f050a020403110607150b0109030f0b0f0c041a0d11070f0209070e0d0609170403241506121506050a12 64
    0xf0503544883c1c040c00400c15030400c9440749084031641e80e03004c060b500510490b0807060751604004802522036028005400c010614420b4001c1034040303a1260b89407a444030f4100510400c4181c003000058030240481894541d2960002c41e034001042c855240103540c41c1000603500c61851030950b52081d00d04d41c500d40f003840113225000c04114007202c1002024501e0b02d0025180c00b54500503241c0c0c880f40e400141c07080906c45a24000c00260100e0a400341182906401c600d40c1e44a0241107a03110380d01a811904014483d04c0041c11205400780c890200c4249010030720400303910180c009904048015981c100f84401d0b81c209500300b1040460b0052102e240c400e00459040d00440c0c1c0320050303054001d140c0d550340c2095206028446880e010345075201e50045075143d0b03590a0081e01841440c504030460320101074020001011072241d0300c40030b50740c0300c0100342403498004117442802e50032000c01141511642c00c4019114050b20100181c5a00d231101601e5034208000280340c1451003810394040c0b460 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 524038363 1250 524037113 524037167
    0x2030a05030c07060f090303020702010216060207060c080d1e0e0303061503040609150c0305010e0609040b0c0c030406090312030618091a01080c01110d12230106030c 73
    0x4030804403035000551102c0c040d9503014502e003134402095a008001a91882d280709007081543c590000c0250328000d030300712010703a80c0440341642c00c42c0350361240c18003580c00603000300700a90240700c0e801030349401180d103e4105002c0e41da2460079152194002c0045030786c0008411680e40c900c6c03059241c4005030400550441c42c14201080000d014001c3c2d401c1075800100004003044220307009002c100d9807003115850998004110b900c06003a0502426011900340400403403c5108900b4031343c4900002032130100180c5990b2251415900090034000450600300007204001d2030810060004100c0d81d82d441c44018594100f554450300310307680030b40425080c040100b000c1403400050b81c404400480000403042210b181406000488801c04144004481c0c00000d00c0300c0e02241c40390200364203881d80001c1100c1555410b4940b0121055900403600300340142151003502d83c000341d4864000400380c0c2c244c0c015501d00b0b103c464002d078080030000b0344842c0c080742c5c0954800c13240c5840380203a410400c13607428 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 524039613 1250 524038363 524038367
    0x13050108030406050c010e2a1206040803091e06010620070506090402070b0f0a060b21070e0d05010f1503050703020402130510030228020d0e120708011b02030a 70
    0x1c2035102d0f08003000b00200d4100c3c0380090039071041807070510ba001114040404103494501d0315581c4003001c1140040c40305950000e0a215200d5a501c200c1000900065179456035070010725000a0800c10741e510448e00c100440f480d00010000013180842e008003170780c0d85081c500801d45420401c4055000d90840f03820354003000001b80e0801900c00c2210904c1d1594031910109000303018500c8041c18001080050003e01d86185901da8007070720030312006220954481240c00c545108500700880c21501c09200d0405950106172103903044841454443c03509906180020084c903140e49080c1c85030795444c440c0c10000d1051b4494202041d10001c4040c0c0034a2950301c0300c1d43c40e0300b9948800f03070040e0f07000500602da043d50040d03114080e2400500298805444050080094004040820541072070341d0310201e940310000c04805044000764014a0b410a11007011140c6260200368650072021a9030882c01d441c2d4244481b2020b0401100001210784800d00700403549401c0c1140c14055410410000035415 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 524040863 1250 524039613 524039617
    0xc030b010e130b130204030c0b07080f03070302071719020d0906110a02030d08090c0d0b22080d0b01080a0504030207120f060614211903050909090601051305010803 72
    0x184084503100031010302c0c55030000c09802d41010040d40404004800315400c60160301078010380303000310710306007625441d4581d07000a40301e9408007800c0c80c0020701102052451040045034492602c1c6005803c1c45c08036075540100b01089403800c150f591f0040350f4103058030600b10180710030000f10300c01890036200c1c408018009000707a002c1c0c60100202407000318101c8000b0081e0800542d40034045801c20340310b6103001040d00c80166040401c41c0106802001c0d40d162000c07121030169044820201c00b0740f41c00601201d02c42d07940c2a5081800000302e001e8004c104050f0151200512402c2c0100381c0c5a9072000040140c0740c000d010345006454201440042035002174200309071080da4400b0031680130b89041c401c2e10200c0b0040020105810b00c40041030b030303580f51010401c1040055922440407458501040e00301130030000d375013400798441c419107080c02d1021051158494000d041440c5040048004103203100760864242a1030b900c5031004000600301241a003a5441d08114200001e50420f41016224 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 524042113 1250 524040863 524040887
    0x6050717070f0201150f0e13110d03030b0d0b010801060501050304050d03110c0d0e0f1f050f0d060f031b060804020d061b080604061a072d03030e010c030b01 69
    0xb4000045420500035400385c0384031020781c3d084180c00780c0c4e0f40d58600d0703c002c90750007017422884022010500120302c2d11411050540e00401403000b0080b520240810300d0354542042d010561a285186843c2d16240001c004c1c540c0034000c100115810200e007582510780ca640a14100501041040041100424001c006200c1d03440e011803140c44c1140c80840e0b900980702650418000c41e4000c02000d60066441c6c004031382c0036141000f0001e085020010002c005c05032002403070414580d400c01c0240b04500404100305000812402c1c106401d00303010464695402c116060407201205106114042c01d00543e190103d9aa844410b403c00200400da4680508028051340c19038444408010340b03a04043c02c440200380000384585079504004101c001d00303590a600a43c9840000302c1c00052103104d206c00d54050010480c50100940c2e1105440c0c5c07100c0b001098501840850901c442c0c05840c0d003401002e000303990100b0503541484c006800c4890340200712080c10b2070220f2941050b6042038001c0741d8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 524043363 1250 524042113 524042117
    0xf19030e060706140718050108011d1b04030b0405070e01052d0d060b10051806070203160b04060e03071401030e010902100f12020f030c0a030b06030a0204030605071707 74
    0x103541d6680f4006000c0c0c4401442800300760b41640030450625880740c03050200080d01c90600004a59403001514107450a000c0c1c40e255411403010760794583d01e00341000390008030440f01402c03804180e19100e04141c0040c3c001710755220403182440113001d01004482d004e0619400c0d08540b030b515190028640000c402d076039255200c039104040b19404030b950019902154040c05620f114040303850b005004107296070700c0da886600d0711034040c0d00d254810015100c2c0d04604200c007501c0c2180e00340401481c0d8203e410101d0b4140304c0c1c10104c1c003030450607540300070003007140c03040e400c0c3c95900700340000c1d00ca0401e0310840c1c0d00039070200901b0004050880d511405400003800d00007840061010194003605240c20069000b0700800d007070035202c40c1d10100ca60008460390340d03242040340381040d028080c3d100c0c1c1d41c1000c2c0360903020300104100a00c418000c040d544101d007000070f940d0032001e01044203070b00300710b6481c08006d6000c03600f00180050303400340300c1c2c3c130410514050001c0400001d02008407071000e420b00b01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 524044613 1250 524043363 524043367
    0x10804030203070b010905042105031308040302040e160b090d060209120a0c080f15060907020a05060c09100f0c03030e0307080c1014011508040317090f19030e06 71
    0x14107000b403003211070882e0020388280d940d43e1a0804a005850241c07800c88614075030500040103280e80103c161030080c0103581380da00c0c0d5121500b01800c440203100058440c00010840040140c0d580d1059110200104001d059804140001806440782c254462200f01004010301c0210741e0310f448000800542c40385006803903101c075001107041e007407803e601184540714550b100000d115020311131800719004002205c103044102000c0e142c88181c1000c0b070034884200e80010441e0340c64001001c1d54041c1aa104840704c491441d00c40314a44182038030011015900002c080341207041c103402d980350314100c0b030a0200e01c0d0028110000c040310305610020781090b43c2e45d8510007a006082c4126405d0980018109854601c403001c281c0d100d51444004229a500c3c0101400e410045070000305d040303c58489048480b81d682100984e184500180218100308807042c00542e4501103401641c02000e0f0382008080041c800340c04c261800306110303840d4000e8946440f42000090b4030a40b1080c00300d6083e1b60107a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 524045863 1250 524044613 524044621
    0x150108150705040b0705010f0f020c07090207050a120e0108010605120a051b0d020d0b0409050304140109050901060c06050106020c100c02190e0a060e04020916020a14010e0c03010213050108 83
    0x2070b0180903980100a1104c1d00142690030b0200540001034003541603a01004482401d0020104030312035804156031a40041c0720401001c001a40604003690040c1c0c15075040c3c2c0141d54580b00c0c40044803c4400c04150341800c1c0a200b540d00c410f0880c0581000d09007280f0301144945060300c40340c0020f180318901c54954000a402d0400c1c070352211241c2d40c024490f652903071100304064010303402039000c0441c514541000000c0382e14040c062602c10a0300200a549000c0c20701c0e03074511429080468550510000d224001015214000018000c00507580c0e080c020041d246050425110181d00c01811540044248603640c0c2e1f0f241842c1413022854244151000501d201140c4012907018443c19980318084000a9240840d02110b1090b505000100601e680326405030103100002c3c0d40c081e4102803408006000040e50f00034040d8014007a004407043c0011075030f58001090b02400300c45d15203035100e40f006d82072041d0800c07407001400c0080300254100140045d0b1004041d145104d41810054244d0200f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 524047113 1250 524045863 524045867
    0x10120305071e121d0402070c0513060b040e041208430206161d12010b12010b0a0603060b1615050c13050409031d2805031501081507 58
    0x25110345540050f00100103540400302405850706082062541d002e880c10341200c07032400740308072041684d0050300b40e0003ca040200b400982e18800001050440c0d031040007188010380300001e07000504442010021500e032510744003203503500c514003440901078004e0910421000c030314415800620b9508005002c5135403880d80321540f114140b00d5000310040701c5403d5050a50103d081441600d14110b00c0070000d1500303004540b04606550000ca10008030341ea411860314004140001c1c2101040020510201000000c4d1180e50101d9000c03500c1e80d915582c103501404c1480340c800c020f0800d420204085071422144050302c0c81020582c0500721103003528030081200040513911800e45070f6004004600e04481e2401c0540c0c0002410b000160301c0820028403031401c0c5c050b003152140d140d03496905070742c52a0140b108035203000c3d610756840102c0c2c4540185851421100700089030300807611819140c5440705060909906482207030304c01c0701d0140103111514000608400b1250049045201a03861000c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 524048363 1250 524047113 524047163
    0x52409040f0e0105091c080109021c0c03061e0b09090c12010602030703030515010e1521011401090b0a081b0f030f0106090513051906030b1012030507 66
    0x40028424a0190a028400415130000717200356020400c5441c000e9440344254194140c00c3e001c070b0700090f20a001404007490607005000d40304135108080c00c88040d00405030048d01d60100e14280000e540d203104201381a0603800650f6400c0403090754400031400d080c3c40c0d040a01c590a503030f900941d4010f0115007540c621000701e882d0140c1107003401ca442e5071208802912a03018020a0f00024184004600c0c210f0070244c000015000585502d00464400310602c030380241e440070000d0306d9400601c015018100c0721351482150b101140704840b01c82d81440107540c8001c00314078945042106e0184280601c810000440d040360700c1034101110203a40310050440505001540080c01c4080412081c0c0b0068514000e140244003002b11010540e8964401311100c800c14031595601c151048046001f40c1c400741e020581001030504568a04c000c8202e0800a480c8550300440b0076200d00c17000c010b00c082000402002a100380da9182e020624a5200104140208100a4070000411032812100030705ea502c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 524049613 1250 524048363 524048381
    0x61d07030b0a120c0b120f0f220c08030a020706030e010b0d1502090a090c0809010507050307050706020904110c0607030510030809010e030105041523010b0901050c070803090a05240904 81
    0x10070380d136860b46986e608200028050b0b03120b1800d0000c031008141d000c40844001441210b0155a050340b006002e041110401642c0c0c3c825a180025000c0106040106100500e40d8a031180c0040c50704918200c2c0c010106c44a9064100c2c10341d1600d03c0c03117501591075860f68201590480740100e01080c00300e00c02002481410102540300014520000390002583c110305101001d58685a01c1503403462802801d17203500311484000110200001601c2c2d42c0034001030413209004d2400103052001d1000450100c689083ea400380a0501180203c506003081001950005481c5810b002c0340c20445200107130948640802051b01401040c8a03000d40d1294a481d851424010024000360501d414410341152600a030015018189402040c400304043c02a540081d100000c01605a180c100300200a8004d001e00300c0c104070341004020030b0f0003c20007640b40035003001d0340078550710310003002040b4282e049640010f00414450f403442d4105e001c60030100607000f41190007507070707910340040c009001006511 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 524050863 1250 524049613 524049629
    0x3020c030d090605010918030e120703050601240f05070609021f0905030f0c010203030f13080a08010806160c1403040906030c0e01140a03120909061d07030b0a120c 72
    0x580b004043c40440e0b0406412036481007002c2003a140090000d0301b03015103e000140105c1d21800c80040d80c4e080c460548000b9150710400ea41e8601e440766200c905101c400e0744034180551200d030405c450303113401810750140d135000390034108c2075410701c0b60024056014000c0d02a140c82ea54400c0c22096480e1011126000303620704031010f01c0101c549002620004c50350050714000d21503000c5003400b80800086425444105030015401c40d9513030080000d10000060880114481315510200081c0d2084c0c068180c3c00600c1d05c0b2004103604102006140c040b0041c40100303001e6100703502e902010781000700080c8890b0805400650400c00101613803461140d98415902c01d40350840c00801d006250148200380c440300c4146405070b0343d88002141c01042c00c0d41a4660003030514200304006800440c9800c440f00403800c010821302e07642e0b442402103070349a50002d01070202c1c0c0551134910484207480c055008a00781010401d00c26032001043d44100e00d40100882d81c41d4045140c2d003402803030000c03100181071003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 524052113 1250 524050863 524050871
    0x260702091504020d050c0d0e0705180c09040e3004030605100f0914150a170c040f020c0c010212030a0209041503050a0510061505070206090a060305090c0108040c0603020c030d 77
    0x1000008450780c0c80701f0703075200d802e43c0307080301c0010101e1002c2018011184002c003070f03850046098412034120f140c090f08103610350004115011160f188e900450468030301d000050301000c0034600b4601062000714400c4012b032181038505c10203103800401641d041c0c0b41c1102002030702d540c0d80c90720380000000310303000310640c0900c80d0030004801c911604040030b6640709001d50760458842451751547c003c0c04000d02503001c824850180071100594264014111003001203520480e1140d000c0780440700351882d90489181c0000303030300750302d01020807002401140a1004001c001c640e1480400340f404060062000d05800180301ea00981d52600030503000c0c0341287c401e00007036650b40b80640e600c2c001c558007115680100d28201e1101c001c5071054804a45034140c01052003004404c003200d02d540524400c0b03a00aa0078480150341c0d49941400300050701c9151030001e401e0400c0451140341440c0b0380e03034180c1003002ca04100800110501440011a4107a041c0913840c1c1d441c4915080c114064416050070722850 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 524053363 1250 524052113 524052121
    0x1a0c0f0609070905010509070c032303010302040b0108090a0201053f0c131520101d0304151e081f03030c0b0c0c0703260702091504020d05 61
    0x10100e0894018035a0204840d86542d4900d00070041d101c0034411550700900c07c1c4005952140500c001c40303142071103032405403c0d5100c0e142807128000c1080044061006000c0300500840c2003921030949116002d082185481c038207442c0480c0d43d00e9411000030304004c03000c14061124041c1c3c0903160280000080c1458000c0441000e480e942204602841c03060422140807d06100e00941280c940c0c00140c1078050f4401d00380502895081c0d40c005c0c910040018420321840030350540481090070030b98030400b40503140c0ca000740d488242c8a58136001160b4003880130a051002d540001120201c808141c10802c0140b4030002c10741e401100d48c141c01c403007030f0340204000c200c5072f52150885104421f4a21440b21001c00d980401b00010102c0c0001000b188500c6840808902102c0c0011350201103031011900d040390f01d8040a00384012540100c994200220b040002060b40d5038140118503041c1410a0402650360009204040082c01001d03507516110403103141526180c04032410a60000018482030034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 524054613 1250 524053363 524053393
    0x90402151303210c0302030307080415020403120215070e121002190215011a1606020c0c1302092b2108072d030f060905040c09020406091a0c 62
    0x8011075000c0304540d00562214070f018000d2240348000343c0c055000b941550b0f907440781034800030000b500c01e59070303d00d161181c400744506500081c03000c0c61190a250b04c030400c40e0380000e0720b40324481d00b2441c2440802c00402c01d03903541c031a454087c0c00504071180c0c85851081c0070b81d9803c19803400980c1e010740c0d00005446441040700c140011203540d242d0300f26103010200c1080d4034404c860a00601203d803140460b501d02e50026400030b4a41009100f200107a40e14003a5107c0049a1207510f0044e19038014003000007480c50040f50490b5100c0c4004004e62420790a0400200003000c2815179000b52008064202c00c0020704004030360003d540808400e0410445041c00200181d0760400080020481c10001e0303005807040d81f45600760300144a1a1070400d08511704481030000e00303e03030001050390f2034040100c400c1050040000500d910f80340062641024107129003aa240c40d004501e84900400040050550210070a82180c11060050901040001c513202e0b840c4600540f40000b4401c59004188880c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 524055863 1250 524054613 524054633
    0x50f2103070c05120a02030d121401080106060207091a06070c0b0d06050405160c021c060f060608070504140609060403020607060b040507020d270b04151b02090402151303 75
    0x38104071084000001c04407404c80d0f956041820094160700400e040d614024000e40c40808a001440300128031410488142203040b42e00741c0c0039501d140c0d1110410841c250701442098081c0c81101400d103c0d40c17603440702890184660800207802104000307594001c1c000758441000142003a02e0a90303a4605140001c1c4028012500500384a0741ca00008582d201c0106d280d030103c4000705840f0700030031b1a01074080010100300030600350300040401101400151032840b03100f1032030a10200000c0da0f1420202c00031b2121030000d0450090100c00c0000b03000841800415501c00482150903d5a41465501242042c000c9620013500701d640490880c0410a1a0700100c803a44015501080702d90303100d2408a0303450400092103030120f460780c2c0f6a1b1030742ca8007085c00d90014180182803804081e648030f180001c6940503900c28980c1c4080d03104c3c3c90152580c00004580c2d040c43c00d9600070f0300764405400081d2003100150001744207034400c90581c40c05072300c498180d40300c6480d90404200025583c0c04c0c036047ca1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 524057113 1250 524055863 524055869
    0x31b0501090308070c0209040210050405040e030408070602070b120903040b19080c090a0e0a09050601150801091401090506030a0206160c080109110910090c0504170106050f2103070c 80
    0x490783d15400582c00340e10841c17200100c0e83e0020901e401984558007030003848003014425800b0010100808181600c5a01501c01d00319a200c0c02190f5407890824102e0401c05990403240c2190014075040200d5803c0d0340c1a2003a031800340c02d000045071100f522031441c500c11a4000b508840010031542c4a1000d80310b0880d070070032078a4403940015902c000c00ea403024401c04540c0d40e402940ca0505202c18008644600d40c042100320001460f0b130803580f2070515042d400d80c402d000240c0c0d400c10000c0500c3e402082940140026101413000406081a580c40c42105001d8103852039507070400504240d9080022680c13543d00075040030354400b0410656101602541002d60f071003510b100c1e000038070080500c64449a237400400845201500d4010040018000741c03400240c025001804645030104c0d214010289540da121681e0300c03441c2c4511034a150140350301c1c18609900d409070400068071a5134541000b0b0b04120340000c5601c088140040b21039094181500c064800070a402040005411402040d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 524058363 1250 524057113 524057117
    0x270a09050c19090216020418170c0307020d02270a150f1202120f060a0e010b01080622150503120a0909380103051006050304020d031b05010903 63
    0x10300c82100900c140c0c0d24078010b001c004600840c00400480281c0c0c0d001d0440c0580f0641000c208641907000203081e00d07005d03070394000a95111170f0f0308010000c01c9030042001c86440762101c2d0030802010222521b90082c0440a4020200121108210754400d5200d20900c002005001d280074065400c44001200c100c40c142d60503413900c00f031040450b40c0c481301001242c02480804004600b03206242809a104144c201d070020494132001c580203400b444808110b51803074008208134900403464a080d520681400b900e60313450003c00c0b50060f6400300043e0392003041958683c80c1e04145071402006d01c02004200c1c906a0320700800360481c00d0b46001da0100702c80c0210111020346075982e640301e03800e100f41001e6801003809010100000100c1c0e4114900c46802c00300a486d10542c1c0400400400c0c5004600031140066900280200d60f0144182900806040030f07500d1441e003040c00103080c0c0c0c803000d0310180c8201e90302c005540425100313002040c0844a0ba54030b01d40a07071003501c0c1c00d5002c0c150044007280 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 524059613 1250 524058363 524058373
    0x703020919032a140102010e10140601170a0509030d021b06011a03010e07020a02060a0206040c0f1217070501230c0f030a0f0b0a060513050d11270a0905 67
    0x14149400c81d5580003c81d181c090340d1000b4603040c6103400d50400d80384094195500c40104403000e62080c826002c0021180f0008a078004041e80c014208410080020381848180e804406c550500300d0405079110b02000c2000805031103c041e01807840c017820250100c40b9000041d045925a2441040f81400032488100c030942e1f626407e030054222142140542c0c00b000900041102d446140502c5420900500645903560117030713000304510341d11950044000da80104103001c10080780101c0d1070000e000c0c45441e80545401d01101810003d010350700604090b4412180d05001c1c4803040c1140d07800359000000708a000780020034200c94054035503103150440d0360100010329815101c4120750100c1c101c01c4020f03203107a940001003c02413080444c40d5099540d14070161895403640301d42907014000a03140c45031100b4140d40010310f520019040a4024150b021051001441da10740b01d07a085581115440038011444000315010844030540200340c10b40754040c0100e4031500d6001010303860060342611 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 524060863 1250 524059613 524059643
    0x212160905070e0d030c0501090b0708071809020d0b040507030c0216051809010e010c110f010e0307020904080d05070e1003140406050c0c1014070804030c0803070302091903 76
    0x1104581c0c04a03000d0012039a010508041c9203425420b036200326200e400e10001e8495251601030031111000d01c11a69103900606100d1256017040f2110f40c4648a80b80c20014a81d11400d007070500410b0303125420905070040b0b8403ca0250350f40d040b41c01002009403040013140b8207080010040c101000d14030016006d0180351b11464640b452032002600c0c00078111007800035100a01103074280c2d000b4103000141d541c688403010f8081c02170242045000c000e0b5110300c80518140850b909083d020544466260316007a5140b030800d102006079000c05804a400041c2c0740d840f070038005050b10a400b4421083ca05d45410011400c2d04110b541804039010303220401c400e00d05600580440d5041c49642c41d410706e4100001e00061345035048140d21140c184003050600483c1c00f43d0902d8070403002549a00070b600e5010328000140100140c90340403140740b810030003a08141d213001d40720000c949400340140701c00100140c80240603804483c00f40300d018080305041c9150040c1d40005060501040ba07498913140c1c180 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 524062113 1250 524060863 524060879
    0xe01060b0c0c01200d260405150a150509100503030406021006050a05090412050c0d0e040e2a0a0e010e0901140106050f1e0301180c02030310150c021216 67
    0x445009440c1d08005c00000c42d45841c142c428180c80c2544480c003021141d0a0388400c04041d1318203004900c00c20040c11800f0580c01420701a00004100c0602189401c01030082c2581514524007181c2003a02e1f124051f13102ca444024905242d0b40140d600b52000160000d041580000c10803014403030540101305903078a910402002c04158418103502081d180003040100e10803851010f082d02040c1801494000b0700f194260401c40c8461038a008142480590210750420380146400303000c140001e1305500140f54211034405054a031640d81d04401e02100d008103803200400400078040780c90f12811a5a91a020203007100d600721038003010f5500300020300c51000395444203541a44c5554540301d050525044002255802c5a807500c00c3c140c5810410302d14880304c0c1c6c8011030181c100c0301070f00400324880031264011744000c08510740846d1301c100100000c0e032140c0390b03900f0140c6121042c801d0b40e00790303a1001150210503503407020b5403103490752500829482e80007407a00a0756220030b07068003640d0790b00c0a030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 524063363 1250 524062113 524062157
    0x2003031b1b010c02100e09012303190b0c0c03031003140606030c010509040b0d030c02011107030201051603110106090f060e130602090d050604030309140c0d060e01060b0c0c01 77
    0x2459000c10310781e045400041c17420a0210190052914188608448500c001190036000303a1090490400b0f40d0f800c0c07029034503101420701c9030103420b034000c2004c0c00c01c2050322a080900d0310b030050f02d01c4c0c40c804041101d0a10760801c40340703801c11b00b40c100c13a240c1c108100000741c101042c0c030088480d041c1003424101d80c42e10203c0c1151180c3d030024090448a2604001504c0c268000c014070342c3c3c41907135000341422a42e204d0700b09804980c088d40c0d56a41028a510000d0301c82019444000f18591000c0c0d0104010b0b03a010007269100c0500c10b0000060302c0c82480d05a4078844030b6042c10800b035003840804200203040d5402110741e04218002400b0550340d07812101c0600c00144d6109000100b2021440040340701038000700181d010203404144000c2d42d0743c551a0030440141c804800281d110110a07050280c44078540c00c1130300e00e03030001c3c00c211000e100001e40d058603164002080e0680710130b04481c81c0d20742944108000c05132040c200341c4c0d50101241c0c02e6143c080034140c05011901301c48108081000f02c0d0f82d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 524064613 1250 524063363 524063413
    0x60f010215010905070c020d080a091d04080a030e0f0c0a0f060206060415030804270c0f080604110f1207080121110d060e21072003031b 60
    0x41c00000360b42400903000203810001e000c4420700c0140240140180c40b8801e8101840f40200c00c003646503d90020010422821988211a0030801e0001e002d5a051030115075500158840d040540e612100e01045e0040c007030050b84d0001c0750081c1c03801151202c4010540f000a84022a0446403151310f40a2242002c4210b0192400580c04000052030b182801d81c816601030303014200300f00d003281d504d640f0b180855000b9000034100e9004980c146c80039502c41c0f8041c080c58525914280002a0b101c1c500400720300340e01103440c040104280204580d9101e80c0e00105030600a4a04503658980c5e16000c4405030b0300c01d240c08800395000c0320005030a00d1207034040e01d0690b49900d85100101d4001150250710381d200c600700340e62010900714011415515415444209441040302240b448a07000540703040154115042210b8081c40380c0c952a896843c90880e44025448803200039025242d92240c41c032a8072080ac0d8682510002840c0c08007204049100c840e501d040c402292049000300454000044041c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 524065863 1250 524064613 524064643
    0x609100f030206160c0803040f0807031a0a06080601090c110118080a09090f0b09060a05011b031e0302032406030c16051f0c030603051002161505060f0102 68
    0x100240010b10701040103015650516510b006065181d8403100d000041c654006c2c8803da10000301004182015010301c401820800e000c0c0c52081d1031900c401042c881400410408034012a0000d039440c581e60344100013a0645108982c2c540d030312090100002c125000580740070070324056008101c070f841405806051105482031801508003035a0b09070b4a0b03006000443d0520425441c00f01e13100c012031041a07001c41c1c2d000d10101e0343c003000100340803078124043d0645002c0c0d183d600303080c4910303600914001d1403504001d80c00b13204049581000c485104c0b05c00341d0302040c02540007083c1841035058010b180101740e0564200c507140d80c1c4000d00c4041c070589411050b040a4180001100c44880e40003426465031580c1c80554000040d550380c0341003049030810484c0c800c800c841b4555038452144210000c1548504041264600350b44030950398110742100c456803250001098180780204521840354180e000e4403400d5041f440151010240c04c08681e01c90080c2c41003500e2003a903601c00585207605a0200f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 524067113 1250 524065863 524065889
    0x6050a0306080f0d1b120207090507022b020705060313050105070507030c0f03111f1109030c09060105070b0a0506011409090609060f031209090703020403050312060a030f0308060910 80
    0x41c440c241c84946220030174203800c1e8890034030180442d805005070580d994040d0b0180c04103078200803281c001c40d00c010303000c5800c5500ca03108016690541c10b82954202052450108102e0b19540003249000722540009800000200a002207c00301031684e03010203114000a01140d074860804440901aa0301e001d8005110360405034041449003400d0101d0130f00902c9c102c03c050040c044000c0c9485210b40c00c00c00304141c50100d2010040b83c41c4a004042c1003504181850190041300103551103524a0080348217001c00004251aa809481210066a80200038400e40d01d031901e2802c0003008204d0348103000c03070b01062030aa040d102c14802c982c121071006100e48500e03221001031120100c0c004181d560000c04d002c0801100340d40420410480f440c002c007100340d43c0c91404041c0060854094009020b0500501c0244005080401039800c82101e02d41211041d98611002652401ca02c0d40050010213003a5440814964000e088030300c1060141c80b00c035025150441008082c0c101c0d40715500034a005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 524068363 1250 524067113 524067133
    0xc050307090e0402040227030f0708101a150403050d0206060d0f060e0f01020403020a2103300212061206070e0d0203030309061e0c0904090501090c06050a0306080f 72
    0x82e80c00c40c0c01600140005003405500701a0702490300f0051581958000c0010a4440030b203401c00007201c08035800c90140000c10310b46240780d641e4001d080c1d05010380c0d07621100114420240004000a00040140900d800003a0a0501c072016130080c0070079581da000728441c059078030b8000215039000d124040d02c03110511070291a48100d604c58043c2c2122240c2e121204403041c030710100000d1a020401c41c00042e40c9902c2c40c410000b00d242c40750701542603401018454150005040c00c0c0c03041154150614580e00c803403e0145a0030703c42c41c030030b0015490036032400120510026070f01600f14240c9038049811541c130f808040000b001c100d00c0c00b900c01750b0b020900203840a40710b40084e0415030710240070010450f01540c0064150380049550130007030351281040010140c0d040d41984c07203d06050b03400d0403140c140031180c04203603c50007805601554031480600e0070002e096005441507a005055100c3d0180c40b204c0c01802648440c03503490000b8240500400c2001d03001c03d0490b01040c10000814403002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 524069613 1250 524068363 524068379
    0x216080a080f12010303120e010506090c1608070309030b0612120a14030408030603060f04120f0c05010203090624013609020c06130b13020307091d010c05030709 71
    0x1014070720054080c00140002c0003e00040c409560103036109458100b401e03400080342c84211191300424401b80c1e030400703040c456140ca0352080181c001c0d265501e042d03a42c000556a1a03030b42400840020120500005c410091591043d4403806403442410302002c1078886108000c43c00169020791205904442246114036a20400070031903400c0c42e0030309c0040382401900040494004640940b0100b10000402205207010700c951030340610807107c04189814551031b0750b000d4001200d001d000380300c8106030110b0003c0c0501d02c0d40d0400c030b601070002d41d500c1c50041c11281d00d800d07064a084905e5010482c000001420300001e01509160603503515804910691580451410150584400200c840340400c81041358880c1f08003d0661010b000d03030341e440128400c504e840c400804c40d02d69a6080310050b00000e0b00190304503003202c010b07100c1c48000300c2c1c0d5000203420003016a2003015007900c4c0040306500495030321040544a00780d20004c2041010b001829600b5110403120400040c2c14074405000b003034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 524070863 1250 524069613 524069617
    0x1120f150509100515013f05220b0402030c061603030b030f0d03150f0608041104060b04031113020d271e1b0b180f09150d061104060216080a08 63
    0x250804001f1070b84541c98100a0b14840c0c41e805500100c1490740030242002e0f20f02075250091180d00075100e103840352a40090960100c3da10043c883c205d49400314055650401840c07410407001040e150369001d0b00100c444120500b080c2c00c42c0840c0c280100740e505d903c1c010801c3d40f004040304014042d03014120f0811001443c1d1607040d5601c955082401050410b190114800a002d40c1e44403100b403410a4100003040840d5035214610850400c4401d0001c0d54000081da0100c80c4d00400f01990b5a201c80300041854100c0784500401d41e10114a0044055482e0050220014112204078000c141c83c482600c50b00500e9901406a1110031aa0044007005070221141035000d104007403004d50344100c440210014651110100c210f02003503c01050240e8030406907100e0342291041c0032102000c002c1303030b01010000c0084a1403a02e0b8840d841080d294400e00341c0001d80d1200d0700300040c1d80c803061a84a660410300071080103110f44105400c20640b041a0041038820040003403050022560340d01c00c0503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 524072113 1250 524070863 524070887
    0x10c0f0e1c060c1704030c020d02011209050d0f030e1e150103030906030c0509090703021c06080d08060a08120901030609050a06060e06040e01120f15050910051501 72
    0x510201d040600031016460910000d00c10200803038959052a0300506915142d07500703400c0041c40c0f04c20f01000130b40101c0d4503c01151b058881035450031701030005072020501c002a2070045400d000d050010001d002c07514500025090f154540c100d000c50404608030744208007034490300e9002104050705032114280d6920820300344811500c520f81c4941040d8aa50000e80c011408506440402c2c00041d815004040806050389803803070800109400044040e440a4111402e05500059002501c080f45114414848400209000d4a640c07030365030980d070302d1905003000300080b99140400c03400d2821054801c1224017000091400c180004280b07945a07104411503418960b4425001a002c001c40c051503204215a00000600a01d0140050107a0340e11000c0c5511503c001c100c24071560114003007403030640c2c043d00d14070101101e8504c1c2c4444448000c2401800305c3c0c1c138540b90040000340d00d420883c450960036040e2408002c0043c88842524020750300c0005c1014546031111213544070708901212 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 524073363 1250 524072113 524072119
    0x21c050c0903030a020705010206160804200a030309030b07030b15031f0303020616111005060301020d09080a180e0c0d20090a14010507031107031704080f010c0f0e 72
    0x2800400703400192071640481904005a007228100700300c15038041c0503c070b502030941d04041c007241d00c0b0100005c21004000388010072903c05404041051010600e0b40c00010714040e0840203070740e84078100a0a021183d00c001c82d401415080080e42d4180b1038050101c1091003d0100326221005c1e182004403a00014040041c8407160281c21048590104034080194084e030080e04040c24038000205000ca0001e02001c00d029a0045401000f080062200c100340c00c003503c00a23868440d0000640681b007100446a0200d090082c0320090003c8440100719441403521038080340d10711101c0481c50303008248203810341d400480b0001441d11100d44000d02844420140001d0703103001584c040d40e200c5d03035031207140851030b07101044a0466040041e41031000c0c1003080400000190308800003011032103043c4c002410040c1450456481e00d03130412003038010715400703000b950401c2d02104004540390880c0c455003019100381001d94101d04018030908000c03082c0740c3c0d5032049400c1c6242054452400f14240e05030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 524074613 1250 524073363 524073367
    0x111b030706110d360305040e0a020903100b060f0d140a0b041a151308010203072c13051810050601030501050307060c0627140709021c050c 61
    0xd50307510940e406140c820242035241d1800154050448000329851805076200c881c01d9401000c105001421049550070084402060391404a910b80107035400307192500300707403014000100d220750081c00440c80300741e00320340c00319180c004011700755108800c1c02c0307030410410401c0e030701410003180c000d00c000340311042e0100700b8081288a4854020044600c02c1d0450758910366442c00d0325081c0586c0a0b1607000c0002e0320003410b403120000e0060306901c046200b84500000b03030700e40542200400c00d0010a0610000c40d1240360002e80a0240d0f0868034052410361082d0b002491000d05103d0445800d403c043d1800340096030b40d14001c0005d00016080541040880400305e2003100100301e400e2811042601c0462203040c290000340940303c040c0c0016100380c01500c800c0c003025500840800c1e14540203800421864003600c149460781580200451400c10710b20002400e01107013005565032401120111481550740d940058120b001c4c0f00c4400028200705d642c00500f01c0119002140c1000d6004407040c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 524075863 1250 524074613 524074627
    0x270604060c03230a2304050a0b0c15070206040c0b030408180406090c03060302040b04050c0a03020a1b051c0212091504080723040902010c0201051806040801140a111b03 74
    0x8a064201080d40000211301708100c016000e0107040c0e1525101a014900b420035080c08000361400c41c150203552601080400e130014039210030054504102d5802c14400e00e2810541ea00a49481007280e00780d4114900c05000148894504101c0340718a400445e618100112a0010000c50610780760081d845921582d02080e140c01920903000c0403c0980c0300010580d2031441404161444031850610852400e420031070074500300c0701110b42e010100d207401070342d0342400d89080d41e1907140503004a41c016035003d03120302000390005484060030710130205210758219902c2e0407a91005d06103512103500d6014400402c0341d04140506903800c42c0e03042c040302c1c1481d403200c2c1d1003840c00a1a130b0002820748410802d4444911044d00f0503884000195000d00032442d20b500060325a510124000741005000680034070a5880392440500048009100c160355968600420f4040c1401c250613642e02c00054020541080c054800e105840100c9071741c080c284030b40032500d41683d20041c001203010340000c1201d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 524077113 1250 524075863 524075927
    0x4060c021c11010506030d050a0804060609020a090305010e01050106231c1e0c02070611030702040c0e03190b0c0a050f130f090c08220503270604060c03 67
    0x90070100800760754095107000068055420340c3e101424141c000c0e00071142c0504c1d400e5100c1b048074200060340c24481d45c01d440e186003003002010183c0c041c00d40c941c40070400c00c0141d940402d030340080720300400c0280009034403d07002908846081c403070540400c5480d100c054440e12112100491a0f9800d043d4904000001044a940c417504028001d6031554540f080c81d41c0401c00ca04e0350206601420b42003043d40026640a991000223008610034088455107203480010200101c44100d42e001c3e000784070940100308050300102ca0150441c1c464000c04400c509400c080003802901a42c0080310a41c054980210a8031503602503680102001000c104070040304c9840f100a00201a420204400c01441c00c51002282a40f6070002c50b820b41c00c00341e010004070b034818205500040d245403801c2c42408240c13120650200c00e027000034410301000c603021042042d08002000b00301190b040b8a0064001a001c00c070091042c0d0240601040e425501840824807542e0000000c000c10f444d0700c030b20b420a070540 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 524078363 1250 524077113 524077153
    0x708061e01110610031712060f120f06011811040b03060604080609070f0e010e041202012c010b0d02031203090a0218070905060a021005091504080c06010b0a0804060c02 74
    0x100007040141c041c20410809500e07501032083c1800d40003142402c0c214007c1706985030010340303c0352060540310740342869555614044001145540c00b2a005051405c2482d903e4003c248241c0a8602c3c403400e20b001c41d00b00038022100c08012084001d4038041c1007078a0101603820145c00c15070030039001d00c40402d4001d0200000707802256100c000342000e03441c00c00080c41d503214a07044a8000d040315001041040c007443d5841d50015400b0440c42d0320802225800ca004005000f04030810700c2201076200c0c0e0011000d0180c0d0084401c6800902000b2074090503c51003407250b20000390183d103d40c840f22a00703034083d4090b50700560440d040d2006150a9000242e01c400d0500003c40080d915005110500e074019102d0030003071070195056400e100d0700c80406910b4210203284c3c010842d07200d0340011304581003407143c0341310720f000f02941c40d405040c94108040185c0081d40045000c0c1321700030011800840d1b04098489248690f42c1740380440c1e0316607403444050030010076402c085d40305405404041c0b80f04101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 524079613 1250 524078363 524078371
    0x60f091f0216120c1b030b06010807031407030c260c180a15020c0d1e0c050301020c031c1505060a0507140d140906030403050a090b040905040b0708061e011106 70
    0x180301d04c900340c503070b013132140d1701c4d0070300180303150040d069420704200054611405950100d400d0808a12039525648150b000d410820151019101d1400c10800713400e4050b40030808400542d900d04802c000320b440d02c041c4580009000c8099007110b0320005034400f102000811454589a058000079240040804d8062071303d6001080301c00d100010380540c42d0340c101304c54200203000310ac104036004529121501141000d03035500d484510200d8007001400b02101c071060050101600071561060140183ca449400001309071a910003604c00d8036200c800c4030701580707019002007000101c85624000810006a00c406212800d1110600070080402d43c0c130050020400c9090b00a0140103020500082c540c13180d142c1c0402d0500001e20088000344c03141400d0f01c1e409030f410f00740195113403d0740c50306071849100c5a0100390724260024011a1600440d0800703030280e480f80040e40440e4a0380442070750404400ca034225000700c0070a0030000005088010840126410304011262080341d203141418804115 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 524080863 1250 524079613 524079617
    0x7030c0201080c0a0c0605090a0b19061d01140d061a0306102102010c05060a020711011409090a0b040603140c010f0903060c1808060f091f021612 64
    0xa2880400d550300720302c659501520f9000103524000494202a0041c0810107002c0d10340c5a5803400649611020466075010780d40241102d005407030003034281110f180ca03140c0781c15100360406000042c4609004005098110f501d865640b02d6801c1812a0f0003804502206680c01540001e0b520040f41a600c40e0040020b80c00d080c42451040800a16160440142004014030264001000240085050300903400706c2401348800c80742c01400100e629109400c00541070340141414049007405540c000c11155100700c1e0b440700502c1055006460840001c040805900010000e441c86850702165595114141c030030005081d00e030740b401140c00c40d0101e800071a070f020901c0140083c2c200b4200400d41c062002464240204801520010300d118818400246440e450315101d03140d141c0102e08400c81c00d1592952040415621101640e6031242030f0b038022840203003038021801280010031407242c4490b10003100c244500c0c500388808025845492000e4409884060f41800030b0850b8440c05050310040e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 524082113 1250 524080863 524080877
    0x7051804031211092812020402040801020c0303070e01081509090106170c0a29180405040c05040515032107020a06020601051503042003030d0606032c070510140703 72
    0x8001170201c0c130310b0308003d400e40b481d0754156618003191801711041e054507001c0303032001c030114054800304d0b0180c007c90b00605460f5002003008621400000701541c840c80d929138406052811000c015070384140e0613601102402d1006c120940c403410040b85c441c3c2c00c250140c6c00000d016a58014030400c8030801d6a081d0181c0d0403012240303003645400c40c04c14010b4000c0c00c0d41c13605500c1d440e44800340310100c001290100743d0004158043c2406c0009030044c1c025202901c180014901450045c1d000d0b0703090b0203100d2040e071400d80400c00000c41c1020811138030b42c02800400c0d20400041101d001e452203040800340d9000e00704001710060b00e503084c1040003840c2c550020802c0e54148002c1003402000c48001000c205414000c0101040b8a03146204100311038580760b007019045c00e00424107511880d4195070102d8208200001c00507450340c4500c0307489840000825041283c800c415039003555500d0007440310b0b402400240564070b000ca00b602581300640c242104100724038503512020340c100070002e4010801d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 524083363 1250 524082113 524082127
    0xa0501060e0105120c06032e0b030a0617060402011808070b0309010c08040f080d181a150f1c0f050d020c061c05040809040603050601080f07051804031211 68
    0x4564101901000c402500b00c240e42e100105015000c01005405204400313503101021840388c1c510a02e82ca000328041000180e03c41c400103140f40c1c001c6c4d503c002c0440c035144000035124412044051a2890312000e42000c1c1c850f83c004640345441401c04c2c2d074036909507000005a0070010002c410050504a18107a100d140145516003100d40207039138101400950010800003840030b88142e01c030154032249541e201c52040742e600005117003c02105c5105d1410712076a100b4044801d800c0440e05c5102c030101c0a26580c1c200003291a40340101c5a01d4210505401041d0b5915240e2440c08513401c1400f911615169035844100d50000340303180556854004008005800d0340c1131182006000081c1d5002d8030300300d030708401c003203140c003070b94880c00001541c80c0d003c182000030000890303040c003000410a00c00e41e5141e04000384c0390b240a2081e02100d102d030351000c003c442c1c0c0200714041140d8004264100311411592800e18110f0001c0c0100c4c200b0110035400c0b040c10401d885049052082c0380c0700e00b625030013 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 524084613 1250 524083363 524083369
    0x3090d060506100e010f05030403020c04060305030d11130302150702060f0705060108030702090a05060a0f1401021608031204150c0806011815140915030f0a110f0c0a0501060e0105 79
    0xa542e5420050010303104c1c2913998211020340030489891619607625902c5050882c01c0c40d100244141d44603007062400000d002d40040688140e5201000c00c120706048812104410700c00e180b00c0c400e02d14007604e0200054648403041031030103410320120f5490a002540016580c2e80404001e0007901004201803003406001c1104c0c0f030140c0345880045203090f03015000900c25071001030014080036101c1000071801c0c0c5941044000814000507418292501c8039007200d0000c03c1d00880c2d900521642000d941d510b500348144808650301c0d070f4040d51400e103542035402119000103000761504003000707400403641e1107144612410350180c0da44000042c1043c000062120080c48002101c010700e001060010b40000100050003e0b40d81c20005802040d56603070905a006080d0310785c0d400028800100d0140340400011881111255124080b644d50141c00000b100c4a03410b050003200e00070722803402804041e10040040c001d411084800600300c507a81c43d420b60b81c1c25000000b9003581c180c01086141 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 524085863 1250 524084613 524084629
    0x40303200102041409060d1401020d0f060f090902010918050118050907091d061e0c0c060103030e0a0816061e17061207080a150b03030901030e03090d060506 69
    0x300c0340000030b518240c80e1000e00800c4810602c0c11a12a010301004560141d8403000c0c0603003150b078020442004803481900383d0b4002c1d0010a41140c240342001242c2c5403100140c0704d0242a901e2200402c55010f003001609401030048000807418072007401000300e82c5251441072070341c2c80c1c400c010001c51158108542030f0440369034080401841820710090154a460100300c0c0c005440a9940010701da241d08800849c19400e103561190950040340140541c070050f00d0f1119110b034041c18800006030f01e428518080c0d40c0329260300002650810001480001d2103585501e0807000c0040c60004e440e51a0310319035081622801c42e001812910700c0b020410184c100d801400354404c8030400c003070786880c3c804010344030a50303001a140c804205100000c0403562800780c0120341c050b90b2003c03138001c80e440349121a500d00900d0803e840c8100044180d00c440c45807406803100410300500514241101c0c140150040c0509885808203400107020170341c44c64407003281480c80e46000b08070108160409805210f404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 524087113 1250 524085863 524085917
    0x1103040f12091d19090b1503070b0a030b13020406080412030614060d230708090601150503060102010b0301020a020c0114041212030603020414010302011e020c01030e070b040303 78
    0x8012048000c02106809852540d149002c036030103100c2c20f507030304d201d0030841c1d901240100c0b0f28145072200003c01d200c00c0c41400c6201e040741c45a03c1c81030600f040c0070159a507550b8411340780395100421200061031320a40021651a202818050000e00c0b45051702007683c02c1a004000040c010700104410301030b0750810780a90319440e0031f04001450420300b2074020f0900c03401d100c40c060000000d40c400c080b0490b038450000d01005c0c1c8403007001e59511a0141e100440c00340c4901d130009540ca8007194003040041a20740c1201e0807104598200340c000001551640c100415190655507540d0000c0701d261002e000504442e40f0b554054461821041c0c0050489946e1180140340307800d0038401444059940c140058550b600b11120700300e0320006550407000303801103400081d0014101800440c0010340701e06070b0380c140c9100341c0301c081040710b056908030312020404c6480e00041c2c0c4038880d92501c0354000c2d40200b0400411a060b980f00caa01d0b80407904c0c0f1640145d0084001541001000344980c030b03200d56001c54 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 524088363 1250 524087113 524087117
    0x804030e040c09060e240a0906030513030c0515090d09060c11011b060c2c0d02060a021e0f070602033f070c0201080604090503070b09011103040f12 65
    0x10384901c2d9100201400481d006401c20b20600c00e03402e40e80c5503030b41032210704489010700b0030394040034980200001ea0b030045003040012070a1000e0100b1381d03a00901031140315420490f4200f80300074403030314102c1e007039811f004081d2161301483c02120802440541c4040c840c40300240103000c0859200d0006040342d031143e00c104104003035540324100184040c490020a20000d01c1c00c044511240c4028282c0281c07040c900400ca5407411030071240843e0010f10007052807038008501c0105440782910418000488281d066100c000802004018905107024124490b4644110707840d07000d5141c2c0b104040c011408030490b2503880200b0103010800c0400c8000b001d414544055070615111790316510b407101c03503075201203080b10f8070012004034107036550810341c180b12960901e03480d6402e207040080d00745041440180e0000b41c4500000e0500e003800d01481500a40c0302c00113601e0000551521a030245011300700200a54861842081082c42d81c406580100d0107000048040b0101c1d00c2c0100702c03201c0407019042 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 524089613 1250 524088363 524088371
    0x306060f1106011e05031605030706320906130e0108030a051b0c180421090303080c1b150901200a020c1903020301060f0b0f0a1b030804030e04 63
    0x10041d4049070180c112420060728007103030705002401c6911042150882074261140200300120300c44000d0b0507104458041e000d40c1c4982d911004125480c045600105d2041901d0f007d1001c9401c0c02c0d0700841a03030f100003107603107410040c000d400203509510220380d85c5103052000e881400503050102c2e055006200325030095240080540c3c010340540542100009640c61100080c100443c007031002c0103660800800d07030703001449103c2c5009007200058030183ea480140804030841c0004d0034a2108180340c094903802e0301d552859130119017001c401044032405031401c0c0904e03001a2421000d004800700188050201c04440708440c1914241c01040005168140501c2183c40e41380c2240c150b0349110360003c555a60100e0720401da150401445070b03582c028250020190729604509190008d0b40d00c00c038001d102e030030355031056040c1c0e10425020301c42030141c08110310f80140707001e0781c020401d002d09810050340e43c503c1ca0344050414040350300190049034030301040004056000c0d11000d0350f014200ca00700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 524090863 1250 524089613 524089637
    0x30414030f2e0212010806160806040b010c0b040f0b1509010e09010e1209030d03020f0d1d06090312130317100f03080703020706090b0904050c0702040c0306060f 71
    0x556840c0b0001c400700c008030011040900a480d00301c0700c0c2103000304200c410756548265611a220700c8000340700c1c1c01114003443e00030814040841b11502c55241c0380303541e803100d01d4580d4010440109401c200c900d0610150824040028802d210141d2043d40200c48000ca07000407401c2c0f030b0480800060072811241c00704100315100c2c1d0b440440050541b1411940c0c8140d90361644030b00d0303005182c0808561824402c1c0e0342440c0d90f02c1010002082c469500b5030a5841c0c401c0c206409500303034010180c07030a03c0d040090041b6881c10005900a110412085e0350b050b4000c030807100000d04215096aa9069a4100182c03540c44581c0d90042d01d0340008004c00340003200089508c000b052644078092000c41f000004003c5182480f017440d100016081481d020581d807907580c5025082e039070004400b1001b40c0503c5a0001d4a43d01845800080703c0070b003050b680c90a1003600c01c000c010280100414454402448150b02584031446958615000768800043d002d003450409071410030650091000c102941ea008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 524092113 1250 524090863 524090893
    0x19060902210303070806041d0106061211030a050a020f030408090405060f030d0807090f0602100c1106070f03090b07030209090105041e0e011808040303030b010311090609030703021203041403 84
    0x3c80c0d110800b1726142606454100001d001342207074030319a10030884072411540c802d42040d4480c400310f4500d5280c80781d01013007040c0124181d403411184002044020300001e13800c040950403265005801c0b030360061806042e08840d8141d80c05c161000e030340200c004030740f9101d581005c2c8151500548111800715040100000080e522103080c0003140c100400c00c0b0125641034080d21020000e0524042c47c00d58084d103890000356034031000d0b0503101c0c081c1d0038881a10081c5004400031802c2e00609406031600d95150081507540c050494100801c140d502c82143c0042036030002940d02503030b00381d500560b4402c01d1408201c154801038101602c03a0f440d12074600c00342c6d190b9150917140141c4a04001c86c02d00c007203614490050074a40d07061040d200540402e0001c21102c0b00060050720300c292030403c08000700c034004400700c4000d0000f11018580c100502d002500c0c00d00090407107140c00404607103219860b030340800c0010000c400c1c142c180d940702103401c0c400c411204811208154054008140000c8081c0d21 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 524093363 1250 524092113 524092117
    0xd05010b0702090a0c0c0210020f190203121b01050f0403020c0909030d1104030803010902031008011107241b0e04230403020f0d0c030e031c11190609022103 69
    0x1c002e07004e07a0312004c410711075018000396559a6001410600d00c0c1d405a04069111704c003103550710001d40200314117507c00c1d00d8000c000c0c103035142e0042c000300020001c44400d10a07a512120380450b00e030301450085500c1c0902406843c1c410741001504030068240b078a406460030f40046501c0384510314030010003a07201d6000003500c0c0b1442d0b01040129840d000341c841c403212031246410151980c0700c000008107101d401900294019503e11081211803a607944030705089403a41c4000d4410b0f100e040148070003242100c4204c1621400d111071b0b4156029090711403400300c6200100203204004a148094003260b04078004041d4440196801d000e072040f84603641d00d00444440c070b245512949240402c05040c42081500c08100c000000c80310306281d50354000d01aa00c84010860000c0d01c608690341050401140100414180c1821001b02e42c020342400e07102d906021038140c00a00c540c0071200100d000d080c0111000740c0c041c0758002500ca07143e0052164400e14950030b0320070f522a01c40c1c0f0440c2240000b003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 524094613 1250 524093363 524093371
    0x201031d160e06030604030f05030c1e070b061005040b0306060415020f010e032a2521030806040c11031c06090e0318030a0606090b03100b31050403050d05010b070209 73
    0x50100e40c6c82c0d4030b03090740600e280146182200d10048802c4a0b1041c586280010318129003b480d1810850362440e042000400c5401807aa0000e40c0c00c0c041080300310042070180da001003000b080c6a0500d0744400c03a5900441610303030658016403118011480c40074081c8107140c0301103000000346141c1100c90202c500d040b5031002c1200042c001071721050034900414000b0070401640089a8034501e1244181d4580100c0140a6101150841b80d180d02000485ca850340881e1360b807680360495140d40c0c94003000028581c01c0c000d40d040c13022200300403001001c10700c02050443e54a40700703a00180b20203081c06044a000ba0010095030307103000104511408004152201511481811240d803040c0902007801d245030b048006041505051000c80c11610710740000410090660480d00a030350485282c60a480d1440c2d5005d812013460300380300c00c0100703171403c04040a9200fa6420f40a40c0403c0b8042812030b0300854099002030400300740f485003440e55009807401810f0720311301c0f81c2c00e1403602d800041403000090 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 524095863 1250 524094613 524094617
    0x114040f08071e05010912080d091212021611060706020f0a030c03060e0711070f06030c0305010509040218040309090204091b021b13110c0606010207060801230d1b050f0901030f0201031d160e06030604030f 90
    0xc0fc101c0829500c800446117007a40c40f29095484802c40300080d403858010382500400b00b0b061171907a1100e94440c1c490300303040342c00140849103903449400c015034502c02c000e4559101c0b40a81d01c40442d541c804106500c00420700c42d0350005108520100003002c07200107030001d40c13140300321005101c0503907101078064401140c4d017600d03104240c8442c5020744901c0b009510102100d07002050004202c00c646c1d219440700f2040410603600000c0004c012a100d00629442c1c160005c0e130b0144425a50500e0111003007510b03124180001e40d45c440d0421035805130042e00d0300b00400d5224000300040b030f582c140071403402442d0f181440656541070030214000046100c6031014039440300c804607902c50b903034418044012604036044c590f00800d01c000180c00c4c1c1005000f03050048841e540f6208040c01c0081586d41220f4101100b01a9440030391300440240c80481441c2140c280c22544c1d40e00020b00c00c1c0220f02c20980010504040030303140082580035541300920081c0300303404c00420000800d4100a6420b40901e0328 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 524097113 1250 524095863 524095883
    0x4050114091f02150c03040c06020c0a1a04030501050a020706060b03160507030e1c170702031f02090a0909120e010e0114040f08071e05010912080d0912120216 70
    0xc01c4100e00e07001030746161300c0c041e0030a80e040c00f10b09182c9000450060707000300600b9009648400040ea95030305612121a00f003060b420007000404405070320440034600120802d4a4140e5a403216800c0d01e406a43e00360f20907500040d00010007285108150080ca181800c10f4107625090310345071211411b448881c000d02400140d048105840b416000c0ba8600009260b504841d1012640011000789800c0c222500003448074465941c0d6a0b6500b9030300440c0c0e000300200b0140c1032010750500c00e1803105065150300c580a101e8803545035900c5d20702c20040c08030540700203403c24203420140c0c440303180d011950040c0040700c4d00a00050764000d1a42e2210b000c2824441c406510b0000102001d2050754000191581500c01c003188201c1c011a1a5088072480c0b071a800c182d170240c9c0c215011f40802c0c0d10070240425450300d400c03c60b101141c05080b2400b801011100e00f029800c00030841541c298140407580181c0080300c46400d150042e9000090b40101c002c11428030469642900300d044124502800002071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 524098363 1250 524097113 524097169
    0x414030f0d14101809020616020307080f0a0f11030a120f050909040f0f0803131110170a0204030507030308010837051606030e07061701060809030903120405011409 72
    0x3a1304240503040c1c0c09031000d0354031985060055003281c101239040380310b4065084001410304e00014074011140025000d400032102d03a51791914420000c0c003003200d85d03c0700e40381c02859940d0140081c850300c50180000c10300402d110400181100380d0000d68000b400700c1800004116101c3c9280d1a1348680d124010000076081da0078807801c0044502c4000f0100b445c00400c104050040c2134903000001c7c41503000002d011143c01c00c2200d294561340c600d00000b0405961610180d40020b815a000f850462006144c103460703850701400c0682940054000c0340340040100715410003002543d403c40a000c0142071902d18000c9019007054490502c81601d851443d8800144203081c421400303226001902113a403c0c0daa01405070107000c038503410001030b001e001000940d042c0903540c41c109190b0f001418140503800e14006403004034014100380a640b00c144011200e070b0300d04200134403944030f001400030b4846141c400010022104209201468401403101d060a42c40b250359500310390042807207810400e42 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 524099613 1250 524098363 524098409
    0x1207021b01120e1e07060306080309010f09080607020a0c081f11130806060a050105030915040c0b0d060f0506071104020a21090303110301060807080414030f0d1410 72
    0xa681851500c0c80d00803504c2c142254450030381e088420f65026400e60b40380540d44d031000d8044495600ca41d003041c2d0000c0004000640c0f08454101c400078442c1041400203880f440001d260882c00c95070304015a002e501c005080c800c00c0c3c000b0720000c00e00d040c001c00d45c020b1440e480c00c80b618180d071800c608054540310300d00400741110003681c03030802002c0c041000c1d40e545c440d1005d59501042d2911405501c1032017000c100c652082085030b00c00c42180e00100070425200c9201c3d03003140d600410503905000501408660565524002c0150764645000401c1c0706007004c8400020b9100d41d804684125010130103400007601000503818a9072040f6070058079440c410506903915a608003042c00307055000d030700744c10000701c2c154400080c55000b60360820240341c2045d201d00983c8021f00441d40130507903140010fa49248112590741d40580300d000c2420502850310411031a6400560b141140d030000420f00c0381000800d841190780410810341c500c01c103810201140000c1d0403941c0203000700101e01030b8103018189 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 524100719 1106 524099613 524099621
    0x1b0504031e031709010213082e09020a061110090222090519110901060f05130e15130b010519030b090c1207021b0112 52
    0x19042806604500081007011410080303d480005800340e1890b101601580900b4005a01c600050040c029040c0341a040a90300b5440310049426004100d0000300449003881115010010002d21040141500035030194002403041c48c0000c0c0c4a07801a680380c20640f001d02a10b41d481e6000e254002a40d115040286d407010114042103803616032a034400c0d25405130450002490360150f941c1134100650102c104401410300001002400030010440c014a8011030310003c41c0d60401c038000c2c0c1401003845006040000c04511000299080d042800c00342c007048420000502c1c1c10260200b00600c40303040240110f4400c260181c00b48403d00400b0000d00c4141c550038200100c10140400100c4c81085190406480d103603103d0b86a20789460301405a41e24030159903641240141045104030085c0802e021175000301074142d42a52088135409040c842440d182c1c801c40d0360400380344054 = true := by decide +kernel

theorem cover : BRFrame.Cov 523920863 524100719 := by
  have h0 := BRFrame.cov_init 523920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 523920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 523920863 ≤ n) (h2 : n < 524100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
