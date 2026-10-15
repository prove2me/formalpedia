-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4380
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:26:02.949948+00:00
-- url     : https://prove2.me/submissions/8bb651d8-5334-42ab-bd37-9aabe05ad397

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 787589928 ≤ n < 787769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 787591178 1250 787589928 787589941
    0x209090106090602010f141812130302120c01120213030b0903030f0a021306120902060310090e031c1808130e09030903060c2107031a010e0108060d0f0506 68
    0x501214840c1c2c4026508141524a841106110310a4a4a4525800105c6440b0740c03c80e018005002c1c2801265482022790302e404900c049006003511402000d03c90041354194030511040011032080c0700903540c881040048243c3e00312010f603100c25610400107846040d44802814090310a510282c94050188107100300c0c81004401544915010140507086840304451203080348600698040705003e0700c2014007181d44200d505c3c00c0b00742c08221000c100c44410b600000c2480c6e01c10b85002a15144d51103040001200501036541038003100c5020b1400c0103040250b4034ac0e17000480b054403070500d40d51004102c403d5030112800303c2c2c1d25004001b040d01d481d042c40345040050300a0144a201ca0740550020340d96000c00001c9865000c4040c018100686840090b490a5041161101070b4007900e806041d0b003140d180b08080e0310071760b802d6801107181003040003014409102405464100300080700d03c43d1a9981003020650030050603220301c20352800301c1c180484005d270660300041840c041d01092041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 787592428 1250 787591178 787591187
    0x30b091e0a0912030b030d09030b01150512100806091b131e021e0304021f1209120801120f020105031b0c150115020c0d0602090303030901200a080f0403030209090106 73
    0x805500a86c22691174412400b800c1e50004a1448000d01840b200c9005201d00b40c1e1000040408118608002d1f0a2841d04401010f03080400c0710320f94810110f03000100200c0408014840d005100300e000307400c102d605014084100624054450b002c0c010001d404000c001040e0f200180c072004607101000054500c03a08a40a076100301208080c0b60314801c00300310b40e0f00703070041203a00807607002b045c3c110040c40304e210107007071082080024000e10007001080e003600c14103401215150341c800c1c2200d05a24080007005400040d06030008500f2000c81110040041c04140400d030f2080c0e02400c2003505d17540c60841030304ca80941501e00682082c804035002c0717841140040c4c5080c040385000c00b45201680c0321040c02c0440038842d9080001a80a400841d42d030f41002c12603184014028000075281948850100b841d580c07003a20041001d079940c400c580c0d0088200c2c0f120400070750091000c24604442c011009040c80781c05800302a003594000c01040406000341d0407200e084402508403400e940e0346000290 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 787593678 1250 787592428 787592441
    0x6051911060708060301050c0f1606060e040b040b0703090f060510120506060f121b0607080418150b121017100b06190c0311010f060501030b091e0a091203 68
    0x5d0003503090001048000030040c0a6070100c40c0490b0002d03051115820400c03a0706000d1803000e83c0e581e5074170400890402d000f68000c5104500840c1c5628403030030320b4645803100460080c024000c0524040c00c070b000107190074283c4410b25400c40c4010a00e41c070f982c40c240003031400580c1b252100302c034202d11020403c03102041e12480b03420100d07101e00c40c56802c001070000c85da09a5003083c482d07400c8000c601c0b010b000142c14203500043c015081900704440782e55034081c160b200390481c0ca10341500b0070040350f1248482c05035404090201c0225200d048c0b40c1001e218143c010510119503c041510005806007908642c002c02441e4800b04403c07040c03200801140c90701c811200da40545801d0491045241c10b042007107500c152558001d10b450205038460454808410b48021004c000f02c9031019000d054090213030032400041d07440000b07946440c0074000350495008200c040e0203240d111041180d00380c40c1601311418004a81507160340c0795640846100203042890340100a41006554161025490352065 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 787594928 1250 787593678 787593691
    0x3081c050a0b12070b0313050106091404060c140a12020f040902120f090c010e0d060e0d170108070509131b030b010506161401060302030105090a0c06050406051911060708 75
    0x1044680910f41e00d26100d04460040b840703d000b04002156a0745450850004154000c40c00011201e44805c0e0010a60b02d8503144845c42500d200103010501c0898428a580e03050141420100d4041141001103140501c1600505101c6018035041e1400c20a40465241e8402c0182d159a60783d00ca00302403000b50060b000101c928401000010741980d012805680100340d020001c0000c111035400460300445a1001e507070300503607011055000503c45000c1c4d5071102000d000501401c080c0c40000405240800300001403003181100108101100403c0d4403040d900706440300041036683c100001003240940f80001d003100a036041003120040d18140d01000e0702c1c80f800c2040d0302a66502e0030842c00e801341c00c006440741d0600543c0a000540300c2504110110081c60020503159901c0d000642140c02c03c90700140c440e0411040d8004101c80b8905040242107541849070400341094001003181c020906c02c0b00c010041229852840e502034806089101825412600d03549007181c0010480c41003910b42 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 787596178 1250 787594928 787594939
    0x4120516170403060b0303131406091305160509010c120513030507061b0203061f17030c0c040c090312030212070509120d0212070c12140f01090c03081c050a0b 70
    0x1750f171240303004011150000c4059084004580c20541140c071010480410103038804000c0109070000d842c0d051340c108000907092400211803a140540d00c4803094410b0102040085c10080c1400c240c0e007054026a202d90411101c411328000740d0310a50707140c8551007008450b01c41c400b01c00020410002a01c2080c0c4030156550400090280a083d191981c0744034025810741042d400581d0880c200c1e5001004a6242034035050055902d4203222030b4038958042850403900000740002c442d150412007407001c503c1c281c41c00c1198180071280244146a1804014a500b13140f60389050303024400e4040e80c0c6560001018bc40351030800c0c14000c0d100b640581e0000e17003d501136020350410030b20040790409221130250003901052141e10b045846680c003540f002c9551744458200407418000324600040c2d0300b031041b4000c40480031844000d030f18041488d12503c50326810034030070200003000c1e040300341c00720313a40101000d071a4200b42c0040100c034150207010715552440c01d010805240b07600c4e000029a500d0903102c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 787597428 1250 787596178 787596191
    0x160305011401060503150a05060a12140f19140115170103080d0b1804030509090115090311010e03060c03010603200f070c0f0308130801050412051617040306 69
    0xa0340d07a4a20801d20a041c0440c90a1000030340303414140c994039a03203c4005246814068807070000801d030340c01c60644c01b00001c0004c4140c404a00040c420034042c2c0800510915091401540310f80c4404001040c040702564029290302c001c06041d004520315864a160803d40c1c0c0d07860b900000c908106d001100c0b80064600b1750040640c1011030581c0303040e83d0300141c6185c600800050309801a02180803103607000710038858a1488038bc03000d18414000c5201e50340303560ba81c8a03500f0410510b45810713000180c5402000c645050a01d4002c0c4414085a500c40c064480495202006a03038010741448156010301031101000101c83c107481c015810b07a046610200a044e00c0500ca142d2101c0f40c48214400303120707040040b0740c0c10700166005424020310079205600d603503880c0d0103400000345040d0300454135410701103a40c0c1800312020b010700d0060a2040020800c40c54281c540369502d115011551040c08000031350340c0e801d04407030480e130820281c000d20000d141c001c541c16291840e80c481e101c00c1e51400d15161 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 787598678 1250 787597428 787597451
    0x3040312050709051011060406150614120a0b12060106120605010c02061308030d0204030303180213090501111204060b04060510120f0e0c041406060d020f070516030501 74
    0x401c060285040e07680300340f201070a010511183c584011041002d002c1c4110580c03149400800c45180300d24407500703001c965200491007559003101c8581210041c00901d000c441e01040201c41030b5103014001c01020f185586560042030024403008003000d800101c12a0013000500300001e0481c103ea030035a442174010b080c1c182015040b21a54010f07e80000d000755050409480c0c0000a41030103c90342c0c3ea54002a6601e0070361605c2c680c0461035900045402060810600d50544901404001904400035610005a000904a50b010a1010a8250b544141402b0300c4004d50081c0300c3d200c1c0c0e1500d83d40e6030b103020915240c4440c00482d4203d84460910741000d010381803d002d48000c030703035003c1c241c89004250b14906803140c2c65090b142c0b541290f92450700351050160341c000c0010b072200700b030007800800f0040707c188415501405030800401c1000000e007c01d940300c0c4421a0311000d5515401a1554020719880001e0b1140360400b0b4018441c51807001038a80d056101403013103038491002040b1058218 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 787599928 1250 787598678 787598681
    0xf120c21060a1d15091b21090601030308070f0807180b0d06030219030507062006011d0f0c0d150807030b01150801140103022805030117191e0602070803040312 70
    0x45804003080704d00e460611806d0708084000d091340400c8010310802d03d0442010b40780500c00b0840b820307260b541c0064010000d06070801c9100c2d411051603d0401a4892448800380403104050940801c00c008295851071000718403042c50090300861600e0342e52840c40700c84200140890707020a0340309104203000c03030a5110a010b544000c482d4808003801019280c443c050728103641c0700315044900d940c01505448400c0092042e48c2c06080390054503810051240c5050000720001004100e150000c001400700c061a8402902c085164040000c161500e40307115480c020003881d404400300784240100801003000070568a41613800901d603602c022752900900311b65902003840380d582050745061303081c0400d501c00d400801d0036000e180b402d21022082d42039403850b000c41c028100000150007000501a00300d030040ca00803880241c00007000b24603102004503100c000c071107200a105c1c0821601707003259442d046140d2220f00381c002c002191030b2141d44c101080140d00c102c80c1100084d043d040c0000005d4420f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 787601178 1250 787599928 787599931
    0x50304080712021c020d0c0f03150c2003040f080a02150f07110a0e13030806100e060714070b09031c08061002120f120c21060a1d1509 59
    0x602c1c0e6860001001c030301c541c519841c130500784d030042080d0380314201240000014000074911380400250340c0d80765003030811503c201c00c035100032110b04014120710b01070780c00155907144c085802d0320140b103400040b4400340b441c4500c1d40050101c0d1004400010481000f24103060002d0082d01d640e0040c280100000f50140b01c0c004910716682c0c010f015030404280003d907146450301c0041d105820f00c0e501c2d0040e203e0064011506403a006601e0b1402104043d0711050181e00b00e041a203240003000f10042c1c001d0213082102055600a11340411948148070070b006070300c02c03001078841c141ea050036143c200602080e402619102e00070322a0401203000d4119400c100c82c00f05d0b170300b07546255040c0ca400d001c011000c6024040c0700b0840c482c0c400c030841c3e0b500c1000000c04030076403044803480d41c401081e030380e445c3c00c07000040c801e800420302070103c0c2030340403100b2102d4520451b10f9515441c0d10340e102400507401000c982c2260410284050051000b0b840b501d0040740900100c0b50001541d40c0b0075420085132000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 787602428 1250 787601178 787601183
    0x10806100b180117043e06030a0603060e100e06151e04020f13080102030f07050703020a05031306120c0f05070201090b0f03070f020a02010801141c050304080712 71
    0x300708110b07104042e10324410600720b2414580700c100c14540d2914504001d0040e101616154017690210a042c41e040000050319507080c594041a101b240d081c45400e180ca1a4802c0e0003400c2c00400500f070f11009511540c05140c0c0b105041091030101c00725507a0340c142c1020500603031071402d00c2c4840c48140000d80540300740480030302038004800c02d0781440b85041306094185481c1215105681641e82c40e8000350261030106d0080f01d44898042c1c901d0060f80489a005032100d0b4410000d01410403152074056601c640c0c10f08081d541ca601070701c2c08904c0d100c41080d018041c0e000c0402d8002e413005442c17065030110b65240e41e030300113030355142000320088074041031449c800b2078030840c1c04527040e9020710003034a5021300504041c0440c1da560b040241d501d030b05c0306101c031007085d40c000200403420390005101d5206125a100410f510101680040c0408806004440b601e100c040321602081d03407102d043c008034501c440c12000c1315500d185001681c0c1d4001d405010001d0040540c04030340725a000b07481520894 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 787603678 1250 787602428 787602449
    0x1217130c0308361309080405090c070b0a0207020108090d090302091b0301120204060f0b09090a0207050f060f010602150f060a1706040b010909121d0a0e01080610 71
    0x1d1840e900c0c0c10301c55100d010400144805100d03284481d07459101010341c520500640e66940b0125034080191201443d548900b00074074090400d008180c0040580d0309542c030546842107144c5402d40b00520700d0082034001403540c0310b00810010030028907005801410300c00c0c1c039071200b16101d0411a68a803540d4000c1c1c4000a1940c440030070151a2441c2d01e150003d105a400701c1481205447c01c0c030456100360068500d1854010718001181003911940c0028403001e0a4000c1a500f0250702c5e02992050081442c81091442d01082c1c422030f1030350480320056441021900e80341c0300341c1d61141d1500f0049450759449100070000140043c001705d0320b42c0d05a204614079542c16544c5003080348410101402c1e00d600300c1501d0342c0c0411050040c002c075826100303008005088501c1c141c6800d0b1204031058000b400c4241c10203400d0720001d2001004c81d101c000c0c1c00d00b4444400e28481590b20000520810f80f60703480f0354501c80001f00c010403240041e040e030f00e041c02030322003d540fa0751200006042034811100e205 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 787604928 1250 787603678 787603703
    0x50405090a06110c0a030e1201151a040906060c05060106030c0527030609100f1a0d0203250501030b0301110a0f020c0d0b0f160f1b121713 61
    0x1442c0c80c3c0c810324222145810107400c0c001c403c0303603052500e00f58050440c0402d100182501e01d6180a61a0410504401c40207201896035115024902003203071183c000d00b81000860b42c4203051000c8162005400041402c003d50782e62210000c0421003555001e81d030724000ca0001141c01c0780b082c00b80344903d40c4240c4910380f404a03012880b0510b41180d41e9041520b0200c0449400e02e55020b103e41400b407802c0304000c1030380c002a101c500c001c0383d000c0240102c01c1271501c800d10a0012458101201451040322604024902800402d080040940b8ce08014044808020710b00c51402000300303003074610a907810403240c3e04071024582213171412000003200003400c0c40041c80c0c0c2845000380e181c150302288140c40c0781e18900f801060090440700b80c1203420030020001c221940810700c028070b900104400c80c280c040e5207100006842007500b48660310400c03e80c10120000101c40c2445a2680f56004040140c0703955801c40c0100100688a80580d2545801000c214084541c1400e01d916640000ba04500b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 787606178 1250 787604928 787604933
    0x20f0d020625080d05070801080609060106050a110706120b0f09010b13090c0906030c230a1404080604290a0506010c0203030c0d14070c1401090b0a0f0801050405090a 73
    0x7084400310701000d80c0c41c0a030391200700142072880030b03041c4c0300b4140e0000304090406200280c2190b41c140c00c040a254045030401803001030020b0300340d0440d203032030401683e1000380360412a220801070a81d0425071140010014100c1e50000304a504003200c9031040241d108100708014440442d810300b40c0d8000101c0780141f141d0700280006001100c3c1180402030690ba481626805403450015080302064002004011154260049520000c1c070351404240840209031341d1a007200114081208051012275038011041c000d46408440c000540002a1600c3e41c0d4164155642ea04550454554001c1a5058084d2403031003c506001a0052400005586c0740d905030401400010303d480d0405c010804140c0160300c0a000408003450382c00302500d9459060000a0a006030117600401609410401c20010a0112500320203941c010305008450980250040f1070740d00c299005000824000035a001c5c4043d04038400e03600741d1405032034230001c80c0e90381c00401c002c03100d08031100b415540044442000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 787607428 1250 787606178 787606207
    0x9080304060c1502090d030e0406090902010c060903020c0a0e1e1b09030a0605090a0b060f010c0201030911060316020d0309120e01030f060909050c0a060f2003030f04020f0d0206 78
    0x1c50200382070f8018180180800000e9604100c2c400a801051542c0941009800c1500a0700e01404181806004d0841c0301d0340001c06c0c4502112000d4422550b40c1c4141d4100340c4240199400100000d140c20030b07294a40000c1c110b0514161140120115490f00b01d02420300343c44500e52080c1c1071030910168001e480c55118070b05070300541186034075004145080c40080d0681c0b142902414082c1c00404000c1502e2424116000014180a03c112842400460160f07803104030005025170a1901240188640c5410f9040196070110140d0290000c400c1110327500c84055240b240301061750071104402503041042d802c5441e8540c0181c90f03c00003990034690030b4000e25801c00c8a10040c980024142c64540c2180102c0d102500041c0380c00d500c8641d0a414081c1c00c02c80090000070441e0301302c0c0258503041025000c08030b4821113405201c00b20000c4801c01145c0150300051b4020300c02520341c2c03480c2c00210442d010204480413441081c14102c0080142004822146002ea0146c01d161400f407400c0803806 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 787608678 1250 787607428 787607453
    0xa020604031506080715030b0301051911040506030c091903051c120603060f0b01090b0406112b090801140601050d2405011704080f0f0d1b09080304060c 67
    0x780140d07224080003c21010030071039100141b8400004401925032000c3c0107017075030034010030b444c8a6814102070000f01d030700c0030103050303c040b054040000c0c42000041d0030383d00d5401540e10840e0700040c08410406000c1c801c900034181010110381200c08140740c1c80e46807403801c28602001e0b08940c070580c0ba180d00d204038400030300154002030401c601049a255400c3c01691101d800481c0c1c03064650b50504550f14081c02604035400d0242400280c3ca030403c04000030b68084c81c8a00d00030010340d42c0003100c2c2c428060162a07681400b51f03e0f0298014280220794400402c0c0c00c0c140d0780040c0703e00100003188170040c03140c00343c514541c030f8609440b40c030303034100441e40d07a081038042031500b1b0340d03420308081100d044078103410007040c5507221700c00c8441c174010005d480b00208541c06040765050038200302c009103e540031105c144141c122001c2c1c0701c4034401c0900c900c0f8002d50315821122440d21501303841c6406501000e5840003081e0b603560006d01d440c1c07042c407512401140b0403400443ea180d405e80c80002c15100010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 787609928 1250 787608678 787608713
    0xf0f0d05130305060a15050609130b0f06030c04080601090903020a0b0403020709020c060f061002060a0c12060b2a12030a02130f090b0a030b0a24080d110a02060403 72
    0x50030090b12034507600d08002050700c0f20941c1645c0c030a036494182d11b10210000040038110303129800c00f1071407004983c20b05610002104070355a58001d0003c00e569036001d5000404028101c1a12460071300720001160340180905c503018401e01000003454880d030f000e42d005071603041c0d0260400b00ca40c0d40c2c50880390344001d88210190302982d800418070180c0b503c09810807000410042c5860b0070507452000d60440e0140807240a20000100c0e0308807107030000783c0c040d0000e410303483c0081d44500e80c0b0700448114a4085403154040e00748000014001000c201800f040c2c200103980381141010203c9144480c100c2d40c40c40f0b005038020107050345a840240000e90b40c8294007030405403801c0404003c1c944555655003000c6048010020180701e540c2d400d1251006000b4152054030f056400c640b08c040d80712600620803180692600c82144040c0c0ca0b00c2c110218100c3e611800c01c2c02e40d034503401c2450f158a600102d2400003001c07508040c802030000100e928046401810b41e0b0700d45810754440121498080380300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 787611178 1250 787609928 787609957
    0xc01091e0806070509120601030209180c03010612111f11010f020705061f030803161809020306040f021903022203030f08070203090a181104030c03050f0f0d05 70
    0x71284000d01c0000c2c030031200340e0380303060b9102c00000400080c0040c40c503444009601001c010700068881140c00e64206c0d1001800301820802d081060345000c0541e8000713a010750034420002010360301c05603010500c41c42074840722107130032030b51051160440401420411000c0140d1109104902030300648071120020300001c2903e0b003201240000703a03070080c141240c0b1030b446842044030708010042440802c0c42c0640c130280c0140e1441e00c0303000e42c500010708070b0303408015168205141580140c16480d05907200b41c20014540766504000c0c40250812620306010358107060801d0b810500a20032110b128105281e81114604400c00880c002e40003071740d0480c040c0829083c2c0a504850001805000b984030b5070302c10f0b14410841000901885000e1300b284190341c02400801b032160b0700d02d40c0000503a41da00c02e88181076a214010740d4044c100683c0d052903600c500003408004c1c40600710940c002c1e2402801190041134024650a0395120070404500003500440c0c600a8042d01c504000c0c00351807000043e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 787612428 1250 787611178 787611239
    0x20a03050a05070b100515070b01091a0306100603050604060503070e0a1d010e010c03050412120f020f0405100503010509040b09280203070923040501020c01020f040609080c0109 78
    0x44540601c0300175900c07403804105681080182d45081e4001d5081c3c80c2d00c0301c601c1d46c2060199a2036a0b107540042c000c4090558550300e03580200203140c00400254180201210040d00702100304088120060250600007805d001c00a0b41c0c0341400d025010440e40b01500410302540f6000d4010b01b180b8019001d54032560b00c51404201d24400d0b0318481500d4448000000740050301825410300b1140b82002c4c082c140342c00c0808000c00702d0700b200003610111000d42072919607141d00300e016400406035034003040700300d078400708469448401c0c020142c025500141d4240e41e072004420825580c81c0000d1007401d074808012000540040c0e112442a50880304c140c049400c15048405140c500160303407010b40100348540c111010540c50200000e00c010a44440204410440507030a803040202441912129901c02e5001c141040001d50484284a04800c000c640303d920b150a81005544079129880010b041100041442a008900b251621034140c540500b10392404ca04c2c20b4401a861903103444a40e2400ea = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 787613678 1250 787612428 787612433
    0x170d1209120807020613080a0c020d0606120b0a0204030809060a050904020a0806130501080714030f0604030f0f1403011a07050d09180b060a20030a02031201060c03020a03050a0507 79
    0x5207110800304640c803800c41ca072410610003450490010400c2c0c10001c1c61181d0440400c2e0104115200e2091034070345064011a10300202d0581008103000501051400100040440788201d00702c0d201841124414040e40f180110b10341a40a680070190842c0000c01204100e031070103800400f150b000608245041c256914001422a00500d65200100d0350000801c5203610b001e840c0d800c25003410781d40c204003d5041071030050740d55041f800b43c40c481300c440f4449180680e404111a0300240808802c44405141c5854014a0071541d1301c100c0c40441d4808681822a6000311210403c100842d440c00e401c2d0b86c86c020413903000c0306c0719050744081103c0030400c10000c180300b4803040d00010815280c0800881ca480c0c0c096808840248182221038a803c2d01d101840e610001150696000c500d4500200315400c008801c80181c800e03108103142c40001042080c5503000300c0580000006901c0c0d401c41a030703031200283c4502001303e0004005070001143d1400090040000c0c01d0f4071030700b03450070506055250707 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 787614928 1250 787613678 787613693
    0x90a05010e180f01060801081f0b04061e0501080903070b0705071703101719080c010615020a110907020a0b100f08010e010b012a17071506170d1209 65
    0xa80304a00d03d06240380040c001e076a00074000302c0c01040c03d1802498680d1540d40c035103003804220204584484d440e01007031301d56940c035034007d0406020002c0700302c160b4a01410045071818124411640802c0c600c00c000b0f4001fa402106070781505030840c21704861991160707001c0300e041d0b00c6500d044410000c02c000131180140d5030b0700a54484c441c0700e281c00c40020b0804007480406058801025038946c000c012841007017101c2c0410f4016250302114568403912142c40340b40c0506226000700441c1c45c0d200305110702c029400611500340c07034003800b4511800000e0b6000c3c410080300c201d5250300940e01c00c00c4c0200005111544d01940980c3c190040c1206a0f1200407002c0d036083d00d9401468280e448201c0240508020301c52101074200908103642840e0b021184101c1200e19103a400130070710040c0c1c151380c050102d0070400802d11403c03c0c010360b03a2824540740000242e09a840c00c404003910782280480c401481c84113100007000000024080b408015004550761201410b0f03100341c69480b104e10500003201c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 787616178 1250 787614928 787614931
    0x10f02070c0b0d180506060f06041815050d0b10080c0915120706050c12040e04150207060f1d120313050a020307030503190f0912030c240e0102090a05010e18 69
    0xe4006d040380c0d0828004100d12000ca502289100d442c041004002c800c407160303017000e000b449200000c1004400d1007e10207248050b648900e4001c24590050010407460f209024411b94070540502911521846030b603070b90349080c68040c1c1d08080180701103441910f81c54000c4111410007003030607200741006203c1505042c010303400900414000b048202c3c0d0204140002094150a09805420540b078100c49909110015002515501d41301e0001070b001803258048504190b0008024400303516601e10703e900600d241c45c40c903603941080b90640d00101d2404160309154110340780420382540c44a09d00000c4400c007500049030188108260036005072802d001200085001d403024588604640900720f034082e02400b000410854483e00c01010030780c000100f001618491744e110302c3c1111492906641400c601c02002e8010a40c07074840061503a01d0074a40d9085800165061000711160020740d4284d0086090050780160058018051940319a0501007110001002030b40b02c824400f0844824400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 787617428 1250 787616178 787616183
    0x307020f1c150b0d021503061201060f05180402090a0e0a170702030607140301060804080c0a060b1507030503040f060b1302130b0705030d0506120706050903010f02070c0b0d18 77
    0x5541c4070342501d01c0c1681c0300fa0481c00805840e161102074080d400200303110a21039641c21031400110204440e525000200046d1410400003084995150f10090a81c2c80b01c51140714499842c0c1e600507141c003150141d01600071030b4040c02110b0395481e00e801000c0502140107010300c144c130940070050082004070b440803209111041c56217070388a51600500d07082100050100c01804a00840b06101c004000101c03811140075150003881500c1e0380c5041d900354864950145881d2050300c512006009250740500c0d103a03007007118128402000110101564041d04134050042a02030001a02040d819031454519078450103000942c03201c5200090318209005000c00c4407183c0c0480c0d100e4080340c1821b0848080d2000f41101410b00038959200c3e40d40380320301500528125101c0000c150030382c9480189600b0840d200c0300fa914503c1c2c032984000e00c19002000503900c02c1d82003840f0405130442c0b03482264041900201a20b200c1030500000c2c64007544000100f0b410180c1d13400b8911920300341e00307640005052 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 787618678 1250 787617428 787617443
    0xc1706090c1215033906090a0f05040b030a08040608090106030c1409011410140903240c0324040e030a0f0212070809100e130207020102011407080601030e0f0a03050a02060a0b030307020f1c 83
    0x2810641440101e8330381e50040c2d8002ea000c0702e01d88000c500c9100a843c101d800502d001401503840d850114003403d46a0310092062503995804201c0c040030600d00801c81c24141c0d40c81c5080daa0303400d800107203030f42c52022284d0080305c0800684290b6100390200e0201001c0b034051186400e400801092070142c01f00400540d48104001009000301d2140f8100e0300f00080c0d2442c5821030801c244880c2032000f41c81e182200c440003881c0b200a9545031500812441007920069903120042160064100e00c0d8254ac50350040c0034980700300c40008802002d44000341d4000d00d040d07081140020501030589000c00016007441440000b41142d81d03a280c1d02c4003c00c0c1e200000c0582c4030318051002a0a40d4001e908035400f400050b4104504d4030340c0320103c0c1d41d1041003481e020440b5181c4051050414003480f081c51040d001301c82e0f00f0710a16801030f0092800c540540d00f210780e00d40c0d4582c1c03c2000c6800403ca01d07036140d0010400c04000d860650002541d4aa0080813103450210031a42e61b0035040381000c0494101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 787619928 1250 787618678 787618709
    0x916031b110d0c030e1c0204050c18010c08030f040c0e0a0c08060907230705060a1a06480708010c1706090c1215033906090a 55
    0x31441445810b104040505081038003450a59000d0b00c0310b0003402045001c0d0140a840711141d600f0242c56040d0183c01400c00c10507418007400450844d803121848001071680c1807070502036540302c2c00d09401c40540004c90a4150348601d0701c01e24a081c0c0103441940e010644101c0881e04954a00e0494010074803101d0018034411071030400303040034100801c0d0368407501346002000900c6030882d1070782180301e4100c003e914400c090b94504107801c2c01201e00280c620f1045e841005001702443d489450755409080e000400c01c0c10300e408004692043d1a6007004410388002c10280c034103505025400e034801600c9124034054226001c01c80828444060340c04a903202c0300003040f07440e200384181c0501100710720700100c050b081590080d510f10340c0503040318014150340000403030b858006419228028120b01d1002c6c01400d040742805d03210427142052a1103030040d41400031914091003191942080741040340301008034001c0446000103601510590402420410038545036680303421600a40a04d10781032407034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 787621178 1250 787619928 787619957
    0x70207150e19060c02011815081f0302010c060b0a030807060c120e0a080c0717060103050c010f08060424090e0105010f0e010b1606050a05061e0916031b 67
    0x5800410300b0b412009840a600340003103036115443c1c80c4003e4081c00d010b00c1d0f5590128406610414a5010f4111501d500401c0d00340540d1081c8010700800c038100c1203c403d1390345181d100c0b0940c506031100074089060325601000003003403908a02c00041c0000e08240320199130351100c020651289108692003542c0f01074140200e83c10446120300c2d209030600400044c0160420310b6a60381d00b402002d819041c0c00315040f2400c0c101045892b01030032024420602c0703041252205942c0301400c3c00112040d00440c500740d6501d51290021800b580400d07079526009072190030500c0b004103005581c102c2048520060503554082d42c812000041443d46d100243ca60750042030282100e0068004c5440390030105010003041301000200b0781920844010240c2d40c07000d900503d1000171440034006d041606240030845689404d0b40490721400080e00e00341050781e6000090048001000740c13640c6d1002940d0081004814107a0900a90321458140091242e024580c0e0038680500c0c03541000c0018241400c0c03020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 787622428 1250 787621178 787621189
    0x5010306140703050601092d0815070201020f040b031504360203070e0702190302070302042f0c120c0d090e010f05010507060219120b0a0806040803070207150e 70
    0x2407264407843c00700018200f58000810080440c85507203041c81b82566508201c85d54000505241e400c81c00320140080e030b0301c014407503c421070650070005060811000499150041c003c440c44900207010302031030281011040f420702c2c0c002401e5030840340703501060088252554480c0300e882c3e2050002c00e0420021005004544240300540600c85d80c01c1081103000589000a998003a02c07051691002d01d0b658140c0120304d2f01b00142609800518400081014542c010413442c0c1034a00075941400020066100100500c03600c89138a02c1e0052003128010f062100080039205680074202501e03000c40c90748041c6601d07a007004090702881d03005402840784841d008640c903c000c1526480981c40c940c58000258540364051140300d06112001032074a0410502d903040715034030880811031030034018000340010480758100c0712147e501c91404450210345d152010a8104562074000103007903079034540e9200100e90f040605084150701c612031020480245c8242003208000301951004d1810300c2000c100308 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 787623678 1250 787622428 787622431
    0x20a050402090603191104320f040e03090d230606030a030c051615090819031b050d020d0e090420131e0617070303080c0d0501030614 59
    0x140304510401c100e100a489070410389603c24084400d41980c3c88050544a000c0c0c145002d078942421000030b808690100c01c0c6c03006c1081d01d0034001d00311013440005130710816211882e84002394458502d10009441c6d107056000b001d07813040c416003583d0030001d2000c0810000c241c1e5200813070300d01c07055403c2680c1172002c0e82e204c02c00e880d050100800309400d0030b40100341c4078402030b240a400c1003200d062860902208000c10800c00700031501070800705a46082143d07281561103d078800044958400081904001071418a5102d01d002c1d018940a15950155502524040c0100c00f000341415183c0100700e05101251000c0d00c80d4002e80b030140000320004100b10000c0408a100d180e980081c080070030440410010800c13004040d0956503840c0200050340114988041d49c042414242130200325440d080e086140c41a05240610a05484154424000c003d90044840543c060038080021903c07480ca807035000750020100d10301d80305819042000348c1d94242c0098855a132180c040c2a04481c181940700e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 787624928 1250 787623678 787623689
    0x2040b0705010e0d050f0f071209030201030e060103020306190b150310090e070905061f0e01020d0201230618010b07022d04020d020c01050126060106080103020120010216020a 77
    0x2000508480d09005d085400703100802210ba00e008500221480c49010403995800c1e0030000407014550140b0000300190aa800124002402c120040c0b10b003c00c0001c1c214103aa0340207020300340743d42d20861a02c0c403000c0d00c1c0940300b5085898041c07000c080d03140c031420001e114140c0246a996864882142001d440c00343d4804031040380f600180942010010a078030003615860000480c0c2c588821000a030000280215820703107c0a00c0b080716101c035000002e03800c4005080e0246d401545420780203908981d4101d0b448413258481400300203c481c803007044507500c0703038004008250001e15040c2d85100b40d01300f604042c00e13282d00040c0000070340c0303045102423001626454003c50074485004244820704051001e0030300442e00800c0c0740c241881c1c1501070700d0b580b403003803002000190ba54840d08080c96140c80c1c141610b500c040201c8414542c008a004c0b03058491f151a43e00c0c0c1c0ea4a0340c2d004540700780e540c401c280f81c480f14407002c500c1d01120a00040000300d002d25213031032100555004104100e417055000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 787626178 1250 787624928 787624933
    0x12a1b03060c1e030507090e1303030e0d0909090804030506040b15060a0c0f030e1c02040507030203240a0905070c03020d08240d0f1410051015030f02040b0705010e 72
    0x220080b10380520035424100d00b45180c0402d460310786d6401665200196041106000100c02c100500c01560b44100d501050081d0b0b0148141080304811585130b100303062011000880c0c04009200507992034001209152090311442d2030690b598a445040c480d040c0c408035080141c013001c2c401214071400610000d40c43c00c8688070729180b03980401400c0303c002004001c2c02c800d000d0ba04401458060110b44007081c00191a009142c00e500091200805844604078465071a040109403154428030a41e40f00b64800724818841400a0b405071050f0300002c60750a62100c5104008150b0038000d0180b0340c086c03002038550800170307002841e01a052104954102e4104040c00701000281240e480f40214181201c0008401403074600e4042028840198409410701c40034944101c00c20114402c3d28009448800a075131041d00d96921a0701541c105540824110034180c80038081c01c0c49414241d00d0a41c22800c0c001204400102ea020071398000c1d51025038400b502141c40d40c00c0c004203003d008042c5140d01c01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 787627428 1250 787626178 787626197
    0x2060304051509120a081801060b090414061c080c1926030115140c06010e0112030518040b09090c01180f060507030c080d0519020306012a1b03060c 65
    0x140c02c503402807860100c100706d650008101c1a41c410360580c000c40a410b00280301c0c81e626100d201100d50f00540c003090013180340c03581e1040180604411b0741e02a1000412240c1c40c2601080d0080032125418000d0b26017a40800c410f80010104004950005904d400c091121202038289181c01058030300c0c205506480264031307800b441208900312810340d284100188011445501c0407900300e0300000d030b80d10600c3c900113100d20346588000727815412180b02210094150381c076603400e1a251004a600200403035800d0040d002a016442408007650b54080e0000508188040000703c810005464400d00c0740c0041f0f09a41036035030f02a606c1910030449450a0440c03504c2c091a450300c00c00c20348281d80822401013010030070103105421358040b054001400c161240b003801d148200403e01600d0003488844902460b0483c682280252845800c0503143e04ca01016080c006050311040011210160418840070100184915070080044010100912002811480c1c801c04a502d090005000d1101000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 787628678 1250 787627428 787627453
    0x30618020d141002040b0d0507050a090501050f0d090c05030613170c01060e0a02030702070510170c040f1e080a080d020c01020f0f0702101d040203040f02060304051509 74
    0x8426280550b11002d000d280144003014241001d484001400f001800058001080305000000e0003602c441c2100800450f100e458080d5641d100313181c0310001040481d036003086a0343c001c0003e855101600c52502d07180c14091241c56003206c204c030b00104c46840c00443c0511030748c01c0c10009140d01520038035403240c512025480e810b00b42807071003178181007410000500d050710030400c1d0031040041103110344101550402d0201d04001e9041210a0001171107142e030000b07640d24042512186484150321491981203811003001231a00e0000c10001d140d900411000a50010040b4400014044030011001c50040d40301c84070705c0070302c01c0d9105011680c013400802e0045021306048401d0058070500041e51049010100b41c0640620b852040c80941c02007010f441c181e807504010110745100311551503002044074410f55110100d08261b070b901d640c0c6501030700a03a003081c0d8019504203000b2081280c6015513580054265441107408581540101c9401051802c11281aa403c4504800548001c0e200b54 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 787629928 1250 787628678 787628689
    0x110705060f0114120c03030a1d150a03020a090305030d0606090b0f030708071116050301230c092224140d1a0103031e0806150c1203010e0103061802 65
    0x14192007441c402803c43c040342c40800000c100301001800b83d907148c1e032500e00c0207840140681c4000043c03030719011130420281f9100a503084424000c00308182005030f8401c003100203401100744a82440000000800420010070160113054241d05011940750b041c20700040240e400755205648294045c01000d03040c401c0300043c1ca43c0035840340350110583d6151582110058035451099416000e4000d00035154501a0424000d81c0e1055000344000c0c1240030b00c101e000140c4404441e100c115620200d04103041c403000802d04240e0003400740c1c1c0b000424440d2040d1980b06091101c0103070340c1d5100c00c1c40c00d08941180c00513010b442c2c00d01c40460076182c8448221919000a1011310401d914204442040040482000300210401c100c8000d5a107900d00580b400e4491120381000c01c2070307101d65015003446420402d01c1100040c0c0302d00d40b041580f46643c011504020200340c801d000740052011500b41490155000b010f04c6100324126501d1402c0100403501080700341341500c10b03140707845005a103d6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 787631178 1250 787629928 787629959
    0x503060109050403050f0a020309090903030402370b0a020f0604050a0615030b070309060e0a080f0c010605031b1801030809120f0a0c0e150a0303030b03030706110705060f01 76
    0x900700082100d41d42c070f00c3e08480901c540000c80300704203004030f0741180c4164000050040e07498156000c1782d0035140c0c03030b89072680c90008a82c003c2d4405140505002d50b62a0281c1000310220102d1520042c5044031104522075119904900028200841d168a0300f5604001000102e504940541080e0400d45c41d0340351103003a4500c1c0a8101750315001d5810900001503090760003940c028101003003034201b00b5002005800318100039101c10b402c2480c401a0702001007640442c00343d00110161402d100071090341e4568014500700404e55596031000a20741c0c6090000c5004080400701c940700c410f004100b04603040710b00d80300720328940801e88014000581d510003140c148041c11100550001007007440d0a190007040100c0d507400340505510720b020460541800703426134a11215204056841c0540d5503030071112141d105900c100250800c00100f070095014040b0340074040c00703407482c00703055440d8001604c8420f4402c9402950019581041c081c09110494000d0b80444403840700794513044641030750411 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 787632428 1250 787631178 787631189
    0x30e0913120c1a040506190203150d060b03120310080706080a0218040c030b091303050f16020a240e03070605130f0f030b0a14040b040206070507030503090406090605030601 76
    0x8540c08000d040c840314540e085981030b1401050f600b1481d0034034009031104030a0b1812108907402c030440400c030400c1b9000f541e1003000314440d1300c40b0107282c5c40f00b0488403c104506c180e40707081e03076142a0f041e5a1405c3c0320700001000d50800c00c41d600c1c10403260403c22a141c42e400b1a0154203c06001d02140754008a415002180c042c80075850b440980c0002500820650f995584589007040b81310001d40c03d41c005096440d0100c0320383c1c215643e640c1c4054404425010020002001040842c1d109403007240941580e8111a40003190030b612070380480c003500700607000120b0300b445500762984603c004000c41403100440d450f18900582510000c1b07071392560540502c030184900828a42d400b44050030810b0002c0000c800c400b6004c41d5241d6481803e80b1480c007050300d200903658005000d201c401d000c2c201214550800c1c0034425a240e4451000202018100301d0b0b0106e001c10250b00490010001040a1406a8003465552080d01d082104075a030550064540d5418500100180e540120350281141c8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 787633678 1250 787632428 787632437
    0x170601030201200c21060702070603150b0406080924060a050301230a0b06040f081203100e04061806060f1208041406040b070b22020f1002010b0d030e091312 69
    0x81c505280c1c0c41c20b080341002c01701030070310603a0300b002000b5a001a50310201e03400ca403400c11105506008801d00c80c90140100c0d0b4040d20700f04410842144100038156200c034200d81598203281c9400401017003a01000060450951000140719142c50103480d92001040300310300811050b203026580c0100b41d0b00c400404010181e0b40000681c0000c1c464200d40140c80c0014102a80c0e2619040c40075070710580b43c0903281051040086040303041c44c8400480b40510000c1125188052502c5440c107030245008100300c5025480f070403503210a901400c03101b0f003110300c22075010a265051400b0781c01407608907840400f4203500c801c404000306040c1400c480641c0c4840345903a450f07240401c0820924402d513403090942c0d038800a4064144a006290300303001d2840c0001540340c09a20791445092480042006588403440c403c4200092504480c0009140a64000440c03500343c024009400612004d4041d40410f40354244c0d0440d80c070b801d03110310f50f0180c15504540c02c80d8145883d403801c00650b8a01410074403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 787634928 1250 787633678 787633699
    0x4030306080f030415030b09041704090204140909071208130506041d0106050405060d020a0c020901080f0c03030307050a0f0c0602040b280503070513170601030201200c 74
    0x52103034011101400040d81160781c02598aa0003e81d81c4d40907100e0200360140a0f0180f2038128030a010b403403c0704200901040744c0d912a501c50b200c1d00c1c0c10081c1c2e03410b040030007007000017600a090f001820080c903200c103216941000b078030240902c4900007010328045800c5040107003c07500c8a4608080e01913040440c203504e6440c00c58201400b500550031095020f1004100013034142c900f02016007c0c42c0903030045103440c0e40d9650050700c0c2c40c000e50050b15481031061203d03030200145503001c0c158004062a000340b842c2c440d074011a0403283c003a0410300e290b401000a440c80e40702c081041100c20b0005400861852601c003030001c00c14011925540b0421081c1d13224074038542d00c0b400c8234648454210004541c0d550b07603103681030b0b0541d005480302070041c0d283c0c01c2c0c0c4403038aa004a541c2c0303112502135101d9506e16681d40400f1a0f09a00c07400e0044200b51301d1120100e58010480364200314040884014030040d4114000034000745090410281c1d02c2d0401c10f404031606101203407000c445041926600c001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 787636178 1250 787634928 787634933
    0xb0417121c0609020c0c011b020f0103050901140414070e2a04031b030b090a1a0c07170a1701080d081e0f0f06060c03031b0c0604120e0d120804 63
    0x2e80407641c00350310340d2030010409010082d00030511569405090301c0d500302ca16854031010310f48050311070001c0d5200c65003502a4246500035048654820000e400000d1144480c41101c034522206407410b03541d4280c02e105850b0800410041b000180a031030328140d010749011400c03d04915a028618119010510b108501c810030720300540e005507030b01c40c0c1c410100124034505041100c0040c4420359070f507444980880c2465001103421b840712a001603c00141c3c160001a0081c5a04064800703149508100b020001040d030440c0080e001d820034040d9560303244003100004003002040c05865134000c1114004201100b0b0010354031041d18154142910695121803d14800103c441e1941f040c914415082241c0c250806a4252041501d552080c00c103407102820f05c1100d009200134180302d50300c00c1012130158200e02005e40c405441c0e40c010940b1704890803003154100402618210340016002000200d103d17007003100224076600c00da41f120310f03660f80d030b840d105101840381860805112038071020509 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 787637428 1250 787636178 787636181
    0x1202041208070201051e09040b0a0b0d0b0a05030f010e0d022a040212041a01060e0d03110a050706170618070315052211030411060a0314010b0417121c 66
    0x80c40350309005e166080701205109100c040e4840d00c07032940f09502d4409c9080341803074409001400d84408104481c00c040d01640c0b080014620965440d90241000f4000902075600f04648000c207680c08002140598410065518110018240c00c0c20f641008400c91880000c12111031000100d074071600c0d01040312900401d0080c800c0088a19842c84000204814061080e0314a0400d44940503d60070030307070741e4081c225041203424a4499002218411080210740304120400e061002541602c450b14403594500c0d03c3e100c0c950384824042030120508540500c182e40b000d40c0e0217003058803062180a8151a0080000c0000700000140b5a80d008246504400700310141c02603c2c1c081c2031a512030580340d00b00c080340702d08030140c03005c0c82d42094140c00e8604401004c3c0c80c003c03544102c440d8040b01c00e8804000241d00b108a041042681c1c82a90302000015802c2c0c1a0080c0720584c0302e181d90300e007030050700b0340900702140c00f100039544080546450709001008654541c010489010340d00b0064180c20340 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 787638678 1250 787637428 787637437
    0x30b0c0a1b060603140106060e1002010216060e071a04090f2903011a090105010c030c060203132109050f0a0306020c06010504140c03010509131a040201120204120807020105 76
    0x19141541c41100c030100001944a032082d039010310761100300212594080b501381c85090141c078002840212103e4114201000031140c00e10043c0005801d2841020a007040740d5443e200c00d41c0c855031518000c0c500e40805100c448060410440c2d4075680000001c980c0040c2d110300e21400e400e490b03035550792440724125030303200c01c10081206045250410285541c81c6030804049407091095180180d0f40100005848880186200c0a01a8065a8a00340c0150f44450100d10140d05028203e401c00300000c5043c4021440f44038034044124042101c1d0800120911111450a134901180458455100c1c1c00c001d44030125501211030310707160700c102004183d00c1d0010350300040596002080f001241d220201d0f074a4162030040c0d60401c0041b002e0580c00d44100800d942c4007a40410410050100d4100020b46035880f001103040a50009101d1352080d0034003000023400803680d002d100c00d1004642e84100119010550201c0541c2041d042c03040c501c00141c0001d0009256140014500046900036420385 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 787639928 1250 787638678 787638707
    0x111c0e0306160801080706093005150708040b0a2409020d1802132a030903120c02072606070801081014060f0f10020307060b0a030b0c0a 60
    0x180c01c0e905090b4114801410301c00c80e24408508804001701d00d02030001070180c111843c03a038a00029510300050180083c1500030b500c4246400c5110b49c400d2600ba580300100882d00c01e5005040907949a034000048101c0030b4a401d00700400f10041c04085071100f141c154000400f0380340004c5046030b88412030319041d07000d144108000255100052122070f030303a01a08a50b03200060a020319854107410b004240d800943c003d60190402c8000b208111090f8450407813203410303404000031080c904440c010102a42c1507041c0c0080c1d00d8821010805230300c07002c50314030b044284e2018480d440e075001010351509414010340700410340710650303504566607540403140d45206400c2940ca40741490040207180d82c809000d2a0040c1c80b0710b201614510b031191040011a1900d00c007404225220201049403120412a405612000c191180f158540e0303459070f092040b00321034009683d00e1215180040035200c0b00c0c1c440e03510440c2c180d181000403480303407450310b580050041609a0364034204142a43c801c410f44000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 787641178 1250 787639928 787639933
    0xa0b0610110d110613030c14120f0a170c030a022208070602070f0308040909050c030f01062303030f0702011704081e190f020c06120610111c0e03 64
    0x4000b1590303000001c41c1d06a035100c000f0f88040795030300000d1802c01115003100500180e410754104c0c010880e42810f004c0581c01107002e03103141081c000c110800a41048050340c401090000d840100207400401d01d40d4001844180244c0e5840c1c0003105440310b0000818909031150000f4241d45031012041c8444400002e003040c48010685902d081c680e2400d080c050720000d032240341c2c000302e00e00180c0130503407003200c3e07200c00c01d20b00d09810a499440130340343d494011519403286451925655a0038015070b07004d180c030000009061171401c200001c5241d42c800d1142e4201c605214000c4280d01c012007280d07401c504007116a591a00c8600c012a800c04114983c81458180c01c014041005940001000f201c190b20503c6140c4448484860703034140306620407204401102c03555070030b003a8010740d01da41c180c00481c0180c1c3e840c45c4021010440941c007180080324145010010004145807020032030100c10714500d0503005051410300c9442c0c2d01e400921840c02d29041c800c40d4505244d03c154003805800001070103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 787642428 1250 787641178 787641193
    0x11030708070c05040c020a0c29121f060e0405040c030f030c1709030d080603120d020408011109030604080c07030227010e060d0615090e0f0f0a0b061011 67
    0x100b81c20111054003c46200d00e0800f8603120000d480000c0b58402030750003c50264040d8078061000c400007884040112012080305014100030b10103101400034951040f032107918030300e0210800070702c136000300000000e1501034000038800c05a02080ca0f0311103890903a4009683e132100d003007150840f619503000800c0010910240020190b204040d0701e012446511104021549101c14078410f0207045e0002e034050788400d0340721075003130710401c10b0710740211000d01a10107403448180380c21400e600030003940c0350603a00090b0400c600f0109108115540b4507030450942024030780070020391030700b001a1000d450180b021542c1d2542d501c05104890065900074003091761842e10401d040da008104050b1002e00e410080000501d038042d450301c4900c03540c402020305a0340c41095840c030b001010201400c007003021034a940420740184e5481030010750030b15000100281c60b1600803440ca04015030124801c143c00803940c00303000541c03041071950010700440700e0031250300646030119188140c44000e6580c03441100b8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 787643678 1250 787642428 787642433
    0x90b0406081b160b0a090803152e080a2a030e071401110c0a0936050f01150b0901030219052508030a090c030b0108010203070e031605011103070807 65
    0x502c20510130f12580c1c40d60a2681c500480008840e0061000342c4900070800026083c0300e0740340420041020b008102c103150f42000154036481e5481d040c0f41019113280c2640361807029810200480d8018404c09042c041605000c03c1c1104400170300c022054412691201007400300d000e908942044540c40d402c1b01c440c40d40d98007416070b103009007025050101c2d03003406003c0b004440c00b240e05084c088001d0030485034103240c00e001c0c1e0300a100303d412903030f00746941c003124000a280c40508295400c0d00c4001010428490f410010f0600f00c03880d4204885c0d0b850018507900704070b8044826000c4441e00c00c03c07141c4409080d00168064811480c0d0308107681000d444810a094024000d0f050086280c28155a5885003202c51001d01c0300d1079002811605090000641c0b10f001600a032407020b205941e40c0e00080d58035075503080b00d40c0342a00802d01c0340c1d4021080244441c0d0050501164203421402003800c8008051030054608560082d2810443e2a0412000c03004003001140c0607194410300c00e03a5a1401c90 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 787644928 1250 787643678 787643707
    0x4091e0606020c03211b060106020c0616020d02060f0d09060c110604150209030712060c08040b0406090302070b0706020702030d0e0619020c041a010201050601090b0406081b 76
    0x4510055400d20306000425554400965a1000d010240062401c01800c43c40e5842c1c1c51642c540860b0042420019508a881003070700310803d80c180c0f04014481c650411001170300b0040001030407030003064180050004010300d6102032052036015903000d40d1100e09800403c0c5503100325024040b81500004401e143c05110307a0201c80c40b2805917008210b441c2550000b101d56400c003451f00c918690100c0b02040c0030401c0003607040f9042d401c240c001481c00c411600440e007080e102e54002030043c0c1900d1200740501c11a4018800e408166252050f0305162035a600707034070303010080c00c01f80c61180d079047c0e00000c16000304484005441c02200355521070850b4502040a0350002200b02c2c080d0288141c1158214002da02960007042c0003003c003810005180c29880c13038520354220040440c0301d0780d00466904d490781d1061101ca0b0075810100451072040030006400c0d100041d0046041011200003041011003140548042e078a251415010365140c1c0503030584001403035609400e124000141042440410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 787646178 1250 787644928 787644971
    0x71701060c11060307050a0503060f04060803040905010b070803010b0c150c07030929210c040e0601300608070b0307081006020715022b02070905040c03020d080409 72
    0x600410542d01d0400d80901c12680001d8502c040401c005001c2d01c03a40324040c1020f5a80f203407018112001c21819440001d0548481c0d5100300081d800016040c444203401d800381c20301401c2a101c02d24581801c0d951800554801485041503012021a540002a4052014030350030304103032405032900e003000c0c21030300f81c25441400d04501142503110002207080350605100303840b041e9000a0440790f545110000d030590b01c0260720301e0070b5441000843d1259036074105d400303000f4000d850665413580d082000400350098007400007030500c044101c601c0c906401e400d6142446443c8110361a800004c00b4011502a01884d000078456016285001c0b03624403d000c0614450181d82ea100b035265181c0c071038041d5102d81b260050b4801038000340c4040c800e0088038040400702094510403180740c241d480281020441014600b0b488140710340c2d1480b0399440c1e0411a4602404440307100300841e0401d80c1d43d540d41c04001d480300a02818a0658200905c85a24107170742c0100f00004e018030000902a5a0340c0c03400e8074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 787647428 1250 787646178 787646183
    0x7020f03120d0b04150303080405150a06050a0e100504021b070308090301050121060203040c0509070306030c08070501080a0c1e0203030405120307080411030f01150317130b03071701060c 82
    0x10302801c03403443d80f4090060b021241c0c2c101102c02802070540c0c07400c40e0780581c000c20a4032148078241000d00c3c3d006070003011502c02c1030015800100d40b81410200503004900d039001040d104000e0060001d1490b80603503a40450f00121b900684e200e0b81ca549a81c1e680106001100703036401101000400d10244000405881c80224020040f584e2078821904203031303500c01003035004d155080d51004000b403d980d00858100d409143c200b007000d680c42d00010a030380022105030340000d4a40ea010010050903000c40b02c007401e02c00380904070745800c00300002d11496000309511034003521821440d0149024191000c030704200100d01d006159920b01002e5540d500c00d640881c0c03503114160700b01a00742c240d0030603280144c2d580d6480481c1a115a02c2c0d451031002c0b1746200d180c1c18091a0f070200680c020074810220203803000c00006000c0c500d582000040c9080300039030203031000c00811101114010a800c800161140703030030450f85039119004100d44020212a2070401110504d0001c10500e404c500341c401007a2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 787648678 1250 787647428 787647431
    0x1a09070906030f020a0b040f142b12052b0917131d0601050903070803041211310b1c0519030e120c03060a0b130204030f0807020f03120d 60
    0x541c1d481b01005184a00d11855941c1000b051082c0300000c13241407900b815080061045170b21843e030820917002114800d1401a900e100004e0b8001044504281c485544505042c11414003004248184c10b07566002800f5419400c4480c41081c1424180d0000d440642c01030304500012042c0e8050128581c0506800d03140766013054800240d00f9041c414600c26aa4503c0415040c0e8484c0c0b0019501500110f0380203a041c0568000441e0401041000e4002043c1c070005000c0c44c0703856400e000040f030300c0550909000d540c0640f6804642000708500c4aa03102e0f01d8100c011000c60103403800c000a003092080168040c00c1d44620407102e800c40c01c1d00b842064001d000740c03682c006000245803403400483c4c90040200d410f25500c02c00798581040072801c042908003c3d2040100e400d40003a0401108417a100800c90b510250035640e810b0004010400e180c2c1444214a03040c00e5860b181004801100f008141c0c4100051100454480001d68075a1100c0a821104010049401642079801c010040601075 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 787649928 1250 787648678 787648699
    0x21c1b1e1505090103090203030c0a060b10020105010b043005011a061c0b04020c010e0318030d090b0d09020d0b010806070c0b0f04170316080a091a09070906030f02 72
    0xa14100c2241c00507110141c8405161204480064024018a4070103076890300060051820320072007030140c0240c4921600000442228007407c00c602480756020301e070f046a1419006000c2228801c00b1541515002d400e00c46202e5506c1c04075407001c5220014510030102124010000c21005410019032481d10640b08000750b03c804007845164000d0003100034240007038814483c00041e5651210140c0728024001502d40722031507050314251508009140099840018404a80c005250032805c03110000c401508401c0465040103100e10464040e1050482d4001800600c00d18550b002d0a40d03154042c1c412040091181031a400d480001d2284204a000c1c042c001201103225402e448005030b80042c01c2d00041c0c840c400f2080031501d0091086408007861101c08441c00521400344d88500c441071611221101e4062005100d41409085144080d0801c22807030000b40c81c038200b040600c0d624018000c21651000361203841c2101c6a403281181920786a0040700344100c030f000340c44056009a500c010003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 787651178 1250 787649928 787649939
    0x80c0d050a030c0516030c14030a0c0606171b0a050919050901052e0308130f0e130b04050c040509030d0e030c0c0907030209090f0a05090a021c1b1e 65
    0x42c03048540c01c1e03001700c5200d045200028090100344140500841c05104680001080c0510351751013100f003040441e2604c1c0c00b00c03040043c5130160001501c0810851078043e402d1243c05a569801c1202018540c88410300314a15501c1d0304030320724002d2100070884003060610b00c00c01d400f9000132040c04001c003414000010b810340414000d0500441034008010404401c49890b5030104041d42c5030048102c0b889840003000c5141d10024212004e05105110300c0d0500e032882a003201040341d4000e4203003500705820020100070358560008203d0700540c21120f16541d502d4550300b4180c80d51541030344146001c041c0480110004003070203218042207420464050700d80701c001c0d82c80c02469059141e60b441002032200e0390504400b1950080524200036041801e0140002c002c89011201c1c1201000400108a000021070060360f800a200c1c80c06028903c0d06500840e98030080300301c1034801412661000c200b00504000c9008984406100009095403964607012031604079200300d03801051103110101c3c5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 787652428 1250 787651178 787651187
    0x20a0314101806050907030213080109081e1b0c010315031518120c0b0a0b0f0108090c0d0506040b100608150a052205092404080c0d050a030c 62
    0x41c040d202151003035645058442d40303810200386000240551282c200060f9600e079820002d0182c14a0f07100962a02041c0e04407036a03070a8140c0c010191681003c0c1d030b900c080f4810004540c2d0321034840500000c90410940c40c10b142e4031074040b8428070241c078080050010000440c004070518402d903000d11000c0185800140854164007001d088501d45400c1c954086805511444040c180308804800c041503035242c40310504020b0403040049000142c03144100040101415030000070320f41d08014004012010a004c19007004c462070610a803000407072004a410080e480281200a1a00c01c91443c176180c86901d61206490071120b0440142c00310b005110001811016546a40e03a403060710faa807188c40c400300a994119880e040701e005580454151a10000c031040b800012141f558080d28040c0b0580444100a0241d240b0750060001107843c03c6900c401c0b04a003048064840805868030b05103180540301c0c00112035840d01c1110031100d10260042c2c05804000c541c0c0d10200000c040c1c1050569 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 787653678 1250 787652428 787652431
    0x7030806030709021e16150c18060f0806131a1509181506040e07021209010e150d02040f03050c030105011d191d0705060a02031c0e0102030109020a0314 67
    0x42d04c1c88100c0b000700d444917401019204040d0303048805480081c032525002515020040181180303900c884040700115040b65107099003d80747d0a40785545807030310300020002079802088004010903040421015540c45211032a0403aa40502b0040e221464407001a5407001c850a2801170785001c40c0030701303a803044500340c034101070018000c0300d111280120482400d2100a02c40c0c0d818011460b0241c5407a2203904c06030024044003480f40c400360900d044068a030000310742d155800e1100c20005515180d9000580390641201540c954040b201c0c0082c144005005510031000828400304000030f88142045103070317048034000c8059901c41c4101d0307018907003a16402d0040750080320b1001d003506007049805003160760000c2d0301c03440c0c80c0504500c40c00345401d40e42e100c460004660100a00504516000d100e4400280003c4403800e10744007e1040c081e44901a03e840f1036040c54100865407403031000c079002600b40e20410300c02195650384440b2024001e4106c0003240000034070380078400d00c030f041500742c003d03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 787654928 1250 787653678 787653697
    0x30706050901140f0405030f031006200d110a0206160209010608090303070c0305070210020f0c1207060302090d0b041a0612070302040e01060f0b03180d1218080703080603070902 78
    0x5005135500c1c8014050b52400280040300d40b48820401031401c400050051070003024030b00d0141480ca807500ba00201415288000000800c2142000003d0690009000d0380200103500301400e4007844212110300301a1300c202c2c0a908100001070141200c44c020720341400f568400c880f000d0503039072100c0301103621201c101e809030351507881000414644c90041020040c03481c860b01c0d2032442d004455020030307212034401300d500016034001400385400400c288420540803d044e2000c0c0000150941102c1d903a607a40d10030341050540c00241400b0750744600f280c1555241e00080d003c141340c00c0c1894038030318407503c001100c4011750f04240422541d14162020302c861b114800e00414000382150208401085403401100c1259030b40d520020742c08005011600c000d0100700c03401034036807804100c3c213007861060782c1840d9a2504407100907007460f900280105804040d00d9400944402500380ba40c4441040990240401da80858810101940301c020148127400940644100503600c035090001e902400c0b41c0e1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 787656178 1250 787654928 787654961
    0x70f0b070b040c030206070506011a0901051602010e10050a180501081906080109140c06130b0705011d1b03030c1902031002040b030f090d0819110309030706050901 72
    0x4000032460a03403025401030700030500800d5281d0351780d00040065024000859030703130308040e00400042120f450300104080503143c0b41d03850301c1c89001c00202148262000303000245071143d09542564403c5c0b64901c81c610014040c68014400840050078a801c010718a100281c40c4010b5401c201d0340000b5401d044a0041e101e5020b0343e115100c903800003410070301d80700e215150f84480006401c1c0c1c0c24001c4081c0c05000b04034140301510492030031800c00710007401d468007034041007060207940c0c03070703280f00a03021201c8454001c1d440d0a5240b03005401b50980b03c404805204654800c00707900c8a011400d80e4251003841c0912144001100030316840b80199502900e103600040c01c100503400e1142800c454191006040c0c5080d540300b01031110481e006900325a4840c0c0d0040f00300030007600f4480001d50032203d8003004103d102d00c610f000070080c01c40100345035109081c100c010546150190002000885440026600e900c1c0869410f030f0380b9000300100351985403c0c880813451811044c8118070051070444071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 787657428 1250 787656178 787656187
    0x70f0e0a050601030f02180a090b06120c070f03080603150106020d03020f0c060f0f153a082a0604170f030109140f2e0f0e09070f0b 58
    0x380d00006010090882e8103043c1c0b207200c03400b80f4994602c000e00782d60f940e9038130210558403500c050021440498001562051500d8020301556171010252000094100c0e101d141556400300d04030603600800c500100310322803400b8280e0070960050130040c4192420350031500400c94080c0550070700031003072043e10007603084071040140d0f4600c0ba400420182d42c4d4000998500a04441e1041c50141c0c21510506413107000d50922000044034843c240d0003d5280c030300c07554500800300005881c1120054603001490b0705440000d0014444007619104018030380c1d55880340c10840c1041d48950384810214990300703240c015503000e2050050990300404000300300500441d03540740d44003c1e28822020607064003070000d1010310400700b0004000d6029007810000440e0720080c192520442070005880040d803112200108801c44030044141d000d00040b10302e00c0e804d080e4030940a124200f1a6803c01860b00c1300010020440e004012102405445840102d5010980d01c2c1c1110025a22500503d01081010407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 787658678 1250 787657428 787657441
    0xc030e01030b03150f0709060f081306060513050f070507050703020f030307080d06030213021603080a02090d0f1101020c010203040b071e030c050d020304060c08032203090305070f0e 80
    0x1072008401c280d028003104d0740c414181c1c0e0400d5a0f41d00450781020b4a14449040002d50f60b400012000186628203003200703680c0300240081c00d03201c40203100180c0d043d000c3c10b400e400d11201c1d0b0401001400087c2200840071070b5038840d04041c000031648a00d0319484500843c0f81da500c624201c9040340d410502a00c1368034219800c1212031801144081e50502c0b090041602141c110750007001840074004d4005043c518500c184841c10b030210010715100762040c0301c82c41400300d0cd44100c10b0440c0d0b0528012100c0e42c2d0f5810010024041c0900d11500301ca1501c131207904101c20801c649442d40d002c3c9481ca0742030302c071f084012661007031142c04190050f0410300003000f04c1080e03040070b40540340c03003410199a44a042d500703d1025241000c8180e0000710f000300c0c500188001840400b044aa5a10166151a0500308040c204005c0440010300c8980c002001542410078414211900c4044400d602c074807030424200104400e00c03034002a1190b004a40d000126910510405012181c0c81402290b4a54511 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 787659928 1250 787658678 787658681
    0x602071b06090b0a050f0d06170d0c08090405090708030d0b240703120e1209010815091911040902041a04030b0c03041b0807060201140103170a050f0c010f0c0c030e0103 74
    0x20403103010026402e0000c0607001f02e02e4001c02c00038041c90507220b03106510310340226140a445040c090203200075441d0305800305d4108800c4450244059601243c144c4460079014a8020ba60740306d000d081c00040340c041b84040b4a6080000360317081c1144e041e04692401d031081101085000c203000440d80c1c1c02c2012000190180c14500301e43d4079840c0d40020302802c244942410032103128142c1c002c010700011406515070300480895000519120820000070204020035041c1f540078181d08a05080515480011120358000028001141d81d0b0142c5072a5101c50800107134106000e003004007a80004072808040030343d42a0340480c0e400009076038240d15a454480400e0384041c0068070340580e0000b002c200e00c1842800c1000502950005012040c03038400b009003101e8055014074401c40200004002003051a46c01078140348514203400d40e220a91201500c1c1440b500d032404008407400b040000440c40103501031205d1403008201417145464180080b1050150640000c0200e210600d40c4005544207 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 787661178 1250 787659928 787659937
    0x703080310092a23040504140709030215210702070509040b150604150e120d020c060a050417070302010e0405060117150415050a060903150b0d0602071b06090b0a05 72
    0x301d003808001d22544000b0300f11010036a130031051440c9000241080182014410100134120f4051400380c1400c1821000b8440030b80b901c401784c4600301c10304d49010403400040440b440c200e03001410400c034010304000c03001681d4045809070b016001d41c01c0001200d003007059001d40b01d140d02c000c8002d200d640b4106149602c141c83d015072a0062800d1101160405081200040301102900e90380d00c43ca510f0300c100131030028941541c460030b030003240b07160030050707000160800380903021504039841b144038800442d5a07004640c4a0302c0c030108405080c80c1c482c1404104101503a000f0b07640d2200c004090f4092006880c400d46500d40000e241c01e64070b07003035140a1000d0fa50070007113245c900c0100d103070010001020b403011408032079002c0855060070842c601c2d241120600810880c01c100c14200e18503101c041c0900380b164480c54400d616081132104030755070401e108a0039580083d085441d400c481c00e1101144030003004040c0d1100c04d805001c984180034038030040458464030f04032460b081c0081d2080ba4035410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 787662428 1250 787661178 787661261
    0x604080a080a0b090f0a11040503030406050c0c04050f0703050a0c05071b03230105060901030b0f040303061a0c010c090b19030b0607050c03100b0a06110f070308031009 74
    0x65415600c00f0316034440c500180104040c1c0f00103815400d050f80044100c43c106e0300400d105500c00c0008014980b004000e440889065040030b0341c0700da00541e1890b00302401c00700c0150f441841c00080242150075500480c0c00741106a508010076a01d520b44e4008031a40300c0c21400109500317210140029510b248501d0104400c1c100c101c121640d25a0355132481d02c80e40d2100e103009000f140301c5229250302441403e61261040b50900c51552554442a445944c040c01e110102001d00d800241414042c1c4c1007800100600301403a040864200302c00c02e8550002e14058825500300400c00d540725118000010590358402e0140385000c5101c1c40041c040928003c545041c952140c01021403030742d5103009000410700230b4002d44402c0794640f0800d410512650052500c241c504a100c2d422900c0b14803004003520f41d40c0c101071000d5070744443c4440c9042d0030034003084070900c2000c102004021100740614014028501c801514a844022440a0302e0040354154902441c558070810044205542d2588030700 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 787663678 1250 787662428 787662431
    0xf16050906180a05070e0a0f030b0c07080a0e09070c11301e070b0f2a010f0606050c03070b0601050720100c1208090c0d0b06030f0604080a080a 63
    0x3018a051142d90380012030343d406076555640c1c1001881500040c94820040040303c13034a0b4a2070a00300002d840314950f000103410041114001061100140c003210360183d0440c1c003c0791103820582e8003c0220b51982c6003d40608041e00200748581d000e401c140106641c4840e2940003400620140418500707011494801c5245842041801d80840d20348070304110303445ca01408281000d8480c03c0b541660305c200f440150b5004a5042003d0884102640c1c020401c5440e0b0903591204200019480c425015180e10302000d404105d0440340c10550181003903a0007194203110450f564001580c0c24080c8440b4000d094204001c401c0000c0c11381c09001c0c0e413100050404c103040c800c80391159841c450f04500300702c1c2414040c0400040310701e0041682800a2101d160800380840079685403420030500d00704074014002c49001042594000740314046844102074500c0352800958101780c444140e0964041d0f00900980700f62180c008000701c2c0031740c429508540d032146450380168045811400040440315045e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 787664928 1250 787663678 787663699
    0x150e0114041508040b010b0301060906180504020a051b0705011d042007060b090705070b040f0615090f050903161a040c091d07090b0d0605090d020f16050906 69
    0x10800e0400700c801c0305000d0383c8214480c5024034203003050070010380018040030028001044070507404a8500c09640451800d007034000348011990b400843c95800241d40b05002094070710f681580712000d01101c84c4000d1207030416145020348032f0303101c055070b005039800600320502c040b00c00701c0d003c02000004031009e000000c1240381001c4041c2c651741c801c005402c141000142001c1805154003c44500400c100e80d130010501b4254006005072003402c6004094030b01c000b0014013031101505d10200841d420400c10b22800d8055003059100394454043c2001c443d141402811501510b4881c00f889155202e00440c1340058aa15604409c40c038442c044901d4606c1240705030024041030300c041c1c0150704c2030321903105182c01c1c2000c070304c20743c0c212640203c3c0207244800c3c180e54404c000602c0000300e48101400080c0c900c2008003140c04642c8444000e00028201000d100b800d11001440e14140d101070340c04d072070403910181c8149440e841500031402c0e8011081000340305528242440582015004240c00c442 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 787666178 1250 787664928 787664939
    0x1107090204080a0b070816210e070614070f020402090d1a0709080303070206152e0206060603010b0301180e16031b0806010b03070504080a110109150e011404 69
    0x3a07901c150050800740e0404144803003004443c114064110495051104043c074089500c2d0320f14002c040f2403141080b40c0d8503840f8603030600e1240601c903120380c25131083c0310211141800c16680d5540d0300c2090005501424a82400240380f41655015503000004084020071602040007941094028582c00b0b03c07071040520004040d55188000402407014462107807402e204064514441640951314580041003001002580420042da00240343c0b5821240296041c0200e50715102490345000d0000110030744494180e180508018800c000e6402c4600954800b0240310050100384110940820288014004d581540d000214604280302d000981c41c0b05999880b441c0c15400c0b800c3c40e1001d07200d40c0b0180280034035080c03502ea0000c1c0010f800c004880c80c200d040c0303565803814030910780703000400f002294029100390100c0d0001c280c8002120044925401c01004c1f1254864106020132a008000600a02c1a405600c2d0500291300c4600343d0301c900c1c00c0103448004c40280310041c4d04c881040007294 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 787667428 1250 787666178 787666181
    0xf030f180b18100c0605010914040320030a03091202010902010507170702060f030a11030c0a0311070b01080607020607030b0906010f0e040f09050f0714060a122904050108030a110709 80
    0x2802a5241d41c4c100740c40c400f5043c0340c000c5601c1a00290340c0241421414040500190300854101d545450020b030991240b90b400e80c4401461004000e00d4000000c860703264547c103802980405011360f04800000c0800744040c2e0803502941e5009022031001d1110744003250312480701380c65003040440d03841c0c0351032031950014242d0741c0010003805d081c003008001d208240c4040e1003402c60340c09080c42c08500c8e40c20409200300042c01842c8030041055101c07200c00c51140e0442c804c3c1c401c22644069100d0440d42c682d0913507620b41c00708070b44150052041000180301244070f0302a1545283c2c011b001203031039894643c0110f0310b000c03201100105125414921a105031124414010000001900001e01e00b00ba4035010b0306000c0490a030b46240d0b4030a160901100707400007141101d1110403100c1a81c0c51120190030780d5241c521640312042a0b141900c40350142d00100745882103500301440000c00e0091403c10001250b40a010f4182e140c0c2c4140003040025010310100300d400681c1400b08d0701100d40c1c42a1080 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 787668678 1250 787667428 787667449
    0x207050a12150911040f110d050603300a0e0a0e060a140a0603021b01050a05060906030328030e1f0b18060607110301090f030f180b18 59
    0x516a2200001000c00c0c00030b0414120074000b040d10080c0303c01111900c60500c0da10b02d00710310600c100c0c0e980d01e0078084803910313500400300380c0c020780c140700d40340d2020710b05c41401404116030050203402418102c440407400c10040c88200540001031119840301c03085046c1071178021114840070f000d086244c94809a8441481c4c00090466041c068890b14100d4180113400300c0f10703030081d101001e800e600b0300313410341c0ea02c166142503940c14500161915103140a02c0c9180000c41c1b1800e8043d440e00c0d092252002440c1c000e0341c4a081c00340c4000c90360351920003d02d03540380702d0000400400481d810115200c00c03203502254028402500e0041038101e0002c800c030b810680511030b48980001c080004803862443c6000701d0380300c1d075022100c20500b03000741290310203440c80c0180654414400050b10800300141d104001c0e88003c0040c008115611052400300140c180500d03003507001c5048664044030740ca01c9002410a0b02e1441c3c14822801c40c0740c0f407440e51a6402010146030380b50b000700503c1c8641e0f03c0b411080b0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 787669928 1250 787668678 787668689
    0xb0112051203011206020a170f0103110a08250e0c07030314090a0b1008100218010906021230150405011d06030f2e06051005030901090b01061706030613080304030207050a 75
    0x804154591300d807880c00140cc01c2481c0d406032201da070040003422008580b00c0400b0f601c640e107440003003002c84245a1403000c1c07a08407c6d880c41d51201440304c0c4228401c043d08503140b00380c90410240036500d03020411018204c0300118650b0000d41c2850000351041291340e00940504442e502040d1240002401e10700b02001030108907030701080c0224118100340c025000300f00c00f030800c0926a410610000c3d25078800c00441d10458400254246030350740c0703480c07502c0c0c0c00814591080d650a045501d0008081c50155400d0030010b00d0005401110300c0d0501c41c5c00c0c1240c07441d0000c1c1c1e0085c198401e1500310014028a0258540100c117180402d0b402c052203a8660004250a69041c072a402084404280c2d00c01803c00d04042c0b07006014405a1591600d05405c81e403103040160b103d035a640c404601400e4052401080c2c0340c140030001601c240c0045407031050030144200400790350f42d07800500d035940380219042511280c0401d00c25010400c91001150402c0c040c1c070654880d10f4450300411042801c40e0b012 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 787671178 1250 787669928 787669951
    0x190c0b36150c03040506180313030f02010f141b010f0c08010e100e06040e0319020c04180c030f21020601050a08030a020a1e0b0112051203011206020a17 67
    0x64000000000d1000d980c0840380110076415030901d17880e49992104020007849003403001c92035906814000f0030555800300b00c2c02c49902441601c9140c040320459481c881240803405414568234110b01410508c01c520800d0090941020348620003686440c021440050280d5641d02a80180340014007407030b105ea0403140c40703000f0307254501120103c40c2900284040c0500360320b076000740038400340d03001019046001103034046410001401c440c0d04500c81d0380061a81101005a101000b68011814007410300c402c6400700407000c0c840c1c803018405640300307034020040e0390a45c0f4140700248075214000c5880d40100b00c0750010001189030340340001140800c40001d60700c1100100490720f00070710382c403014001c404090342c1031024501c0c0207951113100c458010039400c1d1f40e82c41440c06100c91030402d051150807400898040d65039610f2854800310f00c10080d5418015003860001115070031302144c3c100c9110760b41100e0740c148603072158402900400e00c58000c01002c45c6011548400e041c039045e00688280f0320 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 787672428 1250 787671178 787671193
    0xd05090706081b0304030320070c080d03020a02030301030210030e10020910092601380609010c1401020d0c03150504110d02030a0e0a0503190c0b36 65
    0x10b419544010900840386a0310400703240003a01c000140c0e0b401c50307454107000c40c03c4243c000c03401000c01c03a0181486c180b43c402107503c90501c050710b03242c20101c031200425601100340480044041c3e01c035280004e030169200b04010401410007244d403030b00b00600c42c980000c0f80701c01800381c01e041c801c65595626029401040c840454034040c0c640c041c1054883c00e00d40d5039a07143c00c0700d0030b010001d80b295050420781ca2103403400c420b08082d0800c8030340e80c0100c071005661541041000102907862002800c00d0055501d545201d4106201142c0c54000d050319000d140d0f544566a5180d0020307070031040c034451b540a100d4064182054010980e03200099100419401b006c5c0364803189201c55640198811401c0211141c45401107000b12000b1052008001d42c1c3c80e0707180300103440940110825421f43e40701d80100403052082c00f1000d4001851303059000c0100702c6030355200700c9500403e04c00140540c0080030108103a5006007a18040da145030f170000002c0d00080005c00034001c005d2141c01c10082d0007848 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 787673678 1250 787672428 787672439
    0xf13060209063010121104200c2815090525051912080f0304080703030f110d0b060403021216080c0f0103020c100539070f02221a03010b0d080f0d050907 67
    0x210313188002070b160a403524104002b007518500b204285001812010a002c81c245504695410401d2419040400c4802180c0361590801800110700010004200d0b00400811036182c02c910713a9012400000b89140500c2c10303c0781c0b603101142e40200484000104002038008801d612014510450182005640314a45030801409481e08034840d8103801d45003500c1c00384090320420a58404101403070300050b000c96a4004541107209a81002c0d621000301c003411a805075000a40f082e0f215a2541100308480d5111009952a00e052050303981c0480741403201146540300c0e50140000c1c2600390116808005101603100c1100c3c02034801115a17124071100710340030f00741070071a140c0b8580c1c0182101d07030301c100c56070311480b690261800061182582000d044155550114451062100807223a0400039030f2031001c2034000c0c4420301031301d903802c0202003800381146030612409500362006807000d05a0f00056842c1c0fa03881c0d00160181442c0d50040c8000720400c081846581e1082180b90014170b405030805 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 787674928 1250 787673678 787673683
    0x2090111011b1d1f0219050d05030c0f0307020d03060b040f0b09030a1203051e04050d081807030f0501050f13060209063010121104200c 60
    0x14000c031031142e05128201061080c0c0c5041030080c240d451501c2484290100b48070301044103910f04031588280c04200811400d4094080c0140c841c40580844900c4c001ba4111061039024443c070192032038006806940d1030704d000c2c3c0002d41e8041c2d400171000c0c1c502504600c03644007076007040e2607800069200007981001340c0c2c1c040c41100041d02d980b04d14a402d00c2e241c440144d00e14082c0780120401d0020224040d611902c0c200400c0140b03a50040700d0702881501010001d00030841216441100c0011039403011960107545502400349410901811608595050030f440f200f4014000290007059074180540704001804440055885042a1000ca4101c2d040c01c03429100090095414880c0e000184124102081e00e081c10440e0301030300268a0700c20401c00140e050060406d1000c01d00358100103910000d130b69a0b078040020131038003000752007602c45184815100e000c1d0b01801003a0354041c4200000f0031404241d04942c808010804141101146c0742c040c0540400c140c016042d220109250b86800d80a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 787676178 1250 787674928 787674947
    0x60d021605060718051207031e03091409270f0c0406080c0d030c030306050d0c05180402060d0b040612060219050a090909050a020a0e0a060911030619150201020901 72
    0x10340b034210203504810113013180364103580c07240511a12042c01070602841042c0288802541c00c8480100c403040c2c919035096901000110440021f64402d0b80032400d685030028038000b002d4050700201095899082a0206501100101a0518003104021b54501d410482100008000c2d0f011380002c1d03a4070800e02c0140c1e48142c1100456400951441206803521042031001c80c0d0580b40402a008850a0a0340200416080103400002c1034642d42d040c45000c08202c0112581a14490301c2118403000a1241c440c0c182c0d00258045410420b840003c5c5043e042043d03107442c01040000d01a90f41d014641e101c07010014125005500400c0000762110ae0001c1c1502c50314040c00c00720b10f40245024000c1071a1824040c0710381940e544da541d0410b2000401000052550240080840503214014001d20a004450482c03a01d803c084000c20000c043c0c1c050b01702c50300c80840344035065490307803c00c000000090481002a24600714400143c0c251404440d9070307060141e40005960703054403400100072856 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 787677428 1250 787676178 787676191
    0x2030a21050909060607140304060807090b3a0e010f0606170613060503010c0905030609030a08040b060114030c03010518071e030f060906090605040e0601030b06060d02160506 77
    0x50a0000b010320f0b80390105281c0d80207800f140d032544d803600d8502c0c01107008014a41c64a08074030002c1004120160040f221900490765619118402c0c0d540d40c001c803500f449180c4211000c01540e4101400d0b80c804d106404440090640b000c0e614040d0179510007040303a096141e601d400b82e4462070842c8010313040344108000f401c5075203024803001c494a815541000005082c03c1d00681058a039020b002031264080c6c0084d08006000780101c2d110400c0051600100e406010301c24084e500120391850000402c4910b540c800381c4408403640d4850f210500d10503001000c1d2418800300080000005400500451156444000d840e4a0b035040c201444084000e48484800340b0514006210143d034000c1002b459461070f8030701c1e079008504000021005011259100c000090916001046c0210b05420680c02d4540725042042000ea60f0310070001592800131041402c1d801c4240148045070080c203072035520a01c050010b9162205c1c40c0fa0b14003c0307a00400742100c9a5450038400010040305000d4a600a80b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 787678678 1250 787677428 787677437
    0xc12030f0d32070503040203070306061710020406021b030307061409011518051e1009050606040303050a2a060c27150e0607140d0f090504020d0902030a21 68
    0x54814081d001c0d0b50b0b0043c207458207110010000500315907003000f250700030b540e10810510442da175400e040d003048040c040b140c441e1400f84098403101e1504130310a5900312250381c1e0050829410b00a16152503c1403410300541500003041b0501c007149450282d1914002c002540c540d06240c0000c5942c00c40d50413855200e4484070100040000084030235440d1100070304201b000419483c4e00412401104c0e014241064002d148400c00001081d00c15914084418030b690a10542ea01c0100b04401e921880c000100882e01c20700c5107001031886036641500320174030030881c8440030403c0c02030b00e4900d03001074808070750860301d54507103041d1140e00120002c00f280c03800d0b03420748102c05400b10101c14662a80528110b04203452002c1607407038481c640309a0640d0000d0b01f00c0c0e6440b140c03424030711442d071907201c000442c92103038000c1c060b032492003a00068607400c0941d8800c0f6109060608100c0650302030382d00000f5542d16402c01e0400750303074184a1901214459503801804100020314a081114a8007402c400d20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 787679928 1250 787678678 787678751
    0xd060f0f080c100809010b1201020a0e010804120311040b0c0a0c09050f01030611040e151c05030d110d020a08010501030b06042105010e030c0109051e0c12030f0d 71
    0x80d1150201c41150b08200c4c10011800d0b624218914010525501c0c0258008415080103450b018107500131300069245a83e0090004003e038010b42d2100700541d8001c3c6100c0c3c0440c0807101b000c6c400d5005940c4d0301512400145413a6464041c9012500180c603003808030f422001410b000c10245030a02001000b0b048014041c2d4a08840c0c0454113040500c805001144c0740c036217103851040600c040340c0140c1480001031040d0b042c001100380070017595400d814041e4650400c0000c000040010351049650301400031031070244000201c1000e01803a040340703c05500c1c24000c040001c100350018250320304c02a59820000d40c9058001001d640c10080003601030b80c41048244010710742c1c10503081d40c41e001d0150040a0b40c2c5035142c0a4010060903504a286000109d1000a03549040d04110410740c041c5046608501b8041c141034410703082d040700c040c0036510030304801031039003081451080105100003d403030520098400c0d10b00c05030320003030740050308640d2012100e941d5018a81841005d88280d604412035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 787681178 1250 787679928 787679953
    0x17180601140f0d0303181b090204150f09030c030b040b060f03030f030c07080403081b03090109150e221b020622051504030f021b10050d060f0f08 64
    0x420100a20070760003001d4200652040c18061b412500b4071441044507007986010a007010400100440742c00c0d84112000d040002d40344850b4025a01500d0742064034803152400c030141502d9074140c003034049052080e84040000803072401003040000f1801052012030030302c1c1518004400c090010700c014800c80303064000034502d4900000303681c604554001104e40d00d440d5000c00202c14014400c00410381d5000050100c100b04000380036180300305c600c5500a6005003200403007900c03801400c080e00d0025001500402c072842d00071110b9217048005003450f051607581c3c43c02250385c8100c03200e521854688114603481130f581d09071107148000d5482d48030b10b0070010f03030100000b9140c403000341040d9540c12000400d240d211000c040c0b0132440540c0f0008a40c80d03da0721800302400c0c0882190254049070f885409217032042c0c00800e1a46000c0c0e20b003020001070034910001c0015200c1c1e0300f40d226042100504c0941d00e003071058400d04c0080c000c00f00444001504e003408107200300702c10303070070000c001d4011046131000c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 787682428 1250 787681178 787681189
    0x4030e0d0b060d050c06070c0f0801020403080f09010c020d0302010b190b18120a060606080f04020d030302030a020d1a0307050a0e070818060709240c0209071718060114 74
    0x100000e040b43c1d0003401c24400d08081d45816421036a0701e42c030800000b941c03020002501d50100440b500c040c2820101303039903105414200d0050340300240041c03004004004015490300b000301000507050502d40083c00312500402c80c1003030354110031400750790341d10002c28091034200c140500480c1103106481000313081030710825590080703e02012103800c00030040e007026500c9941c907000841066088500303542080c00c2c42c502500c118400d41380810600400b148101603040c3c0c19910071500a0201c5040b490070b680c0444c001e40c00105580c68256090108d40000d260a009640c0c42c5c0080c100c1500482c8070340420103003010190b80c0440d00c5001d20100420914802d0202c0036400030003400c201c01369648102c0c0100c100000d000d00c00699024071030800c5036080d0480020829075038490754000d9481c69414040f1004040300d040740e00410a440d40c103800519020b224a5445032040c42c1544101648000c00350482c01c099500800e210708041d11800b40c450100b104500514030346462410181042d0701044 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 787683678 1250 787682428 787682431
    0x6030705011b03020708030d060e0705270a21060606030e0607030b150705010f0b010e13091419120e0a051002160b0904140106142d0304030e0d0b 64
    0x409000200b40c81e54103241c001d000d041d0040c4250001d0b60340c0c0e1a61141c000008102e01c0c06120014401a4041290700348036500703480c2000c0d40c0105e1000d103031300102c2e04100e10507a8105c40e00e5015a440a010900c000c14024155802c029540c001155040520340714055840d180c2010042500e050b809002c0a18001a07407604040c25080016202c00703501c002ca134443d4003003407030f05c1c124113400100340041010552002d5105c0c235040b00d00304100d20700080112405800e40f060241c0c0540381c2c1a200300303200400c6c3d201c50440ca128a03ca8056034860200d0142014051404084a03003242c4800301d051280e1550702c80d00d2944245060b5145200030b000041d00c0e00410b0241038020021a540410050300030010010222000b2007600074050365900001030981c80b09146038010343c208100f807851040701030f000c14161907254885c201c6142048038002c1094206c2e44140d40541102c044500f17454114080030014000c614008070b07964902418050b07c2e0040b201907450007100b00c2c1c03a115020401210200c0d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 787684928 1250 787683678 787683707
    0x4104061214130c0b120108010b010f0207060e12070609182705100501030b1518010e100308070302030904140603150717090307030f0512070c020a0801090b040b0603070501 75
    0x50800c030b0080d041440074901c460f0030505030128001402a40304203061040740c1201c084100074851454800011a814940c03400040013503070042200b80141401410b00d00c00e140c01c0a03001c9403020101000b01858821903500850208400390014821a01071114404045510303040c203120044802c0a40c0340c00c003440714004d40c8841032050018003004070030f01400008590015052000d5612802c180c00e6800054034803440c411002d105100c071504156094181c480801c091055260f0718085d910400705400070100c00d5144054407000c4005507003003003d0200207019600454651080c0c0cbc01340002c031061407800c1c8500030407607410084142e600107502d1002200f1071000420b40d40f0f8045041e01e1a24011312814500b41c2d1441c201308503c68008044c01d08903003e59107413650b0700e420f8041500c8900c10300418144004500f030009400340c0c000d0221554032132020344042d070030650361121a400c5945a0b5000c40e41d07100050103110900c01c0452030140c114104a0150100528210000c0c04455101110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 787686178 1250 787684928 787684951
    0x40c050402030c040e100501022415030c0a06091a1c0b12030c0a02280e040203070e16031a0607032601030b160e014104061214 56
    0x3e01038000071000c0e02c1c010000300c4441c0c400c604003402080322003842401510300510510081d907481e0348014140c2c2078400e418000e42980e90302d03988140c051a083d450100c84d094461030b10346408545940400320000c0c0803558550704100c9c1400104550040c41d0039090040100900000707a084811038000285201c0a50740010f2824007640030030310814540e0314511490001084142940030080b40e041215842260070f862203030b052482800c425503014408203145081c0e840b052251030207182d03440c0c0d001030009003120540c80c2e03114032a00180900b00ca0002c60450080c403458142c981601800714a007181c0800284003170400720204803940106c0d40c0c09810002c450200840c0383c0d8581d0158004003010001d0b9885a41e16418400d10760031065440a1014422079010a111481007404044044059603003003550036020b0341c8558080f050203412003c100d402c00d01c00701c7c0350242a140c842c03c07207084101d29896a250000240035907401d100640102d505020305202071f0410758140580c441c0b01d001d40c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 787687428 1250 787686178 787686181
    0xc03070c0b030c03190e07080d0311040e0402280603063303110705160513061208030a020903010c020d1d090a09031701060c020906010f1403090c03070b04030b0f040c05040203 77
    0x40e1708050100f4080408543c0103400c000b05100c1404110710003210613136101403060300d418000300d00c0c0b9445544079110085811b000480c005140040129409000f009441c40049122440e1800c103000d8640c004408603940b00e90030020080c100003051001c803107200d8040440006c10300d0403541408039407860340030181d803224001324123140001514070070786c0c0042c202c1e801c8040c07800214400130010702803144241040b007964000c0c04003d008039001c1e279081d481c141e41d0240c00b9a40c1c81d40641c002904c80890207409001c4001c89440910546e00c1825065006241c00a00100b000d8a060025881c068111400b000d81c041c00d0b0b1141e0040540003078005400050f25242ca060454a019104000300c81c0c840d108000080d031280d00c01584c07a4807034000c0340d10a4090710703840700540d4030300c20480400010901d00c0e103149000d90046006580e00003001000d0342c0003149075000280c1400c009801c12001c0100c0030030140b0901c101c114499a20113141580e1015508043d01c903004403440310310545d84910340010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 787688678 1250 787687428 787687471
    0x20703030f050f0d05060f0316060e060d051e07050a0e06030a0627060b0304030c1511040e090f0a0b0f041509110f03010b01140c120c03070c0b030c03 66
    0xc08441e01440b030043c1c02c0d9143d80129030301101420054444c144103040130b02c4035004c103140120310b1513009010701240112041c54400709590a8020100f05a40a00c040c40102c29501039030180502c9060700901c040381d1104035004105c07200340d002d0065400c0001c00d200541445800c0426600a00c0084441503181d0760342d00260009001c02d600240384064040c00b120030101c054418004003c56000400c0c40304030b0b1106614943c5020840e4041c0004044140d5031010070805502074101110544010401340c002c0034040ca2580e10540c40195104064010030083c2d04080c44009458500607001c1d100d07441081e00c603120144030261a149100303000c1307000300f810440301840c1c14107005041c00c420301c014889400d003502c440b5850312145c2e000da075070400d2050741490107109621a1040c140c45050321a4481c010310049074001084004984c0b0074110026240400040a0b08503003203404001c41c0e980c6542c3c0b8007054002c6a541c45104080e5041c01800119200c000c2030780e500c2000807686204550509 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 787689928 1250 787688678 787688687
    0xf01031107050106061d03061e0a0b030111040f1e0b0a030e0a03170f06010f0f2c0a09050f04020d0f02100504140604140108100f090504060b03030703020703030f 71
    0x7000200950b103499800100306400c031510815038005100d100d141600b0b17031001c0c1601c070b10701194040a8034100f00700301e200b41c442404803607030841352031200062140000f801003070855000e540d030400c1070080440c081012001c6038541c00050405108260909a6510112403001d1600d00854540b214003040a0509901c42d034000f40c4824203e0381210f91a441c030b41030290030f0584810403010005ea00200042c0d0b8810691541c601075201a541c402084290110481d402d00c8031a0340b007810031040020360f1143c08106942c8050000e00a0000280c644a8008108101c11241c0c40130800e14104010000502c3c0c8401103268480d40540c0d001c0302c80c241900d042d401c800d102c40d4000703610902d1280e5002c06150f0000c09002960007500d80340082c08400320400106004620038920141511034101669500c07500301550071400c1c4048111040d0344411404840c040d540c1c100701060742e5100c04000500280e40150b6044840c244e0146143c900c0340e4030000e446008600010381800303e005660100980306 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 787691178 1250 787689928 787689937
    0x503030a2001150e0711250815010f0e040c180b0909060702011503020f191a0a08071715030f030a090305060708070c060522030201140f060f010311 65
    0xc0740020850104440c0745840c0707140701c0e4042c03024580f00398400111454001e410b60340f043c07100c1038001d1119072000c0254076400360040704181060712001d40000303091382080058209007030010200d1401581050540c0007030507516800401d02d90155428080450350000d26882511043c80c0140c00d015880182c840203440c0880003640c01240c010100200e054000c50103501840701703580244080343c2036060b803085c01411070001130361040c2814584085881e12104041d00081c01d0a0120405903803024020700040130311b0342c81c204c008000215020b989074400c1d142903020120342032071940f82088045220b0100802014840c1c24008810144040e980402081c0070856030601125541e06400030001e00f54109403104680303a12071075001c1751000e40150f102c244220031645c2e038001402070b65269a40078044c0900705886002e407a102412403840c07000d4084403294000e800125005452810700e005050006010601540d4070703105000450b601c9a5401d5410042480c0100c0d0304071428180b01c405226 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 787692428 1250 787691178 787691237
    0x90203070518060a050301021c0209180709062d0f0e151804020a0f0c110d081914041806051c021206131e0b0711010605010203040503030a 61
    0x20310500c01d5400d02100315405116040a071360351942d00d503603170041c14281d00a0550340c40042d14440908842814144d0203043c0009004200d00c4403041d424031440e000c2c49043c1c50030000181001c005104050f006007500442040c1c0f00014900b941084002c01035100d0048a2a0204a0b000e810309010790301c5402800c10742c140083c0042c00d0b0403c5210100915400700b111041640c18400207541c0500c1e2030b100355004400180c8a014070b010205d00110380200120b007003240c0008600c241d00d001903c074913107a80c1c01c041c81040829550751021030800e88052441041d6000c102694410000700c0840300b0070340d0101d0718a4a004000e03560800000000782c1203c0c0c20041d00180d0b202d81c5498103040404001013524000e80e0075610788500c140125807a0403080303440351012402041c000000030000d100040300744113040c100c07140c818842e9450b40a102c00c166506400628024041e41a00d402841080e005140c00d0005510b02442d010110b0740f81e01501c45d8050502c102c0041c103500c00034888000071309050 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 787693678 1250 787692428 787692439
    0x30c0609060907142d0103061d010e060a03120e2e0503090111160303060b28051b010f0b030a0c0306020a02070305030a1e141603110106030302010b1212030a0902030705 74
    0x240300458000d2000a507024040c002030a0000000c1c20540e04500e02c271070303404042016100c613030a2030690843c1400c081d044d00d80040e41c03004008007203884003100c0001c84038140d90303403550707407095204200044050b6002400b45117051000644800341680d82030700c00000e1428055225a903505440c0d00416030001418402a000900c0840e145a0701c1800110706100340c40030840c1d540c603040c40c44043c2c094200f40c4e817102c203000140c0c075145042c03120040c036980400341b500901e81040f170464842d800e00c01015526150391120120010b00880d030050404424095000304524021a200c400025031a032001074401ca5001031810401031090113403402851300042104e94803214203500810110b009100c0042c0012007c0705020481d00c51241d07070441c0701103991301c0b42c28904d4110070788400d80403041d012014400c0703803d28045000030038041c1800842c02038000040d8a050642440261040c01d240f0b00302d91f80141004030760f42001c3c40d003540c0e00320b031400500280143c11840400e14100d9160840d95001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 787694928 1250 787693678 787693729
    0x40210090f2d0b030106030f0605060f090f0306060d02060d0b090910060f0f051003240305071401090e18011b1115280e030c060906090714 61
    0x282688500040012440b901d0a10240c00950700c04180340c5071800356200e80c2c001000100180c9100780c100e806c004c1105400040c86070780c1c0300b0004260f0341c001504c40c1401000840c11078410714207c240c5108640040d4090310840c58014005084c00c00c0340c07a0020f1040300c01062025403241243d02003031074454090203003025410100a003d54910758502003d124606017003000c1080244100c80c002203420718005a80a9820030040142c20400d9640c0750301010794610030034100d403221800c6c0868404100c50880d8085085007040c074200b03609604030250904100708111b8590b40d018100303208a65840004141c25160000955007048140080740115802d00425110f43e41ba4040b03850030724003194481c0450a60a40103090712113162105445036240310030000303002400f5500601e20000d05100c100000c0041c10050030040b15070030003400d0045d900109000250010400c0860b4201c9000b90040c0254540414069600d006c0c40c02042070003054900d403015961200705503400100081905144030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 787696178 1250 787694928 787694939
    0x5010305032a0316081c0e0c0303070b0a15090504050d08090a030801032307031a060d050c040b1c11030706053915070323040210090f 59
    0x100c1c0c02c0510150603441e400301482c0c803481c0b9418a060b090700128000386040a080144074008158024000d4969600420035107511503080981100345580c000400202d400d045d0656500c4d1000a409680c007a900421010007c0345284404a0b0702400c400c0000c1070300400c440c20302c080c00e50760b079100d44d03a16401c003024031082101c08107064151584541e2130045a40c1c400d80e119540301548000500800e25107001070000c2440601003072401454a00e4001180d200c0c194040c4c0303406d6007035000780c9123511400141261151303414440c9410000403951300c2c0d52000b040d00c4244d2103400c4c2d1150f039840360f40d40b100028941e44444003641d410145070440c45060700900d05118480c8148260580d01c64083d514011842c140124183d840b500e8080e120300c6d4900218996a05440e46905001c42c601d0201030340c000480784041021040100340940d00c1c12503400c00d200003030140e800c0701400782d0191b4000c030600c0c103042c43e01183c00c82c0e00a4048038a0f500700f04003800281c2d5840f5a980040c0c10100c01c20300042031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 787697428 1250 787696178 787696183
    0x90a05060307030905061b2d04060801080105010905040507140d02040f0b01090501021b04051005210615090c0703170a14090601031223130312030509031e0d05010305 73
    0xe9140104140c0700c4540c0d550000800108042c244c00c41001001d0041740883e20000008c0c1203d50405005401102c14020102d903903604264001c40002310343d1b00040c041c00780c0a00540380140703078950081c41942081e94409450f030a8501132850b96050008503001181d9917016001a0341c0d802900400600c0820080ca80103400391000c511701103481d040c40000e1035440091038000e03d69101c501980301006000c204005008082c00003031020710060030201b0995140c14840c9420004251b02c82c843c0d0b41d1603408907040460042c82ca811a01000c1c80e001c40c1d60b1203400700c4580c8842203000c00ca0b52112070f032038165039008c24407070041c0c11444824200202d10f011036101d6480c03854000d51a4071503603244101e40b40d44503400d0000410101045420340c00310390161120005112102050110304522948000d0359500480b42900c0c8550b15050200188429490070380417180d29881d040c01986483c00401e640d0b8440c07503602ca40040c0c2a584250307102c0c41d4480580c2c0c0391284082c014005940e4a0603c03c0d03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 787698678 1250 787697428 787697441
    0x6050901090f2009040b180c03090708061017011506020714120a020405130f0507030201140a2003120f040605060d0c060e01170f0a0609020f040902090a0506030703 72
    0x3141e03180060300c0940007011241140800c1c42c100d00e035407030130054000340300103402e03c800440e4206882043c600244445102c100f80301d0440d262400c0d440b440c0036007804d8600ac0e45d5502c01e080d21340050044c800102c103180f10500030366235424030100000741407041c603c0c0103200098020400303821001c004110305a0108031071044800d0207001050310105030b410003100341300025040c9030680c85250650010308060b0842680840070f0114581c00f0341298a070780601401c5a4411101a0040c00080c411907812030f0385542d5072440315004c1c1d42070982c007100107402c101183d40c07071000d03090000185201080e402c0044503002860483d1341141420400f40480c07191006071011100030303040100041c5141004c1005070740554100010343c03a40c0707280180648600c07952842e641d04114008144441d0140e5151826025125130b400c820b4540c502146030104440040e007007200ca8900400c06100e02682220582382500d881040050b41c3c0c403022400110408440c1e0b110640044010080012540d0542d1014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 787699928 1250 787698678 787698701
    0x21305180106020f0304060912030c1703040510050c1e090a08010e0d0509030d0528020c10030501050a031e0b0906160c0305030406020d0603051c120e0c12010605090109 74
    0x7504c8500400010710b440b4000c0e0300420001a44050080201b00000703140c0c0300c1020300900f82801701804944548600440300c111105150700000b003480308004080023180c08581c8008020400c604008000800d00d21450221000244d5080310700403541000004840c3d03c240c0042001111658400c0b60790f000c2d00d4845124040c1e401010408100f841c0103004403004541c00401804004440d043d00703070b81a030000581ca05000f201104140c1340d915022442e95180c070070a1700101400b4588200700126404c1843c1a84209410200104020b403104801c032030940e60311410713800c00c000c001460b120f2010a85200503109220344814004403040207d00075000d208080c03140c2801d40d4804400b500c01c1d03421190000c3c0020800c10010340030640c107502034000e0898540010941c90f9407602d490b4688a20094000305d0524400c400301d200640100588441c80080c0c9418040010007045081e114a0700a8100d0300900c181664529540000e5201202400000b41000da4039615582548010204020003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 787701178 1250 787699928 787699933
    0xe0406141e0c1317030712050d0c2307060e0303130209010b1201060c0f0501050a0606090e010b0a030e07081221060a260102040306020304052e02130518010602 70
    0xc90400c00c1400c00b00d501041890716020205490320140a8140703c00c20355404c000c1c0400d1241c10000ba86012401c905e1640b02d076102500c41000300d00400403908075051403418000212400c1503491600c521110301156854170340358a404c4d10382400300290411002500f41c0b4080041000070032186000e0b9440405c4c0203582100090b030704c82304420180e1103241001000c01c0302400c01002114400d0001d100020b100b0f450403511000705548480c25241c041d500036540310f45891061180c0c0398448041002000751003c0d40d4565454150040e005200da42e07115002c05440f00007000e40a4400c0010000401c00d8004030b0b840d491034200d1070030a07600400c2c1080070480340d4101c440081078107020824003c240040c07011240780d14203009002c2c00360100184195810400b61041d034149003e00c041c1c40118050b00003da520300d090b02e00746091900d445040c00f60b100544010702c115000b441c419082c070109003200140d40750000080e020ba4401c030ba600050303122900c1c0070a001100c00703010310030b41200e026408 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 787702428 1250 787701178 787701181
    0x10f0501091515020606210109030806040c18091815051f0e060918031201031209060818010b220c1b080d1d03041a0307090e0406141e 59
    0x1000708100d00f082401c0040c2c0c40070001c160380307190040701e51a4003010740b50255515052102d407a800c1d50b02072301d025008220302c04104007441c2480d0082e09034024143c0b606c1040c2030f0070300490f011041d52602540c1c912558681d04c40c0120f01d005001d641d040d83e008804425903035140d034102000380508441180b440c8543c46d5200740d0b102c0c0b40b07500790010f0311910642e1000903924031092009126005001c81d07070b042024800301e038003058280000c04012003000100209903043d82000c42c803003c0d201416804208000c64100070036580204032581080104a1001c00380c452118494050080c50004e2640311040403601260220904a21b0007400702c440c10a1001908808050340d620002d88501b07880c5810070b507141c8000806060040aa0a011460024404100e403010424a0001400004e0181d20005042c000036006c000302021035015089810318600d0b003401c00804c0990603214541c030201181020900300141508420150f10300c20084640307a181c111000c0c2a00a100a0040ca80840510 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 787703678 1250 787702428 787702439
    0x9020a0305160e0c040302040203090a060c0905210c0918010c030c08060d020105180d0c08030405090a02281106040b011508010302030312040309030b010807091d0c040b03010f05010915 81
    0x240c0f00d1103405441181c2c0c0c2800c0c0b5580074000690710050000069002d0700500c02e00142c02403094400d1040300340d440001c0c40703040c13105100320380d05e0000c070303015800d0503007108060100c0001404010441b002e85101031540c941008608507803440b00c0c000e070702c2c82d42003040a25025174540d002c900030401d0f555504c0401c1e201c12040c89600d40712a040030340000d408201c030b136210402c041c03191200420040d10750345c1034514940f01e801d45945e907038203c40e030345800002d82003201d8039200a1203a000120b80d58114074104003a103400011441505020644101d10803d902c81180540820100c58a100081d108207107020715105032200740074001c0341c2c1c80080c00702011030300922400700395050ba54058021031030701125800114054000a008a0800061000c0440020110a500c5008103021401800c18a0810707040c1c205680000a02121661181c0c3c00c8078401030000070810f0b84460107607030001d4403141010100307016007441103204101d0340c107240001aa100d0623034041c48004042c0300c0034001c01c80c3c0385c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 787704928 1250 787703678 787703699
    0x3130905071418040b0a18020306030c0303131401111b031b0a1a0f0a02010c08150603070c17070305040915030f08090621060f1215060409020a030516 66
    0x1601c945800c0c00c11680e0b00d40f860900354410103405100a0001080030340d220055100314805101a0201c030360080280911402d00300010104100708901640c2001035020700d01d202180b4601c204401220031500350b24059008403a142200044202507800070900d0300304805c1071340382040304c00c1d00038880d52603001c0c0c061a110303040c4040d01c0c00040003204081c1ca041006400900511203d18140388104110f840011403000188601d6100d60000b0038132181000c00944080030080c5014240038190311401c0e0179682d05401c0700d90011090a0400110300f85080c001c203006050b01c2c214021090000b001000c0c190800090030890b103010a09210b40e14141c0500012002e4600c00100210800050034000898440c09800c0314070b40076281c5400e0242c21080d080b4548454211400e6409404043c0001030402101c401d1201500b51010021081c7c0b000b1000c0d034600001c03039102d095403401404102c09a4403600950040394004205500850312800c020b912240c40c06000106441c1c0514002100d0005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 787706178 1250 787704928 787704937
    0x402300715051209030405030609072103080c0a020a12050714120f07080d0204030b060f0a06050336030a02070e040809060a03090b01030809010e03030f071103031309050714 76
    0x85075600342c1002c1c4111050030303e000c0b014115400b0380c00107103c00b140d030b91001c106140c0f0845c0d054005081d0607240c0549403032158124440ca0002c0c22542c0c000d040801c0c1c12860301c3d44c000d1006148103545e02c0099108034240500410700508908001d0710800340f040c0d00c07001800156005401c500007044120102565800d85c80081d0307204107500b40545100022000c000c1c00f001d500428070945084540e0b5002c1049138025041282c0405e682d006001e81810301c40ca4803a451201600c8100c3c2460a020001d070003800002c280d5010212002c2128a60540004c260950600f0301c4107402e030102d11392625a0748a070000c0d5040801489840310000e102c07240c2420150046400200c03140ca003040101c2400900d502c0070f02000207254445c1c103220002403003a41418001c4d8001c01c04140c944170300710001011603014440107440b0354000e0100f4200d80b01c0781001c5801c02544000a28007031044600444d045005081103c180005d0380c03240040c40038400d0b004240b08640b25035030f400c0d408c6541003040283c1d020307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 787707428 1250 787706178 787706219
    0xe0a0804230904080c0f0304150e063a1a04140106080601080408040e0901060905100f050909012405040b0a0b0d0b040213030c080c040e03030f04023007 67
    0x5088003c500860840c50041c040912144151103120241d404410f166a003e903000190b4040303e1040350703510603440000030f4040320b4121441440e04106507000c3d100f10600c0c0500301001e0040c614814116400c2d040d150b012904100300038018244840c02551543c89115603082c050341c1064000354000c03028218490603940e51352183c8003d034030f50000440304020000c00440d200e510401c40800d8070958000d00e18882c3c0342080002c640682070800c141b0944501074419158507100050034002c20b0108103400d0290399060710719049568450fa110781c003407c401017446490740821340201c51280e01c0c10200034252032064030240f1940d0b100760248540700440b4801e88171a031030240407041c400c41031600101c01c2d040c0018400f40c140015841d814144407000c2e0b00840c1c03035104a8104011040341884002401c140c01c450801148040f004043c1d241c0c40010422708003000d0707500c00142190340740700718490355484400c4202040c0701880b04040b0150b40c0030404420a10480b0800501d01d54880c01041000e074 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 787708678 1250 787707428 787707439
    0x40510020f0702090108100e120d11040e07180806060d060504060e03040b0c12090a03030503090a0b161d030c04271101120603020607080d0e0a080423 66
    0x199150000003034000d154040540300c02004624050f030760350a9003e0180072100040c00da40e00750400304004a6206c9000c81c01550485032600000f40c92420580b02c3d14000300d032021aa0310441c1007110750510807900700c02c202c6401035040c00340d2198408100100080c88880034403c0c0e076151084182c0c0c03800212021640303c904024010001400ca8000d80d402c98460040450087d0681c0b10090035030700701e904030444914002c80e00d0450b64408014146008480a001c10326001c100030109505980900001d0b05000000010480b903843c00c112908519400c0081c42190381071050000015003152040c14000416182c00c48041c079581429270b40e024580140103096050340310f0309100103495039120075443da540231108031140a0100114040c83d6124480d000040c50011001400c40c456240440009030f18005007171005856074012503000681140003942c60362845403402c006049900d60708a0b460207030805030010884008043c100395026240500604181c20341002d01c04c0071461441a400b0703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 787709928 1250 787708678 787708693
    0x3021902030601030213020c060a240f1703040e0408130e0f0f07030902030a0803040302010c0c20060409020703080a0609020c0c04020a0203090a0602150a0606121d1002030a060b030405 81
    0x600c1c1011040d103850290410140c14230142071400e60414000b12001c01201c0c0e140c003614000c18030b000c00700381060301c10200b48000486c1040980c00c0f40104a0107100e800d140d11b14400e0240402c100b06540040410400d1581d103842c042c90a40e400d1b0304007400340d4000c411890408110402620070f0540300362028061071702181e5400340030691051000d002d0100f455a900017107000758030240030410303205009400f00380c0c1d02e00381031400a00b11801c00c1d864400300041101c1980018500d212825052494042255402c0d25240000b556034842d950051042e288006070b10b00c101034000760124802e42130300108020080d911141c01c000d80c0308425010381141c0001030800c2c082c1c81c0607800380c105030031a4070460741003108440106800705a0347d082000981d00083c0e91a0380a1403170180194010601841840301c0c928010b0040e01c0000300c8010007003d2601c50b0b1b1082d00d0b10002080e0b00141c1048502121001c1d045200600020750044d284903d41508041000c542641c084045a014135400002000f54 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 787711178 1250 787709928 787709933
    0x102030a0c030e0d030507140d0210020d1b02010e1513031d1507050c1c0b040f0b10051306080c130603020a0b03060f010e0a0b0f0f0301080a0302190203060103 70
    0x49451040304800f44038003003d030b030386184d180c000038904a6803180d11140c1d0b8031146401d00c103840480c0d604450030700c0d600003400503c440d90301061360510107042010158540350852101c5024040c501d10050043e040541d20a80c05681500500c1480040c4000e03903818007034442d411003002c1422180840c91039101e816060000740700b500c40c1412401007a8200342c0d0354401000084848080131014044620085402c3c8240601402030f80964942120444160200030145144000611401401c00d14035140040c00303200c14402d64020a65004400342014504003a01094540e05800b0b51401105c4000e00300741c038409284a01c4060b5003502c00100034006040c010000c906d089a20342282c0c0079222a0000300584814420b50040d08a00203c1a140e241c00001d00c10441241c1c0c0d600741c10040c0386005400d040e01d5510068081d100c1e07800405a0701c64050218200d684101084080910340c004000601401c1c00700f04400300f6072207503083e18408040499400c6440c03001c03004c045e5050b000326004100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 787712428 1250 787711178 787711187
    0x1080c0a110111090a0b030f01031101050d050c2718060307031502031b1927030f021203040b12060d2109050625050c10170c03060102030a 61
    0x5100d252200c2960105840c5500f5039045810000f5003040c0411160413526214031004042c00c0070000071801e51408080c0b8000618040c031015100840011202e08241d115808441703220080701010b001a08114901c00d00c50342c010804189201c8003200283c4180e030748243c080d2807941c0c008002410b0305901d140d90004802c1d001e0702c03066041c800d25070700000249900b4001c88080c41c0307100c00141c482c54115401c0000404030b5085910b40441000038544c0035000490000380668180707803080d030b910b55941492603d0500e008111010200c614000010048002d0032504001d100b900d14203c100c0c10b85002c10359a00460080e54103040080c40703d41c1c801c6211321b4901c1d0384000700500ca141d082ca102e4540140141641781c0d120000094107c62042454111641c40e000b80f400b501c03c41e20b08212034110b61202c200c03920b040f02050f010f110300e20707040c888104400c20a00701300070030a030f585c403011b44006400010216212800d106072040082c0c107071143c110680b4071511040c2c01031850411081821203 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 787713678 1250 787712428 787712437
    0x20a060509010e160f0509190917070503030a0606080f0403030c020a0b0f09060c0a050f070f060c0f1e1b02150a0c0201090e010b041e1a0d05090c01080c 67
    0x4100e40d41c5008480c2d02001c00c00118004c00400c1d1202140c85040c6604104009007a401c124012001e003400d11403040a0b0899141030452104000501c203c498a00741038002c038426002c3d9540c000203d8020140500030000714065074188108100751039454500f61400c62045030307842d8401c416100010003003130090300905091030303840c070640b800e241213903403006ca0601081da56000c05082c00390802070b0040c1d0801c01203400c0140c14407100e040c0030400d00024100c2c441c03005144000c04002c00c00204210045140c0640950300c0700d000c0c06804111030000300301c80751211003000094541e10344203000c000c0300e420089031780c03080780d440b00c2c515948450003031280240d01804980280003080e00d0400b813418400500f05d04089a5240c1a0500841c00014140d1900d03400c146031880c12840100840c2600800322000c440c100c0078410b80300d0b4030684000300c800c80c00f0360116003500f0415a1141032540c21b4001804640c440075820040d54a400c012155605124038030503011071095000b04e08800040300292 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 787714928 1250 787713678 787713691
    0x6140d0f051906050f0f0105150a0509100305040b0711060c030c0702091f09021810020a1505100b03040309051e1c2a090f0b0d14010506010e01020a0605 67
    0x7101c0303000d0314001200242502c41c000392900c80d654414460760030351000c161038011489603515000c2c0c2d4142170019481c5104081b060154400004008c80c0460082003a6480341e00020000441071440c3e10307018014050440f41100c03640e07000000104568061002000d20240481c010300e01c07981d44a41c512215840074103042d006d40004d0111500590740c091100340f060400141100d074022040f52000722400e059003114040500600030f00d032340b14040a00341c44e0514022900322040f0340d003401c0181c0c18446401c501801c0c280403901c880d1f4900009410503802103c0070301d401603140740e641600000380d02003910000c0c000750280700100030501d81400012070044001f188503540d4104400020f241e4014a0a00000c12164183c01c2c01880080250f03100c002c0044000610480369020405007199010700030181c2c40d40c1d81c2c083d075100c071260507480607001c41400303400314604c3c03005401c1843c80704100000080c440d43c00d001c0040c466521500c440700e4100010380003881d0381d0900b5518840a8000188030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 787716178 1250 787714928 787714933
    0xb060f0d0510270509010b010215130209040507140409052d010e010917070c180f0c08090d021b04020d0f0903180f050a182d06140d0f05 60
    0x8168034900040d03a8080d4504148416039566541c01c010003134820050200300742e40d241440d00c070140c0e6004107101e148000003100d02a07a03a41d5403041e08620035100d000294108516104102c20041d001038918165101e03480581142090030341007000381c5d881c00754014401e4100c4070794001051030900c2c008000580d16102c56100988100104c6c3c03c6035a050090029a9100ca031400140420320365580594a000d54000e498850140c4903410f120f04244505401117100300c2c0441c4881020f94802c0812aa18201c14840000f4000008042c404155110046402568051200e1f1400050360441814844a0311403140301c0c0c0900700402500509024800643c4070781a081e05400035110b0000001e01c85d0b00e130701048181000344036a810800c0d400100e0980703520401800513595060300070b800c0314900311100401d03e038148000b4026028200380d0400c0407510180b000691800d00c0320300291110a01800c03c0020398a0100682040850310540d4020108940800c08510701e0b64050701c40c903001d0b508 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 787717428 1250 787716178 787716211
    0x1110f0406300c031112010e0a0e0312060102100629091008100e0405210910090611030906041401090312051c02030601121d03040b0301090b060f0d05 66
    0x1000c00c0c0c550621004100050303941c3d034503a40d2894040c40b0365200740b004450200c2c00c10480e0705a800303e510040c0542406020000000340034075100c0c0c0c0000480303801c2d2400792503c4105041010152407003d981e01409801a0b101a01d903410052088204580045030002001c0080c04021500c43d076040c840f0070140b141c1040b40c48540e40301c0440089155021341d6443e050342c6024034081038908000d400200740e110804052002094000681100e1416802e03002c44000d540c1d81e03c08446441003401c5240c010000c41214420a03070030900030317422520b050700d40c20303024a0001015a1a03200d03c9000c40c1c0e0000b403e00007800102c50f8092404039140060500740d001076200d446800c0b0a00c0b1034520240010780001e83c101c030390746025041d0071031030022800541c01c43c00c04400181041c03220b006a03a144940c0c400c0414240c2d040c1c0d10301c01303010700003036400d8070b44e103a84880800801d907109005c1d040c070306404d001e68081241403d004880c0c02d030307000040b06800c040f90f0070b000360003070320014028540b0464500c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 787718678 1250 787717428 787717487
    0x906090a0b06220510110312060103140f0106140a1709150a0b0f01260c16060b040b030604030c08070305040f080d0216300b0f070201110f0406 63
    0xc01022550f244988204a503d140004000100c044040c2d10010070050403046100c420000055072004101c0a00c41b900307642c1e070200102c00400c101a61110b85c09d6502c0c0911001c0700c0d9101c2800e05035142136581d40356041c018a414450f0340f180e0b946100c0003c00000e000f240c2c0800e1056000d80140a65080d1142442452050300d20f0440c2540c0d10340c040c40d6201158102c51030142844c8118030820b0034601000c10440500c0550f101070041412901e0300084001180e101e00030f001c03030b843c80320b40b03094035030381b0008a0910350002d0104e6103da030f0040349072110058691500241c024810333641030b95a03030410300c051740c0da2801e00d4022040c11410322a060002241c0e80e0b600c001420090004000100924060458020700d01040e048a04180035440c680c180b1240f10380180e18180203d503491140c00080e0246649400c0a040d8040034005004500600c03003218228820180107140035402441988406c1982c02e403684660790400100850801c410011035001d01e20380080b115044c1ca001c3d01090048 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 787719928 1250 787718678 787718707
    0x714121f031209090911040203040f05010c0c1a0c03070f12111909050108060103150503010c05130918060b120d12150f03031103360906090a0b06 64
    0x1500100d8400da02e080807008081c0e031154485005000c0c0000611000d1215154084c2e081741c0400841d0155400100150520100d4503001d42720940c000020005880745810082050324446821103401c040d90b91b40d40c00c0a1203000e08640a2040ca1880501c1c42c0c030b0780d0714141e41c140f48226506040c0a2884603424080c600c6101d0040c44010310144103a507480358100d0702198000c030040a109000c180315081c4410b99120090303139403141c0203007400286200100ba6025107181c2c540d10880d419800c10f00d011a14540c0480541064000b400c80033081e00c1d1a0840f000c19100d1000b08010300b29400201c00b1b010400030b0b008422547c2003e440100c0205680c5006030504400003030407004144642164554160248115000c4c0d03000c2608120382c4905061041002c0080c910001d02040020b900181c2590428800c941010a424003800c0f0080340035a0125030304600040c540d881400c04402c502d0050508801061003540020940c2d030309950380d811040c0c010450040701580016050107007030b40c20f0299 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 787721178 1250 787719928 787719991
    0x6030d11070e060a150f030c05120612031e0406090602032b090501021803070602010606171b0c0c18010e1306060504020a02032808040308070e0d080703020105071412 73
    0x1e951b8003100e801022101900b500c5118480c07008004041200100c6c403140c4150350341c0c0060040b076501d1040103005440c1807a500400f0b45c194100c1880b160941701284280c00100103d80326030725103941040d0341d50400c0e038990046859282c0c860303460300300c07002d08981c02c94081c00c40c45104400024880d00280c440c1802c90300080184400c15124144070451498100041c6008003603510091180c11b0501900814260041900f60700c0280c01101240c515281c00c1903608031500d0500d0051340b101004048240c0c0c0355030324100140a401a5081602007410747d004060684104049140d005d131030301d07a615440909020020b541c0c6995400300451166602d00013411a001d00d6130055031030301c40030141e40d54049102e241810604600c00a042400c3d81c101190660ac01e815040526082d69800c0042d5030000710004559406010008294100580c0c00c0150000f80c0c040e80c02007007130b0350f101481514000324190210340e15500a00116449014124500368050041201d481d802001102a00d003042c48 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 787722428 1250 787721178 787721219
    0x6180f070309021807020a020f100207181404150f0507050a0f02120a03060302040b030102031b0c07050a0905071e0909020702030c061303021e3a030806030d11070e060a 74
    0x380047c000e40c07a0492703100c4002181192070300c04802440001940d503c600d84500801d0180806007281e03076589942c800c003480c61640710704042510309868401240015000c0107141103140c2042c4158602c0c9510a0034071805007606c945107416840c030401d9803840a40030b1100c0441c0300d800b082c042c4122801d0702601a00704141c90100d1110b00b90f104000075120341940a6011f07030310620800c2281c40d83d030200032111951503d49143e82d16595003105061003801c0d0405c98104402d41e6000516146a070710452007400d069036210001c05011420361000580020078400040005070244101e404580c002d008bc144020708a8911862030004140f958210083c40c1c5031201c0512400c10641c10100d400706007402080c1001d0050944580014160850003d030400000c0c1e8900c003280708501800c05403549014210b0710450300110381d441e000700b0700314044503001d0007402440040008a4091000726001109400150004504101394101e054400034145a032160558500003900302d4285202c440008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 787723678 1250 787722428 787722433
    0x130c08060a060212160f05060108031801080906010b030c0904050c0d1b0503040f08071b0512030f0415020307080f070302070b09090a0e01022106180f07030902180702 73
    0x20301101048620500c40c1c0c416015034001140c91083c0704404004c640e203080301014200080b8080f03044c28041c40f00310000042c1648a840300100e00b030200040581452044e03407a1402c0c1c11601c040c01100c502034251200d1034103034807510060101400c0e00d400f07181d2006220304a181481c100301c00040070b5600a03039403811103200000718030906050a0055100020007000394080d030501c003540007882c80c440204050124420003035442c082149207021140d80341d421581c0c501400000c643c10b810591042d22406204407001828008030080c0401541d44e2010304c8403800e81020710349904038014a442070f01c07050440c0000c1146100180c102c1001d4130442c110b6a00c03040e2620150f142c043d191001c603410940940105102c014a01c0c1c1da025002d6901090303241d0b000ca1040da03150b011034068040d0445060758002000f1054100d0514201a030744035400843c3d0310304402d02c09040c2948081425990003c0515078400041c20283c040d420016140d40702500e8840990068000c042e00500181d400d40c0041c1c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 787724928 1250 787723678 787723681
    0x3012004152c01020c0915040506011b1e0b040c0e090304030f0303020c070e16090e0c0406210504140d09080d0c0c03051b01020d02210702130c08 64
    0x58120090020300460600b000480c1c16071408294280300150011401c0c004807030080400b0300e9109000f208620712001d170820489041009800c071809207585000c501417464000020b8807588219a0703418807075011000b60440c02c400340c64550b49803018a04e0000c058104417805070000c1d40f000c1d2654810390298441c07200d4035040c101185002d15002d444664154000e100c01c0c408a08800b1040d01032980c103080050b0303254542480e00b41404010b0f48140c40554004080021402d01d1000c0c124480c0380350780c2c802c58a1134580320001c0c040b2009444049003510288000d01125001e41c128105000e02c0c10700303110290720303d0800c006c10303103000300c50440710107100d1030340349810180801c01d15036191200c1c03c0c1464150b00f005841c690303803013900c1301040070030807680d0062007405036040702140a5038020050790000321100e4284150120049000c0b40107200b04035040301d0b814800301b80300c61881455074541481003c5140360003c0c5411066041e0307407140343c035040340030500154451150003e1075602d82c003946 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 787726178 1250 787724928 787724939
    0x1006030c1a09061b0610050a0501200714040c082203020f1023040201021f060305030d1a0a081b010e10090e01060c030e09090f0303011206180f1103012004 68
    0x10105c01500000701c612146405206075540d10300081c064841c2840c10068000505811203892100394040c6652801007920101c1c00c0b010070b030310030760340035009071014403024060b00003c5692440451307242d802e0030010b07156210210030800c40061107901034030403561030403050000a0f09102140c01300034a0310741da4420702a4802800c1c8040881030f10b0382d00201d602450181c0010f500c40300f40240e0400d60481d20102e41d814404a94803c01c0a540c22104517911000c51406030740090002c030042100452000c800410b151501e20440c0090f9500701c405032441c0c001660344a94002140c05450303050111013840202a40c44460302c8007001d43e00e40d500c040c0b001d440d020440d0300c000c4060b081101040340454081c0c0109811800d00c840d168010f0314071400aa03200050b1a0402c0211061030715280400000001e1030403050102d01ca50300c3c002d40c1c08100d1140d0030000c02919034550303407005002652914000300458041c41001188807c064004078030b9204418003032030f516128415000d2051f20200701840b1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 787727428 1250 787726178 787726183
    0x5130905010f090527190503071704030305070b1513091101020303070e01080c0909010f080610031707020a03081903051e061005071506081006030c1a09061b 69
    0x1000c8003c030070401400d1400e4206030a8030500051211004402e84000c01c00f0300810005c08402e01c0c00e8203142200035540b900540341d92010707d040e110320920304031940f403500d041800c49044a0349600c80d240f820010356120190700c0d10041080c247c1d400f022082e0038650300d40d4001e141782d050310200e00103070500c20f40c58100003c207800824541194800d100300808981c20074141d20b030001c1c09080c64500781d42d41d2043d41c819445001801a040708688000081c003001d01d4210380203403030101f0199601541c40000300c207030103040b0303201c0500112113210300d00c0f91000909000f481c91034005402c0040090700c1e5100d03101d03140e000d03a01c2256010490700349041030b19454070440f03400400c043c0808020076110000c0b220110303005480724ac41181d9082140c3d050354001d0f0101e42000e6400824080403010b01e083c05002810070344604080c5000710703801d01c40090114031480c0c0507039510030181c4c0302240c01c3c8440341800f805810074030b0300d070000204800c4401e50f0f0744401820b144203000b0380c07d90004111a0b003290 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 787728678 1250 787727428 787727459
    0x106090e090601261c030518211c1505100c0213111b01050609090a05060c030c07060207120e0a030506010e04020406053c0f060a0513090501 62
    0x200320b030010300050064100c03190a07480c401c003804010050010030094910708094509015030302e2070f960322060400d456050f400c02c5108004441400e80c51000c2440d0351600c07200c1d028030001d484000701014450030048a400307001c018483c0d440e40e414003445461316038200ca202683c40700c3d49000c1001d041105183c02e40d0300c020114918075010702506c0340d0341d012543c8008404200301d0040d441d402d28171300105401c4103030784284240e0284109803d008074689030081000b40c0d0954003515000e00041c159920000308040000d0740200101020340d12403082244070381015200154200c400c02c42d04c03000c501d0b6070000d040c20300c4c010340d1440d40000814001400411040390710b2800b800342c4100402c003260f0046010341c1100c4a4003c1d4940a559074030000d4000c1500c2e4220b10741c003400c11103042d5507010829103038280c440b00c41c0c0b640001003280d07079180c03c0355520070490a40e408115150021410708081c80906030394809800c207a41002207202010302200495000304880541d214010014440250705d01c8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 787729928 1250 787728678 787728691
    0x30c0106140f031b0103020f03040606031205090603060d05160305010219181e0e0403020c09220314071a16030203011a0912030f0a0e10091701140106090e 68
    0x10081502c180c00030030b80718030210300308000c6590800c3d80000c5030b901a4044402454095000e0b903528030302460040c000304260300043d203102c01b601d1868000c0303034060400c84020341002080a0300315900e0074100440c50545000c11035190249040d40302c0301d644040800b80c0a0b40c840c40015071200c9600380d0250400c0c0360038130303400100324440144005580f02e402c01002650908801450360070b59000d103401400c1c21035806410030884504c20001810f502051130030b00c4084c21902c1040e00d49400c0070340c0d0b00905602c0d41040103084100010710000e4090750051010040d001211403c1210f15100c080748100490120300203400c0c040d0808c031031070021104c01410036905040c1142554100000792407908030310203910f101c1c040c00041c3e212253b6039459139490211a110200c90303460041074003065550b0130402c2e44101155080c030511050b450400800d1140070701035911080400d14200c0340280030030003403e5005403556201c081036203041660404501800054a602002e06d1a0101009090380010601c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 787731178 1250 787729928 787729939
    0x10b03120406321309050f010308040501110c0d030201090b0108030c0309042d0c09050a0b030c161a0612011415040605030102030f100609031203150305030c010614 72
    0x140580b5030000b4404500350000042d502024161904582c102c0f115610f4000000d980401c40a180c044010113030760680300800014080e588030202d00c1480901b01f8007005141c03800c240414070075940f00c1c086400b4010409401c071420407240c1d501060f041911003800b540141d44030030000c014824546082801018040300452801c200081000d80724040d83c0f038020301c40c13603c4008606503404003070001c14010710f0075040499520042c10b0384200814000e00396001040322003000040a1a01c01c441e0310440c0c1c5070048403491540e400c1003d400951080880010000340f2004150103e01c100c051121002c401c14035403181803d281d401c0020344d45500c5108010340c0c1c10681d0700c0c510051062a242d400120071340c4100c680c50078820004004d4a030a4202c1034046d072011080068086016440a002d0301c110f4030500800354655008441e8255513010107003841e07500c0d481c802d0019100368001c05901c4168403100b11010740342d030303100c0e42103034807245404003c1c1e034490000340205003911210f9100300c0c00845a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 787732428 1250 787731178 787731187
    0x1709010203040b061c113006090d050702060924030901050f040f1211010f05011811030f091903030b0405061009030311070806040311070602060712090c0e09010b0312 73
    0x43d154107020550100509846203100052400d80341c840c80ba82e10300515407030107e980100b414940100b1188124207091034420480132581c1070f0b901085012061410b0b85d0f4140ca070070115001e00c5075580c04160510342003100c03003120010039507030440d44010800c01091210350ba820010200703030030340700068400485400654207010004406040b0048026408281440d002c900752005541c002d00340c000ca924a5400d000d2204020b805a41c44541600d1100c030b03407444c1c0320206009941c116007604850500440d0200b01003400c82c0041550194000800411100304030448051a011074000800c120003094940d40c8994840ca0a0701409903c0503064130a00c0a00e400d140004241c4402d501c0013070b0511111641d8070482404c144180c501808040d01120720a08143c07038010700f0191420b045000072b010304c0a0100f0000d1003c07800d50700945443c2d48440b00900040c9203100100702000040303035007120311280018500c0c80404801d00c50103541e0000a01040400207140c1004d203003442c80d8048440401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 787733678 1250 787732428 787732459
    0x30106080601051318110a02010903140a0f1d04020f070b1b0d0e070801050106170907180e010b0307090f0b09090d0302130e0a09171314011709010203040b06 69
    0x4c40c58001c03a20811002540001d800395032000070081254440101c5e08000707100d22440341c0541115100c03c0c800e0343c4507510048030304680d20a030b000c0d44883c00e000032901401e1003007503071290041c226000b1a1000a501080d02d807000101280d1014034151441000070031030009100c582d002d515401041c54240d661843e1329000085580c0c0b00707810042c0ea0392607031381d4202d45407240c08002001c007618260780200103558484d41c5c081c00500c2490034054114404000160a40c207000c2006001c031000d0501c0050500d55000c1c0302d002a285558044981d59a14070640500c1d98040002c040280684e60340000c4610070081d05005580841c000c15000346c6010040c0f0410031000108640c0f03081e598900161600c00e5183e0b224131090980e4015411691960180119031140740d0101441500c40d00b50311410808140201c8414041c0d41071340ca20300c00200c0340410400d040b142800640a40500d000d058002480c607001031040c6060343c42000340c0c0e501008100420280b403003c01d07017001e821201c4850400b0b401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 787734928 1250 787733678 787733707
    0x2010903060f0204081504230c0d060227120a0317040f121101050f0708061003060503031602040b06030103080f1804020324060f220b0f03010608060105 67
    0x51100030507195446001c015080502e5064501030003039141900d0482d0803040241c6003d0106641c00e0794000c040703040d8213104100381e0045a80e900d683d50090207001864400700000c0ca68a09420b071007141d02002081c0d80c05045242018446034540c0800c0c404110720300a0000c1e01c0f10701410115541c0c0110280404240c0105440e40c01070050b103981c0c1c906944134035002190032083d450080c0400c8800b8400350489800010b02c9564044140007001169601d4043c40c40b900d206950300801b060110000c5070340c0b8100f101120703040e95020f00300424096a6400400e103154808103080c00c100e100180a02c0441c0303064040c4c0c0641c004101e6405046505645070101d140c8111550003884d040c0010707140c480a041810f4904088400920440d202d20305040e00c401c103141400c903c007130004030992990600d80b60503416a4400c0c0640040c241c103041d180b90610603000d84248031580d807030400c03481c001403482584c0001c00030a01d000310415160b516000000d0203018002c2d1072141480010310880c0c5680000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 787736178 1250 787734928 787734947
    0x3020c070b0f0d0203010821070201080402010f0e090c07030809010b060a11010603060603030c0b07080c030a2301080a030f050a0e130207022e021b0103050612060a0c0e010201090201 80
    0x8909400e9903420210000c10403449008100c3c0441e60010000049101c0007003801c0360304441102c05109400c40300401d600e218811080024089021403021901652080c2c4003404508094100707060219400d0300001d03102079088aa240407140009020810580d105000035000000c42c0028000c0e00304d0300002030058010303020a08204144000000080c0c0c070250403440c0155000041000700c00e440e403d0080100d0322402c03082c0e5038020300ca4003068015208520003807141040070202801d54840708195809004842c0d18428035500c0814181e1040701e102034141e00921a44008194001d000c2c580070f42001c20f005884c000b03000007404048503007a0860f100204a050403201000710020003070048000313010390200a0740008502e4844004101c8540c040120580c80802c1c940070311040c0745040381c0c0c8070600041d0780350400d140d14044807194002d800013500010000c2070285410f05400390b0502d003030812581107000c0e43c5ca42290744a03542c2c1010310900091003c3c8001e00040b544e17900040c1400d42c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 787737428 1250 787736178 787736189
    0xb090c030114150a03150510060503041101030e0a0605011d0117030301150915030c080112020f04050c0405030a0c0524071709030327091b2506091203020c07 69
    0x150300031442800c4c4e680e8a2404060765024241004071400901c12500900c002c83e44048202c80911010401c0c40c00380e0180c1e0b11490344240f403c0d0380b0201c4400114081c02c4007101d1210700d403050f40c40e0080010f195014660191009145403141010b4840d0020003944c13040e8003604d40c440c1d103030100c038600140110131241501c0c00d113801c90203202c001c04401c9030014080e1b03001403510207403d5582d14001d0b505410400b115180c81d55920b2003a40c9030880928012207400c0c2c02076120140403019000c504194200690141c00d20710000d043c5961386010038241030344844220b401031254072080c815803514411111030442d244034a541a8040200f000c1041d2054070341c003500143d0240c60f603172030a0700e0060881d10740c51000341c240d90321a000310806004950403156406c00810f41940c298056080c4095418401e1040f003810405c1407003a8840c1d00c0300c960144101580d00456003403800c0e580001c0c84241c088851280f4400210503400d0308101e40b903045160480410540100301941c104140080d25205840 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 787738678 1250 787737428 787737451
    0x81506040e030d0e1e0303060108162102070f0b010f0608010b030c0702031f1508061302060a0201060b0412020f0315062209050319020f03120a02070506040b090c030114 74
    0x40340c182a062401d200c54000d0203809041c40d50600345da41c008005140030b09800e0321003d4058030351403165600b16102d04e55034400544440e4030104c1c10302d01c0e80b012142c3d5800b902801450300305551903c0c1d06200c401d401c1941d9030348411004020803000612050020000b03481c111070103504017840c4200c02d2101805500d01504003041c03550a5603818400080c002849144118035400d0005a12000e0b00f0940d10301c484603200e0702c4002405074808112240b040010b03218611540038247c0c2000f01a421041c0c0b4130003107650b034900c082807400890000344064141c85503030307d403103100c41d104108544001c00300350350003a00064000ea480e41e030801c03c140c4d00300004072841800314640039003101489030241450942d040c101040c0c841407101c040014410844100c0c80310082400c0c010041c0ea86061101d5500010b600800c00c541c01c400600c040d4a801401d107600140c580505074a0303051074410140c4056685d036204030f051002d410300c10040c5000843c01a0300034010301090b8102c00b90f0f030100c01000307003c205 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 787739928 1250 787738678 787738691
    0x20c010209030a201207092705031905120a020307050f071a010b070b0a0f060503011508011d1011070b01080703150614010c05010204050604081506040e030d 69
    0x1400e40503a4556400a4212420441c06090400319080301518103143d00710124008038080c101091481492400b480091644503d40304002c2d00a14038810040604440d1b810154040080700c0e10315801c00f07000340d00031504c0340114810015060344070800102402003c200b04e120350300519200350340c44134000d40010384031780c0e4568094078a03214441c600091600d0001c0c0304410041c40c07040f05c4030a40d8050305085801d03a02ea240e1401076201c0d081c0302a100a04910026040c00c1c42070300300e880103401591001c100d141e91140400e09450b84030001d000720a524140901411000340f040c201031080ca80e40480822030790030315050702c1d03c9842001220054444103440380c81d6042604440d45264030604120080da920300071b040c9c40344141e0204803030481100070328003158503140c0144c82c2580d5000194402030140301005560801342d00300d04542e02d54091000046982c2c03101d0140008140c1040501410091400312412000300200082d2140385400f2458404047c0041522140c0c0d60742d640c0050314 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 787741178 1250 787739928 787739947
    0x70f06201009031211030c0d0207020a0b07150c0306060c0303020702040207020a0f060f0503040c0905041121010506030708060610031806020d0507030b010206130602040f0e061806100302 82
    0x10410407040e100100350410024208240d41310544403083c0034050780c03c01202d01c001d6220610b510044d03a600c0b0540342c0602042030803c1c00c2d0303070081190a03c018036040866541360b1400d2f9481d0800401650404144140301c0030418142c050001c140800d880d00700100d608144025110070280034000d010191b0108481085488960460758000d400130a07040403580d407107600d03070000e20301360050b84000f032640c800050b00b060151050300d01566006814803001c9040048880090100030030589003030a246c0a04265500c50a85050f0108094042540c18021454425080d01d2002e483d00d402a80301940800c070300c80e408140030343c200c001202c1710810a801d500044001d0041442062a080f0b03100240304100149a4000c3c241e109403904180000e07512020150b0481d4040c1c103049001da040400065104080c0c500358089861180b00b006003099210495034070104203036000b1500c0004182c040c05070600d0303c00412100607020b0142070f501454400003044001c00d01b040e502c01415004119100c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 787742428 1250 787741178 787741183
    0x20f06180718060302150a0c020603190903030506102d050415020c04050a05190e030d02041d010b04150806041103070804020f0609061801110a030c020102070f0620 72
    0x40c5000000c1481e0441c40c40d9542c002000700788822031194440510802c03c1244180641e400c0301519119a60f0200312074081c881107030f000030b0005080a8a92050405804ca184070307018945001c0c0c1d4001640b80b03801402c1c0580b11138007509140034814103610511500c61080c1800b9400f66400c0205103c0300501c00040d00c50340500e03040788850401c6226009a0b195000601c03010016040310140065140c140c04241117801c1036400380c0d80a00306000540d05c11103981c01000c0d0840c1c40000702e030310780395030031000301c04a8102e60801d490640c0035107102030304c00c030440c45458090981004020310b0289400706441103480d80315510300500c85000300003049691254480505000110b092654034030345084c00814045c0c040314100c3c0f2031a00700540745800d06064003a95039000d00034100601d40712401192812103044610714504105c1c0b08003030324401c8403090080150b658800d455240a07000540300190804d4040c0e000860340800622081010300d0780802040046080441d41900fa041c0300f810381030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 787743678 1250 787742428 787742443
    0x41b06142a060f0f01060305070c0210050904021201030c090b06121e0405010b09010f0f1413090c09180c26070b04060e0301020301080706050c030c0106090e0d020f0618 74
    0x20400c1c000d1078100601d45100d0066148544c440010070038140ea03c0340419000c031041a02c3c04000140282054001410407a03c600d224003074074140369040590290000703003682d0000180c03150061000004008204d400c0010b0f4000d8000008180010b0480d000401c205014001c0710086590303582000c21041303000c80b400c01800114503030500c80c862915082650191000c0700109001e00056800040d542048010364820f4600c2c0b1301c580c0d83c0c03561402183c1c02c0da0b2800c0d00e40c003a5000581c40000c0520031030600c03c075521940300700304001089107081c8d440000c8a0b6200761544d205140115688001100c03152050103443c04103c07840c2c8030794150501c08460f800e1008000c8814415001c0126001c1c0141000d44102e4506545108194080100741403d03400288600b001941c0404014001c050146000d01103c4031203504890821044c09400ea00351000e55200450b000c1d0350b0300410301100401d210711200150903000078004a891040000e0717560b040100b01c1031107994104400007443c4020b0081d0b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 787744928 1250 787743678 787743757
    0x307030902130606020f0a02090a2427061a030c09030a242f1306170f070f030f020c011406040617100209010309060203041b0614 57
    0x10b0659400841141c000780828061080503220305084034225002c001840d03288a54042c1c95078800740c8a0121040113414400c90046a107c00d941464044000036001e210081c0440c3c94020085d24100e0900311800340080080981070382401d4081c0403288040c4c500e0b07005c101085d21020354aa90b540041d207000d026000d91705a05002c2c4810400a01c4803104000003044007481c0640710300303028051404100c0d6460001010035000500c80152640003205510702d0f20b0140000c454a8202e80303042104da1644260024400314000c050448078425910314150b6100d81000b000b0343d154102008013810031010003e0b59400c054440250240c003034190380595030315075503501c0280680c110181c404120075508444050141c1e10701000060441c41880080f41115000c10150030503116020f58500a944580e0b44141803584480b0350b9000580144010b51003580601051051074620046c01e20000300503501540411101c02c0c164442d50b004d003411214141d01c044080c0c04602a18007440b808540e805064 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 787746178 1250 787744928 787744939
    0x8040f06150e06041e0b03070b040305101a0609040c0302130b0712080f0f040302073b0c2215020d031b090e100b0f0d0614060f0307030902 61
    0x1280046894040e244050320091031151100b555100f0a100072a0b03611802100f0015a40c140d15441c5192540310b03450a0202505079400507032103081d40132050b81716610459040d400f1403c0c00c440110288130b8060200c02209014600343d074044000340844c0581e14102d441f0365602c908150f00e83c0c3c040e0781101c0114890340c480700c3c05039031f8a4404410542002009840703800008448000c0c251003200715520800611100b080355403540400320901d100700800840640c414041c0201c2c290300300103c0c09008080301032155041400c074003440c0394880c000008003085400e800c0b0910540d000890259880c40010300d00c8000640c4110358248010b12240d07000b1116903104140ba29400b030741c086550302e180d01c0191410300883c41b00107011629481000100400280a1541070201030201c1542d203801020098500fa2400d440c5c0590b0703d01588484e4210003e03d200040c1c40304000054006d40d0002c054800c0300303425552840022803a0303441080c0a03040d44c05400070000d800c5900951001d49990f801420 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 787747428 1250 787746178 787746191
    0x1090213090b0c040f03170705030d0617060408190311040303030605120c030307062c0f0d230f0f0d0f0b091608131b140a03030c020108040f06 63
    0x34018a0000e0310002c80c44800900340751050422601201c07404111741e181903217551242c9451213000d10007521400410001c0380080b600c104003814080c2100c8000040346460207503200c0c03840c2031203003101105822400810002ca1183c0d020703190030820741d0880035a0b00c00030300c1c811001081c20781c00b0845c42580119000c801d055141c2e10540030f0720030580e007515a18400c03d0304140c0d102c6d0507414080d41680100300314400100b03550440c0d4842940814683c42c0342011b44038003212400c00400d02c2d0345070fa12680c00e001507a28100104000c81c54942440c003440c04002d01000c06042c1901d10444411200045d42692400103070100e40002d03008000c04d58881458a84400140482c01c1203842c00505040c00c078881442c0c5032241e00d0003591b508080010940c40c600c000d5841b030400500340500c92038561f032a00041040e8007100c27800301401404140d403460a080d040c0c151464011811406443e0401e0b0910009030070110303e0f90951340909045c0019925031425010200181d4002000e41e4100030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 787748678 1250 787747428 787747459
    0xe060a03230114090606011b0618061404110d03080117030f0a11100506030c010e041e150609050d06020c01020913020a1d0a09050612060f04030e06090603010b0c010902 74
    0x900c0d84c020710100060f2034203510382000465140303070030b5020400303102d000700302d00000603e1340c0d0301981d05a2400d01c03a5898a580c6501c4200c1110420000a0f2640f020340c0b00700800c002d52551100d469070011148101c950546032002007411005000e44a201c6012100c2075030201c1d400c000b615107500401041d10703070f00d5081d405c006081c1248041d41d01c00384d11072038101c0b5001680b41e0044500c40c0c42d002e0700900f200114140115024036901000d0340e0480da694229803080103c4140c00400340003003d4000c110901c03495000302a400180e03104c0c6003002a4250140410740da4000b000505a800c0040540c491600b04040ba00900c91590516403064a80741c3d80c0d94981150f8014103401410780d2518042c12141d2402c0c0d1010481840359140d00c95400f04003070042d010240e020f43d4000700c002e00620000629502c40e2490684142c0d003c1e45a82c40c40707010002010352000f030b04a00c5034000c0d6046030030b081019003c50118041070007a030f4109040070480c084004802d620140200390001c0400100b14900c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 787749928 1250 787748678 787748711
    0x22814030c1f0e030d120c09090c030207140313120501022109011b200a12030e06070c050c0d03021617010b240a1202070803100e060a032301 62
    0x40d81c00403503e100030808980c9408505441e1403030705500c894000b0540000e80b040106030b50030b244024000040e9001c10000300520030054074907650340340141e4500c10350504011600c1228100302407980204000540840c0210401e030803103811458440c00c00c080e6103803803030290140000b00b14840c031010b80c00b41080700d41203c0c01401808000000c0019502800d92843c814030716011400118680c0070f003c0754002041d0085140c1c4102c0182030f2900c0803030680c0e47e4134003c01c0c011072031f0f800a600e0300d000811001c0140059070300085242000b1008210903519903032170b6166643e102d03108034a10000314052600074442c881c842880c50001306d1001d5112140305907400104803864200c1c0d031070a01c0802c054100a81d506451a811100d000c03002060b418460200d9804122007404000b00c216108504405500280080a00c96002c607900c07440c255010000900f40c03644262107c0749070405001050300d0380172070301341581d810003008400700a8001414111440722511076680d0340c68551100c4036141781 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 787751178 1250 787749928 787749979
    0x9100e1305040f02040b0d05060601141b0c040c0206010602060f220506041202011509050c1e0a02060a06031a04020402190503060f060c0d050901021216022814030c 72
    0x300e45c2001486030300400c0c0210101010001401da40c021070103d42d036503001300c1003940150504040300749014007649462080d911400f040900503407151600c40a545030034061010702c100d4920080c661503141c0040250740700e1000e052801c1250f09a40458003001411000d0170028a40b40b0210821954034a0a07175a81d201c120740c01e81d03844210100f8600c4091040c002c140c0044210f04c140310000b4200456440188406050048410000c100034400b850580000c070700c4491426418a440d0084244082c1c2450300090005891500c5c040c028800103446282822a41a04e43c4c5980c0c0d450b91944003040080c8a003241010460942440000920782c0c06801184100c500755400030250b0544d06c148001e50003501c803503440d07070b4100e030001e4510548504080d2640f40c0052045412050360603111402c03560040000d203031049031304105c0f50107500704001101d058910003001c040140302810380a045450060080803100e5039846480314007513804000e180070f251f00c0200880c110301440849205d201c0e82 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 787752428 1250 787751178 787751183
    0x8070b071106090c012007060c050105010e0c030c0a0e03011107021f051c1103040f03020d1e030b03010f05150a060507150903021501080d090b09100e1305040f 70
    0x24546020480c0704000c900240500c2e4920010842c4005034001520b00d0404280d0b41c3c206100310002c402581d071010880c40c0000c18003a00c800900c00ca80d03041081c21f607281600000200203000050000b12a818000c90764000765943c00e254440101d40b008494041d0f01500d4240d056082c525138801095218000786501442212004000f07089114000a45404070650202103002846517154a4102c60000481111040750000b44c410840d101e181060704280d07007d8078400d0300d00c50143c0030590100040f51002e841030600d070078030000e0b003c40383c403044034074000f24010940c907a40c5141441c0c800b50840b041d110740c00c41c0144540d14054103200114a22201e0152080d0300c002c4000515500590445245030780040c2e0890640d40414102c1000e41500398088085103d200710500d002e8591a90b500d01812005010702039142d001c1c2c400400c0070000d5000b09180050400c080181130345d60140588003d49541001c1a1005032000040c4004028281d80e000710703805c060800c400c010384a50303007070280340c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 787753678 1250 787752428 787752437
    0x7050106091a0a0e0601032c0d030c1d0402130911070b1608041b030b090606120c0d1103070b0c07051e03101d030a030519090302030d050c040308070b07 67
    0xc42c0d904204000c9000c0c4218410b080c4004082101d0354070a81201402d141403580701c00f00c20100c40e034150f00c1345c50718510b502e07803c2c1c01450005010702d0303060095041c04d9115203042300703000c14542a0320f5440e8002da40e50340c2c45140d001443e264070001501c0c4910060014801c104a4513036088002c842d82d43c0011011104444604005208a0045440c1c1c44402080c1e070788280c110394540e0f0b1406401c600c0c1d202141c08000c1240c0001000400200c80c0c04c4c03090400d1009043c03c1e0618038140101a207030640841d07155008404400340a860340102d0300100c5030083c2c0c5800d03c940742c050100c0c4c1404204e07008030524007000100c64003140300000ba0700045400c20741c6d400c4140c2612842c05155841c50f003400c182d0541249000184010158200c50244041d008501c0049140170000b1891a80301001e00c0001c6a120030410072440300d908201d5401100d01c4205208240c074503030f0001d40301d224400909400c640d032400450307a60001c51050340c0c051580440c10f030784c0d203480c507090664900314110b66080015 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 787754928 1250 787753678 787753721
    0x31e0203070b0919030f030b090c12070503010b0a0804060b0907020f07050306190b0109050604080106050405090307080403021915030204090e010e07150509030312010e09070e0606030603030705010609 88
    0x70800076080049480004d00488070a542c1e0fa0221148000010380c50105903d071142c0700a29658440340500417001ca59045540c0c07200101103c90541c8000c0c902d40501c0310501c010007602c103440c01125070510039071074424105d40d1140b5000d0000c000c0400303210380146101007044180c41d000150035110001541c2203074900ca940341c040540d40c1034100c949890b030040003000c0d03245650a40d00080c130a8001410407140454485000c902d00340c0155002c03032401c0e9140c40081200e0300381842200d1304090004c001c9c5241c44400c1c2c0b144000c03440f482c80028000d0300502c084c2c04003080521149009026021520180e8604101005000e50014050f01620030f1404500540c5400c3c14800c0104051401014005092070304e000d00551520300003544043c40410840401695002e000901ca40d00c41e800443c2201e50403d40104c05960300240903e8990307000c00300601048403080c1c090741c0d000c0011100315569954010100b4118011600024401d60034010081964425608024550b08000d6000200e5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 787756178 1250 787754928 787754941
    0x30a0b01060c06021c23070c02041e090303150e01030b0f06012006060406082e023c0f030604110702091003021c0b0612071e090516050a0c031e0203070b 67
    0x103c00d00747d6151021030501d410744c90050420760040c49025041c440500c078848190a00d0a007503a0b1011012000280d5401c0503044180d6240c01000107004c01000c2002c1c95819076031072500342032000d00414180c4410700001074250303101d100b04560b042d41d940c0280301c403e0150002603a6034081a900390b4440c0d4100440400c6180000030001500a001c920341c0362032404614500201160b1960b01d01c1080c1e400700b0141c2d05944401d91b14451080990a440d42c4545450040c50100a8074040026421034108680c0240070744480559420810403100003d0402c04c1c84461a4a4810f00c00c0c02500702e241e6104000121109213a208101d1f8000c0d980307103240245030b0500145140348260b0040051103902d02051440c188040181c81b0000c8100440d1000c1d0703100c9144000311104025800345100c6100300a04c807403500c41c01060f070440254160018007a180030009030841c000c4404850401414080c08014144038a400c11100d940041504202c031114200c000d403203610200d0300355441c44840011442 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 787757428 1250 787756178 787756241
    0x9060b011704030e0f12160b0a0c080c07120b0901050105060309070e0c37020109020a05010503040f080318012403080c0f030d09050c030a0b01060c06021c 68
    0x401c1d03001c1456a0210307540e140d5068455114611071035400844c20004a0f18540342d1510f0440d90742c50300c000810001c8008050010300c82c461341c0200c012504140842c04e2400d030810344001403d40c0c031048480d1205840d02c040c0f85040311607404066a0f0300c40b085020180008208094080c03900b07200244503036a00c54050060922096a0304105540540c83c04c0112031030710504540c01c102900c002074a00300f00c61441e00840f203841013400030361780d80c500203881d00d5046000c0714031040d056a00090201c00c426030000b40003420544180c0c3c0c1400000000a402c00c9030764078a41605a5010340f209071030703041c400c1403c14140c51380c89641015600e400602e440004130307084105820f04e41210081c140c42d0441d52044966000401e08404074802d4552445103c1c60a00241200300c070181f00000d00313202141041d5291003a00507401e0f0003600000202000b080d003030b418030b40c192511070034103511003980361410790028419440242e440c61810350140c0b452001ca608459990a092241050580c40031004140c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 787758678 1250 787757428 787757447
    0xc070b0711180105060f04031502030f010614070b2203050d140108190503191e0f140c0a1b050f1008161e0804030801140a0b07020415030609060b01 65
    0x101101d02d4079004100518080d8000e0881c03030071540603141405d540e170365820350400f149901107071410b03004420006e101010f840000e00400c203a00d070084e001a1100300180c113600c55048007500c00048900003544000c854002c04c220008406041d80c0540c115007402401500950f02c100c0c4d00e2402d109040c0303404003944000c0b81c10b031641000034268155000c3c011481c4058030920440f0903002c00e12420500801d2030f082000140e0058803910f030200401d07541039a004484082c0d0305e00307003c1c0442c02054815801a0450340d144030035414190369030100002d0500c0e2183c0b0f40d00041014038004c1140032540c1d840c0c104c2d98102c803015101c0f6845a9401c0d0100310344103000c1c21031040015059400143c004c0b003c51410400001c1608110440c0a06c1580e4070200c0c80c4906018000301e01c050061104155000c0521401804446040020880100c0015459480e28811600c43d4100480c4000665403140d2048502600170a560a2095640d00d4200094128480300369846868452800195400b170040030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 787759928 1250 787758678 787758709
    0x103150305100510140604092003090c030706032c0f070617070207050d0803071205010b0901112a0a1e060207090b09010603050901090c2607080c010c080c070b0711 72
    0x1410503041c054038900400d401803150b27a4000d0340d490b800d00701006810065001d01d83c2000a0020304030580c06051919900394401010546050f0100408402402140d40304900ca14500040380007080d482905e003800c44c40c800ba90342c0c0104140000d0f5981c0240581f1003510740c0e003020307a546603148001661984540d100c0c90381c000701800414000992050002c0d40c1c0004641050300301001c0d8141c26108540c026040402d1065000401c000716682048005d20310f00781e030078020325412200c07c2e0902680c4c1d090030034030601c01e082d040e00b8010030340c4d5420400000d4002503140c003064112031216841040e0075845001e002d40110314020032204440d010ba41c5a80c81c005e40001c0b2280d04c0c040c0700314010700b4000c0a40e80595a42c0a42d54001001549648003d0103000200205103841c590404560140d44103041180d40c00305504005144020980041c0201c090030184030038074480c208032646104445140e2064012800f02041051010300a400c60700d0280b0f030f244910000c11001d124039030804003601d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 787761178 1250 787759928 787759939
    0x30b12030708032203050403060b0901180209010212070c0617100b0c1908030a060f0e130c030b0103050a14011406060c030d02040f080c061206010315030510051014 72
    0x1907001140740d14004640101c02580c40708491041070200455480941c0400c0300040e800080410500c002070168442c6608103e400306129490301c400c0d4104040c810756160001070300400c2c019066070090201800619070358201c5a034651403440c18400c800000d01810000c5100c0441d0808c8505452244520801122440c0200c02c0d09041614100f0b0300201320000c054422541040308203c42d101c5e07801c004500c200f10a949a080c07144400013915204d4110520340140324000b000b60f0041035140941020b80024400240041810700e01544140c641001d040d06c03a001c4000000c00030001000a1980e002d466032070b00360240400d4190a8802c42401e180d4816241000f00d2646c0c03805100a00045441c41d00f101e1074621103221680990700568400501080e5501041240306000d0025400140307003101c1045c60b04440c444045403880c0301800090425035545101c80c0895100081d02000c1c5400404654000c2207900a042c0507000840d180085030f5520900050013420240004100c410001c20 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 787762428 1250 787761178 787761187
    0x4151704050d0815120c0a0819080a03090c06230702030a030f11010f0902030c03070e040605040206040b0408011b0f0c03080c2809050f0915040605130606030b1203 72
    0xb012204003002610041307030a0381602e4401c0c040d54580003030b4404003181c403000d0681d61000300704212418045500c078104940288050030b0010341c008000311600d59004081586419030480704034002c04c41000300408152505101255140d0441c0340b10680508081c60154031050054a422550245440c004d402d03038000a0b400000034002c03407104a51046d00c2c504110358541c2d0803080340c21f44078802009040780c6c0d542c01340301c41581401e00070580149003d80040090a00e0410581e01810005002400c9039903184045021562804111002051003c010303946443d1a103101e24000c103c00e88600b1506040340980642290040009007000c0d1000d4860898074003058409417941800108442c601c603c08021034003420425603050842980b5004070050311403042d92010b003028095402030b034481d110b001808000389e80c40c098115444151001c006840c0320305039001c01d001c0c09251f00003642c0800305070103c079000c080030382c0302c42c0807111a42e4041c002070303407610305004c0c40c491004d0201c40d05070403c00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 787763678 1250 787762428 787762453
    0x50907030c030e0d0c14161809020a0e150a14060d060312050a02060c0c0604030c021c061a0f0d062004080d0f020615190504020415170405 61
    0x5118150301d000740d060204060f0800d19080303003801032000d9407001281a981c807032014402030b01c40000d684403014005001885203119100c3d410001880303981c2c11000c070078800d00303d0030040340c00103903c1c1036000d0062000507407600010544040c0454a06c0034608407404c1c20b1b0644c4c42d150300020304442c4950024000141c2c60014041568844c0c0c40d80b644164540701c0c0000001d20b60320381044117204580d1460784500f154100203050841c003030801280b00038148500111ba42c8045045500310303030701d0704002c1000d941e64400310b010005d0030403040010800b805200c6d0b00384021500000e00150244c1c4075042c3c0100341904100031501600b41c0c4941001d20307030541e10000b880b1a40840703145991480c01da4001842503a04d030840d60310903009000305402c01283c11040c1a044100d01150341d401e40054006c615045480701003203201204007034441c0c00c040300d039170a0210140c42954064540508150340da02d85540707451820781c0203211a00005468080c44259412102ea0914021680400600b07610440d01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 787764928 1250 787763678 787763681
    0x9061909030905040536010b1e310911030a0b0f06060903070b07030828090312020403050a020f1005030406090c05040504032607020a03050c07030f05070906050a05090703 75
    0x1c0034510360304040c00c00d80540541024032081d07101045110800b00c3d201080d07850f822344058000c810b0140c0b160310502c0039036a009848010404406456202e0541c0e404c2c05c01c0548140c0400d10000005100005a48089115084890320700d01a181415594158100307250340c8580c5104050700c250380300d6000c80c0c1074803c2d0013440c50300150b0003040340e0b007040d40349000642001d059900c104402d500004081042681141e80290310401909802c0966444480c0980c80c104000c1c0100546c0c6594402e14010540502504841660703018070454907a912440e01580d50160340c041680329004880e0308070700724a403050545400c0b042c1a51070300d00359100c40e602ca4000d84600d180440c0d00000718040852203803200d01c10281300324005c2d91150399050044e503200b050984001d856000894026080011080e00010308405071a89032030482d42c1c4201d21100642098490340000b4110750100b81200180100051014140c40c481e801c00c01500e59210204001c0301d00341d11905410016040008601030300a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 787766178 1250 787764928 787764931
    0x611184207050609100501090501031a0a060905131b0803071407090203070306031109040203030a0e24040f060e0328061b1d091815090619090309050405 67
    0x861085400d20800d59100342c00c00700c00f1200c4c0c46090340620381c210744281d082c3c0151801020b0a510411665046454006c81020300083c92001e03000e265000c140301c040075900000090200038020092414600e00c07412110070081001d6804002c20b2084900a100b400304003000c403003074000118900b8516548a2405046d0480d01c1d4515003c0c0850018649510780002d600c50300d09135600003441410752034441c4c01484502036907800343c001042003100588001084403107041103414044c0d02d00846e071001441480c0d281c80c0d01100316504480503410044000c0140095407101031443c2c1d035040e01c4600440b9403004c2c001d5095855403184840319a4049503413010401ca502d9000c880c240340c01140c1350744007511805000c0d18000660001d04401c1907900c610680c0c001c1c040b10b000d414850703c001d0000b0f600c101c40a07041d0714000b4041d40ba1520354080170005130107a2648051111300354980040307030940b03841d030407110103416489004001020124601c5180388407607064644144450414003400b005050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 787767428 1250 787766178 787766299
    0xb0a050a03141e1f090b01090b060706020d0b0a120510050a0f05150f0103020a0e040f200406180308070b071808061005010c0b13061118 60
    0x104034404070125010342c444028030090030010031000302c002d14039a1001360540d401540e5070f0b01d40080034001944909a5604458070000041120040c41c1d0002c0c40c14851900002e100d1480002e81da0344815154001c40e800e06000c0300e07070138141d030354031918078444034440c00004005810040b04131445000d036501c4503800420151000900740e9180c40b0788001c0b250280c41c1c81d218003032500c05c00c0020b898800d00c41c201d902801e00e07040d401d01c4c0c006680909a9106040b0303007403007103440d1821008021210b43c4614012002c1d50055210b0310850111198640e00c18000d420001e803594801030800341421022800300c07544202d88a26104190312000402c0c1c8014125031b081000e0400c442c4110300d034008407140a000c0010140c8045d00340005203103823900302944014144900c0c4040360001c82c070301c02445076110588085421500308546000c900400c0e14080c500200c0b88040384041002c0d042c041c3c1050603480c141c668070029500400000c00301d0000042000703076041d140c2d11010950704103186031280d000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 787768678 1250 787767428 787767433
    0x1d0c0c0d0c2f03011d0304032409080408011109100c020411040906090e42010f1d040b0105010c0203070504020f0c2a0418051b040b0a050a0314 63
    0x94440c040d00d02c40c6900e419098446600d1640201c0081c81e00780300e00c0c00d84032142c045604a001a9110b015240c0c0103520000c0c20f0504103c040f200e4101c440c21122907811411a0200081c0101e8034144180782c110780600750f110340c1303818500380f1100d404604440c0f10010003441c4144d2140c0d240d0044a4803000d941382240c000d42c03501c503c0c80c1d128071000c0c0640050065120003007415410504400216680d0b110f1080c02580103d8100c40380240041c0803150a1510014203d042104110600a512203c4203003114071510300d000002c0c180403110380d1006035496100072400305000d0025142c150441643d000c0c00c0c0c030b04074100401c00c07980101d04c0c1070251440581641d406d40d5441d400030b81281c0004d503504040b580002902c0126003800c0c0490401c18840500701503407500c3da41494000000d034541140d0085545030345508408080540510700a94088203c507103d0301c581525509035240d41300818016401c03d03030440210724141401c0010307500701818a9002900d1512400ca407501900c4031501e060 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 787769784 1106 787768678 787768703
    0xf10110409091b120303051323070513020a090f0e04080901030b1009060201050c0c0c040f09050a0506040b0f01030b1602070506041d0c0c0d0c 63
    0x941011400150b6180b59140462101c012581c1e00e5820801ca60f10000341c200c8600c52408040d0711035a01800b0755240d0394000901111000001051406401840e90502113003410500000c502d540403140d55554640c0031a40130f06038911282400380e00011400100c42d0004580360041640c414041d1500d0320b0710440310030031080644010000c020001d01003020760f1081e0401d400c05140203041c0801e0030030140025040c02e80c00d100f114095403e01000400240012090b40c064036124406045a0406031080000820603001e004072916640c6000a01051040000c0c510725071058000308006c2c00c240c14003400155008040c040c0810706000107000185800c01f0458001c0c1c0301d140301009019605a06034140b00040c0c011075000f07900450b000400800e20f4260140d0340d4104040c0841d1074498000380070702c80c0b2030482c5440f101d912207840191030520600c441c1003014001c00c845840c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 787589928 787769784 := by
  have h0 := BRFrame.cov_init 787589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 787589928 ≤ n) (h2 : n < 787769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
